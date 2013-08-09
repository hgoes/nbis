{-# LANGUAGE FlexibleContexts #-}
module Unrollment where

import Language.SMTLib2
import LLVM.FFI.BasicBlock (BasicBlock)
import LLVM.FFI.Instruction (Instruction)
import LLVM.FFI.Value
import LLVM.FFI.Constant

import Value
import Realization
import Program
import Analyzation
import TypeDesc
import MemoryModel

import Data.Map (Map,(!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List
import Foreign.Ptr
import qualified Data.Graph.Inductive as Gr
import Data.Traversable
import Data.Foldable
import Data.Proxy
import Prelude hiding (sequence,mapM,mapM_,foldl,all)
import Data.Ord
import Data.Maybe (catMaybes)

data MergeNode mloc ptr = MergeNode { mergeActivationProxy :: SMTExpr Bool
                                    , mergeInputs :: Map (Ptr Instruction) (Either Val ptr)
                                    , mergePhis :: Map (Ptr BasicBlock) (SMTExpr Bool)
                                    , mergeLoc :: mloc
                                    }

data UnrollEnv mem mloc ptr = UnrollEnv { unrollNextMem :: mloc
                                        , unrollNextPtr :: ptr
                                        , unrollGlobals :: Map (Ptr GlobalVariable) ptr
                                        , unrollMemory :: mem
                                        , unrollMergeNodes :: Map Integer (MergeNode mloc ptr)
                                        , unrollNextMergeNode :: Integer
                                        , unrollGuards :: [Guard]
                                        , unrollWatchpoints :: [Watchpoint]
                                        }

data UnrollContext mloc ptr = UnrollContext { unrollOrder :: [Ptr BasicBlock]
                                            , unrollCtxFunction :: String
                                            , unrollCtxArgs :: Map (Ptr Argument) (Either Val ptr)
                                            , currentMergeNodes :: Map (Ptr BasicBlock,Integer) Integer
                                            , nextMergeNodes :: Map (Ptr BasicBlock,Integer) Integer
                                            , realizationQueue :: [Edge mloc ptr]
                                            , outgoingEdges :: [Edge mloc ptr]
                                            , returns :: [(SMTExpr Bool,Maybe (Either Val ptr),mloc)]
                                            , returnStack :: [(ReturnInfo ptr,Ptr Instruction)]
                                            , calls :: [(String,[Either Val ptr],Map (Ptr Instruction) [(Either Val ptr,SMTExpr Bool)],Map (Ptr Argument) (Either Val ptr),mloc,SMTExpr Bool,Ptr BasicBlock,Integer,Ptr Instruction)]
                                            } deriving (Show)

data Edge mloc ptr = Edge { edgeTargetBlock :: Ptr BasicBlock
                          , edgeTargetSubblock :: Integer
                          , edgeConds :: [(Ptr BasicBlock,SMTExpr Bool,Map (Ptr Instruction) [(Either Val ptr,SMTExpr Bool)],mloc)]
                          } deriving (Show)

data ReturnInfo ptr = ReturnCreate { returnCreateFun :: String
                                   , returnCreateBlk :: Ptr BasicBlock
                                   , returnCreateSBlk :: Integer
                                   , returnCreateInputs :: Map (Ptr Instruction) [(Either Val ptr,SMTExpr Bool)]
                                   , returnCreateArgs :: Map (Ptr Argument) (Either Val ptr)
                                   , returnCreateMergeNodes :: Map (Ptr BasicBlock,Integer) Integer
                                   }
                    | ReturnMerge { returnMergeNode :: Integer
                                  }
                    deriving (Show)

data UnrollConfig = UnrollCfg { unrollDoMerge :: String -> Ptr BasicBlock -> Integer -> Bool
                              , unrollStructs :: Map String [TypeDesc]
                              , unrollTypes :: Set TypeDesc
                              }

enqueueEdge :: [Ptr BasicBlock] -> Edge mloc ptr -> [Edge mloc ptr] -> [Edge mloc ptr]
enqueueEdge = insertWithOrder (\x y -> if edgeTargetBlock x == edgeTargetBlock y
                                       then Just $ comparing edgeTargetSubblock x y
                                       else Nothing)
              (\e1 e2 -> e1 { edgeConds = (edgeConds e1)++(edgeConds e2) }) edgeTargetBlock

insertWithOrder :: Eq b => (a -> a -> Maybe Ordering) -> (a -> a -> a) -> (a -> b) -> [b] -> a -> [a] -> [a]
insertWithOrder cmp comb f order el [] = [el]
insertWithOrder cmp comb f order el (x:xs) = case cmp el x of
  Just LT -> el:x:xs
  Just GT -> x:insertWithOrder cmp comb f order el xs
  Just EQ -> comb el x:xs
  Nothing -> updateOrder' order
  where
    updateOrder' [] = x:insertWithOrder cmp comb f order el xs
    updateOrder' (y:ys)
      | y==f el    = el:x:xs
      | y==f x     = x:insertWithOrder cmp comb f (y:ys) el xs
      | otherwise = updateOrder' ys

compareWithOrder :: Eq a => [a] -> a -> a -> Ordering
compareWithOrder order x y = if x==y
                             then EQ
                             else getOrder' order
  where
    getOrder' [] = error "Elements not in order"
    getOrder' (c:cs) = if c==x
                       then LT
                       else (if c==y
                             then GT
                             else getOrder' cs)

shiftOrder :: (a -> Bool) -> [a] -> [a]
shiftOrder f xs = let (prf,pof) = List.break f xs
                  in pof++prf

addMergeNode :: UnrollEnv mem mloc ptr -> MergeNode mloc ptr -> (UnrollEnv mem mloc ptr,Integer)
addMergeNode env nd = let nxt = unrollNextMergeNode env
                      in (env { unrollMergeNodes = Map.insert nxt nd (unrollMergeNodes env)
                              , unrollNextMergeNode = succ nxt
                              },nxt)

getMergeNode :: UnrollEnv mem mloc ptr -> Integer -> MergeNode mloc ptr
getMergeNode env idx = case Map.lookup idx (unrollMergeNodes env) of
  Just nd -> nd

updateMergeNode :: UnrollEnv mem mloc ptr -> Integer -> MergeNode mloc ptr -> UnrollEnv mem mloc ptr
updateMergeNode env idx nd = env { unrollMergeNodes = Map.insert idx nd (unrollMergeNodes env) }

adjustMergeNode :: Monad m => UnrollEnv mem mloc ptr -> Integer -> (MergeNode mloc ptr -> m (a,MergeNode mloc ptr)) -> m (a,UnrollEnv mem mloc ptr)
adjustMergeNode env idx f = do
  let nd = getMergeNode env idx
  (res,nd') <- f nd
  return (res,updateMergeNode env idx nd')

adjustMergeNode' :: Monad m => UnrollEnv mem mloc ptr -> Integer -> (MergeNode mloc ptr -> m (MergeNode mloc ptr)) -> m (UnrollEnv mem mloc ptr)
adjustMergeNode' env idx f = do
  (_,env') <- adjustMergeNode env idx (\nd -> do
                                          x <- f nd
                                          return ((),x))
  return env'

unrollProxies :: UnrollEnv mem mloc ptr -> (Proxy mloc,Proxy ptr)
unrollProxies _ = (Proxy,Proxy)

startBlock :: Gr.Graph gr => ProgramGraph gr -> (Ptr BasicBlock,Integer)
startBlock pgr = (blk,sblk)
  where
    (start_node,_) = Gr.nodeRange (programGraph pgr)
    Just (blk,_,sblk,_) = Gr.lab (programGraph pgr) start_node

initOrder :: Gr.Graph gr => ProgramGraph gr -> [Ptr BasicBlock]
initOrder pgr = order
  where
    (start_node,_) = Gr.nodeRange (programGraph pgr)
    [dffTree] = Gr.dff [start_node] (programGraph pgr)
    order = reverse $ List.nub $ fmap (\nd -> let Just (blk,_,sblk,_) = Gr.lab (programGraph pgr) nd in blk) $ Gr.postorder dffTree

startingContext :: (Gr.Graph gr,MemoryModel mem Integer Integer)
                   => UnrollConfig -> Map String (ProgramGraph gr) -> String
                   -> Map (Ptr GlobalVariable) (TypeDesc,Maybe MemContent)
                   -> SMT (UnrollContext Integer Integer,UnrollEnv mem Integer Integer)
startingContext cfg program fname globs = case Map.lookup fname program of
  Just gr -> do
    let order = initOrder gr
        (blk,sblk) = startBlock gr
        ((cptr,prog),globs') = mapAccumL (\(ptr',prog') (tp,cont) 
                                          -> ((succ ptr',(ptr',tp,cont):prog'),ptr')
                                         ) (0,[]) globs
    mem <- memNew (Proxy::Proxy Integer) (unrollTypes cfg) (unrollStructs cfg) [ (ptr,tp,cont) | (ptr,PointerType tp,cont) <- prog ]
    return (UnrollContext { unrollOrder = order
                          , unrollCtxFunction = fname
                          , unrollCtxArgs = Map.empty
                          , currentMergeNodes = Map.empty
                          , nextMergeNodes = Map.empty
                          , realizationQueue = [Edge { edgeTargetBlock = blk
                                                     , edgeTargetSubblock = sblk
                                                     , edgeConds = [(nullPtr,constant True,Map.empty,0)]
                                                     }]
                          , outgoingEdges = []
                          , returnStack = []
                          , returns = []
                          , calls = []
                          },UnrollEnv { unrollNextMem = 1
                                      , unrollNextPtr = cptr
                                      , unrollGlobals = globs'
                                      , unrollMemory = mem
                                      , unrollMergeNodes = Map.empty
                                      , unrollNextMergeNode = 0
                                      , unrollGuards = []
                                      , unrollWatchpoints = []
                                      })
  Nothing -> error $ "Function "++fname++" not found in program graph."

spawnContexts :: Gr.Graph gr => Map String (ProgramGraph gr) -> UnrollContext mloc ptr -> [UnrollContext mloc ptr]
spawnContexts funs ctx
  = [ UnrollContext { unrollOrder = shiftOrder (==edgeTargetBlock edge) (unrollOrder ctx)
                    , unrollCtxFunction = unrollCtxFunction ctx
                    , unrollCtxArgs = unrollCtxArgs ctx
                    , currentMergeNodes = Map.delete (edgeTargetBlock edge,edgeTargetSubblock edge) (nextMergeNodes ctx)
                    , nextMergeNodes = Map.empty
                    , realizationQueue = [edge]
                    , outgoingEdges = []
                    , returnStack = returnStack ctx
                    , returns = []
                    , calls = []
                    }
    | edge <- outgoingEdges ctx ]++
    [ UnrollContext { unrollOrder = initOrder (funs!fname)
                    , unrollCtxFunction = fname
                    , unrollCtxArgs = Map.fromList [ (arg_ptr,arg_val) | ((arg_ptr,arg_tp),arg_val) <- zip (arguments fgr) args ]
                    , currentMergeNodes = Map.empty
                    , nextMergeNodes = Map.empty
                    , realizationQueue = [ Edge { edgeTargetBlock = blk
                                                , edgeTargetSubblock = sblk
                                                , edgeConds = [(nullPtr,cond,Map.empty,loc)]
                                                } ]
                    , outgoingEdges = []
                    , returns = []
                    , returnStack = (case Map.lookup (ret_blk,ret_sblk) (nextMergeNodes ctx) of
                                        Just mn -> ReturnMerge mn
                                        Nothing -> ReturnCreate (unrollCtxFunction ctx) ret_blk ret_sblk inps ret_args (nextMergeNodes ctx),ret_addr):(returnStack ctx)
                    , calls = []
                    }
      | (fname,args,inps,ret_args,loc,cond,ret_blk,ret_sblk,ret_addr) <- calls ctx
      , let fgr = funs!fname
      , let (blk,sblk) = startBlock fgr ]++
    (case returnStack ctx of
        (ReturnCreate rfun rblk rsblk rvals rargs rmerge,ret_addr):rstack
          -> [ UnrollContext { unrollOrder = initOrder (funs!rfun)
                             , unrollCtxFunction = rfun
                             , unrollCtxArgs = rargs
                             , currentMergeNodes = rmerge
                             , nextMergeNodes = Map.empty
                             , realizationQueue = [ Edge { edgeTargetBlock = rblk
                                                         , edgeTargetSubblock = rsblk
                                                         , edgeConds = [(rblk,ret_cond,case ret_val of
                                                                            Nothing -> rvals
                                                                            Just rval -> Map.insert ret_addr [(rval,constant True)] rvals,ret_loc) ]
                                                         } ]
                             , outgoingEdges = []
                             , returns = []
                             , returnStack = rstack
                             , calls = []
                             }
             | (ret_cond,ret_val,ret_loc) <- returns ctx ]
        _ -> [])

performUnrollmentCtx :: (Gr.Graph gr,MemoryModel mem mloc ptr,Eq ptr,Enum ptr,Eq mloc,Enum mloc,Show ptr,Show mloc)
                        => Bool
                        -> UnrollConfig
                        -> Map String (ProgramGraph gr)
                        -> UnrollEnv mem mloc ptr
                        -> UnrollContext mloc ptr
                        -> SMT (UnrollEnv mem mloc ptr,UnrollContext mloc ptr)
performUnrollmentCtx isFirst cfg program env ctx
  | unrollmentDone ctx = return (env,ctx)
  | otherwise = do
    --trace ("Step: "++show ctx) (return ())
    (env',ctx') <- stepUnrollCtx isFirst cfg program env ctx
    performUnrollmentCtx False cfg program env' ctx'

unrollmentDone :: UnrollContext mloc ptr -> Bool
unrollmentDone ctx = List.null (realizationQueue ctx)

stepUnrollCtx :: (Gr.Graph gr,MemoryModel mem mloc ptr,Eq ptr,Enum ptr,Eq mloc,Enum mloc)
                 => Bool
                 -> UnrollConfig
                 -> Map String (ProgramGraph gr)
                 -> UnrollEnv mem mloc ptr
                 -> UnrollContext mloc ptr
                 -> SMT (UnrollEnv mem mloc ptr,UnrollContext mloc ptr)
stepUnrollCtx isFirst cfg program env cur = case realizationQueue cur of
  (Edge blk sblk inc):rest -> case Map.lookup (blk,sblk) (currentMergeNodes cur) of
    Nothing -> do
      let pgr = program!(unrollCtxFunction cur)
          node = (nodeMap pgr)!(blk,sblk)
          Just (_,name,_,instrs) = Gr.lab (programGraph pgr) node
          (info,realize) = preRealize (realizeInstructions instrs)
          mkMerge = unrollDoMerge cfg (unrollCtxFunction cur) blk sblk
          blk_name = (case name of
                         Nothing -> show blk
                         Just rname -> rname)++"_"++show sblk
          mergedInps = Map.unionsWith (++) (fmap (\(_,cond,i,_) -> fmap (\opts -> fmap (\(v,cond') -> (v,cond .&&. cond')) opts) i) inc)
      (act,inp,phis,start_loc,prev_locs,merge_node,nenv,mem_instr,ptr_eqs,mem_eqs)
        <- if mkMerge
           then (do
                    act_proxy <- varNamed $ "proxy_"++blk_name
                    act_static <- defConstNamed ("act_"++blk_name) (app or' ([ act | (_,act,_,_) <- inc ]++[act_proxy]))
                    let (nenv1,mp) = Map.mapAccumWithKey (\env' vname (tp,name) -> case tp of
                                                             PointerType _ -> (env' { unrollNextPtr = succ $ unrollNextPtr env' },return (Right $ unrollNextPtr env'))
                                                             _ -> (env',do
                                                                      let rname = case name of
                                                                            Nothing -> show vname
                                                                            Just n -> n
                                                                      v <- valNew rname tp
                                                                      return (Left v))
                                                         ) env (rePossibleInputs info)
                        nenv2 = nenv1 { unrollNextMem = succ $ unrollNextMem nenv1 }
                        loc = unrollNextMem nenv1
                    inp <- sequence mp
                    ptr_eqs <- sequence $
                               Map.intersectionWith (\trg src -> case trg of
                                                        Left trg_v -> do
                                                          mapM_ (\(Left src_v,cond) -> assert $ cond .=>. (valEq trg_v src_v)) src
                                                          return Nothing
                                                        Right trg_p -> return (Just (trg_p,fmap (\(Right src_p,cond) -> (cond,src_p)) src))
                                                    ) inp mergedInps
                    phis <- fmap Map.fromList $
                            mapM (\blk' -> do
                                     phi <- varNamed "phi"
                                     return (blk',phi)
                                 ) (Set.toList $ rePossiblePhis info)
                    return (act_static,inp,phis,loc,[loc],
                            Just $ MergeNode { mergeActivationProxy = act_proxy
                                             , mergeInputs = inp
                                             , mergePhis = phis
                                             , mergeLoc = loc },nenv2,
                            [],[ (cond,src_p,trg_p) | (_,Just (trg_p,src_ps)) <- Map.toList ptr_eqs
                                                    , (cond,src_p) <- src_ps ],
                            [ (act',loc',loc) | (_,act',_,loc') <- inc ]))
           else (do
                    act <- defConstNamed ("act_"++(unrollCtxFunction cur)++"_"++blk_name) (app or' [ act | (_,act,_,_) <- inc ])
                    let (val_eqs,ptr_eqs) = Map.mapEither id $ Map.intersectionWith (\(tp,name) src -> case tp of
                                                                                        PointerType _ -> Right (fmap (\(Right src_p,cond) -> (cond,src_p)) src)
                                                                                        _ -> Left (name,fmap (\(Left src_v,cond) -> (src_v,cond)) src)
                                                                                    ) (rePossibleInputs info) mergedInps
                        (nenv1,ptr_eqs') = Map.mapAccum (\env' ptrs@((_,ptr):ptrs')
                                                         -> if all (\(_,ptr') -> ptr==ptr') ptrs'
                                                            then (env',Left ptr)
                                                            else (env' { unrollNextPtr = succ $ unrollNextPtr env' },Right (unrollNextPtr env',ptrs))
                                                        ) env ptr_eqs
                        (ptr_sims,ptr_eqs'') = Map.mapEither id ptr_eqs'
                        (start_loc,prev_locs,nenv2,mphis) = case inc of
                          (_,_,_,loc'):inc' -> if all (\(_,_,_,loc'') -> loc'==loc'') inc'
                                               then (loc',[loc'],nenv1,[])
                                               else (let loc'' = unrollNextMem nenv1
                                                     in (loc'',[ loc''' | (_,_,_,loc''') <- inc ],nenv1 { unrollNextMem = succ loc'' },[MIPhi [ (act'',loc''') | (_,act'',_,loc''') <- inc ] loc'']))
                    val_eqs' <- sequence $ Map.mapWithKey (\inp (name,vals) -> do
                                                              let rname = "inp_"++(case name of
                                                                                      Nothing -> show inp
                                                                                      Just n -> n)
                                                              valCopy rname (valSwitch vals)
                                                          ) val_eqs
                    phis <- mapM (\blk' -> case [ cond | (blk'',cond,_,_) <- inc, blk''==blk' ] of
                                     [] -> return Nothing
                                     xs -> do
                                       phi <- defConstNamed "phi" (app or' xs)
                                       return $ Just (blk',phi)
                                 ) (Set.toList $ rePossiblePhis info)
                    return (act,Map.unions [fmap Left val_eqs'
                                           ,fmap (Right . fst) ptr_eqs''
                                           ,fmap Right ptr_sims],
                            Map.fromList $ catMaybes phis,start_loc,prev_locs,Nothing,nenv2,
                            [MISelect choices trg | (trg,choices) <- Map.elems ptr_eqs'' ]++
                            mphis,
                            [],[]))
      (fin,nst,outp) <- postRealize (RealizationEnv { reFunction = unrollCtxFunction cur
                                                    , reBlock = blk
                                                    , reSubblock = sblk
                                                    , reActivation = act
                                                    , reGlobals = unrollGlobals nenv
                                                    , reArgs = unrollCtxArgs cur
                                                    , reInputs = inp
                                                    , rePhis = phis
                                                    , reStructs = unrollStructs cfg })
                        start_loc
                        (unrollNextMem nenv)
                        (unrollNextPtr nenv)
                        realize
      let new_vars = Map.union (fmap (\v -> [(v,constant True)]) (reLocals nst)) mergedInps
          outEdges = case fin of
            Jump trgs -> [ Edge { edgeTargetBlock = trg
                                , edgeTargetSubblock = 0
                                , edgeConds = [(blk,act .&&. cond,new_vars,reCurMemLoc nst)]
                                } | (cond,trg) <- trgs ]
            _ -> []
          outCalls = case fin of
            Call fname args ret -> [(fname,args,new_vars,unrollCtxArgs cur,reCurMemLoc nst,act,blk,sblk+1,ret)]
            _ -> []
          outReturns = case fin of
            Return val -> [(act,val,reCurMemLoc nst)]
            _ -> []
          (nqueue,nout) = case merge_node of
            -- A merge point was created, so each outgoing edge creates a new context
            Just _ -> (rest,
                       foldl (flip $ enqueueEdge (unrollOrder cur)) (outgoingEdges cur) outEdges)
            -- Not a merge point, so an edge only creates a new context when it already appeared in this context.
            -- This is achieved by checking if it appears before the current node in the block-order.
            Nothing -> foldl (\(cqueue,cout) edge -> case compareWithOrder (unrollOrder cur) blk (edgeTargetBlock edge) of
                                 LT -> (enqueueEdge (unrollOrder cur) edge cqueue,cout)
                                 _ -> (cqueue,enqueueEdge (unrollOrder cur) edge cout)
                             ) (rest,outgoingEdges cur) outEdges
          (prx_loc,prx_ptr) = unrollProxies nenv
      nmem0 <- if isFirst
               then makeEntry prx_ptr (unrollMemory nenv) start_loc
               else return (unrollMemory nenv)
      nmem1 <- case mem_instr++(reMemInstrs outp) of
        [] -> return nmem0
        xs -> addProgram nmem0 act prev_locs xs
      nmem2 <- foldlM (\cmem (cond,src,trg) -> connectLocation cmem prx_ptr cond src trg
                      ) nmem1 mem_eqs
      nmem3 <- foldlM (\cmem (cond,src_p,trg_p)
                       -> connectPointer cmem prx_loc cond src_p trg_p
                      ) nmem2 ptr_eqs
      return (nenv { unrollNextPtr = reNextPtr nst
                   , unrollNextMem = reNextMemLoc nst
                   , unrollMemory = nmem3
                   , unrollGuards = (reGuards outp)++(unrollGuards nenv)
                   , unrollWatchpoints = (reWatchpoints outp)++(unrollWatchpoints nenv)
                   },cur { realizationQueue = nqueue
                         , outgoingEdges = nout
                         , calls = outCalls ++ (calls cur)
                         , returns = outReturns ++ (returns cur) })
    Just mn -> do
      -- A suitable merge point is available, so just use it.
      ((mnInps,mnLoc),env') <- adjustMergeNode env mn (\mn' -> do
                                                          nprx <- varNamed "proxy"
                                                          assert $ (mergeActivationProxy mn') .==. (app or' ([ act | (_,act,_,_) <- inc ]++[nprx]))
                                                          return ((mergeInputs mn',mergeLoc mn'),mn' { mergeActivationProxy = nprx }))
      nmem1 <- foldlM (\cmem (blk',act',inp',_)
                       -> foldlM (\cmem (trg,src)
                                  -> case trg of
                                    Left trg_v -> case src of
                                      [(Left src_v,_)] -> do
                                        assert $ act' .=>. (valEq trg_v src_v)
                                        return cmem
                                    Right trg_p -> case src of
                                      [(Right src_p,_)] -> do
                                        let (prx_mloc,_) = unrollProxies env
                                        connectPointer cmem prx_mloc act' src_p trg_p
                                 ) cmem (Map.intersectionWith (\trg src -> (trg,src)) mnInps inp')
                      ) (unrollMemory env) inc
      let (_,prx_ptr) = unrollProxies env
      nmem2 <- foldlM (\cmem (_,act,_,loc) -> connectLocation cmem prx_ptr act loc mnLoc) nmem1 inc
      return (env' { unrollMemory = nmem2 },cur { realizationQueue = rest })
