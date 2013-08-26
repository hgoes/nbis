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
import ConditionList

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
import Control.Monad.Trans (lift)
import Control.Monad.State (get,put,modify,StateT,runStateT)

data MergeNode mloc ptr = MergeNode { mergeActivationProxy :: SMTExpr Bool
                                    , mergeInputs :: Map (Ptr Instruction) MergeValueRef
                                    , mergePhis :: Map (Ptr BasicBlock) (SMTExpr Bool)
                                    , mergeLoc :: mloc
                                    }

newtype MergeValueRef = MergeValueRef Integer deriving (Eq,Ord,Show,Enum)

data MergeValue ptr = MergedValue Bool (Either Val ptr)
                    | UnmergedValue String Bool [(MergeValueRef,SMTExpr Bool)]

type MergeValues ptr = Map MergeValueRef (MergeValue ptr)

data UnrollEnv mem mloc ptr = UnrollEnv { unrollNextMem :: mloc
                                        , unrollNextPtr :: ptr
                                        , unrollGlobals :: Map (Ptr GlobalVariable) ptr
                                        , unrollMemory :: mem
                                        , unrollMergeNodes :: Map Integer (MergeNode mloc ptr)
                                        , unrollNextMergeNode :: Integer
                                        , unrollMergeValues :: Map MergeValueRef (MergeValue ptr)
                                        , unrollNextMergeValue :: MergeValueRef
                                        , unrollGuards :: [Guard]
                                        , unrollWatchpoints :: [Watchpoint]
                                        }

type ValueMap = Map (Ptr Instruction) MergeValueRef

data UnrollContext mloc ptr = UnrollContext { unrollOrder :: [Ptr BasicBlock]
                                            , unrollCtxFunction :: String
                                            , unrollCtxArgs :: Map (Ptr Argument) (Either Val ptr)
                                            , currentMergeNodes :: Map (Ptr BasicBlock,Integer) Integer
                                            , nextMergeNodes :: Map (Ptr BasicBlock,Integer) Integer
                                            , realizationQueue :: [Edge mloc ptr]
                                            , outgoingEdges :: [Edge mloc ptr]
                                            , returns :: [(SMTExpr Bool,Maybe MergeValueRef,mloc)]
                                            , returnStack :: [(ReturnInfo ptr,Ptr Instruction)]
                                            , calls :: [(String,[Either Val ptr],ValueMap,Map (Ptr Argument) (Either Val ptr),mloc,SMTExpr Bool,Ptr BasicBlock,Integer,Ptr Instruction)]
                                            } deriving (Show)

data Edge mloc ptr = Edge { edgeTargetBlock :: Ptr BasicBlock
                          , edgeTargetSubblock :: Integer
                          , edgeConds :: [(Ptr BasicBlock,SMTExpr Bool,ValueMap,mloc)]
                          } deriving (Show)

data ReturnInfo ptr = ReturnCreate { returnCreateFun :: String
                                   , returnCreateBlk :: Ptr BasicBlock
                                   , returnCreateSBlk :: Integer
                                   , returnCreateInputs :: ValueMap
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

type UnrollMonad mem mloc ptr = StateT (UnrollEnv mem mloc ptr) SMT

mergeValueMaps :: Bool -> [(SMTExpr Bool,ValueMap)] -> UnrollMonad mem mloc ptr ValueMap
mergeValueMaps extensible mps = do
  let merge_map = Map.unionsWith (++) $ fmap (\(c,mp) -> fmap (\ref -> [(ref,c)]) mp) mps
  sequence $ Map.mapWithKey (\instr entrs -> do
                                env <- get
                                put $ env { unrollMergeValues = Map.insert (unrollNextMergeValue env) (UnmergedValue "inp" extensible entrs) (unrollMergeValues env)
                                          , unrollNextMergeValue = succ (unrollNextMergeValue env)
                                          }
                                return $ unrollNextMergeValue env
                            ) merge_map

addMerge :: (MemoryModel mem mloc ptr,Enum ptr) => Bool -> SMTExpr Bool -> ValueMap -> ValueMap -> UnrollMonad mem mloc ptr ValueMap
addMerge extensible cond mp_new mp_old
  = mapM (\entr -> case entr of
             Left (Left x) -> do
               env <- get
               put $ env { unrollMergeValues = Map.insert (unrollNextMergeValue env) (UnmergedValue "inp" extensible [(x,cond)]) (unrollMergeValues env)
                         , unrollNextMergeValue = succ (unrollNextMergeValue env) }
               return $ unrollNextMergeValue env
             Left (Right x) -> return x
             Right (new,old) -> do
               mergeValues old new cond
               return old) $
    Map.unionWith (\(Left (Left x)) (Left (Right y)) -> Right (x,y)) (fmap (Left . Left) mp_new) (fmap (Left . Right) mp_old)

dumpMergeValue :: MergeValueRef -> UnrollMonad mem mloc ptr String
dumpMergeValue ref@(MergeValueRef n) = do
  env <- get
  case Map.lookup ref (unrollMergeValues env) of
    Just (MergedValue ext v) -> return $ show n++"@(Merged "++
                                (if ext then "extensible " else "")++
                                (case v of
                                    Left v' -> show v'
                                    Right _ -> "pointer")++")"
    Just (UnmergedValue name ext vals) -> do
      rvals <- mapM (\(ref,cond) -> do
                        rval <- dumpMergeValue ref
                        return $ show cond++" ~> "++rval) vals
      return $ show n++"@(Unmerged "++
        (if ext then "extensible " else "")++
        ("{"++List.intercalate ", " rvals++"})")

getMergeValue :: (MemoryModel mem mloc ptr,Enum ptr) => MergeValueRef -> UnrollMonad mem mloc ptr (Either Val ptr)
getMergeValue ref = do
  env <- get
  case Map.lookup ref (unrollMergeValues env) of
    Just (MergedValue _ v) -> return v
    Just (UnmergedValue name extensible vals) -> do
      rvals <- mapM (\(ref,cond) -> do
                        val <- getMergeValue ref
                        return (val,cond)
                    ) vals
      lift $ comment $ "Merging value "++show ref
      res <- case rvals of
        ((Left v,_):_) -> if extensible
                          then (do
                                   nval <- lift $ valNewSameType name v
                                   mapM_ (\(Left val,cond) -> lift $ assert $ cond .=>. (valEq nval val)) rvals
                                   return $ Left nval)
                          else (do
                                   nval <- lift $ valCopy name (valSwitch $ fmap (\(Left val,cond) -> (val,cond)) rvals)
                                   return $ Left nval)
        ((Right p,_):_) -> do
          env <- get
          let (prx,_) = unrollProxies env
              nptr = unrollNextPtr env
          nmem <- lift $ foldlM (\cmem (Right ptr,cond) -> connectPointer cmem prx cond ptr nptr) (unrollMemory env) rvals
          put $ env { unrollNextPtr = succ nptr
                    , unrollMemory = nmem }
          return (Right nptr)
      modify $ \env -> env { unrollMergeValues = Map.insert ref (MergedValue extensible res) (unrollMergeValues env) }
      return res

mergeValues :: (MemoryModel mem mloc ptr,Enum ptr) => MergeValueRef -> MergeValueRef -> SMTExpr Bool -> UnrollMonad mem mloc ptr ()
mergeValues ref val cond = do
  env <- get
  case Map.lookup ref (unrollMergeValues env) of
    Just mn -> do
      nmn <- mergeValue val cond mn
      modify $ \env -> env { unrollMergeValues = Map.insert ref nmn (unrollMergeValues env) }

mergeValue :: (MemoryModel mem mloc ptr,Enum ptr) => MergeValueRef -> SMTExpr Bool -> MergeValue ptr -> UnrollMonad mem mloc ptr (MergeValue ptr)
mergeValue val cond (UnmergedValue name extensible uvals)
  = if extensible
    then return $ UnmergedValue name extensible ((val,cond):uvals)
    else error $ "Merging "++show val++" into non-extensible value "++name++" "++show uvals
mergeValue val cond (MergedValue extensible mval) = do
  rval <- getMergeValue val
  case (rval,mval) of
    (Left v1,Left v2) -> if extensible
                         then lift $ assert $ cond .=>. (valEq v2 v1)
                         else error $ "Merging into non-extensible variable "++show v2
    (Right p1,Right p2) -> do
      env <- get
      let (prx,_) = unrollProxies env
      nmem <- lift $ connectPointer (unrollMemory env) prx cond p1 p2
      put $ env { unrollMemory = nmem }
  return (MergedValue extensible mval)

createMergeValues :: Bool -> Map (Ptr Instruction) (Either Val ptr) -> UnrollMonad mem mloc ptr ValueMap
createMergeValues extensible
  = mapM (\val -> do
             env <- get
             put $ env { unrollMergeValues = Map.insert (unrollNextMergeValue env) (MergedValue extensible val) (unrollMergeValues env)
                       , unrollNextMergeValue = succ $ unrollNextMergeValue env
                       }
             return $ unrollNextMergeValue env
         )

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

addMergeNode :: MergeNode mloc ptr -> UnrollMonad mem mloc ptr Integer
addMergeNode nd = do
  env <- get
  let nxt = unrollNextMergeNode env
  put $ env { unrollMergeNodes = Map.insert nxt nd (unrollMergeNodes env)
            , unrollNextMergeNode = succ nxt
            }
  return nxt

getMergeNode :: Monad m => Integer -> StateT (UnrollEnv mem mloc ptr) m (MergeNode mloc ptr)
getMergeNode idx = do
  env <- get
  case Map.lookup idx (unrollMergeNodes env) of
    Just nd -> return nd

updateMergeNode :: Monad m => Integer -> MergeNode mloc ptr -> StateT (UnrollEnv mem mloc ptr) m ()
updateMergeNode idx nd = modify (\env -> env { unrollMergeNodes = Map.insert idx nd (unrollMergeNodes env) })

adjustMergeNode :: Monad m => Integer -> (MergeNode mloc ptr -> m (a,MergeNode mloc ptr)) -> StateT (UnrollEnv mem mloc ptr) m a
adjustMergeNode idx f = do
  nd <- getMergeNode idx
  (res,nd') <- lift $ f nd
  updateMergeNode idx nd'
  return res

adjustMergeNode' :: Monad m => Integer -> (MergeNode mloc ptr -> m (MergeNode mloc ptr)) -> StateT (UnrollEnv mem mloc ptr) m ()
adjustMergeNode' idx f = adjustMergeNode idx (\nd -> do
                                                 x <- f nd
                                                 return ((),x))

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
                                      , unrollMergeValues = Map.empty
                                      , unrollNextMergeNode = 0
                                      , unrollNextMergeValue = MergeValueRef 0
                                      , unrollGuards = []
                                      , unrollWatchpoints = []
                                      })
  Nothing -> error $ "Function "++fname++" not found in program graph."

spawnContexts :: Gr.Graph gr => Map String (ProgramGraph gr) -> UnrollContext mloc ptr -> [UnrollContext mloc ptr]
spawnContexts funs ctx
  = [ UnrollContext { unrollOrder = shiftOrder (==edgeTargetBlock edge) (unrollOrder ctx)
                    , unrollCtxFunction = unrollCtxFunction ctx
                    , unrollCtxArgs = unrollCtxArgs ctx
                    , currentMergeNodes = Map.delete (edgeTargetBlock edge,edgeTargetSubblock edge) (Map.union (nextMergeNodes ctx) (currentMergeNodes ctx))
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
                                                                            Just rval -> Map.insert ret_addr rval rvals,ret_loc) ]
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
                        -> UnrollContext mloc ptr
                        -> UnrollMonad mem mloc ptr (UnrollContext mloc ptr)
performUnrollmentCtx isFirst cfg program ctx
  | unrollmentDone ctx = return ctx
  | otherwise = do
    --trace ("Step: "++show ctx) (return ())
    ctx' <- stepUnrollCtx isFirst cfg program ctx
    performUnrollmentCtx False cfg program ctx'

unrollmentDone :: UnrollContext mloc ptr -> Bool
unrollmentDone ctx = List.null (realizationQueue ctx)

stepUnrollCtx :: (Gr.Graph gr,MemoryModel mem mloc ptr,Eq ptr,Enum ptr,Eq mloc,Enum mloc)
                 => Bool
                 -> UnrollConfig
                 -> Map String (ProgramGraph gr)
                 -> UnrollContext mloc ptr
                 -> UnrollMonad mem mloc ptr (UnrollContext mloc ptr)
stepUnrollCtx isFirst cfg program cur = case realizationQueue cur of
  (Edge blk sblk inc):rest -> do
    let mergeNode = Map.lookup (blk,sblk) (currentMergeNodes cur)
        mergeNodeCreate = unrollDoMerge cfg (unrollCtxFunction cur) blk sblk
        extensible = case mergeNode of
          Nothing -> mergeNodeCreate
          Just _ -> True
    case mergeNode of
      Just mn -> do
        rmn <- getMergeNode mn
        nprx <- lift $ varNamed "proxy"
        lift $ assert $ (mergeActivationProxy rmn) .==. (app or' ([ act | (_,act,_,_) <- inc ]++[nprx]))
        ninp <- foldlM (\cinp (_,act,mp,_) -> addMerge True act mp cinp) (mergeInputs rmn) inc
        updateMergeNode mn (rmn { mergeActivationProxy = nprx
                                , mergeInputs = ninp })
        mapM_ (\(blk,act,_,loc) -> do
                  env <- get
                  let (_,prx_ptr) = unrollProxies env
                  nmem <- lift $ connectLocation (unrollMemory env) prx_ptr act loc (mergeLoc rmn)
                  put $ env { unrollMemory = nmem }
                  case Map.lookup blk (mergePhis rmn) of
                    Nothing -> return ()
                    Just phi -> lift $ assert $ act .=>. (app and' $ phi:[ not' phi' | (blk',phi') <- Map.toList (mergePhis rmn), blk'/=blk ])
              ) inc
        return (cur { realizationQueue = rest })
      Nothing -> do
        let pgr = program!(unrollCtxFunction cur)
            node = (nodeMap pgr)!(blk,sblk)
            Just (_,name,_,instrs) = Gr.lab (programGraph pgr) node
            (info,realize) = preRealize (realizeInstructions instrs)
            blk_name = (case name of
                           Nothing -> show blk
                           Just rname -> rname)++"_"++show sblk
        (act,inp,inp',phis,start_loc,prev_locs,merge_node,mem_instr,mem_eqs)
          <- if mergeNodeCreate
             then (do
                      act_proxy <- lift $ varNamed $ "proxy_"++blk_name
                      act_static <- lift $ defConstNamed ("act_"++blk_name) (app or' ([ act | (_,act,_,_) <- inc ]++[act_proxy]))
                      inp <- sequence $ Map.mapWithKey (\vname (tp,name) -> case tp of
                                                           PointerType _ -> do
                                                             env <- get
                                                             put $ env { unrollNextPtr = succ $ unrollNextPtr env }
                                                             return $ Right $ unrollNextPtr env
                                                           _ -> do
                                                             let rname = case name of
                                                                   Nothing -> show vname
                                                                   Just n -> n
                                                             v <- lift $ valNew rname tp
                                                             return (Left v)) (rePossibleInputs info)
                      inp' <- createMergeValues True inp
                      inp'' <- foldlM (\cinp (_,act,mp,_) -> addMerge True act mp cinp) inp' inc
                      phis <- fmap Map.fromList $
                              mapM (\blk' -> do
                                       phi <- lift $ varNamed "phi"
                                       return (blk',phi)
                                   ) (Set.toList $ rePossiblePhis info)
                      mapM_ (\(blk,cond,_,_) -> case Map.lookup blk phis of
                                Nothing -> return ()
                                Just phi -> lift $ assert $ cond .=>. (app and' $ phi:[ not' phi' | (blk',phi') <- Map.toList phis, blk'/=blk ])
                            ) inc
                      loc <- do
                        env <- get
                        put $ env { unrollNextMem = succ $ unrollNextMem env }
                        return (unrollNextMem env)
                      env <- get
                      put $ env { unrollMergeNodes = Map.insert (unrollNextMergeNode env)
                                                     (MergeNode { mergeActivationProxy = act_proxy
                                                                , mergeInputs = inp''
                                                                , mergePhis = phis
                                                                , mergeLoc = loc }) (unrollMergeNodes env)
                                , unrollNextMergeNode = succ $ unrollNextMergeNode env }
                      return (act_static,inp,inp'',phis,loc,[loc],
                              Just $ unrollNextMergeNode env,[],[ (act',loc',loc) | (_,act',_,loc') <- inc ]))
             else (do
                      mergedInps <- mergeValueMaps extensible [ (cond,mp) | (_,cond,mp,_) <- inc ]
                      act <- lift $ defConstNamed ("act_"++(unrollCtxFunction cur)++"_"++blk_name) (app or' [ act | (_,act,_,_) <- inc ])
                      inp <- mapM getMergeValue (Map.intersection mergedInps (rePossibleInputs info))
                      (start_loc,prev_locs,mphis) <- case inc of
                        (_,_,_,loc'):inc' -> if all (\(_,_,_,loc'') -> loc'==loc'') inc'
                                             then return (loc',[loc'],[])
                                             else (do
                                                      env <- get
                                                      let loc'' = unrollNextMem env
                                                      put $ env { unrollNextMem = succ loc'' }
                                                      return (loc'',[ loc''' | (_,_,_,loc''') <- inc ],[MIPhi [ (act'',loc''') | (_,act'',_,loc''') <- inc ] loc'']))
                      phis <- mapM (\blk' -> case [ cond | (blk'',cond,_,_) <- inc, blk''==blk' ] of
                                       [] -> return Nothing
                                       xs -> do
                                         phi <- lift $ defConstNamed "phi" (app or' xs)
                                         return $ Just (blk',phi)
                                   ) (Set.toList $ rePossiblePhis info)
                      return (act,inp,mergedInps,
                              Map.fromList $ catMaybes phis,start_loc,prev_locs,Nothing,
                              mphis,[]))
        env <- get
        (fin,nst,outp) <- lift $ postRealize (RealizationEnv { reFunction = unrollCtxFunction cur
                                                             , reBlock = blk
                                                             , reSubblock = sblk
                                                             , reActivation = act
                                                             , reGlobals = unrollGlobals env
                                                             , reArgs = unrollCtxArgs cur
                                                             , reInputs = inp
                                                             , rePhis = phis
                                                             , reStructs = unrollStructs cfg })
                          start_loc
                          (unrollNextMem env)
                          (unrollNextPtr env)
                          realize
        put $ env { unrollNextPtr = reNextPtr nst
                  , unrollNextMem = reNextMemLoc nst }
        outp' <- createMergeValues False (reLocals nst)
        let new_vars = Map.union outp' inp'
            outEdges = case fin of
              Jump trgs -> [ Edge { edgeTargetBlock = trg
                                  , edgeTargetSubblock = 0
                                  , edgeConds = [(blk,act .&&. cond,new_vars,reCurMemLoc nst)]
                                  } | (cond,trg) <- trgs ]
              _ -> []
            outCalls = case fin of
              Call fname args ret -> [(fname,args,new_vars,unrollCtxArgs cur,reCurMemLoc nst,act,blk,sblk+1,ret)]
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
        outReturns <- case fin of
          Return (Just val) -> do
            env <- get
            put $ env { unrollMergeValues = Map.insert (unrollNextMergeValue env) (MergedValue False val) (unrollMergeValues env)
                      , unrollNextMergeValue = succ $ unrollNextMergeValue env }
            return [(act,Just $ unrollNextMergeValue env,reCurMemLoc nst)]
          Return Nothing -> return [(act,Nothing,reCurMemLoc nst)]
          _ -> return []
        if isFirst
          then (do
                   env <- get
                   let (_,prx) = unrollProxies env
                   nmem <- lift $ makeEntry prx (unrollMemory env) start_loc
                   put $ env { unrollMemory = nmem })
          else return ()
        case mem_instr++(reMemInstrs outp) of
          [] -> return ()
          xs -> do
            env <- get
            nmem <- lift $ addProgram (unrollMemory env) act prev_locs xs
            put $ env { unrollMemory = nmem }
        mapM_ (\(cond,src,trg) -> do
                  env <- get
                  let (_,prx) = unrollProxies env
                  nmem <- lift $ connectLocation (unrollMemory env) prx cond src trg
                  put $ env { unrollMemory = nmem }
              ) mem_eqs
        modify (\env -> env { unrollGuards = (reGuards outp)++(unrollGuards env)
                            , unrollWatchpoints = (reWatchpoints outp)++(unrollWatchpoints env)
                            })
        return $ cur { realizationQueue = nqueue
                     , outgoingEdges = nout
                     , calls = outCalls ++ (calls cur)
                     , returns = outReturns ++ (returns cur)
                     , nextMergeNodes = case merge_node of
                       Nothing -> nextMergeNodes cur
                       Just mn -> Map.insert (blk,sblk) mn (nextMergeNodes cur) }

allProxies :: UnrollEnv mem mloc ptr -> [SMTExpr Bool]
allProxies env = [ mergeActivationProxy nd | nd <- Map.elems (unrollMergeNodes env) ]
