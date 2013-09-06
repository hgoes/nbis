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
import Circuit
import InstrDesc

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
import Prelude hiding (sequence,mapM,mapM_,foldl,all,concat)
import Data.Ord
import Data.Maybe (catMaybes)
import Control.Monad.Trans (lift,liftIO)
import Control.Monad.State.Strict (get,put,modify,StateT,runStateT)
import Control.Monad.ST
import Data.IORef
import System.Random

data MergeNode mloc ptr = MergeNode { mergeActivationProxy :: SMTExpr Bool
                                    , mergeInputs :: Map (Either (Ptr Argument) (Ptr Instruction)) (MergeValueRef ptr)
                                    , mergePhis :: Map (Ptr BasicBlock) (SMTExpr Bool)
                                    , mergeLoc :: mloc
                                    }

data NodeId = NodeId { nodeIdFunction :: String
                     , nodeIdBlock :: Ptr BasicBlock
                     , nodeIdSubblock :: Integer
                     , nodeIdCallStack :: Maybe (NodeId,Ptr Instruction)
                     } deriving (Eq,Ord,Show)

type MergeValueRef ptr = IORef (MergeValue ptr)

data MergeValue ptr = MergedValue Bool (Either Val ptr)
                    | UnmergedValue String Bool [(MergeValueRef ptr,SMTExpr Bool)]

data UnrollEnv mem mloc ptr = UnrollEnv { unrollNextMem :: mloc
                                        , unrollNextPtr :: ptr
                                        , unrollGlobals :: Map (Ptr GlobalVariable) ptr
                                        , unrollMemory :: mem
                                        , unrollMergeNodes :: Map Integer (MergeNode mloc ptr)
                                        , unrollNextMergeNode :: Integer
                                        , unrollGuards :: [Guard]
                                        , unrollWatchpoints :: [Watchpoint]
                                        }

type ValueMap ptr = Map (Either (Ptr Argument) (Ptr Instruction)) (MergeValueRef ptr)

data UnrollContext mloc ptr = UnrollContext { unrollOrder :: [(String,Ptr BasicBlock,Integer)]
                                            , currentMergeNodes :: Map NodeId Integer
                                            , nextMergeNodes :: Map NodeId Integer
                                            , realizationQueue :: [Edge mloc ptr]
                                            , outgoingEdges :: [Edge mloc ptr]
                                            }

data Edge mloc ptr = Edge { edgeTarget :: NodeId
                          , edgeConds :: [(String,Ptr BasicBlock,Integer,SMTExpr Bool,[ValueMap ptr],mloc)]
                          }

data ReturnInfo ptr = ReturnCreate { returnCreateFun :: String
                                   , returnCreateBlk :: Ptr BasicBlock
                                   , returnCreateSBlk :: Integer
                                   , returnCreateInputs :: ValueMap ptr
                                   , returnCreateArgs :: Map (Ptr Argument) (Either Val ptr)
                                   , returnCreateMergeNodes :: Map (Ptr BasicBlock,Integer) Integer
                                   }
                    | ReturnMerge { returnMergeNode :: Integer
                                  }

data UnrollConfig mloc ptr = UnrollCfg { unrollDoMerge :: String -> Ptr BasicBlock -> Integer -> Bool
                                       , unrollStructs :: Map String [TypeDesc]
                                       , unrollTypes :: Set TypeDesc
                                       , unrollFunctions :: Map String (UnrollFunInfo mloc ptr)
                                       , unrollCfgGlobals :: Map (Ptr GlobalVariable) (TypeDesc, Maybe MemContent)
                                       , unrollBlockOrder :: [(String,Ptr BasicBlock,Integer)]
                                       }

data UnrollFunInfo mloc ptr = UnrollFunInfo { unrollFunInfoBlocks :: Map (Ptr BasicBlock,Integer) (Maybe String,RealizationInfo,RealizationMonad mloc ptr (BlockFinalization ptr),Set (Ptr Instruction))
                                            , unrollFunInfoStartBlock :: (Ptr BasicBlock,Integer)
                                            , unrollFunInfoArguments :: [(Ptr Argument, TypeDesc)]
                                            }

type UnrollMonad mem mloc ptr = StateT (UnrollEnv mem mloc ptr) SMT

defaultConfig :: (Eq ptr,Enum ptr,Enum mloc) => String -> ProgDesc -> UnrollConfig mloc ptr
defaultConfig entr desc = mergePointConfig entr desc safeMergePoints

randomMergePointConfig :: (Eq ptr,Enum ptr,Enum mloc,RandomGen g) => String -> ProgDesc -> g -> UnrollConfig mloc ptr
randomMergePointConfig entr desc gen = mergePointConfig entr desc (randomMergePoints gen)

mergePointConfig :: (Eq ptr,Enum ptr,Enum mloc) => String -> ProgDesc -> ([[Gr.Node]] -> [Gr.Node]) -> UnrollConfig mloc ptr
mergePointConfig entry (funs,globs,alltps,structs) select
  = UnrollCfg { unrollStructs = structs
              , unrollTypes = alltps
              , unrollFunctions = ext_funs
              , unrollDoMerge = \fname blk sblk -> Set.member (fname,blk,sblk) mergePoints
              , unrollCfgGlobals = globs
              , unrollBlockOrder = order
              }
  where
    ext_funs = fmap (\(args,_,blks,_,_) -> let (start_blk,_,_) = head blks
                                               blk_mp = Map.fromList [ (key,(realize,nd))
                                                                     | ((key,realize),nd) <- zip [ ((blk,sblk),(name,info,real))
                                                                                                 | (blk,name,subs) <- blks, (sblk,instrs) <- zip [0..] subs
                                                                                                 , let (info,real) = preRealize $ realizeInstructions instrs ]
                                                                                             [0..] ]
                                               rblk_mp = fmap fst blk_mp
                                               reach_info = reachabilityInfo rblk_mp
                                               defs = definitionMap rblk_mp
                                               trans_mp = Map.foldlWithKey (\cmp blk (_,info,_)
                                                                            -> let Just reach = Map.lookup blk reach_info
                                                                               in foldl (\cmp instr -> let Just def_blk = Map.lookup instr defs
                                                                                                           trans = case Map.lookup def_blk reach of
                                                                                                             Just t -> t
                                                                                                             Nothing -> Set.empty
                                                                                                       in foldl (\cmp trans_blk -> Map.insertWith Set.union trans_blk (Set.singleton instr) cmp
                                                                                                                ) cmp trans
                                                                                        ) cmp (Map.keys $ rePossibleInputs info)
                                                                           ) (fmap (const Set.empty) rblk_mp) rblk_mp
                                           in UnrollFunInfo { unrollFunInfoBlocks = Map.intersectionWith (\(name,info,realize) trans -> (name,info,realize,trans)) rblk_mp trans_mp
                                                            , unrollFunInfoStartBlock = (start_blk,0)
                                                            , unrollFunInfoArguments = args
                                                            }
                    ) funs
    blk_mp = Map.fromList [ ((fn,blk,sblk),(nd,instrs))
                          | (fn,(args,_,blks,_,_)) <- Map.toList funs
                          , (blk,name,subs) <- blks
                          , (sblk,instrs) <- zip [0..] subs
                          | nd <- [0..] ]
    prog_gr = Gr.mkGraph [ (nd,key) | (key,(nd,_)) <- Map.toList blk_mp ]
              (concat [ [ (nd,nd_nxt,())
                        | nxt_blk <- case last instrs of
                             ITerminator (IBr to) -> [to]
                             ITerminator (IBrCond _ ifT ifF) -> [ifT,ifF]
                             ITerminator (ISwitch _ def cases) -> def:[ blk | (_,blk) <- cases ]
                             _ -> []
                        , let Just (nd_nxt,_) = Map.lookup (fun,nxt_blk,0) blk_mp ] ++
                        [ (nd,nd_nxt,())
                        | nxt_fun <- case last instrs of
                             ITerminator (ICall _ (Operand { operandDesc = ODFunction _ f _ }) _) -> [f]
                             _ -> []
                        , let Just (_,_,(start_blk,_,_):_,_,_) = Map.lookup nxt_fun funs
                        , let Just (nd_nxt,_) = Map.lookup (nxt_fun,start_blk,0) blk_mp ] ++
                        [ (nd_from,nd_to,())
                        | nxt_fun <- case last instrs of
                             ITerminator (ICall _ (Operand { operandDesc = ODFunction _ f _ }) _) -> [f]
                             _ -> []
                        , let Just (nd_to,_) = Map.lookup (fun,blk,sblk+1) blk_mp
                        , nd_from <- [ nd | ((fun',_,_),(nd,instrs)) <- Map.toList blk_mp, case last instrs of
                                          ITerminator (IRet _) -> True
                                          ITerminator IRetVoid -> True
                                          _ -> False ] ]
                      | ((fun,blk,sblk),(nd,instrs)) <- Map.toList blk_mp ]) :: Gr.Gr (String,Ptr BasicBlock,Integer) ()
    Just (_,_,(start_blk,_,_):_,_,_) = Map.lookup entry funs
    Just (start_nd,_) = Map.lookup (entry,start_blk,0) blk_mp
    [dffTree] = Gr.dff [start_nd] prog_gr
    order = reverse $ fmap (\nd -> let Just inf = Gr.lab prog_gr nd in inf) $ Gr.postorder dffTree
    mergePoints = Set.fromList $ fmap (\nd -> let Just inf = Gr.lab prog_gr nd in inf) $ select (possibleMergePoints prog_gr)

reachabilityInfo :: Map (Ptr BasicBlock,Integer) (Maybe String,RealizationInfo,RealizationMonad mloc ptr (BlockFinalization ptr))
                    -> Map (Ptr BasicBlock,Integer) (Map (Ptr BasicBlock,Integer) (Set (Ptr BasicBlock,Integer)))
reachabilityInfo info = Map.foldlWithKey (\cmp entr (_,info',_)
                                          -> let cmp1 = foldl (\cmp succ -> addReach cmp entr (succ,0) Set.empty) cmp (reSuccessors info')
                                                 cmp2 = if Set.null (reCalls info')
                                                        then cmp1
                                                        else addReach cmp1 entr (fst entr,snd entr+1) Set.empty
                                             in cmp2
                                         ) Map.empty info
  where
    addReach mp src trg via
      = let r = case Map.lookup trg mp of
              Just r -> r
              Nothing -> Map.empty
            cvia = Map.lookup src r
            nvia = case cvia of
              Nothing -> via
              Just cvia' -> Set.union via cvia'
            nmp = Map.insert trg (Map.insert src nvia r) mp
            info' = case Map.lookup trg info of
              Just (_,i,_) -> i
              Nothing -> error $ "Unable to find block informations for "++show trg++" "++show (fmap (\(name,inf,_) -> (name,inf)) info)
            new_info = case cvia of
              Nothing -> True
              Just cvia' -> Set.size nvia > Set.size cvia'
        in if new_info
           then (if src==trg
                 then nmp
                 else (let nmp1 = foldl (\cmp succ -> addReach cmp src (succ,0) (Set.insert trg nvia)) nmp (reSuccessors info')
                           nmp2 = if Set.null (reCalls info')
                                  then nmp1
                                  else addReach nmp1 src (fst trg,snd trg+1) (Set.insert trg nvia)
                       in nmp2))
           else mp

definitionMap :: Map (Ptr BasicBlock,Integer) (Maybe String,RealizationInfo,RealizationMonad mloc ptr (BlockFinalization ptr))
              -> Map (Ptr Instruction) (Ptr BasicBlock,Integer)
definitionMap = Map.foldlWithKey (\cmp blk (_,info,_) -> let cmp1 = foldl (\cmp (_,ret_addr) -> Map.insert ret_addr (fst blk,snd blk+1) cmp) cmp (reCalls info)
                                                             cmp2 = foldl (\cmp instr -> Map.insert instr blk cmp) cmp1 (reLocallyDefined info)
                                                         in cmp2
                                 ) Map.empty

mergeValueMaps :: Bool -> [(SMTExpr Bool,ValueMap ptr)] -> UnrollMonad mem mloc ptr (ValueMap ptr)
mergeValueMaps extensible mps = do
  let merge_map = Map.unionsWith (++) $ fmap (\(c,mp) -> fmap (\ref -> [(ref,c)]) mp) mps
  sequence $ Map.mapWithKey (\instr entrs -> liftIO $ newIORef (UnmergedValue "inp" extensible entrs)
                            ) merge_map

mergeValueStacks :: Bool -> [(SMTExpr Bool,[ValueMap ptr])] -> UnrollMonad mem mloc ptr [ValueMap ptr]
mergeValueStacks _ ((_,[]):_) = return []
mergeValueStacks extensible stacks = do
  st_head <- mergeValueMaps extensible (fmap (\(c,x:xs) -> (c,x)) stacks)
  st_tail <- mergeValueStacks extensible (fmap (\(c,x:xs) -> (c,xs)) stacks)
  return $ st_head:st_tail

addMerge :: (MemoryModel mem mloc ptr,Enum ptr) => Bool -> SMTExpr Bool -> ValueMap ptr -> ValueMap ptr -> UnrollMonad mem mloc ptr (ValueMap ptr)
addMerge extensible cond mp_new mp_old
  = mapM (\entr -> case entr of
             Left (Left x) -> liftIO $ newIORef (UnmergedValue "inp" extensible [(x,cond)])
             Left (Right x) -> return x
             Right (new,old) -> do
               mergeValues old new cond
               return old) $
    Map.unionWith (\(Left (Left x)) (Left (Right y)) -> Right (x,y)) (fmap (Left . Left) mp_new) (fmap (Left . Right) mp_old)

dumpMergeValue :: MergeValueRef ptr -> UnrollMonad mem mloc ptr String
dumpMergeValue ref = do
  res <- liftIO $ readIORef ref
  case res of
    MergedValue ext v -> return $ "Merged "++
                         (if ext then "extensible " else "")++
                         (case v of
                             Left v' -> show v'
                             Right _ -> "pointer")
    UnmergedValue name ext vals -> do
      rvals <- mapM (\(ref,cond) -> do
                        rval <- dumpMergeValue ref
                        return $ show cond++" ~> "++rval) vals
      return $ "Unmerged "++
        (if ext then "extensible " else "")++
        ("{"++List.intercalate ", " rvals++"}")

checkLoops' :: Foldable t => t (MergeValueRef ptr) -> UnrollMonad mem mloc ptr ()
checkLoops' = fmap (const ()) . foldlM (checkLoops []) []

checkLoops :: [MergeValueRef ptr] -> [MergeValueRef ptr] -> MergeValueRef ptr -> UnrollMonad mem mloc ptr [MergeValueRef ptr]
checkLoops visited checked ref
  | List.elem ref visited = error "Loop detected"
  | List.elem ref checked = return checked
  | otherwise = do
    res <- liftIO $ readIORef ref
    case res of
      MergedValue _ _ -> return (ref:checked)
      UnmergedValue _ _ vals -> foldlM (checkLoops (ref:visited)) (ref:checked) (fmap fst vals)

getMergeValue :: (MemoryModel mem mloc ptr,Enum ptr) => MergeValueRef ptr -> UnrollMonad mem mloc ptr (Either Val ptr)
getMergeValue ref = do
  res <- liftIO $ readIORef ref
  case res of
    MergedValue _ v -> return v
    UnmergedValue name extensible (refs@((ref',_):_)) -> do
      val <- getMergeValue ref'
      ret <- case val of
        Left v -> if extensible
                  then (do
                           nval <- lift $ valNewSameType name v
                           mapM_ (\(ref,cond) -> do
                                     Left val <- getMergeValue ref
                                     lift $ assert $ cond .=>. (valEq nval val)) refs
                           return $ Left nval)
                  else (do
                           lst <- mapM (\(ref,cond) -> do
                                           Left val <- getMergeValue ref
                                           return (val,cond)) refs
                           nval <- case lst of
                             [(v,_)] -> return v
                             _ -> lift $ valCopy name (valSwitch lst)
                           return $ Left nval)
        Right p -> do
          env <- get
          let nptr = unrollNextPtr env
          put $ env { unrollNextPtr = succ nptr }
          mapM_ (\(ref,cond) -> do
                    Right ptr <- getMergeValue ref
                    env <- get
                    let (prx,_) = unrollProxies env
                    nmem <- lift $ connectPointer (unrollMemory env) prx cond ptr nptr
                    put $ env { unrollMemory = nmem }
                ) refs
          return (Right nptr)
      liftIO $ writeIORef ref (MergedValue extensible ret)
      return ret

mergeValues :: (MemoryModel mem mloc ptr,Enum ptr) => MergeValueRef ptr -> MergeValueRef ptr -> SMTExpr Bool -> UnrollMonad mem mloc ptr ()
mergeValues ref val cond = do
  mn <- liftIO $ readIORef ref
  nmn <- mergeValue val cond mn
  liftIO $ writeIORef ref nmn

mergeValue :: (MemoryModel mem mloc ptr,Enum ptr) => MergeValueRef ptr -> SMTExpr Bool -> MergeValue ptr -> UnrollMonad mem mloc ptr (MergeValue ptr)
mergeValue val cond (UnmergedValue name extensible uvals)
  = if extensible
    then return $ UnmergedValue name extensible ((val,cond):uvals)
    else error $ "Merging into non-extensible value "++name
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

createMergeValues :: Bool -> Map (Either (Ptr Argument) (Ptr Instruction)) (Either Val ptr) -> UnrollMonad mem mloc ptr (ValueMap ptr)
createMergeValues extensible
  = mapM (\val -> liftIO $ newIORef (MergedValue extensible val))

enqueueEdge :: [(String,Ptr BasicBlock,Integer)] -> Edge mloc ptr -> [Edge mloc ptr] -> [Edge mloc ptr]
enqueueEdge = insertWithOrder (\x y -> if nodeIdFunction (edgeTarget x) == nodeIdFunction (edgeTarget y) &&
                                          nodeIdBlock (edgeTarget x) == nodeIdBlock (edgeTarget y) &&
                                          nodeIdSubblock (edgeTarget x) == nodeIdSubblock (edgeTarget y)
                                       then Just $ comparing (nodeIdCallStack . edgeTarget) x y
                                       else Nothing)
              (\e1 e2 -> e1 { edgeConds = (edgeConds e1)++(edgeConds e2) }) (\x -> (nodeIdFunction $ edgeTarget x,nodeIdBlock $ edgeTarget x,nodeIdSubblock $ edgeTarget x))

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

initOrder :: Gr.Graph gr => ProgramGraph gr -> [(Ptr BasicBlock,Integer)]
initOrder pgr = trace ("ORDER: "++show order) order
  where
    (start_node,_) = Gr.nodeRange (programGraph pgr)
    [dffTree] = Gr.dff [start_node] (programGraph pgr)
    order = reverse $ fmap (\nd -> let Just (blk,_,sblk,_) = Gr.lab (programGraph pgr) nd in (blk,sblk)) $ Gr.postorder dffTree

startingContext :: (MemoryModel mem Integer Integer)
                   => UnrollConfig Integer Integer -> String
                   -> SMT (UnrollContext Integer Integer,UnrollEnv mem Integer Integer)
startingContext cfg fname = case Map.lookup fname (unrollFunctions cfg) of
  Just info -> do
    let order = unrollBlockOrder cfg
        (blk,sblk) = unrollFunInfoStartBlock info
        ((cptr,prog),globs') = mapAccumL (\(ptr',prog') (tp,cont) 
                                          -> ((succ ptr',(ptr',tp,cont):prog'),ptr')
                                         ) (0,[]) (unrollCfgGlobals cfg)
    mem <- memNew (Proxy::Proxy Integer) (unrollTypes cfg) (unrollStructs cfg) [ (ptr,tp,cont) | (ptr,PointerType tp,cont) <- prog ]
    return (UnrollContext { unrollOrder = order
                          , currentMergeNodes = Map.empty
                          , nextMergeNodes = Map.empty
                          , realizationQueue = [Edge { edgeTarget = NodeId { nodeIdFunction = fname
                                                                           , nodeIdBlock = blk
                                                                           , nodeIdSubblock = sblk
                                                                           , nodeIdCallStack = Nothing }
                                                     , edgeConds = [(fname,nullPtr,0,constant True,[Map.empty],0)]
                                                     }]
                          , outgoingEdges = []
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

spawnContexts :: UnrollConfig mloc ptr -> UnrollContext mloc ptr -> [UnrollContext mloc ptr]
spawnContexts cfg ctx
  = [ UnrollContext { unrollOrder = norder
                    , currentMergeNodes = Map.filterWithKey (\key _ -> Set.member (nodeIdFunction key,nodeIdBlock key,nodeIdSubblock key) suitableMerges)
                                          (Map.union (nextMergeNodes ctx) (currentMergeNodes ctx))
                    , nextMergeNodes = Map.empty
                    , realizationQueue = [edge]
                    , outgoingEdges = []
                    }
    | edge <- outgoingEdges ctx
    , let norder = shiftOrder (==(nodeIdFunction $ edgeTarget edge,nodeIdBlock $ edgeTarget edge,nodeIdSubblock $ edgeTarget edge)) (unrollOrder ctx)
    , let suitableMerges = suitableMergePoints (Set.fromList [ (fun,blk,sblk) | (fun,blk,sblk,_,_,_) <- edgeConds edge ]) (unrollOrder ctx)
    ]
  where
    suitableMergePoints :: Set (String,Ptr BasicBlock,Integer) -> [(String,Ptr BasicBlock,Integer)] -> Set (String,Ptr BasicBlock,Integer)
    suitableMergePoints refs order
      | Set.null refs = Set.fromList order
      | otherwise = case order of
        [] -> Set.empty
        x:xs -> if Set.member x refs
                then suitableMergePoints (Set.delete x refs) xs
                else suitableMergePoints refs xs

performUnrollmentCtx :: (MemoryModel mem mloc ptr,Eq ptr,Enum ptr,Eq mloc,Enum mloc,Show ptr,Show mloc)
                        => Bool
                        -> UnrollConfig mloc ptr
                        -> UnrollContext mloc ptr
                        -> UnrollMonad mem mloc ptr (UnrollContext mloc ptr)
performUnrollmentCtx isFirst cfg ctx
  | unrollmentDone ctx = return ctx
  | otherwise = do
    --trace ("Step: "++show ctx) (return ())
    ctx' <- stepUnrollCtx isFirst cfg ctx
    performUnrollmentCtx False cfg ctx'

unrollmentDone :: UnrollContext mloc ptr -> Bool
unrollmentDone ctx = List.null (realizationQueue ctx)

stepUnrollCtx :: (MemoryModel mem mloc ptr,Eq ptr,Enum ptr,Eq mloc,Enum mloc)
                 => Bool
                 -> UnrollConfig mloc ptr
                 -> UnrollContext mloc ptr
                 -> UnrollMonad mem mloc ptr (UnrollContext mloc ptr)
stepUnrollCtx isFirst cfg cur = case realizationQueue cur of
  (Edge trg inc):rest -> do
    let mergeNode = Map.lookup trg (currentMergeNodes cur)
        mergeNodeCreate = unrollDoMerge cfg (nodeIdFunction trg) (nodeIdBlock trg) (nodeIdSubblock trg)
        extensible = case mergeNode of
          Nothing -> mergeNodeCreate
          Just _ -> True
    case mergeNode of
      Just mn -> do
        rmn <- getMergeNode mn
        nprx <- lift $ varNamed "proxy"
        lift $ assert $ (mergeActivationProxy rmn) .==. (app or' ([ act | (_,_,_,act,_,_) <- inc ]++[nprx]))
        ninp <- foldlM (\cinp (_,_,_,act,mp,_) -> do
                           --mapM dumpMergeValue cinp >>= liftIO . print
                           addMerge True act (head mp) cinp) (mergeInputs rmn) inc
        --mapM dumpMergeValue ninp >>= liftIO . print
        --checkLoops' ninp
        updateMergeNode mn (rmn { mergeActivationProxy = nprx
                                , mergeInputs = ninp })
        mapM_ (\(fun,blk,sblk,act,_,loc) -> do
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
        let pgr = (unrollFunctions cfg)!(nodeIdFunction trg)
            (name,info,realize,trans) = (unrollFunInfoBlocks pgr)!(nodeIdBlock trg,nodeIdSubblock trg)
            blk_name = (case name of
                           Nothing -> show (nodeIdBlock trg)
                           Just rname -> rname)++"_"++show (nodeIdSubblock trg)
        (act,inp,inp',inp_rest,phis,start_loc,prev_locs,merge_node,mem_instr,mem_eqs)
          <- if mergeNodeCreate
             then (do
                      act_proxy <- lift $ varNamed $ "proxy_"++blk_name
                      act_static <- lift $ defConstNamed ("act_"++blk_name) (app or' ([ act | (_,_,_,act,_,_) <- inc ]++[act_proxy]))
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
                                                             return (Left v)) (Map.mapKeys Right $ rePossibleInputs info)
                      inp' <- createMergeValues True inp
                      inp'' <- foldlM (\cinp (_,_,_,act,mp,_) -> addMerge True act (head mp) cinp) inp' inc
                      inp_rest <- mergeValueStacks True [ (act,stack) | (_,_,_,act,_:stack,_) <- inc ]
                      phis <- fmap Map.fromList $
                              mapM (\blk' -> do
                                       phi <- lift $ varNamed "phi"
                                       return (blk',phi)
                                   ) (Set.toList $ rePossiblePhis info)
                      mapM_ (\(_,blk,_,cond,_,_) -> case Map.lookup blk phis of
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
                      return (act_static,inp,inp'',inp_rest,phis,loc,[loc],
                              Just $ unrollNextMergeNode env,[],[ (act',loc',loc) | (_,_,_,act',_,loc') <- inc ]))
             else (do
                      mergedInps <- mergeValueMaps extensible [ (cond,head mp) | (_,_,_,cond,mp,_) <- inc ]
                      mergedRest <- mergeValueStacks extensible [ (cond,tail mp) | (_,_,_,cond,mp,_) <- inc ]
                      act <- lift $ defConstNamed ("act_"++(nodeIdFunction trg)++"_"++blk_name) (app or' [ act | (_,_,_,act,_,_) <- inc ])
                      inp <- mapM getMergeValue (Map.intersection mergedInps $
                                                 Map.union (fmap (const ()) $ Map.mapKeys Right (rePossibleInputs info))
                                                 (Map.fromList [ (Left k,()) | k <- Set.toList (rePossibleArgs info) ]))
                      (start_loc,prev_locs,mphis) <- case inc of
                        (_,_,_,_,_,loc'):inc' -> if all (\(_,_,_,_,_,loc'') -> loc'==loc'') inc'
                                                 then return (loc',[loc'],[])
                                                 else (do
                                                      env <- get
                                                      let loc'' = unrollNextMem env
                                                      put $ env { unrollNextMem = succ loc'' }
                                                      return (loc'',[ loc''' | (_,_,_,_,_,loc''') <- inc ],[MIPhi [ (act'',loc''') | (_,_,_,act'',_,loc''') <- inc ] loc'']))
                      phis <- mapM (\blk' -> case [ cond | (_,blk'',_,cond,_,_) <- inc, blk''==blk' ] of
                                       [] -> return Nothing
                                       xs -> do
                                         phi <- lift $ defConstNamed "phi" (app or' xs)
                                         return $ Just (blk',phi)
                                   ) (Set.toList $ rePossiblePhis info)
                      return (act,inp,mergedInps,mergedRest,
                              Map.fromList $ catMaybes phis,start_loc,prev_locs,Nothing,
                              mphis,[]))
        env <- get
        (fin,nst,outp) <- lift $ postRealize (RealizationEnv { reFunction = nodeIdFunction trg
                                                             , reBlock = nodeIdBlock trg
                                                             , reSubblock = nodeIdSubblock trg
                                                             , reActivation = act
                                                             , reGlobals = unrollGlobals env
                                                             , reInputs = inp
                                                             , rePhis = phis
                                                             , reStructs = unrollStructs cfg })
                          start_loc
                          (unrollNextMem env)
                          (unrollNextPtr env)
                          realize
        put $ env { unrollNextPtr = reNextPtr nst
                  , unrollNextMem = reNextMemLoc nst }
        outp' <- createMergeValues False (Map.mapKeys Right $ reLocals nst)
        let trans_vars = Map.fromList [ (Right var,()) | var <- Set.toList trans ]
            arg_vars = Map.filterWithKey (\k _ -> case k of
                                             Left _ -> True
                                             _ -> False
                                         ) inp'
            new_vars = Map.union (Map.union outp' (Map.intersection inp' trans_vars)) arg_vars
        outEdges <- case fin of
          Jump trgs -> return [ Edge { edgeTarget = NodeId { nodeIdFunction = nodeIdFunction trg
                                                           , nodeIdBlock = trg_blk
                                                           , nodeIdSubblock = 0
                                                           , nodeIdCallStack = nodeIdCallStack trg }
                                     , edgeConds = [(nodeIdFunction trg,nodeIdBlock trg,nodeIdSubblock trg,act .&&. cond,new_vars:inp_rest,reCurMemLoc nst)]
                                     } | (cond,trg_blk) <- trgs ]
          Call fname args ret -> do
            let fun_info = (unrollFunctions cfg)!fname
                (start_blk,start_sblk) = unrollFunInfoStartBlock fun_info
            arg_vars <- createMergeValues False $ Map.fromList [ (Left arg_ptr,arg) | ((arg_ptr,tp),arg) <- zip (unrollFunInfoArguments fun_info) args ]
            return [ Edge { edgeTarget = NodeId { nodeIdFunction = fname
                                                , nodeIdBlock = start_blk
                                                , nodeIdSubblock = start_sblk
                                                , nodeIdCallStack = Just (trg { nodeIdSubblock = succ $ nodeIdSubblock trg },ret)
                                                }
                          , edgeConds = [(nodeIdFunction trg,nodeIdBlock trg,nodeIdSubblock trg,act,arg_vars:new_vars:inp_rest,reCurMemLoc nst)]
                          } ]
          Return rval -> case nodeIdCallStack trg of
            Just (prev,trg_instr) -> do
              nvars <- case rval of
                Nothing -> return inp_rest
                Just val -> case inp_rest of
                  x:xs -> do
                    val' <- liftIO $ newIORef (MergedValue False val)
                    return $ (Map.insert (Right trg_instr) val' x):xs
              return [ Edge { edgeTarget = prev
                            , edgeConds = [(nodeIdFunction trg,nodeIdBlock trg,nodeIdSubblock trg,act,nvars,reCurMemLoc nst)]
                            } ]
            Nothing -> return []
        let (nqueue,nout) = foldl (\(cqueue,cout) edge -> case compareWithOrder (unrollOrder cur)
                                                               (nodeIdFunction trg,
                                                                nodeIdBlock trg,
                                                                nodeIdSubblock trg)
                                                               (nodeIdFunction $ edgeTarget edge,
                                                                nodeIdBlock $ edgeTarget edge,
                                                                nodeIdSubblock $ edgeTarget edge) of
                                      LT -> (enqueueEdge (unrollOrder cur) edge cqueue,cout)
                                      _ -> (cqueue,enqueueEdge (unrollOrder cur) edge cout)
                                  ) (rest,outgoingEdges cur) outEdges
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
                     , nextMergeNodes = case merge_node of
                       Nothing -> nextMergeNodes cur
                       Just mn -> Map.insert trg mn (nextMergeNodes cur) }

allProxies :: UnrollEnv mem mloc ptr -> [SMTExpr Bool]
allProxies env = [ mergeActivationProxy nd | nd <- Map.elems (unrollMergeNodes env) ]
