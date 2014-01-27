{-# LANGUAGE FlexibleContexts #-}
module Unrollment where

import Language.SMTLib2
import Language.SMTLib2.Strategy
import LLVM.FFI.BasicBlock (BasicBlock)
import LLVM.FFI.Instruction (Instruction)
import LLVM.FFI.Value
import LLVM.FFI.Constant
import LLVM.FFI.Loop

import Value
import Realization
import Program
import Analyzation
import TypeDesc
import MemoryModel
import Circuit
import InstrDesc
import SMTHelper

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Map.Debug ((!))
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List
import Foreign.Ptr
import qualified Data.Graph.Inductive as Gr
import Data.Traversable
import Data.Foldable
import Data.Proxy
import Prelude hiding (sequence,mapM,mapM_,foldl,all,concat,any,minimum,sum)
import Data.Ord
import Data.Maybe (catMaybes,mapMaybe)
import Control.Monad.Trans (lift,liftIO)
import Control.Monad.State.Strict (get,put,modify,StateT,runStateT)
import Data.IORef
import System.Random
import Data.Tree
import Data.Monoid

import Debug.Trace

class UnrollInfo a where
  type UnrollNodeInfo a
  unrollInfoInit :: a
  unrollInfoNewNode :: a -> NodeId -> Either String Integer -> Bool -> (UnrollNodeInfo a,a)
  unrollInfoConnect :: a -> UnrollNodeInfo a -> UnrollNodeInfo a -> a

data MergeNode a mloc ptr = MergeNode { mergeActivationProxy :: SMTExpr Bool
                                      , mergeInputs :: [Map (Either (Ptr Argument) (Ptr Instruction)) (MergeValueRef ptr)]
                                      , mergePhis :: Map (Ptr BasicBlock) (SMTExpr Bool)
                                      , mergeLoc :: mloc
                                      , mergeUnrollInfo :: UnrollNodeInfo a
                                      }

data NodeId = NodeId { nodeIdFunction :: String
                     , nodeIdBlock :: Ptr BasicBlock
                     , nodeIdSubblock :: Integer
                     , nodeIdCallStack :: Maybe (NodeId,Ptr Instruction)
                     } deriving (Eq,Ord,Show)

type MergeValueRef ptr = IORef (MergeValue ptr)

data MergeValue ptr = MergedValue Bool (Either Val ptr)
                    | UnmergedValue String Bool [(MergeValueRef ptr,BoolVal)]

data UnrollEnv a mem mloc ptr = UnrollEnv { unrollNextMem :: mloc
                                          , unrollNextPtr :: ptr
                                          , unrollGlobals :: Map (Ptr GlobalVariable) ptr
                                          , unrollMemory :: mem
                                          , unrollMergeNodes :: Map Integer (MergeNode a mloc ptr)
                                          , unrollNextMergeNode :: Integer
                                          , unrollGuards :: [Guard]
                                          , unrollWatchpoints :: [Watchpoint]
                                          , unrollInfo :: a
                                          }

type ValueMap ptr = Map (Either (Ptr Argument) (Ptr Instruction)) (MergeValueRef ptr)

data UnrollContext a mloc ptr = UnrollContext { unrollOrder :: [(String,Ptr BasicBlock,Integer)]
                                              , currentMergeNodes :: Map NodeId Integer
                                              , nextMergeNodes :: Map NodeId Integer
                                              , usedMergeNodes :: Map NodeId ()
                                              , realizationQueue :: [Edge a mloc ptr]
                                              , outgoingEdges :: [Edge a mloc ptr]
                                              }

type UnrollQueue a mloc ptr = [(UnrollContext a mloc ptr,NodeId,UnrollBudget)]

data Edge a mloc ptr = Edge { edgeTarget :: NodeId
                            , edgeConds :: [(String,Ptr BasicBlock,Integer,BoolVal,[ValueMap ptr],mloc,Maybe (UnrollNodeInfo a))]
                            , edgeCreatedMergeNodes :: Set NodeId
                            , edgeBudget :: UnrollBudget
                            }

data UnrollConfig mem mloc ptr
  = UnrollCfg { unrollDoMerge :: String -> Ptr BasicBlock -> Integer -> Bool
              , unrollPointerWidth :: Integer
              , unrollStructs :: Map String [TypeDesc]
              , unrollTypes :: Set TypeDesc
              , unrollGraph :: BlockGraph mem mloc ptr
              , unrollCfgGlobals :: Map (Ptr GlobalVariable) (TypeDesc, Maybe MemContent)
              , unrollBlockOrder :: [(String,Ptr BasicBlock,Integer)]
              , unrollDynamicOrder :: (NodeId,UnrollBudget) -> (NodeId,UnrollBudget) -> Ordering
              , unrollPerformCheck :: (NodeId,UnrollBudget) -> (NodeId,UnrollBudget) -> Bool
              , unrollDoRealize :: (NodeId,UnrollBudget) -> Bool
              , unrollCheckedErrors :: ErrorDesc -> Bool
              , unrollLoopHeaders :: Map (Ptr BasicBlock) LoopDesc
              , unrollInstrNums :: Map (Ptr Instruction) Integer
              }

data DistanceInfo = DistInfo { distanceToReturn :: Maybe Integer
                             , distanceToError :: Maybe Integer
                             } deriving (Show,Eq,Ord)

type UnrollMonad a mem mloc ptr = StateT (UnrollEnv a mem mloc ptr) SMT

data UnrollBudget = UnrollBudget { unrollDepth :: Integer
                                 , unrollUnwindDepth :: Integer
                                 , unrollUnrollDepth :: Map (Ptr Loop) Integer
                                 , unrollErrorDistance :: Maybe Integer
                                 , unrollContextDepth :: Integer
                                 } deriving (Show,Eq,Ord)

data BlockEdge = EdgeJmp
               | EdgeSucc Gr.Node -- The callled node
               | EdgeCall Gr.Node -- The successor node
               | EdgeRet
               deriving (Eq,Ord,Show)

data BlockInfo mem mloc ptr
  = BlockInfo { blockInfoFun :: String
              , blockInfoBlk :: Ptr BasicBlock
              , blockInfoBlkName :: Either String Integer
              , blockInfoSubBlk :: Integer
              , blockInfoInstrs :: [(InstrDesc Operand,Maybe Integer)]
              , blockInfoRealizationInfo :: RealizationInfo
              , blockInfoRealization :: RealizationMonad mem mloc ptr (BlockFinalization ptr)
              , blockInfoDistance :: DistanceInfo
              }

data FunInfo = FunInfo { funInfoStartBlk :: Gr.Node
                       , funInfoArguments :: [(Ptr Argument,TypeDesc)]
                       } deriving (Show)

data BlockGraph mem mloc ptr
  = BlockGraph { blockGraph :: Gr.Gr (BlockInfo mem mloc ptr) BlockEdge
               , blockFunctions :: Map String FunInfo
               , blockMap :: Map (Ptr BasicBlock,Integer) Gr.Node
               } deriving (Show)

instance Monoid DistanceInfo where
  mempty = DistInfo Nothing Nothing
  mappend d1 d2 = DistInfo { distanceToReturn = case (distanceToReturn d1,distanceToReturn d2) of
                                (Just d1',Just d2') -> Just $ min d1' d2'
                                (Just d1',Nothing) -> Just d1'
                                (Nothing,Just d2') -> Just d2'
                                (Nothing,Nothing) -> Nothing
                           , distanceToError = case (distanceToError d1,distanceToError d2) of
                                (Just d1',Just d2') -> Just $ min d1' d2'
                                (Just d1',Nothing) -> Just d1'
                                (Nothing,Just d2') -> Just d2'
                                (Nothing,Nothing) -> Nothing
                           }

mkBlockGraph :: (MemoryModel mem mloc ptr,Ord ptr,Enum mloc,Enum ptr)
                => ProgDesc -> BlockGraph mem mloc ptr
mkBlockGraph (_,funs,_,_,_,_)
  = BlockGraph { blockGraph = Gr.mkGraph nodeList edgeList
               , blockFunctions = funInfo
               , blockMap = nodeMp
               }
  where
    nodeList = numberFunctions 0 (Map.toList funs)

    numberFunctions _ [] = []
    numberFunctions nd ((fn,(_,_,blks,_,_)):funs)
      = numberBlocks fn nd 0 blks funs
    
    numberBlocks _ nd _ [] funs = numberFunctions nd funs
    numberBlocks fname nd c ((blk,name,subs):blks) funs
      = numberSubblocks fname nd
        (case name of
            Nothing -> c+1
            Just _ -> c)
        blk
        (case name of
            Nothing -> Right c
            Just name' -> Left name')
        0 subs blks funs
    numberSubblocks fname nd c _ _ _ [] blks funs = numberBlocks fname nd c blks funs
    numberSubblocks fname nd c blk blkName sblkNr (instrs:subs) blks funs
      = let (nc,instrs') = mapAccumL (\cc instr -> case instr of
                                         IAssign _ Nothing _ -> (cc+1,(instr,Just cc))
                                         ITerminator (ICall _ Nothing _ _) -> (cc+1,(instr,Just cc))
                                         _ -> (cc,(instr,Nothing))
                                     ) c instrs
            (rinfo,real) = preRealize $ realizeInstructions instrs'
            info = (nd,BlockInfo { blockInfoFun = fname
                                 , blockInfoBlk = blk
                                 , blockInfoBlkName = blkName
                                 , blockInfoSubBlk = sblkNr
                                 , blockInfoInstrs = instrs'
                                 , blockInfoRealizationInfo = rinfo
                                 , blockInfoRealization = real
                                 , blockInfoDistance = DistInfo Nothing Nothing })
            infos = numberSubblocks fname (nd+1) nc blk blkName (sblkNr+1) subs blks funs
        in info:infos
                                         
    nodeMp = Map.fromList [ ((blockInfoBlk info,blockInfoSubBlk info),nd) | (nd,info) <- nodeList ]
    funInfo = Map.mapMaybe (\(args,_,blks,_,_) -> case blks of
                               (blk,_,_):_ -> Just $ FunInfo { funInfoStartBlk = nodeMp!(blk,0)
                                                             , funInfoArguments = args }
                               [] -> Nothing) funs
    edgeList = [(ndFrom,ndTo,edge)
               | (ndFrom,info) <- nodeList
               , (ndTo,edge) <- case fst $ last (blockInfoInstrs info) of
                 ITerminator (IBr to) -> [(nodeMp!(to,0),EdgeJmp)]
                 ITerminator (IBrCond _ ifT ifF)
                   -> [(nodeMp!(ifT,0),EdgeJmp),(nodeMp!(ifF,0),EdgeJmp)]
                 ITerminator (ISwitch _ def cases)
                   -> (nodeMp!(def,0),EdgeJmp):[ (nodeMp!(blk,0),EdgeJmp) | (_,blk) <- cases ]
                 ITerminator (ICall _ _ (Operand { operandDesc = ODFunction _ f _ }) _)
                   -> let callNode = funInfoStartBlk (funInfo!f)
                          succNode = nodeMp!(blockInfoBlk info,blockInfoSubBlk info+1)
                      in [(callNode,EdgeCall succNode)
                         ,(succNode,EdgeSucc callNode)
                         ]
                 ITerminator (IRet _)
                   -> [ (nodeMp!(blockInfoBlk info',blockInfoSubBlk info'+1),EdgeRet)
                      | (_,info') <- nodeList
                      , f <- case fst $ last (blockInfoInstrs info') of
                        ITerminator (ICall _ _ (Operand { operandDesc = ODFunction _ f _ }) _)
                          -> [f]
                        _ -> []
                      , f==blockInfoFun info]
                 ITerminator IRetVoid
                   -> [ (nodeMp!(blockInfoBlk info',blockInfoSubBlk info'+1),EdgeRet)
                      | (_,info') <- nodeList
                      , f <- case fst $ last (blockInfoInstrs info') of
                        ITerminator (ICall _ _ (Operand { operandDesc = ODFunction _ f _ }) _) -> [f]
                        _ -> []
                      , f==blockInfoFun info]
                 _ -> [] ]

nodeIdCallStackList :: NodeId -> [(String,Ptr BasicBlock,Integer)]
nodeIdCallStackList nd = (nodeIdFunction nd,nodeIdBlock nd,nodeIdSubblock nd):
                         (case nodeIdCallStack nd of
                             Nothing -> []
                             Just (nd',_) -> nodeIdCallStackList nd')

nodeIdRecursionCount :: NodeId -> Map String Integer
nodeIdRecursionCount = count' Map.empty
  where
    count' mp nd = let mp' = Map.insertWith (+) (nodeIdFunction nd) 1 mp
                   in case nodeIdCallStack nd of
                     Nothing -> mp'
                     Just (nd',_) -> count' mp' nd'

defaultConfig :: (MemoryModel mem mloc ptr,Ord ptr,Enum ptr,Enum mloc)
                 => String -> ProgDesc -> (ErrorDesc -> Bool)
                 -> UnrollConfig mem mloc ptr
defaultConfig entr desc selectErr = mergePointConfig entr desc safeMergePoints selectErr

randomMergePointConfig :: (MemoryModel mem mloc ptr,Ord ptr,Enum ptr,Enum mloc,RandomGen g)
                          => String -> ProgDesc -> g -> (ErrorDesc -> Bool)
                          -> UnrollConfig mem mloc ptr
randomMergePointConfig entr desc gen selectErr
  = mergePointConfig entr desc (randomMergePoints gen) selectErr

noMergePointConfig :: (MemoryModel mem mloc ptr,Ord ptr,Enum ptr,Enum mloc)
                      => String -> ProgDesc -> (ErrorDesc -> Bool)
                      -> UnrollConfig mem mloc ptr
noMergePointConfig entr desc selectErr = mergePointConfig entr desc (const []) selectErr

explicitMergePointConfig :: (MemoryModel mem mloc ptr,Ord ptr,Enum ptr,Enum mloc)
                            => String -> ProgDesc -> [(String,String,Integer)]
                            -> (ErrorDesc -> Bool)
                            -> UnrollConfig mem mloc ptr
explicitMergePointConfig entry prog merges selectErr
  = mergePointConfig' entry prog
    (\prog_gr -> Set.fromList [ case List.find (\(nd,blk_info)
                                                -> if blockInfoFun blk_info==fun &&
                                                      blockInfoSubBlk blk_info==sblk
                                                   then (case blockInfoBlkName blk_info of
                                                            Left n -> blk==n
                                                            Right nr -> blk==show nr)
                                                   else False
                                               ) (Gr.labNodes (blockGraph prog_gr)) of
                                  Just (_,blk_info) -> (blockInfoFun blk_info,
                                                        blockInfoBlk blk_info,
                                                        blockInfoSubBlk blk_info)
                              | (fun,blk,sblk) <- merges ]) selectErr

mergePointConfig :: (MemoryModel mem mloc ptr,Ord ptr,Enum ptr,Enum mloc)
                    => String -> ProgDesc -> ([[Gr.Node]] -> [Gr.Node]) -> (ErrorDesc -> Bool)
                    -> UnrollConfig mem mloc ptr
mergePointConfig entry prog select selectErr
  = mergePointConfig' entry prog
    (\prog_gr -> Set.fromList $ fmap (\nd -> let Just inf = Gr.lab (blockGraph prog_gr) nd
                                             in (blockInfoFun inf,blockInfoBlk inf,blockInfoSubBlk inf)) $
                 select (possibleMergePoints (blockGraph prog_gr))) selectErr

mergePointConfig' :: (MemoryModel mem mloc ptr,Ord ptr,Enum ptr,Enum mloc)
                     => String -> ProgDesc
                     -> (BlockGraph mem mloc ptr -> Set (String,Ptr BasicBlock,Integer))
                     -> (ErrorDesc -> Bool) -> UnrollConfig mem mloc ptr
mergePointConfig' entry prog@(_,funs,globs,ptrWidth,alltps,structs) select selectErr
  = UnrollCfg { unrollPointerWidth = ptrWidth
              , unrollStructs = structs
              , unrollTypes = alltps
              , unrollGraph = prog_gr
              , unrollDoMerge = \fname blk sblk -> Set.member (fname,blk,sblk) selectedMergePoints
              , unrollCfgGlobals = globs
              , unrollBlockOrder = order
              , unrollDynamicOrder = \(_,b1) (_,b2)
                                     -> case compare
                                             ((unrollUnwindDepth b1) + (sum $ unrollUnrollDepth b1))
                                             ((unrollUnwindDepth b2) + (sum $ unrollUnrollDepth b2)) of
                                          EQ -> compare (unrollErrorDistance b1) (unrollErrorDistance b2)
                                          r -> r
              , unrollPerformCheck = \(_,last) (nd,cur)
                                     -> {-unrollErrorDistance cur == 0
                                        || Set.member (nodeIdFunction nd,
                                                       nodeIdBlock nd,
                                                       nodeIdSubblock nd) selectedMergePoints-}
                                      (unrollContextDepth last) < (unrollContextDepth cur)
              , unrollDoRealize = \b -> True
              , unrollCheckedErrors = selectErr
              , unrollLoopHeaders = loopHdrs
              , unrollInstrNums = getInstructionNumbers prog_gr
              }
  where
    blk_mp = Map.fromList [ ((fn,blk,sblk),(nd,instrs))
                          | (fn,(args,_,blks,_,_)) <- Map.toList funs
                          , (blk,name,subs) <- blks
                          , (sblk,instrs) <- zip [0..] subs
                          | nd <- [0..] ]
    prog_gr' = mkBlockGraph prog
    prog_gr = generateDistanceInfo selectErr prog_gr'
    Just (_,_,(start_blk,_,_):_,_,_) = Map.lookup entry funs
    start_nd = case Map.lookup (entry,start_blk,0) blk_mp of
      Nothing -> error $ "Failed to find entry point "++entry
      Just (x,_) -> x
    order = calculateSimpleOrder prog_gr start_nd
    selectedMergePoints = select prog_gr
    getLoops mp loop = foldl getLoops (Map.insert (loopDescHeader loop) loop mp) (loopDescSubs loop)
    loopHdrs = foldl (\mp (_,_,_,loops,_)
                      -> foldl getLoops mp loops
                     ) Map.empty funs

calculateOrder :: BlockGraph mem mloc ptr -> Gr.Node -> [(String,Ptr BasicBlock,Integer)]
calculateOrder gr startNd = reverse $ Gr.postorder dfsTree
  where
    ([dfsTree],_) = dfs (error "First node must have distance to error.") (blockGraph gr) [startNd]
    dfs dist gr ns = let (gr',ns') = mapAccumL (\cgr n -> case Gr.match n cgr of
                                                   (Nothing,ngr) -> (ngr,Nothing)
                                                   (Just (_,cur,info,suc),ngr)
                                                     -> let suc' = mapMaybe (\(kind,s) -> case kind of
                                                                                EdgeSucc _ -> Nothing
                                                                                _ -> Just s) suc
                                                        in case distanceToError (blockInfoDistance info) of
                                                            Nothing -> case distanceToReturn (blockInfoDistance info) of
                                                              Nothing -> (ngr,Nothing)
                                                              Just rdist -> (ngr,Just (Right rdist,(blockInfoFun info,blockInfoBlk info,blockInfoSubBlk info),suc'))
                                                            Just d' -> (ngr,Just (Left d',(blockInfoFun info,blockInfoBlk info,blockInfoSubBlk info),suc'))
                                               ) gr ns
                         ns'' = List.sortBy (\(d1,_,_) (d2,_,_) -> compare d2 d1) $ catMaybes ns'
                     in dfs' gr' ns''
    dfs' gr [] = ([],gr)
    dfs' gr ((d,info,suc):ns) = let (subs,gr') = dfs d gr suc
                                    (rest,gr'') = dfs' gr' ns
                                in ((Node info subs):rest,gr'')

calculateSimpleOrder :: BlockGraph mem mloc ptr -> Gr.Node -> [(String,Ptr BasicBlock,Integer)]
calculateSimpleOrder gr startNd = reverse $ Gr.postorder dfsTree
  where
    [dfsTree] = Gr.xdffWith (\(_,_,_,succ) -> mapMaybe (\(edge,nd) -> case edge of
                                                           EdgeSucc _ -> Nothing
                                                           _ -> Just nd
                                                       ) succ)
                (\(_,_,info,_) -> (blockInfoFun info,blockInfoBlk info,blockInfoSubBlk info)) [startNd] (blockGraph gr)

reachabilityInfo :: Map (Ptr BasicBlock,Integer)
                    (Maybe String,RealizationInfo,
                     RealizationMonad mem mloc ptr (BlockFinalization ptr))
                    -> Map (Ptr BasicBlock,Integer)
                           (Map (Ptr BasicBlock,Integer) (Set (Ptr BasicBlock,Integer)))
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

definitionMap :: Map (Ptr BasicBlock,Integer)
                     (Maybe String,RealizationInfo,
                      RealizationMonad mem mloc ptr (BlockFinalization ptr))
              -> Map (Ptr Instruction) (Ptr BasicBlock,Integer)
definitionMap = Map.foldlWithKey (\cmp blk (_,info,_) -> let cmp1 = foldl (\cmp (_,ret_addr) -> Map.insert ret_addr (fst blk,snd blk+1) cmp) cmp (reCalls info)
                                                             cmp2 = foldl (\cmp instr -> Map.insert instr blk cmp) cmp1 (reLocallyDefined info)
                                                         in cmp2
                                 ) Map.empty

mergeValueMaps :: Bool -> [(BoolVal,ValueMap ptr)]
                  -> UnrollMonad a mem mloc ptr (ValueMap ptr)
mergeValueMaps extensible mps = do
  let merge_map = Map.unionsWith (++) $ fmap (\(c,mp) -> fmap (\ref -> [(ref,c)]) mp) mps
  sequence $ Map.mapWithKey (\instr entrs -> liftIO $ newIORef (UnmergedValue "inp" extensible entrs)
                            ) merge_map

mergeValueStacks :: Bool -> [(BoolVal,[ValueMap ptr])]
                    -> UnrollMonad a mem mloc ptr [ValueMap ptr]
mergeValueStacks _ ((_,[]):_) = return []
mergeValueStacks extensible stacks = do
  st_head <- mergeValueMaps extensible (fmap (\(c,x:xs) -> (c,x)) stacks)
  st_tail <- mergeValueStacks extensible (fmap (\(c,x:xs) -> (c,xs)) stacks)
  return $ st_head:st_tail

addMerge :: (MemoryModel mem mloc ptr,Enum ptr)
            => Bool -> BoolVal -> ValueMap ptr -> ValueMap ptr
            -> UnrollMonad a mem mloc ptr (ValueMap ptr)
addMerge extensible cond mp_new mp_old
  = mapM (\entr -> case entr of
             Left (Left x) -> liftIO $ newIORef (UnmergedValue "inp" extensible [(x,cond)])
             Left (Right x) -> return x
             Right (new,old) -> do
               mergeValues old new cond
               return old) $
    Map.unionWith (\(Left (Left x)) (Left (Right y)) -> Right (x,y)) (fmap (Left . Left) mp_new) (fmap (Left . Right) mp_old)

dumpMergeValue :: MergeValueRef ptr -> UnrollMonad a mem mloc ptr String
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

checkLoops' :: Foldable t => t (MergeValueRef ptr) -> UnrollMonad a mem mloc ptr ()
checkLoops' = fmap (const ()) . foldlM (checkLoops []) []

checkLoops :: [MergeValueRef ptr] -> [MergeValueRef ptr] -> MergeValueRef ptr -> UnrollMonad a mem mloc ptr [MergeValueRef ptr]
checkLoops visited checked ref
  | List.elem ref visited = error "Loop detected"
  | List.elem ref checked = return checked
  | otherwise = do
    res <- liftIO $ readIORef ref
    case res of
      MergedValue _ _ -> return (ref:checked)
      UnmergedValue _ _ vals -> foldlM (checkLoops (ref:visited)) (ref:checked) (fmap fst vals)

getMergeValue :: (MemoryModel mem mloc ptr,Enum ptr)
                 => MergeValueRef ptr
                 -> UnrollMonad a mem mloc ptr (Either Val ptr)
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
                                     lift $ assert $ (boolValValue cond) .=>. (valEq nval val)
                                 ) refs
                           return $ Left nval)
                  else (do
                           lst <- mapM (\(ref,cond) -> do
                                           Left val <- getMergeValue ref
                                           return (val,cond)) refs
                           let nval = valOptimize (valSwitch lst)
                           nval' <- if valIsComplex nval
                                    then lift $ valCopy name nval
                                    else return nval
                           return $ Left nval')
        Right p -> do
          env <- get
          let nptr = unrollNextPtr env
          put $ env { unrollNextPtr = succ nptr }
          refs' <- mapM (\(ref,cond) -> do
                            Right ptr <- getMergeValue ref
                            return (cond,ptr)
                        ) refs
          if extensible
            then mapM_ (\(cond,ptr) -> do
                           (env :: UnrollEnv a mem mloc ptr) <- get
                           ((),nmem) <- lift $ addInstruction (unrollMemory env) cond
                                        (MIPtrConnect ptr nptr :: MemoryInstruction mloc ptr ())
                                        Map.empty
                           put $ env { unrollMemory = nmem }
                       ) refs'
            else (do
                     (env :: UnrollEnv a mem mloc ptr) <- get
                     let (prx,_) = unrollProxies env
                         emptyLike :: Proxy a -> [a]
                         emptyLike _ = []
                     ((),nmem) <- lift $ addInstruction (unrollMemory env) (ConstBool True)
                                  (MISelect refs' nptr :: MemoryInstruction mloc ptr ())
                                  Map.empty
                     put $ env { unrollMemory = nmem })
          return (Right nptr)
      liftIO $ writeIORef ref (MergedValue extensible ret)
      return ret

mergeValues :: (MemoryModel mem mloc ptr,Enum ptr)
               => MergeValueRef ptr -> MergeValueRef ptr -> BoolVal
               -> UnrollMonad a mem mloc ptr ()
mergeValues ref val cond = do
  mn <- liftIO $ readIORef ref
  nmn <- mergeValue val cond mn
  liftIO $ writeIORef ref nmn

mergeValue :: (MemoryModel mem mloc ptr,Enum ptr)
              => MergeValueRef ptr -> BoolVal -> MergeValue ptr
              -> UnrollMonad a mem mloc ptr (MergeValue ptr)
mergeValue val cond (UnmergedValue name extensible uvals)
  = if extensible
    then return $ UnmergedValue name extensible ((val,cond):uvals)
    else error $ "Merging into non-extensible value "++name
mergeValue val cond (MergedValue extensible mval) = do
  rval <- getMergeValue val
  case (rval,mval) of
    (Left v1,Left v2) -> if extensible
                         then lift $ assert $ (boolValValue cond) .=>. (valEq v2 v1)
                         else error $ "Merging into non-extensible variable "++show v2
    (Right p1,Right p2) -> do
      (env :: UnrollEnv a mem mloc ptr) <- get
      ((),nmem) <- lift $ addInstruction (unrollMemory env) cond
                   (MIPtrConnect p1 p2::MemoryInstruction mloc ptr ()) Map.empty
      put $ env { unrollMemory = nmem }
  return (MergedValue extensible mval)

createMergeValues :: Bool -> Map (Either (Ptr Argument) (Ptr Instruction)) (Either Val ptr) -> UnrollMonad a mem mloc ptr (ValueMap ptr)
createMergeValues extensible
  = mapM (\val -> liftIO $ newIORef (MergedValue extensible val))

enqueueEdge :: [(String,Ptr BasicBlock,Integer)] -> Edge a mloc ptr -> [Edge a mloc ptr] -> [Edge a mloc ptr]
enqueueEdge
  = insertWithOrder
    (\x y -> if nodeIdFunction (edgeTarget x) == nodeIdFunction (edgeTarget y) &&
                nodeIdBlock (edgeTarget x) == nodeIdBlock (edgeTarget y) &&
                nodeIdSubblock (edgeTarget x) == nodeIdSubblock (edgeTarget y)
             then Just $ comparing (nodeIdCallStack . edgeTarget) x y
             else Nothing)
    (\e1 e2 -> e1 { edgeConds = (edgeConds e1)++(edgeConds e2)
                  , edgeCreatedMergeNodes = Set.union (edgeCreatedMergeNodes e1)
                                            (edgeCreatedMergeNodes e2)
                  , edgeBudget = UnrollBudget { unrollDepth = min (unrollDepth $ edgeBudget e1)
                                                              (unrollDepth $ edgeBudget e2)
                                              , unrollUnwindDepth = min (unrollUnwindDepth $ edgeBudget e1) (unrollUnwindDepth $ edgeBudget e2)
                                              , unrollUnrollDepth = min (unrollUnrollDepth $ edgeBudget e1) (unrollUnrollDepth $ edgeBudget e2)
                                              , unrollErrorDistance = case (unrollErrorDistance $ edgeBudget e1,unrollErrorDistance $ edgeBudget e2) of
                                                   (Nothing,d2) -> d2
                                                   (d1,Nothing) -> d1
                                                   (Just d1,Just d2) -> Just $ min d1 d2
                                              , unrollContextDepth = min (unrollContextDepth $ edgeBudget e1) (unrollContextDepth $ edgeBudget e2) }
                  }) (\x -> (nodeIdFunction $ edgeTarget x,
                             nodeIdBlock $ edgeTarget x,
                             nodeIdSubblock $ edgeTarget x))

enqueueEdges :: (Edge a mloc ptr -> Maybe Bool)
             -> UnrollConfig mem mloc ptr -> [Edge a mloc ptr]
             -> UnrollContext a mloc ptr
             -> UnrollContext a mloc ptr
enqueueEdges nxtCtx cfg edges ctx
  = ctx { realizationQueue = nqueue
        , outgoingEdges = nout }
  where
    edges' = filter (\e -> unrollDoRealize cfg (edgeTarget e,edgeBudget e)) edges
    (nqueue,nout) = foldl (\(cqueue,cout) edge
                            -> case nxtCtx edge of
                             Nothing -> (cqueue,cout)
                             Just True -> (cqueue,
                                           enqueueEdge (unrollOrder ctx) edge cout)
                             Just False -> (enqueueEdge (unrollOrder ctx) edge cqueue,
                                            cout)
                          ) (realizationQueue ctx,
                             outgoingEdges ctx) edges'


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

compareWithOrder :: Eq a => [a] -> a -> a -> Maybe Ordering
compareWithOrder order x y = if x==y
                             then Just EQ
                             else getOrder' order
  where
    --getOrder' [] = error "Elements not in order"
    getOrder' [] = Nothing
    getOrder' (c:cs) = if c==x
                       then Just LT
                       else (if c==y
                             then Just GT
                             else getOrder' cs)

shiftOrder :: (a -> Bool) -> [a] -> [a]
shiftOrder f xs = let (prf,pof) = List.break f xs
                  in pof++prf

addMergeNode :: MergeNode a mloc ptr -> UnrollMonad a mem mloc ptr Integer
addMergeNode nd = do
  env <- get
  let nxt = unrollNextMergeNode env
  put $ env { unrollMergeNodes = Map.insert nxt nd (unrollMergeNodes env)
            , unrollNextMergeNode = succ nxt
            }
  return nxt

getMergeNode :: Monad m => Integer -> StateT (UnrollEnv a mem mloc ptr) m (MergeNode a mloc ptr)
getMergeNode idx = do
  env <- get
  case Map.lookup idx (unrollMergeNodes env) of
    Just nd -> return nd

updateMergeNode :: Monad m => Integer -> MergeNode a mloc ptr -> StateT (UnrollEnv a mem mloc ptr) m ()
updateMergeNode idx nd = modify (\env -> env { unrollMergeNodes = Map.insert idx nd (unrollMergeNodes env) })

adjustMergeNode :: Monad m => Integer -> (MergeNode info mloc ptr -> m (a,MergeNode info mloc ptr)) -> StateT (UnrollEnv info mem mloc ptr) m a
adjustMergeNode idx f = do
  nd <- getMergeNode idx
  (res,nd') <- lift $ f nd
  updateMergeNode idx nd'
  return res

adjustMergeNode' :: Monad m => Integer -> (MergeNode a mloc ptr -> m (MergeNode a mloc ptr)) -> StateT (UnrollEnv a mem mloc ptr) m ()
adjustMergeNode' idx f = adjustMergeNode idx (\nd -> do
                                                 x <- f nd
                                                 return ((),x))

unrollProxies :: UnrollEnv a mem mloc ptr -> (Proxy mloc,Proxy ptr)
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

startingContext :: (MemoryModel mem Integer Integer,UnrollInfo a)
                   => UnrollConfig mem Integer Integer -> String
                   -> SMT (UnrollContext a Integer Integer,UnrollEnv a mem Integer Integer)
startingContext cfg fname = case Map.lookup fname (blockFunctions $ unrollGraph cfg) of
  Just info -> do
    let order = unrollBlockOrder cfg
        Just blkInfo = Gr.lab (blockGraph $ unrollGraph cfg) (funInfoStartBlk info)
        --(blk,sblk) = unrollFunInfoStartBlock info
        blk = blockInfoBlk blkInfo
        sblk = blockInfoSubBlk blkInfo
        ((cptr,prog),globs') = mapAccumL (\(ptr',prog') (tp,cont)
                                          -> ((succ ptr',(ptr',tp,cont):prog'),ptr')
                                         ) (0,[]) (unrollCfgGlobals cfg)
    mem <- memNew (Proxy::Proxy Integer) (unrollPointerWidth cfg) (unrollTypes cfg) (unrollStructs cfg) [ (ptr,tp,cont) | (ptr,PointerType tp,cont) <- prog ]
    startArgs <- mapM (\(arg,tp) -> case tp of
                          PointerType _ -> error "No support for nondeterministic pointers yet."
                          _ -> do
                            res <- varNamedAnn "arg" (typeWidth (unrollPointerWidth cfg) (unrollStructs cfg) tp*8)
                            ref <- liftIO $ newIORef (MergedValue False (Left $ DirectValue res))
                            return (Left arg,ref)
                      ) (funInfoArguments info)
    let nId = NodeId { nodeIdFunction = fname
                     , nodeIdBlock = blk
                     , nodeIdSubblock = sblk
                     , nodeIdCallStack = Nothing }
    return (UnrollContext { unrollOrder = order
                          , currentMergeNodes = Map.empty
                          , nextMergeNodes = Map.empty
                          , usedMergeNodes = Map.empty
                          , realizationQueue = [Edge { edgeTarget = nId
                                                     , edgeConds = [(fname,nullPtr,0,ConstBool True,[Map.fromList startArgs],0,Nothing)]
                                                     , edgeCreatedMergeNodes = Set.empty
                                                     , edgeBudget = UnrollBudget 0 0 Map.empty (errorDistanceForNodeId (unrollGraph cfg) nId) 0
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
                                      , unrollInfo = unrollInfoInit
                                      })
  Nothing -> error $ "Function "++fname++" not found in program graph."

spawnContexts :: UnrollConfig mem mloc ptr -> UnrollContext a mloc ptr
                 -> [UnrollContext a mloc ptr]
spawnContexts cfg ctx
  = [ UnrollContext { unrollOrder = norder
                    , currentMergeNodes = Map.filterWithKey (\key _ -> not $ Set.member key (edgeCreatedMergeNodes edge))
                                          (Map.union (nextMergeNodes ctx) (currentMergeNodes ctx))
                    , nextMergeNodes = Map.empty
                    , usedMergeNodes = Map.empty
                    , realizationQueue = [edge { edgeCreatedMergeNodes = Set.empty
                                               , edgeBudget = (edgeBudget edge) { unrollContextDepth = (unrollContextDepth $ edgeBudget edge)+1
                                                                                }}]
                    , outgoingEdges = []
                    }
    | edge <- outgoingEdges ctx
    , let norder = shiftOrder (==(nodeIdFunction $ edgeTarget edge,nodeIdBlock $ edgeTarget edge,nodeIdSubblock $ edgeTarget edge)) (unrollOrder ctx)
    , let suitableMerges = suitableMergePoints (Set.fromList [ (fun,blk,sblk) | (fun,blk,sblk,_,_,_,_) <- edgeConds edge ]) (unrollOrder ctx)
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

--contextWeight :: UnrollConfig mloc ptr -> UnrollContext a mloc ptr -> Integer
--contextWeight cfg ctx = unrollDynamicOrder cfg (edgeBudget $ head $ realizationQueue ctx)

--compareContext :: UnrollConfig mloc ptr -> UnrollContext a mloc ptr -> UnrollContext a mloc ptr -> Ordering
--compareContext cfg = comparing (contextWeight cfg)

performUnrollmentCtx :: (MemoryModel mem mloc ptr,UnrollInfo a,Eq ptr,Enum ptr,Eq mloc,Enum mloc)
                        => Bool
                        -> Bool
                        -> UnrollConfig mem mloc ptr
                        -> UnrollContext a mloc ptr
                        -> UnrollMonad a mem mloc ptr (UnrollContext a mloc ptr)
performUnrollmentCtx incremental isFirst cfg ctx
  | unrollmentDone ctx = return ctx
  | otherwise = do
    --trace ("Step: "++show ctx) (return ())
    ctx' <- stepUnrollCtx isFirst (if incremental
                                   then incrementalEnqueue cfg
                                   else staticEnqueue cfg) cfg ctx
    performUnrollmentCtx incremental False cfg ctx'

unrollmentDone :: UnrollContext a mloc ptr -> Bool
unrollmentDone ctx = List.null (realizationQueue ctx)

nextEdge :: Monad m => UnrollContext a mloc ptr -> m (Edge a mloc ptr,UnrollContext a mloc ptr)
nextEdge ctx = case realizationQueue ctx of
  e:es -> return (e,ctx { realizationQueue = es })

incrementalEnqueue :: UnrollConfig mem mloc ptr
                   -> NodeId -> [Edge a mloc ptr]
                   -> UnrollContext a mloc ptr
                   -> UnrollContext a mloc ptr
incrementalEnqueue cfg trg edges ctx
  = enqueueEdges
    (\e -> case compareWithOrder (unrollOrder ctx)
                (nodeIdFunction trg,
                 nodeIdBlock trg,
                 nodeIdSubblock trg)
                (nodeIdFunction $ edgeTarget e,
                 nodeIdBlock $ edgeTarget e,
                 nodeIdSubblock $ edgeTarget e) of
             Nothing -> Nothing
             Just LT -> Just False
             _ -> Just True)
    cfg edges ctx

staticEnqueue :: UnrollConfig mem mloc ptr
                 -> NodeId -> [Edge a mloc ptr]
                 -> UnrollContext a mloc ptr
                 -> UnrollContext a mloc ptr
staticEnqueue cfg trg edges ctx
  = enqueueEdges (const $ Just False) cfg edges ctx

stepUnrollCtx :: (MemoryModel mem mloc ptr,UnrollInfo a,Eq ptr,Enum ptr,Eq mloc,Enum mloc)
                 => Bool
                 -> (NodeId -> [Edge a mloc ptr]
                     -> UnrollContext a mloc ptr -> UnrollContext a mloc ptr)
                 -> UnrollConfig mem mloc ptr
                 -> UnrollContext a mloc ptr
                 -> UnrollMonad a mem mloc ptr (UnrollContext a mloc ptr)
stepUnrollCtx isFirst enqueue cfg cur = do
  (Edge trg inc createdMerges lvl,cur1) <- nextEdge cur
  --trace ("Realizing "++show trg) (return ())
  let mergeNode = Map.lookup trg (currentMergeNodes cur1)
      mergeNodeCreate = unrollDoMerge cfg (nodeIdFunction trg) (nodeIdBlock trg) (nodeIdSubblock trg)
      extensible = case mergeNode of
        Nothing -> mergeNodeCreate
        Just _ -> True
  case mergeNode of
    Just mn -> connectMerge cur1 mn trg inc
    Nothing -> do
      let blockNode = (blockMap $ unrollGraph cfg)!(nodeIdBlock trg,nodeIdSubblock trg)
          Just blockInfo = Gr.lab (blockGraph $ unrollGraph cfg) blockNode
          info = blockInfoRealizationInfo blockInfo
          realize = blockInfoRealization blockInfo
          blk_name = (case blockInfoBlkName blockInfo of
                         Left rname -> rname
                         Right num -> "lbl"++show num)++"_"++show (nodeIdSubblock trg)
      env <- get
      let (newNodeInfo,newInfo) = unrollInfoNewNode (unrollInfo env) trg
                                  (blockInfoBlkName blockInfo)
                                  mergeNodeCreate
          newInfo' = foldl (\info srcNd -> unrollInfoConnect info srcNd newNodeInfo) newInfo
                     [ srcNd | (_,_,_,_,_,_,Just srcNd) <- inc ]
      put $ env { unrollInfo = newInfo' }
      (act,inp,inp',phis,start_loc,prev_locs,merge_node,mem_instr,mem_eqs)
        <- if mergeNodeCreate
           then createMerge blk_name info newNodeInfo inc
           else createNormal blk_name info trg inc
      env <- get
      (fin,nst,outp) <- lift $ postRealize (unrollMemory env)
                        (RealizationEnv { reFunction = nodeIdFunction trg
                                        , reBlock = nodeIdBlock trg
                                        , reSubblock = nodeIdSubblock trg
                                        , reActivation = act
                                        , reGlobals = unrollGlobals env
                                        , reInputs = inp
                                        , rePhis = phis
                                        , reStructs = unrollStructs cfg
                                        , reInstrNums = unrollInstrNums cfg })
                        start_loc
                        (unrollNextMem env)
                        (unrollNextPtr env)
                        realize
      put $ env { unrollNextPtr = reNextPtr nst
                , unrollNextMem = reNextMemLoc nst
                , unrollMemory = reMem nst }
      outp' <- createMergeValues False (Map.mapKeys Right $ reLocals nst)
      let arg_vars = Map.filterWithKey (\k _ -> case k of
                                           Left _ -> True
                                           _ -> False
                                       ) (case inp' of
                                             h:_ -> h)
          new_vars = Map.union (Map.union outp' (case inp' of
                                                    h:_ -> h)) arg_vars
          nCreatedMerges = if mergeNodeCreate
                           then Set.insert trg createdMerges
                           else createdMerges
      outEdges <- getOutEdges trg act lvl (reCurMemLoc nst)
                  new_vars inp' newNodeInfo nCreatedMerges fin
      let cur2 = enqueue trg outEdges
                 (cur1 { nextMergeNodes = case merge_node of
                            Nothing -> nextMergeNodes cur
                            Just mn -> Map.insert trg mn (nextMergeNodes cur) })
      if isFirst
        then (do
                 env <- get
                 let (_,prx) = unrollProxies env
                 nmem <- lift $ makeEntry prx (unrollMemory env) start_loc
                 put $ env { unrollMemory = nmem })
        else return ()
      mapM_ (\(cond,src,trg) -> do
                (env :: UnrollEnv a mem mloc ptr) <- get
                ((),nmem) <- lift $ addInstruction (unrollMemory env) cond
                             (MIConnect src trg :: MemoryInstruction mloc ptr ())
                             Map.empty
                put $ env { unrollMemory = nmem }
            ) mem_eqs
      modify (\env -> env { unrollGuards = (reGuards outp)++(unrollGuards env)
                          , unrollWatchpoints = (reWatchpoints outp)++(unrollWatchpoints env)
                          })
      return cur2
  where
    connectMerge :: (MemoryModel mem mloc ptr,Enum ptr,UnrollInfo a)
                    => UnrollContext a mloc ptr
                    -> Integer -> NodeId
                    -> [(String,Ptr BasicBlock,Integer,BoolVal,[ValueMap ptr],mloc,Maybe (UnrollNodeInfo a))]
                    -> UnrollMonad a mem mloc ptr (UnrollContext a mloc ptr)
    connectMerge cur mn trg inc = do
      rmn <- getMergeNode mn
      nprx <- lift $ varNamed "proxy"
      lift $ assert $ (mergeActivationProxy rmn) .==.
        (app or' ([ boolValValue act | (_,_,_,act,_,_,_) <- inc ]++[nprx]))
      mapM_ (\(fun,blk,sblk,act,_,loc,_) -> do
                (env :: UnrollEnv a mem mloc ptr) <- get
                ((),nmem) <- lift $ addInstruction (unrollMemory env) act
                             (MIConnect loc (mergeLoc rmn) :: MemoryInstruction mloc ptr ())
                             Map.empty
                put $ env { unrollMemory = nmem }
                case Map.lookup blk (mergePhis rmn) of
                  Nothing -> return ()
                  Just phi -> lift $ assert $ (boolValValue act) .=>.
                              (app and' $ phi:[ not' phi'
                                              | (blk',phi') <- Map.toList (mergePhis rmn),
                                                blk'/=blk ])
            ) inc
      ninp <- foldlM (\cinp (_,_,_,act,mp,_,_) -> do
                         sequence $ zipWith (\mp' cinp'
                                             -> addMerge True act mp' cinp'
                                            ) mp cinp
                     ) (mergeInputs rmn) inc
      modify $ \env -> env { unrollInfo = foldl (\info ndSrc
                                                 -> unrollInfoConnect info ndSrc (mergeUnrollInfo rmn)
                                                ) (unrollInfo env) [ ndSrc | (_,_,_,_,_,_,Just ndSrc) <- inc ] }
      updateMergeNode mn (rmn { mergeActivationProxy = nprx
                              , mergeInputs = ninp })
      return (cur { usedMergeNodes = Map.insert trg () (usedMergeNodes cur) })

    createMerge blk_name info newNodeInfo inc = do
      act_proxy <- lift $ varNamed $ "proxy_"++blk_name
      act_static <- lift $ defConstNamed ("act_"++blk_name)
                    (app or' ([ boolValValue act | (_,_,_,act,_,_,_) <- inc ]++[act_proxy]))

      mergedInps <- mergeValueStacks True [ (cond,mp) | (_,_,_,cond,_:mp,_,_) <- inc ]

      inputProxies <- mapM (\(tp,name) -> case tp of
                               PointerType tp' -> do
                                 env <- get
                                 put $ env { unrollNextPtr = succ (unrollNextPtr env) }
                                 return (Right (unrollNextPtr env))
                               _ -> do
                                 val <- lift $ valNew (case name of
                                                          Nothing -> "inp"
                                                          Just n -> n) tp
                                 return $ Left val
                           ) (rePossibleInputs info)
      inputProxies' <- createMergeValues True inputProxies
      inputProxies'' <- foldlM (\curInp (_,_,_,cond,mp:_,_,_)
                                -> addMerge True cond mp curInp
                               ) inputProxies' inc
      
      let inputs = inputProxies'':mergedInps
          inp = inputProxies
      
      phis <- fmap Map.fromList $
              mapM (\blk' -> do
                       phi <- lift $ varNamed "phi"
                       return (blk',phi)
                   ) (Set.toList $ rePossiblePhis info)
      mapM_ (\(_,blk,_,cond,_,_,_) -> case Map.lookup blk phis of
                Nothing -> return ()
                Just phi -> lift $ assert $ (boolValValue cond) .=>.
                            (app and' $ phi:[ not' phi'
                                            | (blk',phi') <- Map.toList phis,
                                              blk'/=blk ])
            ) inc
      loc <- do
        env <- get
        put $ env { unrollNextMem = succ $ unrollNextMem env }
        return (unrollNextMem env)
      env <- get
      put $ env { unrollMergeNodes = Map.insert (unrollNextMergeNode env)
                                     (MergeNode { mergeActivationProxy = act_proxy
                                                , mergeInputs = inputs
                                                , mergePhis = phis
                                                , mergeLoc = loc
                                                , mergeUnrollInfo = newNodeInfo })
                                     (unrollMergeNodes env)
                , unrollNextMergeNode = succ $ unrollNextMergeNode env }
      return (act_static,inp,inputs,phis,loc,[loc],
              Just $ unrollNextMergeNode env,[],[ (act',loc',loc)
                                                | (_,_,_,act',_,loc',_) <- inc ])
    createNormal blk_name info trg inc = do
      mergedInps <- mergeValueStacks False [ (cond,mp) | (_,_,_,cond,mp,_,_) <- inc ]
      act <- case inc of
        [(_,_,_,act',_,_,_)] -> do
          let optAct = optimizeExpr' (boolValValue act')
          if isComplexExpr optAct
            then lift $ defConstNamed ("act_"++(nodeIdFunction trg)++"_"++blk_name) optAct
            else (do
                     lift $ comment $ "act_"++(nodeIdFunction trg)++"_"++blk_name++" = "++show optAct
                     return optAct)
        _ -> lift $ defConstNamed ("act_"++(nodeIdFunction trg)++"_"++blk_name)
             (app or' [ boolValValue act | (_,_,_,act,_,_,_) <- inc ])
      inp <- mapM getMergeValue (Map.intersection (case mergedInps of
                                                      h:_ -> h) $
                                 rePossibleInputs info)
      (start_loc,prev_locs,mphis) <- case inc of
        (_,_,_,_,_,loc',_):inc'
          -> if all (\(_,_,_,_,_,loc'',_) -> loc'==loc'') inc'
             then return (loc',[loc'],[])
             else (do
                      env <- get
                      let loc'' = unrollNextMem env
                      put $ env { unrollNextMem = succ loc'' }
                      return (loc'',[ loc''' | (_,_,_,_,_,loc''',_) <- inc ],
                              [MIPhi [ (act'',loc''') | (_,_,_,act'',_,loc''',_) <- inc ] loc'']))
      phis <- mapM (\blk' -> case [ boolValValue cond
                                  | (_,blk'',_,cond,_,_,_) <- inc, blk''==blk' ] of
                       [] -> return Nothing
                       xs -> do
                         let phiExpr = optimizeExpr' $ app or' xs
                         phi <- if isComplexExpr phiExpr
                                then lift $ defConstNamed "phi" phiExpr
                                else return phiExpr
                         return $ Just (blk',phi)
                   ) (Set.toList $ rePossiblePhis info)
      return (act,inp,mergedInps,
              Map.fromList $ catMaybes phis,start_loc,prev_locs,Nothing,
              mphis,[])
    getOutEdges trg act lvl curMLoc new_vars inp' newNodeInfo nCreatedMerges (Jump trgs)
      = return [ Edge { edgeTarget = nodeId
                      , edgeConds = [(nodeIdFunction trg,
                                      nodeIdBlock trg,
                                      nodeIdSubblock trg,
                                      DirectBool $ act .&&. cond,
                                      new_vars:(tail inp'),
                                      curMLoc,
                                      Just newNodeInfo)]
                      , edgeCreatedMergeNodes = nCreatedMerges
                      , edgeBudget = lvl { unrollDepth = unrollDepth lvl + 1
                                         , unrollUnrollDepth = case Map.lookup trg_blk (unrollLoopHeaders cfg) of
                                           Nothing -> unrollUnrollDepth lvl
                                           Just loop -> Map.insertWith (+) (loopDescPtr loop) 1 (unrollUnrollDepth lvl)
                                         , unrollErrorDistance = errorDistanceForNodeId (unrollGraph cfg) nodeId
                                         }
                      } | (cond,trg_blk) <- trgs
                        , cond /= constant False
                        , let nodeId = NodeId { nodeIdFunction = nodeIdFunction trg
                                              , nodeIdBlock = trg_blk
                                              , nodeIdSubblock = 0
                                              , nodeIdCallStack = nodeIdCallStack trg } ]
    getOutEdges trg act lvl curMLoc new_vars inp' newNodeInfo nCreatedMerges (Call fname args ret) = do
      let fun_info = (blockFunctions $ unrollGraph cfg)!fname
          Just startBlkInfo = Gr.lab (blockGraph $ unrollGraph cfg) (funInfoStartBlk fun_info)
          start_blk = blockInfoBlk startBlkInfo
          start_sblk = blockInfoSubBlk startBlkInfo
      arg_vars <- createMergeValues False $ Map.fromList [ (Left arg_ptr,arg) | ((arg_ptr,tp),arg) <- zip (funInfoArguments fun_info) args ]
      let nodeId = NodeId { nodeIdFunction = fname
                          , nodeIdBlock = start_blk
                          , nodeIdSubblock = start_sblk
                          , nodeIdCallStack = Just (trg { nodeIdSubblock = succ $ nodeIdSubblock trg },ret)
                          }
      return [ Edge { edgeTarget = nodeId
                    , edgeConds = [(nodeIdFunction trg,
                                    nodeIdBlock trg,
                                    nodeIdSubblock trg,
                                    DirectBool act,
                                    arg_vars:new_vars:(tail inp'),
                                    curMLoc,
                                    Just newNodeInfo)]
                    , edgeCreatedMergeNodes = nCreatedMerges
                    , edgeBudget = lvl { unrollDepth = unrollDepth lvl + 1
                                       , unrollUnwindDepth = unrollUnwindDepth lvl + 1
                                       , unrollErrorDistance = errorDistanceForNodeId (unrollGraph cfg) nodeId
                                       }
                    } ]
    getOutEdges trg act lvl curMLoc _ inp' newNodeInfo nCreatedMerges (Return rval)
      = case nodeIdCallStack trg of
      Just (prev,trg_instr) -> do
        nvars <- case rval of
          Nothing -> return (tail inp')
          Just val -> case tail inp' of
            x:xs -> do
              val' <- liftIO $ newIORef (MergedValue False val)
              return $ (Map.insert (Right trg_instr) val' x):xs
        return [ Edge { edgeTarget = prev
                      , edgeConds = [(nodeIdFunction trg,
                                      nodeIdBlock trg,
                                      nodeIdSubblock trg,
                                      DirectBool act,nvars,curMLoc,
                                      Just newNodeInfo)]
                      , edgeCreatedMergeNodes = nCreatedMerges
                      , edgeBudget = lvl { unrollDepth = unrollDepth lvl + 1
                                         , unrollUnwindDepth = unrollUnwindDepth lvl - 1
                                         , unrollErrorDistance = errorDistanceForNodeId (unrollGraph cfg) prev
                                         }
                      } ]
      Nothing -> return []

errorDistanceForNodeId :: BlockGraph mem mloc ptr -> NodeId -> Maybe Integer
errorDistanceForNodeId gr nd = case Map.lookup (nodeIdBlock nd,nodeIdSubblock nd) (blockMap gr) of
  Nothing -> Nothing
  Just nd -> case Gr.lab (blockGraph gr) nd of
    Just (BlockInfo { blockInfoDistance = dist }) -> case distanceToError dist of
      Just errDist -> case distanceToReturn dist of
        Just retDist -> case prevDist of
          Just pDist -> Just $ min errDist (pDist+retDist)
          Nothing -> Just errDist
        Nothing -> Just errDist
      Nothing -> case distanceToReturn dist of
        Nothing -> Nothing
        Just retDist -> case prevDist of
          Just pDist -> Just (retDist+pDist)
          Nothing -> Nothing
    Nothing -> Nothing
  where
    prevDist = case nodeIdCallStack nd of
      Nothing -> Nothing
      Just (prev,_) -> errorDistanceForNodeId gr prev

allProxies :: UnrollEnv a mem mloc ptr -> [SMTExpr Bool]
allProxies env = [ mergeActivationProxy nd | nd <- Map.elems (unrollMergeNodes env) ]

contextQueueInsert :: UnrollConfig mem mloc ptr -> UnrollContext a mloc ptr
                      -> UnrollQueue a mloc ptr
                      -> UnrollQueue a mloc ptr
contextQueueInsert cfg ctx
  = List.insertBy (\(_,ndx,bx) (_,ndy,by) -> unrollDynamicOrder cfg (ndx,bx) (ndy,by)
                    {-case (realizationQueue x,realizationQueue y) of
                      ([],[]) -> EQ
                      (_:_,[]) -> GT
                      ([],_:_) -> LT
                      (x:xs,y:ys) -> unrollDynamicOrder cfg (edgeBudget x) (edgeBudget y)-}
                  ) (ctx,minNd,budget)
  where
    (minNd,budget) = getMinBudget cfg ctx

contextQueueStep :: (UnrollInfo a,MemoryModel mem mloc ptr,Eq mloc,Eq ptr,Enum mloc,Enum ptr)
                    => Bool -> Bool -> UnrollConfig mem mloc ptr -> (NodeId,UnrollBudget)
                    -> UnrollQueue a mloc ptr
                    -> UnrollMonad a mem mloc ptr (Maybe ((NodeId,UnrollBudget),
                                                          UnrollQueue a mloc ptr))
contextQueueStep incremental isFirst cfg lvl queue = case queue of
  (ctx,minN,minB):qs -> case realizationQueue ctx of
    [] -> contextQueueStep incremental isFirst cfg lvl
          (foldl (\queue' ctx'
                  -> contextQueueInsert cfg ctx' queue'
                 ) qs (spawnContexts cfg ctx))
    _:_ -> case unrollDynamicOrder cfg (minN,minB) lvl of
      GT -> return $ Just ((minN,minB),queue)
      _ -> do
        ctx' <- performUnrollmentCtx incremental isFirst cfg ctx
        --ctx' <- stepUnrollCtx isFirst cfg ctx
        case realizationQueue ctx' of
          [] -> let (minN',minB') = getMinBudget cfg ctx'
                in return $ Just (lvl,(ctx',minN',minB'):qs)
          e:_ -> case unrollDynamicOrder cfg lvl (edgeTarget e,edgeBudget e) of
            LT -> return $ Just (lvl,contextQueueInsert cfg ctx' qs)
            _ -> let (minN',minB') = getMinBudget cfg ctx'
                 in return $ Just (lvl,(ctx',minN',minB'):qs)
  [] -> return Nothing

checkForErrors :: (MemoryModel mem mloc ptr)
                  => UnrollConfig mem mloc ptr
                  -> UnrollMonad a mem mloc ptr (Maybe ([(String,[BitVector BVUntyped])],[ErrorDesc]))
checkForErrors cfg = do
  env <- get
  let (p1,p2) = unrollProxies env
      bugs = filter (\(desc,_) -> unrollCheckedErrors cfg desc) $
             unrollGuards env ++ (memoryErrors (unrollMemory env) p1 p2)
  lift $ stack $ do
    mapM_ (\mn -> assert $ not' $ mergeActivationProxy mn) (unrollMergeNodes env)
    assert $ app or' [ cond | (desc,cond) <- bugs ]
    res <- checkSatUsing (AndThen [UsingParams (CustomTactic "tseitin-cnf") []
                                  ,UsingParams (CustomTactic "bit-blast") []
                                  ,UsingParams (CustomTactic "sat") []])
    --res <- checkSatUsing (UsingParams (CustomTactic "smt") [])
    if res
      then (do
               outp <- mapM (\(name,cond,args) -> do
                                v <- getValue cond
                                if v
                                  then (do
                                           vals <- mapM (\(tp,val) -> getValue val) args
                                           return (Just (name,vals)))
                                  else return Nothing
                            ) (unrollWatchpoints env)
               rerrs <- mapM (\(desc,cond) -> do
                                 cond' <- getValue cond
                                 if cond'
                                   then return $ Just desc
                                   else return Nothing
                             ) bugs
               return $ Just (catMaybes outp,catMaybes rerrs))
      else return Nothing

contextQueueRun :: (UnrollInfo a,MemoryModel mem Integer Integer)
                   => Bool
                   -> Proxy mem
                   -> Proxy a
                   -> UnrollConfig mem Integer Integer
                   -> String
                   -> SMT (Maybe ([(String,[BitVector BVUntyped])],[ErrorDesc]),a)
contextQueueRun incremental (_::Proxy mem) (_::Proxy a) cfg entry = do
  (start,env :: UnrollEnv a mem Integer Integer) <- startingContext cfg entry
  let lvl@(minN,minB) = getMinBudget cfg start
  (res,nenv) <- runStateT (contextQueueCheck incremental 0 True False cfg lvl lvl [(start,minN,minB)]) env
  return (res,unrollInfo nenv)

contextQueueCheck :: (UnrollInfo a,MemoryModel mem mloc ptr,Eq mloc,Eq ptr,Enum mloc,Enum ptr)
                     => Bool -> Integer -> Bool -> Bool
                     -> UnrollConfig mem mloc ptr -> (NodeId,UnrollBudget)
                     -> (NodeId,UnrollBudget)
                     -> UnrollQueue a mloc ptr
                     -> UnrollMonad a mem mloc ptr (Maybe ([(String,[BitVector BVUntyped])],
                                                           [ErrorDesc]))
contextQueueCheck incremental n isFirst mustCheck cfg lastLvl lvl queue = do
  --liftIO $ putStrLn $ "Depth: "++show n++" "++show (length queue,length $ realizationQueue $ head queue)
  res <- contextQueueStep incremental isFirst cfg lvl queue
  case res of
    Nothing -> if mustCheck
               then checkForErrors cfg
               else return Nothing
    Just (nlvl,nqueue) -> if unrollPerformCheck cfg lastLvl nlvl
                          then (do
                                   err <- checkForErrors cfg
                                   case err of
                                     Just err' -> return $ Just err'
                                     Nothing -> contextQueueCheck incremental (n+1) False False cfg nlvl nlvl nqueue)
                          else contextQueueCheck incremental (n+1) False True cfg lastLvl nlvl nqueue

getMinBudget :: UnrollConfig mem mloc ptr -> UnrollContext a mloc ptr -> (NodeId,UnrollBudget)
getMinBudget cfg ctx = minimumBy (unrollDynamicOrder cfg)
                       [ (edgeTarget edge,edgeBudget edge) | edge <- realizationQueue ctx ]

instance Show (BlockInfo mem mloc ptr) where
  show info = (case blockInfoFun info of
                  "main" -> ""
                  "__llbmc_main" -> ""
                  f -> f++".")++
              (case blockInfoBlkName info of
                  Right lbl -> "lbl"++show lbl
                  Left blk -> blk)++
              (if blockInfoSubBlk info==0
               then ""
               else "."++show (blockInfoSubBlk info))

generateDistanceInfo :: (ErrorDesc -> Bool) -> BlockGraph mem mloc ptr
                        -> BlockGraph mem mloc ptr
generateDistanceInfo isError gr = updateDistanceInfo gr upds
  where
    upds = catMaybes [ if hasErrs || isRet
                       then Just (nd,DistInfo { distanceToError = if hasErrs
                                                                  then Just 0
                                                                  else Nothing
                                              , distanceToReturn = if isRet
                                                                   then Just 0
                                                                   else Nothing
                                              })
                       else Nothing
                     | (nd,blk) <- Gr.labNodes (blockGraph gr)
                     , let info = blockInfoRealizationInfo blk
                           hasErrs = any isError (rePotentialErrors info)
                           isRet = reReturns info ]

updateDistanceInfo :: BlockGraph mem mloc ptr -> [(Gr.Node,DistanceInfo)]
                      -> BlockGraph mem mloc ptr
updateDistanceInfo gr [] = gr
updateDistanceInfo gr xs = let (ngr,upds) = updateDistanceInfo' gr xs
                           in updateDistanceInfo ngr upds

updateDistanceInfo' :: BlockGraph mem mloc ptr -> [(Gr.Node,DistanceInfo)]
                       -> (BlockGraph mem mloc ptr,[(Gr.Node,DistanceInfo)])
updateDistanceInfo' gr [] = (gr,[])
updateDistanceInfo' gr (x:xs) = let (gr1,upd1) = updateDistanceInfo'' gr x
                                    (gr2,upd2) = updateDistanceInfo' gr1 xs
                                in (gr2,upd1++upd2)

updateDistanceInfo'' :: BlockGraph mem mloc ptr -> (Gr.Node,DistanceInfo)
                        -> (BlockGraph mem mloc ptr,[(Gr.Node,DistanceInfo)])
updateDistanceInfo'' gr (nd,newDist) = (gr { blockGraph = ngr },upds)
  where
    (Just (prev,_,blk,succ),gr') = Gr.match nd (blockGraph gr)
    oldDist = blockInfoDistance blk
    newRetDist = case (distanceToReturn oldDist,distanceToReturn newDist) of
      (Nothing,Nothing) -> Nothing
      (Just _,Nothing) -> Nothing
      (Nothing,Just n) -> Just n
      (Just odist,Just ndist) -> if odist <= ndist
                                 then Nothing
                                 else Just ndist
    newErrDist = case (distanceToError oldDist,distanceToError newDist) of
      (Nothing,Nothing) -> Nothing
      (Just _,Nothing) -> Nothing
      (Nothing,Just n) -> Just n
      (Just odist,Just ndist) -> if odist <= ndist
                                 then Nothing
                                 else Just ndist
    ngr = (prev,nd,blk { blockInfoDistance = DistInfo { distanceToError = case distanceToError newDist of
                                                           Nothing -> distanceToError oldDist
                                                           Just n -> case distanceToError oldDist of
                                                             Nothing -> Just n
                                                             Just o -> Just $ min n o
                                                      , distanceToReturn = case distanceToReturn newDist of
                                                           Nothing -> distanceToReturn oldDist
                                                           Just n -> case distanceToReturn oldDist of
                                                             Nothing -> Just n
                                                             Just o -> Just $ min n o }
                       },succ) Gr.& gr'
    upds = catMaybes [ case edge of
                          EdgeJmp -> case (newRetDist,newErrDist) of
                            (Nothing,Nothing) -> Nothing
                            _ -> Just (prevNode,DistInfo { distanceToError = fmap (+1) newErrDist
                                                         , distanceToReturn = fmap (+1) newRetDist })
                          EdgeCall succNode -> let Just succBlk = Gr.lab gr' succNode
                                                   succErrDist = distanceToError $ blockInfoDistance succBlk
                                                   succRetDist = distanceToReturn $ blockInfoDistance succBlk
                                                   newErrDist' = case newRetDist of
                                                     Nothing -> fmap (+1) newErrDist
                                                     Just d -> case succErrDist of
                                                       Nothing -> fmap (+1) newErrDist
                                                       Just e -> case newErrDist of
                                                         Nothing -> Just (d+e+1)
                                                         Just derr -> Just (min (derr+1) (d+e+1))
                                                   newRetDist' = case newRetDist of
                                                     Nothing -> Nothing
                                                     Just r -> case succRetDist of
                                                       Nothing -> Nothing
                                                       Just r' -> Just (r+r'+1)
                                               in case (newRetDist,newErrDist) of
                                                 (Nothing,Nothing) -> Nothing
                                                 _ -> Just (prevNode,DistInfo { distanceToError = newErrDist'
                                                                              , distanceToReturn = newRetDist' })
                          EdgeSucc callNode -> case (newRetDist,newErrDist) of
                            (Nothing,Nothing) -> Nothing
                            _ -> let Just callBlk = Gr.lab gr' callNode
                                     minDist = distanceToReturn $ blockInfoDistance callBlk
                                 in case minDist of
                                   Nothing -> Nothing
                                   Just minDist' -> Just (prevNode,DistInfo { distanceToError = fmap (+minDist') newErrDist
                                                                            , distanceToReturn = fmap (+minDist') newRetDist })
                          _ -> Nothing
                     | (edge,prevNode) <- prev ]

dumpBlockGraph :: UnrollConfig mem mloc ptr -> IO ()
dumpBlockGraph cfg = do
  putStrLn $ Gr.graphviz' $ blockGraph $ unrollGraph cfg

getInstructionNumbers :: BlockGraph mem mloc ptr -> Map (Ptr Instruction) Integer
getInstructionNumbers gr
  = getNums' Map.empty (Gr.labNodes (blockGraph gr))
  where
    getNums' mp [] = mp
    getNums' mp ((_,bi):rest) = getNums'' mp
                                (blockInfoInstrs bi) rest

    getNums'' mp [] rest = getNums' mp rest
    getNums'' mp ((IAssign instr Nothing _,Just num):instrs) rest
      = getNums'' (Map.insert instr num mp) instrs rest
    getNums'' mp ((ITerminator (ICall instr Nothing _ _),Just num):instrs) rest
      = getNums'' (Map.insert instr num mp) instrs rest
    getNums'' mp (_:instrs) rest
      = getNums'' mp instrs rest
