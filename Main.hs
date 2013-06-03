{-# LANGUAGE DeriveDataTypeable,TypeFamilies,FlexibleContexts,RankNTypes,OverloadedStrings,ScopedTypeVariables #-}
module Main where

import Analyzation
import Value
import Realization
import ConditionList
import Options
import Program
import TypeDesc
import InstrDesc
import VarStore
import Simplifier

import MemoryModel
{-import MemoryModel.Untyped
import MemoryModel.UntypedBlocks
import MemoryModel.Typed
import MemoryModel.Plain
import MemoryModel.CBMCLike-}
import MemoryModel.Null
import MemoryModel.Snow
import Language.SMTLib2
import Data.Typeable
import Control.Monad.Trans
import Data.List as List (genericLength,genericReplicate,genericSplitAt,zip4,zipWith4,zipWith5,null,lookup,find,genericIndex)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import Prelude hiding (foldl,concat,mapM_,any,foldr,mapM,foldl1,all,elem,sequence)
import Data.Foldable
import Data.Traversable
import System.Exit
import Control.Monad (when)
import Data.Maybe (mapMaybe,maybeToList,catMaybes)
import Data.Bits as Bits
import Foreign.Ptr
import Foreign.Storable
import qualified Foreign.Marshal.Alloc as Alloc
import Text.Show
import Data.Monoid
import qualified Data.Graph.Inductive as Gr
import Control.Monad.State hiding (mapM,mapM_,sequence)
import Control.Monad.RWS (runRWST)
import Data.Proxy
import Data.Ord

import LLVM.FFI.BasicBlock
import LLVM.FFI.Value
import LLVM.FFI.Instruction (Instruction)
import LLVM.FFI.Loop (Loop)
import LLVM.FFI.Constant

(!) :: (Show k,Ord k) => Map k a -> k -> a
(!) mp k = case Map.lookup k mp of
             Nothing -> error $ "Couldn't find key "++show k++" in "++show (Map.keys mp)
             Just r -> r

newtype VarValue = VarValue Integer deriving (Show,Eq,Ord,Enum,Num,Real,Integral)

newtype VarPointer = VarPointer Integer deriving (Show,Eq,Ord,Enum,Num,Real,Integral)

data NodeId = IdStart { startFunction :: String }
            | IdEnd { endFunction :: String }
            | IdBlock { idFunction :: String
                      , idBlock :: Ptr BasicBlock
                      , idSubblock :: Integer 
                      }
            deriving (Eq,Ord,Show)

data Node mloc ptr
  = Node { nodeActivation :: SMTExpr Bool
         , nodeActivationProxy :: SMTExpr Bool
         , nodeType :: NodeType mloc ptr
         , nodeInputLoc :: mloc
         , nodeOutputLoc :: mloc
         }

instance Show (Node mloc ptr) where
  show nd = case nodeType nd of
    RealizedStart fun _ _ -> "start "++fun
    RealizedEnd _ _ -> "end"
    RealizedBlock { nodeBlock = blk
                  , nodeBlockName = name
                  , nodeSubblock = sblk } -> case name of
      Nothing -> show blk++"."++show sblk
      Just n -> n++"."++show sblk

data NodeType mloc ptr
  = RealizedStart { nodeStartName :: String
                  , nodeArguments :: [(Ptr Argument,Either VarValue ptr)]
                  , nodeRealizedEnd :: Maybe Gr.Node }
  | RealizedEnd { nodeEndFunctionNode :: Gr.Node
                , nodeReturns :: Maybe (Either VarValue ptr) }
  | RealizedBlock { nodeFunctionNode :: Gr.Node
                  , nodeBlock :: Ptr BasicBlock
                  , nodeBlockName :: Maybe String
                  , nodeSubblock :: Integer
                  , nodeInput :: Map (Ptr Instruction) (Either Val ptr)
                  , nodePhis :: Map (Ptr BasicBlock) (SMTExpr Bool)
                  , nodeOutput :: Output ptr
                  , nodeFinalization :: BlockFinalization ptr
                  , nodeMemProgram :: MemoryProgram mloc ptr
                  , nodeWatchpoints :: [Watchpoint]
                  , nodeGuards :: [Guard]
                  }
    deriving (Show)

data FunctionDescr gr = FunctionDescr
                        { funDescrArgs :: [(Ptr Argument,TypeDesc)]
                        , funDescrReturnType :: TypeDesc
                        , funDescrBlocks :: [(Ptr BasicBlock,Maybe String,[[InstrDesc Operand]])]
                        , funDescrGraph :: gr ((Ptr BasicBlock,Maybe String,Integer,[InstrDesc Operand])) ()
                        , funDescrNodeMap :: Map (Ptr BasicBlock,Integer) Gr.Node
                        , funDescrSCC :: [[Gr.Node]]
                        , funDescrDefines :: Map (Ptr Instruction) (Ptr BasicBlock,Integer)
                        , funDescrRealizationOrder :: [(Ptr BasicBlock,Integer)]
                        , funDescrLoops :: [LoopDesc]
                        , funDescrDomTree :: Maybe DomTree
                        }

data UnrollGraph gr m mloc ptr
  = UnrollGraph { allFunctions :: Map String (FunctionDescr gr)
                , allStructs :: Map String [TypeDesc]
                , globalMemory :: m
                , globalPointers :: Map (Ptr GlobalVariable) ptr
                , varStore :: VarStore SMT VarValue (String,TypeDesc) Val
                , ptrStore :: VarStore (Unrollment gr m mloc ptr) VarPointer ptr ptr
                , nodeInstances :: Map NodeId [Gr.Node]
                , nodeGraph :: gr (Node mloc ptr) (Transition ptr)
                , startNode :: Gr.Node
                , nextNode :: Gr.Node
                , nextPointer :: ptr
                , nextLocation :: mloc
                , queuedNodes :: [(String,[(Ptr Loop,[QueueEntry ptr])])]
                , delayedNodes :: [DelayedReturn]
                }

type Unrollment gr m mloc ptr = StateT (UnrollGraph gr m mloc ptr) SMT

data DelayedReturn = DelayedReturn { callingNode :: Gr.Node
                                   , callingFunction :: String
                                   , callingBlock :: Ptr BasicBlock
                                   , callingSubblock :: Integer
                                   , calledNode :: Gr.Node
                                   , callReturnsTo :: Ptr Instruction
                                   } deriving Show

data QueueEntry ptr = QueueEntry { queuedNode :: NodeId
                                 , queueLevel :: Integer
                                 , incomingNode :: Gr.Node
                                 , incomingReadNode :: Gr.Node
                                 , incomingEdge :: Transition ptr
                                 } deriving Show

data Transition ptr = TBegin
                    | TJump (SMTExpr Bool)
                    | TCall [Either Val ptr]
                    | TReturn (Maybe (Either Val ptr))
                    | TDeliver (Ptr Instruction) Gr.Node

data Output ptr = Output { outputStatic :: Map (Ptr Instruction) (Either Val ptr,String,TypeDesc)
                         , outputLoopStatics :: [(LoopDesc,Map (Ptr Instruction) (Either Val ptr,String,TypeDesc))]
                         , outputDynamics :: Map (Ptr Instruction) (Either VarValue VarPointer)
                         } deriving (Show)

instance Show (Transition m) where
  showsPrec _ TBegin = id
  showsPrec p (TJump cond) = showsPrec p cond
  showsPrec p (TCall args) = showString "call"
  showsPrec p (TReturn val) = case val of
    Nothing -> showString "ret"
    Just v -> showString "retval"
  showsPrec p (TDeliver to _) = id

newJoinPoint :: String -> TypeDesc -> Unrollment gr m mloc ptr VarValue
newJoinPoint name tp = do
  re <- get
  let (res,nstore) = newEntry (name,tp) (varStore re)
  put (re { varStore = nstore })
  return res

newInput :: (Enum ptr) => String -> TypeDesc -> Unrollment gr m mloc ptr (Either VarValue ptr)
newInput name (PointerType tp) = do
  re <- get
  let ptr = nextPointer re
  put $ re { nextPointer = succ ptr }
  return $ Right ptr
newInput name tp = fmap Left $ newJoinPoint name tp

nodeSuccessors :: Gr.Graph gr => UnrollGraph gr m mloc ptr -> Gr.Node -> Integer -> [QueueEntry ptr]
nodeSuccessors gr nd lvl = case Gr.lab (nodeGraph gr) nd of
  Nothing -> error $ "nbis internal error: nodeSuccessors called with unknown node "++show nd++" "++show (Gr.nodes $ nodeGraph gr)
  Just st -> case nodeType st of
    RealizedStart fun _ _
      -> let blks = funDescrBlocks $ (allFunctions gr)!fun
             (start_blk,_,_) = head blks
         in [QueueEntry { queuedNode = IdBlock fun start_blk 0
                        , queueLevel = 0
                        , incomingNode = nd
                        , incomingReadNode = nd
                        , incomingEdge = TBegin }]
    RealizedEnd fun ret -> []
    RealizedBlock { nodeFunctionNode = fnode
                  , nodeFinalization = fin
                  , nodeBlock = prev_blk
                  , nodeSubblock = prev_sblk
                  } -> case fin of
      Jump trgs -> let Just fun_node = Gr.lab (nodeGraph gr) fnode
                       fun_name = nodeStartName $ nodeType fun_node
                       order = funDescrRealizationOrder $ (allFunctions gr)!fun_name
                   in [ QueueEntry { queuedNode = IdBlock fun_name blk sblk
                                   , queueLevel = case compareWithOrder order (prev_blk,prev_sblk) (blk,sblk) of
                                     GT -> lvl
                                     _ -> lvl+1
                                   , incomingNode = nd
                                   , incomingReadNode = nd
                                   , incomingEdge = TJump cond
                                   }
                      | (cond,(blk,sblk)) <- trgs ]
      Return ret -> let Just fun_node = Gr.lab (nodeGraph gr) fnode
                        fun_name = nodeStartName $ nodeType fun_node
                    in [ QueueEntry { queuedNode = IdEnd fun_name
                                    , queueLevel = 0
                                    , incomingNode = nd
                                    , incomingReadNode = nd
                                    , incomingEdge = TReturn ret } ]
      Call fname args rname -> [ QueueEntry { queuedNode = IdStart fname
                                            , queueLevel = 0
                                            , incomingNode = nd
                                            , incomingReadNode = nd
                                            , incomingEdge = TCall args
                                            } ]

updateDelayed :: Gr.Graph gr => UnrollGraph gr m mloc ptr -> Gr.Node -> Gr.Node -> [DelayedReturn] -> ([QueueEntry ptr],[DelayedReturn])
updateDelayed gr from nd delayed
  = case Gr.lab (nodeGraph gr) nd of
    Just (Node { nodeType = RealizedStart _ _ (Just fnode) }) -> update' fnode delayed
    Just (Node { nodeType = RealizedStart _ _ Nothing })
      -> case Gr.lab (nodeGraph gr) from of
      Just (Node { nodeType = RealizedBlock { nodeFinalization = Call _ _ cret
                                            , nodeFunctionNode = fnode
                                            , nodeBlock = blk
                                            , nodeSubblock = sblk
                                            }
                 }) -> (case Gr.lab (nodeGraph gr) fnode of
                           Just (Node { nodeType = RealizedStart fname _ _ })
                             -> trace ("Delaying "++show (fname,blk,sblk+1))
                                ([],DelayedReturn { callingNode = from
                                                  , callingFunction = fname
                                                  , callingBlock = blk
                                                  , callingSubblock = sblk+1
                                                  , calledNode = nd
                                                  , callReturnsTo = cret
                                                  }:delayed)
                           Nothing -> error $ "Failed to lookup function node "++show fnode
                           Just x -> error $ "Function node is not a function start?? "++show x)
    Just (Node { nodeType = RealizedEnd fnode _ }) -> update' fnode delayed
    _ -> ([],delayed)
    where
      update' fnode [] = ([],[])
      update' fnode (del:dels)
        = let (qs,dels') = update' fnode dels
          in if calledNode del == fnode
             then (QueueEntry { queuedNode = IdBlock 
                                             (callingFunction del)
                                             (callingBlock del)
                                             (callingSubblock del)
                              , queueLevel = 0
                              , incomingNode = nd
                              , incomingReadNode = callingNode del
                              , incomingEdge = TDeliver (callReturnsTo del) (callingNode del)
                              }:qs,dels')
             else (qs,del:dels)

allStatics :: Output ptr -> Map (Ptr Instruction) (Either Val ptr)
allStatics outp = fmap (\(v,_,_) -> v) $ Map.unions $ 
                  (outputStatic outp):(fmap snd $ outputLoopStatics outp)

-- | Remove all static variables which will no longer be static in the new block.
--   Creates empty mappings for all new loops entered by the new block.
--   Also it returns the variables it removes.
adjustLoopStack :: [LoopDesc] -> Ptr BasicBlock -> Output ptr -> (Output ptr,Map (Ptr Instruction) (Either Val ptr,String,TypeDesc))
adjustLoopStack all_loops blk outp = case outputLoopStatics outp of
  [] -> (outp { outputLoopStatics = fmap (\li -> (li,Map.empty)) (findLoopForBlock blk all_loops) },Map.empty)
  (li,mp):lis -> if blk `elem` (loopDescBlocks li)
                 then (outp { outputLoopStatics = (fmap (\li' -> (li',Map.empty)) (findLoopForBlock blk (loopDescSubs li)))++((li,mp):lis) },Map.empty)
                 else let (res,mp') = adjustLoopStack all_loops blk (outp { outputLoopStatics = lis })
                      in (res,Map.union mp mp')

-- | Add new dynamic output variables into an output mapping
makeDynamic :: (Enum ptr,Show ptr) => SMTExpr Bool
               -> Map (Ptr Instruction) (Either Val ptr,String,TypeDesc)
               -> Output ptr
               -> Unrollment gr m mloc ptr (Output ptr)
makeDynamic cond mp outp
  = foldlM (\coutp (instr,(val,name,tp)) -> do
               nentr <- case Map.lookup instr (outputDynamics coutp) of
                 Nothing -> case val of
                   Left v -> do
                     gr <- get
                     let (entr,store1) = newEntry (name,tp) (varStore gr)
                     store2 <- lift $ addJoin entr (Right v) cond store1
                     put $ gr { varStore = store2 }
                     return $ Left entr
                   Right ptr -> do
                     gr <- get
                     let (entr,store1) = newEntry (nextPointer gr) (ptrStore gr)
                     trace ("Add pointer "++show ptr++" to join "++show entr) (return ())
                     store2 <- addJoin entr (Right ptr) cond store1
                     modify $ \gr -> gr { ptrStore = store2
                                        , nextPointer = succ $ nextPointer gr }
                     return $ Right entr
                 Just val' -> case (val,val') of
                   (Left v1,Left v2) -> do
                     gr <- get
                     store1 <- lift $ addJoin v2 (Right v1) cond (varStore gr)
                     put $ gr { varStore = store1 }
                     return $ Left v2
                   (Right ptr,Right ptrs) -> do
                     gr <- get
                     trace ("Add pointer "++show ptr++" to join "++show ptrs) (return ())
                     store1 <- addJoin ptrs (Right ptr) cond (ptrStore gr)
                     modify $ \gr -> gr { ptrStore = store1 }
                     return (Right ptrs)
               return (coutp { outputDynamics = Map.insert instr nentr (outputDynamics coutp) })
           ) outp (Map.toList mp)

makeStatic :: Map (Ptr Instruction) (Either Val ptr,String,TypeDesc) -> Output ptr -> Output ptr
makeStatic mp outp = case outputLoopStatics outp of
  [] -> outp { outputStatic = Map.union mp (outputStatic outp) }
  (li,mp'):lis -> outp { outputLoopStatics = (li,Map.union mp mp'):lis }

{-addOutputs :: (Enum ptr,Show ptr) => Map (Ptr Instruction) (Either Val ptr,String,TypeDesc) -> Output ptr -> Unrollment gr m mloc ptr (Output ptr)
addOutputs vals outp = do
  let (stat,dyn) = Map.mapEither (\(entr,name,tp) -> case entr of
                                     Left val -> Left (val,name,tp)
                                     Right ptr -> Right (Right ptr,name,tp)) vals
      outp1 = makeStatic stat outp
  makeDynamic (constant True) dyn outp1-}

mergeOutputs :: (Gr.DynGraph gr,MemoryModel m mloc ptr,Show ptr) => SMTExpr Bool
                -> Map (Ptr Instruction) (Either VarValue VarPointer)
                -> Map (Ptr Instruction) (Either Val ptr)
                -> Gr.Node
                -> Unrollment gr m mloc ptr ()
mergeOutputs cond new_outs new_statics node = do
  --trace ("Merge "++show (Map.toList new_outs)++" at "++show node++" with condition "++show cond) (return ())
  gr <- get
  let (Just (inc,_,nd,outg),gr') = Gr.match node (nodeGraph gr)
  case nodeType nd of
    RealizedBlock { nodeInput = inp
                  , nodeOutput = outp
                  } -> do
      --trace ("Merge into inputs "++show (Map.toList inp)) (return ())
      --trace ("Merge into outputs "++show (Map.toList $ outputDynamics outp)) (return ())
      mapM_ (\pair -> case pair of 
                (Right ps_out,Right p_in) -> do
                  gr1 <- get
                  (rout,nstore) <- readVar ps_out (ptrStore gr1)
                  modify $ \gr -> gr { ptrStore = nstore }
                  gr2 <- get
                  (pr,_) <- getProxies
                  --trace ("Merge into "++show p_in) (return ())
                  nmem <- lift $ connectPointer (globalMemory gr2) pr cond rout p_in
                  put $ gr2 { globalMemory = nmem }
                (Left vout,Left vin) -> do
                  gr <- get
                  (val_out,nstore) <- lift $ readVar vout (varStore gr)
                  lift $ assert $ cond .=>. (valEq vin val_out)
                  put $ gr { varStore = nstore }
            ) $ Map.intersectionWith (\x y -> (x,y)) new_outs inp
      mapM_ (\pair -> case pair of
                (Right p_out,Right p_in) -> do
                  gr <- get
                  (pr,_) <- getProxies
                  nmem <- lift $ connectPointer (globalMemory gr) pr cond p_out p_in
                  put $ gr { globalMemory = nmem }
                (Left vout,Left vin) -> lift $ assert $ cond .=>. (valEq vin vout)
            ) $ Map.intersectionWith (\x y -> (x,y)) new_statics inp
      let new_outs' = Map.difference new_outs inp
      new_outs'' <- sequence $ Map.unionWith (\old_out new_out -> do
                                                 old_out' <- old_out
                                                 new_out' <- new_out
                                                 case (old_out',new_out') of
                                                   (Left vold,Left vnew) -> do
                                                     gr <- get
                                                     nstore <- lift $ addJoin vold (Left vnew) cond (varStore gr)
                                                     put $ gr { varStore = nstore }
                                                     return (Left vold)
                                                   (Right pold,Right pnew) -> do
                                                     trace ("Add "++show pnew++" to join "++show pold) (return ())
                                                     gr <- get
                                                     nstore <- addJoin pold (Left pnew) cond (ptrStore gr)
                                                     modify $ \gr -> gr { ptrStore = nstore }
                                                     return (Right pold)
                                             )
                    (fmap return $ outputDynamics outp)
                    (fmap return new_outs')
      -- Propagate only unmerged values
      let prop_upds = Map.difference new_outs' (outputDynamics outp)
      modify $ \gr -> gr { nodeGraph = (inc,node,nd { nodeType = (nodeType nd) { nodeOutput = outp { outputDynamics = new_outs'' } } },outg) Gr.& gr' }
      mapM_ (\(_,trg) -> mergeOutputs cond prop_upds new_statics trg) outg
    _ -> return ()

makeNode :: (Gr.DynGraph gr,Enum mloc,Enum ptr,MemoryModel m mloc ptr,Show ptr)
            => Maybe Gr.Node
            -> Maybe Gr.Node
            -> NodeId
            -> Unrollment gr m mloc ptr Gr.Node
makeNode read_from from nid = do
  new_gr_id <- gets nextNode
  modify (\gr -> gr { nextNode = succ new_gr_id })
  (node_type,act,mloc_in,mloc_out,prog) <- case nid of
    IdStart fun -> do
      gr <- get
      let FunctionDescr { funDescrArgs = args } = (allFunctions gr)!fun
      args' <- mapM (\(name,tp) -> do
                        val <- newInput ("funarg_"++fun) tp
                        return (name,val)) args
      act <- case from of
        Nothing -> return $ constant True -- Don't use an activation variable for the first node
        Just _ -> lift $ varNamed $ "start_"++fun
      return (RealizedStart fun args' Nothing,act,nextLocation gr,nextLocation gr,[])
    IdEnd fun -> do
      gr <- get
      let FunctionDescr { funDescrArgs = args
                        , funDescrReturnType = rtp } = (allFunctions gr)!fun
          Just pnode = from
          Just (Node { nodeType = RealizedBlock { nodeFunctionNode = fnode } })
            = Gr.lab (nodeGraph gr) pnode
      rv <- case rtp of
        VoidType -> return Nothing
        _ -> do
          v <- newInput ("return_"++fun) rtp
          return (Just v)
      -- Set the pointer of the function start node
      modify (\gr -> case Gr.match fnode (nodeGraph gr) of
                 (Just (inc,_,nd@Node { nodeType = RealizedStart fun args Nothing },outc),gr')
                   -> gr { nodeGraph = (inc,fnode,nd { nodeType = RealizedStart fun args (Just $ nextNode gr) },outc) Gr.& gr' }
             )
      act <- lift $ varNamed $ "end_"++fun
      return (RealizedEnd fnode rv,act,nextLocation gr,nextLocation gr,[])
    IdBlock fun blk sblk -> do
      gr <- get
      let fun_descr = (allFunctions gr)!fun
          blks = funDescrBlocks fun_descr
          (name,subs) = case List.find (\(name,_,_)
                                        -> name == blk
                                       ) blks of
                   Just (_,n,s) -> (n,s)
                   Nothing -> error $ "Failed to find subblock "++show blk++" of function "++fun
          instrs = subs `genericIndex` sblk
          Just fnid = from
          Just (Node { nodeType = from_nt })
            = Gr.lab (nodeGraph gr) fnid
          ffid = case from_nt of
            RealizedStart _ _ _ -> fnid
            RealizedEnd _ _ -> case read_from of
              Just f -> case Gr.lab (nodeGraph gr) f of
                Just (Node { nodeType = RealizedBlock { nodeFunctionNode = fn } })
                  -> fn
            RealizedBlock { nodeFunctionNode = n } -> n
          Just (Node { nodeType = RealizedStart _ fun_args _ }) = Gr.lab (nodeGraph gr) ffid
          outp_prev = case read_from of
            Just read_from' -> case Gr.lab (nodeGraph gr) read_from' of
              Just nd_read_from -> case nodeType nd_read_from of
                RealizedBlock { nodeOutput = outp } -> outp
                _ -> Output Map.empty [] Map.empty
              Nothing -> Output Map.empty [] Map.empty
          (outp_cur,_) = adjustLoopStack (funDescrLoops fun_descr) blk outp_prev
      liftIO $ putStrLn $ "Creating node for "++show name
      act <- lift $ varNamed (case name of
                                 Nothing -> "act_"++fun++"_"++show blk++"_"++show sblk
                                 Just rname -> "act_"++rname++"_"++show sblk)
      gr <- get
      let env = RealizationEnv { reFunction = fun
                               , reBlock = blk
                               , reSubblock = sblk
                               , reActivation = act
                               , reGlobals = globalPointers gr
                               , reArgs = Map.fromList fun_args
                               , reStaticInput = allStatics outp_cur
                               , reStructs = allStructs gr
                               }
          st = RealizationState { reVarStore = varStore gr
                                , reCurMemLoc = nextLocation gr
                                , reNextPtr = nextPointer gr
                                , reLocals = Map.empty
                                , reInputs = Map.empty
                                , rePhis = Map.empty
                                }
      (fin,nst,outp) <- lift $ runRWST (realizeInstructions instrs) env st
      put $ gr { nextPointer = reNextPtr nst
               , varStore = reVarStore nst }
      let output_vars = makeStatic (Map.union (reLocals nst) (reInputs nst)) (outp_cur { outputDynamics = Map.empty })
      --trace ("Node "++show new_gr_id) (return ())
      --trace ("  Input vars: "++show (Map.toList $ reInputs nst)) (return ())
      --trace ("  Static vars: "++show (Map.toList $ allStatics output_vars)) (return ())
      --trace ("  Output vars: "++show (outputDynamics output_vars)) (return ())
      return (RealizedBlock { nodeFunctionNode = ffid
                            , nodeBlock = blk
                            , nodeBlockName = name
                            , nodeSubblock = sblk
                            , nodeInput = fmap (\(x,_,_) -> x) $ reInputs nst
                            , nodePhis = rePhis nst
                            , nodeOutput = output_vars
                            , nodeFinalization = fin
                            , nodeMemProgram = reMemInstrs outp
                            , nodeWatchpoints = reWatchpoints outp
                            , nodeGuards = reGuards outp
                            },act,nextLocation gr,reCurMemLoc nst,reMemInstrs outp)
  ngr <- get
  let node_graph' = Gr.insNode (new_gr_id,
                                Node { nodeActivation = act
                                     , nodeActivationProxy = act
                                     , nodeInputLoc = mloc_in
                                     , nodeOutputLoc = mloc_out
                                     , nodeType = node_type })
                    (nodeGraph ngr)
  nmem <- lift $ addProgram (globalMemory ngr) act mloc_in prog
  --(p1,p2) <- getProxies
  --trace (debugMem nmem p1 p2) (return ())
  put $ ngr { nodeGraph = node_graph'
            , nextLocation = succ mloc_out
            , globalMemory = nmem
            }
  return new_gr_id

connectNodes :: (Gr.DynGraph gr,MemoryModel m mloc ptr,Enum ptr,Show ptr)
                => Gr.Node -> Gr.Node -> Transition ptr -> Gr.Node 
                -> Unrollment gr m mloc ptr ()
connectNodes from read_from trans to = do
  gr <- get
  let Just nd_from = Gr.lab (nodeGraph gr) from
      nd_read_from = if from==read_from
                     then nd_from
                     else (case Gr.lab (nodeGraph gr) read_from of
                              Just nd -> nd)
      (Just (in_to,_,nd_to,out_to),gr1) = Gr.match to (nodeGraph gr)
      cond = case trans of
        TBegin -> nodeActivation nd_from
        TJump c -> if isTrue c
                   then nodeActivation nd_from
                   else nodeActivation nd_from .&&. c
        TCall _ -> nodeActivation nd_from
        TReturn _ -> nodeActivation nd_from
        TDeliver _ _ -> nodeActivation nd_read_from
      {-eqs = case nodeType nd_from of
        RealizedStart fun_name args _ -> case nodeType nd_to of
          RealizedBlock {} -> []
        RealizedEnd _ ret -> case trans of
          TDeliver ret_name _ -> case nodeType nd_read_from of
            RealizedBlock { nodeOutput = outp_read } -> case nodeType nd_to of
              RealizedBlock { nodeInput = inp }
                -> let io = Map.elems $ Map.intersectionWith (\x y -> (x,y)) outp_read inp
                       io' = case (Map.lookup ret_name inp,ret) of
                         (Nothing,Nothing) -> io
                         (Just o_ret,Just i_ret) -> (o_ret,i_ret):io
                   in io'
        RealizedBlock { nodeOutput = outp
                      , nodeFinalization = fin }
          -> case fin of
          Jump conds -> case nodeType nd_to of
            RealizedBlock { nodeInput = inp } -> Map.elems $ Map.intersectionWith (\x y -> (x,y)) outp inp
          Return ret -> case nodeType nd_to of
            RealizedEnd _ ret' -> case (ret,ret') of
              (Nothing,Nothing) -> []
              (Just r1,Just r2) -> [(r1,r2)]
          Call f args_out del -> case nodeType nd_to of
            RealizedStart _ args_in _ -> zipWith (\arg_o (_,arg_i) -> (arg_o,arg_i)) args_out args_in-}
  nproxy <- lift $ varNamed ("proxy_"++(case nodeType nd_to of
                                           RealizedStart { nodeStartName = fun } -> fun
                                           RealizedEnd { } -> "end"
                                           RealizedBlock { nodeBlock = blk
                                                         , nodeBlockName = blkname
                                                         } -> case blkname of
                                             Nothing -> show blk
                                             Just name' -> name'))
  lift $ assert $ nodeActivationProxy nd_to .==. (cond .||. nproxy)
  put $ gr { nodeGraph = (in_to,to,nd_to { nodeActivationProxy = nproxy },out_to) Gr.& gr1 }
  
  case nodeType nd_read_from of
    RealizedStart {} -> case nodeType nd_to of
      RealizedBlock {} -> return ()
    RealizedBlock { nodeOutput = outp
                  , nodeFunctionNode = fnode }
      -> case nodeType nd_to of
      RealizedBlock { nodeBlock = blk } -> do
        let Just fnd = Gr.lab (nodeGraph gr) fnode
            RealizedStart { nodeStartName = fname } = nodeType fnd
            fun_descr = (allFunctions gr)!fname
            (_,demoted) = adjustLoopStack (funDescrLoops fun_descr) blk outp
        --trace ("Demoted: "++show demoted) (return ())
        outp' <- makeDynamic cond demoted outp
        mergeOutputs cond (outputDynamics outp') (allStatics outp') to
      _ -> return ()
  
  gr <- get
  (_,pr) <- getProxies
  mem' <- lift $ connectLocation (globalMemory gr) pr cond
          (nodeOutputLoc nd_from)
          (nodeInputLoc nd_to)
  put $ gr { globalMemory = mem' }
  
  {-let (ptr_eqs,val_eqs) = foldr (\pair (ptr_eqs,val_eqs) -> case pair of
                                    (Right p1,Right p2) -> ((p1,p2):ptr_eqs,val_eqs)
                                    (Left v1,Left v2) -> (ptr_eqs,(v1,v2):val_eqs)
                                ) ([],[]) eqs
  nstore <- foldlM (\store (v_out,v_in) -> do
                       (rout,store') <- lift $ readVar v_out store
                       lift $ assert $ cond .=>. (valEq v_in rout)
                       return store'
                   ) (varStore gr) val_eqs-}
  case nodeType nd_from of
    RealizedBlock { nodeBlock = blk } -> case nodeType nd_to of
      RealizedBlock { nodePhis = phis } 
        -> lift $ assert $ 
           cond .=>. app and' [ if blk==blk' 
                                then cond'
                                else not' cond'
                              | (blk',cond') <- Map.toList phis ]
      _ -> return ()
    _ -> return ()

targetNode :: (Gr.DynGraph gr,Enum mloc,Enum ptr,MemoryModel m mloc ptr,Show ptr)
              => Gr.Node -> Gr.Node -> NodeId
              -> Unrollment gr m mloc ptr (Gr.Node,Bool)
targetNode read_from from to = do
  gr <- get
  case getNode gr Nothing (insts gr) of
    Nothing -> do
      nd <- makeNode (Just read_from) (Just from) to
      modify $ \gr -> gr { nodeInstances = Map.alter (\minsts -> case minsts of
                                                         Nothing -> Just [nd]
                                                         Just nds -> Just $ nd:nds
                                                     ) to 
                                           (nodeInstances gr) }
      return (nd,True)
    Just nd -> return (nd,False)
  where
    insts gr = case Map.lookup to (nodeInstances gr) of
      Nothing -> []
      Just i -> i
    getNode gr res [] = res
    getNode gr res (x:xs) 
      = let ngr = Gr.insEdge (from,x,undefined) (nodeGraph gr)
        in if all (\x -> case x of
                      [nd] -> not $ isSelfLoop nd ngr
                      _ -> False
                  ) (Gr.scc ngr)
           then getNode gr (Just x) xs
           else res

incrementGraph :: (Gr.DynGraph gr,Enum ptr,Enum mloc,MemoryModel m mloc ptr,Show ptr)
                  => Unrollment gr m mloc ptr ()
incrementGraph = do
  entr <- dequeueNode
  -- Determine the target node
  (nd,new) <- targetNode (incomingReadNode entr) (incomingNode entr) (queuedNode entr)
  if new
    then queueRotate
    else return ()
  -- Connect the nodes
  connectNodes (incomingNode entr)
    (incomingReadNode entr)
    (incomingEdge entr) nd
  -- Add an edge to the node graph
  modify $ \gr -> gr { nodeGraph = Gr.insEdge (incomingNode entr,nd,
                                               incomingEdge entr)
                                   (nodeGraph gr) }
  -- Update delayed nodes
  gr <- get
  let (qs1,ndl) = updateDelayed gr (incomingNode entr) nd (delayedNodes gr)
      qs2 = if new then nodeSuccessors gr nd (queueLevel entr)
            else []
  put $ gr { delayedNodes = ndl }
  mapM_ queueNode qs1
  mapM_ queueNode qs2

unrollGraphComplete :: UnrollGraph gr m mloc ptr -> Bool
unrollGraphComplete gr = case queuedNodes gr of
  [] -> True
  _ -> False

data GrStr = GrStr String

instance Show GrStr where
  show (GrStr x) = x

unrollProgram :: (Gr.DynGraph gr,Integral ptr,Integral mloc,MemoryModel m mloc ptr,Show ptr)
                => ProgDesc -> String 
                -> Unrollment gr m mloc ptr a
                -> SMT a
unrollProgram prog@(funs,globs,tps,structs) init (f::Unrollment gr m mloc ptr a) = do
  let (init_args,_,init_blks,_,_) = funs!init
      globs_mp = fmap (\(tp,_) -> tp) globs
      allfuns = fmap (\(sig,rtp,blks,loops,dt)
                      -> let (pgr,pmp) = programAsGraph blks
                             defs = getDefiningBlocks isIntrinsic blks
                             order = case blks of
                               (start_blk,_,_):_ -> case Map.lookup (start_blk,0) pmp of
                                 Just start_node -> case Gr.dff [start_node] pgr of
                                   [order_tree] -> reverse $ fmap (\nd -> let Just (blk,_,sblk,_) = Gr.lab pgr nd in (blk,sblk)) $ Gr.postorder order_tree
                               [] -> []
                         in FunctionDescr { funDescrArgs = sig
                                          , funDescrReturnType = rtp
                                          , funDescrBlocks = blks
                                          , funDescrGraph = {-getVariableInfo
                                                            (\(_,_,_,instrs) -> instrs)
                                                            (\instr -> let Just (blk,sblk) = Map.lookup instr defs
                                                                           Just nd = Map.lookup (blk,sblk) pmp
                                                                       in nd)
                                                            $ getReachability-} pgr
                                          , funDescrNodeMap = pmp
                                          , funDescrSCC = filter (\comp -> case comp of
                                                                     [nd] -> isSelfLoop nd pgr
                                                                     _ -> True
                                                                 ) (Gr.scc pgr)
                                          , funDescrDefines = defs
                                          , funDescrRealizationOrder = order
                                          , funDescrLoops = loops
                                          , funDescrDomTree = dt
                                          }
                     ) funs
  {-liftIO $ mapM_ (\(fname,f) -> do
                     writeFile ("program-"++fname++".dot") $ Gr.graphviz' (Gr.nmap (\(ptr,name,i,_) -> (GrStr $ case name of
                                                                                                           Nothing -> show ptr
                                                                                                           Just name' -> name',i)) (funDescrGraph f))
                 ) (Map.toList allfuns)
  liftIO $ putStrLn $ unlines $ concat $
    fmap (\(fname,FunctionDescr { funDescrArgs = sig
                                , funDescrReturnType = rtp
                                , funDescrBlocks = blks
                                , funDescrSCC = scc 
                                , funDescrRealizationOrder = order
                                , funDescrLoops = loops })
          -> ["SCC "++fname++": "++show scc
             ,"ORDER "++show (fmap (\(blk,sblk) -> case List.find (\(blk',_,_) -> blk==blk') blks of
                                                        Just (_,Just name,_) -> name
                                   ) order)
             ,"LOOPS "++show loops]
         ) (Map.toList allfuns)-}
  let ((cptr,prog),globs') = mapAccumL (\(ptr',prog') (tp,cont) 
                                        -> ((succ ptr',(ptr',tp,cont):prog'),ptr')
                                       ) (0,[]) globs
  mem0 <- memNew (Proxy::Proxy mloc) tps structs [ (ptr,tp,cont) | (ptr,PointerType tp,cont) <- prog ]
  let gr0 = UnrollGraph { allFunctions = allfuns
                        , allStructs = structs
                        , globalMemory = mem0
                        , globalPointers = globs'
                        , nodeInstances = Map.empty
                        , nodeGraph = Gr.empty
                        , varStore = newStore 
                                     (\cond val1 val2 -> assert $ cond .=>. (valEq val1 val2)) 
                                     (\(name,tp) -> case tp of
                                         IntegerType 1 -> do
                                           res <- varNamed name
                                           return $ ConditionValue res 1
                                         _ -> do
                                           res <- varNamedAnn name (fromIntegral $ bitWidth tp)
                                           return $ DirectValue res)
                        , ptrStore = newStore
                                     (\cond ptr1 ptr2 -> do
                                         gr <- get
                                         (pr,_) <- getProxies
                                         mem' <- lift $ connectPointer (globalMemory gr) pr cond ptr1 ptr2
                                         put $ gr { globalMemory = mem' })
                                     (\p -> return p)
                        , startNode = 0
                        , nextNode = 0
                        , nextPointer = cptr
                        , nextLocation = 0::mloc
                        , queuedNodes = []
                        , delayedNodes = []
                        }
  evalStateT (do
                 nd_start <- makeNode Nothing Nothing (IdStart { startFunction = init })
                 liftIO $ putStrLn $ "nd_start="++show nd_start
                 modify $ \gr -> gr { startNode = nd_start }
                 gr' <- get
                 mapM_ queueNode (nodeSuccessors gr' nd_start 0)
                 f) gr0

renderNodeGraph :: (Gr.Graph gr) => UnrollGraph gr m mloc ptr -> String
renderNodeGraph gr = Gr.graphviz (nodeGraph gr) "nbis" (16,10) (1,1) Gr.Portrait

checkGraph :: (Gr.Graph gr) => UnrollGraph gr m mloc ptr -> SMT (Maybe (ErrorDesc,[String]))
checkGraph gr = do
  let errs = concat $ fmap (\(_,nd) -> case nodeType nd of
                               RealizedBlock { nodeGuards = g } -> g
                               _ -> []) (Gr.labNodes (nodeGraph gr))
      watchs = concat $ fmap (\(_,nd) -> case nodeType nd of
                                 RealizedBlock { nodeWatchpoints = w } -> w
                                 _ -> []) (Gr.labNodes (nodeGraph gr))
  if Prelude.null errs
    then return Nothing
    else (stack $ do
             -- Set all proxies to false (except for the start node)
             mapM_ (\(nd_id,nd) -> if nd_id == startNode gr
                                   then return ()
                                   else assert $ not' $ nodeActivationProxy nd
                   ) (Gr.labNodes (nodeGraph gr))

             liftIO $ putStrLn $ "Checking "++show (length errs)++" errors..."
             assert $ app or' $ fmap (\(_,cond) -> cond) $ errs
             res <- checkSat
             if res
               then (do
                        err <- getError errs
                        strs <- getWatches watchs
                        return $ Just (err,strs)
                    )
               else return Nothing)
    where
      getError [] = error $ "Internal error: An error is indicated, but none could be found (profoundly weird, isn't it?)"
      getError ((d,cond):errs) = do
        v <- getValue cond
        if v
          then return d
          else getError errs
      
      getWatches w = fmap catMaybes $
                     mapM (\(name,cond,args) -> do
                              act <- getValue cond
                              if act
                                then (do
                                         res <- mapM (\(tp,v) -> getValue v) args
                                         return $ Just $ name++": "++show res)
                                else return Nothing) w

main = do
  opts <- getOptions
  when (showHelp opts) $ do
    putStrLn nbisInfo
    exitSuccess
  print "Get program..."
  progs <- mapM (getProgram isIntrinsic) (files opts)
  print "done."
  let program = foldl1 mergePrograms progs
  withSMTSolver (case solver opts of
                    Nothing -> "~/debug-smt.sh output-" ++ (entryPoint opts) ++ ".smt"
                    Just bin -> bin) $ do
    setOption (PrintSuccess False)
    setOption (ProduceModels True)
    unrollProgram program (entryPoint opts) $ case memoryModelOption opts of
      --_ -> perform (bmcDepth opts) (checkUser opts) (checkMemoryAccess opts) :: Unrollment Gr.Gr NullMemory Integer Integer ()
      _ -> perform (bmcDepth opts) (checkUser opts) (checkMemoryAccess opts) :: Unrollment Gr.Gr (SnowMemory Integer Integer) Integer Integer ()
    return ()
  where
    perform depth check_user check_mem 
      = check 0 depth
      
    check i depth
      | i == depth = return ()
      | otherwise = do
        gr <- get
        if unrollGraphComplete gr 
          then return ()
          else (do
                   liftIO $ putStrLn $ "Step "++show i++":"
                   liftIO $ print $ queuedNodes gr
                   liftIO $ print $ delayedNodes gr
                   --liftIO $ putStrLn $ "Realizing "++show (queuedState $ head $ queue gr')++"("++show (incomingEdge $ head $ queue gr')++")"
                   --liftIO $ putStrLn $ memDebug (globalMemory gr)
                   incrementGraph
                   ngr <- get
                   res <- lift $ checkGraph ngr
                   --liftIO $ writeFile ("graph"++show i++".dot") (renderNodeGraph ngr)
                   case res of
                     Nothing -> check (i+1) depth
                     Just (err,watch) -> do
                       (p1,p2) <- getProxies
                       liftIO $ writeFile ("graph"++show i++".dot") (renderNodeGraph ngr)
                       liftIO $ putStrLn $ debugMem (globalMemory gr) p1 p2
                       liftIO $ putStrLn $ "Error "++show err++" found."
                       mapM_ (\str -> liftIO $ putStrLn str) watch
                       return ())

scanForNode :: Gr.Graph gr => gr (Node mloc ptr) (Transition ptr) -> Ptr BasicBlock -> Integer -> Gr.Node -> Maybe (Gr.Node,Node mloc ptr)
scanForNode gr blk sblk nd = trace ("Scanning for "++show blk++"."++show sblk) $ scanForNode' Set.empty nd
  where
    scanForNode' seen nd = case Gr.match nd gr of
      (Just (inc,_,ndcont,_),_) -> case nodeType ndcont of
        RealizedStart _ _ _ -> Nothing -- we've reached the top of the function
        RealizedEnd _ _ -> Nothing -- we've reached a subcall
        RealizedBlock { nodeBlock = blk'
                      , nodeSubblock = sblk' }
          -- Have we found the node we're looking for?
          | blk==blk' && sblk==sblk' -> Just (nd,ndcont)
          -- Or have we already seen it?
          | Set.member nd seen -> Nothing 
          | otherwise -> case inc of
            -- Skip the function call
            [(TDeliver _ prev,_)] -> scanForNode' (Set.insert nd seen) prev
            -- It's a normal node
            prevs -> case mapMaybe (\(_,prev) -> scanForNode' (Set.insert nd seen) prev) prevs of
              [] -> Nothing
              (res:_) -> Just res

{-
gatherInputs :: Gr.Graph gr => Maybe Gr.Node -> Maybe Gr.Node -> NodeId
                -> Unrollment gr m mloc ptr
                (Map (Ptr Instruction) (Either (VarKind VarValue ptr) (TypeDesc,Maybe String)),Map (Ptr Argument) (Either VarValue ptr))
gatherInputs read_from from nid = do
  case nid of
    IdBlock fun blk sblk -> do
      gr <- get
      let FunctionDescr { funDescrBlocks = blks
                        , funDescrDefines = defines 
                        , funDescrNodeMap = nd_mp
                        , funDescrGraph = fun_gr
                        , funDescrSCC = sccs 
                        } = (allFunctions gr)!fun
          subs = case List.find (\(name,_,_) -> name==blk) blks of
            Just (_,_,s) -> s
          instrs = subs `genericIndex` sblk
          Just fnid = read_from
          Just fnode = Gr.lab (nodeGraph gr) fnid
          args = case nodeType fnode of
            RealizedStart { nodeArguments = r } -> r
            RealizedBlock { nodeFunctionNode = fun_id } -> case Gr.lab (nodeGraph gr) fun_id of
              Just (Node { nodeType = RealizedStart { nodeArguments = r }}) -> r
          var_set = getInstrsDeps instrs
          var_mp = Map.mapWithKey (\var tp -> case Map.lookup var defines of
                                      Just src -> case Map.lookup src nd_mp of
                                        Just nd_src -> case List.find (elem nd_src) sccs of
                                          -- The source node is not part of any loop
                                          Nothing -> let Just (_,Node { nodeType = ndsrc}) = scanForNode (nodeGraph gr) (fst src) (snd src) fnid
                                                     in case Map.lookup var (nodeOutput ndsrc) of
                                                       Just val -> Left val
                                          -- There is a loop involved, we need a new copy
                                          Just comp -> case nid of
                                            IdBlock { idBlock = blk
                                                    , idSubblock = sblk } -> case Map.lookup (blk,sblk) nd_mp of
                                              Just nd_trg -> if elem nd_trg comp -- Are target and source in the same component?
                                                             then (if isLoopCenter nd_src comp fun_gr || isLoopCenter nd_trg comp fun_gr -- Is either of them the loop center?
                                                                   then (let Just (_,Node { nodeType = ndsrc}) = scanForNode (nodeGraph gr) (fst src) (snd src) fnid
                                                                         in case Map.lookup var (nodeOutput ndsrc) of
                                                                           Just val -> Left val)
                                                                   else Right tp)
                                                             else Right tp
                                  ) var_set
      return (var_mp,Map.fromList args)
    _ -> return (Map.empty,Map.empty)-}

nodeIdFunction :: NodeId -> String
nodeIdFunction (IdStart f) = f
nodeIdFunction (IdEnd f) = f
nodeIdFunction (IdBlock { idFunction = f }) = f

insertWithOrder :: Eq b => (a -> a -> Ordering) -> (a -> b) -> [b] -> a -> [a] -> [a]
insertWithOrder cmp f order el [] = [el]
insertWithOrder cmp f order el (x:xs) = case cmp el x of
  LT -> el:x:xs
  GT -> x:insertWithOrder cmp f order el xs
  EQ -> updateOrder' order
  where
    updateOrder' [] = x:insertWithOrder cmp f order el xs
    updateOrder' (y:ys)
      | y==f el    = el:x:xs
      | y==f x     = x:insertWithOrder cmp f (y:ys) el xs
      | otherwise = updateOrder' ys

compareWithOrder :: Eq a => [a] -> a -> a -> Ordering
compareWithOrder order x y = if x==y
                             then EQ
                             else getOrder' order
  where
    getOrder' [] = error "Elements not in order"
    getOrder' (c:cs) = if c==x
                       then GT
                       else (if c==y
                             then LT
                             else getOrder' cs)

queueNode :: QueueEntry ptr -> Unrollment gr m mloc ptr ()
queueNode entr = do
  gr <- get
  let Just fdescr = Map.lookup (nodeIdFunction $ queuedNode entr) (allFunctions gr)
      loop_ptr = case queuedNode entr of
        IdBlock { idBlock = blk } -> case findLoopForBlock blk (funDescrLoops fdescr) of
          [] -> nullPtr
          (LoopDesc ptr _ _ _):_ -> ptr
        _ -> nullPtr
      nqueue = insert' (funDescrRealizationOrder fdescr) loop_ptr (queuedNodes gr)
  put $ gr { queuedNodes = nqueue }
  where
    insert' ord loop_ptr [] = [(nodeIdFunction $ queuedNode entr,[(loop_ptr,[entr])])]
    insert' ord loop_ptr ((f,entrs):qs)
      = if nodeIdFunction (queuedNode entr) == f
        then (f,insert'' ord loop_ptr entrs):qs
        else (f,entrs):insert' ord loop_ptr qs
    insert'' ord loop_ptr [] = [(loop_ptr,[entr])]
    insert'' ord loop_ptr ((loop_ptr',entrs):qs)
      = if loop_ptr==loop_ptr'
        then (loop_ptr',insertWithOrder (comparing queueLevel)
                        (\e -> case queuedNode e of
                            IdBlock { idBlock = blk
                                    , idSubblock = sblk
                                    } -> (blk,sblk)
                            _ -> (nullPtr,0)) ord entr entrs):qs
        else (loop_ptr',entrs):insert'' ord loop_ptr qs

dequeueNode :: Unrollment gr m mloc ptr (QueueEntry ptr)
dequeueNode = do
  gr <- get
  let (el,nqueue) = dequeue (queuedNodes gr)
  put $ gr { queuedNodes = nqueue }
  return el
  where
    dequeue [] = error "Nothing to dequeue"
    dequeue ((f,[]):xs) = error "Empty queue bucket"
    dequeue ((f,(l,[]):_):_) = error "Empty queue bucket"
    dequeue ((f,(l,el:els):ys):xs) = case els of
      [] -> case ys of
        [] -> (el,xs)
        _ -> (el,(f,ys):xs)
      _ -> (el,(f,(l,els):ys):xs)

queueRotate :: Unrollment gr m mloc ptr ()
queueRotate = do
  gr <- get
  let nqueue = case queuedNodes gr of
        (f,(l,els):ys):xs -> xs++[(f,ys++[(l,els)])]
        [] -> []
        _ -> error "Invalid queue when rotating"
  put $ gr { queuedNodes = nqueue }

findLoopForBlock :: Ptr BasicBlock -> [LoopDesc] -> [LoopDesc]
findLoopForBlock = findLoopForBlock' []
  where
    findLoopForBlock' cur blk [] = cur
    findLoopForBlock' cur blk (desc@(LoopDesc _ _ blks subs):loops)
      = if blk `elem` blks
        then findLoopForBlock' (desc:cur) blk subs
        else findLoopForBlock' cur blk loops

getProxies :: Unrollment gr m mloc ptr (Proxy mloc,Proxy ptr)
getProxies = return (Proxy,Proxy)