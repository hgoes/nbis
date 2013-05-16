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
import Prelude hiding (foldl,concat,mapM_,any,foldr,mapM,foldl1,all,elem)
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
import Control.Monad.State hiding (mapM,mapM_)
import Control.Monad.RWS (runRWST)
import Data.Proxy

import LLVM.FFI.BasicBlock
import LLVM.FFI.Value
import LLVM.FFI.Instruction (Instruction)
import LLVM.FFI.Loop (Loop)
import LLVM.FFI.Constant

(!) :: (Show k,Ord k) => Map k a -> k -> a
(!) mp k = case Map.lookup k mp of
             Nothing -> error $ "Couldn't find key "++show k++" in "++show (Map.keys mp)
             Just r -> r

data NodeId = IdStart { startFunction :: String }
            | IdEnd { endFunction :: String }
            | IdBlock { idFunction :: String
                      , idBlock :: Ptr BasicBlock
                      , idSubblock :: Integer 
                      }
            deriving (Eq,Ord,Show)

data Node mloc var ptr
  = Node { nodeActivation :: SMTExpr Bool
         , nodeActivationProxy :: SMTExpr Bool
         , nodeType :: NodeType mloc var ptr
         , nodeInputLoc :: mloc
         , nodeOutputLoc :: mloc
         }

instance Show (Node mloc var ptr) where
  show nd = case nodeType nd of
    RealizedStart fun _ _ -> "start "++fun
    RealizedEnd _ _ -> "end"
    RealizedBlock { nodeBlock = blk
                  , nodeBlockName = name
                  , nodeSubblock = sblk } -> case name of
      Nothing -> show blk++"."++show sblk
      Just n -> n++"."++show sblk

data NodeType mloc var ptr
  = RealizedStart { nodeStartName :: String
                  , nodeArguments :: [(Ptr Argument,Either var ptr)]
                  , nodeRealizedEnd :: Maybe Gr.Node }
  | RealizedEnd { nodeEndFunctionNode :: Gr.Node
                , nodeReturns :: Maybe (Either var ptr) }
  | RealizedBlock { nodeFunctionNode :: Gr.Node
                  , nodeBlock :: Ptr BasicBlock
                  , nodeBlockName :: Maybe String
                  , nodeSubblock :: Integer
                  , nodeInput :: Map (Ptr Instruction) (Either var ptr)
                  , nodePhis :: Map (Ptr BasicBlock) (SMTExpr Bool)
                  , nodeOutput :: Map (Ptr Instruction) (VarKind var ptr)
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
                        , funDescrGraph :: gr ((Ptr BasicBlock,Maybe String,Integer,[InstrDesc Operand]),Map Gr.Node (Set [Gr.Node]),VariableInfo) ()
                        , funDescrNodeMap :: Map (Ptr BasicBlock,Integer) Gr.Node
                        , funDescrSCC :: [[Gr.Node]]
                        , funDescrDefines :: Map (Ptr Instruction) (Ptr BasicBlock,Integer)
                        , funDescrRealizationOrder :: [(Ptr BasicBlock,Integer)]
                        , funDescrLoops :: [LoopDesc]
                        }

data UnrollGraph gr m mloc var ptr
  = UnrollGraph { allFunctions :: Map String (FunctionDescr gr)
                , allStructs :: Map String [TypeDesc]
                , globalMemory :: m
                , globalPointers :: Map (Ptr GlobalVariable) ptr
                , varStore :: VarStore var
                , nodeInstances :: Map NodeId [Gr.Node]
                , nodeGraph :: gr (Node mloc var ptr) (Transition var ptr)
                , startNode :: Gr.Node
                , nextNode :: Gr.Node
                , nextPointer :: ptr
                , nextLocation :: mloc
                , queuedNodes :: [(String,[(Ptr Loop,[QueueEntry var ptr])])]
                , delayedNodes :: [DelayedReturn]
                }

type Unrollment gr m mloc var ptr = StateT (UnrollGraph gr m mloc var ptr) SMT

data DelayedReturn = DelayedReturn { callingNode :: Gr.Node
                                   , callingFunction :: String
                                   , callingBlock :: Ptr BasicBlock
                                   , callingSubblock :: Integer
                                   , calledNode :: Gr.Node
                                   , callReturnsTo :: Ptr Instruction
                                   } deriving Show

data QueueEntry var ptr = QueueEntry { queuedNode :: NodeId
                                     , incomingNode :: Gr.Node
                                     , incomingReadNode :: Gr.Node
                                     , incomingEdge :: Transition var ptr
                                     } deriving Show

data Transition var ptr = TBegin
                        | TJump (Maybe (SMTExpr Bool))
                        | TCall [Either Val ptr]
                        | TReturn (Maybe (Either Val ptr))
                        | TDeliver (Ptr Instruction) Gr.Node

instance Show (Transition v m) where
  showsPrec _ TBegin = id
  showsPrec _ (TJump Nothing) = id
  showsPrec p (TJump (Just cond)) = showsPrec p cond
  showsPrec p (TCall args) = showString "call"
  showsPrec p (TReturn val) = case val of
    Nothing -> showString "ret"
    Just v -> showString "retval"
  showsPrec p (TDeliver to _) = id

newJoinPoint :: (Enum var,Ord var) => String -> TypeDesc -> Unrollment gr m mloc var ptr var
newJoinPoint name tp = do
  re <- get
  let (res,nstore) = newEntry name tp (varStore re)
  put (re { varStore = nstore })
  return res

newInput :: (Enum var,Ord var,Enum ptr) => String -> TypeDesc -> Unrollment gr m mloc var ptr (Either var ptr)
newInput name (PointerType tp) = do
  re <- get
  let ptr = nextPointer re
  put $ re { nextPointer = succ ptr }
  return $ Right ptr
newInput name tp = fmap Left $ newJoinPoint name tp

nodeSuccessors :: Gr.Graph gr => UnrollGraph gr m mloc var ptr -> Gr.Node -> [QueueEntry var ptr]
nodeSuccessors gr nd = case Gr.lab (nodeGraph gr) nd of
  Nothing -> error "nbis internal error: nodeSuccessors called with unknown node."
  Just st -> case nodeType st of
    RealizedStart fun _ _
      -> let blks = funDescrBlocks $ (allFunctions gr)!fun
             (start_blk,_,_) = head blks
         in [QueueEntry { queuedNode = IdBlock fun start_blk 0 
                        , incomingNode = nd
                        , incomingReadNode = nd
                        , incomingEdge = TBegin }]
    RealizedEnd fun ret -> []
    RealizedBlock { nodeFunctionNode = fnode
                  , nodeFinalization = fin 
                  } -> case fin of
      Jump trgs -> let Just fun_node = Gr.lab (nodeGraph gr) fnode
                       fun_name = nodeStartName $ nodeType fun_node
                   in [ QueueEntry { queuedNode = IdBlock fun_name blk sblk
                                   , incomingNode = nd
                                   , incomingReadNode = nd
                                   , incomingEdge = TJump cond
                                   }
                      | ((blk,sblk),cond) <- accumConditions trgs ]
      Return ret -> let Just fun_node = Gr.lab (nodeGraph gr) fnode
                        fun_name = nodeStartName $ nodeType fun_node
                    in [ QueueEntry { queuedNode = IdEnd fun_name
                                    , incomingNode = nd
                                    , incomingReadNode = nd
                                    , incomingEdge = TReturn ret } ]
      Call fname args rname -> [ QueueEntry { queuedNode = IdStart fname
                                            , incomingNode = nd
                                            , incomingReadNode = nd
                                            , incomingEdge = TCall args
                                            } ]

updateDelayed :: Gr.Graph gr => UnrollGraph gr m mloc var ptr -> Gr.Node -> Gr.Node -> [DelayedReturn] -> ([QueueEntry var ptr],[DelayedReturn])
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
                              , incomingNode = nd
                              , incomingReadNode = callingNode del
                              , incomingEdge = TDeliver (callReturnsTo del) (callingNode del)
                              }:qs,dels')
             else (qs,del:dels)

makeNode :: (Gr.DynGraph gr,Enum mloc,Enum ptr,Ord var,Enum var,MemoryModel m mloc ptr)
            => Maybe Gr.Node
            -> Maybe Gr.Node
            -> NodeId 
            -> Unrollment gr m mloc var ptr Gr.Node
makeNode read_from from nid = do
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
      let blks = funDescrBlocks $ (allFunctions gr)!fun
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
      act <- lift $ varNamed (case name of
                                 Nothing -> "act_"++fun++"_"++show blk++"_"++show sblk
                                 Just rname -> "act_"++rname++"_"++show sblk)
      (inps,args) <- gatherInputs read_from from nid
      let inps_def = Map.mapMaybe (\v -> case v of
                                      Left val -> Just val
                                      Right _ -> Nothing) inps
      inps_new <- mapM (\(tp,name) -> newInput ("inp_"++name) tp) $
                  Map.mapMaybe (\v -> case v of
                                   Right (tp,name) -> Just (tp,case name of
                                                               Nothing -> "dyn"
                                                               Just name' -> name')
                                   Left _ -> Nothing) inps
      let inps = Map.union inps_def (fmap (\i -> case i of
                                              Left x -> JoinPoint x
                                              Right x -> Pointer x) inps_new)
          allPhis = foldl (\s s' -> Set.union s (Set.fromList $ fmap fst s')) Set.empty (getPhis instrs)
      phis <- fmap Map.fromList $
              lift $ mapM (\from -> do
                              phi_cond <- varNamed "phi"
                              return (from,phi_cond)
                          ) (Set.toList allPhis)
      gr <- get
      let env = RealizationEnv { reFunction = fun
                               , reBlock = blk
                               , reSubblock = sblk
                               , reActivation = act
                               , reGlobals = globalPointers gr
                               , reArgs = Map.fromList fun_args
                               , rePhis = phis
                               }
          st = RealizationState { reLocals = inps
                                , reNextPtr = nextPointer gr
                                , reCurMemLoc = nextLocation gr
                                , reVarStore = varStore gr
                                }
      (fin,nst,outp) <- lift $ runRWST (realizeInstructions instrs) env st
      put $ gr { nextPointer = reNextPtr nst
               , varStore = reVarStore nst }
      return (RealizedBlock { nodeFunctionNode = ffid
                            , nodeBlock = blk
                            , nodeBlockName = name
                            , nodeSubblock = sblk
                            , nodeInput = inps_new
                            , nodePhis = phis
                            , nodeOutput = reLocals nst
                            , nodeFinalization = fin
                            , nodeMemProgram = reMemInstrs outp
                            , nodeWatchpoints = reWatchpoints outp
                            , nodeGuards = reGuards outp
                            },act,nextLocation gr,reCurMemLoc nst,reMemInstrs outp)
  ngr <- get
  let node_graph' = Gr.insNode (nextNode ngr,
                                Node { nodeActivation = act
                                     , nodeActivationProxy = act
                                     , nodeInputLoc = mloc_in
                                     , nodeOutputLoc = mloc_out
                                     , nodeType = node_type })
                    (nodeGraph ngr)
  nmem <- lift $ addProgram (globalMemory ngr) act mloc_in prog
  (p1,p2) <- getProxies
  --trace (debugMem nmem p1 p2) (return ())
  put $ ngr { nodeGraph = node_graph'
            , nextNode = succ (nextNode ngr)
            , nextLocation = succ mloc_out
            , globalMemory = nmem
            }
  return $ nextNode ngr

connectNodes :: (Gr.DynGraph gr,MemoryModel m mloc ptr,Ord var)
                => Gr.Node -> Gr.Node -> Transition var ptr -> Gr.Node 
                -> Unrollment gr m mloc var ptr ()
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
        TJump (Just c) -> nodeActivation nd_from .&&. c
        TJump Nothing -> nodeActivation nd_from
        TCall _ -> nodeActivation nd_from
        TReturn _ -> nodeActivation nd_from
        TDeliver _ _ -> nodeActivation nd_read_from
      eqs = case nodeType nd_from of
        RealizedStart fun_name args _ -> case nodeType nd_to of
          RealizedBlock {} -> []
        RealizedEnd _ ret -> case trans of
          TDeliver ret_name _ -> case nodeType nd_read_from of
            RealizedBlock { nodeOutput = outp_read } -> case nodeType nd_to of
              RealizedBlock { nodeInput = inp }
                -> let io = Map.elems $ Map.intersectionWith (\x y -> (x,y)) outp_read inp
                       io' = case (Map.lookup ret_name inp,ret) of
                         (Nothing,Nothing) -> io
                         (Just o_ret,Just i_ret) -> (case o_ret of
                                                        Left x -> JoinPoint x
                                                        Right x -> Pointer x,i_ret):io
                   in io'
        RealizedBlock { nodeOutput = outp
                      , nodeFinalization = fin }
          -> case fin of
          Jump conds -> case nodeType nd_to of
            RealizedBlock { nodeInput = inp } -> Map.elems $ Map.intersectionWith (\x y -> (x,y)) outp inp
          Return ret -> case nodeType nd_to of
            RealizedEnd _ ret' -> case (ret,ret') of
              (Nothing,Nothing) -> []
              (Just r1,Just r2) -> [(case r1 of
                                        Left x -> Value x
                                        Right x -> Pointer x,r2)]
          Call f args_out del -> case nodeType nd_to of
            RealizedStart _ args_in _ -> zipWith (\arg_o (_,arg_i) -> (case arg_o of
                                                                          Left x -> Value x
                                                                          Right x -> Pointer x,arg_i)) args_out args_in
  nproxy <- lift $ varNamed ("proxy_"++(case nodeType nd_to of
                                           RealizedStart { nodeStartName = fun } -> fun
                                           RealizedEnd { } -> "end"
                                           RealizedBlock { nodeBlock = blk
                                                         , nodeBlockName = blkname
                                                         } -> case blkname of
                                             Nothing -> show blk
                                             Just name' -> name'))
  lift $ assert $ nodeActivationProxy nd_to .==. (cond .||. nproxy)
  let (ptr_eqs,val_eqs) = foldr (\pair (ptr_eqs,val_eqs) -> case pair of
                                    (Pointer p1,Right p2) -> ((p1,p2):ptr_eqs,val_eqs)
                                    (Value v1,Left v2) -> (ptr_eqs,(Left v1,v2):val_eqs)
                                    (JoinPoint v1,Left v2) -> (ptr_eqs,(Right v1,v2):val_eqs)
                                ) ([],[]) eqs
  nstore <- foldlM (\store (v1,v2) -> case v1 of
                       Left v -> lift $ addJoin v2 v cond store
                       Right jp -> do
                         (v,store') <- lift $ readVar jp store
                         lift $ addJoin v2 v cond store'
                   ) (varStore gr) val_eqs
  mem' <- lift $ connectLocation (globalMemory gr)cond
          (nodeOutputLoc nd_from)
          (nodeInputLoc nd_to)
          ptr_eqs
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
  put $ gr { nodeGraph = (in_to,to,nd_to { nodeActivationProxy = nproxy },out_to) Gr.& gr1
           , globalMemory = mem'
           , varStore = nstore }

targetNode :: (Gr.DynGraph gr,Enum mloc,Enum ptr,Ord var,Enum var,MemoryModel m mloc ptr)
              => Gr.Node -> Gr.Node -> NodeId
              -> Unrollment gr m mloc var ptr (Gr.Node,Bool)
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

incrementGraph :: (Gr.DynGraph gr,Enum ptr,Enum mloc,Ord var,Enum var,MemoryModel m mloc ptr)
                  => Unrollment gr m mloc var ptr ()
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
      qs2 = if new then nodeSuccessors gr nd
            else []
  put $ gr { delayedNodes = ndl }
  mapM_ queueNode qs1
  mapM_ queueNode qs2

unrollGraphComplete :: UnrollGraph gr m mloc var ptr -> Bool
unrollGraphComplete gr = case queuedNodes gr of
  [] -> True
  _ -> False

data GrStr = GrStr String

instance Show GrStr where
  show (GrStr x) = x

unrollProgram :: (Gr.DynGraph gr,Integral ptr,Integral mloc,Integral var,MemoryModel m mloc ptr)
                => ProgDesc -> String 
                -> Unrollment gr m mloc var ptr a
                -> SMT a
unrollProgram prog@(funs,globs,tps,structs) init (f::Unrollment gr m mloc var ptr a) = do
  let (init_args,_,init_blks,_) = funs!init
      globs_mp = fmap (\(tp,_) -> tp) globs
      allfuns = fmap (\(sig,rtp,blks,loops)
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
                                          , funDescrGraph = getVariableInfo
                                                            (\(_,_,_,instrs) -> instrs)
                                                            (\instr -> let Just (blk,sblk) = Map.lookup instr defs
                                                                           Just nd = Map.lookup (blk,sblk) pmp
                                                                       in nd)
                                                            $ getReachability pgr
                                          , funDescrNodeMap = pmp
                                          , funDescrSCC = filter (\comp -> case comp of
                                                                     [nd] -> isSelfLoop nd pgr
                                                                     _ -> True
                                                                 ) (Gr.scc pgr)
                                          , funDescrDefines = defs
                                          , funDescrRealizationOrder = order
                                          , funDescrLoops = loops
                                          }
                     ) funs
  liftIO $ mapM_ (\(fname,f) -> do
                     writeFile ("program-"++fname++".dot") $ Gr.graphviz' (Gr.nmap (\((ptr,name,i,_),_,_) -> (GrStr $ case name of
                                                                                                                 Nothing -> show ptr
                                                                                                                 Just name' -> name',i)) (funDescrGraph f))
                 ) (Map.toList allfuns)
  liftIO $ putStrLn $ unlines $ concat $
    fmap (\(fname,FunctionDescr { funDescrArgs = sig
                                , funDescrReturnType = rtp
                                , funDescrBlocks = blks
                                , funDescrSCC = scc 
                                , funDescrRealizationOrder = order })
          -> ["SCC "++fname++": "++show scc
             ,"ORDER "++show order]
         ) (Map.toList allfuns)
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
                        , startNode = 0
                        , nextNode = 0
                        , nextPointer = cptr
                        , nextLocation = 0::mloc
                        , queuedNodes = []
                        , delayedNodes = []
                        }
  evalStateT (do
                 nd_start <- makeNode Nothing Nothing (IdStart { startFunction = init })
                 modify $ \gr -> gr { startNode = nd_start }
                 gr' <- get
                 mapM_ queueNode (nodeSuccessors gr' nd_start)
                 f) gr0

renderNodeGraph :: (Gr.Graph gr) => UnrollGraph gr m var mloc ptr -> String
renderNodeGraph gr = Gr.graphviz (nodeGraph gr) "nbis" (16,10) (1,1) Gr.Portrait

checkGraph :: (Gr.Graph gr) => UnrollGraph gr m mloc var ptr -> SMT (Maybe (ErrorDesc,[String]))
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
      _ -> perform (bmcDepth opts) (checkUser opts) (checkMemoryAccess opts) :: Unrollment Gr.Gr (SnowMemory Integer Integer) Integer Integer Integer ()
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

scanForNode :: Gr.Graph gr => gr (Node mloc var ptr) (Transition var ptr) -> Ptr BasicBlock -> Integer -> Gr.Node -> Maybe (Gr.Node,Node mloc var ptr)
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

gatherInputs :: Gr.Graph gr => Maybe Gr.Node -> Maybe Gr.Node -> NodeId
                -> Unrollment gr m mloc var ptr
                (Map (Ptr Instruction) (Either (VarKind var ptr) (TypeDesc,Maybe String)),Map (Ptr Argument) (Either var ptr))
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
    _ -> return (Map.empty,Map.empty)

nodeIdFunction :: NodeId -> String
nodeIdFunction (IdStart f) = f
nodeIdFunction (IdEnd f) = f
nodeIdFunction (IdBlock { idFunction = f }) = f

insertWithOrder :: Eq b => (a -> b) -> [b] -> a -> [a] -> [a]
insertWithOrder f order el [] = [el]
insertWithOrder f order el (x:xs) = updateOrder' order
  where
    updateOrder' [] = x:insertWithOrder f order el xs
    updateOrder' (y:ys)
      | y==f el    = el:x:xs
      | y==f x     = x:insertWithOrder f (y:ys) el xs
      | otherwise = updateOrder' ys

queueNode :: QueueEntry var ptr -> Unrollment gr m mloc var ptr ()
queueNode entr = do
  gr <- get
  let Just fdescr = Map.lookup (nodeIdFunction $ queuedNode entr) (allFunctions gr)
      loop_ptr = case queuedNode entr of
        IdBlock { idBlock = blk } -> case findLoopForBlock blk (funDescrLoops fdescr) of
          Nothing -> nullPtr
          Just (LoopDesc ptr _ _) -> ptr
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
        then (loop_ptr',insertWithOrder (\e -> case queuedNode e of
                                            IdBlock { idBlock = blk
                                                    , idSubblock = sblk
                                                    } -> (blk,sblk)
                                            _ -> (nullPtr,0)) ord entr entrs):qs
        else (loop_ptr',entrs):insert'' ord loop_ptr qs

dequeueNode :: Unrollment gr m mloc var ptr (QueueEntry var ptr)
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

queueRotate :: Unrollment gr m mloc var ptr ()
queueRotate = do
  gr <- get
  let nqueue = case queuedNodes gr of
        (f,(l,els):ys):xs -> xs++[(f,ys++[(l,els)])]
        [] -> []
        _ -> error "Invalid queue when rotating"
  put $ gr { queuedNodes = nqueue }

findLoopForBlock :: Ptr BasicBlock -> [LoopDesc] -> Maybe LoopDesc
findLoopForBlock blk [] = Nothing
findLoopForBlock blk (desc@(LoopDesc _ blks subs):loops)
  = if blk `elem` blks
    then (case findLoopForBlock blk subs of
             Nothing -> Just desc
             Just res -> Just res)
    else findLoopForBlock blk loops

getProxies :: Unrollment gr m mloc var ptr (Proxy mloc,Proxy ptr)
getProxies = return (Proxy,Proxy)