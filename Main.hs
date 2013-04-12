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
import Data.Map as Map hiding (foldl,foldr,(!),mapMaybe)
import Data.Set as Set hiding (foldl,foldr)
import Debug.Trace
import Prelude hiding (foldl,concat,mapM_,any,foldr,mapM,foldl1,all)
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

import LLVM.FFI.BasicBlock
import LLVM.FFI.Value
import LLVM.FFI.Instruction (Instruction)
import LLVM.FFI.Constant

(!) :: (Show k,Ord k) => Map k a -> k -> a
(!) mp k = case Map.lookup k mp of
             Nothing -> error $ "Couldn't find key "++show k++" in "++show (Map.keys mp)
             Just r -> r

{-
valSwitch :: MemoryModel m => m -> TypeDesc -> [(Val m,SMTExpr Bool)] -> SMT (Val m,m)
valSwitch mem _ [(val,_)] = return (val,mem)
valSwitch mem (PointerType _) choices = do
  (res,mem') <- memPtrSwitch mem [ (ptr,cond) | (PointerValue ptr,cond) <- choices ]
  return $ (PointerValue res,mem')
valSwitch mem tp choices = return (DirectValue $ mkSwitch choices,mem)
  where
    mkSwitch [(val,cond)] = valValue val
    mkSwitch ((val,cond):rest) = ite cond (valValue val) (mkSwitch rest)

newValue :: MemoryModel mem => mem -> TypeDesc -> SMT (Val mem,mem)
newValue mem (PointerType tp) = let (ptr,nmem) = memPtrNew mem
                                in return (PointerValue ptr,nmem)
newValue mem tp = do
  v <- varAnn (fromIntegral $ bitWidth tp)
  return (DirectValue v,mem) -}

data NodeId = IdStart { startFunction :: String }
            | IdEnd { endFunction :: String }
            | IdBlock { idFunction :: String
                      , idBlock :: Ptr BasicBlock
                      , idSubblock :: Integer 
                      }
            deriving (Eq,Ord,Show)

data Node m = Node { nodeActivation :: SMTExpr Bool
                   , nodeActivationProxy :: SMTExpr Bool
                   , nodeType :: NodeType m
                   }

instance Show (Node m) where
  show nd = case nodeType nd of
    RealizedStart fun _ _ -> "start "++fun
    RealizedEnd _ _ -> "end"
    RealizedBlock { nodeBlock = blk
                  , nodeSubblock = sblk } -> show blk++"."++show sblk

data NodeType ptr
  = RealizedStart { nodeStartName :: String
                  , nodeArguments :: [(Ptr Argument,Val ptr)]
                  , nodeRealizedEnd :: Maybe Gr.Node }
  | RealizedEnd { nodeEndFunctionNode :: Gr.Node
                , nodeReturns :: Maybe (Val ptr) }
  | RealizedBlock { nodeFunctionNode :: Gr.Node
                  , nodeBlock :: Ptr BasicBlock
                  , nodeSubblock :: Integer
                  , nodeInput :: Map (Ptr Instruction) (Val ptr)
                  , nodePhis :: Map (Ptr BasicBlock) (SMTExpr Bool)
                  , nodeOutput :: Map (Ptr Instruction) (Val ptr)
                  , nodeFinalization :: BlockFinalization ptr
                  , nodeMemProgram :: MemoryProgram ptr
                  , nodeWatchpoints :: [Watchpoint]
                  , nodeGuards :: [Guard]
                  }
    deriving (Show)

data UnrollGraph gr m ptr
  = UnrollGraph { allFunctions :: Map String ([(Ptr Argument,TypeDesc)],TypeDesc,
                                              [(Ptr BasicBlock,[(BlockSig,[InstrDesc Operand])])])
                , allStructs :: Map String [TypeDesc]
                , globalMemory :: m
                , globalPointers :: Map (Ptr GlobalVariable) ptr
                , nodeInstances :: Map NodeId [Gr.Node]
                , nodeGraph :: gr (Node ptr) (Transition ptr)
                , startNode :: Gr.Node
                , nextNode :: Gr.Node
                , nextPointer :: ptr
                , queuedNodes :: [QueueEntry ptr]
                , delayedNodes :: [DelayedReturn]
                }

type Unrollment gr m ptr = StateT (UnrollGraph gr m ptr) SMT

data DelayedReturn = DelayedReturn { callingNode :: Gr.Node
                                   , callingFunction :: String
                                   , callingBlock :: Ptr BasicBlock
                                   , callingSubblock :: Integer
                                   , calledNode :: Gr.Node
                                   , callReturnsTo :: Ptr Instruction
                                   } deriving Show

data QueueEntry ptr = QueueEntry { queuedNode :: NodeId
                                 , incomingNode :: Gr.Node
                                 , incomingReadNode :: Gr.Node
                                 , incomingEdge :: Transition ptr
                                 } deriving Show

data Transition ptr = TBegin
                    | TJump (Maybe (SMTExpr Bool))
                    | TCall [Val ptr]
                    | TReturn (Maybe (Val ptr))
                    | TDeliver (Ptr Instruction)

instance Show (Transition m) where
  showsPrec _ TBegin = id
  showsPrec _ (TJump Nothing) = id
  showsPrec p (TJump (Just cond)) = showsPrec p cond
  showsPrec p (TCall args) = showString "call"
  showsPrec p (TReturn val) = case val of
    Nothing -> showString "ret"
    Just v -> showString "retval"
  showsPrec p (TDeliver to) = id

newValue :: Enum ptr => TypeDesc -> Unrollment gr m ptr (Val ptr)
newValue (PointerType tp) = do
  st <- get
  let ptr = nextPointer st
  put $ st { nextPointer = succ ptr }
  return $ PointerValue ptr
newValue tp = do
  v <- lift $ varNamedAnn "inputVar" (fromIntegral $ bitWidth tp)
  return (DirectValue v)

isForwardJump :: String -> String -> [(String,a)] -> Bool
isForwardJump from to ((trg,_):rest)
  | trg == from = True
  | trg == to = False
  | otherwise = isForwardJump from to rest

nodeSuccessors :: Gr.Graph gr => UnrollGraph gr m ptr -> Gr.Node -> [QueueEntry ptr]
nodeSuccessors gr nd = case Gr.lab (nodeGraph gr) nd of
  Nothing -> error "nbis internal error: nodeSuccessors called with unknown node."
  Just st -> case nodeType st of
    RealizedStart fun _ _
      -> let (_,_,blks) = (allFunctions gr)!fun
             start_blk = fst $ head blks
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

updateDelayed :: Gr.Graph gr => UnrollGraph gr m ptr -> Gr.Node -> Gr.Node -> [DelayedReturn] -> ([QueueEntry ptr],[DelayedReturn])
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
                              , incomingEdge = TDeliver (callReturnsTo del)
                              }:qs,dels')
             else (qs,del:dels)

makeNode :: (Gr.DynGraph gr,Enum ptr,MemoryModel m ptr)
            => Maybe Gr.Node
            -> Maybe Gr.Node
            -> NodeId 
            -> Unrollment gr m ptr Gr.Node
makeNode read_from from nid = do
  let act_name = case nid of
        IdStart fun -> "start_"++fun
        IdEnd fun -> "end_"++fun
        IdBlock fun blk sblk -> "act_"++fun++"_"++show blk++"_"++show sblk
  act <- case from of
    Nothing -> return $ constant True -- Don't use an activation variable for the first node
    Just _ -> lift $ varNamed act_name
  (node_type,prog) <- case nid of
    IdStart fun -> do
      gr <- get
      let (args,rtp,blks) = (allFunctions gr)!fun
      args' <- mapM (\(name,tp) -> do
                        val <- newValue tp 
                        return (name,val)) args
      {-let io_p = mapMaybe (\(name,val) -> case val of
                              PointerValue ptr -> Just ptr
                              _ -> Nothing
                          ) args'-}
      return (RealizedStart fun args' Nothing,[])
    IdEnd fun -> do
      gr <- get
      let (args,rtp,blks) = (allFunctions gr)!fun
          Just pnode = from
          Just (Node { nodeType = RealizedBlock { nodeFunctionNode = fnode } })
            = Gr.lab (nodeGraph gr) pnode
      rv <- case rtp of
        VoidType -> return Nothing
        _ -> do
          v <- newValue rtp
          return (Just v)
      -- Set the pointer of the function start node
      modify (\gr -> case Gr.match fnode (nodeGraph gr) of
                 (Just (inc,_,nd@Node { nodeType = RealizedStart fun args Nothing },outc),gr')
                   -> gr { nodeGraph = (inc,fnode,nd { nodeType = RealizedStart fun args (Just $ nextNode gr) },outc) Gr.& gr' }
             )
      return (RealizedEnd fnode rv,[])
    IdBlock fun blk sblk -> do
      gr <- get
      let (args,rtp,blks) = (allFunctions gr)!fun
          subs = case List.find (\(name,_)
                                 -> name == blk
                                ) blks of
                   Just (_,s) -> s
                   Nothing -> error $ "Failed to find subblock "++show blk++" of function "++fun
          (sig,instrs) = subs `genericIndex` sblk
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
      inps <- mapM newValue (blockInputs sig)
      let allPhis = foldl (\s (_,s') -> Set.union s s') Set.empty (blockPhis sig)
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
                                }
      (fin,nst,outp) <- lift $ runRWST (realizeInstructions instrs) env st
      put $ gr { nextPointer = reNextPtr nst }
      return (RealizedBlock { nodeFunctionNode = ffid
                            , nodeBlock = blk
                            , nodeSubblock = sblk
                            , nodeInput = inps
                            , nodePhis = phis
                            , nodeOutput = reLocals nst
                            , nodeFinalization = fin
                            , nodeMemProgram = reMemInstrs outp
                            , nodeWatchpoints = reWatchpoints outp
                            , nodeGuards = reGuards outp
                            },reMemInstrs outp)
  ngr <- get
  let node_graph' = Gr.insNode (nextNode ngr,
                                Node { nodeActivation = act
                                     , nodeActivationProxy = act
                                     , nodeType = node_type })
                    (nodeGraph ngr)
  nmem <- lift $ addProgram (globalMemory ngr) (nextNode ngr) prog
  put $ ngr { nodeGraph = node_graph'
            , nextNode = succ (nextNode ngr)
            , globalMemory = nmem
            }
  return $ nextNode ngr

connectNodes :: (Gr.DynGraph gr,MemoryModel m ptr)
                => Gr.Node -> Gr.Node -> Transition ptr -> Gr.Node 
                -> Unrollment gr m ptr ()
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
        TDeliver _ -> nodeActivation nd_read_from
      eqs = case nodeType nd_from of
        RealizedStart fun_name args _ -> case nodeType nd_to of
          RealizedBlock {} -> [ (PointerValue v,PointerValue v) | (_,PointerValue v) <- args ]
        RealizedEnd _ ret -> case trans of
          TDeliver ret_name -> case nodeType nd_read_from of
            RealizedBlock { nodeOutput = outp_read } -> case nodeType nd_to of
              RealizedBlock { nodeInput = inp }
                -> let io = Map.elems $ Map.intersectionWith (\x y -> (x,y)) inp outp_read
                       io' = case (Map.lookup ret_name inp,ret) of
                         (Nothing,Nothing) -> io
                         (Just i_ret,Just o_ret) -> (i_ret,o_ret):io
                   in io'
        RealizedBlock { nodeOutput = outp
                      , nodeFinalization = fin }
          -> case fin of
          Jump conds -> case nodeType nd_to of
            RealizedBlock { nodeInput = inp } -> Map.elems $ Map.intersectionWith (\x y -> (x,y)) inp outp
          Return ret -> case nodeType nd_to of
            RealizedEnd _ ret' -> case (ret,ret') of
              (Nothing,Nothing) -> []
              (Just r1,Just r2) -> [(r2,r1)]
          Call f args del -> case nodeType nd_to of
            RealizedStart _ args' _ -> zipWith (\(_,arg_i) arg_o -> (arg_i,arg_o)) args' args
  nproxy <- lift $ varNamed "proxy"
  lift $ assert $ nodeActivationProxy nd_to .==. (cond .||. nproxy)
  let (ptr_eqs,val_eqs) = foldr (\pair (ptr_eqs,val_eqs) -> case pair of
                                    (PointerValue p1,PointerValue p2) -> ((p1,p2):ptr_eqs,val_eqs)
                                    _ -> (ptr_eqs,pair:val_eqs)
                                ) ([],[]) eqs
  mapM_ (\(v1,v2) -> lift $ assert $ cond .=>. valEq v1 v2) val_eqs
  mem' <- lift $ connectPrograms (globalMemory gr) cond from to ptr_eqs
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
           , globalMemory = mem' }

targetNode :: (Gr.DynGraph gr,Enum ptr,MemoryModel m ptr)
              => Gr.Node -> Gr.Node -> NodeId
              -> Unrollment gr m ptr (Gr.Node,Bool)
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
                      [_] -> True
                      _ -> False
                  ) (Gr.scc ngr) && not (Gr.hasLoop ngr)
           then getNode gr (Just x) xs
           else res

incrementGraph :: (Gr.DynGraph gr,Enum ptr,MemoryModel m ptr)
                  => Unrollment gr m ptr ()
incrementGraph = do
  gr <- get
  case queuedNodes gr of
    [] -> error "incrementGraph: Nothing more to realize."
    (x:xs) -> do
      -- Remove element from queue 
      put $ gr { queuedNodes = xs }
      -- and determine the target node
      (nd,new) <- targetNode (incomingReadNode x) (incomingNode x) (queuedNode x)
      -- Connect the nodes
      connectNodes (incomingNode x) 
        (incomingReadNode x)
        (incomingEdge x) nd
      -- Add an edge to the node graph
      modify $ \gr -> gr { nodeGraph = Gr.insEdge (incomingNode x,nd,
                                                   incomingEdge x)
                                       (nodeGraph gr) }
      -- Update delayed nodes
      gr <- get
      let (qs1,ndl) = updateDelayed gr (incomingNode x) nd (delayedNodes gr)
          qs2 = if new then nodeSuccessors gr nd
                else []
      put $ gr { queuedNodes = (queuedNodes gr) ++ 
                               qs1 ++ qs2
               , delayedNodes = ndl }

unrollGraphComplete :: UnrollGraph gr m ptr -> Bool
unrollGraphComplete gr = case queuedNodes gr of
  [] -> True
  _ -> False

unrollProgram :: (Gr.DynGraph gr,Integral ptr,MemoryModel m ptr)
                => ProgDesc -> String 
                -> Unrollment gr m ptr a 
                -> SMT a
unrollProgram prog@(funs,globs,tps,structs) init (f::Unrollment gr m ptr a) = do
  let (init_args,_,init_blks) = funs!init
      globs_mp = fmap (\(tp,_) -> tp) globs
      allfuns = fmap (\(sig,rtp,blks) 
                      -> let block_sigs = mkBlockSigs blks
                         in (sig,rtp,
                             fmap (\(blk_name,subs) 
                                   -> (blk_name,fmap (\(i,instrs) 
                                                      -> (block_sigs!(blk_name,i),instrs)
                                                     ) (zip [0..] subs)
                                      )
                                  ) blks
                            )
                     ) funs
  mem0 <- memNew (undefined::ptr) tps structs
  let ((cptr,prog),globs') = mapAccumL (\(ptr',prog') (tp,cont) 
                                        -> ((succ ptr',(ptr',tp,cont):prog'),ptr')
                                       ) (0,[]) globs
  mem1 <- foldlM (\cmem (ptr,tp,cont) -> case cont of
                     Just cont' -> addGlobal cmem ptr tp cont'
                     Nothing -> return cmem
                 ) mem0 prog
  let gr0 = UnrollGraph { allFunctions = allfuns
                        , allStructs = structs
                        , globalMemory = mem1
                        , globalPointers = globs'
                        , nodeInstances = Map.empty
                        , nodeGraph = Gr.empty
                        , startNode = 0
                        , nextNode = 0
                        , nextPointer = cptr
                        , queuedNodes = []
                        , delayedNodes = []
                        }
  evalStateT (do
                 nd_start <- makeNode Nothing Nothing (IdStart { startFunction = init })
                 modify $ \gr -> gr { startNode = nd_start 
                                    , queuedNodes = nodeSuccessors gr nd_start }
                 f) gr0
  
  {-(nd,gr1) <- makeNode gr0 Nothing (IdStart { startFunction = init })
  return (gr1 { queuedNodes = nodeSuccessors gr1 nd
              , startNode = nd })-}

renderNodeGraph :: (Gr.Graph gr) => UnrollGraph gr m ptr -> String
renderNodeGraph gr = Gr.graphviz (nodeGraph gr) "nbis" (16,10) (1,1) Gr.Portrait

checkGraph :: (Gr.Graph gr) => UnrollGraph gr m ptr -> SMT (Maybe (ErrorDesc,[String]))
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
  progs <- mapM getProgram (files opts)
  let program = foldl1 mergePrograms progs
  withSMTSolver (case solver opts of
                    Nothing -> "~/debug-smt.sh output-" ++ (entryPoint opts) ++ ".smt"
                    Just bin -> bin) $ do
    setOption (PrintSuccess False)
    setOption (ProduceModels True)
    unrollProgram program (entryPoint opts) $ case memoryModelOption opts of
      _ -> perform (bmcDepth opts) (checkUser opts) (checkMemoryAccess opts) :: Unrollment Gr.Gr (SnowMemory Integer) Integer ()
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
                   --liftIO $ print $ queuedNodes gr
                   --liftIO $ print $ delayedNodes gr
                   --liftIO $ putStrLn $ "Realizing "++show (queuedState $ head $ queue gr')++"("++show (incomingEdge $ head $ queue gr')++")"
                   --liftIO $ putStrLn $ memDebug (globalMemory gr)
                   incrementGraph
                   ngr <- get
                   res <- lift $ checkGraph ngr
                   --liftIO $ writeFile ("graph"++show i++".dot") (renderNodeGraph ngr)
                   case res of
                     Nothing -> check (i+1) depth
                     Just (err,watch) -> do
                       liftIO $ putStrLn $ "Error "++show err++" found."
                       mapM_ (\str -> liftIO $ putStrLn str) watch
                       return ())
