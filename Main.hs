{-# LANGUAGE DeriveDataTypeable,TypeFamilies,FlexibleContexts,RankNTypes,OverloadedStrings #-}
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
import MemoryModel.Plain-}
import MemoryModel.CBMCLike
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
import Control.Monad.State (runStateT)

import LLVM.FFI.BasicBlock
import LLVM.FFI.Value
import LLVM.FFI.Instruction
import LLVM.FFI.Constant

(!) :: (Show k,Ord k) => Map k a -> k -> a
(!) mp k = case Map.lookup k mp of
             Nothing -> error $ "Couldn't find key "++show k++" in "++show (Map.keys mp)
             Just r -> r

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
  return (DirectValue v,mem)

data NodeId = IdStart { startFunction :: String }
            | IdEnd { endFunction :: String }
            | IdBlock { idFunction :: String
                      , idBlock :: Ptr BasicBlock
                      , idSubblock :: Integer 
                      }
            deriving (Eq,Ord,Show)

data Node m = Node { nodeActivation :: SMTExpr Bool
                   , nodeActivationProxy :: SMTExpr Bool
                   , nodeMemoryIn :: LocalMem m
                   , nodeMemoryOut :: LocalMem m
                   , nodeType :: NodeType m
                   }

instance Show (Node m) where
  show nd = case nodeType nd of
    RealizedStart fun _ -> "start "++fun
    RealizedEnd _ _ -> "end"
    RealizedBlock { nodeBlock = blk
                  , nodeSubblock = sblk } -> show blk++"."++show sblk

data NodeType m 
  = RealizedStart { nodeStartName :: String
                  , nodeArguments :: [(Ptr Argument,Val m)] }
  | RealizedEnd { nodeEndFunctionNode :: Gr.Node
                , nodeReturns :: Maybe (Val m) }
  | RealizedBlock { nodeFunctionNode :: Gr.Node
                  , nodeBlock :: Ptr BasicBlock
                  , nodeSubblock :: Integer
                  , nodeInput :: Map (Ptr Instruction) (Val m)
                  , nodePhis :: Map (Ptr BasicBlock) (SMTExpr Bool)
                  , nodeOutput :: Map (Ptr Instruction) (Val m)
                  , nodeFinalization :: BlockFinalization m
                  , nodeWatchpoints :: [Watchpoint]
                  , nodeGuards :: [Guard]
                  }
    deriving (Show)

data UnrollGraph gr m
  = UnrollGraph { allFunctions :: Map String ([(Ptr Argument,TypeDesc)],TypeDesc,
                                              [(Ptr BasicBlock,[(BlockSig,[InstrDesc Operand])])],
                                              Map (Ptr Instruction) TypeDesc
                                             )
                , globalMemory :: m
                , globalPointers :: Map (Ptr GlobalVariable) (Pointer m)
                , nodeInstances :: Map NodeId [Gr.Node]
                , nodeGraph :: gr (Node m) (Transition m)
                , startNode :: Gr.Node
                , nextNode :: Gr.Node
                , queuedNodes :: [QueueEntry m]
                , delayedNodes :: [DelayedReturn]
                }

data DelayedReturn = DelayedReturn { callingNode :: Gr.Node
                                   , callingFunction :: String
                                   , callingBlock :: Ptr BasicBlock
                                   , callingSubblock :: Integer
                                   , calledNode :: Gr.Node
                                   , callReturnsTo :: Ptr Instruction
                                   } deriving Show

data QueueEntry m = QueueEntry { queuedNode :: NodeId
                               , incomingNode :: Gr.Node
                               , incomingReadNode :: Gr.Node
                               , incomingEdge :: Transition m
                               } deriving Show

data Transition m = TBegin
                  | TJump (Maybe (SMTExpr Bool))
                  | TCall [Val m]
                  | TReturn (Maybe (Val m))
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

isForwardJump :: String -> String -> [(String,a)] -> Bool
isForwardJump from to ((trg,_):rest)
  | trg == from = True
  | trg == to = False
  | otherwise = isForwardJump from to rest

nodeSuccessors :: Gr.Graph gr => UnrollGraph gr m -> Gr.Node -> [QueueEntry m]
nodeSuccessors gr nd = case Gr.lab (nodeGraph gr) nd of
  Nothing -> error "nbis internal error: nodeSuccessors called with unknown node."
  Just st -> case nodeType st of
    RealizedStart fun _ 
      -> let (_,_,blks,_) = (allFunctions gr)!fun
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

updateDelayed :: Gr.Graph gr => UnrollGraph gr m -> Gr.Node -> [DelayedReturn] -> ([QueueEntry m],[DelayedReturn])
updateDelayed gr nd delayed
  = case Gr.lab (nodeGraph gr) nd of
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

makeNode :: (MemoryModel m,Gr.DynGraph gr)
            => UnrollGraph gr m
            -> Maybe Gr.Node
            -> NodeId 
            -> SMT (Gr.Node,UnrollGraph gr m)
makeNode gr from nid = do
  let act_name = case nid of
        IdStart fun -> "start_"++fun
        IdEnd fun -> "end_"++fun
        IdBlock fun blk sblk -> "act_"++fun++"_"++show blk++"_"++show sblk
  act <- varNamed act_name
  mem_in <- memInit (globalMemory gr)
  (node_type,mem,mem_out) <- case nid of
    IdStart fun -> do
      let (args,rtp,blks,_) = (allFunctions gr)!fun
          makeArgs [] cmem = return ([],cmem)
          makeArgs ((name,tp):rest) cmem = do
            (val,cmem') <- newValue cmem tp
            (rest',cmem'') <- makeArgs rest cmem'
            return ((name,val):rest',cmem'')
      (args',mem') <- makeArgs args (globalMemory gr)
      mem_out <- memInit mem'
      return (RealizedStart fun args',mem',mem_out)
    IdEnd fun -> do
      let (args,rtp,blks,_) = (allFunctions gr)!fun
          Just pnode = from
          Just (Node { nodeType = RealizedBlock { nodeFunctionNode = fnode } })
            = Gr.lab (nodeGraph gr) pnode
      (rv,mem') <- case rtp of
        VoidType -> return (Nothing,globalMemory gr)
        _ -> do
          (v,mem') <- newValue (globalMemory gr) rtp
          return (Just v,mem')
      mem_out <- memInit mem'
      return (RealizedEnd fnode rv,mem',mem_out)
    IdBlock fun blk sblk -> do
      let (args,rtp,blks,pred) = (allFunctions gr)!fun
          Just (_,subs) = List.find (\(name,_) 
                                     -> name == blk
                                    ) blks
          (sig,instrs) = subs `genericIndex` sblk
          Just fnid = from
          Just (Node { nodeType = from_nt }) 
            = Gr.lab (nodeGraph gr) fnid
          ffid = case from_nt of
            RealizedStart _ _ -> fnid
            RealizedBlock { nodeFunctionNode = n } -> n
          Just (Node { nodeType = RealizedStart _ fun_args }) = Gr.lab (nodeGraph gr) ffid
          mkVars [] cmem = return ([],cmem)
          mkVars ((name,tp):rest) cmem = do
            (val,nmem1) <- newValue cmem tp
            (vals,nmem2) <- mkVars rest nmem1
            return ((name,val):vals,nmem2)
      (inps,mem1) <- mkVars (Map.toList (blockInputs sig)) (globalMemory gr)
      let allPhis = foldl (\s (_,s') -> Set.union s s') Set.empty (blockPhis sig)
      phis <- fmap Map.fromList $
              mapM (\from -> do
                       phi_cond <- varNamed "phi"
                       return (from,phi_cond)
                   ) (Set.toList allPhis)
      --(phi_inps,mem2) <- mkVars (Map.toList $ fmap fst $ blockPhis sig) mem1
      let all_inp = Map.fromList inps --Map.union (Map.fromList inps) (Map.fromList phi_inps)
          env = RealizationEnv { reFunction = fun
                               , reBlock = blk
                               , reSubblock = sblk
                               , reActivation = act
                               , reMemChanged = False
                               , reGlobalMem = mem1
                               , reLocalMem = mem_in
                               , reGlobals = globalPointers gr
                               , reArgs = Map.fromList fun_args
                               , reLocals = all_inp
                               , rePhis = phis
                               , reWatchpoints = []
                               , reGuards = []
                               , rePrediction = pred
                               }
      (fin,nenv) <- runStateT (realizeInstructions instrs) env
      return (RealizedBlock { nodeFunctionNode = ffid
                            , nodeBlock = blk
                            , nodeSubblock = sblk
                            , nodeInput = all_inp
                            , nodePhis = phis
                            , nodeOutput = reLocals nenv
                            , nodeFinalization = fin
                            , nodeWatchpoints = reWatchpoints nenv
                            , nodeGuards = reGuards nenv
                            },reGlobalMem nenv,reLocalMem nenv)
  let node_graph' = Gr.insNode (nextNode gr,Node { nodeActivation = act
                                                 , nodeActivationProxy = act
                                                 , nodeMemoryIn = mem_in
                                                 , nodeMemoryOut = mem_out
                                                 , nodeType = node_type })
                    (nodeGraph gr)
  return (nextNode gr,gr { nodeGraph = node_graph'
                         , nextNode = (nextNode gr) + 1
                         , globalMemory = mem
                         })

connectNodes :: (Gr.DynGraph gr,MemoryModel m) 
                => Gr.Node -> Gr.Node -> Transition m -> Gr.Node 
                -> UnrollGraph gr m -> SMT (UnrollGraph gr m)
connectNodes from read_from trans to gr = do
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
        RealizedStart fun_name args -> case nodeType nd_to of
          RealizedBlock {} -> []
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
            RealizedStart _ args' -> zipWith (\(_,arg_i) arg_o -> (arg_i,arg_o)) args' args
      mkEqs cond [] cmem = return cmem
      mkEqs cond ((PointerValue p1,PointerValue p2):vs) cmem = do
        cmem' <- memPtrExtend cmem p1 p2 cond
        mkEqs cond vs cmem'
      mkEqs cond ((v1,v2):vs) cmem = do
        let (b,cmem') = valEq cmem v1 v2
        assert $ cond .=>. b
        mkEqs cond vs cmem'
  nproxy <- varNamed "proxy"
  assert $ nodeActivationProxy nd_to .==. (cond .||. nproxy)
  mem' <- mkEqs cond eqs (globalMemory gr)
  case nodeType nd_from of
    RealizedBlock { nodeBlock = blk } -> case nodeType nd_to of
      RealizedBlock { nodePhis = phis } 
        -> assert $ cond .=>. app and' [ if blk==blk' 
                                         then cond'
                                         else not' cond'
                                       | (blk',cond') <- Map.toList phis ]
      _ -> return ()
    _ -> return ()
  (nloc,mem'') <- memEq mem' cond (nodeMemoryOut nd_from) (nodeMemoryIn nd_to)
  return $ gr { nodeGraph = (in_to,to,nd_to { nodeActivationProxy = nproxy 
                                            , nodeMemoryIn = nloc },out_to) Gr.& gr1
              , globalMemory = mem'' }

targetNode :: (Gr.DynGraph gr,MemoryModel m) 
              => UnrollGraph gr m
              -> Gr.Node -> NodeId 
              -> SMT (Gr.Node,Bool,UnrollGraph gr m)
targetNode gr from to 
  = case getNode Nothing insts of
    Nothing -> do
      (nd,gr1) <- makeNode gr (Just from) to
      return 
        (nd,True,
         gr1 { nodeInstances 
                 = Map.alter (\minsts -> case minsts of
                                 Nothing -> Just [nd]
                                 Just nds -> Just $ nd:nds
                             ) to 
                   (nodeInstances gr1)
             })
    Just nd -> return (nd,False,gr)
  where
    insts = case Map.lookup to (nodeInstances gr) of
      Nothing -> []
      Just i -> i
    getNode res [] = res
    getNode res (x:xs) 
      = let ngr = Gr.insEdge (from,x,undefined) (nodeGraph gr)
        in if all (\x -> case x of
                      [_] -> True
                      _ -> False
                  ) (Gr.scc ngr) && not (Gr.hasLoop ngr)
           then getNode (Just x) xs
           else res

incrementGraph :: (Gr.DynGraph gr,MemoryModel m)
                  => UnrollGraph gr m
                  -> SMT (UnrollGraph gr m)
incrementGraph gr
  = case queuedNodes gr of
    [] -> error "incrementGraph: Nothing more to realize."
    (x:xs) -> do
      -- Remove element from queue and determine
      -- the target node.
      (nd,new,gr1) <- targetNode 
                      (gr { queuedNodes = xs })
                      (incomingNode x)
                      (queuedNode x) 
      -- Connect the nodes
      gr2 <- connectNodes (incomingNode x) 
             (incomingReadNode x) 
             (incomingEdge x) nd gr1
      -- Add an edge to the node graph
      let gr3 = gr2 { nodeGraph 
                        = Gr.insEdge (incomingNode x,nd,
                                      incomingEdge x)
                          (nodeGraph gr2) }
          (qs1,ndl) = updateDelayed gr3 nd 
                      (delayedNodes gr3)
          qs2 = if new then nodeSuccessors gr3 nd
                else []
      return (gr3 { queuedNodes = (queuedNodes gr3) ++ 
                                  qs1 ++ qs2
                  , delayedNodes = ndl })

unrollGraphComplete :: UnrollGraph gr m -> Bool
unrollGraphComplete gr = case queuedNodes gr of
  [] -> True
  _ -> False

initialGraph :: (MemoryModel m,Gr.DynGraph gr) 
                => ProgDesc -> String 
                -> SMT (UnrollGraph gr m)
initialGraph prog@(funs,globs) init = do
  let (init_args,_,init_blks) = funs!init
      tps = getProgramTypes prog
      globs_mp = fmap (\(tp,_) -> tp) globs
      allfuns = fmap (\(sig,rtp,blks) 
                      -> let block_sigs = mkBlockSigs blks
                         in (sig,rtp,
                             fmap (\(blk_name,subs) 
                                   -> (blk_name,fmap (\(i,instrs) 
                                                      -> (block_sigs!(blk_name,i),instrs)
                                                     ) (zip [0..] subs)
                                      )
                                  ) blks,
                             predictMallocUse (concat [ instrs | (_,sblks) <- blks, instrs <- sblks ])
                            )
                     ) funs
      {-mkPointers ptrs [] cmem = (ptrs,cmem)
      mkPointers ptrs ((name,(tp,_,_)):rest) cmem 
        = let (ptr,cmem') = memPtrNull cmem
          in mkPointers (Map.insert name ptr ptrs) rest cmem'-}
      mkPointers ptrs [] cmem lmem = return (ptrs,cmem,lmem)
      mkPointers ptrs ((name,(tp,cont)):rest) cmem lmem = do
        (ptr,cmem',lmem') <- memAlloc tp (Left (typeWidth tp)) cont cmem lmem
        mkPointers (Map.insert name ptr ptrs) rest cmem' lmem'
  mem0 <- memNew tps
  lmem0 <- memInit mem0
  (ptrs,mem1,lmem1) <- mkPointers Map.empty (Map.toList globs) mem0 lmem0
  let gr0 = UnrollGraph { allFunctions = allfuns
                        , globalMemory = mem1
                        , globalPointers = ptrs
                        , nodeInstances = Map.empty
                        , nodeGraph = Gr.empty
                        , startNode = 0
                        , nextNode = 0
                        , queuedNodes = []
                        , delayedNodes = []
                        }
  (nd,gr1) <- makeNode gr0 Nothing (IdStart { startFunction = init })
  return (gr1 { queuedNodes = nodeSuccessors gr1 nd
              , startNode = nd })

renderNodeGraph :: (Gr.Graph gr) => UnrollGraph gr m -> String
renderNodeGraph gr = Gr.graphviz (nodeGraph gr) "nbis" (16,10) (1,1) Gr.Portrait

checkGraph :: (Gr.Graph gr,MemoryModel m) => UnrollGraph gr m -> SMT (Maybe (ErrorDesc,[String]))
checkGraph gr = stack $ do
  -- Set all proxies to false (except for the start node)
  mapM_ (\(nd_id,nd) -> if nd_id == startNode gr
                        then assert $ nodeActivationProxy nd
                        else assert $ not' $ nodeActivationProxy nd
        ) (Gr.labNodes (nodeGraph gr))
  let errs = concat $ fmap (\(_,nd) -> case nodeType nd of
                               RealizedBlock { nodeGuards = g } -> g
                               _ -> []) (Gr.labNodes (nodeGraph gr))
      watchs = concat $ fmap (\(_,nd) -> case nodeType nd of
                                 RealizedBlock { nodeWatchpoints = w } -> w
                                 _ -> []) (Gr.labNodes (nodeGraph gr))
  liftIO $ putStrLn $ "Checking "++show (length errs)++" errors..."
  if Prelude.null errs
    then return Nothing
    else (do
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
    case memoryModelOption opts of
      _ -> perform program (entryPoint opts) (bmcDepth opts) (checkUser opts) (checkMemoryAccess opts) 
           :: SMT (UnrollGraph Gr.Gr (Memory Gr.Gr))
    return ()
  where
    {-perform :: (MemoryModel mem,DynGraph gr)
               => ProgDesc -> String -> Integer -> Bool -> Bool -> SMT (StateGraph gr mem Integer cont)-}
    perform program entry depth check_user check_mem = do
      gr <- initialGraph program entry
      check gr 0 depth
      
    check gr i depth
      | i == depth = return gr
      | unrollGraphComplete gr = return gr
      | otherwise = do
        liftIO $ putStrLn $ "Step "++show i++":"
        --liftIO $ print $ queuedNodes gr
        --liftIO $ print $ delayedNodes gr
        --liftIO $ putStrLn $ "Realizing "++show (queuedState $ head $ queue gr')++"("++show (incomingEdge $ head $ queue gr')++")"
        liftIO $ putStrLn $ memDebug (globalMemory gr)
        ngr <- incrementGraph gr
        res <- checkGraph ngr
        --liftIO $ writeFile ("graph"++show i++".dot") (renderNodeGraph ngr)
        case res of
          Nothing -> check ngr (i+1) depth
          Just (err,watch) -> do
            liftIO $ putStrLn $ "Error "++show err++" found."
            mapM_ (\str -> liftIO $ putStrLn str) watch
            return ngr