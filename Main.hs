module Main where

import Options
import Program
import Realization (isIntrinsic)
import Unrollment
import Analyzation
import MemoryModel
import MemoryModel.Snow
import MemoryModel.Rivers
import Circuit
import Realization

import Control.Monad (when)
import System.Exit
import Language.SMTLib2
import Data.Graph.Inductive (Gr)
import qualified Data.Graph.Inductive as Gr
import Data.Maybe (catMaybes)
import Data.Foldable (mapM_)
import Prelude hiding (mapM_)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State.Strict (runStateT)
import System.Random
import Control.Monad.Trans (liftIO)

import Debug.Trace
import MemoryModel (debugMem)

data BlkInfo = BlkInfo String

instance Show BlkInfo where
  show (BlkInfo x) = x

instance UnrollInfo (Gr.Gr BlkInfo ()) where
  type UnrollNodeInfo (Gr.Gr BlkInfo ()) = Gr.Node
  unrollInfoInit = Gr.empty
  unrollInfoNewNode gr ndInfo name isMerge
    = let [nd] = Gr.newNodes 1 gr
          ngr = Gr.insNode (nd,case name of
                               Nothing -> BlkInfo ""
                               Just n -> let prefix = if nodeIdFunction ndInfo=="main"
                                                      then ""
                                                      else (nodeIdFunction ndInfo)++"."
                                             postfix = if nodeIdSubblock ndInfo==0
                                                       then ""
                                                       else "."++show (nodeIdSubblock ndInfo)
                                             postfix2 = if isMerge
                                                        then "(m)"
                                                        else ""
                                         in BlkInfo (prefix++n++postfix++postfix2)) gr
      in (nd,ngr)
  unrollInfoConnect gr nd1 nd2 = Gr.insEdge (nd1,nd2,()) gr

main = do
  opts <- getOptions
  when (showHelp opts) $ do
    putStrLn nbisInfo
    exitSuccess
  print "Get program..."
  progs <- mapM (getProgram isIntrinsic) (files opts)
  print "done."
  gen <- getStdGen
  let program = foldl1 mergePrograms progs
      cfg = case manualMergeNodes opts of
        Nothing -> defaultConfig (entryPoint opts) program
        Just nodes -> explicitMergePointConfig (entryPoint opts) program nodes
      --cfg = randomMergePointConfig (entryPoint opts) program gen
      --cfg = noMergePointConfig (entryPoint opts) program
  bug <- withSMTSolver (case solver opts of
                           Nothing -> "~/debug-smt.sh output-" ++ (entryPoint opts) ++ ".smt"
                           Just bin -> bin) $ do
    setOption (PrintSuccess False)
    setOption (ProduceModels True)
    case memoryModelOption opts of
      Rivers -> do
        (start,env :: UnrollEnv (Gr.Gr BlkInfo ()) (RiverMemory Integer Integer) Integer Integer) <- startingContext cfg (entryPoint opts)
        findBug True cfg 0 env [start]
      Snow -> do
        (start,env :: UnrollEnv (Gr.Gr BlkInfo ()) (SnowMemory Integer Integer) Integer Integer) <- startingContext cfg (entryPoint opts)
        findBug True cfg 0 env [start]
  case bug of
    Just (tr,bugs) -> do
      putStrLn $ "Bug found: "++show bugs
      print tr
    Nothing -> putStrLn "No bug found."
  where
    findBug isFirst cfg depth env ctxs = do
      trace ("Depth: "++show depth) (return ())
      --liftIO $ writeFile ("state-space"++show depth++".dot") $ Gr.graphviz' (unrollInfo env)
      {-trace ("Contexts:\n"++(unlines $ fmap (\ctx -> show $ fmap (\edge -> ([ getBlkName cfg (unrollCtxFunction ctx) blk sblk | (blk,sblk,_,_,_) <- edgeConds edge ],
                                                                            getBlkName cfg (unrollCtxFunction ctx) (edgeTargetBlock edge) (edgeTargetSubblock edge)
                                                                           )) $ realizationQueue ctx) ctxs)) (return ())-}
      result <- unroll isFirst cfg env ctxs
      case result of
        Left err -> return (Just err)
        Right ([],nenv) -> return Nothing
        Right (nctxs,nenv) -> findBug False cfg (depth+1) nenv nctxs

    getBlkName cfg fname blk sblk = case Map.lookup fname (unrollFunctions cfg) of
      Just info -> case Map.lookup (blk,sblk) (unrollFunInfoBlocks info) of
        Just (name,_,_,_) -> case name of
          Just name' -> name'
        Nothing -> "Unknown block"
    
    unroll isFirst cfg env []
      = stack (do
                  let (p1,p2) = unrollProxies env
                      bugs = unrollGuards env ++ (memoryErrors (unrollMemory env) p1 p2)
                  --trace (debugMem (unrollMemory env) p1 p2) (return ())
                  --trace ("Checking errors:\n"++unlines (fmap (\(desc,cond) -> "  "++show desc++" ~> "++show cond) bugs)) (return ())
                  mapM_ (\mn -> assert $ not' $ mergeActivationProxy mn) (unrollMergeNodes env)
                  assert $ app or' [ cond | (desc,cond) <- bugs ]
                  res <- checkSat
                  if res
                    then (do
                             liftIO $ writeFile ("state-space.dot") $ Gr.graphviz' (unrollInfo env)
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
                             return $ Left (catMaybes outp,catMaybes rerrs))
                    else return (Right ([],env)))
    unroll isFirst cfg env (ctx:ctxs) = do
      --let (p1,p2) = unrollProxies env in trace (debugMem (unrollMemory env) p1 p2) (return ())
      (nctx,nenv) <- runStateT (performUnrollmentCtx isFirst cfg ctx) env
      result <- unroll False cfg nenv ctxs
      case result of
        Left err -> return $ Left err
        Right (nctxs,nenv2) -> return $ Right ((spawnContexts cfg nctx)++nctxs,nenv2)
