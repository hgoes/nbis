module Main where

import Options
import Program
import Realization (isIntrinsic)
import Unrollment
import Analyzation
import MemoryModel.Snow

import Control.Monad (when)
import System.Exit
import Language.SMTLib2
import Data.Graph.Inductive (Gr)
import Data.Maybe (catMaybes)
import Data.Foldable (mapM_)
import Prelude hiding (mapM_)

import Debug.Trace
import MemoryModel (debugMem)

main = do
  opts <- getOptions
  when (showHelp opts) $ do
    putStrLn nbisInfo
    exitSuccess
  print "Get program..."
  progs <- mapM (getProgram isIntrinsic) (files opts)
  print "done."
  let (funs,globs,alltps,structs) = foldl1 mergePrograms progs
      cfg = UnrollCfg { unrollDoMerge = \_ _ _ -> False
                      , unrollStructs = structs
                      , unrollTypes = alltps }
      pgr = fmap (\(args,_,blks,_,_) -> programAsGraph blks args:: ProgramGraph Gr) funs
  bug <- withSMTSolver (case solver opts of
                           Nothing -> "~/debug-smt.sh output-" ++ (entryPoint opts) ++ ".smt"
                           Just bin -> bin) $ do
    setOption (PrintSuccess False)
    setOption (ProduceModels True)
    (start,env :: UnrollEnv (SnowMemory Integer Integer) Integer Integer) <- startingContext cfg pgr (entryPoint opts) globs
    findBug True cfg pgr 0 env [start]
  case bug of
    Just tr -> do
      putStrLn "Bug found:"
      print tr
    Nothing -> putStrLn "No bug found."
  where
    findBug isFirst cfg prog depth env ctxs = do
      --trace ("Depth: "++show depth) (return ())
      --trace ("Contexts:\n"++(unlines $ fmap show ctxs)) (return ())
      result <- unroll isFirst cfg prog env ctxs
      case result of
        Left err -> return (Just err)
        Right ([],nenv) -> return Nothing
        Right (nctxs,nenv) -> findBug False cfg prog (depth+1) nenv nctxs
    
    unroll isFirst cfg prog env []
      = stack (do
                  let (p1,p2) = unrollProxies env in trace (debugMem (unrollMemory env) p1 p2) (return ())
                  mapM_ (\mn -> assert $ not' $ mergeActivationProxy mn) (unrollMergeNodes env)
                  assert $ app or' [ cond | (desc,cond) <- unrollGuards env ]
                  res <- checkSat
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
                             return $ Left $ catMaybes outp)
                    else return (Right ([],env)))
    unroll isFirst cfg prog env (ctx:ctxs) = do
      (nenv,nctx) <- performUnrollmentCtx isFirst cfg prog env ctx
      result <- unroll False cfg prog nenv ctxs
      case result of
        Left err -> return $ Left err
        Right (nctxs,nenv2) -> return $ Right ((spawnContexts prog nctx)++nctxs,nenv2)
