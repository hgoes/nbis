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
import Language.SMTLib2.Pipe
import Language.SMTLib2.Boolector
import Language.SMTLib2.STP
import Language.SMTLib2.Internals.Optimize
import Data.Graph.Inductive (Gr)
import qualified Data.Graph.Inductive as Gr
import Data.Maybe (catMaybes)
import Data.Foldable (mapM_,all)
import Prelude hiding (mapM_,all)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State.Strict (runStateT)
import System.Random
import Control.Monad.Trans (liftIO)
import qualified Data.List as List
import Data.Proxy

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
          rname = case name of
            Right lbl -> "lbl"++show lbl
            Left n -> n
          ngr = Gr.insNode (nd,let prefix = if nodeIdFunction ndInfo=="main"
                                            then ""
                                            else (nodeIdFunction ndInfo)++"."
                                   postfix = if nodeIdSubblock ndInfo==0
                                             then ""
                                             else "."++show (nodeIdSubblock ndInfo)
                                   postfix2 = if isMerge
                                              then "(m)"
                                              else ""
                               in BlkInfo (prefix++rname++postfix++postfix2)) gr
      in (nd,ngr)
  unrollInfoConnect gr nd1 nd2 = Gr.insEdge (nd1,nd2,()) gr

instance UnrollInfo () where
  type UnrollNodeInfo () = ()
  unrollInfoInit = ()
  unrollInfoNewNode _ _ _ _ = ((),())
  unrollInfoConnect _ _ _ = ()

main = do
  opts <- getOptions
  when (showHelp opts) $ do
    putStrLn nbisInfo
    exitSuccess
  progs <- mapM (getProgram isIntrinsic (entryPoint opts)) (files opts)
  gen <- getStdGen
  let program = foldl1 mergePrograms progs
      selectErr = \err -> List.elem err (checkErrors opts)
      cfg = case manualMergeNodes opts of
        Nothing -> defaultConfig (entryPoint opts) program selectErr
        Just nodes -> explicitMergePointConfig (entryPoint opts) program nodes selectErr
      --cfg = randomMergePointConfig (entryPoint opts) program gen
      --cfg = noMergePointConfig (entryPoint opts) program
      cfg1 = case unwindLimit opts of
        Nothing -> cfg
        Just limit -> cfg { unrollDoRealize = \budget -> (unrollDoRealize cfg budget) &&
                                                         (all (<limit) (unrollUnrollDepth $ snd budget))
                          }
  case action opts of
    Verify -> actVerify opts cfg1
    DumpCFG -> dumpBlockGraph cfg1
    DumpLLVM -> dumpProgram program
  where
    actVerify opts cfg = do
      backend <- createSMTPipe
                 (case solver opts of
                     Nothing -> "~/debug-smt.sh output-" ++ (entryPoint opts) ++ ".smt2"
                     Just bin -> bin)
      --backend <- boolectorBackend
      --backend <- stpBackend
      bug <- withSMTBackend (optimizeBackend backend) $ do
        setLogic "QF_ABV"
        setOption (PrintSuccess False)
        setOption (ProduceModels True)
        case memoryModelOption opts of
          Rivers -> do
            case dumpStateSpace opts of
              Just dumpFile -> do
                (result,info) <- contextQueueRun (incremental opts)
                                 (Proxy::Proxy (RiverMemory Integer Integer))
                                 (Proxy::Proxy (Gr.Gr BlkInfo ())) cfg (entryPoint opts)
                liftIO $ writeFile dumpFile (Gr.graphviz' info)
                return result
              Nothing -> do
                (result,_) <- contextQueueRun (incremental opts)
                              (Proxy::Proxy (RiverMemory Integer Integer))
                              (Proxy::Proxy ()) cfg (entryPoint opts)
                return result
          {-Snow -> do
             (start,env :: UnrollEnv (Gr.Gr BlkInfo ()) (SnowMemory Integer Integer) Integer Integer) <- startingContext cfg1 (entryPoint opts)
             findBug True cfg 0 env [start]-}
      case bug of
        Just (tr,bugs) -> do
          putStrLn $ "Bug found: "++show bugs
          print tr
        Nothing -> putStrLn "No bug found."
