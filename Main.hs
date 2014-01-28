module Main where

import Options
import Program
import Unrollment
--import MemoryModel.Snow
import MemoryModel.Rivers
import Realization

import Control.Monad (when)
import System.Exit
import Language.SMTLib2
import Language.SMTLib2.Pipe
#ifdef WITH_BOOLECTOR
import Language.SMTLib2.Boolector
#endif
#ifdef WITH_STP
import Language.SMTLib2.STP
#endif
#ifdef WITH_YICES
import Language.SMTLib2.Yices
#endif
import Language.SMTLib2.Internals.Optimize
import qualified Data.Graph.Inductive as Gr
import Data.Foldable (all)
import Prelude hiding (mapM_,all)
import System.Random
import Control.Monad.Trans (liftIO)
import qualified Data.List as List
import Data.Proxy

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
      cfg2 = case recursionLimit opts of
        Nothing -> cfg1
        Just limit -> cfg1 { unrollDoRealize = \budget -> (unrollDoRealize cfg1 budget) &&
                                                          (all (<limit) (nodeIdRecursionCount $ fst budget))
                           }
  case action opts of
    Verify -> actVerify opts cfg2
    DumpCFG -> dumpBlockGraph cfg2
    DumpLLVM -> dumpProgram program
  where
    initSolver opts = case solver opts of
#ifdef WITH_YICES
      YicesSolver -> withYices
#endif
      _ -> id
    actVerify opts cfg = initSolver opts $ do
      backend <- case solver opts of
            SMTLib2Solver name -> fmap AnyBackend $ createSMTPipe name
#ifdef WITH_STP
            STPSolver -> fmap AnyBackend stpBackend
#endif
#ifdef WITH_BOOLECTOR
            BoolectorSolver -> fmap AnyBackend boolectorBackend
#endif
#ifdef WITH_YICES
            YicesSolver -> fmap AnyBackend yicesBackend
#endif

      bug <- withSMTBackend (optimizeBackend (backend::AnyBackend IO)) $ do
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
