module Options where

import MemoryModel
import System.Environment (getArgs)
import System.Console.GetOpt
import qualified Data.List as List

data MemoryModelOption = Rivers
                       | Snow
                       deriving (Eq,Ord,Show)

data NbisAction = Verify
                | DumpCFG
                | DumpLLVM
                deriving (Eq,Ord,Show)

data Solver = SMTLib2Solver String
#ifdef WITH_STP
            | STPSolver
#endif
#ifdef WITH_BOOLECTOR
            | BoolectorSolver
#endif
#ifdef WITH_YICES
            | YicesSolver
#endif
            deriving (Eq,Ord,Show)

data Options = Options
               { action :: NbisAction
               , entryPoint :: String
               , bmcDepth :: Integer
               , files :: [String]
               , memoryModelOption :: MemoryModelOption
               , solver :: Solver
               , checkErrors :: [ErrorDesc]
               , showHelp :: Bool
               , manualMergeNodes :: Maybe [(String,String,Integer)]
               , unwindLimit :: Maybe Integer
               , recursionLimit :: Maybe Integer
               , incremental :: Bool
               , completeness :: Bool
               , dumpStateSpace :: Maybe String
               } deriving (Eq,Ord,Show)

nbisInfo :: String
nbisInfo = usageInfo "USAGE:\n  nbis [OPTION...] FILE [FILE...]\n\nOptions:" optionDescr

defaultOptions :: Options
defaultOptions = Options { action = Verify
                         , entryPoint = "main"
                         , bmcDepth = 10
                         , files = []
                         , memoryModelOption = Rivers
                         , solver = SMTLib2Solver "z3 -in -smt2"
                         , checkErrors = [Custom]
                         , showHelp = False
                         , manualMergeNodes = Nothing
                         , unwindLimit = Nothing
                         , recursionLimit = Nothing
                         , incremental = True
                         , completeness = False
                         , dumpStateSpace = Nothing }

optionDescr :: [OptDescr (Options -> Options)]
optionDescr = [Option ['e'] ["entry-point"] (ReqArg (\str opt -> opt { entryPoint = str }) "function") "Specify the main function to test"
              ,Option ['d'] ["depth"] (ReqArg (\str opt -> opt { bmcDepth = read str }) "d") "Maximal unroll depth"
              ,Option ['m'] ["memory-model"] (ReqArg (\str opt -> opt { memoryModelOption = case str of
                                                                           "rivers" -> Rivers
                                                                           "snow" -> Snow
                                                                           _ -> error $ "Unknown memory model "++show str
                                                                      }) "model") "Memory model to use (rivers or snow)"
              ,Option [] ["solver"] (ReqArg (\str opt -> opt { solver = SMTLib2Solver str }) "smt-binary") "The SMT solver to use to solve the generated instance"
#ifdef WITH_STP
              ,Option [] ["stp"] (NoArg (\opt -> opt { solver = STPSolver })) "Use the STP solver."
#endif
#ifdef WITH_BOOLECTOR
              ,Option [] ["boolector"] (NoArg (\opt -> opt { solver = BoolectorSolver })) "Use the boolector solver."
#endif
#ifdef WITH_YICES
              ,Option [] ["yices"] (NoArg (\opt -> opt { solver = YicesSolver })) "Use the yices solver."
#endif
              ,Option [] ["check-errors"] (ReqArg (\str opt -> opt { checkErrors = fmap (\n -> case n of
                                                                                            "user" -> Custom
                                                                                            "null" -> NullDeref
                                                                                            "invalid" -> Overrun
                                                                                            "free-access" -> FreeAccess
                                                                                            "double-free" -> DoubleFree
                                                                                        ) (splitOptions str) }) "opts") "A comma seperated list of bug types which should be checked:\n  user - User defined assertions\n  null - Null pointer dereferentiations\n  invalid - Invalid memory accesses\n  free-access - Access to freed memory locations\n  double-free - Double frees of memory locations"
              ,Option [] ["merge-nodes"]
               (ReqArg (\str opt -> opt { manualMergeNodes = Just (read str) }) "list")
               "A list of merge nodes to use."
              ,Option [] ["non-incremental"]
               (NoArg (\opt -> opt { incremental = False })) "Use non-incremental solving."
              ,Option [] ["check-completeness"]
               (NoArg (\opt -> opt { completeness = True })) "Check if the completeness threshhold of the model has been reached."
              ,Option [] ["unwind-limit"]
               (ReqArg (\str opt -> opt { unwindLimit = Just (read str) }) "n")
               "Limit the number of times a loop can be unwound."
              ,Option [] ["recursion-limit"]
               (ReqArg (\str opt -> opt { recursionLimit = Just (read str) }) "n")
               "Limit the number of times a function can be called recursively."
              ,Option [] ["dump-cfg"]
               (NoArg (\opt -> opt { action = DumpCFG })) "Dump the control flow graph as a graphviz file."
              ,Option [] ["dump-llvm"]
               (NoArg (\opt -> opt { action = DumpLLVM })) "Dump the LLVM IR."
              ,Option [] ["dump-state-space"]
               (OptArg (\str opt -> opt { dumpStateSpace = case str of
                                             Nothing -> Just "state-space.dot"
                                             Just fname -> Just fname }) "file") "Dump the state space after verfication."
              ,Option ['h'] ["help"] (NoArg (\opt -> opt { showHelp = True })) "Show this help."
              ]

splitOptions :: String -> [String]
splitOptions "" = []
splitOptions xs = case List.break (==',') xs of
  (x,[]) -> [x]
  (x,',':rest) -> x:splitOptions rest

getOptions :: IO Options
getOptions = do
  args <- getArgs
  let (res,args',errs) = getOpt Permute optionDescr args
  case errs of
    [] -> let opts = foldl (.) id res (defaultOptions { files = args' })
          in return $ if incremental opts
                      then opts
                      else opts { manualMergeNodes = Just [] }
    _ -> error $ show errs
