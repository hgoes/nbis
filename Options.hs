module Options where

import System.Environment (getArgs)
import System.Console.GetOpt

data MemoryModelOption = UntypedModel
                       | TypedModel
                       | BlockModel
                       | PlainModel
                       deriving (Eq,Ord,Show)

data Options = Options
               { entryPoint :: String
               , bmcDepth :: Integer
               , files :: [String]
               , memoryModelOption :: MemoryModelOption
               , solver :: Maybe String
               , checkUser :: Bool
               , checkMemoryAccess :: Bool
               , showHelp :: Bool
               } deriving (Eq,Ord,Show)

nbisInfo :: String
nbisInfo = usageInfo "USAGE:\n  nbis [OPTION...] FILE [FILE...]\n\nOptions:" optionDescr

defaultOptions :: Options
defaultOptions = Options { entryPoint = "main" 
                         , bmcDepth = 10
                         , files = []
                         , memoryModelOption = PlainModel
                         , solver = Nothing
                         , checkUser = False
                         , checkMemoryAccess = False
                         , showHelp = False }

optionDescr :: [OptDescr (Options -> Options)]
optionDescr = [Option ['e'] ["entry-point"] (ReqArg (\str opt -> opt { entryPoint = str }) "function") "Specify the main function to test"
              ,Option ['d'] ["depth"] (ReqArg (\str opt -> opt { bmcDepth = read str }) "d") "Maximal unroll depth"
              ,Option ['m'] ["memory-model"] (ReqArg (\str opt -> opt { memoryModelOption = case str of
                                                                           "typed" -> TypedModel
                                                                           "untyped" -> UntypedModel
                                                                           "block" -> BlockModel
                                                                           "plain" -> PlainModel
                                                                           _ -> error $ "Unknown memory model "++show str
                                                                      }) "model") "Memory model to use (untyped,typed or block)"
              ,Option [] ["solver"] (ReqArg (\str opt -> opt { solver = Just str }) "smt-binary") "The SMT solver to use to solve the generated instance"
              ,Option [] ["check-user"] (NoArg (\opt -> opt { checkUser = True })) "Validate user assertions"
              ,Option [] ["check-mem"] (NoArg (\opt -> opt { checkMemoryAccess = True })) "Validate memory accesses"
              ,Option ['h'] ["help"] (NoArg (\opt -> opt { showHelp = True })) "Show this help"
              ]

getOptions :: IO Options
getOptions = do
  args <- getArgs
  let (res,args',errs) = getOpt Permute optionDescr args
  case errs of
    [] -> return $ foldl (.) id res (defaultOptions { files = args' })
    _ -> error $ show errs