{-# LANGUAGE ScopedTypeVariables,ExistentialQuantification #-}
module Program where

import MemoryModel
import TypeDesc
import InstrDesc

import Data.Map as Map hiding (foldl)
import Data.Set as Set hiding (foldl)
import Foreign.Ptr as FFI
import Prelude as P hiding (foldl,concat)
import Foreign.C.String
import Foreign.Marshal.Array
import Data.Maybe (catMaybes)
import Control.Concurrent.MVar
import Data.Proxy
import Data.Tree

import LLVM.FFI.BasicBlock
import LLVM.FFI.Constant
import LLVM.FFI.MemoryBuffer
import LLVM.FFI.SMDiagnostic
import LLVM.FFI.Module
import LLVM.FFI.Context
import LLVM.FFI.IPList
import LLVM.FFI.Function
import LLVM.FFI.Value
import LLVM.FFI.Type
import LLVM.FFI.APInt
import LLVM.FFI.OOP
import LLVM.FFI.User
import LLVM.FFI.Pass
import LLVM.FFI.Pass.Haskell
import LLVM.FFI.PassManager
import LLVM.FFI.SetVector
import LLVM.FFI.StringRef
import LLVM.FFI.Transforms.Scalar
import LLVM.FFI.Transforms.IPO
import LLVM.FFI.ArrayRef
import LLVM.FFI.Loop
import LLVM.FFI.CPP

type ProgDesc = (Set (Ptr Module),
                 Map String ([(Ptr Argument, TypeDesc)],
                             TypeDesc,
                             [(Ptr BasicBlock, Maybe String, [[InstrDesc Operand]])],
                             [LoopDesc],
                             Maybe DomTree),
                 Map (Ptr GlobalVariable) (TypeDesc, Maybe MemContent),
                 Integer,
                 Set TypeDesc,
                 Map String [TypeDesc])

getUsedTypes :: Ptr Module -> IO ([TypeDesc],Map String [TypeDesc])
getUsedTypes mod = do
  pass <- newFindUsedTypes
  succ <- modulePassRunOnModule pass mod
  tps_set <- findUsedTypesGetTypes pass
  tps <- setVectorToList tps_set
  all_tps <- mapM reifyType tps
  structs <- mapM (\tp -> case castDown tp of
                      Nothing -> return Nothing
                      Just stp -> do
                        hasN <- structTypeHasName stp
                        if hasN
                          then (do
                                   name <- structTypeGetName stp >>= stringRefData
                                   sz <- structTypeGetNumElements stp
                                   els <- mapM (\i -> structTypeGetElementType stp i >>= reifyType) [0..(sz-1)]
                                   return $ Just (name,els))
                          else return Nothing
                  ) tps
  deleteFindUsedTypes pass
  return (all_tps,Map.fromList $ catMaybes structs)

data LoopDesc = LoopDesc { loopDescPtr :: Ptr Loop
                         , loopDescUniquePath :: Bool
                         , loopDescHeader :: Ptr BasicBlock
                         , loopDescBlocks :: [Ptr BasicBlock]
                         , loopDescSubs :: [LoopDesc]
                         } deriving Show

reifyLoop :: Ptr Loop -> IO LoopDesc
reifyLoop loop = do
  backEdges <- loopGetNumBackEdges loop
  hdr <- loopGetHeader loop
  blks <- loopGetBlocks loop >>= vectorToList
  subs <- loopGetSubLoops loop >>= vectorToList >>= mapM reifyLoop
  return $ LoopDesc loop (backEdges==1) hdr blks subs

type DomTree = Tree (Ptr BasicBlock)

reifyDomTree :: Ptr (DomTreeNodeBase BasicBlock) -> IO DomTree
reifyDomTree tree = do
  blk <- domTreeNodeBaseGetBlock tree
  childs <- domTreeNodeBaseGetChildren tree >>= vectorToList >>= mapM reifyDomTree
  return $ Node blk childs

data APass = forall p. PassC p => APass (IO (Ptr p))

passes :: String -> MVar (Map String ([LoopDesc],Maybe DomTree)) -> [APass]
passes entry var
  = [APass createPromoteMemoryToRegisterPass
    ,APass createConstantPropagationPass
    ,APass createSimplifyLibCallsPass
    ,APass createIndVarSimplifyPass
    ,APass createLoopSimplifyPass
    ,APass createCFGSimplificationPass
    ,APass createLICMPass
    ,APass createLoopRotatePass
    ,APass createLoopUnrollPass
    ,APass (do
               m <- newCString entry
               arr <- newArray [m]
               export_list <- newArrayRef arr 1
               --export_list <- newArrayRefEmpty
               createInternalizePass export_list)
    ,APass (createFunctionInliningPass 100)
    ,APass (newHaskellModulePass
            (\self au -> do
                analysisUsageAddRequired au (Proxy::Proxy DominatorTree)
                analysisUsageAddRequired au (Proxy::Proxy LoopInfo))
            (\self mod -> do
                funs <- moduleGetFunctionList mod >>= ipListToList
                loop_mp <- mapM 
                           (\fun -> do
                               fname <- getNameString fun
                               isDecl <- globalValueIsDeclaration fun
                               (loops,dt) <- if isDecl
                                             then return ([],Nothing)
                                             else (do
                                                      resolver <- passGetResolver self
                                                      pass_li <- analysisResolverFindImplPassFun resolver self (Proxy::Proxy LoopInfo) fun
                                                      pass_dt <- analysisResolverFindImplPassFun resolver self (Proxy::Proxy DominatorTree) fun
                                                      analysis_li <- passGetAnalysis pass_li
                                                      analysis_dt <- passGetAnalysis pass_dt
                                                      base <- loopInfoGetBase analysis_li
                                                      begin <- loopInfoBaseBegin base
                                                      end <- loopInfoBaseEnd base
                                                      loop_list <- vectorIteratorToList begin end
                                                      loops <- mapM reifyLoop loop_list
                                                      dt <- dominatorTreeGetRootNode analysis_dt >>= reifyDomTree
                                                      return (loops,Just dt)
                                                  )
                               return (fname,(loops,dt))
                           ) funs
                putMVar var (Map.fromList loop_mp)
                return False))
    ]

applyOptimizations :: Ptr Module -> String -> IO (Map String ([LoopDesc],Maybe DomTree))
applyOptimizations mod entry = do
  var <- newEmptyMVar
  pm <- newPassManager
  mapM (\(APass c) -> do
           pass <- c
           passManagerAdd pm pass) (passes entry var)
  passManagerRun pm mod
  deletePassManager pm
  res <- takeMVar var
  return res

getTargetLibraryInfo :: Ptr Module -> IO (Ptr TargetLibraryInfo)
getTargetLibraryInfo mod = do
  tli <- newTargetLibraryInfo
  modulePassRunOnModule tli mod
  return tli

#if HS_LLVM_VERSION >= 302
getDataLayout :: Ptr Module -> IO (Ptr DataLayout)
getDataLayout mod = do
  dl <- newDataLayoutFromModule mod
  modulePassRunOnModule dl mod
  return dl
#else
getDataLayout :: Ptr Module -> IO (Ptr TargetData)
getDataLayout mod = do
  dl <- newTargetDataFromModule mod
  modulePassRunOnModule dl mod
  return dl
#endif

getProgram :: (String -> TypeDesc -> [TypeDesc] -> Bool) -> String -> String -> IO ProgDesc
getProgram is_intr entry file = do
  Just buf <- getFileMemoryBufferSimple file
  diag <- newSMDiagnostic
  ctx <- newLLVMContext
  mod <- parseIR buf diag ctx
  loop_mp <- applyOptimizations mod entry
  tli <- getTargetLibraryInfo mod
  dl <- getDataLayout mod
#if HS_LLVM_VERSION >= 302
  ptrWidth <- dataLayoutPointerSize dl 0
#else
  ptrWidth <- targetDataPointerSize dl
#endif
  funs <- moduleGetFunctionList mod >>= 
          ipListToList >>=
          mapM (\fun -> do
                   fname <- getNameString fun
                   ftp <- functionGetFunctionType fun
                   rtp <- functionTypeGetReturnType ftp >>= reifyType
                   sz <- functionTypeGetNumParams ftp
                   argtps <- mapM (\i -> functionTypeGetParamType ftp i >>=
                                         reifyType
                                  ) [0..(sz-1)]
                   args <- functionGetArgumentList fun >>= ipListToList
                   blks <- getBasicBlockList fun >>= 
                           ipListToList >>=
                           mapM (\blk -> do
                                    blkHasName <- hasName blk
                                    blkName <- if blkHasName
                                               then fmap Just (getNameString blk)
                                               else return Nothing
                                    instrs <- getInstList blk >>=
                                              ipListToList >>=
                                              mapM (reifyInstr tli dl)
                                    return (blk,blkName,mkSubBlocks [] instrs))
                   let (lis,dt) = loop_mp!fname
                   return (fname,(zip args argtps,rtp,blks,lis,dt))) >>=
          return . Map.fromList
  globs <- moduleGetGlobalList mod >>= 
           ipListToList >>= 
           mapM (\g -> do
                    init <- globalVariableGetInitializer g
                    init' <- if init == nullPtr
                             then return Nothing
                             else fmap Just (getConstant init)
                    tp <- getType g >>= reifyType . castUp
                    return (g,(tp,init'))) >>=
           return . Map.fromList
  (tps,structs) <- getUsedTypes mod
  return (Set.singleton mod,funs,globs,fromIntegral ptrWidth,Set.fromList tps,structs)
  where
    mkSubBlocks :: [InstrDesc Operand] -> [InstrDesc Operand] -> [[InstrDesc Operand]]
    mkSubBlocks cur (i:is) = case i of
      ITerminator (ICall _ _ fn _) -> case operandDesc fn of
        ODFunction rtp fname argtps -> if is_intr fname rtp argtps
                                       then mkSubBlocks (cur++[i]) is
                                       else (cur++[i]):mkSubBlocks [] is
        _ -> (cur++[i]):mkSubBlocks [] is
      ITerminator _ -> [cur++[i]]
      _ -> mkSubBlocks (cur++[i]) is

getConstant :: Ptr Constant -> IO MemContent
getConstant val 
  = mkSwitch
    [fmap (\ci -> do
              val <- constantIntGetValue ci
              w <- apIntGetBitWidth val
              rval <- apIntGetSExtValue val
              return $ MemCell (toInteger w) (toInteger rval)
          ) (castDown val)
    ,fmap (\carr -> do
              sz <- getNumOperands (carr::Ptr ConstantArray)
              els <- mapM (\i -> do
                              op <- getOperand carr i
                              case castDown op of
                                Nothing -> error "Constant array operand isn't a constant"
                                Just op' -> getConstant op'
                          ) [0..(sz-1)]
              return $ MemArray els
          ) (castDown val)
    ,fmap (\(pnull::Ptr ConstantPointerNull) -> return $ MemNull) (castDown val)
    ,fmap (\(arr::Ptr ConstantArray) -> do
              tp <- getType arr
              sz <- arrayTypeGetNumElements tp
              els <- mapM (\i -> constantGetAggregateElement arr i >>= getConstant) [0..(sz-1)]
              return $ MemArray els
          ) (castDown val)
    ,fmap (\(seq::Ptr ConstantDataSequential) -> do
              sz <- constantDataSequentialGetNumElements seq
              els <- mapM (\i -> constantDataSequentialGetElementAsConstant seq i >>= getConstant) [0..(sz-1)]
              return $ MemArray els
          ) (castDown val)
    ,fmap (\(arr::Ptr ConstantAggregateZero) -> do
              tp <- getType arr
              case castDown tp of
                Just arrTp -> do
                  sz <- arrayTypeGetNumElements arrTp
                  els <- mapM (\i -> constantGetAggregateElement arr i >>= getConstant) [0..(sz-1)]
                  return $ MemArray els
          ) (castDown val)
    ]
    where
      mkSwitch ((Just act):_) = act
      mkSwitch (Nothing:rest) = mkSwitch rest
      mkSwitch [] = do
        valueDump val
        error "Unknown constant."

mergePrograms :: ProgDesc -> ProgDesc -> ProgDesc
mergePrograms (mod1,p1,g1,pw1,tp1,s1) (mod2,p2,g2,pw2,tp2,s2)
  = (Set.union mod1 mod2,
     Map.unionWithKey (\name (args1,tp1,blks1,loops1,dt1) (args2,tp2,blks2,loops2,dt2)
                       -> if fmap snd args1 /= fmap snd args2 || tp1 /= tp2
                          then error $ "Conflicting signatures for function "++show name++" detected"
                          else (if P.null blks1
                                then (args2,tp2,blks2,loops2,dt2)
                                else (if P.null blks2
                                      then (args1,tp1,blks1,loops1,dt1)
                                      else error $ "Conflicting definitions for function "++show name++" found"))) p1 p2,
     Map.union g1 g2,
     if pw1==pw2
     then pw1
     else error "Programs do not agree on pointer width",
     Set.union tp1 tp2,
     Map.union s1 s2)

dumpProgram :: ProgDesc -> IO ()
dumpProgram (mods,_,_,_,_,_) = mapM_ moduleDump (Set.toList mods)
