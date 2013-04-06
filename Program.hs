{-# LANGUAGE ScopedTypeVariables #-}
module Program where

import MemoryModel
import Analyzation
import TypeDesc
import InstrDesc

import Control.Monad.Trans
import Data.Map as Map hiding (foldl)
import Data.Set as Set hiding (foldl)
import qualified Foreign.Marshal.Alloc as Alloc
import Foreign.Ptr as FFI
import Foreign.Storable
import Language.SMTLib2
import Prelude as P hiding (foldl,concat)
import Data.Foldable
import Foreign.Ptr
import Data.Maybe (catMaybes)

import LLVM.FFI.Instruction
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
import LLVM.FFI.SetVector
import LLVM.FFI.StringRef

type ProgDesc = (Map String ([(Ptr Argument, TypeDesc)],
                             TypeDesc,
                             [(Ptr BasicBlock, [[InstrDesc Operand]])]),
                 Map (Ptr GlobalVariable) (TypeDesc, Maybe MemContent),
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

getProgram :: String -> IO ProgDesc
getProgram file = do
  Just buf <- getFileMemoryBufferSimple file
  diag <- newSMDiagnostic
  ctx <- newLLVMContext
  mod <- parseIR buf diag ctx
  funs <- getFunctionList mod >>= 
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
                                    instrs <- getInstList blk >>=
                                              ipListToList >>=
                                              mapM reifyInstr
                                    return (blk,mkSubBlocks [] instrs))
                   return (fname,(zip args argtps,rtp,blks))) >>=
          return . Map.fromList
  globs <- getGlobalList mod >>= 
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
  return (funs,globs,Set.fromList tps,structs)
  where
    mkSubBlocks :: [InstrDesc Operand] -> [InstrDesc Operand] -> [[InstrDesc Operand]]
    mkSubBlocks cur (i:is) = case i of
      ITerminator (ICall _ _ _) -> (cur++[i]):mkSubBlocks [] is
      ITerminator _ -> [cur++[i]]
      _ -> mkSubBlocks (cur++[i]) is

getConstant :: Ptr Constant -> IO MemContent
getConstant val 
  = mkSwitch
    [fmap (\ci -> do
              val <- constantIntGetValue ci
              w <- apIntGetBitWidth val
              rval <- apIntGetSExtValue val
              return $ MemCell w (toInteger rval)
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
    ]
    where
      mkSwitch ((Just act):_) = act
      mkSwitch (Nothing:rest) = mkSwitch rest
      mkSwitch [] = do
        valueDump val
        error "Unknown constant."

mergePrograms :: ProgDesc -> ProgDesc -> ProgDesc
mergePrograms (p1,g1,tp1,s1) (p2,g2,tp2,s2) 
  = (Map.unionWithKey (\name (args1,tp1,blks1) (args2,tp2,blks2)
                       -> if fmap snd args1 /= fmap snd args2 || tp1 /= tp2
                          then error $ "Conflicting signatures for function "++show name++" detected"
                          else (if P.null blks1
                                then (args2,tp2,blks2)
                                else (if P.null blks2
                                      then (args1,tp1,blks1)
                                      else error $ "Conflicting definitions for function "++show name++" found"))) p1 p2,
     Map.union g1 g2,
     Set.union tp1 tp2,
     Map.union s1 s2)
