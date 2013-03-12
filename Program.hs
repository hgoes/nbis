module Program where

import MemoryModel
import Analyzation

import LLVM.Core
import qualified LLVM.FFI.Core as FFI
import Control.Monad.Trans
import Data.Map as Map hiding (foldl)
import Data.Set as Set hiding (foldl)
import qualified Foreign.Marshal.Alloc as Alloc
import Foreign.Storable
import Language.SMTLib2
import Prelude as P hiding (foldl,concat)
import Data.Foldable

type ProgDesc = (Map String ([(String, TypeDesc)],
                             TypeDesc,
                             [(String, [[Instruction]])]),
                 Map String (TypeDesc, MemContent, Bool))

getProgram :: String -> IO ProgDesc
getProgram file = do
  m <- readBitcodeFromFile file
  glob <- getGlobalVariables m >>= 
          mapM (\(name,val) -> do
                   tp <- FFI.typeOf val >>= typeDesc2
                   (c,isConst) <- getConstant val
                   return (name,(tp,c,isConst))
               ) >>= return.(Map.fromList)
  print glob
  funs <- getFunctions m
  res <- mapM (\(name,fun) -> do
                  pars <- liftIO $ getParams fun >>= mapM (\(name,ref) -> do
                                                              tp <- FFI.typeOf ref >>= typeDesc2
                                                              return (name,tp))
                  tp <- liftIO $ FFI.typeOf fun >>= FFI.getElementType >>= FFI.getReturnType >>= typeDesc2
                  blks <- liftIO $ getBasicBlocks fun >>= mapM (\(name,blk) -> do
                                                                   instrs <- getInstructions blk >>= mapM (\(name,instr) -> getInstruction instr)
                                                                   return (name,mkSubBlocks [] instrs))
                  return (name,(pars,tp,blks))) funs
  return (Map.fromList res,glob)
  where
    mkSubBlocks :: [Instruction] -> [Instruction] -> [[Instruction]]
    mkSubBlocks cur (i:is) = case i of
      ICall _ _ _ _ _ -> (cur++[i]):mkSubBlocks [] is
      IRetVoid -> [cur++[i]]
      IRet _ -> [cur++[i]]
      IBr _ -> [cur++[i]]
      IBrCond _ _ _ -> [cur++[i]]
      ISwitch _ _ _ -> [cur++[i]]
      _ -> mkSubBlocks (cur++[i]) is

getConstant :: FFI.ValueRef -> IO (MemContent,Bool)
getConstant val = do
  tp <- FFI.typeOf val >>= typeDesc2
  c <- FFI.isGlobalConstant val
  val <- getConstant' tp val
  return (val,c/=0)
  where
    {-getConstant' (TDStruct name) val = do
      res <- mapM (\(tp,i) -> do
                      nv <- Alloc.alloca (\ptr -> do
                                             poke ptr i
                                             FFI.constExtractValue val ptr 1
                                         )
                      getConstant' tp nv) (zip tps [0..])
      return $ MemArray res-}
    getConstant' (TDArray n tp) val = do
      res <- mapM (\i -> do
                      nv <- Alloc.alloca (\ptr -> do
                                             poke ptr (fromIntegral i)
                                             FFI.constExtractValue val ptr 1
                                         )
                      getConstant' tp nv
                  ) [0..(n-1)]
      return $ MemArray res
    getConstant' (TDVector n tp) val = do
      res <- mapM (\i -> do
                      nv <- Alloc.alloca (\ptr -> do
                                             poke ptr (fromIntegral i)
                                             FFI.constExtractValue val ptr 1
                                         )
                      getConstant' tp nv) [0..(n-1)]
      return $ MemArray res
    getConstant' (TDInt _ w) val = do
      v <- FFI.constIntGetZExtValue val
      return $ MemCell w (fromIntegral v)
    getConstant' (TDPtr tp) val = do
      n <- FFI.isNull val
      if n/=0
        then return MemNull
        else (do
                 v <- Alloc.alloca (\ptr -> do
                                       poke ptr (fromIntegral 0)
                                       FFI.constExtractValue val ptr 1
                                   )
                 getConstant' tp v)

mergePrograms :: ProgDesc -> ProgDesc -> ProgDesc
mergePrograms (p1,g1) (p2,g2) 
  = (Map.unionWithKey (\name (args1,tp1,blks1) (args2,tp2,blks2)
                       -> if fmap snd args1 /= fmap snd args2 || tp1 /= tp2
                          then error $ "Conflicting signatures for function "++show name++" detected"
                          else (if P.null blks1
                                then (args2,tp2,blks2)
                                else (if P.null blks2
                                      then (args1,tp1,blks1)
                                      else error $ "Conflicting definitions for function "++show name++" found"))) p1 p2,
     Map.union g1 g2)

getProgramTypes :: ProgDesc -> Set TypeDesc
getProgramTypes (funs,_) 
  = foldl (\tps' (args,rtp,blks)
           -> Set.union tps' $ 
              Set.union 
              (allTypesBlks blks) 
              (allTypesArgs args)
          ) Set.empty funs
  where
    allTypesArgs :: [(String,TypeDesc)] -> Set TypeDesc
    allTypesArgs = allTypes' Set.empty
    
    allTypes' tps [] = tps
    allTypes' tps ((name,tp):vals) = case tp of
      TDPtr tp' -> allTypes' (Set.insert tp' tps) vals
      _ -> allTypes' tps vals

    allTypesBlks :: [(String,[[Instruction]])] 
                    -> Set TypeDesc
    allTypesBlks = allTypes'' [] Set.empty
    
    allTypes'' [] tps [] = tps
    allTypes'' [] tps ((_,subblks):blks)
      = allTypes'' (concat subblks) tps blks
    allTypes'' (i:is) tps blks 
      = case i of
        ILoad lbl e _ -> case exprType e of
          TDPtr tp -> allTypes'' is 
                      (Set.insert tp tps) blks
        IStore w to _ -> allTypes'' is 
                         (Set.insert (exprType w) tps) blks
        IAlloca lbl tp _ _ -> allTypes'' is 
                              (Set.insert tp tps) blks
        _ -> allTypes'' is tps blks