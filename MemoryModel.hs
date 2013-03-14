{-# LANGUAGE TypeFamilies,FlexibleContexts,MultiParamTypeClasses #-}
module MemoryModel where

import ConditionList

import Language.SMTLib2
import LLVM.Core (TypeDesc(..))
import Data.Typeable
import Data.Unit
import Data.List (genericSplitAt,genericReplicate)
import Data.Set as Set

data MemContent = MemCell Integer Integer
                | MemArray [MemContent]
                | MemNull
                deriving (Show,Eq,Ord)

data ErrorDesc = Custom
               | NullDeref
               | Overrun
               | FreeAccess
               deriving (Show,Eq,Ord)

data MemoryInstruction p
  = MINull TypeDesc p
  | MIAlloc TypeDesc (Either Integer (SMTExpr (BitVector BVUntyped))) p
  | MILoad p (SMTExpr (BitVector BVUntyped))
  | MILoadPtr p p
  | MIStore (SMTExpr (BitVector BVUntyped)) p
  | MIStorePtr p p
  | MICompare p p (SMTExpr Bool)
  | MISelect [(SMTExpr Bool,p)] p
  | MICast TypeDesc TypeDesc p p
  | MIIndex [Either Integer (SMTExpr (BitVector BVUntyped))] p p
  | MICopy (Either Integer (SMTExpr (BitVector BVUntyped))) p p
  | MIGlobal TypeDesc MemContent p
  deriving (Show,Eq)

type MemoryProgram p = [MemoryInstruction p]

class MemoryModel m ptr where
  memNew :: ptr -> Set TypeDesc -> SMT m
  addGlobal :: m -> ptr -> MemContent -> SMT m
  addProgram :: m -> Int -> MemoryProgram ptr -> SMT m
  connectPrograms :: m -> SMTExpr Bool -> Int -> Int -> [(ptr,ptr)] -> SMT m

flattenMemContent :: MemContent -> [(Integer,Integer)]
flattenMemContent (MemCell w v) = [(w,v)]
flattenMemContent (MemArray xs) = concat $ fmap flattenMemContent xs

typeWidth :: TypeDesc -> Integer
typeWidth (TDInt _ w)
  | w `mod` 8 == 0 = w `div` 8
  | otherwise = error $ "typeWidth called for "++show w
typeWidth (TDArray n tp) = n*(typeWidth tp)
typeWidth (TDStruct (Right (tps,_))) = sum (fmap typeWidth tps)
typeWidth tp = error $ "No typeWidth for "++show tp

bitWidth :: TypeDesc -> Integer
bitWidth (TDInt _ w) = w
bitWidth (TDArray n tp) = n*(bitWidth tp)
bitWidth (TDStruct (Right (tps,_))) = sum (fmap bitWidth tps)
bitWidth tp = error $ "No bitWidth for "++show tp

getOffset :: (TypeDesc -> Integer) -> TypeDesc -> [Integer] -> Integer
getOffset width tp idx = getOffset' tp idx 0
    where
      getOffset' _ [] off = off
      getOffset' (TDPtr tp) (i:is) off = getOffset' tp is (off + i*(width tp))
      getOffset' (TDStruct (Right (tps,_))) (i:is) off = let (pre,tp:_) = genericSplitAt i tps
                                                         in getOffset' tp is (off + sum (fmap width pre))
      getOffset' (TDArray _ tp) (i:is) off = getOffset' tp is (off + i*(width tp))

--getDynamicOffset :: (TypeDesc -> Integer) -> TypeDesc -> [Either Integer 

flattenType :: TypeDesc -> [TypeDesc]
flattenType (TDStruct (Right (tps,_))) = concat $ fmap flattenType tps
flattenType (TDArray n tp) = concat $ genericReplicate n (flattenType tp)
flattenType (TDVector n tp) = concat $ genericReplicate n (flattenType tp)
flattenType tp = [tp]
