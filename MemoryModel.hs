{-# LANGUAGE TypeFamilies,FlexibleContexts,MultiParamTypeClasses #-}
module MemoryModel where

import ConditionList

import Language.SMTLib2
import Data.Typeable
import Data.Unit
import Data.List (genericSplitAt,genericReplicate)
import Data.Set as Set
import Data.Map as Map
import TypeDesc

data MemContent = MemCell Integer Integer
                | MemArray [MemContent]
                | MemNull
                deriving (Show,Eq,Ord)

data ErrorDesc = Custom
               | NullDeref
               | Overrun
               | FreeAccess
               deriving (Show,Eq,Ord)

type DynNum = Either Integer (SMTExpr (BitVector BVUntyped))

data MemoryInstruction p
  = MINull TypeDesc p
  | MIAlloc TypeDesc DynNum p
  | MILoad p (SMTExpr (BitVector BVUntyped))
  | MILoadPtr p p
  | MIStore (SMTExpr (BitVector BVUntyped)) p
  | MIStorePtr p p
  | MICompare p p (SMTExpr Bool)
  | MISelect [(SMTExpr Bool,p)] p
  | MICast TypeDesc TypeDesc p p
  | MIIndex [DynNum] p p
  | MICopy DynNum p p
  | MIGlobal TypeDesc MemContent p
  deriving (Show,Eq)

type MemoryProgram p = [MemoryInstruction p]

class MemoryModel m ptr where
  memNew :: ptr -> Set TypeDesc -> Map String [TypeDesc] -> SMT m
  addGlobal :: m -> ptr -> TypeDesc -> MemContent -> SMT m
  addProgram :: m -> Int -> MemoryProgram ptr -> SMT m
  connectPrograms :: m -> SMTExpr Bool -> Int -> Int -> [(ptr,ptr)] -> SMT m

flattenMemContent :: MemContent -> [(Integer,Integer)]
flattenMemContent (MemCell w v) = [(w,v)]
flattenMemContent (MemArray xs) = concat $ fmap flattenMemContent xs

typeWidth :: TypeDesc -> Integer
typeWidth (IntegerType w)
  | w `mod` 8 == 0 = w `div` 8
  | otherwise = error $ "typeWidth called for "++show w
typeWidth (ArrayType n tp) = n*(typeWidth tp)
typeWidth (StructType (Right tps)) = sum (fmap typeWidth tps)
typeWidth tp = error $ "No typeWidth for "++show tp

bitWidth :: TypeDesc -> Integer
bitWidth (IntegerType w) = w
bitWidth (ArrayType n tp) = n*(bitWidth tp)
bitWidth (StructType (Right tps)) = sum (fmap bitWidth tps)
bitWidth tp = error $ "No bitWidth for "++show tp

getOffset :: (TypeDesc -> Integer) -> TypeDesc -> [Integer] -> Integer
getOffset width tp idx = getOffset' tp idx 0
    where
      getOffset' _ [] off = off
      getOffset' (PointerType tp) (i:is) off = getOffset' tp is (off + i*(width tp))
      getOffset' (StructType (Right tps)) (i:is) off = let (pre,tp:_) = genericSplitAt i tps
                                                         in getOffset' tp is (off + sum (fmap width pre))
      getOffset' (ArrayType _ tp) (i:is) off = getOffset' tp is (off + i*(width tp))

--getDynamicOffset :: (TypeDesc -> Integer) -> TypeDesc -> [Either Integer 

flattenType :: TypeDesc -> [TypeDesc]
flattenType (StructType (Right tps)) = concat $ fmap flattenType tps
flattenType (ArrayType n tp) = concat $ genericReplicate n (flattenType tp)
flattenType (VectorType n tp) = concat $ genericReplicate n (flattenType tp)
flattenType tp = [tp]
