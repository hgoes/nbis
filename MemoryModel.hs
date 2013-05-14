{-# LANGUAGE TypeFamilies,FlexibleContexts,MultiParamTypeClasses #-}
module MemoryModel where

import Language.SMTLib2
import Data.Typeable
import Data.Unit
import Data.List (genericSplitAt,genericReplicate)
import Data.Set as Set
import Data.Map as Map
import TypeDesc
import Foreign.Ptr
import LLVM.FFI.BasicBlock
import Data.Proxy

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

data MemoryInstruction m p
  = MINull m TypeDesc p m
  | MIAlloc m TypeDesc DynNum p m
  | MILoad m p (SMTExpr (BitVector BVUntyped))
  | MILoadPtr m p p m
  | MIStore m (SMTExpr (BitVector BVUntyped)) p m
  | MIStorePtr m p p m
  | MICompare m p p (SMTExpr Bool)
  | MISelect m [(SMTExpr Bool,p)] p m
  | MICast m TypeDesc TypeDesc p p m
  | MIIndex m [DynNum] p p m
  | MICopy m DynNum p p m
  deriving (Show,Eq)

type MemoryProgram m p = [MemoryInstruction m p]

class MemoryModel m mloc ptr where
  memNew :: Proxy mloc -> Set TypeDesc -> Map String [TypeDesc] -> [(ptr,TypeDesc,Maybe MemContent)] -> SMT m
  addProgram :: m -> SMTExpr Bool -> mloc -> MemoryProgram mloc ptr -> SMT m
  connectLocation :: m -> SMTExpr Bool -> mloc -> mloc -> [(ptr,ptr)] -> SMT m
  debugMem :: m -> Proxy mloc -> Proxy ptr -> String

flattenMemContent :: MemContent -> [(Integer,Integer)]
flattenMemContent (MemCell w v) = [(w,v)]
flattenMemContent (MemArray xs) = concat $ fmap flattenMemContent xs

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

dynNumCombine :: (Integer -> Integer -> a)
              -> (SMTExpr (BitVector BVUntyped) -> SMTExpr (BitVector BVUntyped) -> a)
              -> DynNum -> DynNum -> a
dynNumCombine f _ (Left i1) (Left i2) = f i1 i2
dynNumCombine _ g (Right i1) (Right i2)
  = case compare (extractAnnotation i1) (extractAnnotation i2) of
      EQ -> g i1 i2
      LT -> g (bvconcat (constantAnn (BitVector 0) ((extractAnnotation i2) - (extractAnnotation i1)) :: SMTExpr (BitVector BVUntyped)) i1) i2
      GT -> g i1 (bvconcat (constantAnn (BitVector 0) ((extractAnnotation i1) - (extractAnnotation i2)) :: SMTExpr (BitVector BVUntyped)) i2)
dynNumCombine _ g (Left i1) (Right i2) = g (constantAnn (BitVector i1) (extractAnnotation i2)) i2
dynNumCombine _ g (Right i1) (Left i2) = g i1 (constantAnn (BitVector i2) (extractAnnotation i1))
