{-# LANGUAGE TypeFamilies,FlexibleContexts #-}
module MemoryModel where

import Language.SMTLib2
import LLVM.Core (TypeDesc(..))
import Data.Typeable
import Data.Unit
import Data.List (genericSplitAt,genericReplicate)


data MemContent = MemCell (SMTExpr BitVector)
                | MemArray [MemContent]
                | MemNull
                deriving Show

data ErrorDesc = Custom
               | NullDeref
               | Overrun
               | FreeAccess
               deriving (Show,Eq,Ord)

class (Typeable m) => MemoryModel m where
    type Pointer m
    memNew :: [TypeDesc] -> SMT m
    memInit :: m -> SMTExpr Bool
    memPtrNew :: m -> TypeDesc -> SMT (Pointer m)
    memAlloc :: TypeDesc -> Either Integer (SMTExpr BitVector) -> Maybe MemContent -> m -> SMT (Pointer m,m)
    memLoad :: TypeDesc -> Pointer m -> m -> (SMTExpr BitVector,[(ErrorDesc,SMTExpr Bool)])
    memLoadPtr :: TypeDesc -> Pointer m -> m -> (Pointer m,[(ErrorDesc,SMTExpr Bool)])
    memStore :: TypeDesc -> Pointer m -> SMTExpr BitVector -> m -> (m,[(ErrorDesc,SMTExpr Bool)])
    memStorePtr :: TypeDesc -> Pointer m -> Pointer m -> m -> (m,[(ErrorDesc,SMTExpr Bool)])
    memIndex :: m -> TypeDesc -> [Either Integer (SMTExpr BitVector)] -> Pointer m -> Pointer m
    memCast :: m -> TypeDesc -> Pointer m -> Pointer m
    memEq :: m -> m -> SMTExpr Bool
    memPtrEq :: m -> Pointer m -> Pointer m -> SMTExpr Bool
    memPtrSwitch :: m -> [(Pointer m,SMTExpr Bool)] -> SMT (Pointer m)
    memCopy :: Integer -> Pointer m -> Pointer m -> m -> m
    memSet :: Integer -> SMTExpr BitVector -> Pointer m -> m -> m
    memDump :: m -> SMT String
    memSwitch :: [(m,SMTExpr Bool)] -> SMT m
    memPtrNull :: m -> Pointer m

flattenMemContent :: MemContent -> [SMTExpr BitVector]
flattenMemContent (MemCell x) = [x]
flattenMemContent (MemArray xs) = concat $ fmap flattenMemContent xs

typeWidth :: TypeDesc -> Integer
typeWidth (TDInt _ w)
  | w `mod` 8 == 0 = w `div` 8
  | otherwise = error $ "typeWidth called for "++show w
typeWidth (TDArray n tp) = n*(typeWidth tp)
typeWidth (TDStruct tps _) = sum (fmap typeWidth tps)
typeWidth tp = error $ "No typeWidth for "++show tp

bitWidth :: TypeDesc -> Integer
bitWidth (TDInt _ w) = w
bitWidth (TDArray n tp) = n*(bitWidth tp)
bitWidth (TDStruct tps _) = sum (fmap bitWidth tps)
bitWidth tp = error $ "No bitWidth for "++show tp

getOffset :: (TypeDesc -> Integer) -> TypeDesc -> [Integer] -> Integer
getOffset width tp idx = getOffset' tp idx 0
    where
      getOffset' _ [] off = off
      getOffset' (TDPtr tp) (i:is) off = getOffset' tp is (off + i*(width tp))
      getOffset' (TDStruct tps _) (i:is) off = let (pre,tp:_) = genericSplitAt i tps
                                               in getOffset' tp is (off + sum (fmap width pre))
      getOffset' (TDArray _ tp) (i:is) off = getOffset' tp is (off + i*(width tp))

flattenType :: TypeDesc -> [TypeDesc]
flattenType (TDStruct tps _) = concat $ fmap flattenType tps
flattenType (TDArray n tp) = concat $ genericReplicate n (flattenType tp)
flattenType (TDVector n tp) = concat $ genericReplicate n (flattenType tp)
flattenType tp = [tp]
