{-# LANGUAGE TypeFamilies,FlexibleContexts #-}
module MemoryModel where

import Language.SMTLib2
import LLVM.Core (TypeDesc(..))
import Data.Typeable
import Data.Unit
import Data.List (genericSplitAt,genericReplicate)
import Data.Set as Set

data MemContent = MemCell Integer Integer
                | MemArray [MemContent]
                | MemNull
                deriving Show

data ErrorDesc = Custom
               | NullDeref
               | Overrun
               | FreeAccess
               deriving (Show,Eq,Ord)

class MemoryModel m where
    type LocalMem m
    type Pointer m
    memNew :: Set TypeDesc -> SMT m
    memInit :: m -> SMT (LocalMem m)
    memAlloc :: TypeDesc -> Either Integer (SMTExpr (BitVector BVUntyped)) 
                -> Maybe MemContent -> m -> LocalMem m -> SMT (Pointer m,m,LocalMem m)
    memLoad :: TypeDesc -> Pointer m -> SMTExpr Bool -> m -> LocalMem m -> SMT (SMTExpr (BitVector BVUntyped),[(ErrorDesc,SMTExpr Bool)],m)
    memLoadPtr :: TypeDesc -> Pointer m -> m -> LocalMem m -> (Pointer m,[(ErrorDesc,SMTExpr Bool)],m)
    memStore :: TypeDesc -> Pointer m -> SMTExpr (BitVector BVUntyped) -> SMTExpr Bool -> m -> LocalMem m 
                -> SMT (m,LocalMem m,[(ErrorDesc,SMTExpr Bool)])
    memStorePtr :: TypeDesc -> Pointer m -> Pointer m -> m -> LocalMem m -> (m,LocalMem m,[(ErrorDesc,SMTExpr Bool)])
    memIndex :: m -> TypeDesc -> [Either Integer (SMTExpr (BitVector BVUntyped))] -> Pointer m -> (Pointer m,m)
    memCast :: m -> TypeDesc -> Pointer m -> (Pointer m,m)
    --memEq :: m -> LocalMem m -> LocalMem m -> SMTExpr Bool
    memEq :: m -> SMTExpr Bool -> LocalMem m -> LocalMem m -> SMT (LocalMem m,m)
    memPtrEq :: m -> Pointer m -> Pointer m -> (SMTExpr Bool,m)
    memPtrSwitch :: m -> [(Pointer m,SMTExpr Bool)] -> SMT (Pointer m,m)
    memCopy :: m -> Integer -> Pointer m -> Pointer m -> LocalMem m -> (LocalMem m,m)
    memSet :: m -> Integer -> SMTExpr (BitVector BVUntyped) -> Pointer m -> LocalMem m -> (LocalMem m,m)
    memDump :: m -> LocalMem m -> SMT String
    memSwitch :: m -> [(LocalMem m,SMTExpr Bool)] -> SMT (LocalMem m)
    memPtrNull :: m -> (Pointer m,m)
    memPtrNew :: m -> (Pointer m,m)
    memPtrExtend :: m -> Pointer m -> Pointer m -> SMTExpr Bool -> SMT m
    memDebug :: m -> String

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
