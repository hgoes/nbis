{-# LANGUAGE TypeFamilies,FlexibleContexts,MultiParamTypeClasses #-}
module MemoryModel where

import Language.SMTLib2
import Data.List (genericSplitAt,genericReplicate)
import Data.Set as Set
import Data.Map as Map
import TypeDesc
import Data.Proxy
import Value

data MemContent = MemCell Integer Integer
                | MemArray [MemContent]
                | MemNull
                deriving (Show,Eq,Ord)

data ErrorDesc = Custom
               | NullDeref
               | Overrun
               | Underrun
               | FreeAccess
               | DoubleFree
               deriving (Show,Eq,Ord)

type DynNum = Either Integer (SMTExpr (BitVector BVUntyped))

data MemoryInstruction m p res where
  MIMerge :: m -> MemoryInstruction m p ()
  MIConnect :: m -> m -> MemoryInstruction m p ()
  MIPtrConnect :: p -> p -> MemoryInstruction m p ()
  MINull :: TypeDesc -> p -> MemoryInstruction m p ()
  MIAlloc :: m -> TypeDesc -> DynNum -> p -> m -> MemoryInstruction m p ()
  MILoad :: m -> p -> Integer -> MemoryInstruction m p Val
  MILoadPtr :: m -> p -> p -> MemoryInstruction m p ()
  MIStore :: m -> Val -> p -> m -> MemoryInstruction m p ()
  MIStorePtr :: m -> p -> p -> m -> MemoryInstruction m p ()
  MICompare :: p -> p -> MemoryInstruction m p BoolVal
  MISelect :: [(BoolVal,p)] -> p -> MemoryInstruction m p ()
  MICast :: TypeDesc -> TypeDesc -> p -> p -> MemoryInstruction m p ()
  MIIndex :: TypeDesc -> TypeDesc -> [Val] -> p -> p -> MemoryInstruction m p ()
  MIPhi :: [(BoolVal,m)] -> m -> MemoryInstruction m p ()
  MICopy :: m -> p -> p -> CopyOptions -> m -> MemoryInstruction m p ()
  MIStrLen :: m -> p -> MemoryInstruction m p Val
  MISet :: m -> p -> Val -> Val -> m -> MemoryInstruction m p ()
  MIFree :: m -> p -> m -> MemoryInstruction m p ()

data CopyOptions = CopyOpts { copySizeLimit :: Maybe Val -- ^ A size in bytes after which to stop the copying
                            , copyStopper :: Maybe Val   -- ^ If this character is found in the source, stop copying
                            , copyMayOverlap :: Bool     -- ^ Are source and destination allowed to overlap?
                            } deriving (Show,Eq)

class MemoryModel mem mloc ptr where
  memNew :: Proxy mloc
            -> Integer      -- ^ Pointer width
            -> Set TypeDesc      -- ^ A set of all types occuring in the program
            -> Map String [TypeDesc] -- ^ The content of all named structs
            -> [(ptr,TypeDesc,Maybe MemContent)] -- ^ Global variables
            -> SMT mem
  makeEntry :: Proxy ptr -> mem -> mloc -> SMT mem
  addInstruction :: mem -> BoolVal
                    -> MemoryInstruction mloc ptr res -> Map ptr TypeDesc
                    -> SMT (res,mem)
  --addProgram :: mem -> SMTExpr Bool -> [mloc] -> MemoryProgram mloc ptr -> Map ptr TypeDesc -> SMT mem
  --connectLocation :: mem -> Proxy ptr -> SMTExpr Bool -> mloc -> mloc -> SMT mem
  --connectPointer :: mem -> Proxy mloc -> SMTExpr Bool -> ptr -> ptr -> SMT mem
  memoryErrors :: mem -> Proxy mloc -> Proxy ptr -> [(ErrorDesc,SMTExpr Bool)]
  debugMem :: mem -> Proxy mloc -> Proxy ptr -> String

memInstrSrc :: MemoryInstruction m p res -> Maybe m
memInstrSrc (MINull _ _) = Nothing
memInstrSrc (MIAlloc m _ _ _ _) = Just m
memInstrSrc (MILoad m _ _) = Just m
memInstrSrc (MILoadPtr m _ _) = Just m
memInstrSrc (MIStore m _ _ _) = Just m
memInstrSrc (MIStorePtr m _ _ _) = Just m
memInstrSrc (MICompare _ _) = Nothing
memInstrSrc (MISelect _ _) = Nothing
memInstrSrc (MICast _ _ _ _) = Nothing
memInstrSrc (MIIndex _ _ _ _ _) = Nothing
memInstrSrc (MIPhi _ _) = Nothing
memInstrSrc (MICopy m _ _ _ _) = Just m
memInstrSrc (MIStrLen m _) = Just m
memInstrSrc (MISet m _ _ _ _) = Just m
memInstrSrc (MIFree m _ _) = Just m

memInstrTrg :: MemoryInstruction m p res -> Maybe m
memInstrTrg (MINull _ _) = Nothing
memInstrTrg (MIAlloc _ _ _ _ m) = Just m
memInstrTrg (MILoad _ _ _) = Nothing
memInstrTrg (MILoadPtr _ _ _) = Nothing
memInstrTrg (MIStore _ _ _ m) = Just m
memInstrTrg (MIStorePtr _ _ _ m) = Just m
memInstrTrg (MICompare _ _) = Nothing
memInstrTrg (MISelect _ _) = Nothing
memInstrTrg (MICast _ _ _ _) = Nothing
memInstrTrg (MIIndex _ _ _ _ _) = Nothing
memInstrTrg (MIPhi _ m) = Just m
memInstrTrg (MICopy _ _ _ _ m) = Just m
memInstrTrg (MIStrLen _ _) = Nothing
memInstrTrg (MISet _ _ _ _ m) = Just m
memInstrTrg (MIFree _ _ m) = Just m

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

dynNumExpr :: Integer -> DynNum -> SMTExpr (BitVector BVUntyped)
dynNumExpr width (Left x) = constantAnn (BitVector x) width
dynNumExpr width (Right x) = case compare width (extractAnnotation x) of
  EQ -> x
  GT -> bvconcat (constantAnn (BitVector 0::BitVector BVUntyped) (width - (extractAnnotation x))) x
