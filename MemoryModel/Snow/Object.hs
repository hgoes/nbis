{-# LANGUAGE RankNTypes #-}
module MemoryModel.Snow.Object where

import Language.SMTLib2
import Data.Map as Map
import Data.List as List

import TypeDesc
import MemoryModel

data Object ptr 
  = Bounded (BoundedObject ptr)
  | Unbounded (UnboundedObject ptr)

data UnboundedObject ptr
  = DynArrayObject { dynArrayIndexSize :: Integer
                   , dynArrayBound :: SMTExpr (SMTExpr (BitVector BVUntyped))
                   , dynArrayWrites :: [(SMTExpr (BitVector BVUntyped),BoundedObject ptr)]
                   }
  | DynFlatArrayObject { dynFlatArrayIndexSize :: Integer
                       , dynFlatArrayBound :: SMTExpr (SMTExpr (BitVector BVUntyped))
                       , dynFlatArray :: [SMTExpr (SMTArray (SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped))]
                       }

data BoundedObject ptr
  = WordObject (SMTExpr (BitVector BVUntyped))
  | StructObject [BoundedObject ptr]
  | StaticArrayObject [BoundedObject ptr]
  | ValidPointer ptr
  | NullPointer
  | AnyPointer
  deriving Show

data ObjAccessor ptr = ObjAccessor (forall a. (Object ptr -> (Object ptr,a,[(ErrorDesc,SMTExpr Bool)])) 
                                    -> Object ptr 
                                    -> (Object ptr,a,[(ErrorDesc,SMTExpr Bool)]))

changeAt :: Integer -> (a -> (a,b,c)) -> [a] -> ([a],b,c)
changeAt 0 f (x:xs) = let (x',y,z) = f x
                      in (x':xs,y,z)
changeAt n f (x:xs) = let (xs',y,z) = changeAt (n-1) f xs
                      in (x:xs',y,z)

indexObject :: Map String [TypeDesc] -> TypeDesc 
               -> [Either Integer (SMTExpr (BitVector BVUntyped))] 
               -> ObjAccessor ptr -> ObjAccessor ptr
-- Static array access
indexObject structs (PointerType tp) (i:idx) (ObjAccessor access)
  = ObjAccessor 
    (\f obj -> access (\obj' -> case (obj',i) of
                          (Bounded (StaticArrayObject objs),Left i') 
                            -> let (nobjs,res,errs) 
                                     = changeAt i' 
                                       (indexBounded structs tp idx f) objs
                               in (Bounded (StaticArrayObject nobjs),res,errs)
                          (Bounded obj,Left 0) 
                            -> let (nobj,res,errs) 
                                     = indexBounded structs tp idx f obj
                               in (Bounded obj,res,errs)
                      ) obj)

indexBounded :: Map String [TypeDesc] -> TypeDesc -> [Either Integer (SMTExpr (BitVector BVUntyped))] 
                -> (Object ptr -> (Object ptr,a,[(ErrorDesc,SMTExpr Bool)])) 
                -> BoundedObject ptr -> (BoundedObject ptr,a,[(ErrorDesc,SMTExpr Bool)])
indexBounded _ _ [] f obj = let (Bounded nobj,res,errs) = f (Bounded obj)
                            in (nobj,res,errs)
indexBounded structs (StructType descr) (Left i:idx) f (StructObject objs)
  = let tps = case descr of
          Left name -> case Map.lookup name structs of
            Just res -> res
            Nothing -> error $ "Couldn't resolve struct type "++name
          Right res -> res
        (nobjs,res,errs) = changeAt i (indexBounded structs (List.genericIndex tps i) idx f) objs
    in (StructObject nobjs,res,errs)
indexBounded structs (ArrayType _ tp) (Left i:idx) f (StaticArrayObject objs)
  = let (nobjs,res,errs) = changeAt i (indexBounded structs tp idx f) objs
    in (StaticArrayObject nobjs,res,errs)
indexBounded _ tp idx _ obj = error $ "indexBounded unimplemented for "++show tp++" "++show idx++" in Snow memory model"

allocaObject :: Map String [TypeDesc] -- ^ All structs in the program
                -> TypeDesc -- ^ The type to be allocated
                -> Either Integer (SMTExpr (BitVector BVUntyped)) -- ^ How many copies should be allocated?
                -> SMT (Object ptr)
allocaObject structs tp (Left 1) = fmap Bounded $ allocaBounded structs tp
allocaObject structs tp (Left sz) = do
  objs <- sequence $ genericReplicate sz (allocaBounded structs tp)
  return $ Bounded $ StaticArrayObject objs

allocaBounded :: Map String [TypeDesc] -- ^ All structs in the program
                 -> TypeDesc -- ^ The type to be allocated
                 -> SMT (BoundedObject ptr)
allocaBounded _ (PointerType tp) = return AnyPointer
allocaBounded _ (IntegerType w) = do
  v <- varNamedAnn "allocInt" w
  return $ WordObject v
allocaBounded structs (StructType desc) = do
  let tps = case desc of
        Left name -> case Map.lookup name structs of
          Just res -> res
          Nothing -> error $ "Couldn't resolve struct type "++name
        Right res -> res
  objs <- mapM (allocaBounded structs) tps
  return $ StructObject objs

loadObject :: Integer -> Object ptr -> (SMTExpr (BitVector BVUntyped),[(ErrorDesc,SMTExpr Bool)])
loadObject sz (Bounded obj) = case loadObject' sz obj of
  (0,Just res,errs) -> (res,errs)

loadObject' :: Integer -> BoundedObject ptr -> (Integer,Maybe (SMTExpr (BitVector BVUntyped)),[(ErrorDesc,SMTExpr Bool)])
loadObject' sz (WordObject v)
  = let vsize = extractAnnotation v
    in case compare sz vsize of
      EQ -> (0,Just v,[])
      LT -> (0,Just $ bvextract' 0 sz v,[])
      GT -> (sz-vsize,Just v,[])
loadObject' sz (StructObject []) = (sz,Nothing,[])
loadObject' sz (StructObject (obj:objs)) = case loadObject' sz obj of
  (0,res,errs) -> (0,res,errs)
  (sz',res,errs) -> let (sz'',res',errs') = loadObject' sz' (StructObject objs)
                    in (sz'',case res of
                           Nothing -> res'
                           Just r1 -> case res' of
                             Nothing -> Just r1
                             Just r2 -> Just $ bvconcat r1 r2,errs++errs')
loadObject' sz (StaticArrayObject []) = (sz,Nothing,[])
loadObject' sz (StaticArrayObject (obj:objs)) = case loadObject' sz obj of
  (0,res,errs) -> (0,res,errs)
  (sz',res,errs) -> let (sz'',res',errs') = loadObject' sz' (StaticArrayObject objs)
                    in (sz'',case res of
                           Nothing -> res'
                           Just r1 -> case res' of
                             Nothing -> Just r1
                             Just r2 -> Just $ bvconcat r1 r2,errs++errs')

storeObject :: SMTExpr (BitVector BVUntyped) -> Object ptr -> (Object ptr,[(ErrorDesc,SMTExpr Bool)])
storeObject bv (Bounded obj) 
  = let (noff,nobj,errs) = storeObject' 0 bv obj
    in (Bounded nobj,errs)

storeObject' :: Integer 
                -> SMTExpr (BitVector BVUntyped) 
                -> BoundedObject ptr 
                -> (Integer,BoundedObject ptr,[(ErrorDesc,SMTExpr Bool)])
storeObject' off bv (WordObject v)
  = let bvsize = extractAnnotation bv
        vsize = extractAnnotation v
    in case compare (bvsize-off) vsize of
      EQ -> (bvsize,WordObject $ if off==0
                                 then bv
                                 else bvextract' off vsize bv,[])
      LT -> (bvsize,WordObject $
                    bvconcat (if off==0
                              then bv
                              else bvextract' off (bvsize-off) bv)
                    (bvextract' (bvsize-off) (vsize-bvsize+off) v),[])
      GT -> (off+vsize,WordObject $
                       bvextract' off vsize bv,[])
storeObject' off bv (StructObject objs) 
  = let (noff,nobjs,errs) = storeObjects' off bv objs
    in (noff,StructObject nobjs,errs)
storeObject' off bv (StaticArrayObject objs)
  = let (noff,nobjs,errs) = storeObjects' off bv objs
    in (noff,StaticArrayObject nobjs,errs)
            
storeObjects' :: Integer -> SMTExpr (BitVector BVUntyped) 
                 -> [BoundedObject ptr]
                 -> (Integer,[BoundedObject ptr],[(ErrorDesc,SMTExpr Bool)])
storeObjects' off bv [] = (off,[],[])
storeObjects' off bv (obj:objs)
  | off==extractAnnotation bv = (off,obj:objs,[])
  | otherwise = let (noff,nobj,errs) = storeObject' off bv obj
                    (noff',nobjs,errs') = storeObjects' noff bv objs
                in (noff',nobj:nobjs,errs++errs')

storePtr :: ptr -> Object ptr -> (Object ptr,[(ErrorDesc,SMTExpr Bool)])
storePtr ptr (Bounded obj) = let (nobj,errs) = storePtr' ptr obj
                             in (Bounded nobj,errs)

storePtr' :: ptr -> BoundedObject ptr -> (BoundedObject ptr,[(ErrorDesc,SMTExpr Bool)])
storePtr' ptr (ValidPointer _) = (ValidPointer ptr,[])
storePtr' ptr NullPointer = (ValidPointer ptr,[])
storePtr' ptr AnyPointer = (ValidPointer ptr,[])