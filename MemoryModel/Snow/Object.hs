{-# LANGUAGE RankNTypes #-}
module MemoryModel.Snow.Object where

import Language.SMTLib2
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List as List
--import Debug.Trace

import TypeDesc
import MemoryModel

data Object ptr
  = Bounded (BoundedObject ptr)
  | Unbounded (UnboundedObject ptr)
  deriving (Show,Eq)

data UnboundedObject ptr
  = DynArrayObject { dynArrayIndexSize :: Integer
                   , dynArrayBound :: SMTExpr (BitVector BVUntyped)
                   , dynArrayWrites :: [(SMTExpr (BitVector BVUntyped),BoundedObject ptr)]
                   }
  | DynFlatArrayObject { dynFlatArrayIndexSize :: Integer
                       , dynFlatArrayBound :: SMTExpr (BitVector BVUntyped)
                       , dynFlatArray :: [SMTExpr (SMTArray (SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped))]
                       }
  deriving (Show,Eq)

data BoundedObject ptr
  = WordObject (SMTExpr (BitVector BVUntyped))
  | StructObject [BoundedObject ptr]
  | StaticArrayObject [BoundedObject ptr]
  | ValidPointer ptr
  | NullPointer
  | AnyPointer
  deriving (Show,Eq)

data ObjAccessor ptr = ObjAccessor (forall a. (Object ptr -> (Object ptr,[(a,SMTExpr Bool)],[(ErrorDesc,SMTExpr Bool)]))
                                    -> Object ptr
                                    -> (Object ptr,[(a,SMTExpr Bool)],[(ErrorDesc,SMTExpr Bool)]))

type PtrIndex = [(TypeDesc,[DynNum])]

ptrIndexCast :: Map String [TypeDesc] -> TypeDesc -> PtrIndex -> PtrIndex
ptrIndexCast structs tp1 ref@((tp2,idx):rest) = case indexType structs tp2 idx of
  StructType desc -> let tps = case desc of
                           Left name -> case Map.lookup name structs of
                             Just res -> res
                           Right res -> res
                     in if head tps == tp1
                        then (tp2,idx++[Left 0]):rest
                        else ptrIndexCast' tp1 ref
  _ -> ptrIndexCast' tp1 ref
ptrIndexCast _ tp ref = ptrIndexCast' tp ref

ptrIndexCast' :: TypeDesc -> PtrIndex -> PtrIndex
ptrIndexCast' tp [] = [(tp,[])]
ptrIndexCast' tp ((_,[]):rest) = (tp,[]):rest
ptrIndexCast' tp1 ((tp2,idx):rest)
  | tp1 == tp2 = (tp1,idx):rest
  | otherwise = (tp1,[]):(tp2,idx):rest

ptrIndexIndex :: [DynNum] -> PtrIndex -> PtrIndex
ptrIndexIndex idx' ((tp,idx):rest) = (tp,mergeIdx idx idx'):rest
  where
    mergeIdx [] idx = idx
    mergeIdx [i1] (i2:rest) = dynNumCombine (\x y -> Left $ x+y) (\x y -> Right $ bvadd x y) i1 i2:rest
    mergeIdx (i:is) idx = i:mergeIdx is idx

ptrIndexEq :: PtrIndex -> PtrIndex -> Either Bool (SMTExpr Bool)
ptrIndexEq [] [] = Left True
ptrIndexEq ((_,[]):r1) ((_,[]):r2) = ptrIndexEq r1 r2
ptrIndexEq ((tp1,idx1):r1) ((tp2,idx2):r2)
  | tp1 == tp2 = case idxCompare idx1 idx2 of
                  Left False -> Left False
                  Left True -> ptrIndexEq r1 r2
                  Right c1 -> case ptrIndexEq r1 r2 of
                               Left False -> Left False
                               Left True -> Right c1
                               Right c2 -> Right (c1 .&&. c2)

ptrIndexGetAccessor :: Show ptr => Map String [TypeDesc] -> PtrIndex -> ObjAccessor ptr
ptrIndexGetAccessor _ [] = ObjAccessor id
ptrIndexGetAccessor structs all@((tp,idx):rest)
  = {-trace (show all) $-} indexObject structs (PointerType tp) (normalizeIndex (PointerType tp) idx) (ptrIndexGetAccessor structs rest)

ptrIndexGetType :: Map String [TypeDesc] -> PtrIndex -> TypeDesc
ptrIndexGetType structs ((tp,idx):_) = indexType structs (PointerType tp) idx

idxCompare :: [DynNum]
              -> [DynNum]
              -> Either Bool (SMTExpr Bool)
idxCompare [] [] = Left True
idxCompare (x:xs) (y:ys) = case dynNumCombine (\x y -> Left $ x==y) (\x y -> Right $ x .==. y) x y of
  Left False -> Left False
  Left True -> case idxCompare xs ys of
    Left res' -> Left res'
    Right res' -> Right res'
  Right res -> case idxCompare xs ys of
    Left False -> Left False
    Left True -> Right res
    Right res' -> Right $ res .&&. res'

changeAt :: Integer -> a -> (a -> (a,b,[(ErrorDesc,SMTExpr Bool)])) -> [a] -> ([a],b,[(ErrorDesc,SMTExpr Bool)])
changeAt 0 _ f (x:xs) = let (x',y,z) = f x
                        in (x':xs,y,z)
changeAt n def f (x:xs) = let (xs',y,z) = changeAt (n-1) def f xs
                          in (x:xs',y,z)
changeAt _ def f [] = let (x',y,errs) = f def
                      in ([],y,(Overrun,constant True):errs)

changeAtDyn :: SMTExpr (BitVector BVUntyped) -> (a -> SMTExpr Bool -> (a,b,c)) -> [a] -> ([a],[b],[c])
changeAtDyn idx f xs = change' 0 xs
  where
    idx_sz = extractAnnotation idx

    change' i [] = ([],[],[])
    change' i (x:xs) = let (nx,r,e) = f x (idx .==. (constantAnn (BitVector i) idx_sz))
                           (nxs,rs,es) = change' (i+1) xs
                       in (nx:nxs,r:rs,e:es)

normalizeIndex :: TypeDesc -> [DynNum] -> [DynNum]
normalizeIndex tp is = case normalizeIndex' tp is of
  (Nothing,nis) -> nis
  (Just _,_) -> is

normalizeIndex' :: TypeDesc -> [DynNum] -> (Maybe DynNum,[DynNum])
normalizeIndex' tp [] = (Nothing,[])
normalizeIndex' (ArrayType n tp) (i:is) = case normalizeIndex' tp is of
  (Nothing,nis) -> case i of
    Left i' -> let (upd,rest) = i' `divMod` n
               in if upd==0
                  then (Nothing,i:nis)
                  else (Just (Left upd),Left rest:nis)
    Right _ -> (Nothing,i:nis)
  (Just upd,nis) -> case (i,upd) of
    (Left i',Left upd') -> let (nupd,rest) = (i'+upd') `divMod` n
                           in if nupd==0
                              then (Nothing,Left rest:nis)
                              else (Just (Left nupd),Left rest:nis)
    _ -> (Nothing,i:is)
normalizeIndex' (PointerType tp) (i:is) = case normalizeIndex' tp is of
  (Just upd,nis) -> case (upd,i) of
    (Left upd',Left i') -> (Nothing,Left (i'+upd'):nis)
    _ -> (Nothing,i:is)
  _ -> (Nothing,i:is)
normalizeIndex' _ is = (Nothing,is)

indexObject :: Show ptr => Map String [TypeDesc] -> TypeDesc
               -> [DynNum]
               -> ObjAccessor ptr -> ObjAccessor ptr
indexObject _ _ [] access = access
-- Static array access
indexObject structs (PointerType tp) (i:idx) (ObjAccessor access)
  = ObjAccessor
    (\f obj -> access (\obj' -> case (obj',i) of
                          (Bounded (StaticArrayObject objs),Left i')
                            -> let (nobjs,res,errs)
                                     = changeAt i' (head objs)
                                       (indexBounded structs tp idx f) objs
                               in (Bounded (StaticArrayObject nobjs),res,errs)
                          (Bounded (StaticArrayObject objs),Right i')
                            -> let (nobjs,res,errs) = changeAtDyn i' (\el cond -> let (nel,res,errs) = indexBounded structs tp idx f el
                                                                                      nerrs = fmap (\(desc,cond') -> (desc,cond .&&. cond')) errs
                                                                                  in (iteBounded cond nel el,(res,cond),nerrs)
                                                                     ) objs
                                   nres = concat $ fmap (\(lst,c) -> fmap (\(x,c') -> (x,c' .&&. c)) lst) res
                               in (Bounded (StaticArrayObject nobjs),nres,concat errs)
                          (Unbounded obj,_) -> let (nobj,res,errs) = indexUnbounded structs tp (i:idx) f obj
                                               in (Unbounded nobj,res,errs)
                          _ -> error $ "indexObject of "++show obj'++" with "++show i++" unimplemented"
                      ) obj)
{-indexObject structs (StructType desc) (Left i:idx) (ObjAccessor access)
  = let tps = case desc of
          Left name -> case Map.lookup name structs of
            Just res -> res
          Right res -> res
        tp = List.genericIndex tps i
    in ObjAccessor
       (\f obj -> access (\obj' -> case obj' of
                             Bounded (StructObject objs)
                               -> let (nobjs,res,errs) = changeAt i (head objs) (indexBounded structs tp idx f) objs
                                  in (Bounded (StructObject nobjs),res,errs)
                         ) obj)-}
indexObject _ tp idx _ = error $ "indexObject not implemented for "++show tp++" "++show idx

indexBounded :: Show ptr => Map String [TypeDesc] -> TypeDesc -> [DynNum]
                -> (Object ptr -> (Object ptr,[(a,SMTExpr Bool)],[(ErrorDesc,SMTExpr Bool)]))
                -> BoundedObject ptr -> (BoundedObject ptr,[(a,SMTExpr Bool)],[(ErrorDesc,SMTExpr Bool)])
indexBounded _ _ [] f obj = let (Bounded nobj,res,errs) = f (Bounded obj)
                            in (nobj,res,errs)
indexBounded structs (StructType descr) (Left i:idx) f (StructObject objs)
  = let tps = case descr of
          Left name -> case Map.lookup name structs of
            Just res -> res
            Nothing -> error $ "Couldn't resolve struct type "++name
          Right res -> res
        (nobjs,res,errs) = changeAt i (head objs) (indexBounded structs (List.genericIndex tps i) idx f) objs
    in (StructObject nobjs,res,errs)
indexBounded structs (ArrayType _ tp) (Left i:idx) f (StaticArrayObject objs)
  = let (nobjs,res,errs) = changeAt i (head objs) (indexBounded structs tp idx f) objs
    in (StaticArrayObject nobjs,res,errs)
indexBounded structs (ArrayType sz tp) (Right i:idx) f (StaticArrayObject objs)
  = let (nobjs,res,errs) = changeAtDyn i (\el cond -> let (nel,res,errs) = indexBounded structs tp idx f el
                                                          nerrs = fmap (\(desc,cond') -> (desc,cond .&&. cond')) errs
                                                      in (iteBounded cond nel el,(res,cond),nerrs)
                                         ) objs
        nres = concat $ fmap (\(lst,c) -> fmap (\(x,c') -> (x,c' .&&. c)) lst) res
    in (StaticArrayObject nobjs,nres,(Overrun,i `bvsge` (constantAnn (BitVector sz) (extractAnnotation i))):
                                     (Underrun,i `bvslt` (constantAnn (BitVector 0) (extractAnnotation i))):
                                     concat errs)
indexBounded _ tp idx _ obj = error $ "indexBounded unimplemented for "++show tp++" "++show idx++" ("++show obj++") in Snow memory model"

indexUnbounded :: Show ptr => Map String [TypeDesc] -> TypeDesc -> [DynNum]
                  -> (Object ptr -> (Object ptr,[(a,SMTExpr Bool)],[(ErrorDesc,SMTExpr Bool)]))
                  -> UnboundedObject ptr
                  -> (UnboundedObject ptr,[(a,SMTExpr Bool)],[(ErrorDesc,SMTExpr Bool)])
indexUnbounded structs tp (i:is) f dynarr@(DynFlatArrayObject { dynFlatArrayBound = sz
                                                              , dynFlatArray = arrs
                                                              , dynFlatArrayIndexSize = idx_sz
                                                              })
  = let i' = case i of
          Right x -> x
          Left x -> constantAnn (BitVector x) idx_sz
        (nobj,res,errs) = indexBounded structs tp is f (assembleObject structs tp [ select arr i' | arr <- arrs ])
    in (dynarr { dynFlatArray = [ store arr i' v | (arr,v) <- zip arrs (disassembleObject nobj) ] },res,{-(Overrun,sz .<=. i):-}errs)
indexUnbounded _ tp idx _ obj = error $ "indexUnbounded unimplemented for "++show tp++" "++show idx++" ("++show obj++") in Snow memory model"

assembleObject :: Map String [TypeDesc] -> TypeDesc -> [SMTExpr (BitVector BVUntyped)] -> BoundedObject ptr
assembleObject _ (IntegerType w) [v] = WordObject v

disassembleObject :: BoundedObject ptr -> [SMTExpr (BitVector BVUntyped)]
disassembleObject (WordObject v) = [v]

allocaObject :: Map String [TypeDesc] -- ^ All structs in the program
                -> TypeDesc -- ^ The type to be allocated
                -> Either Integer (SMTExpr (BitVector BVUntyped)) -- ^ How many copies should be allocated?
                -> SMT (Object ptr)
allocaObject structs tp (Left sz) = do
  objs <- sequence $ genericReplicate sz (allocaBounded structs tp)
  return $ Bounded $ StaticArrayObject objs
allocaObject structs tp (Right sz) = fmap Unbounded (allocaUnbounded structs tp sz)

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
allocaBounded structs (ArrayType sz tp) = do
  objs <- sequence $ genericReplicate sz (allocaBounded structs tp)
  return $ StaticArrayObject objs
allocaBounded _ tp = error $ "allocaBound not implemented for "++show tp

allocaUnbounded :: Map String [TypeDesc]
                   -> TypeDesc
                   -> SMTExpr (BitVector BVUntyped)
                   -> SMT (UnboundedObject ptr)
allocaUnbounded structs (IntegerType w) sz = do
  let sz_width = extractAnnotation sz
  arr <- varNamedAnn "allocArray" (sz_width,w)
  return (DynFlatArrayObject { dynFlatArrayIndexSize = sz_width
                             , dynFlatArrayBound = sz
                             , dynFlatArray = [arr] })

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

loadPtr :: Show ptr => Object ptr -> (Maybe ptr,[(ErrorDesc,SMTExpr Bool)])
loadPtr (Bounded (ValidPointer p)) = (Just p,[])
loadPtr (Bounded NullPointer) = (Nothing,[])
loadPtr (Bounded AnyPointer) = (Nothing,[]) -- FIXME: What to do here?
loadPtr (Bounded (StaticArrayObject (ptr:_))) = loadPtr (Bounded ptr)
loadPtr obj = error $ "Cant load pointer from "++show obj

storeObject :: Show ptr => SMTExpr (BitVector BVUntyped) -> Object ptr -> (Object ptr,[(ErrorDesc,SMTExpr Bool)])
storeObject bv (Bounded obj)
  = let (noff,nobj,errs) = storeObject' 0 bv obj
    in (Bounded nobj,errs)

storeObject' :: Show ptr => Integer
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
storeObject' _ _ obj = error $ "storeObject' not implemented for "++show obj

storeObjects' :: Show ptr => Integer -> SMTExpr (BitVector BVUntyped)
                 -> [BoundedObject ptr]
                 -> (Integer,[BoundedObject ptr],[(ErrorDesc,SMTExpr Bool)])
storeObjects' off bv [] = (off,[],[])
storeObjects' off bv (obj:objs)
  | off==extractAnnotation bv = (off,obj:objs,[])
  | otherwise = let (noff,nobj,errs) = storeObject' off bv obj
                    (noff',nobjs,errs') = storeObjects' noff bv objs
                in (noff',nobj:nobjs,errs++errs')

storePtr :: Show ptr => ptr -> Object ptr -> (Object ptr,[(ErrorDesc,SMTExpr Bool)])
storePtr ptr (Bounded obj) = let (nobj,errs) = storePtr' ptr obj
                             in (Bounded nobj,errs)

storePtr' :: Show ptr => ptr -> BoundedObject ptr -> (BoundedObject ptr,[(ErrorDesc,SMTExpr Bool)])
storePtr' ptr (ValidPointer _) = (ValidPointer ptr,[])
storePtr' ptr NullPointer = (ValidPointer ptr,[])
storePtr' ptr AnyPointer = (ValidPointer ptr,[])
storePtr' ptr (StaticArrayObject (_:ptrs)) = (StaticArrayObject ((ValidPointer ptr):ptrs),[])
storePtr' ptr obj = error $ "storePtr': Storing pointer "++show ptr++" to object "++show obj++" not implemented"

iteBounded :: SMTExpr Bool -> BoundedObject ptr -> BoundedObject ptr -> BoundedObject ptr
iteBounded cond (WordObject w1) (WordObject w2) = WordObject (ite cond w1 w2)
