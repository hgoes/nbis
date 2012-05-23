{-# LANGUAGE TypeFamilies,DeriveDataTypeable #-}
module MemoryModel.Typed where

import MemoryModel
import Language.SMTLib2
import Language.SMTLib2.Internals
import LLVM.Core (TypeDesc(..))
import Data.Word
import Data.Typeable
import Data.List (genericReplicate,mapAccumL,nub)
import Data.Map as Map hiding (foldl)
import qualified Data.Bitstream as BitS
import Data.Bits

type PtrT = Word64

data TypedMemory = TypedMemory { memoryBanks :: Map TypeDesc (SMTExpr PtrT,[SMTExpr (SMTArray (SMTExpr PtrT) BitVector)]) }
                 deriving (Eq,Typeable)

bitWidth' :: TypeDesc -> Integer
bitWidth' (TDPtr _) = 64
bitWidth' tp = bitWidth tp

typeWidth' :: TypeDesc -> Integer
typeWidth' (TDPtr _) = 8
typeWidth' tp = typeWidth tp

{-instance Args TypedMemory where
    type ArgAnnotation TypedMemory = [TypeDesc]
    foldExprs f s mem tps
        = let (mp,ns) = foldl (\(mp,cs) tp -> if Map.member tp mp
                                              then (mp,cs)
                                              else (let ~(old_nxt,old_arrs) = (memoryBanks mem)!tp 
                                                        (c1,nxt) = f cs old_nxt ()
                                                        ((c2,_),arrs) = mapAccumL (\(c,old_arrs) tp -> let (c',arr) = f c (head old_arrs) ((),fromIntegral $ bitWidth' tp)
                                                                                                       in ((c',tail old_arrs),arr)
                                                                                  ) (c1,old_arrs) (flattenType tp)
                                                    in (Map.insert tp (nxt,arrs) mp,c2))
                              ) (Map.empty,s) tps
          in (ns,TypedMemory mp)-}

data TypedPointer' = TypedPointer' { pointerType :: TypeDesc
                                   , pointerLocation :: SMTExpr PtrT
                                   , pointerOffset :: Integer
                                   } deriving (Eq,Typeable)

newtype TypedPointer = TypedPointer { ptrChoices :: [(TypedPointer',SMTExpr Bool)] } deriving (Eq,Typeable)

{-instance Args TypedPointer where
  type ArgAnnotation TypedPointer = TypeDesc
  foldExprs f s ptrs tp = let (s1,nptr) = foldExprs f s (fst $ head $ ptrChoices ptrs) tp
                              (s2,ncond) = f s (snd $ head $ ptrChoices ptrs) ()
                          in (s2,TypedPointer [(nptr,ncond)])

instance Args TypedPointer' where
    type ArgAnnotation TypedPointer' = TypeDesc
    foldExprs f s ptr tp = let (s',loc) = f s (pointerLocation ptr) ()
                           in (s',TypedPointer' tp loc 0) -}

instance MemoryModel TypedMemory where
  type Pointer TypedMemory = TypedPointer
  memNew tps = do
    entrs <- mapM (\tp -> do
                      ptr <- var
                      arrs <- mapM (\tp' -> varAnn ((),fromIntegral $ bitWidth tp')) (flattenType tp)
                      return (tp,(ptr,arrs))) (nub tps)
    return $ TypedMemory (Map.fromList entrs)
  memPtrNew _ tp = do
    loc <- var
    return $ TypedPointer [(TypedPointer' tp loc 0,constant True)]
  memInit mem = and' [ nxt .==. 0 | (nxt,_) <- Map.elems (memoryBanks mem) ]
  memAlloc tp _ cont mem = let (nxt,arrs) = (memoryBanks mem)!tp
                               --narrs = if zero
                               --        then zipWith (\tp' arr -> store arr nxt (constantAnn (BitS.fromNBits (bitWidth tp') (0::Integer)) (fromIntegral $ bitWidth tp'))) (flattenType tp) arrs
                               --        else arrs
                           in return (TypedPointer [(TypedPointer' tp nxt 0,constant True)],TypedMemory $ Map.insert tp (nxt + 1,arrs) (memoryBanks mem))
  memLoad tp (TypedPointer ptrs) mem = (case ptrs of
                                           [(ptr,_)] -> loadSingle ptr
                                           ((ptr,cond):rest) -> ite cond (loadSingle ptr) (fst $ memLoad tp (TypedPointer rest) mem),[])
    where
      banks ptr = [ select bank (pointerLocation ptr) | bank <- snd $ (memoryBanks mem)!(pointerType ptr) ]
      loadSingle ptr = if pointerType ptr == tp && pointerOffset ptr == 0
                       then (case banks ptr of
                                [bank] -> bank
                                bs -> bvconcats bs)
                       else typedLoad (pointerOffset ptr) (bitWidth' tp) (flattenType $ pointerType ptr) (banks ptr)
  memStore tp (TypedPointer ptrs) val mem = (TypedMemory $ store' ptrs (memoryBanks mem),[])
    where
      store' [(ptr,_)] mem = let (nxt,banks) = mem!(pointerType ptr)
                                 nbanks = fmap fst $ typedStore (pointerOffset ptr) (bitWidth' tp) 0 (flattenType $ pointerType ptr) (pointerLocation ptr) val banks
                             in Map.insert (pointerType ptr) (nxt,nbanks) mem
      store' ((ptr,cond):ptrs) mem = let (nxt,banks) = mem!(pointerType ptr)
                                         nbanks = typedStore (pointerOffset ptr) (bitWidth' tp) 0 (flattenType $ pointerType ptr) (pointerLocation ptr) val banks
                                         nbanks' = zipWith (\obank (nbank,ch) -> if ch
                                                                                 then ite cond nbank obank
                                                                                 else obank
                                                           ) banks nbanks
                                     in store' ptrs (Map.insert (pointerType ptr) (nxt,nbanks') mem)
  memIndex _ tp idx (TypedPointer ptrs) = TypedPointer $ fmap (\(ptr,cond) -> (ptr { pointerOffset = (pointerOffset ptr) + (getOffset bitWidth' tp (fmap (\(Left i) -> i) idx)) },cond)) ptrs
  memCast _ tp ptr = ptr
  memEq mem1 mem2 = and' $ Map.elems $ Map.intersectionWith (\(nxt1,bank1) (nxt2,bank2) -> and' ((nxt1 .==. nxt2):(zipWith (.==.) bank1 bank2))) (memoryBanks mem1) (memoryBanks mem2)
  {-memPtrEq _ p1 p2
    | pointerType p1 /= pointerType p2     = constant False
    | pointerOffset p1 /= pointerOffset p2 = constant False
    | otherwise = (pointerLocation p1) .==. (pointerLocation p2) -}
  memCopy len (TypedPointer [(ptr_to,_)]) (TypedPointer [(ptr_from,_)]) mem
    = let (nxt_to,banks_to) = (memoryBanks mem)!(pointerType ptr_to)
          vecs = [ select bank (pointerLocation ptr_from) | bank <- snd $ (memoryBanks mem)!(pointerType ptr_from) ]
          nbanks = typedMemCopy (len*8) (pointerOffset ptr_to) (pointerOffset ptr_from)
                   (flattenType $ pointerType ptr_to) 
                   (flattenType $ pointerType ptr_from) (pointerLocation ptr_to) banks_to vecs
      in TypedMemory $ Map.insert (pointerType ptr_to) (nxt_to,nbanks) (memoryBanks mem)
  memSet len val (TypedPointer [(ptr,_)]) mem
    = let (nxt,banks) = (memoryBanks mem)!(pointerType ptr)
          nbanks = typedMemSet (len*8) (pointerOffset ptr) (flattenType $ pointerType ptr) (pointerLocation ptr) banks val
      in TypedMemory $ Map.insert (pointerType ptr) (nxt,nbanks) (memoryBanks mem)
  memDump mem = do
    mapM (\(tp,(nxt,banks)) -> do
      rnxt <- getValue nxt
      objs <- if rnxt > 0
              then mapM (\i -> do
                        vs <- mapM (\(tp',arr) -> getValue' (fromIntegral $ bitWidth' tp') (select arr (constant i))) (zip (flattenType tp) banks)
                        return (("  obj "++show i):(fmap ("    "++) (renderMemObject tp vs)))) [0..(fromIntegral $ rnxt-1 :: PtrT)]
              else return []
      return (unlines $ show tp:concat objs)) (Map.toList $ memoryBanks mem) >>= return.unlines
  memPtrSwitch _ conds = do
    res <- mapM (\(TypedPointer ptrs,cond) -> do
                    ncond <- var
                    assert $ ncond .==. cond
                    case ptrs of
                      [(ptr,_)] -> return [(ptr,ncond)]
                      _ -> return [(ptr,and' [ncond,cond']) | (ptr,cond') <- ptrs ]) conds
    return $ TypedPointer $ concat res
  memSwitch [(mem,_)] = return mem
  memSwitch conds = do
    rmp <- mapM (\(tp,(ptr,arr)) -> do
                    nptr <- var
                    narr <- mapM (\tp' -> varAnn ((),fromIntegral $ bitWidth tp')) (flattenType tp)
                    assert $ nptr .==. ptr
                    mapM_ (\(nel,el) -> assert $ nel .==. el) (zip narr arr)
                    return (tp,(nptr,narr))
                ) (Map.toAscList $ mkSwitch conds)
    return $ TypedMemory $ Map.fromAscList rmp
    where
      mkSwitch :: [(TypedMemory,SMTExpr Bool)] -> Map TypeDesc (SMTExpr PtrT,[SMTExpr (SMTArray (SMTExpr PtrT) BitVector)])
      mkSwitch [(TypedMemory mem,cond)] = mem
      mkSwitch ((TypedMemory mem',cond'):rest)
        = Map.unionWith (\(ptr1,banks1) (ptr2,banks2) -> (ite cond' ptr1 ptr2,zipWith (\e1 e2 -> if e1==e2
                                                                                                 then e1
                                                                                                 else ite cond' e1 e2) banks1 banks2)) mem' (mkSwitch rest)

renderMemObject :: TypeDesc -> [BitVector] -> [String]
renderMemObject tp bvs = snd $ renderMemObject' bvs tp

renderMemObject' :: [BitVector] -> TypeDesc -> ([BitVector],[String])
renderMemObject' bvs (TDStruct tps _) = let (rest,res) = mapAccumL renderMemObject' bvs tps
                                        in (rest,"struct {":(fmap ("  "++) $ concat res)++["}"])
renderMemObject' bvs (TDArray n tp) = let (rest,res) = mapAccumL renderMemObject' bvs (genericReplicate n tp)
                                      in (rest,"array {":(fmap ("  "++) $ concat res)++["}"])
renderMemObject' bvs (TDVector n tp) = let (rest,res) = mapAccumL renderMemObject' bvs (genericReplicate n tp)
                                       in (rest,"vector {":(fmap ("  "++) $ concat res)++["}"])
renderMemObject' (bv:bvs) (TDInt s bits) = let r = BitS.toBits bv :: Integer
                                               rr = if s && testBit r (fromIntegral (bits-1))
                                                    then (complement r) - 1
                                                    else r
                                           in (bvs,[show r++" : "++(if s then "i" else "u")++show bits])

typedLoad :: Integer -> Integer -> [TypeDesc] -> [SMTExpr BitVector] -> SMTExpr BitVector
typedLoad offset len tps banks = case typedLoad' offset len tps banks of
  [(_,res)] -> res
  (_,f):rest -> foldl bvconcat f (fmap snd rest)

typedLoad' :: Integer -> Integer -> [TypeDesc] -> [SMTExpr BitVector] -> [(Integer,SMTExpr BitVector)]
typedLoad' offset len ((TDStruct tps _):rest) banks = typedLoad' offset len (tps++rest) banks
typedLoad' _ 0 _ _ = []
typedLoad' offset len (tp:tps) (bank:banks)
  | offset >= tlen             = typedLoad' (offset - tlen) len tps banks
  | offset == 0 && tlen <= len = (tlen,bank):typedLoad' 0 (len-tlen) tps banks
  | tlen <= len+offset         = (tlen-offset,bvextract (tlen-offset-1) 0 bank):typedLoad' 0 (len-tlen+offset) tps banks
  | otherwise                  = [(len,bvextract (tlen-offset-1) (tlen-offset-len) bank)]
  where
    tlen = bitWidth' tp

typedStore :: Integer -> Integer -> Integer -> [TypeDesc] -> SMTExpr PtrT -> SMTExpr BitVector -> [SMTExpr (SMTArray (SMTExpr PtrT) BitVector)] -> [(SMTExpr (SMTArray (SMTExpr PtrT) BitVector),Bool)]
typedStore offset len eoff [] idx expr [] = []
typedStore offset len eoff (tp:tps) idx expr (arr:arrs)
    | eoff >= len                             = fmap (\x -> (x,False)) (arr:arrs)
    | offset >= tlen                          = (arr,False):typedStore (offset - tlen) len eoff tps idx expr arrs
    | offset == 0 && tlen == len && eoff == 0 = (store arr idx expr,True):(fmap (\x -> (x,False)) arrs)
    | offset == 0 && tlen <= len-eoff         = (store arr idx (bvextract (eoff+tlen-1) eoff expr),True):(typedStore 0 len (eoff+tlen) tps idx expr arrs)
    | offset == 0                             = (store arr idx (bvconcat expr (bvextract (tlen-len-1) eoff (select arr idx))),True):(fmap (\x -> (x,False)) arrs)
    | otherwise                               = (store arr idx (bvconcat
                                                                (bvextract (tlen-1) offset (select arr idx))
                                                                (bvconcat
                                                                 expr
                                                                 (bvextract (offset+len-eoff-1) 0 (select arr idx)))),True):(fmap (\x -> (x,False)) arrs)
    where
      tlen = bitWidth' tp

typedMemCopy' :: SMTExpr PtrT -> Integer -> Integer -> [(Integer,SMTExpr BitVector)] -> [(Integer,SMTExpr (SMTArray (SMTExpr PtrT) BitVector))] -> [SMTExpr (SMTArray (SMTExpr PtrT) BitVector)]
typedMemCopy' ptr off_v off_b [] banks = fmap snd banks
typedMemCopy' ptr off_v off_b ((len,vec):vecs) ((blen,bank):banks)
  | off_v >= len                            = typedMemCopy' ptr (off_v-len) off_b vecs ((blen,bank):banks)
  | off_b >= blen                           = bank:typedMemCopy' ptr off_v (off_b - blen) ((len,vec):vecs) banks
  | off_v == 0 && off_b == 0 && len == blen = (store bank ptr vec):typedMemCopy' ptr 0 0 vecs banks
  | off_v == 0 && off_b == 0 && len < blen  = (store bank ptr (bvconcat vec (bvextract (blen-len-1) 0 (select bank ptr)))):(fmap snd banks)
  | off_b == 0 && len-off_v >= blen         = (store bank ptr (bvextract (len-off_v-1) (len-blen) vec)):typedMemCopy' ptr (off_v + blen) 0 ((len,vec):vecs) banks
  | blen-off_b >= len-off_v                 = (store bank ptr
                                               (bvconcat
                                                (bvextract (blen-1) (blen-off_b) (select bank ptr))
                                                (bvconcat
                                                 (bvextract (len-off_v-1) 0 vec)
                                                 (bvextract (blen-off_b-len+off_v-1) 0 (select bank ptr))))):(fmap snd banks)
  | otherwise                               = (store bank ptr
                                               (bvconcat
                                                (bvextract (blen-1) (blen-off_b) (select bank ptr))
                                                (bvextract (len-off_v-1) (len-blen+off_b-off_v) vec))):typedMemCopy' ptr (off_v+blen-off_b) 0 ((len,vec):vecs) banks

mergeTypeLens :: [TypeDesc] -> [a] -> [(Integer,a)]
mergeTypeLens [] [] = []
mergeTypeLens (tp:tps) (x:xs) = (bitWidth' tp,x):mergeTypeLens tps xs

typedMemCopy :: Integer -> Integer -> Integer -> [TypeDesc] -> [TypeDesc] -> SMTExpr PtrT -> [SMTExpr (SMTArray (SMTExpr PtrT) BitVector)] -> [SMTExpr BitVector] -> [SMTExpr (SMTArray (SMTExpr PtrT) BitVector)]
typedMemCopy len off_to off_from tps_to tps_from ptr arrs vecs
  = let vec = typedLoad' off_from len tps_from vecs
    in typedMemCopy' ptr 0 off_to vec (mergeTypeLens tps_to arrs)

typedMemSet :: Integer -> Integer -> [TypeDesc] -> SMTExpr PtrT -> [SMTExpr (SMTArray (SMTExpr PtrT) BitVector)] -> SMTExpr BitVector -> [SMTExpr (SMTArray (SMTExpr PtrT) BitVector)]
typedMemSet 0 _ _ _ mem _ = mem
typedMemSet len off (tp:tps) ptr (arr:arrs) val
  | off >= tlen = arr:typedMemSet len (off-tlen) tps ptr arrs val
  | off==0 && tlen == 8 = (store arr ptr val):typedMemSet (len-8) 0 tps ptr arrs val
  | otherwise = (store arr ptr (bvconcats cont)):typedMemSet (max (len-tlen+off) 0) (if r==0 
                                                                                     then 0
                                                                                     else (8-r)) tps ptr arrs val
  where
    tlen = bitWidth' tp
    (x,r) = (min (tlen-off) len) `divMod` 8
    cont = (if off==0
            then []
            else [bvextract (tlen-1) (tlen-off) (select arr ptr)]
           ) ++ genericReplicate x val 
           ++ (if r==0
               then []
               else [bvextract 7 (8-r) val])