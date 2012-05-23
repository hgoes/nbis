{-# LANGUAGE DeriveDataTypeable,TypeFamilies,RankNTypes,FlexibleInstances,TypeSynonymInstances,ExistentialQuantification #-}
module MemoryModel.Plain (PlainMemory) where

import MemoryModel
import LLVM.Core (TypeDesc(..))
import Language.SMTLib2
import Data.Map as Map hiding (foldl,(!))
import Data.Typeable
import Data.Maybe
import Data.Bitstream as BitS (fromNBits,toBits)
import Data.Traversable
import Prelude hiding (mapM,sequence)
import Data.List (genericReplicate,genericIndex,genericDrop,intersperse,genericLength)
import Data.Bits

(!) :: (Show k,Ord k) => Map k a -> k -> a
(!) mp k = case Map.lookup k mp of
             Nothing -> error $ "Couldn't find key "++show k++" in "++show (Map.keys mp)
             Just r -> r

newBV :: Integer -> Integer -> SMTExpr BitVector
newBV sz val = constantAnn (BitS.fromNBits sz val) (fromIntegral sz)

data PlainMemory = PlainMem (Map TypeDesc (Map Int (Bool,PlainCont)))
                 deriving Typeable

debugMem :: PlainMemory -> String
debugMem (PlainMem mp) = show [ (tp,Map.keys bank) | (tp,bank) <- Map.toList mp ]


data PlainPointer = PlainPtr { ptrType :: TypeDesc
                             , ptrLocation :: Int
                             , ptrOffset :: [Either Integer (SMTExpr BitVector)]
                             } deriving (Typeable,Show)

data PlainCont = PlainStruct [PlainCont] 
               | forall p. PlainIdx p => PlainSingle (SMTExpr p) [SMTExpr BitVector]
               | PlainPtrs PlainPtrCont

data PlainPtrCont = PlainPtrArray [PlainPtrCont]
                  | PlainPtrCell [(Maybe PlainPointer,SMTExpr Bool)]

class SMTType p => PlainIdx p where
  plainWithIdx :: SMTExpr p -> SMTExpr BitVector -> (forall q. PlainIdx q => SMTExpr q -> (a,Maybe (SMTExpr q))) -> Maybe (a,Maybe (SMTExpr p))
  plainWithCell :: SMTExpr p -> (SMTExpr BitVector -> (a,Maybe (SMTExpr BitVector))) -> Maybe (a,Maybe (SMTExpr p))
  plainAnn :: p -> Integer -> SMTAnnotation p

instance PlainIdx BitVector where
  plainWithIdx _ _ _ = Nothing
  plainWithCell expr f = Just (f expr)
  plainAnn _ w = fromIntegral w

instance PlainIdx a => PlainIdx (SMTArray (SMTExpr BitVector) a) where
  plainWithIdx arr idx f = let (r,nv) = f (select arr idx)
                               narr = case nv of
                                 Nothing -> Nothing
                                 Just rnv -> Just $ store arr idx rnv
                           in Just (r,narr)
  plainWithCell _ _ = Nothing
  plainAnn u w = (64,plainAnn (fromUndefArray u) w)
    where
      fromUndefArray :: SMTArray (SMTExpr BitVector) a -> a
      fromUndefArray _ = undefined

mkPlainIdx :: Integer -> Integer -> (forall p. PlainIdx p => SMTExpr p -> SMT a) -> SMT a
mkPlainIdx w n f = undefFor n (\u -> do
                                  v <- varAnn (plainAnn (plainUndef u) w)
                                  f (enforceEq u v))
  where
    plainUndef :: SMTExpr p -> p
    plainUndef _ = undefined
    
    enforceEq :: u -> u -> u
    enforceEq _ = id

    undefFor :: Integer -> (forall p. PlainIdx p => SMTExpr p -> a) -> a
    undefFor 0 f = f (undefined::SMTExpr BitVector)
    undefFor n f = undefFor (n-1) (\u -> f (toUndefArray u))

    toUndefArray :: SMTExpr a -> SMTExpr (SMTArray (SMTExpr BitVector) a)
    toUndefArray _ = undefined

allIdx :: TypeDesc -> [[Integer]]
allIdx (TDStruct tps _) = concat $ zipWith (\n tp -> fmap (n:) (allIdx tp)) [0..] tps
allIdx (TDArray l tp) = concat $ fmap (\n -> fmap (n:) (allIdx tp)) [0..(l-1)]
allIdx (TDVector l tp) = concat $ fmap (\n -> fmap (n:) (allIdx tp)) [0..(l-1)]
allIdx _ = [[]]

allSuccIdx :: TypeDesc -> [Either Integer (SMTExpr BitVector)] -> [[Either Integer (SMTExpr BitVector)]]
allSuccIdx tp [] = fmap (fmap Left) (allIdx tp)
allSuccIdx (TDStruct tps _) ((Left i):is) = concat $ zipWith (\n tp -> fmap ((Left n):) (allSuccIdx tp is)) [i..] (genericDrop i tps)
allSuccIdx (TDArray l tp) ((Left i):is) = concat $ fmap (\n -> fmap ((Left n):) (allSuccIdx tp is)) [i..(l-1)]
allSuccIdx (TDArray l tp) ((Right i):is) = concat $ fmap (\n -> fmap ((Right $ if n==0 then i else bvadd i (constantAnn (BitS.fromNBits 64 (n::Integer)) 64)):) (allSuccIdx tp is)) [0..]
allSuccIdx (TDVector l tp) ((Left i):is) = concat $ fmap (\n -> fmap ((Left n):) (allSuccIdx tp is)) [i..(l-1)]
allSuccIdx (TDArray l tp) ((Right i):is) = concat $ fmap (\n -> fmap ((Right $ if n==0 then i else bvadd i (constantAnn (BitS.fromNBits 64 (n::Integer)) 64)):) (allSuccIdx tp is)) [0..]
allSuccIdx (TDPtr tp) ((Left i):is) = concat $ fmap (\n -> fmap ((Left n):) (allSuccIdx tp is)) [i..]
allSuccIdx (TDPtr tp) ((Right i):is) = concat $ fmap (\n -> fmap ((Right $ if n==0 then i else bvadd i (constantAnn (BitS.fromNBits 64 (n::Integer)) 64)):) (allSuccIdx tp is)) [0..]
allSuccIdx tp idx = error $ "Indexing type "++show tp++" with "++show idx

plainResolve :: PlainCont -> [Integer] -> [SMTExpr BitVector] -> SMTExpr BitVector
plainResolve (PlainStruct conts) (i:is) dis = plainResolve (conts `genericIndex` i) is dis
plainResolve (PlainStruct _) [] _ = error "plainResolve: There are too few static indices"
plainResolve (PlainSingle el _) [] [] = case plainWithCell el (\x -> (x,Nothing)) of
  Nothing -> error "plainResolve: Too few dynamic indices"
  Just (res,_) -> res
plainResolve (PlainSingle el dims) [] (i:is) = case plainWithIdx el i (\np -> (plainResolve (PlainSingle np (tail dims)) [] is,Nothing)) of
  Nothing -> error "plainResolve: Too many dynamic indices"
  Just (res,_) -> res
plainResolve (PlainSingle _ _) _ _ = error "plainResolve: Too many static indices"

plainModify :: PlainCont -> [Integer] -> [SMTExpr BitVector] -> (SMTExpr BitVector -> (a,Maybe (SMTExpr BitVector))) -> (a,PlainCont)
plainModify (PlainStruct conts) (i:is) dis f = let (res,conts') = modifyStruct i conts 
                                               in (res,PlainStruct conts')
  where
    modifyStruct 0 (x:xs) = let (a,nx) = plainModify x is dis f
                            in (a,nx:xs)
    modifyStruct i (x:xs) = let (a,xs') = modifyStruct (i-1) xs
                            in (a,x:xs')
plainModify (PlainStruct _) [] _ _ = error "plainModify: Too few static indices"
plainModify (PlainSingle el dim) [] dis f = let (res,nel) = modify' el dis f
                                                rnel = case nel of
                                                  Nothing -> el
                                                  Just el' -> el'
                                            in (res,PlainSingle rnel dim)
  where
    modify' :: PlainIdx p => SMTExpr p -> [SMTExpr BitVector] -> (SMTExpr BitVector -> (a,Maybe (SMTExpr BitVector))) -> (a,Maybe (SMTExpr p))
    modify' el [] f = case plainWithCell el (\bv -> f bv) of
      Just res -> res
      Nothing -> error "plainModify: Too few dynamic indices"
    modify' arr (i:is) f = case plainWithIdx arr i (\el -> modify' el is f) of
      Just res -> res
      Nothing -> error "plainModify: Too many dynamic indices"
plainModify (PlainSingle _ _) _ _ _ = error "plainModify: Too many static indices"

plainModifyPtr :: PlainPtrCont -> [Integer] -> [SMTExpr BitVector] -> ([(Maybe PlainPointer,SMTExpr Bool)] -> (a,[(Maybe PlainPointer,SMTExpr Bool)])) -> (a,PlainPtrCont)
plainModifyPtr _ _ (_:_) _ = error "Dynamic indices not allowed for pointer arrays"
plainModifyPtr (PlainPtrArray arr) (i:is) dyn f = (res,PlainPtrArray new)
  where
    (res,new) = modify' arr i
    
    modify' (x:xs) 0 = let (res,new) = plainModifyPtr x is dyn f
                       in (res,new:xs)
    modify' (x:xs) n = let (res,new) = modify' xs (n-1)
                       in (res,x:new)
plainModifyPtr (PlainPtrCell alts) [] dyn f = let (res,nalts) = f alts
                                              in (res,PlainPtrCell nalts)

translateIdx :: TypeDesc -> [Either Integer (SMTExpr BitVector)] -> ([Integer],[SMTExpr BitVector])
translateIdx (TDStruct tps _) ((Left idx):rest) = let (rst,rdyn) = translateIdx (genericIndex tps idx) rest
                                                  in (idx:rst,rdyn)
translateIdx (TDArray len tp) (idx:rest) = let (rst,rdyn) = translateIdx tp rest
                                               nidx = case idx of
                                                 Left st -> constantAnn (BitS.fromNBits 64 st) 64
                                                 Right bv -> bv
                                           in (rst,nidx:rdyn)
translateIdx (TDVector len tp)  (idx:rest) = let (rst,rdyn) = translateIdx tp rest
                                                 nidx = case idx of
                                                   Left st -> constantAnn (BitS.fromNBits 64 st) 64
                                                   Right bv -> bv
                                             in (rst,nidx:rdyn)
translateIdx (TDPtr tp) (idx:rest) = let (rst,rdyn) = translateIdx tp rest
                                         nidx = case idx of
                                           Left st -> constantAnn (BitS.fromNBits 64 st) 64
                                           Right bv -> bv
                                     in (rst,nidx:rdyn)
translateIdx _ [] = ([],[])
translateIdx tp idx = error $ "Implement translateIdx for "++show tp++" "++show idx

expandIdx :: [Either Integer (SMTExpr BitVector)] -> [Either Integer (SMTExpr BitVector)]
expandIdx = fmap (\v -> case v of
                     Left i -> Left i
                     Right bv -> let BitstreamLen w = extractAnnotation bv
                                 in if w < 64
                                    then Right $ bvconcat (constantAnn (BitS.fromNBits (64-w) (0::Integer) :: BitVector) (fromIntegral $ 64-w)) bv
                                    else Right bv)

contentToCell :: MemContent -> [Integer] -> SMTExpr BitVector
contentToCell (MemArray arr) (i:is) = contentToCell (genericIndex arr i) is
contentToCell (MemCell e) [] = e

plainNew :: TypeDesc -> [Either Integer (SMTExpr BitVector)] -> SMT PlainCont
plainNew (TDStruct tps _) d = do
  subs <- mapM (\tp -> plainNew tp d) tps
  return $ PlainStruct subs
plainNew (TDArray len tp) d = plainNew tp (d++[Left len])
plainNew (TDVector len tp) d = plainNew tp (d++[Left len])
plainNew (TDPtr tp) d = return $ PlainPtrs $ plainNewPtr d
  where
    plainNewPtr (Left l:ls) = PlainPtrArray $ genericReplicate l (plainNewPtr ls)
    plainNewPtr [] = PlainPtrCell [(Nothing,constant True)]
plainNew tp d = mkPlainIdx (bitWidth tp) (genericLength d) (\r -> return (PlainSingle r (fmap (\d' -> case d' of
                                                                                                  Left rd -> newBV 64 rd
                                                                                                  Right sz -> sz
                                                                                              ) d)))

plainAssign :: TypeDesc -> PlainCont -> MemContent -> [Integer] -> SMT ()
plainAssign (TDStruct tps _) (PlainStruct conts) (MemArray cells) path
  = mapM_ (\(tp,cont,cell) -> plainAssign tp cont cell path) (Prelude.zip3 tps conts cells)
plainAssign (TDArray len tp) cont (MemArray cells) path
  = mapM_ (\(i,cell) -> plainAssign tp cont cell (i:path)) (zip [0..] cells)
plainAssign (TDArray len tp) cont (MemArray cells) path
  = mapM_ (\(i,cell) -> plainAssign tp cont cell (i:path)) (zip [0..] cells)
plainAssign (TDPtr tp) cont mem path = return ()
plainAssign tp (PlainSingle el _) (MemCell bv) path
  = assert $ (resolve' el (Prelude.reverse path)) .==. bv
  where
    resolve' :: PlainIdx p => SMTExpr p -> [Integer] -> SMTExpr BitVector
    resolve' el (i:is) = case plainWithIdx el bv (\nel -> (resolve' nel is,Nothing)) of
      Just (res,_) -> res
    resolve' el [] = case plainWithCell el (\bv -> (bv,Nothing)) of
      Just (res,_) -> res

plainSwitch :: SMTExpr Bool -> TypeDesc -> PlainCont -> PlainCont -> Integer -> SMT PlainCont
plainSwitch cond (TDStruct tps _) (PlainStruct c1) (PlainStruct c2) d = do
  c3 <- mapM (\(tp,x,y) -> plainSwitch cond tp x y d) (Prelude.zip3 tps c1 c2)
  return $ PlainStruct c3
plainSwitch cond tp (PlainPtrs p1) (PlainPtrs p2) 0 = switchPtr cond tp p1 p2 >>= return.PlainPtrs
  where
    switchPtr cond (TDArray _ tp) (PlainPtrArray a1) (PlainPtrArray a2) = do
      res <- mapM (\(x,y) -> switchPtr cond tp x y) (zip a1 a2)
      return $ PlainPtrArray res
    switchPtr cond (TDVector _ tp) (PlainPtrArray a1) (PlainPtrArray a2) = do
      res <- mapM (\(x,y) -> switchPtr cond tp x y) (zip a1 a2)
      return $ PlainPtrArray res
    switchPtr cond (TDPtr tp) (PlainPtrCell c1) (PlainPtrCell c2) = return (PlainPtrCell $
                                                                            [ (trg,and' [c,cond]) | (trg,c) <- c1 ] ++
                                                                            [ (trg,and' [c,not' cond]) | (trg,c) <- c2 ])
plainSwitch cond (TDArray len tp) p1 p2 d = plainSwitch cond tp p1 p2 (d+1)
plainSwitch cond (TDVector len tp) p1 p2 d = plainSwitch cond tp p1 p2 (d+1)
plainSwitch cond tp (PlainSingle c1 dims1) (PlainSingle c2 dims2) d = case cast c2 of
  Just c2' -> if c1 == c2'
              then return (PlainSingle c1 dims1)
              else mkPlainIdx (bitWidth tp) d (\nc -> case cast nc of
                                                  Just nc' -> do
                                                    assert $ nc' .==. (ite cond c1 c2')
                                                    dims <- mapM (\(d1,d2) -> if d1==d2
                                                                              then return d1
                                                                              else (do
                                                                                       d <- varAnn 64
                                                                                       assert $ d .==. ite cond d1 d2
                                                                                       return d)) (zip dims1 dims2)
                                                    return (PlainSingle nc' dims))

addIndirection :: PlainCont -> SMT PlainCont
addIndirection (PlainStruct cs) = do
  cs' <- mapM addIndirection cs
  return (PlainStruct cs')
addIndirection (PlainSingle expr dims) = do
  nvar <- varAnn (64,extractAnnotation expr)
  assert $ (select nvar (constantAnn (BitS.fromNBits 64 (0::Integer)) 64::SMTExpr BitVector)) .==. expr
  return (PlainSingle nvar ((constantAnn (BitS.fromNBits 64 (1::Integer)) 64):dims))
addIndirection (PlainPtrs cont) = return $ PlainPtrs (PlainPtrArray [cont])

plainEq :: PlainCont -> PlainCont -> SMT ()
plainEq (PlainStruct s1) (PlainStruct s2) = mapM_ (\(x,y) -> plainEq x y) (zip s1 s2)
plainEq (PlainSingle s1 _) (PlainSingle s2 _) = case cast s2 of
  Just s2' -> assert $ s1 .==. s2'


plainDup :: PlainMemory -> SMT PlainMemory
plainDup (PlainMem mem) = do
  mp <- mapM (\arg -> case arg of
                 (TDPtr tp,bank) -> let dupPtrs (PlainPtrArray arr) = mapM dupPtrs arr >>= return.PlainPtrArray
                                        dupPtrs (PlainPtrCell cell) = mapM (\(c,cond) -> do
                                                                               ncond <- var
                                                                               assert $ ncond .==. cond
                                                                               return (c,ncond)) cell >>= return.PlainPtrCell
                                    in mapM (\(indir,PlainPtrs ptr) -> dupPtrs ptr >>= \ptr' -> return (indir,PlainPtrs ptr')) bank >>= \bank' -> return (TDPtr tp,bank')
                 (tp,bank) -> do
                   bank' <- mapM (\(indir,cont) -> do
                                     var <- plainNew tp (if indir then [case cont of
                                                                           PlainSingle _ (bv:_) -> Right bv] else [])
                                     plainEq cont var
                                     return (indir,var)) bank
                   return (tp,bank')
             ) (Map.toList mem)
  return $ PlainMem $ Map.fromList mp

instance MemoryModel PlainMemory where
  type Pointer PlainMemory = [(Maybe PlainPointer,SMTExpr Bool)]
  memNew tps = return $ PlainMem $ Map.fromList [ (tp,Map.empty) | tp <- tps ]
  memInit _ = constant True
  memAlloc tp sz cont (PlainMem mp) = do
    let indir = case sz of
          Left 1 -> False
          _ -> True
        off = if indir
              then [Left 0]
              else []
    res <- plainNew tp (if indir then [sz] else [])
    case cont of
      Nothing -> return ()
      Just cont' -> plainAssign tp res cont' []
    let (bank,mp') = Map.updateLookupWithKey (\_ entrs -> Just (Map.insert (Map.size entrs) (indir,res) entrs)) tp mp
    return $ case bank of
      Nothing -> ([(Just $ PlainPtr tp 0 off,constant True)],PlainMem (Map.insert tp (Map.singleton 0 (indir,res)) mp))
      Just bank' -> ([(Just $ PlainPtr tp (Map.size bank' - 1) off,constant True)],PlainMem mp')
  memIndex _ _ idx ptr = let nidx = expandIdx idx
                         in fmap (\(ptr',cond) -> (case ptr' of
                                                      Just ptr'' -> Just $ plainOffset ptr'' nidx
                                                      Nothing -> Nothing,cond)) ptr
  memSwitch choices = do 
    mem <- mkSwitch choices
    plainDup (PlainMem mem)
    where
      mkSwitch [(PlainMem mem,_)] = return mem
      mkSwitch ((PlainMem mem,cond):rest) = do
        res <- mkSwitch rest
        sequence $ Map.intersectionWithKey (\tp mp1 mp2 -> sequence $ Map.unionWith (\o1 o2
                                                                                     -> do
                                                                                       (i1,b1) <- o1
                                                                                       (i2,b2) <- o2
                                                                                       case (i1,i2) of
                                                                                         (False,True) -> do
                                                                                           b1' <- addIndirection b1
                                                                                           res <- plainSwitch cond tp b1' b2 1
                                                                                           return (True,res)
                                                                                         (True,False) -> do
                                                                                           b2' <- addIndirection b2
                                                                                           res <- plainSwitch cond tp b1 b2' 1
                                                                                           return (True,res)
                                                                                         (True,True) -> do
                                                                                           res <- plainSwitch cond tp b1 b2 1
                                                                                           return (True,res)
                                                                                         (False,False) -> do
                                                                                           res <- plainSwitch cond tp b1 b2 0
                                                                                           return (False,res)
                                                                                    ) (fmap return mp1) (fmap return mp2)
                                           ) mem res
  memLoad tp ptr (PlainMem mem) = (load' [ let (indir,cont) = (mem!(ptrType ptr')!(ptrLocation ptr'))
                                               off = if indir 
                                                     then ptrOffset ptr'
                                                     else case ptrOffset ptr' of
                                                       [] -> []
                                                       Left 0:rest -> rest
                                                       _ -> error $ "invalid memory indirection in load: "++show (ptrOffset ptr')
                                               rtp = if indir
                                                     then TDPtr (ptrType ptr')
                                                     else ptrType ptr'
                                               paths = allSuccIdx rtp off
                                               banks = fmap (\path -> let (stat,dyn) = translateIdx rtp path
                                                                      in plainResolve cont stat dyn) paths
                                           in (case typedLoad (bitWidth tp) [(ptrType ptr')] banks of
                                                  [bv] -> bv
                                                  bvs -> bvconcats bvs,cond) | (Just ptr',cond) <- ptr ],[])
    where
      load' [(bv,cond)] = bv
      load' ((bv,cond):rest) = ite cond bv (load' rest)
      load' [] = constantAnn (BitS.fromNBits (bitWidth tp) (0::Integer)) (fromIntegral $ bitWidth tp)
  memLoadPtr tp ptr (PlainMem mem)
    = (concat [ [ (cont',and' [cond,cond']) | (cont',cond') <- ptr_cont ]
             | (Just ptr',cond) <- ptr,
               let (indir,PlainPtrs cont) = mem!(ptrType ptr')!(ptrLocation ptr')  
                   off = if indir 
                         then ptrOffset ptr'
                         else case ptrOffset ptr' of
                           [] -> []
                           Left 0:rest -> rest
                           _ -> error $ "invalid memory indirection in load: "++show (ptrOffset ptr')
                   rtp = if indir
                         then TDPtr (ptrType ptr')
                         else ptrType ptr'
                   (stat,dyn) = translateIdx (ptrType ptr') off
                   (ptr_cont,_) = plainModifyPtr cont stat dyn (\ocont -> (ocont,ocont))
             ],[])
  memStore tp ptr cont (PlainMem mem) = (PlainMem $ store' ptr mem [],[])
    where
      store' [] mem _ = mem
      store' ((Nothing,cond):ptrs) mem prev = store' ptrs mem ((not' cond):prev)
      store' ((Just ptr,cond):ptrs) mem prev
        = store' ptrs (Map.adjust (Map.adjust (\(indir,pcont) -> let off = if indir then ptrOffset ptr
                                                                           else case ptrOffset ptr of
                                                                             [] -> []
                                                                             Left 0:rest -> rest
                                                                             _ -> error "invalid memory indirection in store"
                                                                     rtp = if indir then TDPtr (ptrType ptr)
                                                                           else ptrType ptr
                                                                     (stat,dyn) = translateIdx rtp off
                                                                     (_,ncont) = plainModify pcont stat dyn (\ocont -> ((),Just $ if Prelude.null ptrs && Prelude.null prev
                                                                                                                                  then cont
                                                                                                                                  else ite (and' (cond:prev)) cont ocont
                                                                                                                       ))
                                                                 in (indir,ncont)
                                              ) (ptrLocation ptr)) (ptrType ptr) mem) ((not' cond):prev)
  memStorePtr tp trg src (PlainMem mem) = (PlainMem $ store' trg mem [],[])
    where
      store' [] mem _ = mem
      store' ((Just ptr,cond):ptrs) mem prev
        = store' ptrs (Map.adjust (Map.adjust (\(indir,PlainPtrs cont) 
                                               -> let off = if indir then ptrOffset ptr
                                                            else case ptrOffset ptr of
                                                              [] -> []
                                                              Left 0:rest -> rest
                                                              _ -> error "invalid memory indirection in store"
                                                      rtp = if indir then TDPtr (ptrType ptr)
                                                            else ptrType ptr
                                                      (stat,dyn) = translateIdx rtp off
                                                      (_,ncont) = plainModifyPtr cont stat dyn 
                                                                  (\ocont -> ((),[ (n,and' $ cond:c:prev) | (n,c) <- src ]))
                                                  in (indir,PlainPtrs ncont)
                                              ) (ptrLocation ptr)) (ptrType ptr) mem) ((not' cond):prev)
  memDump (PlainMem mem) = mapM (\(tp,bank) -> do
                                    res <- mapM (\(nr,(indir,cont)) -> do
                                                    res <- dumpPlainCont tp cont (if indir then [1] else [])
                                                    return $ "  obj "++show nr++"\n    "++res
                                                ) (Map.toList bank)
                                    return $ unlines $ show tp:res
                                ) (Map.toList mem) >>= return.unlines
    where
      dumpPlainCont (TDStruct tps _) (PlainStruct conts) limits = do
        res <- mapM (\(tp,cont) -> dumpPlainCont tp cont limits) (zip tps conts)
        return $ "{ " ++ concat (intersperse ", " res) ++ " }"
      dumpPlainCont (TDArray len tp) plain limits = dumpPlainCont tp plain (limits++[len])
      dumpPlainCont (TDVector len tp) plain limits = dumpPlainCont tp plain (limits++[len])
      dumpPlainCont tp (PlainSingle cont _) [] = case plainWithCell cont (\x -> (x,Nothing)) of
        Just (r,_) -> do
          v <- getValue' (fromIntegral $ bitWidth tp) r
          return $ show (BitS.toBits v :: Integer)
      dumpPlainCont tp (PlainSingle cont dims) (l:ls) = do
        res <- mapM (\i -> case plainWithIdx cont (constantAnn (BitS.fromNBits 64 i) 64) (\expr -> (dumpPlainCont tp (PlainSingle expr (tail dims)) ls,Nothing)) of
                        Just (r,_) -> r) [0..(l-1)]
        return $ "[ "++concat (intersperse ", " res)++" ]"
  memCast _ to ptr = fmap (\(ptr',cond) -> case ptr' of
                              Just ptr'' -> if ptrType ptr'' /= to
                                            then error $ "Can't yet cast pointers from "++show (ptrType ptr'')++" to "++show to
                                            else (Just ptr'',cond)
                              Nothing -> (Nothing,cond)) ptr
  memPtrEq _ ptr1 ptr2 = or' [ and' $ [c1,c2]++extra 
                             | (ptr1',c1) <- ptr1,
                               (ptr2',c2) <- ptr2,
                               extra <- case ptr1' of
                                  Nothing -> case ptr2' of
                                    Nothing -> [[]]
                                    Just _ -> []
                                  Just ptr1'' -> case ptr2' of
                                    Nothing -> []
                                    Just ptr2'' -> if ptrType ptr1'' == ptrType ptr2'' && ptrLocation ptr1'' == ptrLocation ptr2''
                                                   then (case offEq (ptrOffset ptr1'') (ptrOffset ptr2'') of
                                                            Nothing -> []
                                                            Just res -> [res])
                                                   else []
                             ]
    where
      offEq [] [] = Just []
      offEq (x:xs) (y:ys) = case offEq xs ys of
        Nothing -> Nothing
        Just rest -> case x of
          Left ix -> case y of
            Left iy -> if ix==iy
                       then Just rest
                       else Nothing
            Right by -> let rw@(BitstreamLen w) = extractAnnotation by
                        in Just $ (constantAnn (BitS.fromNBits w ix) rw .==. by):rest
          Right bx -> case y of
            Left iy -> let rw@(BitstreamLen w) = extractAnnotation bx
                        in Just $ (constantAnn (BitS.fromNBits w iy) rw .==. bx):rest
            Right by -> Just $ (bx .==. by):rest
  memPtrNull _ = [(Nothing,constant True)]
  memPtrSwitch _ ptrs = return $ concat [ [ (ptr',and' [cond',cond]) | (ptr',cond') <- ptr ] | (ptr,cond) <- ptrs ]
      

typedLoad :: Integer -> [TypeDesc] -> [SMTExpr BitVector] -> [SMTExpr BitVector]
typedLoad 0 _ _ = []
typedLoad l ((TDStruct tps _):rest) banks = typedLoad l (tps++rest) banks
typedLoad l ((TDArray len tp):rest) banks = typedLoad l ((genericReplicate len tp)++rest) banks
typedLoad l ((TDVector len tp):rest) banks = typedLoad l ((genericReplicate len tp)++rest) banks
typedLoad l (tp:tps) (bank:banks) = case compare l (bitWidth tp) of
  EQ -> [bank]
  GT -> bank : typedLoad (l - (bitWidth tp)) tps banks
  LT -> [bvextract ((bitWidth tp)-1) ((bitWidth tp)-l) bank]
  
plainOffset :: PlainPointer -> [Either Integer (SMTExpr BitVector)] -> PlainPointer
plainOffset ptr idx = ptr { ptrOffset = plainIdxMerge (ptrOffset ptr) idx }
  where
    plainIdxMerge [] idx = idx
    plainIdxMerge idx [] = idx
    plainIdxMerge [Left x] (Left y:ys) = Left (x+y):ys
    plainIdxMerge [Right x] (Right y:ys) = Right (bvadd x y):ys
    plainIdxMerge [Left x] (Right y:ys) = Right (bvadd (constantAnn (BitS.fromNBits 64 x) 64) y):ys
    plainIdxMerge [Right x] (Left y:ys) = Right (bvadd x (constantAnn (BitS.fromNBits 64 y) 64)):ys
    plainIdxMerge (x:xs) ys = x:plainIdxMerge xs ys

{-
instance MemoryModel PlainMemory where
  type Pointer PlainMemory = [(PlainPointer,SMTExpr Bool)]
  memNew tps = return $ PlainMem $ Map.fromList [ (tp,Map.empty) | tp <- tps ]
  memInit _ = constant True
  -- TODO: zero
  memAlloc tp cont (PlainMem mp) = do
    res <- case cont of
      Nothing -> mapM (\tp' -> varAnn (fromIntegral $ bitWidth tp')) (flattenType tp)
      Just rcont -> mapM (\(tp',bv) -> do
                             v <- varAnn (fromIntegral $ bitWidth tp')
                             assert $ v .==. bv
                             return v
                         ) (zip (flattenType tp) (flattenMemContent rcont))
    let (bank,mp') = Map.updateLookupWithKey (\_ entrs -> Just (Map.insert (Map.size entrs) res entrs)) tp mp
    return $ case bank of
      Nothing -> ([(PlainPtr tp 0 0,constant True)],PlainMem (Map.insert tp (Map.singleton 0 res) mp))
      Just bank' -> ([(PlainPtr tp (Map.size bank' - 1) 0,constant True)],PlainMem mp')
  memPtrNew _ tp = return [(PlainPtr tp 0 0,constant True)]
  memLoad tp ptr (PlainMem mem) = load' [ (typedLoad (fromIntegral $ ptrOffset ptr') (bitWidth tp) (ptrType ptr') (mem!(ptrType ptr')!(ptrLocation ptr')),cond) | (ptr',cond) <- ptr ]
    where
      load' [(bv,cond)] = bv
      load' ((bv,cond):rest) = ite cond bv (load' rest)
  memIndex _ tp idx ptr = let off = fromIntegral $ getOffset bitWidth tp idx in [ (ptr' { ptrOffset = (ptrOffset ptr') + off },cond) | (ptr',cond) <- ptr ]
  memStore tp ptr val (PlainMem mem) = PlainMem $
                                       store' [ (ptr',typedStore (fromIntegral $ ptrOffset ptr') (bitWidth tp) 0 (flattenType $ ptrType ptr') val (mem!(ptrType ptr')!(ptrLocation ptr')),cond)
                                              | (ptr',cond) <- ptr ] []
    where
      store' ((ptr,res,cond):rest) pres 
        = let cond' = (case rest of
                          [] -> []
                          _ -> [cond]) ++ pres
          in Map.adjust (Map.adjust (\ocont -> zipWith (\o (n,u) -> if u
                                                                    then ite (and' cond') n o
                                                                    else o
                                                       ) ocont res) (ptrLocation ptr)
                        ) (ptrType ptr) (store' rest ((not' cond):pres))
      store' [] _ = mem
  memSwitch choices = do 
    mem <- mkSwitch choices
    return $ PlainMem mem
    where
      mkSwitch [(PlainMem mem,_)] = return mem
      mkSwitch ((PlainMem mem,cond):rest) = do
        res <- mkSwitch rest
        sequence $ Map.intersectionWithKey (\tp mp1 mp2 -> sequence $ Map.intersectionWith (\b1 b2 -> sequence $
                                                                                                     zipWith3 (\tp' e1 e2 -> if e1==e2
                                                                                                                             then return e1
                                                                                                                             else (do
                                                                                                                                      e <- varAnn (fromIntegral $ bitWidth tp')
                                                                                                                                      assert $ e .==. ite cond e1 e2
                                                                                                                                      return e)
                                                                                                              ) (flattenType tp) b1 b2
                                                                                          ) mp1 mp2
                                          ) mem res
  memDump (PlainMem mem) = mapM (\(tp,mp) -> do
                                    r <- mapM (\(nr,bank) -> do
                                                  vs <- mapM (\(tp',e) -> getValue' (fromIntegral $ bitWidth tp') e) (zip (flattenType tp) bank)
                                                  return $ ("  obj "++show nr):(fmap ("    "++) (renderMemObject tp vs))
                                              ) (Map.toList mp)
                                    return $ (show tp):(concat r)
                                ) (Map.toList mem) >>= return.unlines.concat
                                    
typedLoad :: Integer -> Integer -> TypeDesc -> [SMTExpr BitVector] -> SMTExpr BitVector
typedLoad offset len tp banks = case typedLoad' offset len (flattenType tp) banks of
  [(_,res)] -> res
  (_,f):rest -> foldl bvconcat f (fmap snd rest)

typedLoad' :: Integer -> Integer -> [TypeDesc] -> [SMTExpr BitVector] -> [(Integer,SMTExpr BitVector)]
typedLoad' _ 0 _ _ = []
typedLoad' offset len (tp:tps) (bank:banks)
  | offset >= tlen             = typedLoad' (offset - tlen) len tps banks
  | offset == 0 && tlen <= len = (tlen,bank):typedLoad' 0 (len-tlen) tps banks
  | tlen <= len+offset         = (tlen-offset,bvextract (tlen-offset-1) 0 bank):typedLoad' 0 (len-tlen+offset) tps banks
  | otherwise                  = [(len,bvextract (tlen-offset-1) (tlen-offset-len) bank)]
  where
    tlen = bitWidth tp
    {-rbank b = case b of
      Nothing -> error "Load from invalid memory"
      Just b' -> b'-}

typedStore :: Integer -> Integer -> Integer -> [TypeDesc] -> SMTExpr BitVector -> [SMTExpr BitVector] -> [(SMTExpr BitVector,Bool)]
typedStore offset len eoff [] expr [] = []
typedStore offset len eoff (tp:tps) expr (arr:arrs)
    | eoff >= len                             = fmap (\x -> (x,False)) (arr:arrs)
    | offset >= tlen                          = (arr,False):typedStore (offset - tlen) len eoff tps expr arrs
    | offset == 0 && tlen == len && eoff == 0 = (expr,True):(fmap (\x -> (x,False)) arrs)
    | offset == 0 && tlen <= len-eoff         = (bvextract (eoff+tlen-1) eoff expr,True):(typedStore 0 len (eoff+tlen) tps expr arrs)
    | offset == 0                             = let orig = bvextract (tlen-len-1) eoff arr
                                                in (bvconcat expr orig,True):(fmap (\x -> (x,False)) arrs)
    | otherwise                               = let (orig_l,orig_r) = (bvextract (tlen-1) offset arr,
                                                                       bvextract (offset+len-eoff-1) 0 arr)
                                                in (bvconcat orig_l (bvconcat expr orig_r),True):(fmap (\x -> (x,False)) arrs)
    where
      tlen = bitWidth tp-}

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
