{-# LANGUAGE DeriveDataTypeable,TypeFamilies #-}
module MemoryModel.Plain where

import MemoryModel
import LLVM.Core (TypeDesc(..))
import Language.SMTLib2
import Data.Map as Map hiding (foldl)
import Data.Typeable
import Data.Maybe
import Data.Bitstream as BitS hiding (foldl,zipWith,zipWith3,concat,zip)
import Data.Traversable
import Prelude hiding (mapM,sequence)
import Data.List (genericReplicate)
import Data.Bits

newtype PlainMemory = PlainMem (Map TypeDesc (Map Int [SMTExpr BitVector])) deriving (Eq,Typeable)

data PlainPointer = PlainPtr { ptrType :: TypeDesc
                             , ptrLocation :: Int
                             , ptrOffset :: Int
                             } deriving (Eq,Ord,Show,Typeable)

instance MemoryModel PlainMemory where
  type Pointer PlainMemory = [(PlainPointer,SMTExpr Bool)]
  memNew tps = return $ PlainMem $ Map.fromList [ (tp,Map.empty) | tp <- tps ]
  memInit _ = constant True
  -- TODO: zero
  memAlloc _ tp (PlainMem mp) = do
    res <- mapM (\tp' -> varAnn (fromIntegral $ bitWidth tp')) (flattenType tp)
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
      tlen = bitWidth tp

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
