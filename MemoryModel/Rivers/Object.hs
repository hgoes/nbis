{-# LANGUAGE RankNTypes,PackageImports #-}
module MemoryModel.Rivers.Object where

--import MemoryModel
import Language.SMTLib2
--import TypeDesc
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (intercalate)
--import "mtl" Control.Monad.Trans (liftIO)
import Debug.Trace

data RiverObject = StaticObj [StaticObject]
                 | DynamicObj DynamicObject
                 deriving (Show,Eq)

data StaticObject = StaticWord (SMTExpr (BitVector BVUntyped))
                  | StaticArray { staticArrayObj :: [SMTExpr (SMTArray (SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped))]
                                , staticArrayBound :: Integer
                                }
                  deriving (Show,Eq)

data DynamicObject = DynamicArray { dynamicArrayObj :: [SMTExpr (SMTArray (SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped))]
                                  , dynamicArrayBound :: SMTExpr (BitVector BVUntyped)
                                  }
                   deriving (Show,Eq)

data Offset = Offset { staticOffset :: Integer -- ^ In bytes
                     , dynamicOffset :: Map Integer (SMTExpr (BitVector BVUntyped))
                     } deriving (Show,Eq)

data StaticAcc = StaticAcc { staticAccBefore :: [StaticObject]
                           , staticAccPos :: StaticPos
                           , staticAccAfter :: [StaticObject]
                           }

data StaticPos = InBetween
               | InWord { inWord :: SMTExpr (BitVector BVUntyped)
                        , inWordBound :: Integer
                        , inWordPos :: Integer
                        }
               | InArray { inArrayBefore :: [SMTExpr (SMTArray (SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped))]
                         , inArrayAfter :: [SMTExpr (SMTArray (SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped))]
                         , inArrayBound :: Integer
                         , inArrayIdx :: Integer
                         , inArrayPos :: Maybe (Integer,Integer,SMTExpr (SMTArray (SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped)))
                         }

mkStaticAcc :: [StaticObject] -> StaticAcc
mkStaticAcc objs = StaticAcc { staticAccBefore = []
                             , staticAccPos = InBetween
                             , staticAccAfter = objs }

delStaticAcc :: StaticAcc -> [StaticObject]
delStaticAcc acc = (reverse $ staticAccBefore acc)++
                   (case staticAccPos acc of
                       InBetween -> []
                       InWord { inWord = w } -> [StaticWord w]
                       InArray { inArrayBefore = before
                               , inArrayAfter = after
                               , inArrayBound = bound
                               , inArrayPos = pos }
                         -> [StaticArray ((reverse before)++
                                          (case pos of
                                              Nothing -> []
                                              Just (_,_,arr) -> [arr])++
                                          after) bound])++
                   (staticAccAfter acc)

staticAccAdvance :: Integer -> StaticAcc -> StaticAcc
staticAccAdvance 0 acc = acc
staticAccAdvance n acc = case staticAccPos acc of
  InBetween -> let w:ws = staticAccAfter acc
                   npos = case w of
                     StaticWord w' -> InWord w' (extractAnnotation w') 0
                     StaticArray arr b -> InArray [] arr b 0 Nothing
               in staticAccAdvance n (acc { staticAccPos = npos
                                          , staticAccAfter = ws })
  InWord { inWordPos = pos
         , inWordBound = b
         , inWord = w } -> if n+pos >= b
                           then staticAccAdvance (n-b+pos)
                                (acc { staticAccBefore = (StaticWord w):(staticAccBefore acc)
                                     , staticAccPos = InBetween
                                     })
                           else acc { staticAccPos = InWord { inWord = w
                                                            , inWordBound = b
                                                            , inWordPos = pos+n } }
  InArray { inArrayPos = p
          , inArrayBefore = before
          , inArrayAfter = after
          , inArrayBound = b
          , inArrayIdx = idx } -> case p of
    Nothing -> case after of
      a:as -> let (_,el_sz) = extractAnnotation a
              in staticAccAdvance n
                 (acc { staticAccPos = (staticAccPos acc) { inArrayPos = Just (0,el_sz,a)
                                                          , inArrayAfter = as }
                      })
      [] -> if idx==b
            then staticAccAdvance n
                 (acc { staticAccBefore = (StaticArray (reverse before) b):(staticAccBefore acc)
                      , staticAccPos = InBetween
                      })
            else staticAccAdvance n
                 (acc { staticAccPos = InArray { inArrayBefore = []
                                               , inArrayAfter = reverse before
                                               , inArrayBound = b
                                               , inArrayIdx = idx+1
                                               , inArrayPos = Nothing } })
    Just (off,bnd,arr) -> if n+off >= bnd
                          then staticAccAdvance (n-bnd+off)
                               (acc { staticAccPos = InArray { inArrayBefore = arr:before
                                                             , inArrayAfter = after
                                                             , inArrayBound = b
                                                             , inArrayIdx = idx
                                                             , inArrayPos = Nothing }
                                    })
                          else acc { staticAccPos = InArray { inArrayBefore = before
                                                            , inArrayAfter = after
                                                            , inArrayBound = b
                                                            , inArrayIdx = idx
                                                            , inArrayPos = Just (off+n,bnd,arr)
                                                            }
                                   }

staticAccChew :: (a -> SMTExpr (BitVector BVUntyped) -> (a,SMTExpr (BitVector BVUntyped)))
              -> a -> Integer
              -> StaticAcc
              -> (a,StaticAcc)
staticAccChew f cur size acc = case staticAccPos acc of
  InBetween -> let w:ws = staticAccAfter acc
               in case w of
                 StaticWord w'
                   -> staticAccChew f cur size
                      (acc { staticAccAfter = ws
                           , staticAccPos = InWord { inWord = w'
                                                   , inWordBound = extractAnnotation w'
                                                   , inWordPos = 0 }
                           })
                 StaticArray arrs b
                   -> staticAccChew f cur size
                      (acc { staticAccAfter = ws
                           , staticAccPos = InArray { inArrayBefore = []
                                                    , inArrayAfter = arrs
                                                    , inArrayBound = b
                                                    , inArrayIdx = 0
                                                    , inArrayPos = Nothing }
                           })
  InWord { inWord = w
         , inWordBound = b
         , inWordPos = p }
    | p==0 && b==size -> let (ncur,nw) = f cur w
                         in (ncur,acc { staticAccBefore = (StaticWord nw):staticAccBefore acc
                                      , staticAccPos = InBetween })
    | p==0 && b<size -> let (cur1,nw) = f cur w
                        in staticAccChew f cur1 (size-b)
                           (acc { staticAccBefore = (StaticWord nw):(staticAccBefore acc)
                                , staticAccPos = InBetween
                                })
    | p==0 && b>size -> let (ncur,nw) = f cur (bvextract' (b-size) size w)
                        in (ncur,acc { staticAccPos = InWord { inWord = bvconcat nw (bvextract' 0 (b-size) w)
                                                             , inWordBound = b
                                                             , inWordPos = p+size }
                                     })
    | p+size<=b -> let (ncur,w1) = f cur (bvextract' (b-p-size) size w)
                       w2 = bvconcat (bvextract' (b-p) p w)
                            (bvconcat w1
                             (bvextract' 0 (b-p-size) w))
                   in (ncur,acc { staticAccPos = InWord { inWord = w2
                                                        , inWordBound = b
                                                        , inWordPos = p+size } })
    | otherwise -> let (cur1,w1) = f cur (bvextract' 0 (b-p) w)
                   in staticAccChew f cur1 (size-b+p)
                      (acc { staticAccBefore = (StaticWord (bvconcat (bvextract' (b-p) p w) w1)):
                                               (staticAccBefore acc)
                           , staticAccPos = InBetween })
  InArray { inArrayBefore = before
          , inArrayAfter = after
          , inArrayBound = b
          , inArrayIdx = idx
          , inArrayPos = pos }
    -> case pos of
    Nothing -> case after of
      [] -> if idx==b
            then staticAccChew f cur size
                 (acc { staticAccBefore = (StaticArray (reverse before) b):
                                          (staticAccBefore acc)
                      , staticAccPos = InBetween
                      })
            else staticAccChew f cur size
                 (acc { staticAccPos = InArray { inArrayBefore = []
                                               , inArrayAfter = reverse before
                                               , inArrayBound = b
                                               , inArrayIdx = idx+1
                                               , inArrayPos = Nothing }
                      })
      a:as -> staticAccChew f cur size
              (acc { staticAccPos = InArray { inArrayBefore = before
                                            , inArrayAfter = as
                                            , inArrayBound = b
                                            , inArrayIdx = idx
                                            , inArrayPos = Just (0,snd (extractAnnotation a),a)
                                            }
                   })
    Just (off,el_sz,a)
      | off==0 && el_sz==size
        -> let (cur1,nw) = f cur (select a (constOff idx))
           in (cur1,acc { staticAccPos = InArray { inArrayBefore = (store a (constOff idx) nw):before
                                                 , inArrayAfter = after
                                                 , inArrayBound = b
                                                 , inArrayIdx = idx
                                                 , inArrayPos = Nothing }
                        })
      | off==0 && el_sz<size
        -> let (cur1,nw) = f cur (select a (constOff idx))
           in staticAccChew f cur1 (size-el_sz)
              (acc { staticAccPos = InArray { inArrayBefore = (store a (constOff idx) nw):before
                                            , inArrayAfter = after
                                            , inArrayBound = b
                                            , inArrayIdx = idx
                                            , inArrayPos = Nothing } })
      | off==0 && el_sz>size
        -> let (cur1,nw) = f cur (bvextract' (el_sz-size) size (select a (constOff idx)))
           in (cur1,acc { staticAccPos = InArray { inArrayBefore = before
                                                 , inArrayAfter = after
                                                 , inArrayBound = b
                                                 , inArrayIdx = idx
                                                 , inArrayPos = Just (off+size,el_sz,
                                                                      store a (constOff idx)
                                                                      (bvconcat nw (bvextract' 0 (el_sz-size) (select a (constOff idx)))))
                                                 } })
      | off+size <= el_sz
        -> let (cur1,nw) = f cur (bvextract' (el_sz-off-size) size (select a (constOff idx)))
           in (cur1,acc { staticAccPos = InArray { inArrayBefore = before
                                                 , inArrayAfter = after
                                                 , inArrayBound = b
                                                 , inArrayIdx = idx
                                                 , inArrayPos = Just (off+size,el_sz,
                                                                      store a (constOff idx)
                                                                      (bvconcat
                                                                       (bvextract' (el_sz-off) off (select a (constOff idx)))
                                                                       (bvconcat nw
                                                                        (bvextract' 0 (el_sz-size) (select a (constOff idx))))))
                                                 } })
      | otherwise
        -> let (cur1,nw) = f cur (bvextract' 0 (el_sz-off) (select a (constOff idx)))
           in staticAccChew f cur1 (size-el_sz+off)
              (acc { staticAccPos = InArray { inArrayBefore = (store a (constOff idx)
                                                               (bvconcat (bvextract' off (el_sz-off) (select a (constOff idx)))
                                                                nw)):before
                                            , inArrayAfter = after
                                            , inArrayBound = b
                                            , inArrayIdx = idx
                                            , inArrayPos = Nothing } })

defaultOffsetSize :: Integer
defaultOffsetSize = 64

toOff :: SMTExpr (BitVector BVUntyped) -> SMTExpr (BitVector BVUntyped)
toOff expr = case compare w defaultOffsetSize of
  EQ -> expr
  LT -> bvconcat (constantAnn (BitVector 0) (defaultOffsetSize-w)
                  ::SMTExpr (BitVector BVUntyped)) expr
  where
    w = extractAnnotation expr

offsetAdd :: Offset -> Offset -> Offset
offsetAdd off1 off2
  = Offset { staticOffset = (staticOffset off1) + (staticOffset off2)
           , dynamicOffset = Map.unionWith bvadd (dynamicOffset off1) (dynamicOffset off2)
           }

offsetSize :: Offset -> Either Integer (SMTExpr (BitVector BVUntyped))
offsetSize off
  | Map.null (dynamicOffset off) = Left $ staticOffset off
  | otherwise = Right $ if staticOffset off == 0
                        then dynOff
                        else bvadd (constOff (staticOffset off)) dynOff
  where
    dynOff = foldl1 bvadd [ if off==1
                            then cnt
                            else bvmul (constOff off) cnt
                          | (off,cnt) <- Map.toList (dynamicOffset off) ]

offsetOverflows :: RiverObject -> Offset -> Integer -> Either Bool (SMTExpr Bool)
offsetOverflows obj off len = case (objSize,offSize) of
  (Left objSize',Left offSize') -> Left $ objSize' < offSize'
  _ -> Right $ bvult dynObjSize dynOffSize
  where
    offSize = offsetSize off'
    objSize = objectSize obj
    dynOffSize = case offSize of
      Left x -> constOff x
      Right x -> x
    dynObjSize = case objSize of
      Left x -> constOff x
      Right x -> x
    off' = off { staticOffset = (staticOffset off) + (len `div` 8) }

offsetCompare :: Offset -> Offset -> Either Bool (SMTExpr Bool)
offsetCompare off1 off2 = case (sz1,sz2) of
  (Left s1,Left s2) -> Left $ s1==s2
  _ -> Right $ sz1' .==. sz2'
  where
    sz1 = offsetSize off1
    sz2 = offsetSize off2
    sz1' = case sz1 of
      Left s -> constOff s
      Right s -> s
    sz2' = case sz2 of
      Left s -> constOff s
      Right s -> s

disassembleStaticObjects :: [StaticObject] -> [SMTExpr (BitVector BVUntyped)]
disassembleStaticObjects = concat . fmap disassembleStaticObject

disassembleStaticObject :: StaticObject -> [SMTExpr (BitVector BVUntyped)]
disassembleStaticObject (StaticWord w) = [w]
disassembleStaticObject (StaticArray arrs b)
  = [ select arr (constantAnn (BitVector i) defaultOffsetSize)
    | i <- [0..(b-1)]
    , arr <- arrs ]

assembleStaticObjects :: [StaticObject] -> [(Bool,SMTExpr (BitVector BVUntyped))] -> [StaticObject]
assembleStaticObjects [] [] = []
assembleStaticObjects (obj:objs) xs
  = nobj:assembleStaticObjects objs nxs
  where
    (nobj,nxs) = assembleStaticObject obj xs

assembleStaticObject :: StaticObject -> [(Bool,SMTExpr (BitVector BVUntyped))] -> (StaticObject,[(Bool,SMTExpr (BitVector BVUntyped))])
assembleStaticObject (StaticWord w) xs
  = (StaticWord (if ch then w' else w),rest)
  where
    (ch,w',rest) = assembleWord (extractAnnotation w) xs
assembleStaticObject (StaticArray arr b) xs
  = (StaticArray narr b,rest)
  where
    (narr,rest) = assembleArr arr [0..(b-1)] xs
    
    assembleArr arrs [] rest = (arrs,rest)
    assembleArr arrs (i:is) xs
      = let (narrs,nxs) = assembleCell arrs i xs
        in assembleArr narrs is nxs
    assembleCell (arr:arrs) i xs
      = let (_,el_sz) = extractAnnotation arr
            (ch,w,nxs) = assembleWord el_sz xs
            narr = if ch
                   then store arr (constantAnn (BitVector i) defaultOffsetSize) w
                   else arr
            (narrs,rest) = assembleCell arrs i nxs
        in (narr:narrs,rest)
    assembleCell [] _ xs = ([],xs)

assembleWord :: Integer -> [(Bool,SMTExpr (BitVector BVUntyped))]
                -> (Bool,SMTExpr (BitVector BVUntyped),[(Bool,SMTExpr (BitVector BVUntyped))])
assembleWord len ((ch,w):ws)
  = case compare len len_w of
  EQ -> (ch,w,ws)
  GT -> let (ch',w',ws') = assembleWord (len-len_w) ws
        in (ch||ch',bvconcat w w',ws')
  LT -> (ch,bvextract' (len_w-len) len w,(ch,bvextract' 0 (len_w-len) w):ws)
  where
    len_w = extractAnnotation w

splitStatic :: Integer -- ^ Split offset in bits
               -> [SMTExpr (BitVector BVUntyped)]
               -> ([SMTExpr (BitVector BVUntyped)],
                   [SMTExpr (BitVector BVUntyped)])
splitStatic 0 xs = ([],xs)
splitStatic n (x:xs) = case compare n len_x of
  EQ -> ([x],xs)
  GT -> let (s1,s2) = splitStatic (n-len_x) xs
        in (x:s1,s2)
  LT -> ([bvextract' (len_x-n) n x],(bvextract' 0 (len_x-n) x):xs)
  where
    len_x = extractAnnotation x

constOff :: Integer -> SMTExpr (BitVector BVUntyped)
constOff n = constantAnn (BitVector n) defaultOffsetSize

accessObject :: Offset -> Integer
             -> (SMTExpr (BitVector BVUntyped) -> (a,SMTExpr (BitVector BVUntyped)))
             -> (SMTExpr Bool -> a -> a -> a)
             -> RiverObject
             -> (a,RiverObject)
accessObject off len f comb (StaticObj objs)
  = let dis = disassembleStaticObjects objs
        (res,ndis) = access off len f comb dis
        nobjs = assembleStaticObjects objs ndis
    in (res,StaticObj nobjs)
accessObject off len f comb (DynamicObj obj)
  = let (res,narr) = accessArray off len f comb (dynamicArrayObj obj)
    in (res,DynamicObj $ obj { dynamicArrayObj = narr })

accessArray :: Offset -> Integer
            -> (SMTExpr (BitVector BVUntyped) -> (a,SMTExpr (BitVector BVUntyped)))
            -> (SMTExpr Bool -> a -> a -> a)
            -> [SMTExpr (SMTArray (SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped))]
            -> (a,[SMTExpr (SMTArray (SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped))])
accessArray off len f comb arrs
  = (res,narrs)
  where
    el_sz = (sum $ fmap (snd.extractAnnotation) arrs) `div` 8
    (static_idx,static_off) = (staticOffset off) `divMod` el_sz
    static_idx' = if static_idx==0
                  then []
                  else [constOff static_idx]
    (good_idx,bad_idx) = Map.mapEitherWithKey
                         (\off cnt -> case off `mod` el_sz of
                             0 -> case off `div` el_sz of
                               1 -> Left cnt
                               n -> Left $ cnt `bvmul` (constOff n)
                             n -> Right (cnt `bvmul` (constOff off))
                         ) (dynamicOffset off)
    good_idx' = Map.elems good_idx
    (bad_idx',rest_idx) = if Map.null bad_idx
                          then ([],Map.empty)
                          else (let sum = foldl1 bvadd (Map.elems bad_idx)
                                in ([sum `bvudiv` (constOff el_sz)],
                                    Map.singleton 1 (sum `bvurem` (constOff el_sz))))
    res_idx = case static_idx'++good_idx'++bad_idx' of
      [] -> constOff 0
      xs -> foldl1 bvadd xs
    obj_count = ((len + (static_off*8)) `div` (el_sz*8))+
                (if Map.null rest_idx
                 then 0
                 else 1)
    obj = [ select arr (if i==0
                        then res_idx
                        else bvadd res_idx (constOff i))
          | i <- [0..obj_count]
          , arr <- arrs ]
    (res,nobj) = access (Offset { staticOffset = static_off
                                , dynamicOffset = rest_idx }) len
                 f comb obj
    narrs = assembleDynArray arrs res_idx obj_count nobj

assembleDynArray :: [SMTExpr (SMTArray (SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped))]
                 -> SMTExpr (BitVector BVUntyped)
                 -> Integer
                 -> [(Bool,SMTExpr (BitVector BVUntyped))]
                 -> [SMTExpr (SMTArray (SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped))]
assembleDynArray arrs idx count xs = arrs'
  where
    (arrs',[]) = assemble arrs 0 xs
    
    assemble arrs n xs = if n>count
                         then (arrs,xs)
                         else (let (narrs,xs') = assemble' (if n==0
                                                            then idx
                                                            else bvadd idx (constOff n)
                                                           ) arrs xs
                               in assemble narrs (n+1) xs')
    
    assemble' _ [] xs = ([],xs)
    assemble' idx (arr:arrs) xs = let (_,el_sz) = extractAnnotation arr
                                      (ch,w,xs') = assembleWord el_sz xs
                                      (arrs',rest) = assemble' idx arrs xs'
                                      arr' = if ch
                                             then store arr idx w
                                             else arr
                                  in (arr':arrs',rest)

access :: Offset -> Integer
          -> (SMTExpr (BitVector BVUntyped) -> (a,SMTExpr (BitVector BVUntyped)))
          -> (SMTExpr Bool -> a -> a -> a)
          -> [SMTExpr (BitVector BVUntyped)]
          -> (a,[(Bool,SMTExpr (BitVector BVUntyped))])
access off len f comb xs
  = trace ("access "++show off) $ (res,(fmap (\x -> (False,x)) before)++nafter)
  where
    (res,nafter) = accessDynamic (dynamicOffset off) len f comb after
    (before,after) = splitStatic (staticOffset off*8) xs

accessDynamic :: Map Integer (SMTExpr (BitVector BVUntyped))
              -> Integer
              -> (SMTExpr (BitVector BVUntyped) -> (a,SMTExpr (BitVector BVUntyped)))
              -> (SMTExpr Bool -> a -> a -> a)
              -> [SMTExpr (BitVector BVUntyped)]
              -> (a,[(Bool,SMTExpr (BitVector BVUntyped))])
accessDynamic offs len f comb xs
  = accessDynamic' (Map.toDescList offs) (fmap (\x -> (False,x)) xs)
  where
    accessDynamic' [] xs = accessHere len f xs
    accessDynamic' ((off,cnt):offs) xs
      -- Compute the maximum for cnt
      = let total = ((sum $ fmap ((`div` 8).extractAnnotation.snd) xs) - (len `div` 8)) `div` off
        in accessDynamic'' off offs cnt [0..total] xs
    accessDynamic'' _ offs _ [_] xs = accessDynamic' offs xs
    accessDynamic'' off offs cnt (i:is) xs
      = let cond = cnt .==. (constantAnn (BitVector i) defaultOffsetSize)
            (res_here,xs_here) = accessDynamic' offs xs
            (ch,w,xs') = assembleWord (off*8) xs
            (res_nhere,xs_nhere) = accessDynamic'' off offs cnt is xs'
            xs_nhere' = (ch,w):xs_nhere
        in (comb cond res_here res_nhere,
            mergeChanges cond xs_here xs_nhere')

accessHere :: Integer
           -> (SMTExpr (BitVector BVUntyped) -> (a,SMTExpr (BitVector BVUntyped)))
           -> [(Bool,SMTExpr (BitVector BVUntyped))]
           -> (a,[(Bool,SMTExpr (BitVector BVUntyped))])
accessHere len f xs
  = (res,(True,w'):xs'')
  where
    (res,w') = f w
    (_,w,xs'') = assembleWord len xs

mergeChanges :: SMTExpr Bool
             -> [(Bool,SMTExpr (BitVector BVUntyped))]
             -> [(Bool,SMTExpr (BitVector BVUntyped))]
             -> [(Bool,SMTExpr (BitVector BVUntyped))]
mergeChanges _ [] [] = []
mergeChanges cond ((chx,x):xs) ((chy,y):ys)
  = case compare len_x len_y of
  EQ -> (chx||chy,if chx||chy
                  then ite cond x y
                  else x):
        mergeChanges cond xs ys
  LT -> (chx||chy,if chx||chy
                  then ite cond x
                       (bvextract' (len_y-len_x) len_x y)
                  else x):
        mergeChanges cond xs ((chy,bvextract' 0 (len_y-len_x) y):ys)
  GT -> (chx||chy,if chx||chy
                  then ite cond
                       (bvextract' (len_x-len_y) len_y x) y
                  else y):
        mergeChanges cond ((chx,bvextract' 0 (len_x-len_y) x):xs) ys
  where
    len_x = extractAnnotation x
    len_y = extractAnnotation y

objectSize :: RiverObject -> Either Integer (SMTExpr (BitVector BVUntyped))
objectSize (StaticObj obj) = Left $ staticObjectSize obj
objectSize (DynamicObj dyn) = Right $ dynamicObjectSize dyn

staticObjectSize :: [StaticObject] -> Integer
staticObjectSize = (`div` 8) . sum . fmap objSize
  where
    objSize (StaticWord w) = extractAnnotation w
    objSize (StaticArray arrs b)
      = (sum $ fmap (snd . extractAnnotation) arrs)*b

dynamicObjectSize :: DynamicObject -> SMTExpr (BitVector BVUntyped)
dynamicObjectSize dyn
  = if el_size==1
    then dynamicArrayBound dyn
    else bvmul (dynamicArrayBound dyn) (constOff el_size)
  where
    el_size = (sum $ fmap (snd . extractAnnotation) (dynamicArrayObj dyn))
              `div` 8

objectITE :: SMTExpr Bool -> RiverObject -> RiverObject -> RiverObject
objectITE cond (StaticObj objs1) (StaticObj objs2)
  = StaticObj (zipWith comb objs1 objs2)
  where
    comb (StaticWord w1) (StaticWord w2)
      = StaticWord (if w1==w2
                    then w1
                    else ite cond w1 w2)
    comb (StaticArray arr1 b1) (StaticArray arr2 b2)
      = StaticArray (zipWith (\a1 a2 -> if a1==a2
                                        then a1
                                        else ite cond a1 a2
                             ) arr1 arr2) b1
objectITE cond (DynamicObj (DynamicArray arr1 b1)) (DynamicObj (DynamicArray arr2 b2))
  = DynamicObj (DynamicArray (zipWith (\a1 a2 -> if a1==a2
                                                 then a1
                                                 else ite cond a1 a2
                                      ) arr1 arr2)
                (if b1==b2
                 then b1
                 else ite cond b1 b2))

objectEq :: RiverObject -> RiverObject -> SMTExpr Bool
objectEq (StaticObj objs1) (StaticObj objs2)
  = app and' (zipWith comb objs1 objs2)
  where
    comb (StaticWord w1) (StaticWord w2) = w1 .==. w2
    comb (StaticArray arr1 _) (StaticArray arr2 _)
      = app and' (zipWith (.==.) arr1 arr2)
objectEq (DynamicObj (DynamicArray arr1 b1)) (DynamicObj (DynamicArray arr2 b2))
  = app and' ((zipWith (.==.) arr1 arr2)++
              [b1 .==. b2])

objectSkel :: RiverObject -> SMT RiverObject
objectSkel (StaticObj objs) = do
  nobjs <- mapM (\obj -> case obj of
                    StaticWord w -> do
                      v <- varAnn (extractAnnotation w)
                      return $ StaticWord v
                    StaticArray arrs b -> do
                      arrs' <- mapM (\arr -> varAnn (extractAnnotation arr)) arrs
                      return (StaticArray arrs' b)
                ) objs
  return $ StaticObj nobjs
objectSkel (DynamicObj (DynamicArray arrs b)) = do
  narrs <- mapM (\arr -> varAnn (extractAnnotation arr)
                ) arrs
  nb <- varAnn (extractAnnotation b)
  return (DynamicObj (DynamicArray narrs nb))

debugStaticObject :: StaticObject -> SMT String
debugStaticObject (StaticWord w) = do
  BitVector v <- getValue w
  return (show v)
debugStaticObject (StaticArray arrs b) = do
  els <- mapM (\i
               -> debugStaticObjects
                  (fmap (\arr -> StaticWord (select arr (constantAnn (BitVector i)
                                                         defaultOffsetSize))
                        ) arrs)
              ) [0..(b-1)]
  return $ "["++intercalate "," els++"]"

debugStaticObjects :: [StaticObject] -> SMT String
debugStaticObjects objs = do
  strs <- mapM debugStaticObject objs
  case strs of
    [str] -> return str
    _ -> return $ "{"++intercalate " # " strs++"}"

debugDynamicObject :: DynamicObject -> SMT String
debugDynamicObject (DynamicArray arrs b) = do
  BitVector rb <- getValue b
  debugStaticObject (StaticArray arrs rb)

debugObject :: RiverObject -> SMT String
debugObject (StaticObj objs) = debugStaticObjects objs
debugObject (DynamicObj obj) = debugDynamicObject obj

{-
test :: SMT ()
test = do
  arr <- varAnn (defaultOffsetSize,16)
  let arr1 = store arr (constantAnn (BitVector 1) defaultOffsetSize) (constantAnn (BitVector 67) 16)
      arr2 = store arr1 (constantAnn (BitVector 2) defaultOffsetSize) (constantAnn (BitVector 22) 16)
      arr3 = store arr2 (constantAnn (BitVector 0) defaultOffsetSize) (constantAnn (BitVector 19) 16)
  arr' <- defConst arr3
  let obj = [StaticWord (constantAnn (BitVector 17) 32)
            ,StaticArray [arr'] 3]
      dis = disassembleStaticObjects obj
      off1 = Offset { staticOffset = 12
                    , dynamicOffset = Map.empty }
      off2 = Offset { staticOffset = 2
                    , dynamicOffset = Map.singleton 2 (constantAnn (BitVector 1) defaultOffsetSize) }
      (load,ndis) = access off2 16 (\x -> (x,bvmul x (constantAnn (BitVector 2) 16))) ite dis
      nobj = assembleStaticObjects obj ndis
  checkSat
  debugStaticObjects obj >>= liftIO.putStrLn
  getValue load >>= liftIO.print
  debugStaticObjects nobj >>= liftIO.putStrLn
-}
