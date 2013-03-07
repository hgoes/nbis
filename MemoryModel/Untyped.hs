{-# LANGUAGE TypeFamilies,DeriveDataTypeable #-}
module MemoryModel.Untyped where

import MemoryModel
import Language.SMTLib2
import Language.SMTLib2.Internals
import LLVM.Core (TypeDesc(..))
import Data.Word
import Data.Typeable
import Data.List (genericSplitAt)
--import qualified Data.Bitstream as BitS
import Numeric (showHex)

type PtrT = BV64

data UntypedMemory = UntypedMemory
    { memoryBlocks :: SMTExpr (SMTArray (SMTExpr PtrT) (BitVector BVUntyped))
    , memoryNextFree :: SMTExpr PtrT
    } deriving (Eq,Typeable)

instance Args UntypedMemory where
    type ArgAnnotation UntypedMemory = [TypeDesc]
    foldExprs f s mem _ = let (s1,blocks) = f s (memoryBlocks mem) ((),8)
                              (s2,next) = f s1 (memoryNextFree mem) ()
                          in (s2,UntypedMemory { memoryBlocks = blocks
                                               , memoryNextFree = next })

bitWidth' :: TypeDesc -> Integer
bitWidth' (TDPtr _) = 64
bitWidth' tp = bitWidth tp

typeWidth' :: TypeDesc -> Integer
typeWidth' (TDPtr _) = 8
typeWidth' tp = typeWidth tp

newtype UntypedPointer = UntypedPointer { pointerLocation :: SMTExpr PtrT } deriving (Eq,Typeable)

instance Args UntypedPointer where
    type ArgAnnotation UntypedPointer = TypeDesc
    foldExprs f s ptr _ = let (s',ptr') = foldExprs f s (pointerLocation ptr) ()
                          in (s',UntypedPointer ptr')

instance MemoryModel UntypedMemory where
    type Pointer UntypedMemory = UntypedPointer
    memNew tps = argVarsAnn tps
    memInit mem = (memoryNextFree mem) .==. 0
    -- TODO: Constant init
    memAlloc tp _ cont mem = let w = typeWidth' tp
                             in return (UntypedPointer $ memoryNextFree mem,mem { memoryNextFree = (memoryNextFree mem) + (fromInteger w) })
    memLoad tp (UntypedPointer ptr) mem = let w = typeWidth' tp
                                          in (if w==1
                                              then select (memoryBlocks mem) ptr
                                              else foldl1 bvconcat [ select (memoryBlocks mem) (if i==0
                                                                                                then ptr
                                                                                                else ptr + (fromInteger i))
                                                                   | i <- [0..(w-1)] ],[])
    memStore tp (UntypedPointer ptr) val mem
      = let w = typeWidth' tp
        in (mem { memoryBlocks = if w==1
                                 then store (memoryBlocks mem) ptr val
                                 else letAnn (fromIntegral w) val 
                                      $ \val' -> foldl (\cmem (blk,off) -> store cmem (if off==0
                                                                                       then ptr
                                                                                       else ptr + (fromInteger off)) blk)
                                                 (memoryBlocks mem) 
                                                 [ (bvextract' (i*8) 8 val',w-i-1) | i <- [0..(w-1)] ] },[])
    memCast _ tp ptr = ptr
    memIndex _ tp idx (UntypedPointer ptr) = UntypedPointer $ case getOffset typeWidth' tp (fmap (\(Left i) -> i) idx) of
      0 -> ptr
      off' ->  ptr + (fromInteger off')
    memEq mem1 mem2 = (memoryBlocks mem1 .==. memoryBlocks mem2) .&&. (memoryNextFree mem1 .==. memoryNextFree mem2)
    memPtrEq _ (UntypedPointer p1) (UntypedPointer p2) = p1 .==. p2
    memCopy len (UntypedPointer p1) (UntypedPointer p2) mem
      = mem { memoryBlocks = foldl (\cmem i -> store cmem (if i==0
                                                           then p1
                                                           else p1 + fromInteger i) 
                                               (select (memoryBlocks mem) (if i==0
                                                                           then p2
                                                                           else p2 + fromInteger i))
                                   ) (memoryBlocks mem) [0..(len-1)]
            }
    memSet len val (UntypedPointer p) mem = mem { memoryBlocks = foldl (\cmem i -> store cmem (if i==0
                                                                                               then p
                                                                                               else p + fromInteger i) val)
                                                                 (memoryBlocks mem) [0..(len - 1)]
                                                }
    memPtrSwitch _ choices = return $ UntypedPointer (mkSwitch choices)
      where
        mkSwitch [(UntypedPointer ptr,_)] = ptr
        mkSwitch ((UntypedPointer ptr,cond):rest) = ite cond ptr (mkSwitch rest)
    memDump mem = do
      BitVector nxt <- getValue (memoryNextFree mem)
      if nxt > 0
        then (do
                 res <- mapM (\i -> getValue' 8 (select (memoryBlocks mem) (fromInteger i))) [0..(nxt-1)]
                 return $ unwords [ ((if r' < 16 then showChar '0' else id) . showHex r') "" 
                                  | BitVector r <- res, let r' = fromIntegral r :: Word8 ])
        else return "[]"
    memSwitch [(mem,_)] = return mem
    memSwitch conds = do
      nblocks <- varAnn ((),8)
      nfree <- var
      let (blocks,free) = mkSwitch conds
      assert $ nblocks .==. blocks
      assert $ nfree .==. free
      return $ UntypedMemory nblocks nfree
      where
        mkSwitch [(mem,_)] = (memoryBlocks mem,memoryNextFree mem)
        mkSwitch ((UntypedMemory mem free,cond):rest) = let (mem',free') = mkSwitch rest
                                                        in (ite cond mem mem',ite cond free free')