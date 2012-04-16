{-# LANGUAGE TypeFamilies,DeriveDataTypeable #-}
module MemoryModel.UntypedBlocks where

import MemoryModel
import Language.SMTLib2
import Language.SMTLib2.Internals
import LLVM.Core (TypeDesc(..))
import Data.Word
import Data.Typeable
import Data.List (genericSplitAt)
import qualified Data.Bitstream as BitS
import Numeric (showHex)

type PtrT = Word64

data UntypedBlockMemory = UntypedBlockMemory
    { memoryBlocks :: SMTExpr (SMTArray (SMTExpr PtrT,SMTExpr PtrT) BitVector)
    , memoryBlockSizes :: SMTExpr (SMTArray (SMTExpr PtrT) PtrT)
    , memoryNextFree :: SMTExpr PtrT
    } deriving (Eq,Typeable)

instance Args UntypedBlockMemory where
    type ArgAnnotation UntypedBlockMemory = [TypeDesc]
    foldExprs f s mem _ = let (s1,blocks) = f s (memoryBlocks mem) (((),()),8)
                              (s2,next) = f s1 (memoryNextFree mem) ()
                              (s3,sizes) = f s2 (memoryBlockSizes mem) ((),())
                          in (s3,UntypedBlockMemory { memoryBlocks = blocks
                                                    , memoryBlockSizes = sizes
                                                    , memoryNextFree = next })

data UntypedPointer = UntypedPointer
    { pointerBlock :: SMTExpr PtrT
    , pointerOffset :: SMTExpr PtrT
    } deriving (Eq,Typeable)

instance Args UntypedPointer where
    type ArgAnnotation UntypedPointer = TypeDesc
    foldExprs f s ptr _ = let (s1,nblock) = f s (pointerBlock ptr) ()
                              (s2,noff) = f s1 (pointerOffset ptr) ()
                          in (s2,UntypedPointer nblock noff)

instance MemoryModel UntypedBlockMemory where
    type Pointer UntypedBlockMemory = UntypedPointer
    memInit mem = (memoryNextFree mem) .==. (constant 0)
    memAlloc tp mem = (UntypedPointer { pointerBlock = (memoryNextFree mem)
                                      , pointerOffset = 0 }
                      ,mem { memoryNextFree = (memoryNextFree mem) + 1 
                           , memoryBlockSizes = store (memoryBlockSizes mem) (memoryNextFree mem) (constant $ fromIntegral $ typeWidth tp)
                           })
    memLoad tp ptr mem = let w = typeWidth tp
                         in if w==1
                            then select (memoryBlocks mem) (pointerBlock ptr,pointerOffset ptr)
                            else bvconcats [ select (memoryBlocks mem) (pointerBlock ptr,if i==0
                                                                                         then pointerOffset ptr
                                                                                         else pointerOffset ptr + (constant $ fromIntegral i))
                                             | i <- [0..(w-1)] ]
    memStore tp ptr val mem = let w = typeWidth tp
                              in mem { memoryBlocks = if w==1
                                                      then store (memoryBlocks mem) (pointerBlock ptr,pointerOffset ptr) val
                                                      else letAnn (fromIntegral w) val 
                                                           $ \val' -> foldl (\cmem (blk,off) -> store cmem (pointerBlock ptr,if off==0
                                                                                                                             then pointerOffset ptr
                                                                                                                             else pointerOffset ptr + (constant $ fromIntegral off)) blk)
                                                                      (memoryBlocks mem) 
                                                                      [ (bvextract ((i+1)*8 - 1) (i*8) val',w-i-1) | i <- [0..(w-1)] ] }
    memCast _ tp ptr = ptr
    memIndex _ tp idx ptr = ptr { pointerOffset = pointerOffset ptr + (constant $ fromIntegral $ getOffset typeWidth tp idx) }
    memEq mem1 mem2 = and' [ memoryBlocks mem1 .==. memoryBlocks mem2
                           , memoryBlockSizes mem1 .==. memoryBlockSizes mem2
                           , memoryNextFree mem1 .==. memoryNextFree mem2 ]
    memPtrEq _ p1 p2 = and' [pointerBlock p1 .==. pointerBlock p2
                            ,pointerOffset p1 .==. pointerOffset p2]
    memPtrSwitch mem [(ptr,_)] = ptr
    memPtrSwitch mem ((ptr,cond):rest) = let ptr' = memPtrSwitch mem rest
                                         in UntypedPointer { pointerBlock = ite cond (pointerBlock ptr) (pointerBlock ptr')
                                                           , pointerOffset = ite cond (pointerOffset ptr) (pointerOffset ptr')
                                                           }
    memSet len val ptr mem = foldl (\cmem i -> cmem { memoryBlocks = store (memoryBlocks cmem) (pointerBlock ptr,if i==0
                                                                                                                 then pointerOffset ptr
                                                                                                                 else (pointerOffset ptr) + (constant $ fromIntegral i)) val
                                                    }) mem [0..(len-1)]
    memCopy len ptr_to ptr_from mem = foldl (\cmem i -> cmem { memoryBlocks = store (memoryBlocks cmem) 
                                                                              (pointerBlock ptr_to,if i==0
                                                                                                   then pointerOffset ptr_to
                                                                                                   else (pointerOffset ptr_to) + (constant $ fromIntegral i))
                                                                              (select (memoryBlocks cmem) (pointerBlock ptr_from,if i==0
                                                                                                                                 then pointerOffset ptr_from
                                                                                                                                 else (pointerOffset ptr_from) + (constant $ fromIntegral i)))
                                                             }) mem [0..(len-1)]
    memDump mem = do
      nxt <- getValue (memoryNextFree mem)
      if nxt > 0
         then mapM (\i -> do
                       blksz <- getValue' () (select (memoryBlockSizes mem) (constant $ fromIntegral i))
                       mapM (\j -> do
                                wrd <- getValue' 8 (select (memoryBlocks mem) (constant $ fromIntegral i,constant $ fromIntegral j))
                                let res = BitS.toBits wrd :: Word8
                                return $ ((if res < 16 then showChar '0' else id) . showHex res) ""
                            ) [0..(blksz-1)] >>= return.unwords
                   ) [0..(nxt-1)] >>= return.unlines
        else return ""