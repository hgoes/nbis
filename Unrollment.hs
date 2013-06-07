module Unrollment where

import Language.SMTLib2
import LLVM.FFI.BasicBlock
import LLVM.FFI.Instruction

import Value

import Data.Map as Map
import Foreign.Ptr

type BlockOrder = [Ptr BasicBlock]

data MergeNode ptr = MergeNode { mergeActivationProxy :: SMTExpr Bool
                               , mergeInputs :: Map (Ptr Instruction) (Either Val ptr)
                               }

data UnrollContext ptr = UnrollContext { unrollCtxFunction :: String
                                       , mergeNodes :: Map (Ptr BasicBlock) (MergeNode ptr)
                                       , realizationQueue :: [(Ptr BasicBlock,[(SMTExpr Bool,Map (Ptr Instruction) (Either Val ptr))])]
                                       , outgoingEdges :: [(Ptr BasicBlock,[(SMTExpr Bool,Map (Ptr Instruction) (Either Val ptr))])]
                                       }

