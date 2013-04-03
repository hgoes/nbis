{-# LANGUAGE ScopedTypeVariables #-}
module InstrDesc where

import TypeDesc
import Foreign.Ptr
import LLVM.FFI.Value
import LLVM.FFI.Instruction
import LLVM.FFI.BasicBlock
import LLVM.FFI.User
import LLVM.FFI.OOP
import LLVM.FFI.Function
import LLVM.FFI.Type
import LLVM.FFI.Constant
import LLVM.FFI.APInt
import LLVM.FFI.Use

data InstrDesc a
  = IAssign (Ptr Instruction) (AssignDesc a)
  | IStore a a
  | ITerminator (TerminatorDesc a)
  deriving (Show,Eq,Ord)
    
data AssignDesc a
  = IBinaryOperator BinOpType a a
  | IFCmp FCmpOp a a
  | IICmp ICmpOp a a
  | IGetElementPtr a [a]
  | IPhi [(Ptr BasicBlock,a)]
  | ISelect a a a
  | ILoad a
  | IBitCast TypeDesc a
  | ISExt TypeDesc a
  | ITrunc TypeDesc a
  | IZExt TypeDesc a
  | IAlloca TypeDesc (Maybe a)
  deriving (Show,Eq,Ord)

data TerminatorDesc a
  = IRetVoid
  | IRet a
  | IBr (Ptr BasicBlock)
  | IBrCond a (Ptr BasicBlock) (Ptr BasicBlock)
  | ISwitch a (Ptr BasicBlock) [(a,Ptr BasicBlock)]
  | ICall (Ptr Instruction) a [a]
  deriving (Show,Eq,Ord)

data Operand = Operand { operandType :: TypeDesc
                       , operandDesc :: OperandDesc Operand
                       }
             deriving (Show,Eq,Ord)

data OperandDesc a
  = ODUndef
  | ODNull
  | ODInt Integer
  | ODInstr (Ptr Instruction) (Ptr BasicBlock)
  | ODFunction TypeDesc String [TypeDesc]
  | ODMetaData (Ptr MDNode)
  | ODGlobal (Ptr GlobalVariable)
  | ODArgument (Ptr Argument)
  deriving (Show,Eq,Ord)

reifyInstr :: Ptr Instruction -> IO (InstrDesc Operand)
reifyInstr ptr 
  = mkSwitch
    [fmap (\binop -> do
              opcode <- binOpGetOpCode binop
              op1 <- getOperand binop 0 >>= reifyOperand
              op2 <- getOperand binop 1 >>= reifyOperand
              return $ IAssign ptr $ IBinaryOperator opcode op1 op2
          ) (castDown ptr)
    ,fmap (\call -> do
              cobj <- callInstGetCalledValue call >>= reifyOperand
              nargs <- callInstGetNumArgOperands call
              args <- mapM (\i -> callInstGetArgOperand call i >>= reifyOperand) [0..(nargs-1)]
              return $ ITerminator $ ICall ptr cobj args
          ) (castDown ptr)
    ,fmap (\cmp -> do
              op <- getICmpOp cmp
              op1 <- getOperand cmp 0 >>= reifyOperand
              op2 <- getOperand cmp 1 >>= reifyOperand
              return $ IAssign ptr $ IICmp op op1 op2
          ) (castDown ptr)
    ,fmap (\br -> do
              isC <- branchInstIsConditional br
              if isC
                then (do
                         cond <- branchInstGetCondition br >>= reifyOperand
                         succ1 <- terminatorInstGetSuccessor br 0
                         succ2 <- terminatorInstGetSuccessor br 1
                         return $ ITerminator $ IBrCond cond succ1 succ2)
                else (do
                         succ <- terminatorInstGetSuccessor br 0
                         return $ ITerminator $ IBr succ)
          ) (castDown ptr)
    ,fmap (\ret -> do
              val <- returnInstGetReturnValue ret
              if val == nullPtr
                then return $ ITerminator $ IRetVoid
                else (do
                         val' <- reifyOperand val
                         return $ ITerminator $ IRet val')
          ) (castDown ptr)
    ,fmap (\phi -> do
              sz <- phiNodeGetNumIncomingValues phi
              blks <- mapM (\i -> do
                               val <- phiNodeGetIncomingValue phi i >>= reifyOperand
                               blk <- phiNodeGetIncomingBlock phi i
                               return (blk,val)
                           ) [0..(sz-1)]
              return $ IAssign ptr (IPhi blks)
          ) (castDown ptr)
    ,fmap (\store -> do
              val <- storeInstGetValueOperand store >>= reifyOperand
              ptr <- storeInstGetPointerOperand store >>= reifyOperand
              return $ IStore val ptr
          ) (castDown ptr)
    ,fmap (\load -> do
              op <- getOperand (load::Ptr LoadInst) 0 >>= reifyOperand
              return $ IAssign ptr (ILoad op)
          ) (castDown ptr)
    ,fmap (\gep -> do
              ptr' <- getElementPtrInstGetPointerOperand gep >>= reifyOperand
              begin <- getElementPtrInstIdxBegin gep
              end <- getElementPtrInstIdxEnd gep
              idx <- useToList begin end >>= mapM reifyOperand
              return $ IAssign ptr (IGetElementPtr ptr' idx)
          ) (castDown ptr)
    ,fmap (\zext -> do
              op <- getOperand (zext::Ptr ZExtInst) 0 >>= reifyOperand
              tp <- getType zext >>= reifyType
              return $ IAssign ptr (IZExt tp op)
          ) (castDown ptr)
    ,fmap (\trunc -> do
              op <- getOperand (trunc::Ptr TruncInst) 0 >>= reifyOperand
              tp <- getType trunc >>= reifyType
              return $ IAssign ptr (ITrunc tp op)
          ) (castDown ptr)
    ,fmap (\bcast -> do
              op <- getOperand (bcast::Ptr BitCastInst) 0 >>= reifyOperand
              tp <- getType bcast >>= reifyType
              return $ IAssign ptr (IBitCast tp op)
          ) (castDown ptr)
    ]
  where
    mkSwitch ((Just act):_) = act
    mkSwitch (Nothing:rest) = mkSwitch rest
    mkSwitch [] = do
      valueDump ptr
      error "Unknown instruction."

reifyOperand :: Ptr Value -> IO Operand
reifyOperand ptr = do
  tp <- valueGetType ptr
  rtp <- reifyType tp
  desc <- mkSwitch 
          [fmap (\i -> do
                    parent <- instructionGetParent i
                    return $ ODInstr i parent
                ) (castDown ptr)
          ,fmap (\f -> do
                    ftp <- functionGetFunctionType f
                    rtp <- functionTypeGetReturnType ftp >>= reifyType
                    nargs <- functionTypeGetNumParams ftp
                    args <- mapM (\i -> functionTypeGetParamType ftp i >>= reifyType) [0..(nargs-1)]
                    name <- getNameString f
                    return $ ODFunction rtp name args
                ) (castDown ptr)
          ,fmap (\md -> return $ ODMetaData md) (castDown ptr)
          ,fmap (\i -> do
                    v <- constantIntGetValue i
                    rv <- apIntGetSExtValue v
                    return $ ODInt $ fromIntegral rv) (castDown ptr)
          ,fmap (\gv -> return $ ODGlobal gv) (castDown ptr)
          ,fmap (\arg -> return $ ODArgument arg) (castDown ptr)
          ,fmap (\(null::Ptr ConstantPointerNull) -> return ODNull) (castDown ptr)
          ]
  return $ Operand { operandType = rtp
                   , operandDesc = desc
                   }
    where
      mkSwitch ((Just act):_) = act
      mkSwitch (Nothing:rest) = mkSwitch rest
      mkSwitch [] = do
        valueDump ptr
        error "Unknown operand"