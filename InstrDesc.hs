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
import LLVM.FFI.Pass
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Foldable
import Prelude hiding (foldl)

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
  | IMalloc (Ptr Instruction) (Maybe TypeDesc) a Bool
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
  | ODGetElementPtr a [a]
  deriving (Show,Eq,Ord)

reifyInstr :: Ptr TargetLibraryInfo
#if HS_LLVM_VERSION >= 303
              -> Ptr DataLayout
#else
              -> Ptr TargetData
#endif
              -> Ptr Instruction
              -> IO (InstrDesc Operand)
reifyInstr tl dl ptr
  = mkSwitch
    [fmap (\binop -> do
              opcode <- binOpGetOpCode binop
              op1 <- getOperand binop 0 >>= reifyOperand
              op2 <- getOperand binop 1 >>= reifyOperand
              return $ IAssign ptr $ IBinaryOperator opcode op1 op2
          ) (castDown ptr)
    ,fmap (\call -> do
#if HS_LLVM_VERSION >= 303
              isMalloc <- isMallocLikeFn call tl False
#else
              isMalloc <- isMallocLikeFn call
#endif
              if isMalloc
                then (do
#if HS_LLVM_VERSION >= 303
                         tp <- getMallocAllocatedType call tl
#else
                         tp <- getMallocAllocatedType call
#endif
                         rtp <- if tp==nullPtr
                                then return Nothing
                                else fmap Just (reifyType tp)
#if HS_LLVM_VERSION >= 303
                         sz <- getMallocArraySize call dl tl False
#else
                         sz <- getMallocArraySize call dl False
#endif
                         (rsz,c) <- if sz==nullPtr
                                    then (do
                                             x <- callInstGetArgOperand call 0 >>= reifyOperand
                                             return (x,False))
                                    else (do
                                             x <- reifyOperand sz
                                             return (x,True))
                         return $ ITerminator $ IMalloc ptr rtp rsz c)
                else (do
                         cobj <- callInstGetCalledValue call >>= reifyOperand
                         nargs <- callInstGetNumArgOperands call
                         args <- mapM (\i -> callInstGetArgOperand call i >>= reifyOperand) [0..(nargs-1)]
                         return $ ITerminator $ ICall ptr cobj args)
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
              --begin <- getElementPtrInstIdxBegin gep
              --end <- getElementPtrInstIdxEnd gep
              --idx <- useToList begin end >>= mapM reifyOperand
              sz <- getElementPtrInstGetNumIndices gep
              idx <- mapM (\i -> getOperand gep i >>= reifyOperand) [1..sz]
              --print sz
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
              PointerType tp <- getType bcast >>= reifyType
              return $ IAssign ptr (IBitCast tp op)
          ) (castDown ptr)
    ,fmap (\sel -> do
              cond <- selectInstGetCondition sel >>= reifyOperand
              ifT <- selectInstGetTrueValue sel >>= reifyOperand
              ifF <- selectInstGetFalseValue sel >>= reifyOperand
              return $ IAssign ptr (ISelect cond ifT ifF)
          ) (castDown ptr)
    ]
  where
    mkSwitch ((Just act):_) = act
    mkSwitch (Nothing:rest) = mkSwitch rest
    mkSwitch [] = do
      valueDump ptr
      error "Unknown instruction."

getInstrType :: Map String [TypeDesc] -> InstrDesc Operand -> TypeDesc
getInstrType structs (IAssign _ desc) = case desc of
  IBinaryOperator _ l _ -> operandType l
  IFCmp _ _ _ -> IntegerType 1
  IICmp _ _ _ -> IntegerType 1
  IGetElementPtr ptr idx -> let PointerType tp = operandType ptr
                            in indexType structs tp [ case operandDesc i of
                                                         ODInt x -> Left x
                                                         _ -> Right ()
                                                    | i <- idx ]
  IPhi ((_,op):_) -> operandType op
  ISelect _ arg _ -> operandType arg
  ILoad ptr -> let PointerType tp = operandType ptr
               in tp
  IBitCast to _ -> to
  ISExt to _ -> to
  ITrunc to _ -> to
  IZExt to _ -> to
  IAlloca tp _ -> PointerType tp
getInstrType _ (IStore _ _) = VoidType
getInstrType _ (ITerminator desc) = case desc of
  ICall _ f _ -> case operandType f of
    PointerType (FunctionType rtp _ _) -> rtp
    tp -> error $ "Invalid type for call argument: "++show tp
  IMalloc _ (Just tp) _ _ -> PointerType tp
  _ -> VoidType

getInstrTarget :: InstrDesc Operand -> Maybe (Ptr Instruction)
getInstrTarget (IAssign x _) = Just x
getInstrTarget (ITerminator desc) = case desc of
  ICall trg _ _ -> Just trg
  IMalloc trg _ _ _ -> Just trg
  _ -> Nothing
getInstrTarget (IStore _ _) = Nothing

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
          ,fmap (\expr -> do
                    opcode <- constantExprGetOpcode expr
                    case opcode of
                      MemoryOp GetElementPtr -> do
                        sz <- getNumOperands expr
                        ptr <- getOperand expr 0 >>= reifyOperand
                        idx <- mapM (\i -> getOperand expr i >>= reifyOperand) [1..(sz-1)]
                        return $ ODGetElementPtr ptr idx
                      _ -> do
                           valueDump expr
                           error "Unknown constant expr"
                ) (castDown ptr)
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

getInstrsDeps :: [InstrDesc Operand] -> Map (Ptr Instruction) TypeDesc
getInstrsDeps = snd . foldl (\(loc,mp) instr -> (case getInstrTarget instr of
                                                    Nothing -> loc
                                                    Just t -> Set.insert t loc,getInstrDeps loc mp instr)
                            ) (Set.empty,Map.empty)
  where
    getInstrDeps loc mp (IAssign _ expr) = case expr of
      IBinaryOperator _ l r -> getOperandDeps loc (getOperandDeps loc mp l) r
      IFCmp _ l r -> getOperandDeps loc (getOperandDeps loc mp l) r
      IICmp _ l r -> getOperandDeps loc (getOperandDeps loc mp l) r
      IGetElementPtr ptr idx -> getOperandDeps loc (foldl (getOperandDeps loc) mp idx) ptr
      IPhi phis -> foldl (\cmp (_,op) -> getOperandDeps loc cmp op) mp phis
      ISelect c t f -> getOperandDeps loc (getOperandDeps loc (getOperandDeps loc mp c) t) f
      ILoad ptr -> getOperandDeps loc mp ptr
      IBitCast _ op -> getOperandDeps loc mp op
      ISExt _ op -> getOperandDeps loc mp op
      ITrunc _ op -> getOperandDeps loc mp op
      IZExt _ op -> getOperandDeps loc mp op
      IAlloca _ sz -> case sz of
        Nothing -> mp
        Just sz' -> getOperandDeps loc mp sz'
    getInstrDeps loc mp (IStore val ptr) = getOperandDeps loc (getOperandDeps loc mp val) ptr
    getInstrDeps loc mp (ITerminator term) = case term of
      IBrCond cond _ _ -> getOperandDeps loc mp cond
      ISwitch val _ cases -> getOperandDeps loc (foldl (\cmp (c,_) -> getOperandDeps loc cmp c) mp cases) val
      ICall _ fun args -> getOperandDeps loc (foldl (getOperandDeps loc) mp args) fun
      IMalloc _ _ sz _ -> getOperandDeps loc mp sz
      _ -> mp

    getOperandDeps loc mp op = case operandDesc op of
      ODInstr instr _ -> if Set.member instr loc
                         then mp
                         else Map.insert instr (operandType op) mp
      ODGetElementPtr ptr idx -> getOperandDeps loc (foldl (getOperandDeps loc) mp idx) ptr
      _ -> mp