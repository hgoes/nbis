module Realization where

import MemoryModel
import Value
import Analyzation
import ConditionList
import TypeDesc
import InstrDesc

import Language.SMTLib2
import Control.Monad
import Control.Monad.RWS
import Data.Map as Map
import Data.Foldable as F
import Foreign.Ptr

import LLVM.FFI.Value
import LLVM.FFI.Instruction (Instruction,ICmpOp(..))
import LLVM.FFI.BasicBlock
import LLVM.FFI.Constant

type Watchpoint = (String,SMTExpr Bool,[(TypeDesc,SMTExpr (BitVector BVUntyped))])

type Guard = (ErrorDesc,SMTExpr Bool)

data RealizationEnv ptr
  = RealizationEnv { reFunction :: String
                   , reBlock :: Ptr BasicBlock
                   , reSubblock :: Integer
                   , reActivation :: SMTExpr Bool
                   , reGlobals :: Map (Ptr GlobalVariable) ptr
                   , reArgs :: Map (Ptr Argument) (Val ptr)
                   , rePhis :: Map (Ptr BasicBlock) (SMTExpr Bool)
                   }

data RealizationState ptr 
  = RealizationState { reLocals :: Map (Ptr Instruction) (Val ptr)
                     , reNextPtr :: ptr
                     }

data RealizationOutput ptr
  = RealizationOutput { reWatchpoints :: [Watchpoint]
                      , reGuards :: [Guard]
                      , reMemInstrs :: [MemoryInstruction ptr]
                      }

instance Monoid (RealizationOutput ptr) where
  mempty = RealizationOutput { reWatchpoints = mempty
                             , reGuards = mempty
                             , reMemInstrs = mempty
                             }
  mappend o1 o2 = RealizationOutput { reWatchpoints = (reWatchpoints o1) `mappend` (reWatchpoints o2)
                                    , reGuards = (reGuards o1) `mappend` (reGuards o2)
                                    , reMemInstrs = (reMemInstrs o1) `mappend` (reMemInstrs o2)
                                    }

type Realization ptr = RWST (RealizationEnv ptr) (RealizationOutput ptr) (RealizationState ptr) SMT

data BlockFinalization mem = Jump (ConditionList (Ptr BasicBlock,Integer))
                           | Return (Maybe (Val mem))
                           | Call String [Val mem] (Ptr Instruction)
                           deriving (Show)

reError :: String -> Realization ptr a
reError msg = do
  re <- ask
  return $ error $ "Error while realizing "++
    (reFunction re)++"."++
    (show $ reBlock re)++"."++
    (show $ reSubblock re)++": "++
    msg

reEnvError :: String -> Realization ptr a
reEnvError msg = do
  re <- ask
  rs <- get
  reError $ msg ++ show (Map.keys $ reLocals rs)
    ++ " " ++ show (Map.keys $ reArgs re)
    ++ " " ++ show (Map.keys $ reGlobals re)

rePutVar :: Ptr Instruction -> Val ptr -> Realization ptr ()
rePutVar name val = modify (\st -> st { reLocals = Map.insert name val (reLocals st) })

reNewPtr :: Enum ptr => Realization ptr ptr
reNewPtr = do
  rs <- get
  let ptr = reNextPtr rs
  put $ rs { reNextPtr = succ ptr }
  return ptr

reMemInstr :: MemoryInstruction ptr -> Realization ptr ()
reMemInstr instr = tell (mempty { reMemInstrs = [instr] })

argToExpr :: Enum ptr => Operand -> Realization ptr (Val ptr)
argToExpr expr = case operandDesc expr of
  ODNull -> do
    ptr <- reNewPtr
    let PointerType tp = operandType expr
    reMemInstr (MINull tp ptr)
    return $ PointerValue ptr
  ODInt v -> return $ ConstValue v (bitWidth (operandType expr))
  ODInstr instr _ _ -> do
    re <- get
    case Map.lookup instr (reLocals re) of
      Nothing -> reEnvError $ "Couldn't find local variable "++show instr
      Just res -> return res
  ODGlobal g -> do
    re <- ask
    case Map.lookup g (reGlobals re) of
      Nothing -> reEnvError $ "Couldn't find global variable "++show g
      Just res -> return $ PointerValue res
  ODArgument arg -> do
    re <- ask
    case Map.lookup arg (reArgs re) of
      Nothing -> reEnvError $ "Couldn't find argument variable "++show arg
      Just res -> return res
  ODGetElementPtr ptr idx -> do
    PointerValue val_ptr <- argToExpr ptr
    val_idx <- mapM (\i -> do
                        i' <- argToExpr i 
                        return $ case i' of
                          ConstValue bv _ -> Left bv
                          DirectValue bv -> Right bv
                    ) idx
    ptr' <- reNewPtr
    reMemInstr (MIIndex val_idx val_ptr ptr')
    return $ PointerValue ptr'
  ODUndef -> return (ConstValue 0 (bitWidth (operandType expr)))
  _ -> reError $ "Implement argToExpr for "++show expr

realizeInstructions :: Enum ptr => [InstrDesc Operand] 
                       -> Realization ptr (BlockFinalization ptr)
realizeInstructions (instr:instrs) = do
  res <- realizeInstruction instr
  case res of
    Just fin -> return fin
    Nothing -> realizeInstructions instrs
realizeInstructions [] = reError $ "Block terminates prematurely"

realizeInstruction :: Enum ptr => InstrDesc Operand -> Realization ptr (Maybe (BlockFinalization ptr))
realizeInstruction (ITerminator (IRet e)) = do
  res <- argToExpr e
  return $ Just $ Return $ Just res
realizeInstruction (ITerminator IRetVoid) = return $ Just $ Return Nothing
realizeInstruction (ITerminator (IBr to)) = do
  re <- get
  return $ Just $ Jump (CondElse (to,0))
realizeInstruction (ITerminator (IBrCond cond ifT ifF)) = do
  cond' <- argToExpr cond
  case cond' of
    ConstCondition cond'' -> return $ Just $ Jump (CondElse 
                                                   (if cond''
                                                    then ifT
                                                    else ifF,0))
    _ -> return $ Just $ Jump $
         CondIf (ifT,0) (valCond cond') $
         CondElse (ifF,0)
realizeInstruction (ITerminator (ISwitch val def args)) = do
  val' <- argToExpr val
  args' <- mapM (\(cmp_v,to) -> do
                    cmp_v' <- argToExpr cmp_v
                    return (cmp_v',to)) args
  case val' of
    ConstValue v _ -> case [ to | (ConstValue v' _,to) <- args', v==v' ] of
      [] -> return $ Just $ Jump (CondElse (def,0))
      [to] -> return $ Just $ Jump (CondElse (to,0))
    _ -> do
      jumps <- foldrM (\(cmp_v,to) cond -> do
                          let res = valEq cmp_v val'
                          return (CondIf (to,0) res cond)
                      ) (CondElse (def,0)) args'
      return $ Just $ Jump jumps
realizeInstruction (IAssign trg name expr) = do
  let genName v = case name of
        Just name' -> "assign_"++name'
        Nothing -> "assign"++v
  rval <- case expr of
    IBinaryOperator op lhs rhs -> do
      lhs' <- argToExpr lhs
      rhs' <- argToExpr rhs
      lift $ valCopy (genName "BinOp") $ valBinOp op lhs' rhs'
    IICmp op lhs rhs -> case operandType lhs of
      PointerType _ -> do
        lhs' <- fmap asPointer $ argToExpr lhs
        rhs' <- fmap asPointer $ argToExpr rhs
        cond <- lift $ varNamed (genName "PtrCompare")
        reMemInstr (MICompare lhs' rhs' cond)
        case op of
          I_EQ -> return $ ConditionValue cond 1
          I_NE -> return $ ConditionValue (not' cond) 1
          _ -> reError $ "Comparing pointers using "++show op++
               " unsupported (only (in-)equality allowed)"
      _ -> do
        lhs' <- argToExpr lhs
        rhs' <- argToExpr rhs
        lift $ valCopy (genName "ICmp") $ valIntComp op lhs' rhs'
    IGetElementPtr ptr idx -> do
      PointerValue ptr' <- argToExpr ptr
      idx' <- mapM (\arg -> do
                      arg' <- argToExpr arg
                      return $ case arg' of
                        ConstValue bv _ -> Left bv
                        DirectValue bv -> Right bv
                  ) idx
      ptr'' <- reNewPtr
      reMemInstr (MIIndex idx' ptr' ptr'')
      return $ PointerValue ptr''
    IPhi args -> do
      nargs <- mapM (\(lbl,arg) -> do
                        arg' <- argToExpr arg
                        re <- ask
                        let Just phi_cond = Map.lookup lbl (rePhis re)
                        return (arg',phi_cond)
                    ) args
      case nargs of
        ((PointerValue _,_):_) -> do
          ptr <- reNewPtr
          reMemInstr (MISelect [ (cond,ptr') | (PointerValue ptr',cond) <- nargs ] ptr)
          return (PointerValue ptr)
        _ -> lift $ valCopy (genName "Phi") $ valSwitch nargs
    ILoad arg -> do
      PointerValue ptr <- argToExpr arg
      re <- get
      case operandType arg of
        PointerType (PointerType tp) -> do
          ptr2 <- reNewPtr
          reMemInstr (MILoadPtr ptr ptr2)
          return $ PointerValue ptr2
        PointerType tp -> do
          loadRes <- lift $ varNamedAnn (genName "LoadRes") ((typeWidth tp)*8)
          reMemInstr (MILoad ptr loadRes)
          return $ DirectValue loadRes
    IBitCast tp_to arg -> do
      PointerValue ptr <- argToExpr arg
      let PointerType tp_from = operandType arg
      ptr' <- reNewPtr
      reMemInstr (MICast tp_from tp_to ptr ptr')
      return $ PointerValue ptr'
    ISExt tp arg -> do
      arg' <- argToExpr arg
      case arg' of
        ConditionValue v w -> return $ ConditionValue v (bitWidth (operandType arg))
        _ -> let v = valValue arg'
                 w = bitWidth (operandType arg)
                 d = (bitWidth tp) - w
                 nv = bvconcat (ite (bvslt v (constantAnn (BitVector 0) w::SMTExpr (BitVector BVUntyped)))
                                (constantAnn (BitVector (-1)) d::SMTExpr (BitVector BVUntyped))
                                (constantAnn (BitVector 0) (fromIntegral d))) v
             in lift $ valCopy (genName "SExt") $ DirectValue nv
    ITrunc tp arg -> do
      let w = bitWidth tp
      arg' <- argToExpr arg
      case arg' of
        ConstValue bv _ -> return $ ConstValue bv w
        ConditionValue v _ -> return $ ConditionValue v w
        _ -> lift $ valCopy (genName "Trunc") $ DirectValue (bvextract' 0 w (valValue arg'))
    IZExt tp arg -> do
      arg' <- argToExpr arg
      case arg' of
        ConditionValue v w -> return $ ConditionValue v (bitWidth (operandType arg))
        _ -> let v = valValue arg'
                 d = (bitWidth tp) - (bitWidth (operandType arg))
                 nv = bvconcat (constantAnn (BitVector 0) d::SMTExpr (BitVector BVUntyped)) v
             in lift $ valCopy (genName "ZExt") $ DirectValue nv
    IAlloca tp sz -> do
      size' <- case sz of
        Nothing -> return (ConstValue 1 32)
        Just sz' -> argToExpr sz'
      let size'' = case size' of
            ConstValue bv _ -> Left bv
            DirectValue bv -> Right bv
      ptr <- reNewPtr
      reMemInstr (MIAlloc tp size'' ptr)
      return $ PointerValue ptr
    ISelect cond ifT ifF -> do
      condArg <- argToExpr cond
      ifTArg <- argToExpr ifT
      ifFArg <- argToExpr ifF
      let cond' = valCond condArg
      case (ifTArg,ifFArg) of
        (PointerValue ifT',PointerValue ifF') -> do
          ptr <- reNewPtr
          reMemInstr (MISelect [(cond',ifT'),(not' cond',ifF')] ptr)
          return $ PointerValue ptr
        (ifT',ifF') -> do
          lift $ valCopy (genName "Switch") $ valSwitch [(ifT',cond'),(ifF',not' cond')]
    IMalloc (Just tp) sz True -> do
      rsz <- argToExpr sz
      let size = case rsz of
            ConstValue bv _ -> Left bv
            DirectValue bv -> Right bv
      ptr <- reNewPtr
      reMemInstr (MIAlloc tp size ptr)
      return (PointerValue ptr)
    _ -> reEnvError $ "Unimplemented assign instruction: "++show expr
  rePutVar trg rval
  return Nothing
realizeInstruction (IStore val to) = do
  PointerValue ptr <- argToExpr to
  val' <- argToExpr val
  case (operandType val,val') of
    (PointerType tp,PointerValue ptr2) -> reMemInstr (MIStorePtr ptr2 ptr)
    (tp,_) -> reMemInstr (MIStore (valValue val') ptr)
  return Nothing
realizeInstruction (ITerminator (ICall trg f args)) = case operandDesc f of
  ODFunction rtp fn argtps -> do
    args' <- mapM (\arg -> do
                      arg' <- argToExpr arg
                      return (arg',operandType arg)) args
    case intrinsics fn of
      Just intr -> do
        intr trg args'
        re <- ask
        return $ Just $ Jump (CondElse (reBlock re,reSubblock re + 1))
      Nothing -> return $ Just $ Call fn (fmap fst args') trg
realizeInstruction instr = reError $ "Implement realizeInstruction for "++show instr

intrinsics :: Enum ptr => String -> Maybe (Ptr Instruction -> [(Val ptr,TypeDesc)] -> Realization ptr ())
intrinsics "llvm.memcpy.p0i8.p0i8.i64" = Just intr_memcpy
intrinsics "llvm.memcpy.p0i8.p0i8.i32" = Just intr_memcpy
intrinsics "llvm.memset.p0i8.i32" = Just intr_memset
intrinsics "llvm.memset.p0i8.i64" = Just intr_memset
intrinsics "nbis_restrict" = Just intr_restrict
intrinsics "nbis_assert" = Just intr_assert
intrinsics "nbis_nondet_i64" = Just (intr_nondet 64)
intrinsics "nbis_nondet_i32" = Just (intr_nondet 32)
intrinsics "nbis_nondet_i16" = Just (intr_nondet 16)
intrinsics "nbis_nondet_i8" = Just (intr_nondet 8)
intrinsics "nbis_nondet_u64" = Just (intr_nondet 64)
intrinsics "nbis_nondet_u32" = Just (intr_nondet 32)
intrinsics "nbis_nondet_u16" = Just (intr_nondet 16)
intrinsics "nbis_nondet_u8" = Just (intr_nondet 8)
intrinsics "nbis_watch" = Just intr_watch
intrinsics _ = Nothing

intr_memcpy _ [(PointerValue to,_),(PointerValue from,_),(len,_),_,_] = do
  let len' = case len of
        ConstValue l _ -> Left l
        DirectValue l -> Right l
  reMemInstr (MICopy len' from to)

intr_memset _ [(PointerValue dest,_),(val,_),(ConstValue len _,_),_,_] = do
  reError "memset not implemented"
  
intr_restrict _ [(val,_)] = do
  re <- ask
  lift $ comment " Restriction:"
  case val of
    ConditionValue val _ -> lift $ assert $ (reActivation re) .=>. val
    _ -> do
      let nval = valValue val
          sz = extractAnnotation nval
      lift $ assert $ (reActivation re) .=>. (not' $ nval .==. constantAnn (BitVector 0) sz)

intr_assert _ [(val,_)] = do
  re <- ask
  let nval = valValue val
      sz = extractAnnotation nval
      guard_cond = case val of
        ConstValue v w -> if v==0
                          then Just (reActivation re)
                          else Nothing
        ConditionValue val _ -> Just $ (reActivation re) .&&. (not' val)
        _ -> Just $ (reActivation re) .&&. (nval .==. constantAnn (BitVector 0) sz)
  case guard_cond of
    Just guard' -> tell $ mempty { reGuards = [(Custom,guard')] }
    Nothing -> return ()

intr_watch _ ((ConstValue bv _,_):exprs) = do
  re <- ask
  tell $ mempty { reWatchpoints = [(show bv,reActivation re,
                                    [ (tp,valValue val) 
                                    | (val,tp) <- exprs ])] }

intr_nondet width trg [] = do
  v <- lift $ varNamedAnn "nondetVar" width
  rePutVar trg (DirectValue v)
