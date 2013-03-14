module Realization where

import MemoryModel
import Value
import Analyzation
import ConditionList

import Language.SMTLib2
import Control.Monad
import Control.Monad.RWS
import Data.Map as Map
import LLVM.Core
import Data.Foldable as F

type Watchpoint = (String,SMTExpr Bool,[(TypeDesc,SMTExpr (BitVector BVUntyped))])

type Guard = (ErrorDesc,SMTExpr Bool)

data RealizationEnv ptr
  = RealizationEnv { reFunction :: String
                   , reBlock :: String
                   , reSubblock :: Integer
                   , reActivation :: SMTExpr Bool
                   , reGlobals :: Map String ptr
                   , reArgs :: Map String (Val ptr)
                   , rePhis :: Map String (SMTExpr Bool)
                   , rePrediction :: Map String TypeDesc
                   }

data RealizationState ptr 
  = RealizationState { reLocals :: Map String (Val ptr)
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

data BlockFinalization mem = Jump (ConditionList (String,Integer))
                           | Return (Maybe (Val mem))
                           | Call String [Val mem] String
                           deriving (Show)

reError :: String -> Realization ptr a
reError msg = do
  re <- ask
  return $ error $ "Error while realizing "++
    (reFunction re)++"."++
    (reBlock re)++"."++
    (show $ reSubblock re)++": "++
    msg

reEnvError :: String -> Realization ptr a
reEnvError msg = do
  re <- ask
  rs <- get
  reError $ msg ++ show (Map.keys $ reLocals rs)
    ++ " " ++ show (Map.keys $ reArgs re)
    ++ " " ++ show (Map.keys $ reGlobals re)

reGetVar :: String -> Realization ptr (Val ptr)
reGetVar name = do
  re <- ask
  rs <- get
  case Map.lookup name (reLocals rs) of
    Just v -> return v
    Nothing -> case Map.lookup name (reArgs re) of
      Just v -> return v
      Nothing -> case Map.lookup name (reGlobals re) of
        Just v -> return (PointerValue v)
        Nothing -> reEnvError $ "Couldn't find "++show name

rePutVar :: String -> Val ptr -> Realization ptr ()
rePutVar name val = modify (\st -> st { reLocals = Map.insert name val (reLocals st) })

reNewPtr :: Enum ptr => Realization ptr ptr
reNewPtr = do
  rs <- get
  let ptr = reNextPtr rs
  put $ rs { reNextPtr = succ ptr }
  return ptr

reMemInstr :: MemoryInstruction ptr -> Realization ptr ()
reMemInstr instr = tell (mempty { reMemInstrs = [instr] })

argToExpr :: Enum ptr => Expr -> Realization ptr (Val ptr)
argToExpr expr = case exprDesc expr of
  EDNamed name -> reGetVar name
  EDNull -> do
    ptr <- reNewPtr
    reMemInstr (MINull (exprType expr) ptr)
    return $ PointerValue ptr
  EDICmp pred lhs rhs -> case exprType lhs of
    TDPtr _ -> do
      PointerValue lhs' <- argToExpr lhs
      PointerValue rhs' <- argToExpr rhs
      cond <- lift $ varNamed "ptrCompare"
      reMemInstr (MICompare lhs' rhs' cond)
      case pred of
        IntEQ -> return $ ConditionValue cond 1
        IntNE -> return $ ConditionValue (not' cond) 1
        _ -> reError $ "Comparing pointers using "++show pred++
             " unsupported (only (in-)equality allowed)"
    _ -> do
      lhs' <- argToExpr lhs
      rhs' <- argToExpr rhs
      return $ valIntComp pred lhs' rhs'
  EDInt v -> return $ ConstValue v (bitWidth (exprType expr))
  EDUnOp op arg -> do
    arg' <- argToExpr arg
    case op of
      UOZExt -> case arg' of
        ConditionValue v w -> return $ ConditionValue v (bitWidth (exprType expr))
        _ -> let v = valValue arg'
                 d = (bitWidth (exprType expr)) - (bitWidth (exprType arg))
                 nv = bvconcat (constantAnn (BitVector 0) d::SMTExpr (BitVector BVUntyped)) v
             in return $ DirectValue nv
      UOSExt -> case arg' of
        ConditionValue v w -> return $ ConditionValue v (bitWidth (exprType expr))
        _ -> let v = valValue arg'
                 w = bitWidth (exprType arg)
                 d = (bitWidth (exprType expr)) - w
                 nv = bvconcat (ite (bvslt v (constantAnn (BitVector 0) w::SMTExpr (BitVector BVUntyped)))
                                (constantAnn (BitVector (-1)) d::SMTExpr (BitVector BVUntyped))
                                (constantAnn (BitVector 0) (fromIntegral d))) v
             in return $ DirectValue nv
      UOTrunc -> let w = bitWidth (exprType expr)
                 in case arg' of
                   ConstValue bv _ -> return $ ConstValue bv w
                   ConditionValue v _ -> return $ ConditionValue v w
                   _ -> return $ DirectValue (bvextract' 0 w (valValue arg'))
      UOBitcast -> do
        let PointerValue ptr = arg'
            TDPtr tp_to = exprType expr
            TDPtr tp_from = exprType arg
        ptr' <- reNewPtr
        reMemInstr (MICast tp_from tp_to ptr ptr')
        return $ PointerValue ptr'
      _ -> reError $ "Implement argToExpr for "++show expr
  EDGetElementPtr expr' args -> do
    PointerValue ptr <- argToExpr expr'
    args' <- mapM (\arg -> do
                      arg' <- argToExpr arg
                      return $ case arg' of
                        ConstValue bv _ -> Left bv
                        DirectValue bv -> Right bv
                  ) args
    ptr' <- reNewPtr
    reMemInstr (MIIndex args' ptr ptr')
    return $ PointerValue ptr'
  EDBinOp op lhs rhs -> do
    lhs' <- argToExpr lhs
    rhs' <- argToExpr rhs
    return $ valBinOp op lhs' rhs'
  EDSelect val ifT ifF -> do
    val' <- argToExpr val
    ifT' <- argToExpr ifT
    ifF' <- argToExpr ifF
    case val' of
      ConstValue i w -> return $ if i/=0
                                 then ifT'
                                 else ifF'
      ConstCondition c -> return $ if c 
                                   then ifT'
                                   else ifF'
      _ -> do
        let cond = valCond val'
        case (ifT',ifF') of
          (PointerValue pT,PointerValue pF) -> do
            ptr <- reNewPtr
            reMemInstr (MISelect [(cond,pT),(not' cond,pF)] ptr)
            return $ PointerValue ptr
          _ -> return $ valSwitch [(ifT',cond),(ifF',not' cond)]
  _ -> reError $ "Implement argToExpr for "++show expr

realizeInstructions :: Enum ptr => [Instruction] 
                       -> Realization ptr (BlockFinalization ptr)
realizeInstructions (instr:instrs) = do
  res <- realizeInstruction instr
  case res of
    Just fin -> return fin
    Nothing -> realizeInstructions instrs
realizeInstructions [] = reError $ "Block terminates prematurely"

realizeInstruction :: Enum ptr => Instruction -> Realization ptr (Maybe (BlockFinalization ptr))
realizeInstruction (IRet e) = do
  res <- argToExpr e
  return $ Just $ Return $ Just res
realizeInstruction IRetVoid = return $ Just $ Return Nothing
realizeInstruction (IBr to) = return $ Just $ Jump (CondElse (to,0))
realizeInstruction (IBrCond cond ifT ifF) = do
  cond' <- argToExpr cond
  case cond' of
    ConstCondition cond'' -> return $ Just $ Jump (CondElse 
                                                   (if cond''
                                                    then ifT
                                                    else ifF,0))
    _ -> return $ Just $ Jump $
         CondIf (ifT,0) (valCond cond') $
         CondElse (ifF,0)
realizeInstruction (ISwitch val def args) = do
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
realizeInstruction (IAssign trg expr) = do
  expr' <- argToExpr expr
  rePutVar trg expr'
  return Nothing
realizeInstruction (IAlloca trg tp size align) = do
  size' <- argToExpr size
  let size'' = case size' of
        ConstValue bv _ -> Left bv
        DirectValue bv -> Right bv
  ptr <- reNewPtr
  reMemInstr (MIAlloc tp size'' ptr)
  rePutVar trg (PointerValue ptr)
  return Nothing
realizeInstruction (IStore val to align) = do
  PointerValue ptr <- argToExpr to
  val' <- argToExpr val
  case (exprType val,val') of
    (TDPtr tp,PointerValue ptr2) -> reMemInstr (MIStorePtr ptr2 ptr)
    (tp,_) -> reMemInstr (MIStore (valValue val') ptr)
  return Nothing
realizeInstruction (IPhi trg args) = do
  nargs <- mapM (\(arg,lbl) -> do
                    arg' <- argToExpr arg
                    re <- ask
                    let Just phi_cond = Map.lookup lbl (rePhis re)
                    return (arg',phi_cond)
                ) args
  case nargs of
    ((PointerValue _,_):_) -> do
      ptr <- reNewPtr
      reMemInstr (MISelect [ (cond,ptr') | (PointerValue ptr',cond) <- nargs ] ptr)
      rePutVar trg (PointerValue ptr)
    _ -> rePutVar trg (valSwitch nargs)
  return Nothing
realizeInstruction (ICall rtp trg _ f args) = case exprDesc f of
  EDNamed fn -> do
    args' <- mapM (\arg -> do
                      arg' <- argToExpr arg
                      return (arg',exprType arg)) args
    case intrinsics fn of
      Just intr -> do
        intr trg args'
        re <- ask
        return $ Just $ Jump (CondElse (reBlock re,reSubblock re + 1))
realizeInstruction (ILoad trg arg align) = do
  PointerValue ptr <- argToExpr arg
  re <- get
  case exprType arg of
    TDPtr (TDPtr tp) -> do
      ptr2 <- reNewPtr
      reMemInstr (MILoadPtr ptr ptr2)
      rePutVar trg (PointerValue ptr2)
    TDPtr tp -> do
      loadRes <- lift $ varNamedAnn "loadRes" ((typeWidth tp)*8)
      reMemInstr (MILoad ptr loadRes)
      rePutVar trg (DirectValue loadRes)
  return Nothing
realizeInstruction instr = reError $ "Implement realizeInstruction for "++show instr

intrinsics :: Enum ptr => String -> Maybe (String -> [(Val ptr,TypeDesc)] -> Realization ptr ())
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
intrinsics "malloc" = Just intr_malloc
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
        ConditionValue val _ -> (reActivation re) .&&. (not' val)
        _ -> (reActivation re) .&&. (nval .==. constantAnn (BitVector 0) sz)
  tell $ mempty { reGuards = [(Custom,guard_cond)] }

intr_watch _ ((ConstValue bv _,_):exprs) = do
  re <- ask
  tell $ mempty { reWatchpoints = [(show bv,reActivation re,
                                    [ (tp,valValue val) 
                                    | (val,tp) <- exprs ])] }

intr_malloc trg [(size,sztp)] = do
  re <- ask
  let Just tp = Map.lookup trg (rePrediction re)
      size' = case size of
        ConstValue bv _ -> Left bv
        DirectValue bv -> Right bv
  ptr <- reNewPtr
  reMemInstr (MIAlloc tp size' ptr)
  rePutVar trg (PointerValue ptr)

intr_nondet width trg [] = do
  v <- lift $ varNamedAnn "nondetVar" width
  rePutVar trg (DirectValue v)