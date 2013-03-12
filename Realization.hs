module Realization where

import MemoryModel
import Value
import Analyzation
import ConditionList

import Language.SMTLib2
import Control.Monad
import Control.Monad.State
import Data.Map as Map
import LLVM.Core
import Data.Foldable as F

type Watchpoint = (String,SMTExpr Bool,[(TypeDesc,SMTExpr (BitVector BVUntyped))])

type Guard = (ErrorDesc,SMTExpr Bool)

data RealizationEnv m
  = RealizationEnv { reFunction :: String
                   , reBlock :: String
                   , reSubblock :: Integer
                   , reActivation :: SMTExpr Bool
                   , reMemChanged :: Bool
                   , reGlobalMem :: m
                   , reLocalMem :: LocalMem m
                   , reGlobals :: Map String (Pointer m)
                   , reArgs :: Map String (Val m)
                   , reLocals :: Map String (Val m)
                   , rePhis :: Map String (SMTExpr Bool)
                   , reWatchpoints :: [Watchpoint]
                   , reGuards :: [Guard]
                   , rePrediction :: Map String TypeDesc
                   }

type Realization m = StateT (RealizationEnv m) SMT

data BlockFinalization mem = Jump (ConditionList (String,Integer))
                           | Return (Maybe (Val mem))
                           | Call String [Val mem] String
                           deriving (Show)

reError :: String -> Realization m a
reError msg = do
  re <- get
  return $ error $ "Error while realizing "++
    (reFunction re)++"."++
    (reBlock re)++"."++
    (show $ reSubblock re)++": "++
    msg

reEnvError :: String -> Realization m a
reEnvError msg = do
  re <- get
  reError $ msg ++ show (Map.keys $ reLocals re)
    ++ " " ++ show (Map.keys $ reArgs re)
    ++ " " ++ show (Map.keys $ reGlobals re)

reGetVar :: String -> Realization m (Val m)
reGetVar name = do
  re <- get
  case Map.lookup name (reLocals re) of
    Just v -> return v
    Nothing -> case Map.lookup name (reArgs re) of
      Just v -> return v
      Nothing -> case Map.lookup name (reGlobals re) of
        Just v -> return (PointerValue v)
        Nothing -> reEnvError $ "Couldn't find "++show name

argToExpr :: MemoryModel m => Expr -> Realization m (Val m)
argToExpr expr = case exprDesc expr of
  EDNamed name -> reGetVar name
  EDNull -> do
    re <- get
    let (ptr,nmem) = memPtrNull (reGlobalMem re)
    put $ re { reGlobalMem = nmem }
    return $ PointerValue ptr
  EDICmp pred lhs rhs -> case exprType lhs of
    TDPtr _ -> do
      PointerValue lhs' <- argToExpr lhs
      PointerValue rhs' <- argToExpr rhs
      re <- get
      let (cond,nmem) = memPtrEq (reGlobalMem re) lhs' rhs'
      put $ re { reGlobalMem = nmem }
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
        re <- get
        let PointerValue ptr = arg'
            TDPtr tp = exprType expr
            (ptr',nmem) = memCast (reGlobalMem re) tp ptr
        put $ re { reGlobalMem = nmem }
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
    re <- get
    let (ptr',nmem) = memIndex (reGlobalMem re) (exprType expr') args' ptr
    put $ re { reGlobalMem = nmem }
    return $ PointerValue ptr'
  EDBinOp op lhs rhs -> do
    lhs' <- argToExpr lhs
    rhs' <- argToExpr rhs
    return $ valBinOp op lhs' rhs'
  _ -> reError $ "Implement argToExpr for "++show expr

realizeInstructions :: MemoryModel m => [Instruction] 
                       -> Realization m (BlockFinalization m)
realizeInstructions (instr:instrs) = do
  res <- realizeInstruction instr
  case res of
    Just fin -> return fin
    Nothing -> realizeInstructions instrs
realizeInstructions [] = reError $ "Block terminates prematurely"

realizeInstruction :: MemoryModel m => Instruction -> Realization m (Maybe (BlockFinalization m))
realizeInstruction (IRet e) = do
  res <- argToExpr e
  return $ Just $ Return $ Just res
realizeInstruction IRetVoid = return $ Just $ Return Nothing
realizeInstruction (IBr to) = do
  re <- get
  return $ Just $ Jump (CondElse (to,0))
realizeInstruction (IBrCond cond ifT ifF) = do
  cond' <- argToExpr cond
  re <- get
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
  re <- get
  case val' of
    ConstValue v _ -> case [ to | (ConstValue v' _,to) <- args', v==v' ] of
      [] -> return $ Just $ Jump (CondElse (def,0))
      [to] -> return $ Just $ Jump (CondElse (to,0))
    _ -> do
      jumps <- foldrM (\(cmp_v,to) cond -> do
                          re <- get
                          let (res,nmem) = valEq (reGlobalMem re) cmp_v val'
                          put $ re { reGlobalMem = nmem }
                          return (CondIf (to,0) res cond)
                      ) (CondElse (def,0)) args'
      return $ Just $ Jump jumps
realizeInstruction (IAssign trg expr) = do
  expr' <- argToExpr expr
  modify (\re -> re { reLocals = Map.insert trg expr' (reLocals re) })
  return Nothing
realizeInstruction (IAlloca trg tp size align) = do
  size' <- argToExpr size
  let size'' = case size' of
        ConstValue bv _ -> Left bv
        DirectValue bv -> Right bv
  re <- get
  (ptr,nmem,nloc) <- lift $ memAlloc tp size'' Nothing (reGlobalMem re) (reLocalMem re)
  put $ re { reGlobalMem = nmem
           , reLocalMem = nloc
           , reMemChanged = True 
           , reLocals = Map.insert trg (PointerValue ptr) (reLocals re) }
  return Nothing
realizeInstruction (IStore val to align) = do
  PointerValue ptr <- argToExpr to
  val' <- argToExpr val
  case (exprType val,val') of
    (TDPtr tp,PointerValue ptr2) -> do
      re <- get
      let (nmem,nloc,errs) = memStorePtr tp ptr ptr2 (reGlobalMem re) (reLocalMem re)
      put $ re { reGlobalMem = nmem
               , reLocalMem = nloc
               , reMemChanged = True
               , reGuards = [ (err,reActivation re .&&. cond) | (err,cond) <- errs ] ++ reGuards re
               }
    (tp,_) -> do
      re <- get
      (nmem,nloc,errs) <- lift $ memStore tp ptr (valValue val') (reActivation re) (reGlobalMem re) (reLocalMem re)
      put $ re { reGlobalMem = nmem
               , reLocalMem = nloc
               , reMemChanged = True 
               , reGuards = [ (err,reActivation re .&&. cond) | (err,cond) <- errs ] ++ reGuards re
               }
  return Nothing
realizeInstruction (IPhi trg args) = do
  nargs <- mapM (\(arg,lbl) -> do
                    arg' <- argToExpr arg
                    re <- get
                    let Just phi_cond = Map.lookup lbl (rePhis re)
                    return (arg',phi_cond)
                ) args
  case nargs of
    ((PointerValue _,_):_) -> error "Phi pointer not yet implemented"
    _ -> do
         re <- get
         put $ re { reLocals = Map.insert trg (valSwitch nargs) (reLocals re) }
  return Nothing
  {-F.mapM_ (\(arg,lbl) -> do
              arg' <- argToExpr arg
              re <- get
              let Just phi_cond = Map.lookup lbl (rePhis re)
                  --Just phi_res = Map.lookup trg (reLocals re)
              cmem <- case (arg',phi_res) of
                (PointerValue p1,PointerValue p2) 
                  -> lift $ memPtrExtend (reGlobalMem re) p1 p2 phi_cond
                _ -> do
                  let (cond,cmem') = valEq (reGlobalMem re) phi_res arg'
                  lift $ assert $ phi_cond .=>. cond
                  return cmem'
              put $ re { reGlobalMem = cmem }
          ) args
  return Nothing-}
realizeInstruction (ICall rtp trg _ f args) = case exprDesc f of
  EDNamed fn -> do
    args' <- mapM (\arg -> do
                      arg' <- argToExpr arg
                      return (arg',exprType arg)) args
    case intrinsics fn of
      Just intr -> do
        intr trg args'
        re <- get
        return $ Just $ Jump (CondElse (reBlock re,reSubblock re + 1))
realizeInstruction (ILoad trg arg align) = do
  PointerValue ptr <- argToExpr arg
  re <- get
  case exprType arg of
    TDPtr (TDPtr tp) -> do
      let (ptr',errs,nmem) = memLoadPtr tp ptr (reGlobalMem re) (reLocalMem re)
      put $ re { reLocals = Map.insert trg (PointerValue ptr') (reLocals re)
               , reGlobalMem = nmem
               , reGuards = [ (err,reActivation re .&&. cond) | (err,cond) <- errs ] ++ reGuards re
               }
    TDPtr tp -> do
      (ret,errs,nmem) <- lift $ memLoad tp ptr (reActivation re) (reGlobalMem re) (reLocalMem re)
      put $ re { reLocals = Map.insert trg (DirectValue ret) (reLocals re)
               , reGlobalMem = nmem
               , reGuards = [ (err,reActivation re .&&. cond) | (err,cond) <- errs ] ++ reGuards re
               }
  return Nothing
realizeInstruction instr = reError $ "Implement realizeInstruction for "++show instr

intrinsics :: MemoryModel m => String -> Maybe (String -> [(Val m,TypeDesc)] -> Realization m ())
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

intr_memcpy _ [(PointerValue to,_),(PointerValue from,_),(ConstValue len _,_),_,_] = do
  re <- get
  let (nloc,nmem) = memCopy (reGlobalMem re) len to from (reLocalMem re)
  put $ re { reGlobalMem = nmem
           , reLocalMem = nloc
           , reMemChanged = True
           }

intr_memset _ [(PointerValue dest,_),(val,_),(ConstValue len _,_),_,_] = do
  re <- get
  let (nloc,nmem) = memSet (reGlobalMem re) len (valValue val) dest (reLocalMem re)
  put $ re { reGlobalMem = nmem
           , reLocalMem = nloc
           , reMemChanged = True
           }

intr_restrict _ [(val,_)] = do
  re <- get
  lift $ comment " Restriction:"
  case val of
    ConditionValue val _ -> lift $ assert $ (reActivation re) .=>. val
    _ -> lift $ assert $ (reActivation re) .=>. (not' $ valValue val .==. constantAnn (BitVector 0) 32)

intr_assert _ [(val,_)] 
  = modify $ \re -> let guard_cond = case val of
                          ConditionValue val _ -> (reActivation re) .&&. (not' val)
                          _ -> (reActivation re) .&&. (valValue val .==. constantAnn (BitVector 0) 32)
                    in re { reGuards = (Custom,guard_cond):(reGuards re) }

intr_watch _ ((ConstValue bv _,_):exprs)
  = modify $ \re -> re { reWatchpoints = (show bv,reActivation re,
                                          [ (tp,valValue val) 
                                          | (val,tp) <- exprs ]
                                         ):(reWatchpoints re) }

intr_malloc trg [(size,sztp)] = do
  re <- get
  let Just tp = Map.lookup trg (rePrediction re)
      size' = case size of
        ConstValue bv _ -> Left bv
        DirectValue bv -> Right bv
  (ptr,nmem,nloc) <- lift $ memAlloc tp size' Nothing (reGlobalMem re) (reLocalMem re)
  put $ re { reLocals = Map.insert trg (PointerValue ptr) (reLocals re)
           , reGlobalMem = nmem
           , reLocalMem = nloc
           , reMemChanged = True
           }

intr_nondet width trg [] = do
  v <- lift $ varAnn width
  modify $ \re -> re { reLocals = Map.insert trg (DirectValue v) (reLocals re) }
