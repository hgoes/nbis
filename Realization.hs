module Realization where

import MemoryModel
import Value
import Analyzation
import ConditionList
import TypeDesc
import InstrDesc
import VarStore

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

data VarKind var ptr = Value Val
                     | Pointer ptr
                     | JoinPoint var
                     deriving Show

data RealizationEnv var ptr
  = RealizationEnv { reFunction :: String
                   , reBlock :: Ptr BasicBlock
                   , reSubblock :: Integer
                   , reActivation :: SMTExpr Bool
                   , reGlobals :: Map (Ptr GlobalVariable) ptr
                   , reArgs :: Map (Ptr Argument) (Either var ptr)
                   , reStaticInput :: Map (Ptr Instruction) (Either Val ptr)
                   , reStructs :: Map String [TypeDesc]
                   }

data RealizationState mem var ptr
  = RealizationState { reVarStore :: VarStore SMT var (String,TypeDesc) Val
                     , reCurMemLoc :: mem
                     , reNextPtr :: ptr
                     , reLocals :: Map (Ptr Instruction) (Either Val ptr,String,TypeDesc)
                     , reInputs :: Map (Ptr Instruction) (Either Val ptr,String,TypeDesc)
                     , rePhis :: Map (Ptr BasicBlock) (SMTExpr Bool)
                     }

data RealizationOutput mem ptr
  = RealizationOutput { reWatchpoints :: [Watchpoint]
                      , reGuards :: [Guard]
                      , reMemInstrs :: [MemoryInstruction mem ptr]
                      }

instance Monoid (RealizationOutput mem ptr) where
  mempty = RealizationOutput { reWatchpoints = mempty
                             , reGuards = mempty
                             , reMemInstrs = mempty
                             }
  mappend o1 o2 = RealizationOutput { reWatchpoints = (reWatchpoints o1) `mappend` (reWatchpoints o2)
                                    , reGuards = (reGuards o1) `mappend` (reGuards o2)
                                    , reMemInstrs = (reMemInstrs o1) `mappend` (reMemInstrs o2)
                                    }

type Realization mem var ptr = RWST (RealizationEnv var ptr) (RealizationOutput mem ptr) (RealizationState mem var ptr) SMT

data BlockFinalization ptr = Jump (CondList (Ptr BasicBlock,Integer))
                           | Return (Maybe (Either Val ptr))
                           | Call String [Either Val ptr] (Ptr Instruction)
                           deriving (Show)

reError :: String -> Realization mem var ptr a
reError msg = do
  re <- ask
  return $ error $ "Error while realizing "++
    (reFunction re)++"."++
    (show $ reBlock re)++"."++
    (show $ reSubblock re)++": "++
    msg

reEnvError :: String -> Realization mem var ptr a
reEnvError msg = do
  re <- ask
  rs <- get
  reError $ msg ++ show (Map.keys $ reLocals rs)
    ++ " " ++ show (Map.keys $ reArgs re)
    ++ " " ++ show (Map.keys $ reGlobals re)

rePutVar :: Ptr Instruction -> String -> TypeDesc -> Either Val ptr -> Realization mem var ptr ()
rePutVar instr name td val = modify (\st -> st { reLocals = Map.insert instr (val,name,td) (reLocals st) })

reNewPtr :: Enum ptr => Realization mem var ptr ptr
reNewPtr = do
  rs <- get
  let ptr = reNextPtr rs
  put $ rs { reNextPtr = succ ptr }
  return ptr

reNewMemLoc :: Enum mem => Realization mem var ptr mem
reNewMemLoc = do
  rs <- get
  let loc = reCurMemLoc rs
  put $ rs { reCurMemLoc = succ loc }
  return $ succ loc

reMemLoc :: Realization mem var ptr mem
reMemLoc = do
  rs <- get
  return $ reCurMemLoc rs

reMemInstr :: MemoryInstruction mem ptr -> Realization mem var ptr ()
reMemInstr instr = tell (mempty { reMemInstrs = [instr] })

reGetJoin :: Ord var => var -> Realization mem var ptr Val
reGetJoin i = do
  rs <- get
  (val,nstore) <- lift $ readVar i (reVarStore rs)
  modify $ \rs -> rs { reVarStore = nstore }
  return val
  
reGetVar :: Ord var => VarKind var ptr -> Realization mem var ptr (Either Val ptr)
reGetVar (Pointer ptr) = return (Right ptr)
reGetVar (Value v) = return (Left v)
reGetVar (JoinPoint i) = fmap Left $ reGetJoin i
  
reNewVar :: Enum ptr => Ptr Instruction -> Maybe String -> TypeDesc -> Realization mem var ptr (Either Val ptr)
reNewVar instr name (PointerType tp) = do
  re <- get
  let ptr = reNextPtr re
  put $ re { reNextPtr = succ ptr }
  return $ Right ptr
reNewVar instr name tp = do
  let name' = case name of
        Nothing -> "input_"++(show instr)
        Just n -> "input_"++n
  val <- case tp of
    IntegerType 1 -> do
      v <- lift $ varNamed name'
      return $ ConditionValue v 1
    IntegerType w -> do
      v <- lift $ varNamedAnn name' w
      return $ DirectValue v
  return $ Left val

argToExpr :: (Enum ptr,Enum mem,Ord var) => Operand -> Realization mem var ptr (Either Val ptr)
argToExpr expr = case operandDesc expr of
  ODNull -> do
    ptr <- reNewPtr
    let PointerType tp = operandType expr
    loc <- reMemLoc
    nloc <- reNewMemLoc
    reMemInstr (MINull loc tp ptr nloc)
    return $ Right ptr
  ODInt v -> return $ Left $ ConstValue v (bitWidth (operandType expr))
  ODInstr instr _ name -> do
    let tp = operandType expr
    re <- get
    rs <- ask
    case Map.lookup instr (reLocals re) of
      Just (res,_,_) -> return res
      Nothing -> case Map.lookup instr (reInputs re) of
        Just (res,_,_) -> return res
        Nothing -> case Map.lookup instr (reStaticInput rs) of
          Just res -> return res
          Nothing -> do
            res <- reNewVar instr name (operandType expr)
            re <- get
            put $ re { reInputs = Map.insert instr (res,case name of
                                                       Nothing -> show instr
                                                       Just n -> n,tp) (reInputs re) }
            return res
  ODGlobal g -> do
    re <- ask
    case Map.lookup g (reGlobals re) of
      Nothing -> reEnvError $ "Couldn't find global variable "++show g
      Just res -> return $ Right res
  ODArgument arg -> do
    re <- ask
    case Map.lookup arg (reArgs re) of
      Nothing -> reEnvError $ "Couldn't find argument variable "++show arg
      Just (Right res) -> return (Right res)
      Just (Left res) -> fmap Left $ reGetJoin res
  ODGetElementPtr ptr idx -> do
    Right val_ptr <- argToExpr ptr
    val_idx <- mapM (\i -> do
                        i' <- argToExpr i 
                        return $ case i' of
                          Left (ConstValue bv _) -> Left bv
                          Left (DirectValue bv) -> Right bv
                    ) idx
    ptr' <- reNewPtr
    loc <- reMemLoc
    nloc <- reNewMemLoc
    reMemInstr (MIIndex loc val_idx val_ptr ptr' nloc)
    return $ Right ptr'
  ODUndef -> return (Left $ ConstValue 0 (bitWidth (operandType expr)))
  _ -> reError $ "Implement argToExpr for "++show expr

realizeInstructions :: (Enum ptr,Enum mem,Ord var)
                       => [InstrDesc Operand] 
                       -> Realization mem var ptr (BlockFinalization ptr)
realizeInstructions (instr:instrs) = do
  res <- realizeInstruction instr
  case res of
    Just fin -> return fin
    Nothing -> realizeInstructions instrs
realizeInstructions [] = reError $ "Block terminates prematurely"

realizeInstruction :: (Enum ptr,Enum mem,Ord var) => InstrDesc Operand -> Realization mem var ptr (Maybe (BlockFinalization ptr))
realizeInstruction (ITerminator (IRet e)) = do
  res <- argToExpr e
  return $ Just $ Return $ Just res
realizeInstruction (ITerminator IRetVoid) = return $ Just $ Return Nothing
realizeInstruction (ITerminator (IBr to)) = do
  re <- get
  return $ Just $ Jump [(constant True,(to,0))]
realizeInstruction (ITerminator (IBrCond cond ifT ifF)) = do
  cond' <- argToExpr cond
  case cond' of
    Left (ConstCondition cond'')
      -> return $ Just $ Jump [(constant True,(if cond''
                                               then ifT
                                               else ifF,0))]
    Left v -> return $ Just $ Jump [(valCond v,(ifT,0))
                                   ,(not' $ valCond v,(ifF,0))]
realizeInstruction (ITerminator (ISwitch val def args)) = do
  val' <- argToExpr val
  args' <- mapM (\(cmp_v,to) -> do
                    cmp_v' <- argToExpr cmp_v
                    return (cmp_v',to)) args
  case val' of
    Left (ConstValue v _) -> case [ to | (Left (ConstValue v' _),to) <- args', v==v' ] of
      [] -> return $ Just $ Jump [(constant True,(def,0))]
      [to] -> return $ Just $ Jump [(constant True,(to,0))]
    Left v -> do
      (jumps,cond') <- foldrM (\(Left cmp_v,to) (lst,cond) -> do
                                  let res = valEq cmp_v v
                                  return ((res .&&. cond,(to,0)):lst,(not' res) .&&. cond)
                              ) ([],constant True) args'
      let jumps' = (cond',(def,0)):jumps
      return $ Just $ Jump jumps'
realizeInstruction instr@(IAssign trg name expr) = do
  let genName v = case name of
        Just name' -> "assign_"++name'
        Nothing -> "assign"++v
  tp <- asks (\re -> getInstrType (reStructs re) instr)
  rval <- case expr of
    IBinaryOperator op lhs rhs -> do
      Left lhs' <- argToExpr lhs
      Left rhs' <- argToExpr rhs
      fmap Left $ lift $ valCopy (genName "BinOp") $ valBinOp op lhs' rhs'
    IICmp op lhs rhs -> case operandType lhs of
      PointerType _ -> do
        Right lhs' <- argToExpr lhs
        Right rhs' <- argToExpr rhs
        cond <- lift $ varNamed (genName "PtrCompare")
        rcond <- case op of
          I_EQ -> return cond
          I_NE -> return $ not' cond
          _ -> reError $ "Comparing pointers using "++show op++
               " unsupported (only (in-)equality allowed)"
        loc <- reMemLoc
        reMemInstr (MICompare loc lhs' rhs' rcond)
        return $ Left $ ConditionValue cond 1
      _ -> do
        Left lhs' <- argToExpr lhs
        Left rhs' <- argToExpr rhs
        fmap Left $ lift $ valCopy (genName "ICmp") $ valIntComp op lhs' rhs'
    IGetElementPtr ptr idx -> do
      Right ptr' <- argToExpr ptr
      idx' <- mapM (\arg -> do
                      arg' <- argToExpr arg
                      return $ case arg' of
                        Left (ConstValue bv _) -> Left bv
                        Left (DirectValue bv) -> Right bv
                  ) idx
      ptr'' <- reNewPtr
      loc <- reMemLoc
      nloc <- reNewMemLoc
      reMemInstr (MIIndex loc idx' ptr' ptr'' nloc)
      return $ Right ptr''
    IPhi args -> do
      nargs <- mapM (\(lbl,arg) -> do
                        arg' <- argToExpr arg
                        re <- get
                        phi_cond <- case Map.lookup lbl (rePhis re) of
                          Nothing -> do
                            phi <- lift $ varNamed "phi"
                            put $ re { rePhis = Map.insert lbl phi (rePhis re) }
                            return phi
                          Just phi -> return phi
                        return (arg',phi_cond)
                    ) args
      case nargs of
        ((Right _,_):_) -> do
          ptr <- reNewPtr
          loc <- reMemLoc
          nloc <- reNewMemLoc
          reMemInstr (MISelect loc [ (cond,ptr') | (Right ptr',cond) <- nargs ] ptr nloc)
          return (Right ptr)
        _ -> fmap Left $ lift $ valCopy (genName "Phi") $ valSwitch (fmap (\(Left v,c) -> (v,c)) nargs)
    ILoad arg -> do
      Right ptr <- argToExpr arg
      loc <- reMemLoc
      case operandType arg of
        PointerType (PointerType tp) -> do
          ptr2 <- reNewPtr
          nloc <- reNewMemLoc
          reMemInstr (MILoadPtr loc ptr ptr2 nloc)
          return $ Right ptr2
        PointerType tp -> do
          loadRes <- lift $ varNamedAnn (genName "LoadRes") ((typeWidth tp)*8)
          reMemInstr (MILoad loc ptr loadRes)
          return $ Left $ DirectValue loadRes
    IBitCast tp_to arg -> do
      Right ptr <- argToExpr arg
      let PointerType tp_from = operandType arg
      ptr' <- reNewPtr
      loc <- reMemLoc
      nloc <- reNewMemLoc
      reMemInstr (MICast loc tp_from tp_to ptr ptr' nloc)
      return $ Right ptr'
    ISExt tp arg -> do
      arg' <- argToExpr arg
      case arg' of
        Left (ConditionValue v w) -> return $ Left $ ConditionValue v (bitWidth (operandType arg))
        Left arg'' -> let v = valValue arg''
                          w = bitWidth (operandType arg)
                          d = (bitWidth tp) - w
                          nv = bvconcat (ite (bvslt v (constantAnn (BitVector 0) w::SMTExpr (BitVector BVUntyped)))
                                         (constantAnn (BitVector (-1)) d::SMTExpr (BitVector BVUntyped))
                                         (constantAnn (BitVector 0) (fromIntegral d))) v
                      in fmap Left $ lift $ valCopy (genName "SExt") $ DirectValue nv
    ITrunc tp arg -> do
      let w = bitWidth tp
      arg' <- argToExpr arg
      case arg' of
        Left (ConstValue bv _) -> return $ Left $ ConstValue bv w
        Left (ConditionValue v _) -> return $ Left $ ConditionValue v w
        Left arg'' -> fmap Left $ lift $ valCopy (genName "Trunc") $ DirectValue (bvextract' 0 w (valValue arg''))
    IZExt tp arg -> do
      arg' <- argToExpr arg
      case arg' of
        Left (ConditionValue v w) -> return $ Left $ ConditionValue v (bitWidth (operandType arg))
        Left arg'' -> let v = valValue arg''
                          d = (bitWidth tp) - (bitWidth (operandType arg))
                          nv = bvconcat (constantAnn (BitVector 0) d::SMTExpr (BitVector BVUntyped)) v
                      in fmap Left $ lift $ valCopy (genName "ZExt") $ DirectValue nv
    IAlloca tp sz -> do
      size' <- case sz of
        Nothing -> return (ConstValue 1 32)
        Just sz' -> do
                    Left sz'' <- argToExpr sz'
                    return sz''
      let size'' = case size' of
            ConstValue bv _ -> Left bv
            DirectValue bv -> Right bv
      ptr <- reNewPtr
      loc <- reMemLoc
      new_loc <- reNewMemLoc
      reMemInstr (MIAlloc loc tp size'' ptr new_loc)
      return $ Right ptr
    ISelect cond ifT ifF -> do
      Left condArg <- argToExpr cond
      ifTArg <- argToExpr ifT
      ifFArg <- argToExpr ifF
      let cond' = valCond condArg
      case (ifTArg,ifFArg) of
        (Right ifT',Right ifF') -> do
          ptr <- reNewPtr
          loc <- reMemLoc
          nloc <- reNewMemLoc
          reMemInstr (MISelect loc [(cond',ifT'),(not' cond',ifF')] ptr nloc)
          return $ Right ptr
        (Left ifT',Left ifF') -> fmap Left $ lift $ valCopy (genName "Switch") $ valSwitch [(ifT',cond'),(ifF',not' cond')]
    IMalloc (Just tp) sz True -> do
      Left rsz <- argToExpr sz
      let size = case rsz of
            ConstValue bv _ -> Left bv
            DirectValue bv -> Right bv
      ptr <- reNewPtr
      loc <- reMemLoc
      new_loc <- reNewMemLoc
      reMemInstr (MIAlloc loc tp size ptr new_loc)
      return (Right ptr)
    _ -> reEnvError $ "Unimplemented assign instruction: "++show expr
  rePutVar trg (case name of
                   Nothing -> show trg
                   Just n -> n) tp rval
  return Nothing
realizeInstruction (IStore val to) = do
  Right ptr <- argToExpr to
  val' <- argToExpr val
  loc <- reMemLoc
  new_loc <- reNewMemLoc
  case (operandType val,val') of
    (PointerType tp,Right ptr2) -> reMemInstr (MIStorePtr loc ptr2 ptr new_loc)
    (tp,Left v) -> reMemInstr (MIStore loc (valValue v) ptr new_loc)
  return Nothing
realizeInstruction (ITerminator (ICall trg f args)) = case operandDesc f of
  ODFunction rtp fn argtps -> do
    args' <- mapM (\arg -> do
                      arg' <- argToExpr arg
                      return (arg',operandType arg)) args
    case intrinsics fn of
      Just intr -> do
        intr trg args'
        return Nothing
      Nothing -> return $ Just $ Call fn (fmap fst args') trg
realizeInstruction instr = reError $ "Implement realizeInstruction for "++show instr

isIntrinsic :: String -> Bool
isIntrinsic name = case intrinsics name :: Maybe (Ptr Instruction -> [(Either Val Int,TypeDesc)] -> Realization Int Int Int ()) of
  Nothing -> False
  Just _ -> True

intrinsics :: (Enum ptr,Enum mem) => String -> Maybe (Ptr Instruction -> [(Either Val ptr,TypeDesc)] -> Realization mem var ptr ())
intrinsics "llvm.memcpy.p0i8.p0i8.i64" = Just intr_memcpy
intrinsics "llvm.memcpy.p0i8.p0i8.i32" = Just intr_memcpy
intrinsics "llvm.memset.p0i8.i32" = Just intr_memset
intrinsics "llvm.memset.p0i8.i64" = Just intr_memset
intrinsics "llvm.stacksave" = Just intr_stacksave
intrinsics "llvm.stackrestore" = Just intr_stackrestore
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

intr_memcpy _ [(Right to,_),(Right from,_),(Left len,_),_,_] = do
  let len' = case len of
        ConstValue l _ -> Left l
        DirectValue l -> Right l
  loc <- reMemLoc
  nloc <- reNewMemLoc
  reMemInstr (MICopy loc len' from to nloc)

intr_memset _ [(Right dest,_),(val,_),(Left (ConstValue len _),_),_,_] = do
  reError "memset not implemented"
  
intr_restrict _ [(Left val,_)] = do
  re <- ask
  lift $ comment " Restriction:"
  case val of
    ConditionValue val _ -> lift $ assert $ (reActivation re) .=>. val
    _ -> do
      let nval = valValue val
          sz = extractAnnotation nval
      lift $ assert $ (reActivation re) .=>. (not' $ nval .==. constantAnn (BitVector 0) sz)

intr_assert _ [(Left val,_)] = do
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

intr_watch _ ((Left (ConstValue bv _),_):exprs) = do
  re <- ask
  tell $ mempty { reWatchpoints = [(show bv,reActivation re,
                                    [ (tp,valValue val) 
                                    | (Left val,tp) <- exprs ])] }

intr_nondet width trg [] = do
  v <- lift $ varNamedAnn "nondetVar" width
  rePutVar trg "nondetVar" (IntegerType width) (Left $ DirectValue v)

intr_stacksave _ _ = return ()
intr_stackrestore _ _ = return ()