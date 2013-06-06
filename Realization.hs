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
import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable
import Data.Foldable
import Foreign.Ptr
import Prelude hiding (foldr)
import Data.Maybe (catMaybes)

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
                   , reArgs :: Map (Ptr Argument) (Either Val ptr)
                   , reInputs :: Map (Ptr Instruction) (Either Val ptr)
                   , rePhis :: Map (Ptr BasicBlock) (SMTExpr Bool)
                   , reStructs :: Map String [TypeDesc]
                   }

data RealizationState mem ptr
  = RealizationState { reCurMemLoc :: mem
                     , reNextPtr :: ptr
                     , reLocals :: Map (Ptr Instruction) (Either Val ptr)
                     }

data RealizationOutput mem ptr
  = RealizationOutput { reWatchpoints :: [Watchpoint]
                      , reGuards :: [Guard]
                      , reMemInstrs :: [MemoryInstruction mem ptr]
                      }

data RealizationInfo = RealizationInfo { rePossiblePhis :: Set (Ptr BasicBlock)
                                       , rePossibleInputs :: Set (Ptr Instruction)
                                       , rePossibleArgs :: Set (Ptr Argument)
                                       , rePossibleGlobals :: Set (Ptr GlobalVariable)
                                       , reLocallyDefined :: Set (Ptr Instruction) }

type RealizationMonad mem ptr = RWST (RealizationEnv ptr) (RealizationOutput mem ptr) (RealizationState mem ptr) SMT

newtype Realization mem ptr a = Realization { runRealization :: RealizationInfo -> (RealizationInfo,RealizationMonad mem ptr a) }

instance Monoid (RealizationOutput mem ptr) where
  mempty = RealizationOutput { reWatchpoints = mempty
                             , reGuards = mempty
                             , reMemInstrs = mempty
                             }
  mappend o1 o2 = RealizationOutput { reWatchpoints = (reWatchpoints o1) `mappend` (reWatchpoints o2)
                                    , reGuards = (reGuards o1) `mappend` (reGuards o2)
                                    , reMemInstrs = (reMemInstrs o1) `mappend` (reMemInstrs o2)
                                    }

instance Functor (Realization mem ptr) where
  fmap f (Realization x) = Realization (\info -> let (ninfo,res) = x info
                                                 in (ninfo,fmap f res))

instance Applicative (Realization mem ptr) where
  pure x = reLift (return x)
  (<*>) (Realization f) (Realization x) = Realization (\info -> let (info1,rf) = f info
                                                                    (info2,rx) = x info1
                                                                in (info2,do
                                                                       rrf <- rf
                                                                       rrx <- rx
                                                                       return $ rrf rrx))

reLift :: RealizationMonad mem ptr a -> Realization mem ptr a
reLift act = Realization $ \info -> (info,act)

reInject :: (a -> RealizationMonad mem ptr b) -> Realization mem ptr a -> Realization mem ptr b
reInject f x = Realization $ \info -> let (info1,act) = runRealization x info
                                      in (info1,act >>= f)

reDefineVar :: Enum ptr => Ptr Instruction -> String -> Realization mem ptr (Either Val ptr) -> Realization mem ptr ()
reDefineVar instr name genval = Realization $ \info -> let (info1,rgen) = runRealization genval info
                                                       in (info1 { reLocallyDefined = Set.insert instr (reLocallyDefined info) },
                                                           do
                                                             val <- rgen
                                                             nval <- case val of
                                                               Left rval -> lift $ fmap Left $ valCopy name rval
                                                               Right ptr -> return (Right ptr)
                                                             modify (\st -> st { reLocals = Map.insert instr nval (reLocals st) })
                                                          )

reNewPtr :: Enum ptr => RealizationMonad mem ptr ptr
reNewPtr = do
  rs <- get
  let ptr = reNextPtr rs
  put $ rs { reNextPtr = succ ptr }
  return ptr

reNewMemLoc :: Enum mem => RealizationMonad mem ptr mem
reNewMemLoc = do
  rs <- get
  let loc = reCurMemLoc rs
  put $ rs { reCurMemLoc = succ loc }
  return $ succ loc

reMemLoc :: RealizationMonad mem ptr mem
reMemLoc = do
  rs <- get
  return $ reCurMemLoc rs

reMemInstr :: MemoryInstruction mem ptr -> RealizationMonad mem ptr ()
reMemInstr instr = tell (mempty { reMemInstrs = [instr] })

reGetPhi :: (Enum mem,Enum ptr) => (Ptr BasicBlock,Operand) -> Realization mem ptr (Maybe (SMTExpr Bool,Either Val ptr))
reGetPhi (blk,instr) = Realization $ \info -> let (info1,getArg) = runRealization (argToExpr instr) info
                                              in (info1 { rePossiblePhis = Set.insert blk (rePossiblePhis info) },do
                                                     re <- ask
                                                     case Map.lookup blk (rePhis re) of
                                                       Nothing -> return Nothing
                                                       Just cond -> do
                                                         val <- getArg
                                                         return $ Just (cond,val))

argToExpr :: (Enum ptr,Enum mem) => Operand -> Realization mem ptr (Either Val ptr)
argToExpr expr = case operandDesc expr of
  ODNull -> let PointerType tp = operandType expr
            in reInject (\(ptr,instr) -> reMemInstr instr >> return (Right ptr)) $
               liftA3 (\ptr loc nloc -> (ptr,MINull loc tp ptr nloc)) (reLift reNewPtr) (reLift reMemLoc) (reLift reNewMemLoc)
  ODInt v -> pure $ Left $ ConstValue v (bitWidth (operandType expr))
  ODInstr instr _ name -> Realization $ \info -> if Set.member instr (reLocallyDefined info)
                                                 then (info,do
                                                          rs <- get
                                                          case Map.lookup instr (reLocals rs) of
                                                            Just res -> return res)
                                                 else (info { rePossibleInputs = Set.insert instr (rePossibleInputs info) },do
                                                          re <- ask
                                                          case Map.lookup instr (reInputs re) of
                                                            Just res -> return res)
  ODGlobal g -> Realization $ \info -> (info { rePossibleGlobals = Set.insert g (rePossibleGlobals info) },do
                                           re <- ask
                                           case Map.lookup g (reGlobals re) of
                                             Just res -> return $ Right res)
  ODArgument arg -> Realization $ \info -> (info { rePossibleArgs = Set.insert arg (rePossibleArgs info) },do
                                               re <- ask
                                               case Map.lookup arg (reArgs re) of
                                                 Just res -> return res)
  ODGetElementPtr ptr idx -> reInject (\(ptr',instr) -> reMemInstr instr >> return (Right ptr')) $
                             (\(Right val_ptr) val_idx ptr' loc nloc -> (ptr',MIIndex loc (fmap (\i -> case i of
                                                                                                    Left (ConstValue bv _) -> Left bv
                                                                                                    Left (DirectValue bv) -> Right bv
                                                                                                ) val_idx
                                                                                          ) val_ptr ptr' nloc)) <$>
                             (argToExpr ptr) <*>
                             (traverse argToExpr idx) <*>
                             (reLift reNewPtr) <*>
                             (reLift reMemLoc) <*>
                             (reLift reNewMemLoc)
  ODUndef -> pure (Left $ ConstValue 0 (bitWidth (operandType expr)))

data BlockFinalization ptr = Jump (CondList (Ptr BasicBlock))
                           | Return (Maybe (Either Val ptr))
                           | Call String [Either Val ptr] (Ptr Instruction)
                           deriving (Show)

realizeInstruction :: (Enum ptr,Enum mem) => InstrDesc Operand -> Realization mem ptr (Maybe (BlockFinalization ptr))
realizeInstruction (ITerminator (IRet e)) = Just . Return . Just <$> argToExpr e
realizeInstruction (ITerminator IRetVoid) = pure $ Just $ Return Nothing
realizeInstruction (ITerminator (IBr to)) = pure $ Just $ Jump [(constant True,to)]
realizeInstruction (ITerminator (IBrCond cond ifT ifF))
  = (\cond' -> case cond' of
        Left (ConstCondition cond'') -> Just $ Jump [(constant True,if cond''
                                                                    then ifT
                                                                    else ifF)]
        Left v -> Just $ Jump [(valCond v,ifT)
                              ,(not' $ valCond v,ifF)]) <$>
    (argToExpr cond)
realizeInstruction (ITerminator (ISwitch val def args))
  = (\val' args' -> case val' of
        Left (ConstValue v _)
          -> case [ to | (Left (ConstValue v' _),to) <- args', v==v' ] of
          [] -> Just $ Jump [(constant True,def)]
          [to] -> Just $ Jump [(constant True,to)]
        Left v -> let (jumps,cond') = foldr (\(Left cmp_v,to) (lst,cond)
                                             -> let res = valEq cmp_v v
                                                in ((res .&&. cond,to):lst,(not' res) .&&. cond)
                                            ) ([],constant True) args'
                      jumps' = (cond',def):jumps
                  in Just $ Jump jumps') <$>
    (argToExpr val) <*>
    (traverse (\(cmp_v,to) -> (\r -> (r,to)) <$> (argToExpr cmp_v)) args)
realizeInstruction (IAssign trg name expr)
  = let rname = case name of
          Just name' -> "assign_"++name'
          Nothing -> "assign"++(case expr of
                                   IBinaryOperator _ _ _ -> "BinOp"
                                   IICmp _ _ _ -> "ICmp"
                                   IGetElementPtr _ _ -> "GetElementPtr"
                                   IPhi _ -> "Phi"
                                   ILoad _ -> "Load"
                                   IBitCast _ _ -> "BitCast"
                                   ISExt _ _ -> "SExt"
                                   IZExt _ _ -> "ZExt"
                                   IAlloca _ _ -> "Alloca"
                                   ISelect _ _ _ -> "Select"
                                   _ -> "Unknown")
    in (reDefineVar trg rname
        (case expr of
            IBinaryOperator op lhs rhs -> (\(Left lhs') (Left rhs') -> Left $ valBinOp op lhs' rhs') <$>
                                          (argToExpr lhs) <*>
                                          (argToExpr rhs)
            IICmp op lhs rhs -> case operandType lhs of
              PointerType _ -> reInject (\(val,instr) -> reMemInstr instr >> return val) $
                               (\(Right lhs') (Right rhs') loc cond
                                -> (Left $ ConditionValue (case op of
                                                              I_EQ -> cond
                                                              I_NE -> not' cond) 1,MICompare loc lhs' rhs' cond)) <$>
                               (argToExpr lhs) <*>
                               (argToExpr rhs) <*>
                               (reLift reMemLoc) <*>
                               (reLift $ lift $ varNamed "PtrCompare")
              _ -> (\(Left lhs') (Left rhs') -> Left $ valIntComp op lhs' rhs') <$>
                   (argToExpr lhs) <*>
                   (argToExpr rhs)
            IGetElementPtr ptr idx -> reInject (\(ptr',instr) -> reMemInstr instr >> return (Right ptr')) $
                                      (\(Right val_ptr) val_idx ptr' loc nloc -> (ptr',MIIndex loc (fmap (\i -> case i of
                                                                                                             Left (ConstValue bv _) -> Left bv
                                                                                                             Left (DirectValue bv) -> Right bv
                                                                                                         ) val_idx
                                                                                                   ) val_ptr ptr' nloc)) <$>
                                      (argToExpr ptr) <*>
                                      (traverse argToExpr idx) <*>
                                      (reLift reNewPtr) <*>
                                      (reLift reMemLoc) <*>
                                      (reLift reNewMemLoc)
            IPhi args -> reInject (\args' -> case args' of
                                      Left [(_,v)] -> return (Left v)
                                      Right [(_,p)] -> return (Right p)
                                      Left vs -> return $ Left $ valSwitch (fmap (\(c,v) -> (v,c)) vs)
                                      Right ps -> do
                                        ptr <- reNewPtr
                                        loc <- reMemLoc
                                        nloc <- reNewMemLoc
                                        reMemInstr (MISelect loc ps ptr nloc)
                                        return $ Right ptr
                                  ) $
                         (\args' -> case catMaybes args' of
                             all@((_,Right _):_) -> Right (fmap (\(cond,Right p) -> (cond,p)) all)
                             all@((_,Left _):_) -> Left (fmap (\(cond,Left v) -> (cond,v)) all)) <$>
                         (traverse reGetPhi args)
            ILoad arg -> reInject (\(Right ptr) -> do
                                      loc <- reMemLoc
                                      case operandType arg of
                                        PointerType (PointerType tp) -> do
                                          ptr2 <- reNewPtr
                                          nloc <- reNewMemLoc
                                          reMemInstr (MILoadPtr loc ptr ptr2 nloc)
                                          return $ Right ptr2
                                        PointerType tp -> do
                                          loadRes <- lift $ varNamedAnn "LoadRes" ((typeWidth tp)*8)
                                          reMemInstr (MILoad loc ptr loadRes)
                                          return $ Left $ DirectValue loadRes)
                         (argToExpr arg)
            IBitCast tp_to arg -> reInject (\(Right ptr) -> do
                                               let PointerType tp_from = operandType arg
                                               loc <- reMemLoc
                                               ptr' <- reNewPtr
                                               nloc <- reNewMemLoc
                                               reMemInstr (MICast loc tp_from tp_to ptr ptr' nloc)
                                               return $ Right ptr')
                                  (argToExpr arg)
            ISExt tp arg -> (\arg' -> case arg' of
                                Left (ConditionValue v w) -> Left $ ConditionValue v (bitWidth (operandType arg))
                                Left arg'' -> let v = valValue arg''
                                                  w = bitWidth (operandType arg)
                                                  d = (bitWidth tp) - w
                                                  nv = bvconcat (ite (bvslt v (constantAnn (BitVector 0) w::SMTExpr (BitVector BVUntyped)))
                                                                 (constantAnn (BitVector (-1)) d::SMTExpr (BitVector BVUntyped))
                                                                 (constantAnn (BitVector 0) (fromIntegral d))) v
                                              in Left $ DirectValue nv) <$>
                            (argToExpr arg)
            IZExt tp arg -> (\arg' -> case arg' of
                                Left (ConditionValue v w) -> Left $ ConditionValue v (bitWidth (operandType arg))
                                Left arg'' -> let v = valValue arg''
                                                  w = bitWidth (operandType arg)
                                                  d = (bitWidth tp) - w
                                                  nv = bvconcat (ite (bvslt v (constantAnn (BitVector 0) w::SMTExpr (BitVector BVUntyped)))
                                                                 (constantAnn (BitVector (-1)) d::SMTExpr (BitVector BVUntyped))
                                                                 (constantAnn (BitVector 0) (fromIntegral d))) v
                                              in Left $ DirectValue nv) <$>
                            (argToExpr arg)
            IAlloca tp sz -> reInject (\size -> do
                                          ptr <- reNewPtr
                                          loc <- reMemLoc
                                          new_loc <- reNewMemLoc
                                          reMemInstr (MIAlloc loc tp size ptr new_loc)
                                          return $ Right ptr) $
                             (case sz of
                                 Nothing -> pure (Left 1)
                                 Just sz' -> (\(Left r) -> case r of
                                                 ConstValue bv _ -> Left bv
                                                 DirectValue bv -> Right bv
                                             ) <$> argToExpr sz')
            ISelect cond ifT ifF -> reInject (\(cond',ifTArg,ifFArg)
                                              -> case (ifTArg,ifFArg) of
                                                (Right ifT',Right ifF') -> do
                                                  ptr <- reNewPtr
                                                  loc <- reMemLoc
                                                  nloc <- reNewMemLoc
                                                  reMemInstr (MISelect loc [(cond',ifT'),(not' cond',ifF')] ptr nloc)
                                                  return $ Right ptr
                                                (Left ifT',Left ifF') -> return $ Left $ valSwitch [(ifT',cond'),(ifF',cond')]) $
                                    (\(Left argCond) ifT' ifF' -> (valCond argCond,ifT',ifF')) <$>
                                    (argToExpr cond) <*>
                                    (argToExpr ifT) <*>
                                    (argToExpr ifF)
            IMalloc (Just tp) sz True -> reInject (\size -> do
                                                      ptr <- reNewPtr
                                                      loc <- reMemLoc
                                                      new_loc <- reNewMemLoc
                                                      reMemInstr (MIAlloc loc tp size ptr new_loc)
                                                      return $ Right ptr) $
                                         (\(Left r) -> case r of
                                             ConstValue bv _ -> Left bv
                                             DirectValue bv -> Right bv
                                         ) <$> argToExpr sz
        )) *> pure Nothing
realizeInstruction (IStore val to) = reInject (\(ptr,val) -> do
                                                  loc <- reMemLoc
                                                  new_loc <- reNewMemLoc
                                                  case val of
                                                    Right ptr2 -> reMemInstr (MIStorePtr loc ptr2 ptr new_loc)
                                                    Left v -> reMemInstr (MIStore loc (valValue v) ptr new_loc)
                                                  return Nothing) $
                                     (\(Right ptr) val -> (ptr,val)) <$>
                                     (argToExpr to) <*>
                                     (argToExpr val)
realizeInstruction (ITerminator (ICall trg f args)) = case operandDesc f of
  ODFunction rtp fn argtps -> let args' = traverse (\arg -> (\r -> (r,operandType arg)) <$> argToExpr arg) args
                              in case intrinsics fn of
                                Nothing -> (\args'' -> Just $ Call fn (fmap fst args'') trg) <$> args'
                                Just (def,intr) -> (if def
                                                    then reDefineVar trg (fn++"Result") (reInject (\args'' -> do
                                                                                                      Just res <- intr args''
                                                                                                      return res) args')
                                                    else reInject (\args'' -> intr args'' >> return ()) args') *> pure Nothing

isIntrinsic :: String -> Bool
isIntrinsic name = case intrinsics name :: Maybe (Bool,[(Either Val Int,TypeDesc)] -> RealizationMonad Int Int (Maybe (Either Val Int))) of
  Nothing -> False
  Just _ -> True

intrinsics :: (Enum ptr,Enum mem) => String -> Maybe (Bool,[(Either Val ptr,TypeDesc)] -> RealizationMonad mem ptr (Maybe (Either Val ptr)))
--intrinsics "llvm.memcpy.p0i8.p0i8.i64" = Just intr_memcpy
--intrinsics "llvm.memcpy.p0i8.p0i8.i32" = Just intr_memcpy
--intrinsics "llvm.memset.p0i8.i32" = Just intr_memset
--intrinsics "llvm.memset.p0i8.i64" = Just intr_memset
intrinsics "llvm.stacksave" = Just (False,intr_stacksave)
intrinsics "llvm.stackrestore" = Just (False,intr_stackrestore)
intrinsics "nbis_restrict" = Just (False,intr_restrict)
intrinsics "nbis_assert" = Just (False,intr_assert)
intrinsics "nbis_nondet_i64" = Just (True,intr_nondet 64)
intrinsics "nbis_nondet_i32" = Just (True,intr_nondet 32)
intrinsics "nbis_nondet_i16" = Just (True,intr_nondet 16)
intrinsics "nbis_nondet_i8" = Just (True,intr_nondet 8)
intrinsics "nbis_nondet_u64" = Just (True,intr_nondet 64)
intrinsics "nbis_nondet_u32" = Just (True,intr_nondet 32)
intrinsics "nbis_nondet_u16" = Just (True,intr_nondet 16)
intrinsics "nbis_nondet_u8" = Just (True,intr_nondet 8)
intrinsics "nbis_watch" = Just (False,intr_watch)
intrinsics _ = Nothing

intr_memcpy [(Right to,_),(Right from,_),(Left len,_),_,_] = do
  let len' = case len of
        ConstValue l _ -> Left l
        DirectValue l -> Right l
  loc <- reMemLoc
  nloc <- reNewMemLoc
  reMemInstr (MICopy loc len' from to nloc)
  return Nothing

--intr_memset _ [(Right dest,_),(val,_),(Left (ConstValue len _),_),_,_] = do
--  reError "memset not implemented"

intr_restrict [(Left val,_)] = do
  re <- ask
  lift $ comment " Restriction:"
  case val of
    ConditionValue val _ -> lift $ assert $ (reActivation re) .=>. val
    _ -> do
      let nval = valValue val
          sz = extractAnnotation nval
      lift $ assert $ (reActivation re) .=>. (not' $ nval .==. constantAnn (BitVector 0) sz)
  return Nothing

intr_assert [(Left val,_)] = do
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
  return Nothing

intr_watch ((Left (ConstValue bv _),_):exprs) = do
  re <- ask
  tell $ mempty { reWatchpoints = [(show bv,reActivation re,
                                    [ (tp,valValue val)
                                    | (Left val,tp) <- exprs ])] }
  return Nothing

intr_nondet width [] = do
  v <- lift $ varNamedAnn "nondetVar" width
  return (Just $ Left $ DirectValue v)

intr_stacksave _ = return Nothing
intr_stackrestore _ = return Nothing