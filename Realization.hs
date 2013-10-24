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
import Prelude hiding (foldr,foldl,all)
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
                   , reInputs :: Map (Either (Ptr Argument) (Ptr Instruction)) (Either Val ptr)
                   , rePhis :: Map (Ptr BasicBlock) (SMTExpr Bool)
                   , reStructs :: Map String [TypeDesc]
                   }

data RealizationState mem ptr
  = RealizationState { reCurMemLoc :: mem
                     , reNextMemLoc :: mem
                     , reNextPtr :: ptr
                     , reLocals :: Map (Ptr Instruction) (Either Val ptr)
                     , rePtrTypes :: Map ptr TypeDesc
                     }

data RealizationOutput mem ptr
  = RealizationOutput { reWatchpoints :: [Watchpoint]
                      , reGuards :: [Guard]
                      , reMemInstrs :: [MemoryInstruction mem ptr]
                      }

data RealizationInfo = RealizationInfo { rePossiblePhis :: Set (Ptr BasicBlock)
                                       , rePossibleInputs :: Map (Ptr Instruction) (TypeDesc,Maybe String)
                                       , rePossibleArgs :: Map (Ptr Argument) (TypeDesc,Maybe String)
                                       , rePossibleGlobals :: Set (Ptr GlobalVariable)
                                       , reLocallyDefined :: Set (Ptr Instruction)
                                       , reSuccessors :: Set (Ptr BasicBlock)
                                       , reCalls :: Set (String,Ptr Instruction)
                                       , reReturns :: Bool } deriving (Show)

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

reAddSuccessor :: Ptr BasicBlock -> Realization mem ptr ()
reAddSuccessor succ = Realization $ \info -> (info { reSuccessors = Set.insert succ (reSuccessors info) },return ())

reAddCall :: String -> Ptr Instruction -> Realization mem ptr ()
reAddCall fun ret_addr = Realization $ \info -> (info { reCalls = Set.insert (fun,ret_addr) (reCalls info) },return ())

reSetReturn :: Realization mem ptr ()
reSetReturn = Realization $ \info -> (info { reReturns = True },return ())

reNewPtr :: Enum ptr => RealizationMonad mem ptr ptr
reNewPtr = do
  rs <- get
  let ptr = reNextPtr rs
  put $ rs { reNextPtr = succ ptr }
  return ptr

reNewMemLoc :: Enum mem => RealizationMonad mem ptr mem
reNewMemLoc = do
  rs <- get
  let loc = reNextMemLoc rs
  put $ rs { reNextMemLoc = succ loc
           , reCurMemLoc = loc }
  return loc

reMemLoc :: RealizationMonad mem ptr mem
reMemLoc = do
  rs <- get
  return $ reCurMemLoc rs

reMemInstr :: MemoryInstruction mem ptr -> RealizationMonad mem ptr ()
reMemInstr instr = tell (mempty { reMemInstrs = [instr] })

rePtrType :: Ord ptr => ptr -> TypeDesc -> RealizationMonad mem ptr ()
rePtrType ptr tp = modify (\st -> st { rePtrTypes = Map.insert ptr tp (rePtrTypes st) })

reGetPhi :: (Ord ptr,Enum mem,Enum ptr) => (Ptr BasicBlock,Operand) -> Realization mem ptr (Maybe (SMTExpr Bool,Either Val ptr))
reGetPhi (blk,instr) = Realization $ \info -> let (info1,getArg) = runRealization (argToExpr instr) info
                                              in (info1 { rePossiblePhis = Set.insert blk (rePossiblePhis info) },do
                                                     re <- ask
                                                     case Map.lookup blk (rePhis re) of
                                                       Nothing -> return Nothing
                                                       Just cond -> do
                                                         val <- getArg
                                                         return $ Just (cond,val))

reUndef :: TypeDesc -> Realization mem ptr (Either Val ptr)
reUndef tp = Realization $ \info -> (info,case tp of
                                        IntegerType w -> do
                                          v <- lift $ varNamedAnn "undef" w
                                          return $ Left $ DirectValue v)

argToExpr :: (Ord ptr,Enum ptr,Enum mem) => Operand -> Realization mem ptr (Either Val ptr)
argToExpr expr = reInject getType result
  where
    getType res = case operandType expr of
      PointerType tp -> case res of
        Right ptr -> do
          rePtrType ptr tp
          return res
      _ -> return res
    result = case operandDesc expr of
      ODNull -> let PointerType tp = operandType expr
                in reInject (\(ptr,instr) -> reMemInstr instr >> return (Right ptr)) $
                   liftA (\ptr -> (ptr,MINull tp ptr)) (reLift reNewPtr)
      ODInt v -> case operandType expr of
        IntegerType 1 -> pure $ Left $ ConstCondition (v/=0)
        IntegerType w -> pure $ Left $ ConstValue v w
      ODInstr instr _ name -> Realization $ \info -> if Set.member instr (reLocallyDefined info)
                                                     then (info,do
                                                              rs <- get
                                                              case Map.lookup instr (reLocals rs) of
                                                                Just res -> return res)
                                                     else (info { rePossibleInputs = Map.insert instr (operandType expr,name) (rePossibleInputs info) },do
                                                              re <- ask
                                                              case Map.lookup (Right instr) (reInputs re) of
                                                                Just res -> return res
                                                                Nothing -> error $ "Can't find value "++show instr++(case name of
                                                                                                                        Nothing -> ""
                                                                                                                        Just rname -> "("++rname++")")
                                                          )
      ODGlobal g -> Realization $ \info -> (info { rePossibleGlobals = Set.insert g (rePossibleGlobals info) },do
                                               re <- ask
                                               case Map.lookup g (reGlobals re) of
                                                 Just res -> return $ Right res)
      ODArgument arg -> Realization $ \info -> (info { rePossibleArgs = Map.insert arg (operandType expr,Nothing) (rePossibleArgs info) },do
                                                   re <- ask
                                                   case Map.lookup (Left arg) (reInputs re) of
                                                     Just res -> return res)
      ODGetElementPtr ptr idx -> let PointerType tpTo = operandType expr
                                     PointerType tpFrom = operandType ptr
                                 in reInject (\(ptr',instr) -> reMemInstr instr >> return (Right ptr')) $
                                    (\(Right val_ptr) val_idx ptr' -> (ptr',MIIndex tpFrom tpTo (fmap (\i -> case i of
                                                                                                          Left (ConstValue bv _) -> Left bv
                                                                                                          Left (DirectValue bv) -> Right bv
                                                                                                      ) val_idx
                                                                                                ) val_ptr ptr')) <$>
                                    (argToExpr ptr) <*>
                                    (traverse argToExpr idx) <*>
                                    (reLift reNewPtr)
      ODUndef -> reUndef (operandType expr)

data BlockFinalization ptr = Jump (CondList (Ptr BasicBlock))
                           | Return (Maybe (Either Val ptr))
                           | Call String [Either Val ptr] (Ptr Instruction)
                           deriving (Show)

preRealize :: Realization mem ptr a -> (RealizationInfo,RealizationMonad mem ptr a)
preRealize r = runRealization r (RealizationInfo Set.empty Map.empty Map.empty Set.empty Set.empty Set.empty Set.empty False)

postRealize :: RealizationEnv ptr -> mem -> mem -> ptr -> RealizationMonad mem ptr a -> SMT (a,RealizationState mem ptr,RealizationOutput mem ptr)
postRealize env cur_mem next_mem next_ptr act = runRWST act env (RealizationState { reCurMemLoc = cur_mem
                                                                                  , reNextMemLoc = next_mem
                                                                                  , reNextPtr = next_ptr
                                                                                  , reLocals = Map.empty
                                                                                  , rePtrTypes = Map.empty })

realizeInstructions :: (Ord ptr,Enum ptr,Enum mem) => [InstrDesc Operand] -> Realization mem ptr (BlockFinalization ptr)
realizeInstructions [instr] = (\(Just fin) -> fin) <$> realizeInstruction instr
realizeInstructions (instr:instrs) = ((\Nothing -> ()) <$> realizeInstruction instr) *> realizeInstructions instrs

realizeInstruction :: (Ord ptr,Enum ptr,Enum mem) => InstrDesc Operand -> Realization mem ptr (Maybe (BlockFinalization ptr))
realizeInstruction (ITerminator (IRet e)) = reSetReturn *> (Just . Return . Just <$> argToExpr e)
realizeInstruction (ITerminator IRetVoid) = reSetReturn *> (pure $ Just $ Return Nothing)
realizeInstruction (ITerminator (IBr to)) = (reAddSuccessor to) *> (pure $ Just $ Jump [(constant True,to)])
realizeInstruction (ITerminator (IBrCond cond ifT ifF))
  = (reAddSuccessor ifT) *>
    (reAddSuccessor ifF) *>
    ((\cond' -> case cond' of
         Left (ConstCondition cond'') -> Just $ Jump [(constant True,if cond''
                                                                     then ifT
                                                                     else ifF)]
         Left v -> Just $ Jump [(valCond v,ifT)
                               ,(not' $ valCond v,ifF)]) <$>
     (argToExpr cond))
realizeInstruction (ITerminator (ISwitch val def args))
  = foldl (\cur (_,to) -> cur *> reAddSuccessor to) (reAddSuccessor def) args *>
    ((\val' args' -> case val' of
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
     (traverse (\(cmp_v,to) -> (\r -> (r,to)) <$> (argToExpr cmp_v)) args))
realizeInstruction assignInstr@(IAssign trg name expr)
  = reDefineVar trg rname (reInject getType result) *> pure Nothing
  where
    rname = case name of
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
    getType res = do
      structs <- asks reStructs
      case getInstrType structs assignInstr of
        PointerType tp -> case res of
          Right ptr -> rePtrType ptr tp >> return res
        _ -> return res
    result = case expr of
      IBinaryOperator op lhs rhs -> (\(Left lhs') (Left rhs') -> Left $ valBinOp op lhs' rhs') <$>
                                    (argToExpr lhs) <*>
                                    (argToExpr rhs)
      IICmp op lhs rhs -> case operandType lhs of
        PointerType _ -> reInject (\(val,instr) -> reMemInstr instr >> return val) $
                         (\(Right lhs') (Right rhs') cond
                          -> (Left $ ConditionValue (case op of
                                                        I_EQ -> cond
                                                        I_NE -> not' cond) 1,MICompare lhs' rhs' cond)) <$>
                         (argToExpr lhs) <*>
                         (argToExpr rhs) <*>
                         (reLift $ lift $ varNamed "PtrCompare")
        _ -> (\(Left lhs') (Left rhs') -> Left $ valIntComp op lhs' rhs') <$>
             (argToExpr lhs) <*>
             (argToExpr rhs)
      IGetElementPtr ptr idx -> let PointerType tpFrom = operandType ptr
                                in reInject (\(ptr',val_ptr,ridx) -> do
                                                structs <- asks reStructs
                                                let tpTo = case getInstrType structs assignInstr of
                                                      PointerType tp -> tp
                                                      tp -> error $ "Result of getelementptr instruction is non-pointer type "++show tp++" "++show assignInstr
                                                reMemInstr (MIIndex tpFrom tpTo ridx val_ptr ptr') >> return (Right ptr')) $
                                   (\(Right val_ptr) val_idx ptr' -> (ptr',val_ptr,fmap (\i -> case i of
                                                                                            Left (ConstValue bv _) -> Left bv
                                                                                            Left (DirectValue bv) -> Right bv
                                                                                        ) val_idx)) <$>
                                   (argToExpr ptr) <*>
                                   (traverse argToExpr idx) <*>
                                   (reLift reNewPtr)
      IPhi args -> reInject (\args' -> case args' of
                                Left [(_,v)] -> return (Left v)
                                Left vs -> return $ Left $ valSwitch (fmap (\(c,v) -> (v,c)) vs)
                                Right ps@((_,p):ps') -> if all (\(_,p') -> p==p') ps'
                                                        then return (Right p)
                                                        else (do
                                                                 ptr <- reNewPtr
                                                                 reMemInstr (MISelect ps ptr)
                                                                 return $ Right ptr)
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
                                    reMemInstr (MILoadPtr loc ptr ptr2)
                                    return $ Right ptr2
                                  PointerType tp -> do
                                    loadRes <- lift $ varNamedAnn "LoadRes" (bitWidth' tp)
                                    reMemInstr (MILoad loc ptr loadRes)
                                    return $ Left $ DirectValue loadRes)
                   (argToExpr arg)
      IBitCast tp_to arg -> reInject (\(Right ptr) -> do
                                         let PointerType tp_from = operandType arg
                                         ptr' <- reNewPtr
                                         reMemInstr (MICast tp_from tp_to ptr ptr')
                                         return $ Right ptr')
                            (argToExpr arg)
      ISExt tp arg -> (\arg' -> case arg' of
                          Left (ConditionValue v w) -> Left $ ConditionValue v (bitWidth' (operandType arg))
                          Left arg'' -> let v = valValue arg''
                                            w = bitWidth' (operandType arg)
                                            d = (bitWidth' tp) - w
                                            nv = bvconcat (ite (bvslt v (constantAnn (BitVector 0) w::SMTExpr (BitVector BVUntyped)))
                                                           (constantAnn (BitVector (-1)) d::SMTExpr (BitVector BVUntyped))
                                                           (constantAnn (BitVector 0) (fromIntegral d))) v
                                        in Left $ DirectValue nv) <$>
                      (argToExpr arg)
      IZExt tp arg -> (\arg' -> case arg' of
                          Left (ConditionValue v w) -> Left $ ConditionValue v (bitWidth' (operandType arg))
                          Left arg'' -> let v = valValue arg''
                                            w = bitWidth' (operandType arg)
                                            d = (bitWidth' tp) - w
                                            nv = bvconcat (constantAnn (BitVector 0) (fromIntegral d)::SMTExpr (BitVector BVUntyped)) v
                                        in Left $ DirectValue nv) <$>
                      (argToExpr arg)
      ITrunc tp arg -> (\arg' -> case arg' of
                           Left (ConditionValue v w) -> Left $ ConditionValue v (bitWidth' tp)
                           Left arg'' -> let v = valValue arg''
                                             w = bitWidth' (operandType arg)
                                             d = w - (bitWidth' tp)
                                             nv = bvextract' 0 (bitWidth' tp) v
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
                                          (Right ifT',Right ifF') -> if ifT'==ifF'
                                                                     then return (Right ifT')
                                                                     else (do
                                                                              ptr <- reNewPtr
                                                                              reMemInstr (MISelect [(cond',ifT'),(not' cond',ifF')] ptr)
                                                                              return $ Right ptr)
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
      _ -> error $ "Unknown expression: "++show expr
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
                              in case intrinsics fn rtp argtps of
                                Nothing -> reAddCall fn trg *> ((\args'' -> Just $ Call fn (fmap fst args'') trg) <$> args')
                                Just (def,intr) -> (if def
                                                    then reDefineVar trg (fn++"Result") (reInject (\args'' -> do
                                                                                                      Just res <- intr args''
                                                                                                      return res) args')
                                                    else reInject (\args'' -> intr args'' >> return ()) args') *> pure Nothing

isIntrinsic :: String -> TypeDesc -> [TypeDesc] -> Bool
isIntrinsic name rtp argtps = case intrinsics name rtp argtps :: Maybe (Bool,[(Either Val Int,TypeDesc)] -> RealizationMonad Int Int (Maybe (Either Val Int))) of
  Nothing -> False
  Just _ -> True

intrinsics :: (Enum ptr,Enum mem) => String -> TypeDesc -> [TypeDesc] -> Maybe (Bool,[(Either Val ptr,TypeDesc)] -> RealizationMonad mem ptr (Maybe (Either Val ptr)))
intrinsics "llvm.memcpy.p0i8.p0i8.i64" _ _ = Just (True,intr_memcpy)
intrinsics "llvm.memcpy.p0i8.p0i8.i32" _ _ = Just (True,intr_memcpy)
--intrinsics "llvm.memset.p0i8.i32" = Just intr_memset
--intrinsics "llvm.memset.p0i8.i64" = Just intr_memset
intrinsics "llvm.stacksave" _ _ = Just (True,intr_stacksave)
intrinsics "llvm.stackrestore" _ _ = Just (False,intr_stackrestore)
intrinsics "nbis_restrict" _ _ = Just (False,intr_restrict)
intrinsics "nbis_assert" _ _ = Just (False,intr_assert)
intrinsics "nbis_nondet_i64" _ _ = Just (True,intr_nondet 64)
intrinsics "nbis_nondet_i32" _ _ = Just (True,intr_nondet 32)
intrinsics "nbis_nondet_i16" _ _ = Just (True,intr_nondet 16)
intrinsics "nbis_nondet_i8" _ _ = Just (True,intr_nondet 8)
intrinsics "nbis_nondet_u64" _ _ = Just (True,intr_nondet 64)
intrinsics "nbis_nondet_u32" _ _ = Just (True,intr_nondet 32)
intrinsics "nbis_nondet_u16" _ _ = Just (True,intr_nondet 16)
intrinsics "nbis_nondet_u8" _ _ = Just (True,intr_nondet 8)
intrinsics "nbis_watch" _ _ = Just (False,intr_watch)
intrinsics "llvm.lifetime.start" _ _ = Just (False,intr_lifetime_start)
intrinsics "llvm.lifetime.end" _ _ = Just (False,intr_lifetime_end)
intrinsics "strlen" rtp _ = Just (True,intr_strlen (bitWidth' rtp))
intrinsics _ _ _ = Nothing

intr_memcpy [(Right to,_),(Right from,_),(Left len,_),_,_] = do
  let len' = case len of
        ConstValue l _ -> Left l
        DirectValue l -> Right l
  loc <- reMemLoc
  nloc <- reNewMemLoc
  reMemInstr (MICopy loc from to (CopyOpts { copySizeLimit = Just len'
                                           , copyStopper = Nothing
                                           , copyMayOverlap = False }) nloc)
  return $ Just (Right to)

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

intr_stacksave _ = do
  ptr <- reNewPtr
  reMemInstr (MINull (IntegerType 8) ptr)
  return (Just $ Right ptr)
intr_stackrestore _ = return Nothing

intr_lifetime_start _ = return Nothing
intr_lifetime_end _ = return Nothing

intr_strlen width [(Right ptr,_)] = do
  res <- lift $ varNamedAnn "strlen" width
  loc <- reMemLoc
  reMemInstr (MIStrLen loc ptr res)
  return (Just $ Left $ DirectValue res)
