module Realization where

import MemoryModel
import Value
import ConditionList
import TypeDesc
import InstrDesc

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
                   , reInstrNums :: Map (Ptr Instruction) Integer
                   }

data RealizationState mem mloc ptr
  = RealizationState { reMem :: mem
                     , reCurMemLoc :: mloc
                     , reNextMemLoc :: mloc
                     , reNextPtr :: ptr
                     , reLocals :: Map (Ptr Instruction) (Either Val ptr)
                     , rePtrTypes :: Map ptr TypeDesc
                     }

data RealizationOutput
  = RealizationOutput { reWatchpoints :: [Watchpoint]
                      , reGuards :: [Guard]
                      }

data RealizationInfo = RealizationInfo { rePossiblePhis :: Set (Ptr BasicBlock)
                                       , rePossibleInputs :: Map (Ptr Instruction) (TypeDesc,Maybe String)
                                       , rePossibleArgs :: Map (Ptr Argument) (TypeDesc,Maybe String)
                                       , rePossibleGlobals :: Set (Ptr GlobalVariable)
                                       , reLocallyDefined :: Set (Ptr Instruction)
                                       , reSuccessors :: Set (Ptr BasicBlock)
                                       , reCalls :: Set (String,Ptr Instruction)
                                       , reReturns :: Bool
                                       , rePotentialErrors :: [ErrorDesc] } deriving (Show)

type RealizationMonad mem mloc ptr
       = RWST (RealizationEnv ptr) RealizationOutput (RealizationState mem mloc ptr) SMT

newtype Realization mem mloc ptr a
          = Realization { runRealization :: RealizationInfo
                                            -> (RealizationInfo,RealizationMonad mem mloc ptr a)
                        }

instance Monoid RealizationOutput where
  mempty = RealizationOutput { reWatchpoints = mempty
                             , reGuards = mempty
                             }
  mappend o1 o2 = RealizationOutput { reWatchpoints = (reWatchpoints o1) `mappend` (reWatchpoints o2)
                                    , reGuards = (reGuards o1) `mappend` (reGuards o2)
                                    }

instance Functor (Realization mem mloc ptr) where
  fmap f (Realization x) = Realization (\info -> let (ninfo,res) = x info
                                                 in (ninfo,fmap f res))

instance Applicative (Realization mem mloc ptr) where
  pure x = reLift (return x)
  (<*>) (Realization f) (Realization x) = Realization (\info -> let (info1,rf) = f info
                                                                    (info2,rx) = x info1
                                                                in (info2,do
                                                                       rrf <- rf
                                                                       rrx <- rx
                                                                       return $ rrf rrx))

reLift :: RealizationMonad mem mloc ptr a -> Realization mem mloc ptr a
reLift act = Realization $ \info -> (info,act)

reInject :: (a -> RealizationMonad mem mloc ptr b)
            -> Realization mem mloc ptr a -> Realization mem mloc ptr b
reInject f x = Realization $ \info -> let (info1,act) = runRealization x info
                                      in (info1,act >>= f)

reDefineVar :: Enum ptr => Ptr Instruction -> String
               -> Realization mem mloc ptr (Either Val ptr) -> Realization mem mloc ptr ()
reDefineVar instr name genval = Realization $ \info -> let (info1,rgen) = runRealization genval info
                                                       in (info1 { reLocallyDefined = Set.insert instr (reLocallyDefined info) },
                                                           do
                                                             val <- rgen
                                                             nval <- case val of
                                                               Left rval -> let nval = valOptimize rval
                                                                            in if valIsComplex nval
                                                                               then lift $ fmap Left $ valCopy name nval
                                                                               else (do
                                                                                        lift $ comment $ name++" = "++show nval
                                                                                        return $ Left nval)
                                                               Right ptr -> return (Right ptr)
                                                             modify (\st -> st { reLocals = Map.insert instr nval (reLocals st) })
                                                          )

reAddSuccessor :: Ptr BasicBlock -> Realization mem mloc ptr ()
reAddSuccessor succ = Realization $ \info -> (info { reSuccessors = Set.insert succ (reSuccessors info) },return ())

reAddCall :: String -> Ptr Instruction -> Realization mem mloc ptr ()
reAddCall fun ret_addr = Realization $ \info -> (info { reCalls = Set.insert (fun,ret_addr) (reCalls info) },return ())

reSetReturn :: Realization mem mloc ptr ()
reSetReturn = Realization $ \info -> (info { reReturns = True },return ())

reNewPtr :: Enum ptr => RealizationMonad mem mloc ptr ptr
reNewPtr = do
  rs <- get
  let ptr = reNextPtr rs
  put $ rs { reNextPtr = succ ptr }
  return ptr

reNewMemLoc :: Enum mloc => RealizationMonad mem mloc ptr mloc
reNewMemLoc = do
  rs <- get
  let loc = reNextMemLoc rs
  put $ rs { reNextMemLoc = succ loc
           , reCurMemLoc = loc }
  return loc

reMemLoc :: RealizationMonad mem mloc ptr mloc
reMemLoc = do
  rs <- get
  return $ reCurMemLoc rs

reMemInstr :: MemoryModel mem mloc ptr
              => MemoryInstruction mloc ptr res
              -> RealizationMonad mem mloc ptr res
reMemInstr instr = do
  env <- ask
  st <- get
  (res,nmem) <- lift $ addInstruction (reMem st)
                (DirectBool $ reActivation env)
                instr
                (rePtrTypes st)
  put $ st { reMem = nmem }
  return res

rePtrType :: Ord ptr => ptr -> TypeDesc -> RealizationMonad mem mloc ptr ()
rePtrType ptr tp = modify (\st -> st { rePtrTypes = Map.insert ptr tp (rePtrTypes st) })

reGetPhi :: (MemoryModel mem mloc ptr,Ord ptr,Enum mloc,Enum ptr)
            => (Ptr BasicBlock,Operand)
            -> Realization mem mloc ptr (Maybe (BoolVal,Either Val ptr))
reGetPhi (blk,instr)
  = Realization $ \info
                  -> let (info1,getArg) = runRealization (argToExpr instr) info
                     in (info1 { rePossiblePhis = Set.insert blk (rePossiblePhis info) },do
                            re <- ask
                            case Map.lookup blk (rePhis re) of
                              Nothing -> return Nothing
                              Just cond -> do
                                val <- getArg
                                return $ Just (DirectBool cond,val))

reUndef :: TypeDesc -> Realization mem mloc ptr (Either Val ptr)
reUndef tp = Realization $ \info -> (info,case tp of
                                        IntegerType w -> do
                                          v <- lift $ varNamedAnn "undef" w
                                          return $ Left $ DirectValue v)

reErrorAnn :: ErrorDesc -> Realization mem mloc ptr ()
reErrorAnn desc = Realization $ \info -> (info { rePotentialErrors = desc:(rePotentialErrors info) },return ())

argToExpr :: (MemoryModel mem mloc ptr,Ord ptr,Enum ptr,Enum mloc)
             => Operand -> Realization mem mloc ptr (Either Val ptr)
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
        IntegerType 1 -> pure $ Left $ ConditionValue (ConstBool (v/=0)) 1
        IntegerType w -> pure $ Left $ ConstValue v w
      ODInstr instr _ name
        -> Realization $ \info -> if Set.member instr (reLocallyDefined info)
                                  then (info,do
                                           rs <- get
                                           case Map.lookup instr (reLocals rs) of
                                             Just res -> return res)
                                  else (info { rePossibleInputs = Map.insert instr (operandType expr,name) (rePossibleInputs info) },do
                                           re <- ask
                                           case Map.lookup (Right instr) (reInputs re) of
                                             Just res -> return res
                                             Nothing -> error $ "Can't find value "++show instr++(case name of
                                                                                                     Nothing -> case Map.lookup instr (reInstrNums re) of
                                                                                                       Just i -> "(%"++show i++")"
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
      ODGetElementPtr ptr idx
        -> let PointerType tpTo = operandType expr
               PointerType tpFrom = operandType ptr
           in reInject (\(ptr',instr) -> reMemInstr instr >> return (Right ptr')) $
              (\(Right val_ptr) val_idx ptr'
               -> (ptr',MIIndex tpFrom tpTo (fmap (\i -> case i of
                                                      Left i' -> i'
                                                  ) val_idx
                                            ) val_ptr ptr')) <$>
              (argToExpr ptr) <*>
              (traverse argToExpr idx) <*>
              (reLift reNewPtr)
      ODBitcast ptr -> let PointerType tpTo = operandType expr
                           PointerType tpFrom = operandType ptr
                       in reInject (\(ptr',instr) -> reMemInstr instr >> return (Right ptr')) $
                          (\(Right val_ptr) ptr' -> (ptr',MICast tpFrom tpTo val_ptr ptr')) <$>
                          (argToExpr ptr) <*>
                          (reLift reNewPtr)
      ODUndef -> reUndef (operandType expr)

data BlockFinalization ptr = Jump (CondList (Ptr BasicBlock))
                           | Return (Maybe (Either Val ptr))
                           | Call String [Either Val ptr] (Ptr Instruction)
                           deriving (Show)

preRealize :: Realization mem mloc ptr a -> (RealizationInfo,RealizationMonad mem mloc ptr a)
preRealize r = runRealization r (RealizationInfo Set.empty Map.empty Map.empty Set.empty Set.empty Set.empty Set.empty False [])

postRealize :: mem -> RealizationEnv ptr -> mloc -> mloc -> ptr -> RealizationMonad mem mloc ptr a
               -> SMT (a,RealizationState mem mloc ptr,RealizationOutput)
postRealize mem env cur_mem next_mem next_ptr act
  = runRWST act env (RealizationState { reMem = mem
                                      , reCurMemLoc = cur_mem
                                      , reNextMemLoc = next_mem
                                      , reNextPtr = next_ptr
                                      , reLocals = Map.empty
                                      , rePtrTypes = Map.empty })

realizeInstructions :: (MemoryModel mem mloc ptr,Ord ptr,Enum ptr,Enum mloc)
                       => [(InstrDesc Operand,Maybe Integer)]
                       -> Realization mem mloc ptr (BlockFinalization ptr)
realizeInstructions [instr] = (\(Just fin) -> fin) <$> realizeInstruction instr
realizeInstructions (instr:instrs) = ((\Nothing -> ()) <$> realizeInstruction instr) *> realizeInstructions instrs

realizeInstruction :: (MemoryModel mem mloc ptr,Ord ptr,Enum ptr,Enum mloc)
                      => (InstrDesc Operand,Maybe Integer)
                      -> Realization mem mloc ptr (Maybe (BlockFinalization ptr))
realizeInstruction (ITerminator (IRet e),_)
  = reSetReturn *> (Just . Return . Just <$> argToExpr e)
realizeInstruction (ITerminator IRetVoid,_) = reSetReturn *> (pure $ Just $ Return Nothing)
realizeInstruction (ITerminator (IBr to),_) = (reAddSuccessor to) *> (pure $ Just $ Jump [(constant True,to)])
realizeInstruction (ITerminator (IBrCond cond ifT ifF),_)
  = (reAddSuccessor ifT) *>
    (reAddSuccessor ifF) *>
    ((\cond' -> case cond' of
         Left (ConditionValue (ConstBool cond'') _) -> Just $ Jump [(constant True,if cond''
                                                                                   then ifT
                                                                                   else ifF)]
         Left v -> Just $ Jump [(valCond v,ifT)
                               ,(not' $ valCond v,ifF)]) <$>
     (argToExpr cond))
realizeInstruction (ITerminator (ISwitch val def args),_)
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
realizeInstruction (assignInstr@(IAssign trg name expr),num)
  = reDefineVar trg rname (reInject getType result) *> pure Nothing
  where
    rname = case name of
      Just name' -> "assign_"++name'
      Nothing -> case num of
        Just num' -> "assign"++show num'
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
        PointerType _ -> reInject (\instr -> do
                                      cond <- reMemInstr instr
                                      return $ Left $ ConditionValue
                                        (case op of
                                            I_EQ -> cond
                                            I_NE -> boolValNot cond) 1
                                  ) $
                         (\(Right lhs') (Right rhs')
                          -> MICompare lhs' rhs') <$>
                         (argToExpr lhs) <*>
                         (argToExpr rhs)
        _ -> (\(Left lhs') (Left rhs') -> Left $ ConditionValue (valIntComp op lhs' rhs') 1) <$>
             (argToExpr lhs) <*>
             (argToExpr rhs)
      IGetElementPtr ptr idx
        -> let PointerType tpFrom = operandType ptr
           in reInject (\(ptr',val_ptr,ridx) -> do
                           structs <- asks reStructs
                           let tpTo = case getInstrType structs assignInstr of
                                 PointerType tp -> tp
                                 tp -> error $ "Result of getelementptr instruction is non-pointer type "++show tp++" "++show assignInstr
                           reMemInstr (MIIndex tpFrom tpTo ridx val_ptr ptr') >> return (Right ptr')) $
              (\(Right val_ptr) val_idx ptr'
               -> (ptr',val_ptr,fmap (\i -> case i of
                                         Left i' -> i'
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
      ILoad arg -> reErrorAnn NullDeref *>
                   reErrorAnn Overrun *>
                   reInject (\(Right ptr) -> do
                                loc <- reMemLoc
                                case operandType arg of
                                  PointerType (PointerType tp) -> do
                                    ptr2 <- reNewPtr
                                    reMemInstr (MILoadPtr loc ptr ptr2)
                                    return $ Right ptr2
                                  PointerType tp -> do
                                    loadRes <- reMemInstr (MILoad loc ptr (bitWidth' tp))
                                    return $ Left loadRes)
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
      ISelect cond ifT ifF
        -> reInject (\(cond',ifTArg,ifFArg)
                     -> case (ifTArg,ifFArg) of
                       (Right ifT',Right ifF')
                         -> if ifT'==ifF'
                            then return (Right ifT')
                            else (do
                                     ptr <- reNewPtr
                                     reMemInstr (MISelect [(cond',ifT')
                                                          ,(boolValNot cond',ifF')] ptr)
                                     return $ Right ptr)
                       (Left ifT',Left ifF')
                         -> return $ Left $ valSwitch [(ifT',cond'),(ifF',cond')]) $
           (\(Left argCond) ifT' ifF' -> (valCond' argCond,ifT',ifF')) <$>
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
realizeInstruction (IStore val to,_)
  = reErrorAnn NullDeref *>
    reErrorAnn Overrun *>
    (reInject (\(ptr,val) -> do
                  loc <- reMemLoc
                  new_loc <- reNewMemLoc
                  case val of
                    Right ptr2 -> reMemInstr (MIStorePtr loc ptr2 ptr new_loc)
                    Left v -> reMemInstr (MIStore loc v ptr new_loc)
                  return Nothing) $
     (\(Right ptr) val -> (ptr,val)) <$>
     (argToExpr to) <*>
     (argToExpr val))
realizeInstruction (ITerminator (ICall trg _ f args),_) = case operandDesc f of
  ODFunction rtp fn argtps -> let args' = traverse (\arg -> (\r -> (r,operandType arg)) <$> argToExpr arg) args
                              in case intrinsics fn rtp argtps of
                                Nothing -> reAddCall fn trg *> ((\args'' -> Just $ Call fn (fmap fst args'') trg) <$> args')
                                Just (def,errs,intr) -> (traverse_ reErrorAnn errs) *>
                                                        (if def
                                                         then reDefineVar trg (fn++"Result") (reInject (\args'' -> do
                                                                                                           Just res <- intr args''
                                                                                                           return res) args')
                                                         else reInject (\args'' -> intr args'' >> return ()) args') *> pure Nothing

isIntrinsic :: String -> TypeDesc -> [TypeDesc] -> Bool
isIntrinsic name rtp argtps
  = case intrinsics name rtp argtps
         :: Maybe (Bool,[ErrorDesc],[(Either Val Int,TypeDesc)] -> (forall mem . MemoryModel mem Int Int => RealizationMonad mem Int Int (Maybe (Either Val Int)))) of
  Nothing -> False
  Just _ -> True

intrinsics :: (Enum ptr,Enum mloc)
              => String -> TypeDesc -> [TypeDesc]
              -> Maybe (Bool,[ErrorDesc],[(Either Val ptr,TypeDesc)] -> (forall mem . MemoryModel mem mloc ptr => RealizationMonad mem mloc ptr (Maybe (Either Val ptr))))
intrinsics "llvm.memcpy.p0i8.p0i8.i64" _ _ = Just (True,[Overrun],intr_memcpy)
intrinsics "llvm.memcpy.p0i8.p0i8.i32" _ _ = Just (True,[Overrun],intr_memcpy)
intrinsics "llvm.memset.p0i8.i32" _ _ = Just (True,[Overrun],intr_memset)
intrinsics "llvm.memset.p0i8.i64" _ _ = Just (True,[Overrun],intr_memset)
intrinsics "llvm.stacksave" _ _ = Just (True,[],intr_stacksave)
intrinsics "llvm.stackrestore" _ _ = Just (False,[],intr_stackrestore)
intrinsics "nbis_restrict" _ _ = Just (False,[],intr_restrict)
intrinsics "nbis_assert" _ _ = Just (False,[Custom],intr_assert)
intrinsics ('n':'b':'i':'s':'_':'n':'o':'n':'d':'e':'t':'_':tp) (IntegerType w) _ = Just (True,[],intr_nondet w)
intrinsics "nbis_watch" _ _ = Just (False,[],intr_watch)
intrinsics "llvm.lifetime.start" _ _ = Just (False,[],intr_lifetime_start)
intrinsics "llvm.lifetime.end" _ _ = Just (False,[],intr_lifetime_end)
intrinsics "strlen" rtp _ = Just (True,[],intr_strlen (bitWidth' rtp))
intrinsics "malloc" _ _ = Just (True,[],intr_malloc)
intrinsics "free" _ _ = Just (False,[DoubleFree],intr_free)
intrinsics _ _ _ = Nothing

intr_memcpy [(Right to,_),(Right from,_),(Left len,_),_,_] = do
  loc <- reMemLoc
  nloc <- reNewMemLoc
  reMemInstr (MICopy loc from to (CopyOpts { copySizeLimit = Just len
                                           , copyStopper = Nothing
                                           , copyMayOverlap = False }) nloc)
  return $ Just (Right to)

intr_memset [(Right dest,_),(Left val,_),(Left len,_),_,_] = do
  loc <- reMemLoc
  nloc <- reNewMemLoc
  reMemInstr (MISet loc dest val len nloc)
  return $ Just (Right dest)

intr_restrict [(Left val,_)] = do
  re <- ask
  lift $ comment " Restriction:"
  case val of
    ConditionValue val _ -> lift $ assert $ (reActivation re) .=>. boolValValue val
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
        ConditionValue val _ -> Just $ (reActivation re) .&&. (not' $ boolValValue val)
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
  loc <- reMemLoc
  res <- reMemInstr (MIStrLen loc ptr)
  return (Just $ Left res)

intr_malloc [(Left sz,_)] = do
  let sz' = case sz of
        ConstValue l _ -> Left l
        DirectValue l -> Right l
  loc <- reMemLoc
  nloc <- reNewMemLoc
  ptr <- reNewPtr
  reMemInstr (MIAlloc loc (IntegerType 8) sz' ptr nloc)
  return (Just $ Right ptr)

intr_free [(Right ptr,_)] = do
  loc <- reMemLoc
  nloc <- reNewMemLoc
  reMemInstr (MIFree loc ptr nloc)
  return Nothing
