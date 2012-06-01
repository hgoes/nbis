{-# LANGUAGE DeriveDataTypeable,TypeFamilies,FlexibleContexts,RankNTypes,OverloadedStrings #-}
module Main where

import MemoryModel
import MemoryModel.Untyped
import MemoryModel.UntypedBlocks
import MemoryModel.Typed
import MemoryModel.Plain
import Language.SMTLib2
import Language.SMTLib2.Internals
import Data.Typeable
import Control.Monad.Trans
import System.Environment (getArgs)
import Data.List as List (genericLength,genericReplicate,genericSplitAt,zip4,zipWith4,zipWith5,null,lookup)
import Data.Map as Map hiding (foldl,foldr,(!),mapMaybe)
import Data.Set as Set hiding (foldl,foldr)
import qualified Data.Bitstream as BitS
import LLVM.Core
import LLVM.Pretty
import qualified LLVM.FFI.Core as FFI
import Debug.Trace
import Prelude hiding (foldl,concat,mapM_,any,foldr,mapM,foldl1)
import Data.Foldable
import Data.Traversable
import System.Console.GetOpt
import System.Exit
import Control.Monad (when)
import Data.Maybe (mapMaybe,maybeToList,catMaybes)
import Data.Bits as Bits
import Foreign.Ptr
import Foreign.Storable
import qualified Foreign.Marshal.Alloc as Alloc
import Text.Show
import Data.Monoid

type Watchpoint = (String,SMTExpr Bool,[(TypeDesc,SMTExpr BitVector)])

type Guard = (ErrorDesc,SMTExpr Bool)

(!) :: (Show k,Ord k) => Map k a -> k -> a
(!) mp k = case Map.lookup k mp of
             Nothing -> error $ "Couldn't find key "++show k++" in "++show (Map.keys mp)
             Just r -> r

data Val m = ConstValue { asConst :: BitVector }
           | DirectValue { asValue :: SMTExpr BitVector }
           | PointerValue { asPointer :: Pointer m }
           | ConditionValue { asCondition :: SMTExpr Bool
                            , conditionWidth :: Integer }
           | ConstCondition { asConstCondition :: Bool }
             deriving (Typeable)

instance Show (Val m) where
  show (ConstValue c) = show c
  show (DirectValue dv) = show dv
  show (PointerValue _) = "<pointer>"
  show (ConditionValue c _) = show c
  show (ConstCondition c) = show c

type RealizationQueue = [(String,String,Integer,Integer)]

valEq :: MemoryModel m => m -> Val m -> Val m -> SMTExpr Bool
valEq mem (ConstValue x) (ConstValue y) = if x==y then constant True else constant False
valEq mem (ConstValue x) (DirectValue y) = y .==. constantAnn x (BitS.length x)
valEq mem (DirectValue x) (ConstValue y) = x .==. constantAnn y (BitS.length y)
valEq mem (DirectValue v1) (DirectValue v2) = v1 .==. v2
valEq mem (PointerValue p1) (PointerValue p2) = memPtrEq mem p1 p2
valEq mem (ConditionValue v1 _) (ConditionValue v2 _) = v1 .==. v2
valEq mem (ConditionValue v1 w) (ConstValue v2) = if v2 == BitS.fromNBits w (1::Integer)
                                                  then v1
                                                  else not' v1
valEq mem (ConstValue v1) (ConditionValue v2 w) = if v1 == BitS.fromNBits w (1::Integer)
                                                  then v2
                                                  else not' v2
valEq mem (ConditionValue v1 w) (DirectValue v2) = v1 .==. (v2 .==. (constantAnn (BitS.fromNBits w (1::Integer)) (fromIntegral w)))
valEq mem (DirectValue v2) (ConditionValue v1 w) = v1 .==. (v2 .==. (constantAnn (BitS.fromNBits w (1::Integer)) (fromIntegral w)))
valEq mem (ConstCondition x) (ConstCondition y) = constant (x == y)
valEq mem (ConstCondition x) (ConditionValue y _) = if x then y else not' y
valEq mem (ConditionValue x _) (ConstCondition y) = if y then x else not' x

valSwitch :: MemoryModel m => m -> TypeDesc -> [(Val m,SMTExpr Bool)] -> SMT (Val m)
valSwitch mem _ [(val,_)] = return val
valSwitch mem (TDPtr _) choices = do
  res <- memPtrSwitch mem [ (ptr,cond) | (PointerValue ptr,cond) <- choices ]
  return $ PointerValue res
valSwitch mem tp choices = return $ DirectValue $ mkSwitch choices
  where
    mkSwitch [(val,cond)] = valValue val
    mkSwitch ((val,cond):rest) = ite cond (valValue val) (mkSwitch rest)

valCond :: Val m -> SMTExpr Bool
valCond (ConstValue x) = case BitS.unpack x of
  [x'] -> constant x'
  _ -> error "A constant of bit-length > 1 is used in a condition"
valCond (DirectValue x) = x .==. (constantAnn (BitS.pack [True]) 1)
valCond (ConditionValue x _) = x
valCond (ConstCondition x) = constant x

valValue :: Val m -> SMTExpr BitVector
valValue (ConstValue x) = constantAnn x (BitS.length x)
valValue (DirectValue x) = x
valValue (ConditionValue x w) = ite x (constantAnn (BitS.fromNBits w (1::Integer)) (fromIntegral w)) (constantAnn (BitS.fromNBits w (0::Integer)) (fromIntegral w))
valValue (ConstCondition x) = constantAnn (BitS.pack [x]) 1

newValue :: MemoryModel mem => mem -> TypeDesc -> SMT (Val mem)
newValue mem (TDPtr tp) = do
  ptr <- memPtrNew mem tp
  return (PointerValue ptr)
newValue _ tp = do
  v <- varAnn (fromIntegral $ bitWidth tp)
  return (DirectValue v)

data RealizedBlock m = RealizedBlock { rblockActivation :: SMTExpr Bool
                                     , rblockMemoryOut  :: m
                                     , rblockOutput     :: Map String (Val m)
                                     , rblockJumps      :: Map StateId (SMTExpr Bool)
                                     , rblockReturns    :: Maybe (Maybe (Val m))
                                     }

data RealizationState m = RealizationState { alreadyRealized :: Map StateId (RealizedBlock m)
                                           , realizationQueue :: [QueuedState m]
                                           , currentInvocationLevels :: Map String Integer
                                           }

data StateId = StateId { stateFunction :: String
                       , stateBlock :: String
                       , stateSubblock :: Integer
                       , stateInvocationLevel :: Integer
                       , stateRecursionLevel :: Integer
                       } deriving (Eq,Ord)

instance Show StateId where
  show st = stateFunction st ++ "->" 
            ++ stateBlock st ++ "."
            ++ show (stateSubblock st)
            ++(case stateInvocationLevel st of
                  0 -> ""
                  n -> "[i"++show n++"]")
            ++(case stateRecursionLevel st of
                  0 -> ""
                  n -> "[r"++show n++"]")

data QueuedState m = QueuedState { qstateId :: StateId
                                 , qstateArguments :: Map String (Val m)
                                 , qstateStack :: [(StateId,String)]
                                 }

localPredecessor :: Map String (Map String Integer) -> String -> Integer -> StateId -> Maybe StateId
localPredecessor order blk sub st
  = let nlvl = if (order!(stateFunction st)!blk) <= (order!(stateFunction st)!(stateBlock st))
               then stateRecursionLevel st
               else stateRecursionLevel st - 1
    in if nlvl >= 0
       then Just $ st { stateBlock = blk
                      , stateSubblock = sub
                      , stateRecursionLevel = nlvl
                      }
       else Nothing

globalSuccessor :: Map String (Map String Integer) -> String -> String -> Integer -> StateId -> RealizationState m -> (StateId,RealizationState m)
globalSuccessor order f blk sub st real 
  = if f == stateFunction st
    then (st { stateBlock = blk
             , stateSubblock = sub
             , stateRecursionLevel = if (order!f!blk) > (order!f!(stateBlock st)) || (blk == stateBlock st && sub > stateSubblock st)
                                     then stateRecursionLevel st
                                     else stateRecursionLevel st + 1
             },real)
    else (let (lvl,nm) = case Map.lookup f (currentInvocationLevels real) of
                Nothing -> (0,Map.insert f 0 (currentInvocationLevels real))
                Just r -> (r,Map.insert f (r+1) (currentInvocationLevels real))
          in (StateId { stateFunction = f
                      , stateBlock = blk
                      , stateSubblock = sub
                      , stateRecursionLevel = 0
                      , stateInvocationLevel = lvl },real { currentInvocationLevels = nm }))

queueState :: Map String (Map String Integer) -> QueuedState m -> RealizationState m -> RealizationState m
queueState order ins st = if Map.member (qstateId ins) (alreadyRealized st) 
                          then st
                          else st { realizationQueue = queue' (realizationQueue st) }
  where
    fun_in = stateFunction $ qstateId ins
    blk_in = stateBlock $ qstateId ins
    queue' [] = [ins]
    queue' (q@(x:xs)) 
      = case mconcat [compare (stateRecursionLevel $ qstateId ins) (stateRecursionLevel $ qstateId x)
                     ,compare (stateInvocationLevel $ qstateId ins) (stateInvocationLevel $ qstateId x)
                     ,compare (stateFunction $ qstateId ins) (stateFunction $ qstateId x)
                     ,compare (order!fun_in!blk_in) (order!(stateFunction (qstateId x))!(stateBlock $ qstateId x))
                     ,compare (stateSubblock $ qstateId ins) (stateSubblock $ qstateId x)
                     ] of
          EQ -> q --error "Internal error: Queuing an already queued state"
          LT -> ins:q
          GT -> x:queue' xs

newInvocation :: String -> RealizationState m -> (Integer,RealizationState m)
newInvocation fname st 
  = let lvl = Map.findWithDefault 0 fname (currentInvocationLevels st)
    in (lvl,st { currentInvocationLevels = Map.insert fname (lvl+1) (currentInvocationLevels st) })

getCurrentLevel :: String -> RealizationState m -> Integer
getCurrentLevel fname st = Map.findWithDefault 0 fname (currentInvocationLevels st)

realizationDone :: RealizationState m -> Bool
realizationDone st = List.null (realizationQueue st)

popState :: RealizationState m -> (QueuedState m,RealizationState m)
popState st = (head (realizationQueue st),st { realizationQueue = tail (realizationQueue st) })

stepRealization :: MemoryModel m => [TypeDesc]
                   -> m
                   -> Map String (Pointer m)
                   -> Map String ([(String,TypeDesc)],TypeDesc,[(String,[(Integer,[Instruction])])])
                   -> Map String (Map String (Map Integer BlockSig))
                   -> Map String TypeDesc
                   -> Map String (Map String Integer)
                   -> RealizationState m -> SMT ([Watchpoint],[Guard],RealizationState m)
stepRealization tps init_mem globals prog sigs preds order st
  = let (qst,nxt) = popState st
        sig_fun = case Map.lookup (stateFunction $ qstateId qst) sigs of
          Nothing -> error $ "Internal error: Can't find signature for function "++stateFunction (qstateId qst)
          Just r -> r
        sig = case (Map.lookup (stateBlock $ qstateId qst) sig_fun >>= Map.lookup (stateSubblock $ qstateId qst)) of
          Nothing -> error $ "Internal error: No signature found for block "++stateBlock (qstateId qst)++"."++show (stateSubblock $ qstateId qst)++" of "++stateFunction (qstateId qst)
          Just r -> r
        fun_blks = case Map.lookup (stateFunction $ qstateId qst) prog of
          Nothing -> error $ "Internal error: Function "++stateFunction (qstateId qst)++" not found in program"
          Just (_,_,r) -> r
        instrs = case List.lookup (stateBlock $ qstateId qst) fun_blks of
          Nothing -> error $ "Internal error: Block "++stateBlock (qstateId qst)++" of function "++stateFunction (qstateId qst)++" not found in program"
          Just sub_blks -> case List.lookup (stateSubblock $ qstateId qst) sub_blks of
            Nothing -> error $ "Internal error: Block "++stateBlock (qstateId qst)++" of function "++stateFunction (qstateId qst)++" not found in program"
            Just r -> r
        (_,_,((start_blk,_):_)) = prog!(stateFunction (qstateId qst))
        froms = [ (rblockActivation realized,rblockMemoryOut realized,realized_cond)
                | from <- (catMaybes $ fmap (\(blk,sblk) 
                                             -> localPredecessor order blk sblk (qstateId qst)) $ 
                           Set.toList (blockOrigins sig))
                          ++ (if stateBlock (qstateId qst) == start_blk && stateRecursionLevel (qstateId qst) == 0
                              then case qstateStack qst of
                                [] -> []
                                (prev,_):_ -> [prev]
                              else []),
                  let sig_from = case (Map.lookup (stateBlock from) sig_fun >>= Map.lookup (stateSubblock from)) of
                        Nothing -> error $ "Internal error: Can't find origin block "++stateBlock from++"."++show (stateSubblock from)++" for "++stateBlock (qstateId qst)
                        Just r -> r,
                  realized <- maybeToList $ Map.lookup from (alreadyRealized st),
                  realized_cond <- maybeToList $ Map.lookup (qstateId qst) (rblockJumps realized)
                ]
    in do
      act <- var
      case froms of
        [] -> assert act
        _ -> assert $ act .==. or' [ and' [act',cond] | (act',_,cond) <- froms ]
      mem <- case froms of
        [] -> return init_mem
        _ -> memSwitch [ (mem,and' [act',cond])  | (act',mem,cond) <- froms ]
      let inps_simple = Map.fromList $ mapMaybe (\(iname,(from_blk,from_sub,expr,tp)) -> do
                                                    from <- localPredecessor order from_blk from_sub (qstateId qst)
                                                    inp_block <- case Map.lookup from (alreadyRealized nxt) of
                                                      Nothing -> Map.lookup (from { stateRecursionLevel = 0 }) (alreadyRealized nxt)
                                                      Just blk -> return blk
                                                    return $ (iname,argToExpr expr (rblockOutput inp_block) mem)
                                              ) (Map.toList $ blockInputsSimple sig)
          inp_global = fmap PointerValue globals
          inp0 = Map.union inps_simple inp_global
      inps_phi <- mapM (\(iname,(from,tp)) 
                        -> do
                          let choices = mapMaybe (\(blk,subblk,arg) 
                                                  -> do
                                                    case arg of
                                                      Expr { exprDesc = EDUndef } -> Nothing
                                                      _ -> return ()
                                                    from_st <- localPredecessor order blk subblk (qstateId qst)
                                                    realized_from <- Map.lookup from_st (alreadyRealized nxt)
                                                    realized_cond <- Map.lookup (qstateId qst)
                                                                     (rblockJumps realized_from)
                                                    return (argToExpr arg inp0 mem,
                                                            and' [rblockActivation realized_from,realized_cond])
                                                 ) from
                          res <- valSwitch mem tp choices
                          return (iname,res)
                       ) (Map.toList $ blockInputsPhi sig)
      let inps = Map.union inp0 (Map.fromList inps_phi)
      comment $ "Block "++show (qstateId qst)
      (mem',values',res,watch,guards) <- realizeBlock (stateFunction $ qstateId qst) (stateBlock $ qstateId qst) (stateSubblock $ qstateId qst) instrs act mem False inps preds [] []
      (jumps,succ,ret,nxt') <- case res of
        Return r -> case qstateStack qst of
          [] -> return (Map.empty,[],Just r,nxt)
          (st,res):stack -> let nst = st { stateSubblock = (stateSubblock st) + 1 }
                            in return (Map.singleton nst (constant True),
                                       [ QueuedState { qstateId = nst
                                                     , qstateArguments = case r of
                                                       Nothing -> Map.empty
                                                       Just r' -> Map.singleton res r'
                                                     , qstateStack = stack } ],Nothing,nxt)
        Jump jmps -> let (nxt',jmps') = mapAccumL (\cnxt ((fn,blk,sub),act) -> let (st,cnxt') = globalSuccessor order fn blk sub (qstateId qst) cnxt
                                                                               in (cnxt',(st,act))) nxt jmps
                     in do
                       jmps'' <- translateJumps jmps'
                       return (jmps'',[ QueuedState { qstateId = st
                                                    , qstateArguments = Map.empty 
                                                    , qstateStack = qstateStack qst }
                                      | (st,_) <- jmps' ],Nothing,nxt')
        Call fn args ret -> let (arg_tps,_,_) = prog!fn
                                rargs = Map.fromList (zipWith (\arg (name,_) -> (name,arg)) args arg_tps)
                                (lvl,nxt') = newInvocation fn nxt
                                (_,_,(start_blk,_):_) = prog!fn
                                nst = StateId { stateFunction = fn
                                              , stateBlock = start_blk
                                              , stateSubblock = 0
                                              , stateInvocationLevel = lvl
                                              , stateRecursionLevel = 0
                                              }
                            in return (Map.singleton nst (constant True),
                                       [ QueuedState { qstateId = nst
                                                     , qstateArguments = rargs
                                                     , qstateStack = (qstateId qst,ret):(qstateStack qst) } ],
                                       Nothing,nxt')
      let nxt'' = foldl (\cnxt st -> queueState order st cnxt) nxt' succ
      --trace ("Realized state "++show (qstateId qst)) (return ())
      return (watch,guards,
              nxt'' { alreadyRealized = Map.insert (qstateId qst) 
                                        (RealizedBlock { rblockActivation = act
                                                       , rblockMemoryOut = case mem' of
                                                         Nothing -> mem
                                                         Just nmem -> nmem
                                                       , rblockOutput = values'
                                                       , rblockJumps = jumps
                                                       , rblockReturns = ret
                                                       }) (alreadyRealized nxt'')
                   })


translateProgram :: (MemoryModel mem) 
                    => ProgDesc -> String -> (ErrorDesc -> Bool) -> (ErrorDesc -> [(String,[(TypeDesc,BitVector)])] -> SMT a) -> SMT (mem,Maybe a)
translateProgram (program,globs) entry_point check_err f = do
  let alltps_funs = foldl (\tps (args,rtp,blocks) 
                           -> let tpsArgs = allTypesArgs args
                                  tpsBlocks = allTypesBlks blocks
                              in tps++tpsArgs++tpsBlocks) [] program
      alltps_globs = foldl (\tps (TDPtr tp,_,_) -> tp:tps) [] globs
      alltps = alltps_funs++alltps_globs
      (args,rtp,blks) = program!entry_point
      preds = predictMallocUse $ concat [ instrs | (fname,(_,_,blks)) <- Map.toList program, (blk,subs) <- blks, (sub,instrs) <- subs ]
      order = orderMap (program,globs)
  --liftIO $ print globs
  (arg_vals,globals,mem_in) <- prepareEnvironment alltps args globs
  let (_,_,(start_blk,_):_) = program!entry_point
      startq = QueuedState { qstateId = StateId { stateFunction = entry_point
                                                , stateBlock = start_blk
                                                , stateSubblock = 0
                                                , stateInvocationLevel = 0
                                                , stateRecursionLevel = 0
                                                }
                           , qstateArguments = Map.fromList $ zipWith (\(name,_) arg -> (name,arg)) args arg_vals
                           , qstateStack = []
                           }
      start = RealizationState { alreadyRealized = Map.empty
                               , realizationQueue = [ startq ]
                               , currentInvocationLevels = Map.singleton entry_point 1
                               }
      sigs = fmap (\(args,rtp,body) -> let blkmp = mkVarBlockMap (fmap fst args) [ name | (name,_) <- Map.toList globs ] body
                                       in mkBlockSigs blkmp body
                  ) program
  {-liftIO $ putStrLn $ unlines $ concat [ [fn]++concat [ ["  "++blk]++
                                                        concat [ fmap ("    "++) $ showBlockSig (show sub) sig 
                                                               | (sub,sig) <- Map.toList subs ]
                                                      | (blk,subs) <- Map.toList sig ]
                                       | (fn,sig) <- Map.toList sigs ]-}
  verify alltps mem_in globals program sigs preds order [] start
  where
    verify alltps mem_in globals program sigs preds order watch cur 
      = if realizationDone cur
        then return (mem_in,Nothing)
        else (do
                 (watch',guard',ncur) <- stepRealization alltps mem_in globals program sigs preds order cur
                 let nwatch = watch++watch'
                     check [] = verify alltps mem_in globals program sigs preds order nwatch ncur
                     check ((err,cond):errs) 
                       = if check_err err
                         then (do
                                  liftIO $ putStrLn $ "Checking for error "++show err
                                  r <- stack $ do
                                    assert cond
                                    active <- checkSat
                                    if active
                                      then (do
                                               wres <- mapM (\(name,cond',args) -> do
                                                                wactive <- getValue cond'
                                                                if wactive
                                                                  then (do
                                                                           args' <- mapM (\(tp,arg) -> do
                                                                                             r <- getValue' (fromIntegral $ bitWidth tp) arg
                                                                                             return (tp,r)) args
                                                                           return $ Just (name,args'))
                                                                  else return Nothing) nwatch
                                               res <- f err (catMaybes wres)
                                               return $ Just res)
                                      else return Nothing
                                  case r of
                                    Nothing -> check errs
                                    Just res -> return (mem_in,Just res))
                         else check errs
                 check guard')

translateJumps :: Ord a => [(a,Maybe (SMTExpr Bool))] -> SMT (Map a (SMTExpr Bool))
translateJumps = translateJumps' []
  where
    translateJumps' [] [(from,Nothing)] = return $ Map.singleton from (constant True)
    translateJumps' _ [] = return Map.empty
    translateJumps' pre ((from,cond):rest) = do
      (npre,rcond) <- case cond of
        Nothing -> return (pre,case pre of
                              [] -> constant True
                              _ -> and' $ fmap not' pre)
        Just cond' -> do
          v <- var
          assert $ v .==. cond'
          return (v:pre,case pre of
                     [] -> v
                     _ -> and' (v:(fmap not' pre)))
      mp <- translateJumps' npre rest
      return $ Map.insert from rcond mp
        
showBlockSig :: String -> BlockSig -> [String]
showBlockSig name sig 
  = name:(if Map.null (blockInputsSimple sig) then []
          else "  inputs":[ "    " ++ iname ++ "("++ifrom++"."++show inum++") : "++show tp++" ~> "++ show expr | (iname,(ifrom,inum,expr,tp)) <- Map.toList (blockInputsSimple sig) ]) ++
    (if Map.null (blockInputsPhi sig) then [] 
     else "  phis":(concat [ ("    "++iname++" : "++show itp): 
                             [ "    "++(fmap (const ' ') iname)++" | "++ 
                               from ++ "." ++ show from_sub ++ " ~> "++show inf
                             | (from,from_sub,inf) <- ifrom
                             ] | (iname,(ifrom,itp)) <- Map.toList (blockInputsPhi sig) ])) ++
    (if Set.null (blockGlobals sig) then [] else "  globals":[ "    "++name | name <- Set.toList (blockGlobals sig) ]) ++
    (if Map.null (blockOutputs sig) then [] else "  outputs":[ "    "++oname++" : "++show otp | (oname,otp) <- Map.toList (blockOutputs sig) ]) ++
    (if Map.null (blockCalls sig) then [] else  "  calls":[ "    "++cname++" : "++concat [ show atp++" -> " | atp <- args ]++show tp | (cname,(args,tp)) <- Map.toList (blockCalls sig) ]) ++
    (if Set.null (blockJumps sig) then [] else "  jumps":[ "    "++trg++"("++show tnum++")" | (trg,tnum) <- Set.toList (blockJumps sig) ]) ++
    (if Set.null (blockOrigins sig) then [] else "  origins":[ "    "++src++"("++show snum++")" | (src,snum) <- Set.toList (blockOrigins sig) ])

data BlockSig = BlockSig
    { blockInputsPhi    :: Map String ([(String,Integer,Expr)],TypeDesc)
    , blockInputsSimple :: Map String (String,Integer,Expr,TypeDesc)
    , blockOutputs      :: Map String TypeDesc
    , blockGlobals      :: Set String
    , blockCalls        :: Map String ([TypeDesc],TypeDesc)
    , blockJumps        :: Set (String,Integer)
    , blockOrigins      :: Set (String,Integer)
    } deriving Show

emptyBlockSig :: BlockSig
emptyBlockSig = BlockSig { blockInputsSimple = Map.empty
                         , blockInputsPhi = Map.empty
                         , blockOutputs = Map.empty
                         , blockGlobals = Set.empty
                         , blockCalls = Map.empty
                         , blockJumps = Set.empty
                         , blockOrigins = Set.empty }

realizeBlock :: MemoryModel mem => String -> String -> Integer -> [Instruction]
                -> SMTExpr Bool
                -> mem
                -> Bool
                -> Map String (Val mem)
                -> Map String TypeDesc
                -> [Watchpoint]
                -> [Guard]
                -> SMT (Maybe mem,Map String (Val mem),
                        BlockFinalization mem,
                        [Watchpoint],[Guard])
realizeBlock fname blk subblk (instr:instrs) act mem changed values pred watch guard = do
  res <- realizeInstruction instr fname blk subblk pred act mem values
  let values' = case valueAssigned res of
        Nothing -> values
        Just (lbl,res) -> Map.insert lbl res values
      (mem',changed') = case memoryUpdated res of
        Nothing -> (mem,changed)
        Just n -> (n,True)
      watch' = watch ++ watchpointsCreated res
      guard' = guard ++ guardsCreated res
  case finalization res of
    Just fin -> return (if changed' then Just mem' else Nothing,values',fin,watch',guard')
    Nothing -> realizeBlock fname blk subblk instrs act mem' changed' values' pred watch' guard'
realizeBlock fname blks subblk [] _ _ _ _ _ _ _ = error $ "Internal error: Block "++blks++" of "++fname++" terminates prematurely"
      
{-
realizeBlock :: MemoryModel mem => String -> [Instruction] 
                -> SMTExpr Bool
                -> mem
                -> Bool
                -> Map String (Val mem) 
                -> (String -> String -> SMTExpr Bool -> mem -> [(Val mem,TypeDesc)] -> SMT (mem,Maybe (Val mem),[Watchpoint],[Guard]))
                -> [Watchpoint]
                -> [Guard]
                -> SMT (Maybe mem,Map String (Val mem),Maybe (Maybe (Val mem)),[(String,Maybe (SMTExpr Bool))],[Watchpoint],[Guard])
realizeBlock fname (instr:instrs) act mem changed values calls watch guard
    = do
      --liftIO $ print instr
      --liftIO $ putStrLn $ "Values: "++show values
      (nmem,nvalue,ret,jumps,watch',guard') <- realizeInstruction fname instr act mem values calls
      let values' = case nvalue of
            Nothing -> values
            Just (lbl,res) -> Map.insert lbl res values
          (mem',changed') = case nmem of
            Nothing -> (mem,changed)
            Just n -> (n,True)
      case ret of
        Just ret' -> return (if changed then Just mem' else Nothing,values',ret,jumps,watch++watch',guard++guard')
        Nothing -> case jumps of
          _:_ -> return (if changed then Just mem' else Nothing,values',ret,jumps,watch++watch',guard++guard')
          [] -> realizeBlock fname instrs act mem' changed' values' calls (watch ++ watch') (guard++guard')-}

argToExpr :: MemoryModel mem => Expr -> Map String (Val mem) -> mem -> Val mem
argToExpr e values mem = {-trace ("argToExpr: "++show e++" "++show (Map.toList values)) $-} case exprDesc e of
  EDNamed var -> case Map.lookup var values of
    Just val -> val
    Nothing -> error $ "Failed to find variable "++show var++" "++show (Map.toList values)
  EDNull -> PointerValue (memPtrNull mem)
  EDICmp pred lhs rhs -> case exprType lhs of
    TDPtr _ -> let PointerValue lhs' = argToExpr lhs values mem
                   PointerValue rhs' = argToExpr rhs values mem
               in case pred of
                 IntEQ -> ConditionValue (memPtrEq mem lhs' rhs') 1
                 IntNE -> ConditionValue (not' $ memPtrEq mem lhs' rhs') 1
                 _ -> error $ "Comparing pointers using "++show pred++" unsupported (only (in-)equality allowed)"
    _ -> let lhs' = argToExpr lhs values mem
             rhs' = argToExpr rhs values mem
             apply (ConstValue lhs) (ConstValue rhs) = let lhs' = BitS.toBits lhs :: Integer
                                                           rhs' = BitS.toBits rhs :: Integer
                                                           op = case pred of
                                                             IntEQ -> (==)
                                                             IntNE -> (/=)
                                                             IntUGT -> (>)
                                                             IntUGE -> (>=)
                                                             IntULT -> (<)
                                                             IntULE -> (<=)
                                                             IntSGT -> (>)
                                                             IntSGE -> (>=)
                                                             IntSLT -> (<)
                                                             IntSLE -> (<=)
                                                       in ConstCondition (op lhs' rhs')
             apply lhs rhs = let lhs' = valValue lhs
                                 rhs' = valValue rhs
                                 op = case pred of
                                   IntEQ -> (.==.)
                                   IntNE -> \x y -> not' $ x .==. y
                                   IntUGT -> BVUGT
                                   IntUGE -> BVUGE
                                   IntULT -> BVULT
                                   IntULE -> BVULE
                                   IntSGT -> BVSGT
                                   IntSGE -> BVSGE
                                   IntSLT -> BVSLT
                                   IntSLE -> BVSLE
                             in ConditionValue (op lhs' rhs') 1
         in apply lhs' rhs'
  EDInt v -> ConstValue (BitS.fromNBits (bitWidth (exprType e)) v)
  EDUnOp op arg -> case op of
    UOZExt -> case argToExpr arg values mem of
      ConditionValue v w -> ConditionValue v (bitWidth (exprType e))
      e' -> let v = valValue e'
                d = (bitWidth (exprType e)) - (bitWidth (exprType arg))
                nv = bvconcat (constantAnn (BitS.fromNBits d (0::Integer) :: BitVector) (fromIntegral d)) v
           in DirectValue nv
    UOSExt -> case argToExpr arg values mem of
      ConditionValue v w -> ConditionValue v (bitWidth (exprType e))
      e' -> let v = valValue e'
                w = bitWidth (exprType arg)
                d = (bitWidth (exprType e)) - w
                nv = bvconcat (ite (bvslt v (constantAnn (BitS.fromNBits d (0::Integer)) (fromIntegral w)))
                               (constantAnn (BitS.fromNBits d (-1::Integer) :: BitVector) (fromIntegral d))
                               (constantAnn (BitS.fromNBits d (0::Integer) :: BitVector) (fromIntegral d))) v
            in DirectValue nv
    UOTrunc -> let w = bitWidth (exprType e) 
               in case argToExpr arg values mem of
                 ConstValue bv -> ConstValue (BitS.fromNBits w (BitS.toBits bv :: Integer))
                 ConditionValue v _ -> ConditionValue v w
                 expr -> DirectValue (bvextract (w - 1) 0 (valValue expr))
    UOBitcast -> let PointerValue ptr = argToExpr arg values mem
                     TDPtr tp = exprType e
                 in PointerValue $ memCast mem tp ptr
    _ -> error $ "Implement argToExpr for "++show e
  EDGetElementPtr expr args -> case argToExpr expr values mem of
    PointerValue ptr -> let ptr' = memIndex mem (exprType expr) (fmap (\arg -> case arg of
                                                                          Expr { exprDesc = EDInt i } -> Left i
                                                                          _ -> case argToExpr arg values mem of
                                                                            ConstValue bv -> Left $ BitS.toBits bv
                                                                            DirectValue bv -> Right bv
                                                                      ) args) ptr
                        in PointerValue ptr'
  EDBinOp op lhs rhs -> let lhs' = argToExpr lhs values mem
                            rhs' = argToExpr rhs values mem
                            apply (ConstValue lhs) (ConstValue rhs) = let lhs' = BitS.toBits lhs :: Integer
                                                                          rhs' = BitS.toBits rhs :: Integer
                                                                          rop = case op of
                                                                            BOXor -> Bits.xor
                                                                            BOAdd -> (+)
                                                                            BOAnd -> (.&.)
                                                                            BOSub -> (-)
                                                                            BOShL -> \x y -> shiftL x (fromIntegral y)
                                                                            BOOr -> (.|.)
                                                                            BOMul -> (*)
                                                                      in ConstValue (BitS.fromNBits (BitS.length lhs) (rop lhs' rhs'))
                            apply lhs rhs = let lhs' = valValue lhs
                                                rhs' = valValue rhs
                                                rop = case op of 
                                                  BOXor -> BVXor
                                                  BOAdd -> BVAdd
                                                  BOAnd -> BVAnd
                                                  BOSub -> BVSub
                                                  BOShL -> BVSHL
                                                  BOOr -> BVOr
                                                  BOMul -> BVMul
                                                  _ -> error $ "unsupported operator: "++show op
                                            in DirectValue (rop lhs' rhs')
                        in apply lhs' rhs'
  _ -> error $ "Implement argToExpr for "++show e

data BlockFinalization mem = Jump [((String,String,Integer),Maybe (SMTExpr Bool))]
                           | Return (Maybe (Val mem))
                           | Call String [Val mem] String

data InstructionResult mem = InstrResult { valueAssigned :: Maybe (String,Val mem)
                                         , memoryUpdated :: Maybe mem
                                         , finalization :: Maybe (BlockFinalization mem)
                                         , watchpointsCreated :: [Watchpoint]
                                         , guardsCreated :: [Guard]
                                         }

emptyInstructionResult :: InstructionResult mem
emptyInstructionResult = InstrResult Nothing Nothing Nothing [] []

realizeInstruction :: MemoryModel mem => Instruction
                      -> String
                      -> String
                      -> Integer
                      -> Map String TypeDesc
                      -> SMTExpr Bool
                      -> mem 
                      -> Map String (Val mem)
                      -> SMT (InstructionResult mem)
realizeInstruction instr fname blk subblk pred act mem values
  = {-trace ("Realizing "++show instr++"..") $-} case instr of
    IRet e -> return $ emptyInstructionResult { finalization = Just $ Return (Just (argToExpr e values mem)) }
    IRetVoid -> return $ emptyInstructionResult { finalization = Just $ Return Nothing }
    IBr to -> return $ emptyInstructionResult { finalization = Just $ Jump [((fname,to,0),Nothing)] }
    IBrCond cond ifT ifF -> case argToExpr cond values mem of
      ConstCondition cond' -> return $ emptyInstructionResult { finalization = Just $ Jump [((fname,if cond' then ifT else ifF,0),Nothing)] }
      cond' -> return $ emptyInstructionResult { finalization = Just $ Jump [((fname,ifT,0),Just $ valCond cond'),((fname,ifF,0),Nothing)] }
    ISwitch val def args -> case argToExpr val values mem of
      ConstValue v -> case [ to | (cmp_v,to) <- args, let ConstValue v' = argToExpr cmp_v values mem, v' == v ] of
        [] -> return $ emptyInstructionResult { finalization = Just $ Jump [((fname,def,0),Nothing)] }
        [to] -> return $ emptyInstructionResult { finalization = Just $ Jump [((fname,to,0),Nothing)] }
      v -> return $ emptyInstructionResult { finalization = Just $ Jump $ [ ((fname,to,0),Just $ valEq mem v (argToExpr cmp_v values mem))
                                                                          | (cmp_v,to) <- args
                                                                          ] ++ [ ((fname,def,0),Nothing) ] }
    IAssign trg expr -> return $ emptyInstructionResult { valueAssigned = Just (trg,argToExpr expr values mem) }
    IAlloca trg tp size align -> do
      (ptr,mem') <- memAlloc tp (case argToExpr size values mem of
                                    ConstValue bv -> Left $ BitS.toBits bv
                                    DirectValue bv -> Right bv) Nothing mem
      return $ emptyInstructionResult { memoryUpdated = Just mem'
                                      , valueAssigned = Just (trg,PointerValue ptr) }
    IStore val to align -> let PointerValue ptr = argToExpr to values mem
                           in case exprType val of
                             TDPtr tp -> case argToExpr val values mem of
                               PointerValue ptr2 -> let (mem',guards) = memStorePtr tp ptr ptr2 mem
                                                    in return $ emptyInstructionResult { memoryUpdated = Just mem'
                                                                                       , guardsCreated = [ (err,and' [act,cond]) | (err,cond) <- guards ] }
                             tp -> let (mem',guards) = memStore tp ptr (valValue $ argToExpr val values mem) mem
                                   in return $ emptyInstructionResult { memoryUpdated = Just mem' 
                                                                      , guardsCreated = [ (err,and' [act,cond]) | (err,cond) <- guards ] }
    IPhi _ _ -> return emptyInstructionResult
    ICall rtp trg _ f args -> case exprDesc f of
                                   EDNamed fn -> case intrinsics fn of
                                     Just intr -> do
                                       res <- intr trg (Map.lookup trg pred) act mem 
                                              [ (argToExpr arg values mem,exprType arg) | arg <- args ]
                                       return $ res { finalization = Just $ Jump [((fname,blk,subblk+1),Nothing)] }
                                     Nothing -> return $ emptyInstructionResult { finalization = Just $ Call fn [ argToExpr arg values mem | arg <- args ] trg }
    ILoad trg arg align -> let PointerValue ptr = argToExpr arg values mem
                           in case exprType arg of
                             TDPtr (TDPtr tp) -> let (res,guards) = memLoadPtr tp ptr mem
                                                 in return $ emptyInstructionResult { valueAssigned = Just (trg,PointerValue res)
                                                                                    , guardsCreated = [ (err,and' [act,cond]) | (err,cond) <- guards ] }
                             TDPtr tp -> let (res,guards) = memLoad tp ptr mem
                                         in return $ emptyInstructionResult { valueAssigned = Just (trg,DirectValue res)
                                                                            , guardsCreated = [ (err,and' [act,cond]) | (err,cond) <- guards ] }
    _ -> error $ "Implement realizeInstruction for "++show instr

data LabelOrigin = ArgumentOrigin
                 | GlobalOrigin
                 | BlockOrigin String Integer
                 deriving (Eq,Ord,Show)

mkVarBlockMap :: [String] -> [String] -> [(String,[(Integer,[Instruction])])] -> Map String LabelOrigin
mkVarBlockMap args globs
  = foldl (\mp (blk,subblks)
            -> foldl (\mp' (n,instrs)
                       -> let blk' = BlockOrigin blk n
                          in foldl (\mp'' instr
                                    -> case instr of
                                      IAssign lbl _ -> Map.insert lbl blk' mp''
                                      IAlloca lbl _ __ _ -> Map.insert lbl blk' mp''
                                      ILoad lbl _ _ -> Map.insert lbl blk' mp''
                                      ICall _ lbl _ _ _ -> Map.insert lbl blk' mp''
                                      IVAArg lbl _ _ -> Map.insert lbl blk' mp''
                                      IPhi lbl _ -> Map.insert lbl blk' mp''
                                      _ -> mp''
                                   ) mp' instrs
                     ) mp subblks
          ) (Map.fromList $ [(arg,ArgumentOrigin) | arg <- args] ++ [(arg,GlobalOrigin) | arg <- globs])

mkBlockSigs :: Map String LabelOrigin -> [(String,[(Integer,[Instruction])])] -> Map String (Map Integer BlockSig)
mkBlockSigs lbl_mp blks
    = {-Map.adjust (Map.adjust (\sig -> sig { blockOrigins = Set.singleton ("",0) }) 0) (fst $ head blks) $-}
      foldl (\mp (blk,subblks)
              -> foldl (\mp' (n,instrs)
                         -> foldl (\mp'' instr
                                    -> case instr of
                                     IRet e -> addExpr blk n e mp''
                                     IBr to -> addJump blk n to 0 mp''
                                     IBrCond cond ifT ifF -> addExpr blk n cond $
                                                             addJump blk n ifT 0 $
                                                             addJump blk n ifF 0 mp''
                                     ISwitch val def cases -> addExpr blk n val $
                                                              addJump blk n def 0 $
                                                              foldl (\mp''' (expr,to) -> addExpr blk n expr $
                                                                                         addJump blk n to 0 mp''') mp'' cases
                                     IIndirectBr e trgs -> addExpr blk n e $
                                                           foldl (\mp''' trg -> addJump blk n trg 0 mp''') mp'' trgs
                                     IResume e -> addExpr blk n e mp''
                                     IAssign _ e -> addExpr blk n e mp''
                                     ILoad _ ptr _ -> addExpr blk n ptr mp''
                                     IStore e ptr _ -> addExpr blk n e $
                                                       addExpr blk n ptr mp''
                                     IPhi trg cases -> let (mp1,vec) = mapAccumL (\cmp (val,from) -> let Just subs = List.lookup from blks
                                                                                                         (sub,_) = last subs
                                                                                                     in (addExpr blk n val cmp,(from,sub,val))) mp'' cases
                                                           mp2 = addPhi blk n trg (vec,exprType $ fst $ head cases) mp1
                                                       in mp2
                                     ICall rtp res cc fn args -> foldl (\mp''' arg -> addExpr blk n arg mp''') (addJump blk n blk (n+1) mp'') args
                                     _ -> mp''
                                  ) (Map.adjust (Map.insertWith (\_ o -> o) n emptyBlockSig) blk mp') instrs
                       ) (Map.insertWith (\_ o -> o) blk (Map.singleton 0 emptyBlockSig) mp) subblks
            ) Map.empty {-(Map.singleton "" (Map.singleton 0 $ emptyBlockSig { blockJumps = Set.singleton (fst $ head blks,0) }))-} blks
      where
        addExpr :: String -> Integer -> Expr -> Map String (Map Integer BlockSig) -> Map String (Map Integer BlockSig)
        addExpr blk n e = case exprDesc e of
          EDNamed name -> case Map.lookup name lbl_mp of
            Nothing -> error $ "Can't find "++name++" in label mapping"
            Just (BlockOrigin blk_from n_from) -> if blk_from==blk && n_from == n
                                                  then id
                                                  else addOutput blk_from n_from name (exprType e) . addInput blk n name (blk_from,n_from,e,exprType e)
            Just GlobalOrigin -> addGlobal blk n name
          EDUnOp _ arg -> addExpr blk n arg
          EDICmp _ lhs rhs -> addExpr blk n lhs . addExpr blk n rhs
          EDBinOp _ lhs rhs -> addExpr blk n lhs . addExpr blk n rhs
          EDGetElementPtr expr args -> addExpr blk n expr . (\mp -> foldr (addExpr blk n) mp args)
          EDInt _ -> id
          EDUndef -> id
          EDNull -> id
          e' -> error $ "Implement addExpr for "++show e'
        addPhi blk n lbl args = Map.alter (\c -> case c of
                                              Nothing -> Just (Map.singleton n $ emptyBlockSig { blockInputsPhi = Map.singleton lbl args })
                                              Just bank -> Just $ Map.alter (\c' -> case c' of
                                                                                Nothing -> Just $ emptyBlockSig { blockInputsPhi = Map.singleton lbl args }
                                                                                Just blksig -> Just $ blksig { blockInputsPhi = Map.insert lbl args (blockInputsPhi blksig) }
                                                                            ) n bank
                                          ) blk
        addInput blk n lbl args = Map.alter (\c -> case c of
                                                Nothing -> Just (Map.singleton n $ emptyBlockSig { blockInputsSimple = Map.singleton lbl args })
                                                Just bank -> Just $ Map.alter (\c' -> case c' of
                                                                                  Nothing -> Just $ emptyBlockSig { blockInputsSimple = Map.singleton lbl args }
                                                                                  Just blksig -> Just $ blksig { blockInputsSimple = Map.insert lbl args (blockInputsSimple blksig) }
                                                                              ) n bank
                                            ) blk
        addOutput blk n lbl tp = Map.alter (\c -> case c of
                                               Nothing -> Just (Map.singleton n $ emptyBlockSig { blockOutputs = Map.singleton lbl tp })
                                               Just bank -> Just $ Map.alter (\c' -> case c' of
                                                                                 Nothing -> Just $ emptyBlockSig { blockOutputs = Map.singleton lbl tp }
                                                                                 Just blksig -> Just $ blksig { blockOutputs = Map.insert lbl tp (blockOutputs blksig) }
                                                                             ) n bank
                                           ) blk
        addJump :: String -> Integer -> String -> Integer -> Map String (Map Integer BlockSig) -> Map String (Map Integer BlockSig)
        addJump blk n to ton = Map.alter (\c -> case c of
                                             Nothing -> Just (Map.singleton n $ emptyBlockSig { blockJumps = Set.singleton (to,ton) })
                                             Just bank -> Just $ Map.alter (\c' -> case c' of
                                                                               Nothing -> Just $ emptyBlockSig { blockJumps = Set.singleton (to,ton) }
                                                                               Just blksig -> Just $ blksig { blockJumps = Set.insert (to,ton) (blockJumps blksig) }
                                                                           ) n bank
                                         ) blk .
                               Map.alter (\c -> case c of
                                             Nothing -> Just (Map.singleton ton $ emptyBlockSig { blockOrigins = Set.singleton (blk,n) })
                                             Just bank -> Just $ Map.alter (\c' -> case c' of
                                                                               Nothing -> Just $ emptyBlockSig { blockOrigins = Set.singleton (blk,n) }
                                                                               Just blksig -> Just $ blksig { blockOrigins = Set.insert (blk,n) (blockOrigins blksig) }
                                                                           ) ton bank
                                         ) to
        addGlobal blk n lbl = Map.alter (\c -> case c of
                                            Nothing -> Just (Map.singleton n $ emptyBlockSig { blockGlobals = Set.singleton lbl })
                                            Just bank -> Just $ Map.alter (\c' -> case c' of
                                                                              Nothing -> Just $ emptyBlockSig { blockGlobals = Set.singleton lbl }
                                                                              Just blksig -> Just $ blksig { blockGlobals = Set.insert lbl (blockGlobals blksig) }
                                                                          ) n bank
                                        ) blk

allTypesArgs :: [(String,TypeDesc)] -> [TypeDesc]
allTypesArgs = allTypes' []
    where
      allTypes' tps [] = tps
      allTypes' tps ((name,tp):vals) = case tp of
        TDPtr tp' -> allTypes' (tp':tps) vals
        _ -> allTypes' tps vals

allTypesBlks :: [(String,[(Integer,[Instruction])])] -> [TypeDesc]
allTypesBlks = allTypes' [] []
    where
      allTypes' [] tps [] = tps
      allTypes' [] tps ((_,subblks):blks) = allTypes' (concat $ fmap snd subblks) tps blks
      allTypes' (i:is) tps blks = case i of
                                        ILoad lbl e _ -> case exprType e of
                                          TDPtr tp -> allTypes' is (tp:tps) blks
                                        IStore w to _ -> allTypes' is ((exprType w):tps) blks
                                        IAlloca lbl tp _ _ -> allTypes' is (tp:tps) blks
                                        
                                        _ -> allTypes' is tps blks

intr_memcpy,intr_memset,intr_restrict,intr_watch,intr_malloc :: MemoryModel mem => String -> Maybe TypeDesc -> SMTExpr Bool -> mem -> [(Val mem,TypeDesc)] -> SMT (InstructionResult mem)
intr_memcpy _ _ _ mem [(PointerValue to,_),(PointerValue from,_),(ConstValue len,_),_,_]
  = return $ emptyInstructionResult { memoryUpdated = Just $ memCopy (BitS.toBits len) to from mem }

intr_memset _ _ _ mem [(PointerValue dest,_),(val,_),(ConstValue len,_),_,_]
  = return $ emptyInstructionResult { memoryUpdated = Just $ memSet (BitS.toBits len) (valValue val) dest mem }

intr_restrict _ _ act mem [(val,_)] = do
  comment " Restriction:"
  case val of
    ConditionValue val _ -> assert $ act .=>. val
    _ -> assert $ act .=>. (not' $ valValue val .==. constantAnn (BitS.fromNBits (32::Int) (0::Integer)) 32)
  return emptyInstructionResult
intr_assert _ _ act mem [(val,_)] = do
  return $ emptyInstructionResult { guardsCreated = [(Custom,case val of
                                                         ConditionValue val _ -> and' [act,not' val]
                                                         _ -> and' [act,valValue val .==. constantAnn (BitS.fromNBits (32::Int) (0::Integer)) 32])] }


intr_watch _ _ act mem ((ConstValue num,_):exprs)
  = return $ emptyInstructionResult { watchpointsCreated = [(show (BitS.toBits num :: Integer),act,[ (tp,valValue val) | (val,tp) <- exprs ])] }

intr_malloc trg (Just tp) act mem [(size,sztp)] = do
  (ptr,mem') <- memAlloc tp (case size of
                                ConstValue bv -> Left $ BitS.toBits bv
                                DirectValue bv -> Right bv) Nothing mem
  return $ emptyInstructionResult { memoryUpdated = Just mem'
                                  , valueAssigned = Just (trg,PointerValue ptr) }

intr_nondet :: MemoryModel mem => Integer -> String -> Maybe TypeDesc -> SMTExpr Bool -> mem -> [(Val mem,TypeDesc)] -> SMT (InstructionResult mem)
intr_nondet width trg _ _ mem [] = do
  v <- varAnn (fromIntegral width)
  return $ emptyInstructionResult { valueAssigned = Just (trg,DirectValue v) }

intrinsics :: MemoryModel mem => String -> Maybe (String -> Maybe TypeDesc -> SMTExpr Bool -> mem -> [(Val mem,TypeDesc)] -> SMT (InstructionResult mem))
intrinsics "llvm.memcpy.p0i8.p0i8.i64" = Just intr_memcpy
intrinsics "llvm.memcpy.p0i8.p0i8.i32" = Just intr_memcpy
intrinsics "llvm.memset.p0i8.i32" = Just intr_memset
intrinsics "llvm.memset.p0i8.i64" = Just intr_memset
intrinsics "furchtbar_restrict" = Just intr_restrict
intrinsics "furchtbar_assert" = Just intr_assert
intrinsics "furchtbar_nondet_i64" = Just (intr_nondet 64)
intrinsics "furchtbar_nondet_i32" = Just (intr_nondet 32)
intrinsics "furchtbar_nondet_i16" = Just (intr_nondet 16)
intrinsics "furchtbar_nondet_i8" = Just (intr_nondet 8)
intrinsics "furchtbar_nondet_u64" = Just (intr_nondet 64)
intrinsics "furchtbar_nondet_u32" = Just (intr_nondet 32)
intrinsics "furchtbar_nondet_u16" = Just (intr_nondet 16)
intrinsics "furchtbar_nondet_u8" = Just (intr_nondet 8)
intrinsics "furchtbar_watch" = Just intr_watch
intrinsics "malloc" = Just intr_malloc
intrinsics _ = Nothing

getConstant :: FFI.ValueRef -> IO (MemContent,Bool)
getConstant val = do
  tp <- FFI.typeOf val >>= typeDesc2
  c <- FFI.isGlobalConstant val
  val <- getConstant' tp val
  return (val,c/=0)
  where
    getConstant' (TDStruct tps _) val = do
      res <- mapM (\(tp,i) -> do
                      nv <- Alloc.alloca (\ptr -> do
                                             poke ptr i
                                             FFI.constExtractValue val ptr 1
                                         )
                      getConstant' tp nv) (zip tps [0..])
      return $ MemArray res
    getConstant' (TDArray n tp) val = do
      res <- mapM (\i -> do
                      nv <- Alloc.alloca (\ptr -> do
                                             poke ptr (fromIntegral i)
                                             FFI.constExtractValue val ptr 1
                                         )
                      getConstant' tp nv
                  ) [0..(n-1)]
      return $ MemArray res
    getConstant' (TDVector n tp) val = do
      res <- mapM (\i -> do
                      nv <- Alloc.alloca (\ptr -> do
                                             poke ptr (fromIntegral i)
                                             FFI.constExtractValue val ptr 1
                                         )
                      getConstant' tp nv) [0..(n-1)]
      return $ MemArray res
    getConstant' (TDInt _ w) val = do
      v <- FFI.constIntGetZExtValue val
      return $ MemCell $ constantAnn (BitS.fromNBits w v) (fromIntegral w)
    getConstant' (TDPtr tp) val = do
      n <- FFI.isNull val
      if n/=0
        then return MemNull
        else (do
                 v <- Alloc.alloca (\ptr -> do
                                       poke ptr (fromIntegral 0)
                                       FFI.constExtractValue val ptr 1
                                   )
                 getConstant' tp v)

type ProgDesc = (Map String ([(String,TypeDesc)],TypeDesc,[(String,[(Integer,[Instruction])])]),Map String (TypeDesc,MemContent,Bool))

orderMap :: ProgDesc -> Map String (Map String Integer)
orderMap (prog,_) = fmap (\(_,_,blks) -> Map.fromList [ (name,n) | ((name,_),n) <- zip blks [0..] ]) prog

getProgram :: String -> IO ProgDesc
getProgram file = do
  m <- readBitcodeFromFile file
  glob <- getGlobalVariables m >>= mapM (\(name,val) -> do
                                            tp <- FFI.typeOf val >>= typeDesc2
                                            (c,isConst) <- getConstant val
                                            return (name,(tp,c,isConst))
                                        ) >>= return.(Map.fromList)
  funs <- getFunctions m
  res <- mapM (\(name,fun) -> do
                  pars <- liftIO $ getParams fun >>= mapM (\(name,ref) -> do
                                                              tp <- FFI.typeOf ref >>= typeDesc2
                                                              return (name,tp))
                  tp <- liftIO $ FFI.typeOf fun >>= FFI.getElementType >>= FFI.getReturnType >>= typeDesc2
                  blks <- liftIO $ getBasicBlocks fun >>= mapM (\(name,blk) -> do
                                                                   instrs <- getInstructions blk >>= mapM (\(name,instr) -> getInstruction instr)
                                                                   return (name,mkSubBlocks 0 [] instrs))
                  return (name,(pars,tp,blks))) funs
  return (Map.fromList res,glob)
  where
    mkSubBlocks :: Integer -> [Instruction] -> [Instruction] -> [(Integer,[Instruction])]
    mkSubBlocks n cur (i:is) = case i of
      ICall _ _ _ _ _ -> (n,cur++[i]):mkSubBlocks (n+1) [] is
      IRetVoid -> [(n,cur++[i])]
      IRet _ -> [(n,cur++[i])]
      IBr _ -> [(n,cur++[i])]
      IBrCond _ _ _ -> [(n,cur++[i])]
      ISwitch _ _ _ -> [(n,cur++[i])]
      _ -> mkSubBlocks n (cur++[i]) is

mergePrograms :: ProgDesc -> ProgDesc -> ProgDesc
mergePrograms (p1,g1) (p2,g2) = (Map.unionWithKey (\name (args1,tp1,blks1) (args2,tp2,blks2)
                                                   -> if fmap snd args1 /= fmap snd args2 || tp1 /= tp2
                                                      then error $ "Conflicting signatures for function "++show name++" detected"
                                                      else (if Prelude.null blks1
                                                            then (args2,tp2,blks2)
                                                            else (if Prelude.null blks2
                                                                  then (args1,tp1,blks1)
                                                                  else error $ "Conflicting definitions for function "++show name++" found"))) p1 p2,
                                 Map.union g1 g2)

data MemoryModelOption = UntypedModel
                       | TypedModel
                       | BlockModel
                       | PlainModel
                       deriving (Eq,Ord,Show)

data Options = Options
               { entryPoint :: String
               , bmcDepth :: Integer
               , files :: [String]
               , memoryModel :: MemoryModelOption
               , solver :: Maybe String
               , checkUser :: Bool
               , checkMemoryAccess :: Bool
               , showHelp :: Bool
               } deriving (Eq,Ord,Show)

defaultOptions :: Options
defaultOptions = Options { entryPoint = "main" 
                         , bmcDepth = 10
                         , files = []
                         , memoryModel = PlainModel
                         , solver = Nothing
                         , checkUser = False
                         , checkMemoryAccess = False
                         , showHelp = False }

optionDescr :: [OptDescr (Options -> Options)]
optionDescr = [Option ['e'] ["entry-point"] (ReqArg (\str opt -> opt { entryPoint = str }) "function") "Specify the main function to test"
              ,Option ['d'] ["depth"] (ReqArg (\str opt -> opt { bmcDepth = read str }) "d") "Maximal unroll depth"
              ,Option ['m'] ["memory-model"] (ReqArg (\str opt -> opt { memoryModel = case str of
                                                                           "typed" -> TypedModel
                                                                           "untyped" -> UntypedModel
                                                                           "block" -> BlockModel
                                                                           "plain" -> PlainModel
                                                                           _ -> error $ "Unknown memory model "++show str
                                                                      }) "model") "Memory model to use (untyped,typed or block)"
              ,Option [] ["solver"] (ReqArg (\str opt -> opt { solver = Just str }) "smt-binary") "The SMT solver to use to solve the generated instance"
              ,Option [] ["check-user"] (NoArg (\opt -> opt { checkUser = True })) "Validate user assertions"
              ,Option [] ["check-mem"] (NoArg (\opt -> opt { checkMemoryAccess = True })) "Validate memory accesses"
              ,Option ['h'] ["help"] (NoArg (\opt -> opt { showHelp = True })) "Show this help"
              ]

getOptions :: IO Options
getOptions = do
  args <- getArgs
  let (res,args',errs) = getOpt Permute optionDescr args
  case errs of
    [] -> return $ foldl (.) id res (defaultOptions { files = args' })
    _ -> error $ show errs

main = do
  opts <- getOptions
  when (showHelp opts) $ do
    putStrLn $ usageInfo "USAGE:\n  furchtbar [OPTION...] FILE [FILE...]\n\nOptions:" optionDescr
    exitSuccess
  progs <- mapM getProgram (files opts)
  let program = foldl1 mergePrograms progs
  withSMTSolver (case solver opts of
                    Nothing -> "~/debug-smt.sh output-" ++ (entryPoint opts) ++ ".smt"
                    Just bin -> bin) $ do
    setOption (PrintSuccess False)
    setOption (ProduceModels True)
    setLogic "QF_ABV"
    (case memoryModel opts of
        TypedModel -> do
          perform program (entryPoint opts) (bmcDepth opts) (checkUser opts) (checkMemoryAccess opts) :: SMT TypedMemory
          return ()
        UntypedModel -> do
          perform program (entryPoint opts) (bmcDepth opts) (checkUser opts) (checkMemoryAccess opts) :: SMT UntypedMemory
          return ()
        BlockModel -> do
          perform program (entryPoint opts) (bmcDepth opts) (checkUser opts) (checkMemoryAccess opts) :: SMT UntypedBlockMemory
          return ()
        PlainModel -> do
          perform program (entryPoint opts) (bmcDepth opts) (checkUser opts) (checkMemoryAccess opts) :: SMT PlainMemory
          return ()
      )
  where
    perform :: (MemoryModel mem)
               => ProgDesc -> String -> Integer -> Bool -> Bool -> SMT mem
    perform program entry depth check_user check_mem = do
      (mem_in,res) <- translateProgram program entry (\err -> case err of
                                                         Custom -> check_user
                                                         NullDeref -> check_mem
                                                         Overrun -> check_mem
                                                         FreeAccess -> check_mem)
                      (\err watch -> return $ "Error found: "++(case err of
                                                  Custom -> "User error"
                                                  NullDeref -> "Null dereference"
                                                  Overrun -> "Memory overrun"
                                                  FreeAccess -> "Accessing free'd memory")
                                     ++ "\nWatchpoints:\n"
                                     ++ unlines (fmap (\(name,args) -> "  "++name++":"++concat (fmap (\(tp,rval) -> " "++show (BitS.toBits rval :: Integer)) args)) watch))
      case res of
        Just err -> liftIO $ putStrLn err
        Nothing -> liftIO $ putStrLn "No error found."
      return mem_in
    
prepareEnvironment :: (MemoryModel mem)
                      => [TypeDesc] -> [(String,TypeDesc)] -> Map String (TypeDesc,MemContent,Bool) -> SMT ([Val mem],Map String (Pointer mem),mem)
prepareEnvironment alltp args globals = do
  imem <- memNew alltp
  assert $ memInit imem
  (m0,globals') <- createGlobals imem (Map.toList globals) Map.empty
  (args,m1) <- foldrM (\(name,tp) (args,mem) -> case tp of
                          TDPtr tp -> do
                            (ptr,mem') <- memAlloc tp (Left 1) Nothing mem
                            return ((PointerValue ptr):args,mem')
                          tp -> do
                            var <- newValue mem tp
                            return (var:args,mem)
                      ) ([],m0) args
  return (args,globals',m1)
  where
    createGlobals mem [] mp = return (mem,mp)
    createGlobals mem ((name,(TDPtr tp,cont,_)):rest) mp = do
      (ptr,mem') <- memAlloc tp (Left 1) (Just cont) mem
      createGlobals mem' rest (Map.insert name ptr mp)

predictMallocUse :: [Instruction] -> Map String TypeDesc
predictMallocUse = predict' Map.empty Set.empty
  where
    predict' mp act [] = Map.union mp (Map.fromList [ (entr,TDInt False 8) | entr <- Set.toList act ])
    predict' mp act (instr:instrs) = case instr of
      ICall _ name _ (Expr { exprDesc = EDNamed "malloc" }) _ -> predict' mp (Set.insert name act) instrs
      IAssign _ (Expr { exprDesc = EDGetElementPtr (Expr { exprDesc = EDNamed name })  _ }) -> if Set.member name act
                                                                                               then predict' (Map.insert name (TDInt False 8) mp) (Set.delete name act) instrs
                                                                                               else predict' mp act instrs
      IAssign _ (Expr { exprDesc = EDUnOp UOBitcast (Expr { exprDesc = EDNamed name })
                      , exprType = TDPtr tp }) -> if Set.member name act
                                                  then predict' (Map.insert name tp mp) (Set.delete name act) instrs
                                                  else predict' mp act instrs
      ILoad _ (Expr { exprDesc = EDNamed name }) _ -> if Set.member name act
                                                      then predict' (Map.insert name (TDInt False 8) mp) (Set.delete name act) instrs
                                                      else predict' mp act instrs
      _ -> predict' mp act instrs
