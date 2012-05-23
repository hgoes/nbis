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
import Data.List (genericLength,genericReplicate,genericSplitAt,zip4,zipWith4,zipWith5)
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

type Watchpoint = (String,SMTExpr Bool,[(TypeDesc,SMTExpr BitVector)])

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

instance MemoryModel m => Eq (Val m) where
    (ConstValue x) == (ConstValue y) = x == y
    (DirectValue x) == (DirectValue y) = x == y
    --(PointerValue x) == (PointerValue y) = x == y
    (ConditionValue x _) == (ConditionValue y _) = x == y
    (ConstCondition x) == (ConstCondition y) = x == y
    _ == _ = False

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
                                     , rblockJumps      :: Map String (SMTExpr Bool)
                                     , rblockReturns    :: Maybe (Maybe (Val m))
                                     }

translateProgram :: (MemoryModel mem) 
                    => ProgDesc -> String -> Integer -> SMT (mem,mem,[Watchpoint])
translateProgram (program,globs) entry_point limit = do
  let alltps = foldl (\tps (args,rtp,blocks) 
                      -> let tpsArgs = allTypesArgs args
                             tpsBlocks = allTypesBlks blocks
                         in tps++tpsArgs++tpsBlocks) [] program
      (args,rtp,blks) = program!entry_point
  liftIO $ print globs
  (arg_vals,globals,mem_in) <- prepareEnvironment alltps args globs
  (mem_out,ret,watches) <- translateFunction alltps program entry_point args rtp blks globals limit (constant True) mem_in (zip arg_vals (fmap snd args))
  return (mem_in,mem_out,watches)

translateFunction :: (MemoryModel m)
                     => [TypeDesc]
                     -> Map String ([(String,TypeDesc)],TypeDesc,[(String,[Instruction])])
                     -> String
                     -> [(String,TypeDesc)] -> TypeDesc
                     -> [(String,[Instruction])]
                     -> Map String (Pointer m)
                     -> Integer
                     -> SMTExpr Bool
                     -> m
                     -> [(Val m,TypeDesc)]
                     -> SMT (m,Maybe (Val m),[Watchpoint])
translateFunction allTps program fname argTps tp blocks globals limit act mem_in args
  = do
    --liftIO $ putStr $ unlines $ concat [ (fname++" :: "++show args++" -> "++show rtype):concat [ ("  "++blkname++":"):[ "    "++show instr | instr <- instrs ]  | (blkname,instrs) <- blks ] | (fname,(args,rtype,blks)) <- Map.toList program ]
    let blockMp = mkVarBlockMap (fmap fst argTps) (Map.keys globals) blocks
        blockSigs = mkBlockSigs blockMp blocks
        ordMp = Map.fromList (zipWith (\(name,instrs) n -> (name,(instrs,n))) (("",[]):blocks) [0..])
        infoMp = Map.intersectionWith (\(instrs,n) sig -> (instrs,n,sig)) ordMp blockSigs
        inps = zipWith (\(name,_) (arg,_) -> (name,arg)) argTps args
        predictions = predictMallocUse blocks
    --liftIO $ mapM_ (\(name,sig) -> putStr (unlines (showBlockSig name sig))) (Map.toList blockSigs)
    --comment $ show $ prettyFunction fname tp argTps blocks
    --liftIO $ print predictions
    bfs allTps infoMp predictions
      (Map.singleton ("",0) (RealizedBlock { rblockActivation = act
                                           , rblockMemoryOut = mem_in
                                           , rblockOutput = Map.fromList inps
                                           , rblockJumps = Map.singleton (fst $ head blocks) (constant True)
                                           , rblockReturns = Nothing 
                                           }))
      [] [(fst $ head blocks,0,1)]
  where
    bfs _ _ _ done watch [] = do
      rmem <- memSwitch [ (mem,act) | RealizedBlock { rblockReturns = Just _ 
                                                    , rblockMemoryOut = mem 
                                                    , rblockActivation = act } <- Map.elems done ]
      ret <- case tp of
        TDVoid -> return Nothing
        _ -> do
          ret' <- valSwitch rmem tp [ (val,act) | RealizedBlock { rblockReturns = Just (Just val)
                                                                , rblockActivation = act
                                                                } <- Map.elems done ]
          return $ Just ret'
      return (rmem,ret,watch)
    bfs tps info preds done watch (nxt@(name,lvl,_):rest)
      | Map.member (name,lvl) done = bfs tps info preds done watch rest
      | otherwise = do
        --liftIO $ putStrLn $ " Block "++fname++" -> "++name++" ("++show lvl++")"
        comment $ " Block "++fname++" -> "++name++" ("++show lvl++")"
        (nblk,watch') <- trans tps done 
                         (\f name -> case intrinsics f of
                             Nothing -> case Map.lookup f program of
                               Nothing -> error $ "Function "++show f++" not found"
                               Just (args,rtp,blocks) -> case blocks of
                                 [] -> error $ "Function "++f++" has no implementation"
                                 _ -> translateFunction allTps program f args rtp blocks globals (limit-lvl-1)
                             Just intr -> intr (Map.lookup name preds)
                         ) fname globals info (name,lvl)
        let (_,lvl_cur,_) = case Map.lookup name info of
              Nothing -> error $ "Internal error: Failed to find block signature for "++name
              Just x -> x
            trgs = [ (trg,lvl',lvl_trg) 
                   | trg <- Map.keys $ rblockJumps nblk,
                     let (_,lvl_trg,_) = info!trg,let lvl' = if lvl_cur < lvl_trg then lvl else lvl+1,lvl' < limit ]
        bfs tps info preds (Map.insert (name,lvl) nblk done) (watch++watch') (foldl insert' rest trgs)
    
    insert' [] it = [it]
    insert' all@((cname,clvl,cord):rest) (name,lvl,ord)
      | clvl > lvl || (clvl==lvl && cord > ord) = (name,lvl,ord):all
      | otherwise = (cname,clvl,cord):(insert' rest (name,lvl,ord))
                         
trans :: (MemoryModel m) 
         => [TypeDesc] -> Map (String,Integer) (RealizedBlock m) 
         -> (String -> String -> SMTExpr Bool -> m -> [(Val m,TypeDesc)] -> SMT (m,Maybe (Val m),[Watchpoint]))
         -> String
         -> Map String (Pointer m)
         -> Map String ([Instruction],Integer,BlockSig)
         -> (String,Integer) 
         -> SMT (RealizedBlock m,[Watchpoint])
trans tps acts calls fname globals blocks (name,lvl) = do
    let (instrs,ord,sig) = blocks!name
        froms = [ (rblockActivation realized,rblockMemoryOut realized,(rblockJumps realized)!name)
                | from <- Set.toList (blockOrigins sig), 
                  let (_,ord_from,sig_from) = blocks!from,
                  let lvl_from = if ord_from < ord
                                 then lvl
                                 else lvl-1,
                  lvl_from >= 0, 
                  realized <- maybeToList (Map.lookup (from,lvl_from) acts) ]
    act <- var
    assert $ act .==. or' [ and' [act',cond] | (act',_,cond) <- froms ]
    mem <- case froms of
             [] -> do
               mem <- memNew tps
               assert $ memInit mem
               return mem
             conds -> memSwitch [ (mem,and' [act',cond])  | (act',mem,cond) <- conds ]
    let inps_simple = Map.fromList $ mapMaybe (\(iname,(from,expr,tp)) -> do
                                                  let (_,ord_from,_) = blocks!from
                                                      lvl_from = if ord_from < ord
                                                                 then lvl
                                                                 else lvl-1
                                                  if lvl_from < 0
                                                    then Nothing
                                                    else return ()
                                                  inp_block <- case Map.lookup (from,lvl_from) acts of
                                                    Nothing -> Map.lookup (from,0) acts
                                                    Just blk -> return blk
                                                  return $ (iname,argToExpr expr (rblockOutput inp_block) mem)
                                              ) (Map.toList $ blockInputsSimple sig)
        inp_global = fmap PointerValue globals
        inp0 = Map.union inps_simple inp_global
    inps_phi <- mapM (\(iname,(from,tp)) -> do
                         let no_undef = Prelude.filter (\(blk,expr) -> exprDesc expr /= EDUndef) from
                             choices = mapMaybe (\(blk,arg) -> let (_,ord_from,_) = blocks!blk
                                                                   lvl_from = if ord_from < ord
                                                                              then lvl
                                                                              else lvl-1
                                                               in if lvl_from < 0
                                                                  then Nothing
                                                                  else (case Map.lookup (blk,lvl_from) acts of
                                                                           Nothing -> Nothing
                                                                           Just realized_from -> case arg of
                                                                             Expr { exprDesc = EDUndef } -> Nothing
                                                                             _ -> Just (argToExpr arg inp0 mem,
                                                                                        and' [rblockActivation realized_from,(rblockJumps realized_from)!name]))
                                                ) from
                         res <- valSwitch mem tp choices
                         return (iname,res)
                     ) (Map.toList $ blockInputsPhi sig)
    (nmem,outps,ret',jumps,watch) <- realizeBlock fname instrs act mem False (Map.union inp0 (Map.fromList inps_phi)) calls []
    jumps' <- translateJumps jumps
    return $ (RealizedBlock { rblockActivation = act
                            , rblockMemoryOut = case nmem of
                              Nothing -> mem
                              Just nmem' -> nmem'
                            , rblockOutput = outps
                            , rblockJumps = jumps'
                            , rblockReturns = ret'
                            },watch)

translateJumps :: [(String,Maybe (SMTExpr Bool))] -> SMT (Map String (SMTExpr Bool))
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
          else "  inputs":[ "    " ++ iname ++ " : "++show tp++" ~> "++ show expr | (iname,(ifrom,expr,tp)) <- Map.toList (blockInputsSimple sig) ]) ++
    (if Map.null (blockInputsPhi sig) then [] 
     else "  phis":(concat [ ("    "++iname++" : "++show itp): 
                             [ "    "++(fmap (const ' ') iname)++" | "++ 
                               from ++ " ~> "++show inf
                             | (from,inf) <- ifrom
                             ] | (iname,(ifrom,itp)) <- Map.toList (blockInputsPhi sig) ])) ++
    (if Set.null (blockGlobals sig) then [] else "  globals":[ "    "++name | name <- Set.toList (blockGlobals sig) ]) ++
    (if Map.null (blockOutputs sig) then [] else "  outputs":[ "    "++oname++" : "++show otp | (oname,otp) <- Map.toList (blockOutputs sig) ]) ++
    (if Map.null (blockCalls sig) then [] else  "  calls":[ "    "++cname++" : "++concat [ show atp++" -> " | atp <- args ]++show tp | (cname,(args,tp)) <- Map.toList (blockCalls sig) ]) ++
    (if Set.null (blockJumps sig) then [] else "  jumps":[ "    "++trg | trg <- Set.toList (blockJumps sig) ]) ++
    (if Set.null (blockOrigins sig) then [] else "  origins":[ "    "++src | src <- Set.toList (blockOrigins sig) ])

data BlockSig = BlockSig
    { blockInputsPhi    :: Map String ([(String,Expr)],TypeDesc)
    , blockInputsSimple :: Map String (String,Expr,TypeDesc)
    , blockOutputs      :: Map String TypeDesc
    , blockGlobals      :: Set String
    , blockCalls        :: Map String ([TypeDesc],TypeDesc)
    , blockJumps        :: Set String
    , blockOrigins      :: Set String
    } deriving Show

emptyBlockSig :: BlockSig
emptyBlockSig = BlockSig { blockInputsSimple = Map.empty
                         , blockInputsPhi = Map.empty
                         , blockOutputs = Map.empty
                         , blockGlobals = Set.empty
                         , blockCalls = Map.empty
                         , blockJumps = Set.empty
                         , blockOrigins = Set.empty }

realizeBlock :: MemoryModel mem => String -> [Instruction] 
                -> SMTExpr Bool
                -> mem
                -> Bool
                -> Map String (Val mem) 
                -> (String -> String -> SMTExpr Bool -> mem -> [(Val mem,TypeDesc)] -> SMT (mem,Maybe (Val mem),[Watchpoint]))
                -> [Watchpoint]
                -> SMT (Maybe mem,Map String (Val mem),Maybe (Maybe (Val mem)),[(String,Maybe (SMTExpr Bool))],[Watchpoint])
realizeBlock fname (instr:instrs) act mem changed values calls watch
    = do
      --liftIO $ print instr
      --liftIO $ putStrLn $ "Values: "++show values
      (nmem,nvalue,ret,jumps,watch') <- realizeInstruction fname instr act mem values calls
      let values' = case nvalue of
            Nothing -> values
            Just (lbl,res) -> Map.insert lbl res values
          (mem',changed') = case nmem of
            Nothing -> (mem,changed)
            Just n -> (n,True)
      case ret of
        Just ret' -> return (if changed then Just mem' else Nothing,values',ret,jumps,watch++watch')
        Nothing -> case jumps of
          _:_ -> return (if changed then Just mem' else Nothing,values',ret,jumps,watch++watch')
          [] -> realizeBlock fname instrs act mem' changed' values' calls (watch ++ watch')

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
                 ConditionValue v w -> ConditionValue v w
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

realizeInstruction :: MemoryModel mem => String -> Instruction
                      -> SMTExpr Bool
                      -> mem 
                      -> Map String (Val mem) 
                      -> (String -> String -> SMTExpr Bool -> mem -> [(Val mem,TypeDesc)] -> SMT (mem,Maybe (Val mem),[Watchpoint]))
                      -> SMT (Maybe mem,Maybe (String,Val mem),Maybe (Maybe (Val mem)),[(String,Maybe (SMTExpr Bool))],[Watchpoint])
realizeInstruction fname instr act mem values calls
  = {-trace ("Realizing "++show instr++"..") $-} case instr of
    IRet e -> return (Nothing,Nothing,Just (Just (argToExpr e values mem)),[],[])
    IRetVoid -> return (Nothing,Nothing,Just Nothing,[],[])
    IBr to -> return (Nothing,Nothing,Nothing,[(to,Nothing)],[])
    IBrCond cond ifT ifF -> case argToExpr cond values mem of
      ConstCondition cond' -> return (Nothing,Nothing,Nothing,[(if cond' then ifT else ifF,Nothing)],[])
      cond' -> return (Nothing,Nothing,Nothing,[(ifT,Just $ valCond cond'),(ifF,Nothing)],[])
    ISwitch val def args -> case argToExpr val values mem of
      ConstValue v -> case [ to | (cmp_v,to) <- args, let ConstValue v' = argToExpr cmp_v values mem, v' == v ] of
        [] -> return (Nothing,Nothing,Nothing,[(def,Nothing)],[])
        [to] -> return (Nothing,Nothing,Nothing,[(to,Nothing)],[])
      v -> return (Nothing,Nothing,Nothing,[ (to,Just $ valEq mem v (argToExpr cmp_v values mem))
                                           | (cmp_v,to) <- args
                                           ] ++ [ (def,Nothing) ],[])
    IAssign trg expr -> return (Nothing,Just (trg,argToExpr expr values mem),Nothing,[],[])
    IAlloca trg tp size align -> do -- TODO: Ignores the size parameter for now
      (ptr,mem') <- memAlloc tp (case argToExpr size values mem of
                                    ConstValue bv -> Left $ BitS.toBits bv
                                    DirectValue bv -> Right bv) Nothing mem
      return (Just mem',Just (trg,PointerValue ptr),Nothing,[],[])
    IStore val to align -> let PointerValue ptr = argToExpr to values mem
                           in case exprType val of
                             TDPtr tp -> case argToExpr val values mem of
                               PointerValue ptr2 -> return (Just $ memStorePtr tp ptr ptr2 mem,Nothing,Nothing,[],[])
                             tp -> return (Just $ memStore tp ptr (valValue $ argToExpr val values mem) mem,Nothing,Nothing,[],[])
    IPhi _ _ -> return (Nothing,Nothing,Nothing,[],[])
    ICall rtp trg _ f args -> case exprDesc f of
                                   EDNamed fn -> do
                                     (mem',ret,watch) <- calls fn trg act mem [ (argToExpr arg values mem,exprType arg) | arg <- args ]
                                     return (Just mem',case ret of
                                                Nothing -> Nothing
                                                Just ret' -> Just (trg,ret'),Nothing,[],watch)
    ILoad trg arg align -> let PointerValue ptr = argToExpr arg values mem
                           in case exprType arg of
                             TDPtr (TDPtr tp) -> return (Nothing,Just (trg,PointerValue $ memLoadPtr tp ptr mem),Nothing,[],[])
                             TDPtr tp -> return (Nothing,Just (trg,DirectValue $ memLoad tp ptr mem),Nothing,[],[])
    _ -> error $ "Implement realizeInstruction for "++show instr
    {-
      IDRet tp arg -> return (Nothing,Nothing,Just (Just (argToExpr tp arg values)),[],[])
      IDRetVoid -> return (Nothing,Nothing,Just Nothing,[],[])
      IDBrCond cond (AL ifT) (AL ifF) -> case argToExpr (TDInt False 1) cond values of
        ConstCondition cond' -> return (Nothing,Nothing,Nothing,[(if cond' then ifT else ifF,Nothing)],[])
        cond' -> return (Nothing,Nothing,Nothing,[(ifT,Just $ valCond cond'),(ifF,Nothing)],[])
      IDBrUncond (AL to) -> return (Nothing,Nothing,Nothing,[(to,Nothing)],[])
      IDSwitch tp ((val,AL def):args) -> case argToExpr tp val values of
        ConstValue v -> case [ to | (cmp_v,AL to) <- args, let ConstValue v' = argToExpr tp cmp_v values, v' == v ] of
          [] -> return (Nothing,Nothing,Nothing,[(def,Nothing)],[])
          [to] -> return (Nothing,Nothing,Nothing,[(to,Nothing)],[])
        v -> return (Nothing,Nothing,Nothing,[ (to,Just $ valEq mem v (argToExpr tp cmp_v values))
                                             | (cmp_v,AL to) <- args
                                             ] ++ [ (def,Nothing) ],[])
      IDBinOp op tp lhs rhs -> let lhs' = argToExpr tp lhs values
                                   rhs' = argToExpr tp rhs values
                                   apply (ConstValue lhs) (ConstValue rhs) = let lhs' = BitS.toBits lhs :: Integer
                                                                                 rhs' = BitS.toBits rhs :: Integer
                                                                                 rop = case op of
                                                                                   BOXor -> Bits.xor
                                                                                   BOAdd -> (+)
                                                                                   BOAnd -> (.&.)
                                                                                   BOSub -> (-)
                                                                                   BOShL -> \x y -> shiftL x (fromIntegral y)
                                                                                   BOOr -> (.|.)
                                                                                 nvalue = ConstValue (BitS.fromNBits (BitS.length lhs) (rop lhs' rhs'))
                                                                             in return (Nothing,Just nvalue,Nothing,[],[])
                                   apply lhs rhs = let lhs' = valValue lhs
                                                       rhs' = valValue rhs
                                                       rop = case op of 
                                                         BOXor -> BVXor
                                                         BOAdd -> BVAdd
                                                         BOAnd -> BVAnd
                                                         BOSub -> BVSub
                                                         BOShL -> BVSHL
                                                         BOOr -> BVOr
                                                         _ -> error $ "unsupported operator: "++show op
                                                       nvalue = DirectValue (rop lhs' rhs')
                                                   in return (Nothing,Just nvalue,Nothing,[],[])
                               in apply lhs' rhs'
      IDAlloca tp _ _ -> do
        (ptr,mem') <- memAlloc False tp mem
        return (Just mem',Just (PointerValue ptr),Nothing,[],[])
      IDLoad tp arg -> let PointerValue ptr = argToExpr (TDPtr tp) arg values
                       in return (Nothing,Just (DirectValue $ memLoad tp ptr mem),Nothing,[],[])
      IDStore tp val to -> let PointerValue ptr = argToExpr (TDPtr tp) to values
                               val' = valValue $ argToExpr tp val values
                           in return (Just $ memStore tp ptr val' mem,Nothing,Nothing,[],[])
      IDGetElementPtr tp_to tp_from (arg:args) -> case argToExpr tp_from arg values of
        PointerValue ptr -> let ptr' = memIndex mem tp_from [ fromIntegral i | AI i <- args ] ptr
                            in return (Nothing,Just (PointerValue ptr'),Nothing,[],[])
        v -> error $ "First argument to getelementptr must be a pointer, but I found: "++show v++" ("++fname++")\n"++show instr
      IDZExt tp tp' var -> let v = valValue $ argToExpr tp' var values
                               d = (bitWidth tp') - (bitWidth tp)
                               nv = bvconcat (constantAnn (BitS.fromNBits d (0::Integer) :: BitVector) (fromIntegral d)) v
                           in return (Nothing,Just (DirectValue nv),Nothing,[],[])
      IDSExt tp tp' var -> let v = valValue $ argToExpr tp' var values
                               d = (bitWidth tp') - (bitWidth tp)
                               s = (bvextract ((bitWidth tp)-1) ((bitWidth tp)-1) v) .==. (constantAnn (BitS.fromNBits 1 (1::Integer)) 1)
                               ext = ite s
                                     (constantAnn (BitS.pack (genericReplicate d True) :: BitVector) (fromIntegral d))
                                     (constantAnn (BitS.pack (genericReplicate d False)) (fromIntegral d))
                               nv = bvconcat ext v
                           in return (Nothing,Just (DirectValue nv),Nothing,[],[])
      IDBitcast (TDPtr tp) (TDPtr tp') arg -> let PointerValue ptr = argToExpr (TDPtr tp') arg values
                                                  nptr = memCast mem tp ptr
                                              in return (Nothing,Just (PointerValue nptr),Nothing,[],[])
      IDICmp pred tp lhs rhs -> let lhs' = argToExpr tp lhs values
                                    rhs' = argToExpr tp rhs values
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
                                                                              in return (Nothing,Just (ConstCondition (op lhs' rhs')),Nothing,[],[])
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
                                                    in return (Nothing,Just (ConditionValue (op lhs' rhs')),Nothing,[],[])
                                in apply lhs' rhs'
      IDPhi _ _ -> return (Nothing,Nothing,Nothing,[],[])
      IDCall _ (AFP fn) args -> do
        (mem',ret,watch) <- calls fn act mem [ (argToExpr tp arg values,tp) | (arg,tp) <- args ]
        return (Just mem',ret,Nothing,[],watch)
      IDSelect tp cond ifT ifF -> let res = case argToExpr (TDInt False 1) cond values of
                                        ConstCondition c -> if c 
                                                            then argToExpr tp ifT values
                                                            else argToExpr tp ifF values
                                        cond' -> DirectValue $ ite 
                                                 (valCond cond') 
                                                 (valValue $ argToExpr tp ifT values) 
                                                 (valValue $ argToExpr tp ifF values)
                                  in return (Nothing,Just res,Nothing,[],[])
      IDTrunc tp_from tp_to arg -> return (Nothing,Just (case argToExpr tp_from arg values of
                                                            ConstValue bv -> ConstValue (BitS.fromNBits (bitWidth tp_to) (BitS.toBits bv :: Integer))
                                                            expr -> DirectValue (bvextract (bitWidth tp_to - 1) 0 (valValue expr))),Nothing,[],[])
      _ -> error $ "Unsupported instruction: "++show instr
    where
      argToExpr :: TypeDesc -> ArgDesc -> Map String (Val m) -> Val m
      argToExpr _ (AV var) mp = case Map.lookup var mp of
                                  Just val -> val
                                  Nothing -> error $ "Failed to find variable "++show var
      argToExpr tp (AI i) _ = if bitWidth tp == 1
                              then ConstCondition (i /= 0)
                              else ConstValue $ BitS.fromNBits (bitWidth tp) i
      argToExpr tp AE mp = ConstValue $ BitS.fromNBits (bitWidth tp) (0::Integer)
      argToExpr tp arg _ = error $ "argToExpr unimplemented for "++show arg

      ncond :: MemoryModel m => Val m -> SMTExpr Bool
      ncond (ConstValue v) = case BitS.unpack v of
                                  [x] -> constant x 
      ncond (DirectValue v) = v .==. (constantAnn (BitS.pack [False]) 1)
   -}

data LabelOrigin = ArgumentOrigin
                 | GlobalOrigin
                 | BlockOrigin String
                 deriving (Eq,Ord,Show)

mkVarBlockMap :: [String] -> [String] -> [(String,[Instruction])] -> Map String LabelOrigin
mkVarBlockMap args globs
  = foldl (\mp (blk,instrs) 
           -> let blk' = BlockOrigin blk
              in foldl (\mp' instr
                        -> case instr of
                          IAssign lbl _ -> Map.insert lbl blk' mp'
                          IAlloca lbl _ __ _ -> Map.insert lbl blk' mp'
                          ILoad lbl _ _ -> Map.insert lbl blk' mp'
                          ICall _ lbl _ _ _ -> Map.insert lbl blk' mp'
                          IVAArg lbl _ _ -> Map.insert lbl blk' mp'
                          IPhi lbl _ -> Map.insert lbl blk' mp'
                          _ -> mp'
                       ) mp instrs
          ) (Map.fromList $ [(arg,ArgumentOrigin) | arg <- args] ++ [(arg,GlobalOrigin) | arg <- globs])

mkBlockSigs :: Map String LabelOrigin -> [(String,[Instruction])] -> Map String BlockSig
mkBlockSigs lbl_mp blks
    = Map.adjust (\sig -> sig { blockOrigins = Set.singleton "" }) (fst $ head blks) $
      foldl (\mp (blk,instrs)
               -> foldl (\mp' instr
                        -> case instr of
                           IRet e -> addExpr blk e mp'
                           IBr to -> addJump blk to mp'
                           IBrCond cond ifT ifF -> addExpr blk cond $
                                                   addJump blk ifT $
                                                   addJump blk ifF mp'
                           ISwitch val def cases -> addExpr blk val $
                                                    addJump blk def $
                                                    foldl (\mp'' (expr,to) -> addExpr blk expr $
                                                                              addJump blk to mp'') mp' cases
                           IIndirectBr e trgs -> addExpr blk e $
                                                 foldl (\mp'' trg -> addJump blk trg mp'') mp' trgs
                           IResume e -> addExpr blk e mp'
                           IAssign _ e -> addExpr blk e mp'
                           ILoad _ ptr _ -> addExpr blk ptr mp'
                           IStore e ptr _ -> addExpr blk e $
                                             addExpr blk ptr mp'
                           IPhi trg cases -> let (mp1,vec) = mapAccumL (\cmp (val,from) -> (addExpr blk val cmp,(from,val))) mp' cases
                                                 mp2 = addPhi blk trg (vec,exprType $ fst $ head cases) mp1
                                             in mp2
                           ICall rtp res cc fn args -> foldl (\mp'' arg -> addExpr blk arg mp'') mp' args
                           _ -> mp'
                           {-
                           IPhi cases -> foldl (\mp'' (e,from) -> addOutput from 
                          IDRet tp arg -> addArg blk arg tp mp'
                          IDBrCond arg (AL ifT) (AL ifF) -> addArg blk arg (TDInt False 1) $
                                                           addJump blk ifT $ addJump blk ifF mp'
                          IDBrUncond (AL to) -> addJump blk to mp'
                          IDSwitch tp ((what,AL def):cases) 
                            -> addArg blk what tp $ addJump blk def $ foldl (\cmp (_,AL to) -> addJump blk to cmp) mp' cases
                          IDBinOp _ tp lhs rhs -> addArg blk lhs tp $ addArg blk rhs tp mp'
                          IDLoad tp arg -> addArg blk arg tp mp'
                          IDStore tp arg trg -> addArg blk arg tp $ addArg blk trg (TDPtr tp) mp'
                          IDGetElementPtr _ tp (arg:_) -> addArg blk arg tp mp'
                          IDTrunc _ tp arg -> addArg blk arg tp mp'
                          IDZExt _ tp arg -> addArg blk arg tp mp'
                          IDSExt _ tp arg -> addArg blk arg tp mp'
                          IDFPtoUI _ tp arg -> addArg blk arg tp mp'
                          IDFPtoSI _ tp arg -> addArg blk arg tp mp'
                          IDUItoFP _ tp arg -> addArg blk arg tp mp'
                          IDSItoFP _ tp arg -> addArg blk arg tp mp'
                          IDFPTrunc _ tp arg -> addArg blk arg tp mp'
                          IDFPExt _ tp arg -> addArg blk arg tp mp'
                          IDPtrToInt _ tp arg -> addArg blk arg tp mp'
                          IDIntToPtr _ tp arg -> addArg blk arg tp mp'
                          IDBitcast _ tp arg -> addArg blk arg tp mp'
                          IDICmp _ tp lhs rhs -> addArg blk lhs tp $ addArg blk rhs tp mp'
                          IDFCmp _ tp lhs rhs -> addArg blk lhs tp $ addArg blk rhs tp mp'
                          IDPhi tp args -> let vec = foldr (\(val,AL from) lst -> case val of
                                                              AE -> lst
                                                              AV var -> (from,Left (lbl_mp!var,var)):lst
                                                              AI i -> (from,Right (BitS.fromNBits (bitWidth tp) i)):lst
                                                          ) [] args
                                               mp1 = foldl (\mp'' (blk',lbl') -> addOutput blk' lbl' tp mp'') mp' [ x | (from,Left x) <- vec ]
                                               mp2 = addInput blk lbl (vec,tp) mp1
                                          in mp2
                          IDCall rtp (AFP fn) args
                            -> addCall blk fn (fmap snd args) rtp $ foldl (\cmp (arg,tp) -> addArg blk arg tp cmp) mp' args
                          IDSelect tp expr lhs rhs -> addArg blk expr (TDInt False 1) $ addArg blk lhs tp $ addArg blk rhs tp mp'
                          _ -> mp' -}
                       ) (Map.insertWith (\n o -> o) blk emptyBlockSig mp) instrs
            ) (Map.singleton "" (emptyBlockSig { blockJumps = Set.singleton $ fst $ head blks })) blks
      where
        addExpr :: String -> Expr -> Map String BlockSig -> Map String BlockSig
        addExpr blk e = case exprDesc e of
          EDNamed name -> case Map.lookup name lbl_mp of
            Nothing -> error $ "Can't find "++name++" in label mapping"
            Just (BlockOrigin blk_from) -> if blk_from==blk
                                           then id
                                           else addOutput blk_from name (exprType e) . addInput blk name (blk_from,e,exprType e)
            Just GlobalOrigin -> addGlobal blk name
          EDUnOp _ arg -> addExpr blk arg
          EDICmp _ lhs rhs -> addExpr blk lhs . addExpr blk rhs
          EDBinOp _ lhs rhs -> addExpr blk lhs . addExpr blk rhs
          EDGetElementPtr expr args -> addExpr blk expr . (\mp -> foldr (addExpr blk) mp args)
          EDInt _ -> id
          EDUndef -> id
          EDNull -> id
          e' -> error $ "Implement addExpr for "++show e'
        {-
        addArg blk arg tp = case arg of
                              AV var -> let blk_from = case Map.lookup var lbl_mp of
                                                         Nothing -> ""
                                                         Just b -> b
                                        in if blk_from==blk
                                           then id
                                           else addOutput blk_from var tp . addInput blk var ([(blk_from,Left (blk_from,var))],tp)
                              _ -> id
        -}
        addPhi blk lbl args = Map.alter (\c -> case c of
                                            Nothing -> Just (emptyBlockSig { blockInputsPhi = Map.singleton lbl args })
                                            Just blksig -> Just $ blksig { blockInputsPhi = Map.insert lbl args (blockInputsPhi blksig) }) blk
        addInput blk lbl args = Map.alter (\c -> case c of
                                                   Nothing -> Just (emptyBlockSig { blockInputsSimple = Map.singleton lbl args })
                                                   Just blksig -> Just $ blksig { blockInputsSimple = Map.insert lbl args (blockInputsSimple blksig) }) blk
        addOutput blk lbl tp = Map.alter (\c -> case c of
                                             Nothing -> Just (emptyBlockSig { blockOutputs = Map.singleton lbl tp })
                                             Just blksig -> Just $ blksig { blockOutputs = Map.insert lbl tp (blockOutputs blksig) }) blk
        {-addCall blk fn argtps rtp = Map.alter (\c -> case c of
                                                       Nothing -> Just (emptyBlockSig { blockCalls = Map.singleton fn (argtps,rtp) })
                                                       Just blksig -> Just $ blksig { blockCalls = Map.insert fn (argtps,rtp) (blockCalls blksig) }) blk-}
        addJump blk to = Map.alter (\c -> case c of
                                            Nothing -> Just (emptyBlockSig { blockJumps = Set.singleton to })
                                            Just blksig -> Just $ blksig { blockJumps = Set.insert to (blockJumps blksig) }) blk .
                         Map.alter (\c -> case c of
                                       Nothing -> Just (emptyBlockSig { blockOrigins = Set.singleton blk })
                                       Just blksig -> Just $ blksig { blockOrigins = Set.insert blk (blockOrigins blksig) }) to
        addGlobal blk lbl = Map.alter (\c -> case c of
                                          Nothing -> Just (emptyBlockSig { blockGlobals = Set.singleton lbl })
                                          Just blksig -> Just $ blksig { blockGlobals = Set.insert lbl (blockGlobals blksig) }) blk

allTypesArgs :: [(String,TypeDesc)] -> [TypeDesc]
allTypesArgs = allTypes' []
    where
      allTypes' tps [] = tps
      allTypes' tps ((name,tp):vals) = case tp of
        TDPtr tp' -> allTypes' (tp':tps) vals
        _ -> allTypes' tps vals

allTypesBlks :: [(String,[Instruction])] -> [TypeDesc]
allTypesBlks = allTypes' [] []
    where
      allTypes' [] tps [] = tps
      allTypes' [] tps ((_,instrs):blks) = allTypes' instrs tps blks
      allTypes' (i:is) tps blks = case i of
                                        ILoad lbl e _ -> case exprType e of
                                          TDPtr tp -> allTypes' is (tp:tps) blks
                                        IAlloca lbl tp _ _ -> allTypes' is (tp:tps) blks
                                        
                                        _ -> allTypes' is tps blks

intr_memcpy,intr_memset,intr_restrict,intr_watch,intr_malloc :: MemoryModel mem => Maybe TypeDesc -> SMTExpr Bool -> mem -> [(Val mem,TypeDesc)] -> SMT (mem,Maybe (Val mem),[Watchpoint])
intr_memcpy _ _ mem [(PointerValue to,_),(PointerValue from,_),(ConstValue len,_),_,_]
  = return (memCopy (BitS.toBits len) to from mem,Nothing,[])

intr_memset _ _ mem [(PointerValue dest,_),(val,_),(ConstValue len,_),_,_]
  = return (memSet (BitS.toBits len) (valValue val) dest mem,Nothing,[])

intr_restrict _ act mem [(val,_)] = do
  comment " Restriction:"
  case val of
    ConditionValue val _ -> assert $ act .=>. val
    _ -> assert $ act .=>. (not' $ valValue val .==. constantAnn (BitS.fromNBits (32::Int) (0::Integer)) 32)
  return (mem,Nothing,[])

intr_watch _ act mem ((ConstValue num,_):exprs)
  = return (mem,Nothing,[(show (BitS.toBits num :: Integer),act,[ (tp,valValue val) | (val,tp) <- exprs ])])

intr_malloc (Just tp) act mem [(size,sztp)] = do
  (ptr,mem') <- memAlloc tp (case size of
                                ConstValue bv -> Left $ BitS.toBits bv
                                DirectValue bv -> Right bv) Nothing mem
  return (mem',Just (PointerValue ptr),[])

intr_nondet :: MemoryModel mem => Integer -> Maybe TypeDesc -> SMTExpr Bool -> mem -> [(Val mem,TypeDesc)] -> SMT (mem,Maybe (Val mem),[Watchpoint])
intr_nondet width _ _ mem [] = do
  v <- varAnn (fromIntegral width)
  return (mem,Just (DirectValue v),[])

intrinsics :: MemoryModel mem => String -> Maybe (Maybe TypeDesc -> SMTExpr Bool -> mem -> [(Val mem,TypeDesc)] -> SMT (mem,Maybe (Val mem),[Watchpoint]))
intrinsics "llvm.memcpy.p0i8.p0i8.i64" = Just intr_memcpy
intrinsics "llvm.memcpy.p0i8.p0i8.i32" = Just intr_memcpy
intrinsics "llvm.memset.p0i8.i32" = Just intr_memset
intrinsics "llvm.memset.p0i8.i64" = Just intr_memset
intrinsics "furchtbar_restrict" = Just intr_restrict
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

type ProgDesc = (Map String ([(String,TypeDesc)],TypeDesc,[(String,[Instruction])]),Map String (TypeDesc,MemContent,Bool))

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
                                                                   return (name,instrs))
                  return (name,(pars,tp,blks))) funs
  return (Map.fromList res,glob)

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
               , showHelp :: Bool
               } deriving (Eq,Ord,Show)

defaultOptions :: Options
defaultOptions = Options { entryPoint = "main" 
                         , bmcDepth = 10
                         , files = []
                         , memoryModel = PlainModel
                         , solver = Nothing
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
          perform program (entryPoint opts) (bmcDepth opts) :: SMT TypedMemory
          return ()
        UntypedModel -> do
          perform program (entryPoint opts) (bmcDepth opts) :: SMT UntypedMemory
          return ()
        BlockModel -> do
          perform program (entryPoint opts) (bmcDepth opts) :: SMT UntypedBlockMemory
          return ()
        PlainModel -> do
          perform program (entryPoint opts) (bmcDepth opts) :: SMT PlainMemory
          return ()
      )
  where
    perform :: (MemoryModel mem)
               => ProgDesc -> String -> Integer -> SMT mem
    perform program entry depth = do
      (mem_in,mem_out,watches) <- translateProgram program entry depth
      liftIO $ putStrLn "Done translating program"
      checkSat
      liftIO $ putStrLn "Found a solution"
      --dump_in <- memDump mem_in
      --dump_out <- memDump mem_out
      --liftIO $ putStrLn dump_in
      --liftIO $ putStrLn dump_out
      mapM_ (\(name,act,vals) -> do
                ract <- getValue act
                if ract
                  then (do
                           rvals <- mapM (\(tp,val) -> getValue' (fromIntegral $ bitWidth tp) val) vals
                           liftIO $ putStrLn $ "Watchpoint "++name++":"
                             ++concat (fmap (\rval -> " "++show (BitS.toBits rval :: Integer)) rvals))
                  else return ()
            ) watches
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

predictMallocUse :: [(String,[Instruction])] -> Map String TypeDesc
predictMallocUse = predict' Map.empty Set.empty []
  where
    predict' mp act [] [] = Map.union mp (Map.fromList [ (entr,TDInt False 8) | entr <- Set.toList act ])
    predict' mp act [] ((name,instrs):blks) = predict' mp act instrs blks
    predict' mp act (instr:instrs) blks = case instr of
      ICall _ name _ (Expr { exprDesc = EDNamed "malloc" }) _ -> predict' mp (Set.insert name act) instrs blks
      IAssign _ (Expr { exprDesc = EDGetElementPtr (Expr { exprDesc = EDNamed name })  _ }) -> if Set.member name act
                                                                                               then predict' (Map.insert name (TDInt False 8) mp) (Set.delete name act) instrs blks
                                                                                               else predict' mp act instrs blks
      IAssign _ (Expr { exprDesc = EDUnOp UOBitcast (Expr { exprDesc = EDNamed name })
                      , exprType = TDPtr tp }) -> if Set.member name act
                                                  then predict' (Map.insert name tp mp) (Set.delete name act) instrs blks
                                                  else predict' mp act instrs blks
      ILoad _ (Expr { exprDesc = EDNamed name }) _ -> if Set.member name act
                                                      then predict' (Map.insert name (TDInt False 8) mp) (Set.delete name act) instrs blks
                                                      else predict' mp act instrs blks
      _ -> predict' mp act instrs blks