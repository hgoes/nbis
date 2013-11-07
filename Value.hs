{-# LANGUAGE DeriveDataTypeable #-}
module Value where

import MemoryModel
import TypeDesc
import SMTHelper

import Language.SMTLib2 as SMT2
import Data.Typeable
import Data.Bits as Bits
import LLVM.FFI.Instruction

data Val = ConstValue { asConst :: Integer
                      , constWidth :: Integer }
         | DirectValue { asValue :: SMTExpr (BitVector BVUntyped) }
         | ConditionValue { asCondition :: SMTExpr Bool
                          , conditionWidth :: Integer }
         | ConstCondition { asConstCondition :: Bool }
         deriving (Typeable,Eq)

instance Show Val where
  show (ConstValue c _) = show c
  show (DirectValue dv) = show dv
  show (ConditionValue c _) = show c
  show (ConstCondition c) = show c

valValue :: Val -> SMTExpr (BitVector BVUntyped)
valValue (ConstValue x w) = constantAnn (BitVector x) w
valValue (DirectValue x) = x
valValue (ConditionValue x w) = ite x (constantAnn (BitVector 1) (fromIntegral w)) (constantAnn (BitVector 0) (fromIntegral w))
valValue (ConstCondition x) = constantAnn (BitVector $ if x then 1 else 0) 1

valCond :: Val -> SMTExpr Bool
valCond (ConstValue x 1) = constant $ x==1
valCond (ConstValue _  _) = error "A constant of bit-length > 1 is used in a condition"
valCond (DirectValue x) = x .==. (constantAnn (BitVector 1) 1)
valCond (ConditionValue x _) = x
valCond (ConstCondition x) = constant x

valEq :: Val -> Val -> SMTExpr Bool
valEq (ConstValue x _) (ConstValue y _) = constant $ x==y
valEq (ConstValue x w) (DirectValue y) = y .==. constantAnn (BitVector x) w
valEq (DirectValue x) (ConstValue y w) = x .==. constantAnn (BitVector y) w
valEq (DirectValue v1) (DirectValue v2) = v1 .==. v2
valEq (ConditionValue v1 _) (ConditionValue v2 _) = v1 .==. v2
valEq (ConditionValue v1 w1) (ConstValue v2 w2) = if v2 == 1
                                                  then v1
                                                  else not' v1
valEq (ConstValue v1 _) (ConditionValue v2 _) = if v1 == 1
                                                then v2
                                                else not' v2
valEq (ConditionValue v1 w) (DirectValue v2)
  = v1 .==. (v2 .==. (constantAnn (BitVector 1) (fromIntegral w)))
valEq (DirectValue v2) (ConditionValue v1 w) 
  = v1 .==. (v2 .==. (constantAnn (BitVector 1) (fromIntegral w)))
valEq (ConstCondition x) (ConstCondition y) = constant (x == y)
valEq (ConstCondition x) (ConditionValue y _) = if x then y else not' y
valEq (ConditionValue x _) (ConstCondition y) = if y then x else not' x

valSwitch :: [(Val,SMTExpr Bool)] -> Val
valSwitch [(val,cond)] = val
valSwitch ((val,cond):rest) 
  = case (val,valSwitch rest) of
  (ConditionValue v1 w,ConditionValue v2 _) -> ConditionValue (ite cond v1 v2) w
  (x,xs) -> DirectValue (ite cond (valValue x) (valValue xs))

valIntComp :: ICmpOp -> Val -> Val -> Val
valIntComp op (ConstValue lhs _) (ConstValue rhs _)
  = ConstCondition $ case op of
  I_EQ -> lhs == rhs
  I_NE -> lhs /= rhs
  I_UGT -> lhs > rhs
  I_UGE -> lhs >= rhs
  I_ULT -> lhs < rhs
  I_ULE -> lhs <= rhs
  I_SGT -> lhs > rhs
  I_SGE -> lhs >= rhs
  I_SLT -> lhs < rhs
  I_SLE -> lhs <= rhs
valIntComp op lhs rhs
  = let lhs' = valValue lhs
        rhs' = valValue rhs
    in ConditionValue (case op of
                          I_EQ -> lhs' .==. rhs'
                          I_NE -> not' (lhs' .==. rhs')
                          I_UGT -> bvugt lhs' rhs'
                          I_UGE -> bvuge lhs' rhs'
                          I_ULT -> bvult lhs' rhs'
                          I_ULE -> bvule lhs' rhs'
                          I_SGT -> bvsgt lhs' rhs'
                          I_SGE -> bvsge lhs' rhs'
                          I_SLT -> bvslt lhs' rhs'
                          I_SLE -> bvsle lhs' rhs') 1

valBinOp ::  BinOpType -> Val -> Val -> Val
valBinOp op (ConstValue lhs w) (ConstValue rhs _)
  = ConstValue (case op of
                   Xor -> Bits.xor lhs rhs
                   Add -> lhs + rhs
                   And -> lhs .&. rhs
                   Sub -> lhs - rhs
                   Shl -> shiftL lhs (fromIntegral rhs)
                   Or -> lhs .|. rhs
                   Mul -> lhs * rhs
                   SRem -> lhs `rem` rhs
                   SDiv -> lhs `div` rhs
                   _ -> error $ "Unsupported operator for constant values: "++show op
               ) w
valBinOp op l@(ConditionValue lhs w) r@(ConditionValue rhs _) = case op of
  Xor -> ConditionValue (app SMT2.xor [lhs,rhs]) w
  Add -> DirectValue (bvadd (valValue l) (valValue r))
  And -> ConditionValue (lhs .&&. rhs) w
  Sub -> DirectValue (bvsub (valValue l) (valValue r))
  Shl -> DirectValue (bvshl (valValue l) (valValue r))
  LShr -> DirectValue (bvlshr (valValue l) (valValue r))
  Or -> ConditionValue (lhs .||. rhs) w
  Mul -> DirectValue (bvmul (valValue l) (valValue r))
  SDiv -> DirectValue (bvsdiv (valValue l) (valValue r))
  _ -> error $ "nbis: Unsupported binary operator "++show op
valBinOp op lhs rhs 
  = let lhs' = valValue lhs
        rhs' = valValue rhs
        rop = case op of
          Xor -> bvxor
          Add -> bvadd
          And -> bvand
          Sub -> bvsub
          Shl -> bvshl
          LShr -> bvlshr
          Or -> bvor
          Mul -> bvmul
          SRem -> bvsrem
          SDiv -> bvsdiv
          _ -> error $ "nbis: Unsupported binary operator "++show op
    in DirectValue (rop lhs' rhs')

valNew :: String -> TypeDesc -> SMT Val
valNew name (IntegerType 1) = do
  res <- varNamed name
  return $ ConditionValue res 1
valNew name tp = do
  res <- varNamedAnn name (fromIntegral $ bitWidth
                           (error "Can't create value for pointer type")
                           (error "Can't create value for struct type") tp)
  return $ DirectValue res

valCopy :: String -> Val -> SMT Val
valCopy name (DirectValue val) = do
  nval <- defConstNamed name val
  return (DirectValue nval)
valCopy name (ConditionValue c w) = do
  nc <- defConstNamed name c
  return (ConditionValue nc w)
valCopy _ v = return v

valNewSameType :: String -> Val -> SMT Val
valNewSameType name (ConstValue { constWidth = w }) = do
  var <- varNamedAnn name w
  return (DirectValue var)
valNewSameType name (DirectValue v) = do
  var <- varNamedAnn name (extractAnnotation v)
  return (DirectValue var)
valNewSameType name (ConditionValue { asCondition = c
                                    , conditionWidth = w }) = do
  var <- varNamed name
  return (ConditionValue { asCondition = var
                         , conditionWidth = w })
valNewSameType name (ConstCondition c) = do
  var <- varNamed name
  return (ConditionValue { asCondition = var
                         , conditionWidth = 1 })

valOptimize :: Val -> Val
valOptimize (DirectValue x) = DirectValue $ optimizeExpr' x
valOptimize (ConditionValue c w) = ConditionValue (optimizeExpr' c) w
valOptimize x = x

valIsComplex :: Val -> Bool
valIsComplex (DirectValue x) = isComplexExpr x
valIsComplex (ConditionValue c _) = isComplexExpr c
valIsComplex _ = False
