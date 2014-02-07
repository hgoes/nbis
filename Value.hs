{-# LANGUAGE DeriveDataTypeable #-}
module Value where

import TypeDesc
import SMTHelper

import Language.SMTLib2 as SMT2
import Language.SMTLib2.Pipe (renderExpr)
import Data.Typeable
import Data.Bits as Bits
import LLVM.FFI.Instruction

data Val = ConstValue { asConst :: Integer
                      , constWidth :: Integer }
         | DirectValue { asValue :: SMTExpr (BitVector BVUntyped) }
         | ConditionValue { asCondition :: BoolVal
                          , conditionWidth :: Integer }
         deriving (Typeable,Eq)

data BoolVal = ConstBool Bool
             | DirectBool (SMTExpr Bool)
             deriving (Typeable,Eq)

renderValue :: Val -> SMT String
renderValue (ConstValue c _) = return $ show c
renderValue (DirectValue dv) = renderExpr dv
renderValue (ConditionValue c _) = renderBoolValue c

renderBoolValue :: BoolVal -> SMT String
renderBoolValue (ConstBool c) = return $ show c
renderBoolValue (DirectBool v) = renderExpr v

valValue :: Val -> SMTExpr (BitVector BVUntyped)
valValue (ConstValue x w) = constantAnn (BitVector x) w
valValue (DirectValue x) = x
valValue (ConditionValue (ConstBool b) w)
  = constantAnn (BitVector (if b then 1 else 0)) (fromIntegral w)
valValue (ConditionValue (DirectBool x) w)
  = ite x (constantAnn (BitVector 1) (fromIntegral w)) (constantAnn (BitVector 0) (fromIntegral w))

boolValValue :: BoolVal -> SMTExpr Bool
boolValValue (ConstBool c) = constant c
boolValValue (DirectBool c) = c

valCond :: Val -> SMTExpr Bool
valCond (ConstValue x 1) = constant $ x==1
valCond (ConstValue _  _) = error "A constant of bit-length > 1 is used in a condition"
valCond (DirectValue x) = x .==. (constantAnn (BitVector 1) 1)
valCond (ConditionValue c _) = boolValValue c

valCond' :: Val -> BoolVal
valCond' (ConstValue x 1) = ConstBool (x==1)
valCond' (ConstValue _ _) = error "A constant of bit-length > 1 is used in a condition"
valCond' (DirectValue x) = case extractAnnotation x of
  1 -> DirectBool $ x .==. constantAnn (BitVector 1) 1
  _ -> error "A constant of bit-length > 1 is used in a condition"
valCond' (ConditionValue c _) = c

valEq :: Val -> Val -> SMTExpr Bool
valEq (ConstValue x _) (ConstValue y _) = constant $ x==y
valEq (ConstValue x w) (DirectValue y) = y .==. constantAnn (BitVector x) w
valEq (ConstValue x _) (ConditionValue (ConstBool b) _)
  = constant $ (x==0 && not b) || (x/=0 && b)
valEq (ConstValue x _) (ConditionValue (DirectBool b) _)
  = if x==0
    then not' b
    else b
valEq (DirectValue x) (ConstValue y w) = x .==. (constantAnn (BitVector y) w)
valEq (DirectValue x) (DirectValue y) = x .==. y
valEq (DirectValue x) (ConditionValue (ConstBool b) w)
  = if b
    then not' $ x .==. (constantAnn (BitVector 0) w)
    else x .==. (constantAnn (BitVector 0) w)
valEq (DirectValue x) (ConditionValue (DirectBool b) w)
  = ite b (not' $ x .==. (constantAnn (BitVector 0) w))
          (x .==. (constantAnn (BitVector 0) w))
valEq (ConditionValue (ConstBool b) _) (ConstValue c _)
  = constant $ (c==0 && not b) || (c/=0 && b)
valEq (ConditionValue (ConstBool b) w) (DirectValue x)
  = if b
    then not' $ x .==. (constantAnn (BitVector 0) w)
    else x .==. (constantAnn (BitVector 0) w)
valEq (ConditionValue (ConstBool b) _) (ConditionValue (ConstBool b') _)
  = constant $ b==b'
valEq (ConditionValue (ConstBool b) _) (ConditionValue (DirectBool b') _)
  = if b then b' else not' b'
valEq (ConditionValue (DirectBool b) _) (ConstValue c _)
  = if c==0 then not' b else b
valEq (ConditionValue (DirectBool b) w) (DirectValue y)
  = ite b (not' $ y .==. (constantAnn (BitVector 0) w))
          (y .==. (constantAnn (BitVector 0) w))
valEq (ConditionValue (DirectBool b) _) (ConditionValue (ConstBool b') _)
  = if b' then b else not' b
valEq (ConditionValue (DirectBool b) _) (ConditionValue (DirectBool b') _)
  = b .==. b'

valSwitch :: [(Val,BoolVal)] -> Val
valSwitch [(val,cond)] = val
valSwitch ((val,cond):rest) 
  = case cond of
  ConstBool True -> val
  ConstBool False -> valSwitch rest
  DirectBool c -> case (val,valSwitch rest) of
    (ConditionValue v1 w,ConditionValue v2 _)
      -> ConditionValue (DirectBool $ ite c (boolValValue v1) (boolValValue v2)) w
    (x,xs) -> DirectValue (ite c (valValue x) (valValue xs))

valIntComp :: ICmpOp -> Val -> Val -> BoolVal
valIntComp op (ConstValue lhs _) (ConstValue rhs _)
  = ConstBool $ case op of
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
    in DirectBool (case op of
                      I_EQ -> lhs' .==. rhs'
                      I_NE -> not' (lhs' .==. rhs')
                      I_UGT -> bvugt lhs' rhs'
                      I_UGE -> bvuge lhs' rhs'
                      I_ULT -> bvult lhs' rhs'
                      I_ULE -> bvule lhs' rhs'
                      I_SGT -> bvsgt lhs' rhs'
                      I_SGE -> bvsge lhs' rhs'
                      I_SLT -> bvslt lhs' rhs'
                      I_SLE -> bvsle lhs' rhs')

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
valBinOp op l@(ConditionValue (DirectBool lhs) w) r@(ConditionValue (DirectBool rhs) _)
  = case op of
  Xor -> ConditionValue (DirectBool (app SMT2.xor [lhs,rhs])) w
  Add -> DirectValue (bvadd (valValue l) (valValue r))
  And -> ConditionValue (DirectBool $ lhs .&&. rhs) w
  Sub -> DirectValue (bvsub (valValue l) (valValue r))
  Shl -> DirectValue (bvshl (valValue l) (valValue r))
  LShr -> DirectValue (bvlshr (valValue l) (valValue r))
  Or -> ConditionValue (DirectBool $ lhs .||. rhs) w
  Mul -> DirectValue (bvmul (valValue l) (valValue r))
  SDiv -> DirectValue (bvsdiv (valValue l) (valValue r))
  UDiv -> DirectValue (bvudiv (valValue l) (valValue r))
  URem -> DirectValue (bvurem (valValue l) (valValue r))
  AShr -> DirectValue (bvashr (valValue l) (valValue r))
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
          UDiv -> bvudiv
          URem -> bvurem
          AShr -> bvashr
          _ -> error $ "nbis: Unsupported binary operator "++show op
    in DirectValue (rop lhs' rhs')

valNew :: String -> TypeDesc -> SMT Val
valNew name (IntegerType 1) = do
  res <- varNamed name
  return $ ConditionValue (DirectBool res) 1
valNew name tp = do
  res <- varNamedAnn name (fromIntegral $ bitWidth
                           (error "Can't create value for pointer type")
                           (error "Can't create value for struct type") tp)
  return $ DirectValue res

valCopy :: String -> Val -> SMT Val
valCopy name (DirectValue val) = do
  nval <- defConstNamed name val
  return (DirectValue nval)
valCopy name (ConditionValue (DirectBool c) w) = do
  nc <- defConstNamed name c
  return (ConditionValue (DirectBool nc) w)
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
  return (ConditionValue { asCondition = DirectBool var
                         , conditionWidth = w })

valOptimize :: Val -> Val
valOptimize (DirectValue x) = DirectValue $ optimizeExpr' x
valOptimize (ConditionValue (DirectBool c) w)
  = ConditionValue (DirectBool $ optimizeExpr' c) w
valOptimize x = x

valIsComplex :: Val -> Bool
valIsComplex (DirectValue x) = isComplexExpr x
valIsComplex (ConditionValue (DirectBool c) _) = isComplexExpr c
valIsComplex _ = False

valConstInt :: Val -> Maybe Integer
valConstInt (ConstValue c _) = Just c
valConstInt (ConditionValue (ConstBool b) _) = Just $ if b then 1 else 0
valConstInt _ = Nothing

valWidth :: Val -> Integer
valWidth (ConstValue _ w) = w
valWidth (DirectValue v) = extractAnnotation v
valWidth (ConditionValue _ w) = w

boolValNot :: BoolVal -> BoolVal
boolValNot (ConstBool c) = ConstBool (not c)
boolValNot (DirectBool c) = DirectBool (not' c)
