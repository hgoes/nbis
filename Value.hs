{-# LANGUAGE DeriveDataTypeable #-}
module Value where

import MemoryModel

import Language.SMTLib2
import Data.Typeable
import LLVM.Core
import Data.Bits as Bits

data Val m = ConstValue { asConst :: Integer
                        , constWidth :: Integer }
           | DirectValue { asValue :: SMTExpr (BitVector BVUntyped) }
           | PointerValue { asPointer :: Pointer m }
           | ConditionValue { asCondition :: SMTExpr Bool
                            , conditionWidth :: Integer }
           | ConstCondition { asConstCondition :: Bool }
             deriving (Typeable)

instance Show (Val m) where
  show (ConstValue c _) = show c
  show (DirectValue dv) = show dv
  show (PointerValue _) = "<pointer>"
  show (ConditionValue c _) = show c
  show (ConstCondition c) = show c

valValue :: Val m -> SMTExpr (BitVector BVUntyped)
valValue (ConstValue x w) = constantAnn (BitVector x) w
valValue (DirectValue x) = x
valValue (ConditionValue x w) = ite x (constantAnn (BitVector 1) (fromIntegral w)) (constantAnn (BitVector 0) (fromIntegral w))
valValue (ConstCondition x) = constantAnn (BitVector $ if x then 1 else 0) 1

valCond :: Val m -> SMTExpr Bool
valCond (ConstValue x 1) = constant $ x==1
valCond (ConstValue _  _) = error "A constant of bit-length > 1 is used in a condition"
valCond (DirectValue x) = x .==. (constantAnn (BitVector 1) 1)
valCond (ConditionValue x _) = x
valCond (ConstCondition x) = constant x

valEq :: MemoryModel m => m -> Val m -> Val m -> (SMTExpr Bool,m)
valEq mem (ConstValue x _) (ConstValue y _) = (if x==y then constant True else constant False,mem)
valEq mem (ConstValue x w) (DirectValue y) = (y .==. constantAnn (BitVector x) w,mem)
valEq mem (DirectValue x) (ConstValue y w) = (x .==. constantAnn (BitVector y) w,mem)
valEq mem (DirectValue v1) (DirectValue v2) = (v1 .==. v2,mem)
valEq mem (PointerValue p1) (PointerValue p2) = memPtrEq mem p1 p2
valEq mem (ConditionValue v1 _) (ConditionValue v2 _) = (v1 .==. v2,mem)
valEq mem (ConditionValue v1 w1) (ConstValue v2 w2)
  = (if v2 == 1
     then v1
     else not' v1,mem)
valEq mem (ConstValue v1 _) (ConditionValue v2 _)
  = (if v1 == 1
     then v2
     else not' v2,mem)
valEq mem (ConditionValue v1 w) (DirectValue v2)
  = (v1 .==. (v2 .==. (constantAnn (BitVector 1) (fromIntegral w))),mem)
valEq mem (DirectValue v2) (ConditionValue v1 w) 
  = (v1 .==. (v2 .==. (constantAnn (BitVector 1) (fromIntegral w))),mem)
valEq mem (ConstCondition x) (ConstCondition y) = (constant (x == y),mem)
valEq mem (ConstCondition x) (ConditionValue y _) = (if x then y else not' y,mem)
valEq mem (ConditionValue x _) (ConstCondition y) = (if y then x else not' x,mem)

valSwitch :: [(Val m,SMTExpr Bool)] -> Val m
valSwitch [(val,cond)] = val
valSwitch ((val,cond):rest) 
  = case (val,valSwitch rest) of
  (ConditionValue v1 w,ConditionValue v2 _) -> ConditionValue (ite cond v1 v2) w
  (x,xs) -> DirectValue (ite cond (valValue x) (valValue xs))

valIntComp :: IntPredicate -> Val m -> Val m -> Val m
valIntComp op (ConstValue lhs _) (ConstValue rhs _)
  = ConstCondition $ case op of
  IntEQ -> lhs == rhs
  IntNE -> lhs /= rhs
  IntUGT -> lhs > rhs
  IntUGE -> lhs >= rhs
  IntULT -> lhs < rhs
  IntULE -> lhs <= rhs
  IntSGT -> lhs > rhs
  IntSGE -> lhs >= rhs
  IntSLT -> lhs < rhs
  IntSLE -> lhs <= rhs
valIntComp op lhs rhs
  = let lhs' = valValue lhs
        rhs' = valValue rhs
    in ConditionValue (case op of
                          IntEQ -> lhs' .==. rhs'
                          IntNE -> not' (lhs' .==. rhs')
                          IntUGT -> bvugt lhs' rhs'
                          IntUGE -> bvuge lhs' rhs'
                          IntULT -> bvult lhs' rhs'
                          IntULE -> bvule lhs' rhs'
                          IntSGT -> bvsgt lhs' rhs'
                          IntSGE -> bvsge lhs' rhs'
                          IntSLT -> bvslt lhs' rhs'
                          IntSLE -> bvsle lhs' rhs') 1

valBinOp ::  BinOpDesc -> Val m -> Val m -> Val m
valBinOp op (ConstValue lhs w) (ConstValue rhs _)
  = ConstValue (case op of
                   BOXor -> Bits.xor lhs rhs
                   BOAdd -> lhs + rhs
                   BOAnd -> lhs .&. rhs
                   BOSub -> lhs - rhs
                   BOShL -> shiftL lhs (fromIntegral rhs)
                   BOOr -> lhs .|. rhs
                   BOMul -> lhs * rhs) w
valBinOp op lhs rhs 
  = let lhs' = valValue lhs
        rhs' = valValue rhs
        rop = case op of
          BOXor -> bvxor
          BOAdd -> bvadd
          BOAnd -> bvand
          BOSub -> bvsub
          BOShL -> bvshl
          BOLShR -> bvlshr
          BOOr -> bvor
          BOMul -> bvmul
          _ -> error $ "nbis: Unsupported binary operator "++show op
    in DirectValue (rop lhs' rhs')