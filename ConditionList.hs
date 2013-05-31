module ConditionList where

import Language.SMTLib2
import Simplifier

type CondList a = [(SMTExpr Bool,a)]

simplifyCondList :: CondList a -> CondList a
simplifyCondList [] = []
simplifyCondList ((c,x):xs) = let c' = simplifier c
                              in (if isFalse c'
                                  then simplifyCondList xs
                                  else (c',x):simplifyCondList xs)

mergeCondList :: Eq a => CondList a -> CondList a -> CondList a
mergeCondList [] ys = ys
mergeCondList (x:xs) ys = mergeCondList xs (insert x ys)
  where
    insert x [] = [x]
    insert x@(cx,objx) (y@(cy,objy):ys) = if objx==objy
                                          then (simplifier $ cx .||. cy,objx):ys
                                          else y:(insert x ys)