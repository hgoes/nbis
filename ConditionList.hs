module ConditionList where

import Language.SMTLib2

data ConditionList a
  = CondIf a (SMTExpr Bool) (ConditionList a)
  | CondElse a

instance Show a => Show (ConditionList a) where
  show (CondIf x cond rest) = "if "++show cond++" then "++show x++" else ("++show rest++")"
  show (CondElse x) = show x

accumConditions :: ConditionList a -> [(a,Maybe (SMTExpr Bool))]
accumConditions = accum' []
  where
    accum' [] (CondIf x cond rest) = (x,Just cond):accum' [not' cond] rest
    accum' [] (CondElse x) = [(x,Nothing)]
    accum' conds (CondIf x cond rest)
      = (x,Just (app and' (conds++[cond]))):accum' (conds++[not' cond]) rest
    accum' conds (CondElse x) = [(x,Just (app and' conds))]