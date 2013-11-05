module SMTHelper where

import Language.SMTLib2
import Language.SMTLib2.Internals

isComplexExpr :: SMTExpr a -> Bool
isComplexExpr (Const _ _) = False
isComplexExpr (Var _ _) = False
isComplexExpr _ = True
