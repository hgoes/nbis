{-# LANGUAGE ExistentialQuantification #-}
module DecisionTree 
       (DecisionTree()
       ,decision
       ,boolDecision
       ,switchDecision
       ,accumDecisionTree
       ,decisionTreeEq)
       where

import Language.SMTLib2
import Data.Typeable
import Data.Foldable
import Data.Traversable
import Control.Applicative
import Data.Monoid

data DecisionTree a
  = BoolNode (SMTExpr Bool) (DecisionTree a) (DecisionTree a)
  | forall b. SMTType b => SwitchNode (SMTExpr b) (Maybe (DecisionTree a)) [(SMTExpr b,DecisionTree a)]
  | GroundNode a

instance Functor DecisionTree where
  fmap f (GroundNode x) = GroundNode (f x)
  fmap f (BoolNode c x y) = BoolNode c (fmap f x) (fmap f y)
  fmap f (SwitchNode cmp def cases) = SwitchNode cmp (fmap (fmap f) def) (fmap (\(cmp',tree) -> (cmp',fmap f tree)) cases)

instance Eq a => Eq (DecisionTree a) where
  (==) (GroundNode x) (GroundNode y) = x==y
  (==) (BoolNode c1 x1 y1) (BoolNode c2 x2 y2) = c1==c2 && x1==x2 && y1==y2
  (==) (SwitchNode cmp1 def1 cases1) (SwitchNode cmp2 def2 cases2) = case gcast cmp2 of
    Nothing -> False
    Just cmp2' -> cmp1 == cmp2' && def1 == def2 &&
                  cases1 == fmap (\(expr,tree) -> case gcast expr of
                                     Just expr' -> (expr',tree)) cases2
  (==) _ _ = False

instance Foldable DecisionTree where
  foldMap f (GroundNode x) = f x
  foldMap f (BoolNode _ x y) = (foldMap f x) `mappend` (foldMap f y)
  foldMap f (SwitchNode _ def cases) = (case def of
                                           Nothing -> mempty
                                           Just def' -> foldMap f def') `mappend`
                                       (foldMap (foldMap f . snd) cases)

instance Traversable DecisionTree where
  traverse f (GroundNode x) = GroundNode <$> f x
  traverse f (BoolNode c ifT ifF) = BoolNode c <$> traverse f ifT <*> traverse f ifF
  traverse f (SwitchNode c Nothing cases)
    = SwitchNode c Nothing <$> traverse (\(val,dt) -> fmap (\ndt -> (val,ndt)) (traverse f dt)) cases
  traverse f (SwitchNode c (Just def) cases)
    = SwitchNode c <$> (Just <$> traverse f def) <*> traverse (\(val,dt) -> fmap (\ndt -> (val,ndt)) (traverse f dt)) cases

{-
unrollDecisionTree :: SMTType b => (a -> SMTExpr b) -> DecisionTree a -> SMTExpr b
unrollDecisionTree f (GroundNode x) = f x
unrollDecisionTree f (BoolNode cond x y) = ite cond (unrollDecisionTree f x) (unrollDecisionTree f y)
unrollDecisionTree f (SwitchNode cmp def cases) = mkCompare cases
  where
    mkCompare [] = case def of
      Just def' -> unrollDecisionTree f def'
    mkCompare [(cmp',tree)] = case def of
      Nothing -> unrollDecisionTree f tree
      Just def' -> ite (cmp .==. cmp') (unrollDecisionTree f tree) (unrollDecisionTree f def')
    mkCompare ((cmp',tree):rest) = ite (cmp .==. cmp') (unrollDecisionTree f tree) (mkCompare rest)
-}

boolDecision :: SMTExpr Bool -> DecisionTree a -> DecisionTree a -> DecisionTree a
boolDecision = BoolNode

switchDecision :: SMTType b => SMTExpr b -> (Maybe (DecisionTree a)) -> [(SMTExpr b,DecisionTree a)] -> DecisionTree a
switchDecision = SwitchNode

decision :: a -> DecisionTree a
decision = GroundNode

decisionTreeEq :: (a -> a -> Either Bool (SMTExpr Bool)) -> DecisionTree a -> DecisionTree a -> SMTExpr Bool
decisionTreeEq f x y = case mkEq f x y of
  Left c -> constant c
  Right cond -> cond
  where
    mkEq :: (a -> a -> Either Bool (SMTExpr Bool)) -> DecisionTree a -> DecisionTree a -> Either Bool (SMTExpr Bool)
    mkEq f (GroundNode x) (GroundNode y) = f x y
    mkEq f (BoolNode c x1 x2) y = case mkEq f x1 y of
      Left True -> case mkEq f x2 y of
        Left True -> Left True
        Left False -> Right c
        Right e -> Right $ (not' c) .=>. e
      Left False -> case mkEq f x2 y of
        Left True -> Right $ not' c
        Left False -> Left False
        Right e -> Right ((not' c) .&&. e)
      Right e1 -> case mkEq f x2 y of
        Left True -> Right $ c .=>. e1
        Left False -> Right $ c .&&. e1
        Right e2 -> Right (ite c e1 e2)
    mkEq f (SwitchNode cmp def cases) y = mkEqSwitch f cmp def cases [] y
    mkEq f x y = mkEq f y x
    
    mkEqSwitch f cmp def [] done y = case def of
      Nothing -> Left False
      Just def' -> case mkEq f def' y of
        Left True -> if null done
                     then Left True
                     else Right $ app and' done
        Left False -> Left False
        Right e -> Right $ app and' (done++[e])
    mkEqSwitch f cmp def ((cmp',tree):rest) done y = case mkEq f tree y of
      Left True -> case mkEqSwitch f cmp def rest done y of
        Left True -> Left True
        Left False -> Right $ cmp .==. cmp'
        Right e -> Right $ (not' $ cmp .==. cmp') .=>. e
      Left False -> mkEqSwitch f cmp def rest ((not' (cmp .==. cmp')):done) y
      Right e1 -> case mkEqSwitch f cmp def rest done y of
        Left True -> Right $ (cmp .==. cmp') .=>. e1
        Left False -> Right $ (cmp .==. cmp') .&&. e1
        Right e2 -> Right $ ite (cmp .==. cmp') e1 e2

accumDecisionTree :: SMTType b => (SMTExpr Bool -> a -> (SMTExpr b,c)) -> DecisionTree a -> (SMTExpr b,[c])
accumDecisionTree f = accum' f []
  where
    accum' :: SMTType b => (SMTExpr Bool -> a -> (SMTExpr b,c)) -> [SMTExpr Bool] -> DecisionTree a -> (SMTExpr b,[c])
    accum' f cur (GroundNode x) = let (expr,x') = f (app and' cur) x
                                  in (expr,[x'])
    accum' f cur (BoolNode cond x y) = let (ex,x') = accum' f (cond:cur) x
                                           (ey,y') = accum' f ((not' cond):cur) y
                                       in (ite cond ex ey,x'++y')
    accum' f cur (SwitchNode cmp def cases) = mkCompare f cur cmp def [] cases
    
    mkCompare f cur cmp (Just def) done [] = accum' f (done++cur) def
    mkCompare f cur cmp Nothing done [(cmp',tree)] = accum' f ((cmp .==. cmp'):cur) tree
    mkCompare f cur cmp def done ((cmp',tree):rest) = let (e,acc) = accum' f ((cmp .==. cmp'):cur) tree
                                                          (e',acc') = mkCompare f cur cmp def ((not' $ cmp .==. cmp'):done) rest
                                                      in (ite (cmp .==. cmp') e e',acc++acc')