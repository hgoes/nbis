{-# LANGUAGE ExistentialQuantification #-}
module DecisionTree 
       (DecisionTree()
       ,decision
       ,boolDecision
       ,caseDecision
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
  | CaseNode (Maybe (DecisionTree a)) [(SMTExpr Bool,DecisionTree a)]
  | GroundNode a

instance Functor DecisionTree where
  fmap f (GroundNode x) = GroundNode (f x)
  fmap f (BoolNode c x y) = BoolNode c (fmap f x) (fmap f y)
  fmap f (CaseNode def cases) = CaseNode (fmap (fmap f) def) (fmap (\(cmp,tree) -> (cmp,fmap f tree)) cases)

instance Eq a => Eq (DecisionTree a) where
  (==) (GroundNode x) (GroundNode y) = x==y
  (==) (BoolNode c1 x1 y1) (BoolNode c2 x2 y2) = c1==c2 && x1==x2 && y1==y2
  (==) (CaseNode def1 cases1) (CaseNode def2 cases2) = def1==def2 && cases1==cases2
  (==) _ _ = False

instance Foldable DecisionTree where
  foldMap f (GroundNode x) = f x
  foldMap f (BoolNode _ x y) = (foldMap f x) `mappend` (foldMap f y)
  foldMap f (CaseNode def cases) = (case def of
                                       Nothing -> mempty
                                       Just def' -> foldMap f def') `mappend`
                                   (foldMap (foldMap f . snd) cases)

instance Traversable DecisionTree where
  traverse f (GroundNode x) = GroundNode <$> f x
  traverse f (BoolNode c ifT ifF) = BoolNode c <$> traverse f ifT <*> traverse f ifF
  traverse f (CaseNode Nothing cases)
    = CaseNode Nothing <$> traverse (\(val,dt) -> fmap (\ndt -> (val,ndt)) (traverse f dt)) cases
  traverse f (CaseNode (Just def) cases)
    = CaseNode <$> (Just <$> traverse f def) <*> traverse (\(val,dt) -> fmap (\ndt -> (val,ndt)) (traverse f dt)) cases

boolDecision :: SMTExpr Bool -> DecisionTree a -> DecisionTree a -> DecisionTree a
boolDecision = BoolNode

switchDecision :: SMTType b => SMTExpr b -> (Maybe (DecisionTree a)) -> [(SMTExpr b,DecisionTree a)] -> DecisionTree a
switchDecision cmp def cases
  = CaseNode def (fmap (\(cmp',dt) -> (cmp .==. cmp',dt)) cases)

caseDecision :: Maybe (DecisionTree a) -> [(SMTExpr Bool,DecisionTree a)] -> DecisionTree a
caseDecision = CaseNode

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
    mkEq f (CaseNode def cases) y = mkEqCase f def cases [] y
    mkEq f x y = mkEq f y x
    
    mkEqCase f def [] done y = case def of
      Nothing -> Left False
      Just def' -> case mkEq f def' y of
        Left True -> if null done
                     then Left True
                     else Right $ app and' done
        Left False -> Left False
        Right e -> Right $ app and' (done++[e])
    mkEqCase f def ((cmp,tree):rest) done y = case mkEq f tree y of
      Left True -> case mkEqCase f def rest done y of
        Left True -> Left True
        Left False -> Right cmp
        Right e -> Right $ (not' cmp) .=>. e
      Left False -> mkEqCase f def rest ((not' cmp):done) y
      Right e1 -> case mkEqCase f def rest done y of
        Left True -> Right $ cmp .=>. e1
        Left False -> Right $ cmp .&&. e1
        Right e2 -> Right $ ite cmp e1 e2

accumDecisionTree :: SMTType b => (SMTExpr Bool -> a -> (SMTExpr b,c)) -> DecisionTree a -> (SMTExpr b,[c])
accumDecisionTree f = accum' f []
  where
    accum' :: SMTType b => (SMTExpr Bool -> a -> (SMTExpr b,c)) -> [SMTExpr Bool] -> DecisionTree a -> (SMTExpr b,[c])
    accum' f cur (GroundNode x) = let (expr,x') = f (app and' cur) x
                                  in (expr,[x'])
    accum' f cur (BoolNode cond x y) = let (ex,x') = accum' f (cond:cur) x
                                           (ey,y') = accum' f ((not' cond):cur) y
                                       in (ite cond ex ey,x'++y')
    accum' f cur (CaseNode def cases) = mkCompare f cur def [] cases
    
    mkCompare f cur (Just def) done [] = accum' f (done++cur) def
    mkCompare f cur Nothing done [(cmp,tree)] = accum' f (cmp:cur) tree
    mkCompare f cur def done ((cmp,tree):rest) = let (e,acc) = accum' f (cmp:cur) tree
                                                     (e',acc') = mkCompare f cur def ((not' cmp):done) rest
                                                 in (ite cmp e e',acc++acc')