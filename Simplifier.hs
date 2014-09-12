module Simplifier where

import Data.List (nub)

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators

isFalse :: SMTExpr Bool -> Bool
isFalse (Const False _) = True
isFalse _ = False

isTrue :: SMTExpr Bool -> Bool
isTrue (Const True _) = True
isTrue _ = False

simplifier :: SMTExpr Bool -> SMTExpr Bool
simplifier (App (SMTLogic And) xs) = case simplifyAnd xs of
  Nothing -> Const False ()
  Just [] -> Const True ()
  Just [x] -> x
  Just xs -> App (SMTLogic And) xs
  where
    simplifyAnd [] = Just []
    simplifyAnd (x:xs) = let x' = simplifier x
                         in if isTrue x'
                            then simplifyAnd xs
                            else (if isFalse x'
                                  then Nothing
                                  else (case simplifyAnd xs of
                                           Nothing -> Nothing
                                           Just xs' -> Just (x':xs')))

simplifier (App (SMTLogic Or) xs) = case simplifyOr xs of
  Nothing -> Const True ()
  Just [] -> Const False ()
  Just [x] -> x
  Just xs' -> App (SMTLogic Or) (nub xs')
  where
    simplifyOr [] = Just []
    simplifyOr (x:xs) = let x' = simplifier x
                        in if isTrue x'
                           then Nothing
                           else (if isFalse x'
                                 then simplifyOr xs
                                 else (case simplifyOr xs of
                                          Nothing -> Nothing
                                          Just xs' -> Just (x':xs')))

simplifier (App SMTNot x)
  = let x' = simplifier x
    in if isFalse x'
       then Const True ()
       else (if isTrue x'
             then Const False ()
             else App SMTNot x')
simplifier (App f xs) = App f xs
simplifier x = x
