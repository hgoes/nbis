module Simplifier where

import Data.Typeable

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Functions

isFalse :: SMTExpr Bool -> Bool
isFalse (Const False _) = True
isFalse _ = False

isTrue :: SMTExpr Bool -> Bool
isTrue (Const True _) = True
isTrue _ = False

simplifier :: SMTExpr Bool -> SMTExpr Bool
simplifier (App f xs)
  = case cast f of
  Just And -> case cast xs of
    Just ys -> case simplifyAnd ys of
      Nothing -> Const False ()
      Just [] -> Const True ()
      Just [x] -> x
      Just xs -> App And xs
  Just Or -> case cast xs of
    Just ys -> case simplifyOr ys of
      Nothing -> Const True ()
      Just [] -> Const False ()
      Just [x] -> x
      Just xs -> App Or xs
  Just _ -> App f xs
  Nothing -> case cast f of
    Just Not -> case cast xs of
      Just x -> let x' = simplifier x
                in if isFalse x'
                   then Const True ()
                   else (if isTrue x'
                         then Const False ()
                         else App Not x')
    _ -> App f xs
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
    simplifyOr [] = Just []
    simplifyOr (x:xs) = let x' = simplifier x
                        in if isTrue x'
                           then Nothing
                           else (if isFalse x'
                                 then simplifyOr xs
                                 else (case simplifyOr xs of
                                          Nothing -> Nothing
                                          Just xs' -> Just (x':xs')))
simplifier x = x