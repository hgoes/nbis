module Activation where

import Language.SMTLib2
import LLVM.FFI.Instruction

import Data.Map as Map
import Foreign.Ptr

data ActivationVar = ActivationVar { activationVar :: SMTExpr Bool
                                   , activationProxy :: Maybe (SMTExpr Bool)
                                   }

newExtensibleActivation :: String -> SMT ActivationVar
newExtensibleActivation name = do
  act <- varNamed name
  return $ ActivationVar act (Just act)

newStaticActivation :: String -> SMTExpr Bool -> SMT ActivationVar
newStaticActivation name cond = do
  act <- defConstNamed name cond
  return $ ActivationVar act Nothing

disableActivationExtension :: ActivationVar -> SMT ()
disableActivationExtension var = case activationProxy var of
  Nothing -> return ()
  Just prx -> assert $ not' prx