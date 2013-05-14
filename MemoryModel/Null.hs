{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses #-}
module MemoryModel.Null where

import MemoryModel

data NullMemory = NullMemory

instance MemoryModel NullMemory mloc ptr where
  memNew _ _ _ _ = return NullMemory
  addProgram _ _ _ _ = return NullMemory
  connectLocation _ _ _ _ _ = return NullMemory