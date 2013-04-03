{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses #-}
module MemoryModel.Null where

import MemoryModel

data NullMemory = NullMemory

instance MemoryModel NullMemory ptr where
  memNew _ _ = return NullMemory
  addGlobal _ _ _ = return NullMemory
  addProgram _ _ _ = return NullMemory
  connectPrograms _ _ _ _ _ = return NullMemory