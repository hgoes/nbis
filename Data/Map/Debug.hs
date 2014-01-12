module Data.Map.Debug where

import Data.Map (Map)
import qualified Data.Map as Map

(!) :: (Show k,Ord k) => Map k a -> k -> a
(!) mp key = case Map.lookup key mp of
  Nothing -> error $ "Key "++show key++" not found in map "++show (Map.keys mp)
  Just r -> r
