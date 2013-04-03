{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses #-}
module MemoryModel.Snow where

import MemoryModel
import DecisionTree

import Language.SMTLib2
--import qualified Data.Graph.Inductive as Gr
import Data.Map as Map hiding (foldl)
import Data.Foldable
import Prelude hiding (foldl1,foldl,mapM_)
import Data.Bits
import Control.Monad.Trans

type BVPtr = BV64
type BVByte = BitVector BVUntyped

data Object 
  = NormalObject (SMTExpr (SMTArray (SMTExpr BVPtr) BVByte))
  | NullObject

data SnowMemory ptr = SnowMemory { snowLocs :: Map Int (MemoryProgram ptr,Map ptr (DecisionTree Object))
                                 , snowGlobals :: Map ptr Object
                                 }

instance (Ord ptr,Show ptr) => MemoryModel (SnowMemory ptr) ptr where
  memNew _ _ = return $ SnowMemory Map.empty Map.empty
  addGlobal mem ptr cont = do
    glb <- mkGlobal cont
    return $ mem { snowGlobals = Map.insert ptr glb (snowGlobals mem)
                 }
  addProgram mem loc prog 
    = do
      liftIO $ do
        putStrLn $ "New program for "++show loc++":"
        mapM_ print prog
      objs <- initialObjects prog
      return $ mem { snowLocs = Map.insert loc (prog,objs) (snowLocs mem) }
  connectPrograms mem cond from to ptrs = do
    liftIO $ do
      putStrLn $ "Connect location "++show from++" with "++show to
      putStrLn $ show ptrs
    let (_,env_from) = (snowLocs mem)!from
        (prog_to,env_to) = (snowLocs mem)!to
        new_env1 = foldl (\mp (ptr_from,ptr_to) 
                          -> Map.insert ptr_to (env_from!ptr_from) mp
                         ) (Map.union env_to (fmap decision (snowGlobals mem))) ptrs
        new_env2 = foldl (\mp ptr
                           -> case Map.lookup ptr env_from of
                            Nothing -> mp
                            Just glob -> Map.insert ptr glob mp
                         ) new_env1 (Map.keys (snowGlobals mem))
    new_env' <- updateLocation cond new_env2 prog_to
    return $ mem { snowLocs = Map.insert to (prog_to,new_env') (snowLocs mem) }

initialObjects :: Ord ptr => [MemoryInstruction ptr] -> SMT (Map ptr (DecisionTree Object))
initialObjects = foldlM (\mp instr -> case instr of
                            MINull _ p -> return $ Map.insert p (decision NullObject) mp
                            MIAlloc _ _ p -> do
                              v <- varNamedAnn "allocation" ((),8)
                              return $ Map.insert p (decision $ NormalObject v) mp
                            _ -> return mp
                        ) Map.empty

updateLocation :: Ord ptr => SMTExpr Bool 
                  -> Map ptr (DecisionTree Object) 
                  -> [MemoryInstruction ptr] 
                  -> SMT (Map ptr (DecisionTree Object))
updateLocation cond 
  = foldlM (\mp instr -> case instr of
               MILoad ptr res -> case Map.lookup ptr mp of
                 Just dt -> do
                   let sz = extractAnnotation res
                       rsz = sz `div` 8
                       obj' = fst $ accumDecisionTree 
                              (\_ obj -> case obj of
                                  NormalObject obj' 
                                    -> let selects = fmap (\i -> select obj' (fromInteger i)) [0..rsz-1]
                                       in (foldl1 bvconcat selects,())
                              ) dt
                   assert $ cond .=>. (res .==. obj')
                   return mp
               MIStore val ptr -> case Map.lookup ptr mp of
                 Just dt -> do
                   obj <- mkObject val
                   let ndt = boolDecision cond (decision obj) dt
                   return $ Map.insert ptr ndt mp
               _ -> return mp
           )

mkObject :: SMTExpr (BitVector BVUntyped) -> SMT Object
mkObject bv = do
  let sz = extractAnnotation bv
      rsz = sz `div` 8
      null = constArray (constantAnn (BitVector 0) 8) ()
      arr = foldl (\arr' i -> store arr' (fromInteger i)
                              (bvextract' ((rsz - i - 1)*8) 8 bv)
                  ) null [0..rsz-1]
  narr <- defConstNamed "storeRes" arr
  return $ NormalObject narr

mkGlobal :: MemContent -> SMT Object
mkGlobal (MemCell w v) = do
  let null = constArray (constantAnn (BitVector 0) 8) ()
      rw = w `div` 8
      arr = foldl (\arr' i -> store arr' (fromInteger i)
                              (constantAnn (BitVector $ v `shiftR` (fromInteger $ i*8)) 8)
                  ) null [0..rw-1]
  narr <- defConstNamed "global" arr
  return $ NormalObject narr