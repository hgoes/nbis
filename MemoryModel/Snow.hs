{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses,GADTs,RankNTypes #-}
module MemoryModel.Snow where

import MemoryModel
import DecisionTree
import TypeDesc

import Language.SMTLib2
--import qualified Data.Graph.Inductive as Gr
import Data.Map as Map hiding (foldl)
import Data.Foldable
import Prelude hiding (foldl1,foldl,mapM_)
import Data.Bits
import Control.Monad.Trans

import MemoryModel.Snow.Object

type BVPtr = BV64
type BVByte = BitVector BVUntyped

data SnowMemory ptr = SnowMemory { snowStructs :: Map String [TypeDesc]
                                 , snowLocs :: Map Int (MemoryProgram ptr,
                                                        Map ptr (DecisionTree
                                                                 (Integer,TypeDesc,
                                                                  ObjAccessor ptr)))
                                 , snowObjects :: Map Integer (Object ptr)
                                 , snowGlobals :: Map ptr (Integer,TypeDesc)
                                 , snowNextObject :: Integer
                                 }

instance (Ord ptr,Show ptr) => MemoryModel (SnowMemory ptr) ptr where
  memNew _ _ structs = return $ SnowMemory structs Map.empty Map.empty Map.empty 0
  addGlobal mem ptr tp cont = do
    glb <- mkGlobal cont
    return $ mem { snowGlobals = Map.insert ptr (snowNextObject mem,tp) (snowGlobals mem)
                 , snowObjects = Map.insert (snowNextObject mem) glb (snowObjects mem)
                 , snowNextObject = succ (snowNextObject mem)
                 }
  addProgram mem loc prog
    = do
      liftIO $ do
        putStrLn $ "New program for "++show loc++":"
        mapM_ print prog
      (ptrs,objs,next) <- initialObjects (snowStructs mem) (snowNextObject mem) prog
      return $ mem { snowLocs = Map.insert loc (prog,ptrs) (snowLocs mem)
                   , snowObjects = Map.union objs (snowObjects mem)
                   , snowNextObject = next
                   }
  connectPrograms mem cond from to ptrs = do
    liftIO $ do
      putStrLn $ "Connect location "++show from++" with "++show to
      putStrLn $ show ptrs
    let (_,env_from) = (snowLocs mem)!from
        (prog_to,env_to) = (snowLocs mem)!to
        new_env1 = foldl (\mp (ptr_to,ptr_from)
                          -> Map.insert ptr_to (env_from!ptr_from) mp
                         ) (Map.union env_to (fmap (\(obj_p,tp) -> decision (obj_p,tp,ObjAccessor id))
                                              (snowGlobals mem))) ptrs
        new_env2 = foldl (\mp ptr
                           -> case Map.lookup ptr env_from of
                            Nothing -> mp
                            Just glob -> Map.insert ptr glob mp
                         ) new_env1 (Map.keys (snowGlobals mem))
    (new_env',nobjs,next') <- updateLocation (snowStructs mem) cond new_env2 (snowObjects mem) (snowNextObject mem) prog_to
    return $ mem { snowLocs = Map.insert to (prog_to,new_env') (snowLocs mem)
                 , snowObjects = nobjs
                 , snowNextObject = next'
                 }

initialObjects :: Ord ptr => Map String [TypeDesc]
                  -> Integer
                  -> [MemoryInstruction ptr]
                  -> SMT (Map ptr (DecisionTree (Integer,TypeDesc,ObjAccessor ptr)),
                          Map Integer (Object ptr),
                          Integer)
initialObjects structs n
  = foldlM (\(ptrs,objs,next) instr -> case instr of
               MINull tp p -> return (Map.insert p (decision (next,tp,ObjAccessor id)) ptrs,
                                      Map.insert next (Bounded NullPointer) objs,
                                      succ next)
               MIAlloc tp sz p -> do
                 obj <- allocaObject structs tp sz
                 return (Map.insert p (decision (next,tp,ObjAccessor id)) ptrs,
                         Map.insert next obj objs,
                         succ next)
               _ -> return (ptrs,objs,next)
           ) (Map.empty,Map.empty,n)

updateLocation :: (Ord ptr,Show ptr) => Map String [TypeDesc] 
                  -> SMTExpr Bool 
                  -> Map ptr (DecisionTree (Integer,TypeDesc,ObjAccessor ptr))
                  -> Map Integer (Object ptr)
                  -> Integer
                  -> [MemoryInstruction ptr] 
                  -> SMT (Map ptr (DecisionTree (Integer,TypeDesc,ObjAccessor ptr)),
                          Map Integer (Object ptr),
                          Integer)
updateLocation structs cond ptrs objs next
  = foldlM (\(ptrs,objs,next) instr -> case instr of
               -- Allocations don't have to be updated
               MIAlloc _ _ _ -> return (ptrs,objs,next)
               -- Neither do null pointers
               MINull _ _ -> return (ptrs,objs,next)
               MILoad ptr res -> case Map.lookup ptr ptrs of
                 Just dt -> do
                   let sz = extractAnnotation res
                       obj' = fst $ accumDecisionTree
                              (\_ (obj_p,tp,ObjAccessor access)
                               -> case Map.lookup obj_p objs of
                                 Just obj -> let (_,res,errs) = access (\obj' -> let (res,errs) = loadObject sz obj'
                                                                                 in (obj',res,errs)
                                                                       ) obj
                                             in (res,errs)
                              ) dt
                   assert $ cond .=>. (res .==. obj')
                   return (ptrs,objs,next)
               MIStore val ptr -> case Map.lookup ptr ptrs of
                 Just dt -> do
                   let (nnext,nobjs,ups)
                         = foldl (\(cnext,cobjs,cups) (obj_p,_,ObjAccessor idx)
                                  -> case Map.lookup obj_p objs of
                                    Just obj -> let (nobj,_,_) = idx (\obj' -> let (nobj',errs') = storeObject val obj
                                                                               in (nobj',(),errs')
                                                                     ) obj
                                                in (succ cnext,
                                                    Map.insert cnext nobj cobjs,
                                                    Map.insert obj_p cnext cups)
                                 ) (next,objs,Map.empty) dt
                       nptrs = fmap (fmap (\(obj_p,tp,access) -> case Map.lookup obj_p ups of
                                              Nothing -> (obj_p,tp,access)
                                              Just nobj_p -> (nobj_p,tp,access)
                                          )
                                    ) ptrs
                   return (nptrs,nobjs,nnext)
               MIStorePtr ptr trg -> case Map.lookup trg ptrs of
                 Just dt -> do
                   let (nnext,nobjs,ups)
                         = foldl (\(cnext,cobjs,cups) (obj_p,_,ObjAccessor idx)
                                  -> case Map.lookup obj_p objs of
                                    Just obj -> let (nobj,_,_) = idx (\obj' -> let (nobj',errs') = storePtr ptr obj
                                                                               in (nobj',(),errs')
                                                                     ) obj
                                                in (succ cnext,
                                                    Map.insert cnext nobj cobjs,
                                                    Map.insert obj_p cnext cups)
                                 ) (next,objs,Map.empty) dt
                       nptrs = fmap (fmap (\(obj_p,tp,access) -> case Map.lookup obj_p ups of
                                              Nothing -> (obj_p,tp,access)
                                              Just nobj_p -> (nobj_p,tp,access)
                                          )
                                    ) ptrs
                   return (nptrs,nobjs,nnext)
               MICast from to ptr_from ptr_to -> case Map.lookup ptr_from ptrs of
                 Just dt -> do
                   let ndt = fmap (\(obj_p,_,idx) -> (obj_p,to,idx)) dt
                   return (Map.insert ptr_to ndt ptrs,objs,next)
               MIIndex idx ptr_from ptr_to -> case Map.lookup ptr_from ptrs of
                 Just dt -> do
                   let ndt = fmap (\(obj_p,tp,access) -> (obj_p,indexType structs tp idx,
                                                          indexObject structs tp idx access)) dt
                   return (Map.insert ptr_to ndt ptrs,objs,next)
               --MISelect opts ptr -> 
               _ -> error $ "Memory instruction "++show instr++" not implemented in Snow memory model."
           ) (ptrs,objs,next)

{-
mkObject :: SMTExpr (BitVector BVUntyped) -> SMT Object
mkObject bv = do
  let sz = extractAnnotation bv
      rsz = sz `div` 8
      null = constArray (constantAnn (BitVector 0) 8) ()
      arr = foldl (\arr' i -> store arr' (fromInteger i)
                              (bvextract' ((rsz - i - 1)*8) 8 bv)
                  ) null [0..rsz-1]
  narr <- defConstNamed "storeRes" arr
  return $ NormalObject narr -}

mkGlobal :: MemContent -> SMT (Object ptr)
mkGlobal cont = do
  glob <- mkGlobal' cont
  return $ Bounded $ StaticArrayObject [glob]
  where
    mkGlobal' (MemCell w v) = do
      obj <- defConstNamed "global" (constantAnn (BitVector v) w)
      return $ WordObject obj
    mkGlobal' (MemArray els) = do
      els' <- mapM mkGlobal' els
      return $ StaticArrayObject els'
  