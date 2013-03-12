{-# LANGUAGE TypeFamilies,DeriveDataTypeable #-}
module MemoryModel.CBMCLike where

import DecisionTree
import Language.SMTLib2
import LLVM.Core (TypeDesc)
import Data.Map as Map hiding (foldl)
import Data.Typeable
import qualified Data.Graph.Inductive as Gr
import MemoryModel
import Data.Bits

type BVPtr = BV64
type BVByte = BitVector BVUntyped

data PointerData = PointerData { pointerObject :: DecisionTree (Integer,Maybe (SMTExpr BVPtr))
                               }

data Memory gr = Memory { memPointers :: gr PointerData PointerDep
                        , memPtrEqs :: Map Gr.Node [(Gr.Node,SMTExpr Bool)]
                        , memLoads :: Map Gr.Node [(Integer,SMTExpr (BitVector BVUntyped))]
                        , memStores :: Map Gr.Node [(Integer,SMTExpr (BitVector BVUntyped),Integer)]
                        , memObjects :: Objects
                        , memLastObject :: Integer
                        , memLastPointer :: Gr.Node
                        }

data Object
  = ConcreteObject (SMTExpr (SMTArray (SMTExpr BVPtr) BVByte))
  | PointerObject (DecisionTree Integer)
  | NullObject

type Objects = Map Integer Object

data PointerDep
  = Deref
  | Index (SMTExpr BVPtr)
  | CondEq (SMTExpr Bool)

makeLoad :: PointerData -> Integer -> Objects -> SMTExpr (BitVector BVUntyped)
makeLoad (PointerData obj) sz objs
  = fst $ accumDecisionTree 
    (\_ (ptr,Nothing) -> case Map.lookup ptr objs of
        Just (ConcreteObject arr) -> (foldl1 bvconcat (fmap (\i -> select arr (fromInteger i)) [0..sz-1]),())
        Just NullObject -> (constantAnn (BitVector 0) (sz*8),())
    ) obj

makeEq :: PointerData -> PointerData -> SMTExpr Bool
makeEq (PointerData obj1) (PointerData obj2) 
  = decisionTreeEq (\x y -> Left (x==y)) obj1 obj2

makeStore :: PointerData -> SMTExpr (BitVector BVUntyped) -> Integer -> Objects 
             -> (SMTExpr (SMTArray (SMTExpr BVPtr) BVByte))
makeStore (PointerData obj) bv sz objs
  = fst $ accumDecisionTree 
    (\cond' (ptr,Nothing) 
     -> case Map.lookup ptr objs of
       Just (ConcreteObject arr) 
         -> (foldl (\arr' idx -> store arr' (fromInteger idx) (bvextract' (idx*8) 8 bv)) arr [0..(sz-1)],())
       Just NullObject -> (constArray (constantAnn (BitVector 0) 8) (),())
    ) obj

addIncomingPtr :: Gr.DynGraph gr => Memory gr -> SMTExpr Bool -> Gr.Node -> Gr.Node -> SMT ()
addIncomingPtr mem cond inc cur = do
  let (cur_in,_,cur_ptr,cur_out) = Gr.context (memPointers mem) cur
      Just inc_ptr = Gr.lab (memPointers mem) inc
  case Map.lookup cur (memLoads mem) of
    Nothing -> return ()
    Just loads -> mapM_ (\(sz,trg) 
                         -> assert $ cond .=>. (trg .==. makeLoad inc_ptr sz (memObjects mem))
                        ) loads
  case Map.lookup cur (memPtrEqs mem) of
    Nothing -> return ()
    Just eqs -> mapM_ (\(oth,res) -> do
                          let Just oth_ptr = Gr.lab (memPointers mem) oth
                          assert $ cond .=>. (res .==. makeEq inc_ptr oth_ptr)
                      ) eqs
  case Map.lookup cur (memStores mem) of
    Nothing -> return ()
    Just stores -> mapM_ (\(sz,bv,ptr) -> do
                             let Just (ConcreteObject trg) = Map.lookup ptr (memObjects mem)
                             assert $ cond .=>. (trg .==. makeStore inc_ptr bv sz (memObjects mem))
                         ) stores
  mapM_ (\(dep,oth) -> case dep of
            CondEq cond' -> addIncomingPtr mem (cond .&&. cond') inc oth
        ) cur_out
  
instance Gr.DynGraph gr => MemoryModel (Memory gr) where
  type LocalMem (Memory gr) = ()
  type Pointer (Memory gr) = Gr.Node
  memNew _ = return (Memory { memPointers = Gr.insNode (0,PointerData (decision (0,Nothing))) Gr.empty 
                            , memPtrEqs = Map.empty
                            , memLoads = Map.empty
                            , memStores = Map.empty
                            , memObjects = Map.singleton 0 NullObject
                            , memLastObject = 1
                            , memLastPointer = 1 })
  memInit _ = return ()
  memAlloc tp _ cont mem () = do
    arr <- case cont of
      Nothing -> varNamedAnn "allocation" ((),8)
      Just (MemCell w v) -> do
        c <- defConstNamed "allocation_content" $
             foldl (\arr (i,bv) -> store arr (fromInteger i) bv) 
             (constArray (constantAnn (BitVector 0) 8) ())
             [ (i,constantAnn (BitVector ((v `shiftR` (fromInteger $ (w-i-1)*8)) `mod` 256)) 8)
             | i <- [0..w-1]]
        return c
    let ptr = memLastPointer mem
        obj = memLastObject mem
        objs = Map.insert obj (ConcreteObject arr) (memObjects mem)
        gr = Gr.insNode (ptr,PointerData (decision (obj,Nothing)))
             (memPointers mem)
    return (ptr,mem { memPointers = gr
                    , memObjects = objs
                    , memLastObject = obj + 1
                    , memLastPointer = ptr + 1
                    },())
  memLoad tp ptr cond mem () = do
    let Just ptr_dat = Gr.lab (memPointers mem) ptr
        sz = typeWidth tp
    v <- varNamedAnn "loaded" (sz*8)
    assert $ cond .=>. (v .==. makeLoad ptr_dat sz (memObjects mem))
    return (v,[],mem { memLoads = Map.insertWith (++) ptr [(sz,v)] (memLoads mem) })
  memStore tp ptr bv cond mem () = do
    let Just ptr_dat = Gr.lab (memPointers mem) ptr
        sz = typeWidth tp
    arr <- varNamedAnn "stored" ((),8)
    assert $ cond .=>. (arr .==. makeStore ptr_dat bv sz (memObjects mem))
    return (mem { memObjects = Map.insert (memLastObject mem) (ConcreteObject arr) (memObjects mem)
                , memStores = Map.insertWith (++) ptr [(sz,bv,memLastObject mem)] (memStores mem)
                , memLastObject = (memLastObject mem) + 1
                },(),[])
  memEq mem _ () () = return ((),mem)
  memPtrExtend mem ptr_from ptr_to cond = do
    addIncomingPtr mem cond ptr_from ptr_to
    return $ mem { memPointers = Gr.insEdge (ptr_from,ptr_to,CondEq cond) (memPointers mem) }
  memCast mem _ ptr = (ptr,mem)
  memPtrNew mem = let ptr = memLastPointer mem
                  in (ptr,mem { memLastPointer = ptr + 1 
                              , memPointers = Gr.insNode (ptr,PointerData (decision (-1,Nothing))) (memPointers mem) 
                              })
  memPtrNull mem = (0,mem)
  memDebug mem = show (Gr.nodes (memPointers mem))
