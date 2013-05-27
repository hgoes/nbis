module VarStore where

import Language.SMTLib2

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (foldlM)

data VarStore m i a v
  = VarStore { varStoreNext :: i
             , varStoreVars :: Map i (VarState i a v)
             , varStoreCombine :: SMTExpr Bool -> v -> v -> m ()
             , varStoreAlloc :: a -> m v
             }

data VarState i a v = Unmerged a [(Either i v,SMTExpr Bool)]
                    | Merged v

newStore :: (Integral i) => (SMTExpr Bool -> v -> v -> m ()) -> (a -> m v) -> VarStore m i a v
newStore f g = VarStore { varStoreNext = 0
                        , varStoreVars = Map.empty
                        , varStoreCombine = f
                        , varStoreAlloc = g
                        }

newEntry :: (Enum i,Ord i) => a -> VarStore m i a v -> (i,VarStore m i a v)
newEntry ann store = (varStoreNext store,store { varStoreNext = succ (varStoreNext store)
                                               , varStoreVars = Map.insert (varStoreNext store) (Unmerged ann []) (varStoreVars store)
                                               })

readVar :: (Ord i,Monad m) => i -> VarStore m i a v -> m (v,VarStore m i a v)
readVar x store = case Map.lookup x (varStoreVars store) of
  Just (Merged val) -> return (val,store)
  Just (Unmerged ann joins) -> do
    val <- varStoreAlloc store ann
    let store1 = store { varStoreVars = Map.insert x (Merged val) (varStoreVars store) }
    store2 <- foldlM (\cstore (val',cond) -> do
                         (rval,nstore) <- case val' of
                           Left y -> readVar y cstore
                           Right y -> return (y,cstore)
                         varStoreCombine nstore cond val rval
                         return nstore
                     ) store1 joins
    return (val,store2)

addJoin :: (Ord i,Monad m) => i -> Either i v -> SMTExpr Bool -> VarStore m i a v -> m (VarStore m i a v)
addJoin x val cond store = case Map.lookup x (varStoreVars store) of
  Just (Unmerged ann joins)
    -> return (store { varStoreVars = Map.insert x 
                                      (Unmerged ann ((val,cond):joins))
                                      (varStoreVars store) })
  Just (Merged val') -> do
    (rval,nstore) <- case val of
      Right x -> return (x,store)
      Left x -> readVar x store
    varStoreCombine nstore cond rval val'
    return nstore
