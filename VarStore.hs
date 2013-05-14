module VarStore where

import TypeDesc
import Value

import Language.SMTLib2

import Data.Map (Map)
import qualified Data.Map as Map

data VarStore i
  = VarStore { varStoreNext :: i
             , varStoreVars :: Map i VarState
             }

data VarState = Unmerged String TypeDesc [(Val,SMTExpr Bool)]
              | Merged Val

newStore :: (Integral i) => VarStore i
newStore = VarStore { varStoreNext = 0
                    , varStoreVars = Map.empty
                    }

newEntry :: (Enum i,Ord i) => String -> TypeDesc -> VarStore i -> (i,VarStore i)
newEntry name tp store = (varStoreNext store,store { varStoreNext = succ (varStoreNext store)
                                                   , varStoreVars = Map.insert (varStoreNext store) (Unmerged name tp []) (varStoreVars store)
                                                   })

readVar :: (Ord i) => i -> VarStore i -> SMT (Val,VarStore i)
readVar x store = case Map.lookup x (varStoreVars store) of
  Just (Merged val) -> return (val,store)
  Just (Unmerged name tp joins) -> case tp of
    IntegerType 1 -> do
      v <- varNamed name
      let val = ConditionValue v 1
      mapM_ (\(val',cond) -> assert $ cond .=>. (valEq val val')) joins
      return (val,
              store { varStoreVars = Map.insert x (Merged val) (varStoreVars store)
                    })
    _ -> do
      v <- varNamedAnn name (fromIntegral $ bitWidth tp)
      let val = DirectValue v
      mapM_ (\(val',cond) -> assert $ cond .=>. (valEq val val')) joins
      return (val,
              store { varStoreVars = Map.insert x (Merged val) (varStoreVars store)
                    })

addJoin :: (Ord i) => i -> Val -> SMTExpr Bool -> VarStore i -> SMT (VarStore i)
addJoin x val cond store = case Map.lookup x (varStoreVars store) of
  Just (Unmerged name tp joins)
    -> return (store { varStoreVars = Map.insert x 
                                      (Unmerged name tp ((val,cond):joins))
                                      (varStoreVars store) })
  Just (Merged val') -> do
    assert $ cond .=>. (valEq val val')
    return store