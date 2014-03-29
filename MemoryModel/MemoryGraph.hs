{-# LANGUAGE MultiParamTypeClasses #-}
module MemoryModel.MemoryGraph where

import MemoryModel
import TypeDesc
import Value

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

data MemoryGraph mloc ptr
  = MemGraph { nullsByPtr :: Map ptr TypeDesc
             , comparesByLHS :: Map ptr (ptr,BoolVal)
             , comparesByRHS :: Map ptr (ptr,BoolVal)
             , ptrPhisByTrg :: Map ptr (Map ptr BoolVal)
             , ptrPhisBySrc :: Map ptr (Map ptr BoolVal)
             , ptrIdxBySrc :: Map ptr (Map ptr (TypeDesc,TypeDesc,[Val]))
             , ptrIdxByTrg :: Map ptr (ptr,TypeDesc,TypeDesc,[Val])
             , ptrCastsBySrc :: Map ptr (Map ptr (TypeDesc,TypeDesc))
             , ptrCastsByTrg :: Map ptr (ptr,TypeDesc,TypeDesc)
             , allocsBySrcLoc :: Map mloc (Map mloc (TypeDesc,DynNum,ptr,BoolVal))
             , allocsByTrgLoc :: Map mloc (mloc,TypeDesc,DynNum,ptr,BoolVal)
             , allocsByPtr :: Map ptr (mloc,TypeDesc,DynNum,mloc,BoolVal)
             , loadsBySrcLoc :: Map mloc (ptr,Val,BoolVal)
             , loadsBySrcPtr :: Map ptr (Map mloc (Val,BoolVal))
             , ptrLoadsBySrcLoc :: Map mloc [(ptr,ptr,BoolVal)]
             , ptrLoadsBySrcPtr :: Map ptr (Map mloc (ptr,BoolVal))
             , ptrLoadsByTrgPtr :: Map ptr (mloc,ptr,BoolVal)
             , storesBySrcLoc :: Map mloc (Map mloc (Val,ptr,BoolVal))
             , storesByTrgLoc :: Map mloc (mloc,Val,ptr,BoolVal)
             , storesByTrgPtr :: Map ptr (Map (mloc,mloc) (Val,BoolVal))
             , ptrStoresBySrcLoc :: Map mloc (Map mloc (ptr,ptr,BoolVal))
             , ptrStoresByTrgLoc :: Map mloc (mloc,ptr,ptr,BoolVal)
             , ptrStoresByTrgPtr :: Map ptr (Map (mloc,mloc) (ptr,BoolVal))
             , ptrStoresBySrcPtr :: Map ptr (Map (mloc,mloc) (ptr,BoolVal))
             , locPhisBySrc :: Map mloc (Map mloc BoolVal)
             , locPhisByTrg :: Map mloc (Map mloc BoolVal)
             , memSetsBySrc :: Map mloc (Map mloc (ptr,Val,Val,BoolVal))
             , memSetsByPtr :: Map ptr (Map (mloc,mloc) (Val,Val,BoolVal))
             , memCopyBySrc :: Map mloc (Map mloc (ptr,ptr,CopyOptions))
             , memCopyBySrcPtr :: Map ptr (Map (mloc,mloc) (ptr,CopyOptions))
             , memCopyByTrgPtr :: Map ptr (Map (mloc,mloc) (ptr,CopyOptions))
             , freesBySrc :: Map mloc (Map mloc ptr)
             , freesByPtr :: Map ptr (Set (mloc,mloc))
             }

memGraphEmpty :: MemoryGraph mloc ptr
memGraphEmpty = MemGraph { nullsByPtr = Map.empty
                         , comparesByLHS = Map.empty
                         , comparesByRHS = Map.empty
                         , ptrPhisByTrg = Map.empty
                         , ptrPhisBySrc = Map.empty
                         , ptrIdxBySrc = Map.empty
                         , ptrIdxByTrg = Map.empty
                         , ptrCastsBySrc = Map.empty
                         , ptrCastsByTrg = Map.empty
                         , allocsBySrcLoc = Map.empty
                         , allocsByTrgLoc = Map.empty
                         , allocsByPtr = Map.empty
                         , loadsBySrcLoc = Map.empty
                         , loadsBySrcPtr = Map.empty
                         , ptrLoadsBySrcLoc = Map.empty
                         , ptrLoadsBySrcPtr = Map.empty
                         , ptrLoadsByTrgPtr = Map.empty
                         , storesBySrcLoc = Map.empty
                         , storesByTrgLoc = Map.empty
                         , storesByTrgPtr = Map.empty
                         , ptrStoresBySrcLoc = Map.empty
                         , ptrStoresByTrgLoc = Map.empty
                         , ptrStoresByTrgPtr = Map.empty
                         , ptrStoresBySrcPtr = Map.empty
                         , locPhisBySrc = Map.empty
                         , locPhisByTrg = Map.empty
                         , memSetsBySrc = Map.empty
                         , memSetsByPtr = Map.empty
                         , memCopyBySrc = Map.empty
                         , memCopyBySrcPtr = Map.empty
                         , memCopyByTrgPtr = Map.empty
                         , freesBySrc = Map.empty
                         , freesByPtr = Map.empty
                         }

connectLocation :: (Ord mloc,Ord ptr) => BoolVal -> mloc -> mloc -> MemoryGraph mloc ptr -> MemoryGraph mloc ptr
connectLocation cond locSrc locTrg gr
    = gr { locPhisBySrc = Map.insertWith Map.union locSrc (Map.singleton locTrg cond) (locPhisBySrc gr)
         , locPhisByTrg = Map.insertWith Map.union locTrg (Map.singleton locSrc cond) (locPhisByTrg gr) }

connectPointer :: (Ord mloc,Ord ptr) => BoolVal -> ptr -> ptr -> MemoryGraph mloc ptr -> MemoryGraph mloc ptr
connectPointer cond pSrc pTrg gr
    = gr { ptrPhisBySrc = Map.insertWith Map.union pSrc (Map.singleton pTrg cond) (ptrPhisBySrc gr)
         , ptrPhisByTrg = Map.insertWith Map.union pTrg (Map.singleton pSrc cond) (ptrPhisByTrg gr) }

addGraphInstruction :: (Ord mloc,Ord ptr,Show mloc,Show ptr) => BoolVal -> MemoryInstruction mloc ptr res -> res
                  -> MemoryGraph mloc ptr -> MemoryGraph mloc ptr
addGraphInstruction _ (MINull tp ptr) () gr
  = gr { nullsByPtr = Map.insert ptr tp (nullsByPtr gr) }
addGraphInstruction act (MIAlloc mfrom tp sz ptr mto) () gr
  = gr { allocsBySrcLoc = Map.insertWith Map.union mfrom (Map.singleton mto (tp,sz,ptr,act)) (allocsBySrcLoc gr)
       , allocsByTrgLoc = Map.insert mto (mfrom,tp,sz,ptr,act) (allocsByTrgLoc gr)
       , allocsByPtr = Map.insert ptr (mfrom,tp,sz,mto,act) (allocsByPtr gr) }
addGraphInstruction act (MILoad mfrom ptr _) res gr
  = gr { loadsBySrcLoc = Map.insert mfrom (ptr,res,act) (loadsBySrcLoc gr)
       , loadsBySrcPtr = Map.insertWith Map.union ptr (Map.singleton mfrom (res,act)) (loadsBySrcPtr gr) }
addGraphInstruction act (MILoadPtr mfrom ptrSrc ptrTrg) () gr
  = gr { ptrLoadsBySrcLoc = Map.insertWith (++) mfrom [(ptrSrc,ptrTrg,act)] (ptrLoadsBySrcLoc gr)
       , ptrLoadsBySrcPtr = Map.insertWith Map.union ptrSrc (Map.singleton mfrom (ptrTrg,act)) (ptrLoadsBySrcPtr gr)
       , ptrLoadsByTrgPtr = Map.insert ptrTrg (mfrom,ptrTrg,act) (ptrLoadsByTrgPtr gr) }
addGraphInstruction act (MIStore mfrom bv ptr mto) () gr
  = gr { storesBySrcLoc = Map.insertWith Map.union mfrom (Map.singleton mto (bv,ptr,act)) (storesBySrcLoc gr)
       , storesByTrgLoc = Map.insert mto (mfrom,bv,ptr,act) (storesByTrgLoc gr)
       , storesByTrgPtr = Map.insertWith Map.union ptr (Map.singleton (mfrom,mto) (bv,act)) (storesByTrgPtr gr) }
addGraphInstruction act (MIStorePtr mfrom ptrSrc ptrTrg mto) () gr
  = gr { ptrStoresBySrcLoc = Map.insertWith Map.union mfrom (Map.singleton mto (ptrSrc,ptrTrg,act)) (ptrStoresBySrcLoc gr)
       , ptrStoresByTrgLoc = Map.insert mto (mfrom,ptrSrc,ptrTrg,act) (ptrStoresByTrgLoc gr)
       , ptrStoresBySrcPtr = Map.insertWith Map.union ptrSrc (Map.singleton (mfrom,mto) (ptrTrg,act)) (ptrStoresBySrcPtr gr)
       , ptrStoresByTrgPtr = Map.insertWith Map.union ptrTrg (Map.singleton (mfrom,mto) (ptrSrc,act)) (ptrStoresByTrgPtr gr)
       }
addGraphInstruction _ (MICompare p1 p2) res gr
  = gr { comparesByLHS = Map.insert p1 (p2,res) (comparesByLHS gr)
       , comparesByRHS = Map.insert p2 (p1,res) (comparesByRHS gr) }
addGraphInstruction _ (MISelect cases ptr) () gr
  = gr { ptrPhisByTrg = Map.insert ptr (Map.fromList [ (ptr',cond) | (cond,ptr') <- cases ]) (ptrPhisByTrg gr)
       , ptrPhisBySrc = foldl (\mp (cond,ptr') -> Map.insertWith Map.union ptr' (Map.singleton ptr cond) mp
                              ) (ptrPhisBySrc gr) cases }
addGraphInstruction _ (MICast tpFrom tpTo ptrSrc ptrTrg) () gr
  = gr { ptrCastsBySrc = Map.insertWith Map.union ptrSrc (Map.singleton ptrTrg (tpFrom,tpTo)) (ptrCastsBySrc gr)
       , ptrCastsByTrg = Map.insert ptrTrg (ptrSrc,tpFrom,tpTo) (ptrCastsByTrg gr) }
addGraphInstruction _ (MIIndex tpSrc tpTrg idx ptrSrc ptrTrg) () gr
  = gr { ptrIdxBySrc = Map.insertWith Map.union ptrSrc (Map.singleton ptrTrg (tpSrc,tpTrg,idx)) (ptrIdxBySrc gr)
       , ptrIdxByTrg = Map.insert ptrTrg (ptrSrc,tpSrc,tpTrg,idx) (ptrIdxByTrg gr) }
addGraphInstruction act (MIPhi cases mto) () gr
  = gr { locPhisBySrc = foldl (\mp (cond,mfrom) -> Map.insertWith Map.union mfrom (Map.singleton mto cond) mp
                              ) (locPhisBySrc gr) cases
       , locPhisByTrg = Map.insertWith Map.union mto (Map.fromList [ (mfrom,cond) | (cond,mfrom) <- cases ]) (locPhisByTrg gr) }
addGraphInstruction act (MISet mfrom ptr val len mto) () gr
  = gr { memSetsBySrc = Map.insertWith Map.union mfrom (Map.singleton mto (ptr,val,len,act))
                        (memSetsBySrc gr)
       , memSetsByPtr = Map.insertWith Map.union ptr (Map.singleton (mfrom,mto) (val,len,act))
                        (memSetsByPtr gr) }
addGraphInstruction act (MICopy mfrom ptrFrom ptrTo opts mto) () gr
  = gr { memCopyBySrc = Map.insertWith Map.union mfrom (Map.singleton mto (ptrFrom,ptrTo,opts))
                        (memCopyBySrc gr)
       , memCopyBySrcPtr = Map.insertWith Map.union ptrFrom (Map.singleton (mfrom,mto) (ptrTo,opts))
                           (memCopyBySrcPtr gr) }
addGraphInstruction act (MIFree mfrom ptr mto) () gr
  = gr { freesBySrc = Map.insertWith Map.union mfrom (Map.singleton mto ptr) (freesBySrc gr)
       , freesByPtr = Map.insertWith Set.union ptr (Set.singleton (mfrom,mto)) (freesByPtr gr) }
addGraphInstruction act (MIConnect mfrom mto) () gr
  = gr { locPhisBySrc = Map.insertWith Map.union mfrom (Map.singleton mto act) (locPhisBySrc gr)
       , locPhisByTrg = Map.insertWith Map.union mto (Map.singleton mfrom act) (locPhisByTrg gr) }
addGraphInstruction act (MIPtrConnect pfrom pto) () gr
  = gr { ptrPhisBySrc = Map.insertWith Map.union pfrom (Map.singleton pto act) (ptrPhisBySrc gr)
       , ptrPhisByTrg = Map.insertWith Map.union pto (Map.singleton pfrom act) (ptrPhisByTrg gr) }
addGraphInstruction _ instr _ _ = error $ "MemoryGraph: Unimplemented instruction: "++show instr
