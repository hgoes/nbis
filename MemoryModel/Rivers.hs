{-# LANGUAGE MultiParamTypeClasses #-}
module MemoryModel.Rivers where

import Data.Map (Map,(!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable
import Data.Traversable
import Prelude hiding (foldl,foldl1,mapM,mapM_,sum,sequence,sequence_,concat,all)
import Data.List (genericLength,genericSplitAt)
import qualified Data.List as List
import Data.Monoid

import Language.SMTLib2
import MemoryModel
import TypeDesc

import Debug.Trace

data RiverMemory mloc ptr
  = RiverMemory { riverPointerWidth :: Integer
                , riverPointerOffset :: Integer
                , riverPointers :: Map ptr PointerInfo
                , riverNextObject :: RiverObjectRef
                , riverLocations :: Map mloc RiverLocation
                , riverGlobals :: RiverLocation
                , riverProgram :: [(SMTExpr Bool,MemoryInstruction mloc ptr)]
                , riverConnections :: Map mloc (Set mloc)
                , riverPointerConnections :: Map ptr (Set ptr)
                , riverStructs :: Map String [TypeDesc]
                , riverErrors :: [(ErrorDesc,SMTExpr Bool)]
                }

newtype RiverObjectRef = RiverObjectRef Integer deriving (Show,Eq,Ord,Enum)

type RiverReachability = Map RiverObjectRef (Maybe (Set Integer))

data RiverLocation = RiverLocation { riverObjects :: Map RiverObjectRef ObjectInfo } deriving Show

data PointerInfo = PointerInfo { pointerObject :: SMTExpr (BitVector BVUntyped)
                               , pointerOffset :: SMTExpr (BitVector BVUntyped)
                               , pointerReachability :: RiverReachability
                               , pointerType :: TypeDesc
                               }

data ObjectInfo = ObjectInfo { objectRepresentation :: RiverObject
                             , objectReachability :: RiverReachability
                             } deriving (Show,Eq)

data Offset = Offset { staticOffset :: Integer
                     , dynamicOffset :: Maybe (SMTExpr (BitVector BVUntyped))
                     } deriving Show

data RiverObject = StaticObject TypeDesc (SMTExpr (BitVector BVUntyped))
                 | DynamicObject TypeDesc (SMTExpr (SMTArray (SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped)))
                   (Either Integer (SMTExpr (BitVector BVUntyped)))
                 deriving (Show,Eq)

nullObj :: RiverObjectRef
nullObj = RiverObjectRef 0

instance (Ord ptr,Ord mloc,Show ptr,Show mloc) => MemoryModel (RiverMemory mloc ptr) mloc ptr where
  memNew _ ptrWidth _ structs globals = do
    let ptrOffset = ptrWidth `div` 2
    (globs,ptrs,next) <- foldlM (\(loc,ptrs,next) (ptr,tp,cont) -> do
                                    glob <- case cont of
                                      Just cont' -> mkGlobal ptrWidth structs tp cont'
                                    return (loc { riverObjects = Map.insert (RiverObjectRef next) (ObjectInfo { objectRepresentation = glob
                                                                                                              , objectReachability = Map.empty }) (riverObjects loc)
                                                },Map.insert ptr (PointerInfo { pointerObject = objRepr ptrOffset (RiverObjectRef next)
                                                                              , pointerOffset = offRepr ptrWidth ptrOffset 0
                                                                              , pointerReachability = Map.singleton (RiverObjectRef next) (Just $ Set.singleton 0)
                                                                              , pointerType = tp
                                                                              }) ptrs,succ next)
                                ) (RiverLocation Map.empty,Map.empty,1) globals
    return $ RiverMemory { riverPointerWidth = ptrWidth
                         , riverPointerOffset = ptrOffset
                         , riverPointers = ptrs
                         , riverNextObject = RiverObjectRef next
                         , riverLocations = Map.empty
                         , riverGlobals = globs
                         , riverProgram = []
                         , riverConnections = Map.empty
                         , riverPointerConnections = Map.empty
                         , riverStructs = structs
                         , riverErrors = []
                         }
  makeEntry _ mem loc = return $ mem { riverLocations = Map.insert loc (riverGlobals mem) (riverLocations mem) }
  addProgram mem cond prev is ptrs = do
    --trace ("Add program: "++show is) (return ())
    let is' = fmap (\i -> (cond,i)) is
    addInstructions ptrs (mem { riverProgram = is'++(riverProgram mem) }) is' {->>= simplifyRiver-}
  connectLocation mem _ cond locFrom locTo = do
    --trace ("Connect location: "++show cond++" "++show locFrom++" ~> "++show locTo) (return ())
    let mem1 = mem { riverLocations = insertIfNotPresent locFrom (RiverLocation Map.empty) $
                                      insertIfNotPresent locTo (RiverLocation Map.empty) $
                                      riverLocations mem
                   , riverConnections = Map.insertWith Set.union locFrom (Set.singleton locTo) (riverConnections mem) }
        locFrom' = (riverLocations mem1)!locFrom
        locTo' = (riverLocations mem1)!locTo
    (nobjs,nreach) <- foldlM (\(cobjs,creach) (objRef,objInfo) -> case Map.lookup objRef (riverObjects locTo') of
                                 Just objInfo' -> do
                                   assert $ cond .=>. (objectEq (objectRepresentation objInfo) (objectRepresentation objInfo'))
                                   return (cobjs,Map.insertWith unionReachability objRef (objectReachability objInfo) creach)
                                 Nothing -> do
                                   skel <- objectSkel (objectRepresentation objInfo)
                                   assert $ cond .=>. (objectEq (objectRepresentation objInfo) skel)
                                   return (Map.insert objRef (ObjectInfo { objectRepresentation = skel
                                                                         , objectReachability = objectReachability objInfo }) cobjs,creach)
                             ) (Map.empty,Map.empty) (Map.toList $ riverObjects locFrom')
    let ptrReach = Map.mapMaybe (\ptrInfo -> let diffReach = Map.intersection (pointerReachability ptrInfo) nobjs
                                             in if Map.null diffReach
                                                then Nothing
                                                else Just diffReach
                                ) (riverPointers mem1)
    let upd = noUpdate { newPtrReachability = ptrReach
                       , newObjReachability = Map.singleton locTo nreach
                       , newObjects = Map.singleton locTo nobjs
                       }
    applyUpdateRec mem1 upd
  connectPointer mem _ cond ptrSrc ptrTrg = do
    --trace ("Connect pointer: "++show cond++" "++show ptrSrc++" ~> "++show ptrTrg) (return ())
    let Just ptrSrc' = Map.lookup ptrSrc (riverPointers mem)
    (ptrTrg',mem1) <- case Map.lookup ptrTrg (riverPointers mem) of
      Nothing -> do
        info <- newPointer (riverPointerWidth mem) (riverPointerOffset mem) (pointerType ptrSrc')
        return (info,mem { riverPointers = Map.insert ptrTrg info (riverPointers mem) })
      Just info -> return (info,mem)
    assert $ cond .=>. (((pointerObject ptrTrg') .==. (pointerObject ptrSrc')) .&&.
                        ((pointerOffset ptrTrg') .==. (pointerOffset ptrSrc')))
    let upds = updateFromPtr mem1 ptrSrc
        upd = noUpdate { newPtrReachability = case Map.lookup ptrSrc (newPtrReachability upds) of
                            Just res -> Map.singleton ptrTrg res
                            Nothing -> Map.empty
                       }
    applyUpdateRec mem1 upd
  memoryErrors mem _ _ = riverErrors mem
  debugMem mem _ _ = debugRiver mem

addInstructions :: (Ord ptr,Ord mloc,Show ptr,Show mloc) => Map ptr TypeDesc
                   -> RiverMemory mloc ptr
                   -> [(SMTExpr Bool,MemoryInstruction mloc ptr)]
                   -> SMT (RiverMemory mloc ptr)
addInstructions ptrs mem is
  = foldlM (\cmem (cond,i) -> do
               (cmem',upd) <- initUpdate ptrs cmem cond i
               return $ applyUpdate cmem' upd
           ) mem is

data Update mloc ptr = Update { newPtrReachability :: Map ptr RiverReachability                       -- ^ New reachability information for pointers
                              , newObjReachability :: Map mloc (Map RiverObjectRef RiverReachability) -- ^ New reachability information for objects
                              , newObjects :: Map mloc (Map RiverObjectRef ObjectInfo)                -- ^ New reachable objects
                              }
                     deriving Show

noUpdate :: Update mloc ptr
noUpdate = Update Map.empty Map.empty Map.empty

isNoUpdate :: (Ord mloc,Ord ptr) => Update mloc ptr -> Bool
isNoUpdate upd = Map.null (newPtrReachability upd) &&
                 Map.null (newObjReachability upd) &&
                 (all Map.null (newObjects upd))

instance (Ord ptr,Ord mloc) => Monoid (Update mloc ptr) where
  mempty = noUpdate
  mappend u1 u2 = Update { newPtrReachability = Map.unionWith unionReachability (newPtrReachability u1) (newPtrReachability u2)
                         , newObjReachability = Map.unionWith (Map.unionWith unionReachability) (newObjReachability u1) (newObjReachability u2)
                         , newObjects = Map.unionWith Map.union (newObjects u1) (newObjects u2)
                         }

unionReachability :: RiverReachability -> RiverReachability -> RiverReachability
unionReachability = Map.unionWith (\reach1 reach2 -> case (reach1,reach2) of
                                      (Just r1,Just r2) -> Just (Set.union r1 r2)
                                      _ -> Nothing)

updateInstruction :: (Ord ptr,Ord mloc,Show ptr,Show mloc)
                     => RiverMemory mloc ptr
                     -> Update mloc ptr
                     -> SMTExpr Bool
                     -> MemoryInstruction mloc ptr
                     -> SMT (Update mloc ptr,[(ErrorDesc,SMTExpr Bool)])
updateInstruction mem _ _ (MINull _ _) = return (noUpdate,[])
updateInstruction mem upd _ (MIAlloc mfrom _ _ _ mto)
  = return (noUpdate { newObjReachability = case Map.lookup mfrom (newObjReachability upd) of
                          Nothing -> Map.empty
                          Just nreach -> Map.singleton mto nreach
                     , newObjects = case Map.lookup mfrom (newObjects upd) of
                          Nothing -> Map.empty
                          Just nobjs -> Map.singleton mto nobjs },[])
updateInstruction mem upd act (MILoad mfrom ptr res) = case Map.lookup ptr (newPtrReachability upd) of
  Nothing -> return (noUpdate,[])
  Just nreach -> do
    let Just locInfo = Map.lookup mfrom (riverLocations mem)
        Just ptrInfo = Map.lookup ptr (riverPointers mem)
    errs <- sequence $ Map.mapWithKey
            (\objRef reach
             -> let obj = case Map.lookup objRef (riverObjects locInfo) of
                      Just o -> o
                      Nothing -> error $ "Internal error: Object "++show objRef++" not found at location "++show mfrom++" ("++show locInfo++")"
                in case reach of
                  Nothing -> do
                    let off = Offset { staticOffset = 0
                                     , dynamicOffset = Just $ pointerOffset ptrInfo
                                     }
                        cond = (pointerObject ptrInfo) .==. objRepr (riverPointerOffset mem) objRef
                        (loadRes,errs) = loadObject (act .&&. cond) ((extractAnnotation res) `div` 8) (objectRepresentation obj) off
                    case loadRes of
                      Just loadRes' -> assert $ cond .=>. (res .==. loadRes')
                      Nothing -> return ()
                    return errs
                  Just offs -> do
                    errs <- foldlM (\cerrs soff -> do
                                       let off = Offset { staticOffset = soff
                                                        , dynamicOffset = Nothing }
                                           cond = ((pointerObject ptrInfo) .==. objRepr (riverPointerOffset mem) objRef) .&&.
                                                  ((pointerOffset ptrInfo) .==. offRepr (riverPointerWidth mem) (riverPointerOffset mem) soff)
                                           (loadRes,errs) = loadObject (act .&&. cond) ((extractAnnotation res) `div` 8) (objectRepresentation obj) off
                                       case loadRes of
                                         Nothing -> return ()
                                         Just loadRes' -> assert $ cond .=>. (res .==. loadRes')
                                       return (errs++cerrs)
                                   ) [] offs
                    return errs
            ) (Map.delete nullObj nreach)
    return (noUpdate,(if Map.member nullObj nreach
                      then [(NullDeref,act .&&. ((pointerObject ptrInfo) .==. objRepr (riverPointerOffset mem) nullObj))]
                      else [])++concat errs)
updateInstruction mem upd act (MILoadPtr mfrom ptrSrc ptrTrg) = do
  let Just locInfo = Map.lookup mfrom (riverLocations mem)
      Just ptrFromInfo = Map.lookup ptrSrc (riverPointers mem)
      Just ptrToInfo = Map.lookup ptrTrg (riverPointers mem)
  -- Two things can happen:
  -- 1. An existing object gets reachable:
  (upd1,errs1) <- case Map.lookup ptrSrc (newPtrReachability upd) of
    Nothing -> return (noUpdate,[])
    Just nreach -> do
      (nreach',errs)
         <- Map.foldlWithKey
            (\cupd objRef reach -> do
                     (cupd',cerrs) <- cupd
                     let Just obj = Map.lookup objRef (riverObjects locInfo)
                     nerrs <- case reach of
                       Nothing -> do
                         let off = Offset { staticOffset = 0
                                          , dynamicOffset = Just $ pointerOffset ptrFromInfo }
                             cond = (pointerObject ptrFromInfo) .==. objRepr (riverPointerOffset mem) objRef
                             (loadRes,errs) = loadObject (act .&&. cond) (riverPointerWidth mem) (objectRepresentation obj) off
                         case loadRes of
                           Just loadRes' -> assert $ cond .=>. ((bvconcat (pointerObject ptrToInfo) (pointerOffset ptrToInfo)) .==. loadRes')
                           Nothing -> return ()
                         return errs
                       Just offs -> do
                         errs <- foldlM (\cerrs soff -> do
                                            let off = Offset { staticOffset = soff
                                                             , dynamicOffset = Nothing }
                                                cond = ((pointerObject ptrFromInfo) .==. objRepr (riverPointerOffset mem) objRef) .&&.
                                                       ((pointerOffset ptrFromInfo) .==. offRepr (riverPointerWidth mem) (riverPointerOffset mem) soff)
                                                (loadRes,errs) = loadObject (act .&&. cond) (riverPointerWidth mem) (objectRepresentation obj) off
                                            case loadRes of
                                              Just loadRes' -> assert $ cond .=>. ((bvconcat (pointerObject ptrToInfo) (pointerOffset ptrToInfo)) .==. loadRes')
                                              Nothing -> return ()
                                            return (errs++cerrs)
                                        ) [] offs
                         return errs
                     return (unionReachability cupd' (objectReachability obj),nerrs)
                 ) (return (Map.empty,[])) (Map.delete nullObj nreach)
      return (noUpdate { newPtrReachability = Map.singleton ptrTrg nreach' },
              (if Map.member nullObj nreach
               then [(NullDeref,act .&&. ((pointerObject ptrFromInfo) .==. objRepr (riverPointerOffset mem) nullObj))]
               else [])++errs)
  -- 2. An already reachable object gets new reachability information:
  let upd2 = case Map.lookup mfrom (newObjReachability upd) of
        Nothing -> noUpdate
        Just nobjReach -> noUpdate { newPtrReachability = Map.singleton ptrTrg $
                                                          Map.foldlWithKey (\cupd reachObj _ -> case Map.lookup reachObj nobjReach of
                                                                               Nothing -> cupd
                                                                               Just nreach -> unionReachability cupd nreach
                                                                           ) Map.empty (pointerReachability ptrFromInfo)
                                   }
  return (upd1 `mappend` upd2,errs1)
updateInstruction mem upd act (MIStore mfrom word ptr mto) = do
  let Just locFrom = Map.lookup mfrom (riverLocations mem)
      Just ptr' = Map.lookup ptr (riverPointers mem)
      newObjs1 = Map.findWithDefault Map.empty mfrom (newObjects upd)
  case Map.lookup ptr (newPtrReachability upd) of
    Nothing -> return (noUpdate,[])
    Just nreach
      -> let (newObjs2,errs)
               = Map.foldlWithKey (\(objs,errs) objRef reach
                                   -> let Just obj = Map.lookup objRef (riverObjects locFrom)
                                      in case reach of
                                        Nothing -> let off = Offset { staticOffset = 0
                                                                    , dynamicOffset = Just $ pointerOffset ptr' }
                                                       cond = (pointerObject ptr') .==. objRepr (riverPointerOffset mem) objRef
                                                       (obj',errs') = storeObject
                                                                      (riverPointerWidth mem)
                                                                      (riverStructs mem)
                                                                      (act .&&. cond) word (objectRepresentation obj) off
                                                   in (Map.insert objRef (obj { objectRepresentation = objectITE cond
                                                                                                       obj'
                                                                                                       (objectRepresentation obj) }) objs,errs'++errs)
                                        Just offs -> let (nobj,nerrs)
                                                           = foldl (\(cobj,cerrs) soff
                                                                    -> let off = Offset { staticOffset = soff
                                                                                        , dynamicOffset = Nothing }
                                                                           cond = ((pointerObject ptr') .==. objRepr (riverPointerOffset mem) objRef) .&&.
                                                                                  ((pointerOffset ptr') .==. offRepr (riverPointerWidth mem) (riverPointerOffset mem) soff)
                                                                           (obj',errs') = storeObject
                                                                                          (riverPointerWidth mem)
                                                                                          (riverStructs mem)
                                                                                          (act .&&. cond) word (objectRepresentation obj) off
                                                                       in (cobj { objectRepresentation = objectITE cond
                                                                                                         obj'
                                                                                                         (objectRepresentation obj)
                                                                                },errs'++cerrs)
                                                                   ) (obj,[]) offs
                                                            in (Map.insert objRef nobj objs,nerrs++errs)
                                  ) (newObjs1,[]) (Map.delete nullObj nreach)
         in return (noUpdate { newObjects = Map.singleton mto newObjs2 },
                    (if Map.member nullObj nreach
                     then [(NullDeref,act .&&. ((pointerObject ptr') .==. objRepr (riverPointerOffset mem) nullObj))]
                     else [])++errs)
updateInstruction mem upd act (MIStorePtr mfrom ptrFrom ptrTo mto) = do
  let Just locFrom = Map.lookup mfrom (riverLocations mem)
      Just ptrFrom' = Map.lookup ptrFrom (riverPointers mem)
      Just ptrTo' = Map.lookup ptrTo (riverPointers mem)
      word = bvconcat (pointerObject ptrFrom') (pointerOffset ptrFrom')
      newObjs1 = Map.findWithDefault Map.empty mfrom (newObjects upd)
      newObjReach = case Map.lookup ptrFrom (newPtrReachability upd) of
        Nothing -> Map.empty
        Just nreach -> Map.singleton mto (Map.mapWithKey (\obj _ -> nreach) (pointerReachability ptrTo'))
  case Map.lookup ptrTo (newPtrReachability upd) of
    Nothing -> return (noUpdate { newObjReachability = newObjReach },[])
    Just nreach
      -> let (newObjs2,errs)
               = Map.foldlWithKey (\(objs,errs) objRef reach
                                   -> let Just obj = Map.lookup objRef (riverObjects locFrom)
                                      in case reach of
                                        Nothing -> let off = Offset { staticOffset = 0
                                                                    , dynamicOffset = Just $ pointerOffset ptrFrom' }
                                                       cond = (pointerObject ptrTo') .==. objRepr (riverPointerOffset mem) objRef
                                                       (obj',errs') = storeObject
                                                                      (riverPointerWidth mem)
                                                                      (riverStructs mem)
                                                                      (act .&&. cond) word (objectRepresentation obj) off
                                                   in (Map.insert objRef (obj { objectRepresentation = objectITE cond
                                                                                                       obj'
                                                                                                       (objectRepresentation obj) }) objs,errs'++errs)
                                        Just offs -> let (nobj,nerrs)
                                                           = foldl (\(cobj,cerrs) soff
                                                                    -> let off = Offset { staticOffset = soff
                                                                                        , dynamicOffset = Nothing }
                                                                           cond = ((pointerObject ptrTo') .==. objRepr (riverPointerOffset mem) objRef) .&&.
                                                                                  ((pointerOffset ptrTo') .==. offRepr (riverPointerWidth mem) (riverPointerOffset mem) soff)
                                                                           (obj',errs') = storeObject
                                                                                          (riverPointerWidth mem)
                                                                                          (riverStructs mem)
                                                                                          (act .&&. cond) word (objectRepresentation obj) off
                                                                       in (cobj { objectRepresentation = objectITE cond
                                                                                                         obj'
                                                                                                         (objectRepresentation obj)
                                                                                },errs'++cerrs)
                                                                   ) (obj,[]) offs
                                                     in (Map.insert objRef nobj objs,nerrs++errs)
                                  ) (newObjs1,[]) (Map.delete nullObj nreach)
         in return (noUpdate { newObjects = Map.singleton mto newObjs2
                             , newObjReachability = newObjReach },
                    (if Map.member nullObj nreach
                     then [(NullDeref,act .&&. ((pointerObject ptrTo') .==. objRepr (riverPointerOffset mem) nullObj))]
                     else [])++errs)
updateInstruction _ _ _ (MICompare _ _ _) = return (noUpdate,[])
updateInstruction _ upd _ (MISelect cases pto)
  = return (foldl (\cupd (_,pfrom) -> case Map.lookup pfrom (newPtrReachability upd) of
                      Nothing -> cupd
                      Just nreach -> cupd { newPtrReachability = Map.insertWith unionReachability pto nreach (newPtrReachability cupd) }
                  ) noUpdate cases,[])
updateInstruction mem upd _ (MICast _ _ pfrom pto) = case Map.lookup pfrom (newPtrReachability upd) of
  Nothing -> return (noUpdate,[])
  Just nreach -> return (noUpdate { newPtrReachability = Map.singleton pto nreach },[])
updateInstruction mem upd _ (MIIndex tp_from _ idx pfrom pto) = case Map.lookup pfrom (newPtrReachability upd) of
  Nothing -> return (noUpdate,[])
  Just nreach -> let off = buildOffset (riverPointerWidth mem) (riverStructs mem) tp_from idx
                     nreach' = fmap (\reach' -> case reach' of
                                        Nothing -> Nothing
                                        Just offs -> case dynamicOffset off of
                                          Nothing -> Just $ Set.map (\soff -> soff + (staticOffset off)) offs
                                          Just _ -> Nothing) nreach
                 in return (noUpdate { newPtrReachability = Map.singleton pto nreach' },[])
updateInstruction mem upd _ (MIPhi cases mto) = do
  let allLocs = Map.fromList [ (m,()) | (_,m) <- cases ]
      newObjs = buildNewObjs cases
      newReach = foldl (Map.unionWith unionReachability) Map.empty $
                 Map.intersection (newObjReachability upd) allLocs
  return (noUpdate { newObjects = if Map.null newObjs
                                  then Map.empty
                                  else Map.singleton mto newObjs
                   , newObjReachability = if Map.null newReach
                                          then Map.empty
                                          else Map.singleton mto newReach },[])
  where
    buildNewObjs [(_,loc)] = case Map.lookup loc (newObjects upd) of
      Just objs -> objs
      Nothing -> Map.empty
    buildNewObjs ((c,loc):locs) = let nobjs = buildNewObjs locs
                                      objs = case Map.lookup loc (newObjects upd) of
                                        Just o -> o
                                        Nothing -> Map.empty
                                  in Map.unionWith (\obj1 obj2 -> ObjectInfo { objectRepresentation = objectITE c (objectRepresentation obj1) (objectRepresentation obj2)
                                                                             , objectReachability = unionReachability (objectReachability obj1) (objectReachability obj2)
                                                                             }) objs nobjs

applyUpdate :: (Ord mloc,Ord ptr,Show mloc,Show ptr) => RiverMemory mloc ptr -> Update mloc ptr -> RiverMemory mloc ptr
applyUpdate mem upd
  = let mem1 = Map.foldlWithKey (\cmem loc newObjs
                                 -> cmem { riverLocations = Map.adjust (\(RiverLocation locInfo)
                                                                        -> RiverLocation $
                                                                           Map.union locInfo newObjs
                                                                       ) loc (riverLocations cmem)
                                         }) mem (newObjects upd)
        mem2 = Map.foldlWithKey (\cmem ptr nreach -> cmem { riverPointers = Map.adjust (\info -> info { pointerReachability = unionReachability (pointerReachability info) nreach
                                                                                                      }) ptr (riverPointers cmem) }
                                ) mem1 (newPtrReachability upd)
        mem3 = Map.foldlWithKey (\cmem loc objReaches
                                 -> cmem { riverLocations = Map.adjust (\(RiverLocation locInfo)
                                                                        -> RiverLocation $
                                                                           Map.differenceWith
                                                                           (\objInfo nreach -> Just $ objInfo { objectReachability = unionReachability (objectReachability objInfo) nreach
                                                                                                              }
                                                                           ) locInfo objReaches
                                                                       ) loc (riverLocations cmem) }
                                ) mem2 (newObjReachability upd)
    in mem3

propagateUpdate :: (Ord mloc,Ord ptr) => RiverMemory mloc ptr -> Update mloc ptr -> Update mloc ptr
propagateUpdate mem upd
  = noUpdate { newPtrReachability = Map.fromList
                                    [ (trg,nreach)
                                    | (trgs,nreach) <- Map.elems $ Map.intersectionWith (\x y -> (x,y)) (riverPointerConnections mem) (newPtrReachability upd)
                                    , trg <- Set.toList trgs ]
             , newObjReachability = Map.fromList
                                    [ (trg,nreach)
                                    | (trgs,nreach) <- Map.elems $ Map.intersectionWith (\x y -> (x,y)) (riverConnections mem) (newObjReachability upd)
                                    , trg <- Set.toList trgs ]
             }

initUpdate :: (Ord mloc,Ord ptr,Show mloc,Show ptr) => Map ptr TypeDesc -> RiverMemory mloc ptr -> SMTExpr Bool -> MemoryInstruction mloc ptr -> SMT (RiverMemory mloc ptr,Update mloc ptr)
initUpdate _ mem _ (MINull tp ptr) = do
  return (mem { riverPointers = Map.insert ptr
                                (PointerInfo { pointerObject = objRepr (riverPointerOffset mem) (RiverObjectRef 0)
                                             , pointerOffset = offRepr (riverPointerWidth mem) (riverPointerOffset mem) 0
                                             , pointerReachability = Map.singleton (RiverObjectRef 0) (Just (Set.singleton 0))
                                             , pointerType = tp
                                             })
                                (riverPointers mem)
              },noUpdate)
initUpdate _ mem act instr@(MIAlloc mfrom tp sz ptr mto) = do
  newObj <- case sz of
    Left 1 -> do
      v <- varNamedAnn "alloc" (bitWidth ((riverPointerWidth mem)*8) (riverStructs mem) tp)
      return $ StaticObject tp v
    Right sz -> do
      v <- varNamedAnn "allocArr" (64,bitWidth ((riverPointerWidth mem)*8) (riverStructs mem) tp)
      return $ DynamicObject tp v (Right sz)
  let mem1 = mem { riverNextObject = succ (riverNextObject mem)
                 , riverPointers = Map.insert ptr (PointerInfo { pointerObject = objRepr (riverPointerOffset mem)
                                                                                 (riverNextObject mem)
                                                               , pointerOffset = offRepr (riverPointerWidth mem)
                                                                                 (riverPointerOffset mem)
                                                                                 0
                                                               , pointerReachability = Map.empty
                                                               , pointerType = tp
                                                               }) (riverPointers mem)
                 , riverLocations = insertIfNotPresent mfrom (RiverLocation Map.empty) $
                                    insertIfNotPresent mto (RiverLocation Map.empty) $
                                    riverLocations mem
                 }
      upd = updateFromLoc mem1 mfrom
  (upd',errs) <- updateInstruction mem1 upd act instr
  return (mem1 { riverErrors = errs++(riverErrors mem1) },
          upd' { newObjects = Map.insertWith Map.union mto (Map.singleton (riverNextObject mem)
                                                            (ObjectInfo { objectRepresentation = newObj
                                                                        , objectReachability = Map.empty })) (newObjects upd')
               , newPtrReachability = Map.insert ptr (Map.singleton (riverNextObject mem) (Just $ Set.singleton 0)) (newPtrReachability upd')
               })
initUpdate ptrs mem act instr@(MILoad mfrom ptr res) = do
  (ptrInfo,mem1) <- getPointer mem ptrs ptr
  let mem2 = mem1 { riverLocations = insertIfNotPresent mfrom (RiverLocation Map.empty)
                                     (riverLocations mem1)
                  }
      upd = updateFromPtr mem2 ptr
  (upd',errs) <- updateInstruction mem2 upd act instr
  return (mem2 { riverErrors = errs++(riverErrors mem2) },upd')
initUpdate ptrs mem act instr@(MILoadPtr mfrom ptrFrom ptrTo) = do
  (_,mem1) <- getPointer mem ptrs ptrFrom
  (ptrInfo,mem2) <- getPointer mem1 ptrs ptrTo
  let mem3 = mem2 { riverLocations = insertIfNotPresent mfrom (RiverLocation Map.empty)
                                     (riverLocations mem2) }
      upd1 = updateFromPtr mem3 ptrFrom
      upd2 = updateFromPtr mem3 ptrTo
  (upd3,errs) <- updateInstruction mem3 (mappend upd1 upd2) act instr
  return (mem3 { riverErrors = errs++(riverErrors mem3) },upd3)
initUpdate ptrs mem act instr@(MIStore mfrom word ptr mto) = do
  (ptrInfo,mem1) <- getPointer mem ptrs ptr
  let mem2 = mem1 { riverLocations = insertIfNotPresent mfrom (RiverLocation Map.empty) $
                                     insertIfNotPresent mto (RiverLocation Map.empty) $
                                     riverLocations mem1
                  }
      upd1 = updateFromLoc mem2 mfrom
      upd2 = updateFromPtr mem2 ptr
  (upd3,errs) <- updateInstruction mem2 (mappend upd1 upd2) act instr
  return (mem2 { riverErrors = errs++(riverErrors mem2) },upd3)
initUpdate ptrs mem act instr@(MIStorePtr mfrom ptrFrom ptrTo mto) = do
  (_,mem1) <- getPointer mem ptrs ptrFrom
  (ptrInfo,mem2) <- getPointer mem1 ptrs ptrTo
  let mem3 = mem2 { riverLocations = insertIfNotPresent mfrom (RiverLocation Map.empty) $
                                     insertIfNotPresent mto (RiverLocation Map.empty) $
                                     riverLocations mem2
                  }
      upd1 = updateFromPtr mem3 ptrFrom
      upd2 = updateFromPtr mem3 ptrTo
      upd3 = updateFromLoc mem3 mfrom
      upd4 = mconcat [upd1,upd2,upd3]
  (upd5,errs) <- updateInstruction mem3 upd4 act instr
  return (mem3 { riverErrors = errs++(riverErrors mem3) },upd5)
initUpdate ptrs mem _ (MICompare ptr1 ptr2 res) = do
  (info1,mem1) <- getPointer mem ptrs ptr1
  (info2,mem2) <- getPointer mem1 ptrs ptr2
  assert $ res .==. (((pointerObject info1) .==. (pointerObject info2)) .&&.
                     ((pointerOffset info1) .==. (pointerOffset info2)))
  return (mem2,noUpdate)
initUpdate ptrs mem act instr@(MISelect cases ptr) = do
  (obj,off,mem1,upd1) <- buildCases mem cases
  obj' <- defConstNamed "ptrObj" obj
  off' <- defConstNamed "ptrOff" off
  let mem2 = mem1 { riverPointers = Map.insert ptr (PointerInfo { pointerObject = obj'
                                                                , pointerOffset = off'
                                                                , pointerReachability = Map.empty
                                                                , pointerType = ptrs!ptr
                                                                }) (riverPointers mem1)
                  }
  (upd2,errs) <- updateInstruction mem2 upd1 act instr
  return (mem2 { riverErrors = errs++(riverErrors mem2) },upd2)
  where
    buildCases cmem [(_,p)] = do
      (info,nmem) <- getPointer cmem ptrs p
      let upd = updateFromPtr nmem p
      return (pointerObject info,pointerOffset info,nmem,upd)
    buildCases cmem ((c,p):ps) = do
      (info,nmem) <- getPointer cmem ptrs p
      let upd1 = updateFromPtr nmem p
      (obj,off,nmem',upd2) <- buildCases nmem ps
      return (ite c (pointerObject info) obj,
              ite c (pointerOffset info) off,
              nmem',mappend upd1 upd2)
initUpdate ptrs mem act instr@(MICast _ _ ptrFrom ptrTo) = do
  (infoFrom,mem1) <- getPointer mem ptrs ptrFrom
  let mem2 = mem1 { riverPointers = Map.insert ptrTo (infoFrom { pointerReachability = Map.empty }) (riverPointers mem1) }
      upd = updateFromPtr mem2 ptrFrom
  (upd',errs) <- updateInstruction mem2 upd act instr
  return (mem2 { riverErrors = errs++(riverErrors mem2) },upd')
initUpdate ptrs mem act instr@(MIIndex tpFrom tpTo idx ptrFrom ptrTo) = do
  (infoFrom,mem1) <- getPointer mem ptrs ptrFrom
  let tp_to = ptrs!ptrTo
      off = buildOffset (riverPointerWidth mem1) (riverStructs mem1) tpFrom idx
      mem2 = mem1 { riverPointers = Map.insert ptrTo (PointerInfo { pointerObject = pointerObject infoFrom
                                                                  , pointerOffset = bvadd (pointerOffset infoFrom)
                                                                                    (offsetToExpr ((riverPointerWidth mem1)-(riverPointerOffset mem2)) off)
                                                                  , pointerReachability = Map.empty
                                                                  , pointerType = tp_to
                                                                  }) (riverPointers mem1)
                  }
      upd = updateFromPtr mem2 ptrFrom
  (upd',errs) <- updateInstruction mem2 upd act instr
  return (mem2 { riverErrors = errs++(riverErrors mem2) },upd')
initUpdate ptrs mem act instr@(MIPhi cases mto) = do
  let (mem1,upd) = buildCases (mem { riverLocations = insertIfNotPresent mto (RiverLocation Map.empty)
                                                      (riverLocations mem)
                                   }) cases
  (upd',errs) <- updateInstruction mem1 upd act instr
  return (mem1 { riverErrors = errs++(riverErrors mem1) },upd')
  where
    buildCases cmem [(_,loc)]
      = let cmem1 = cmem { riverLocations = insertIfNotPresent loc (RiverLocation Map.empty)
                                            (riverLocations cmem) }
            upd = updateFromLoc cmem1 loc
        in (cmem1,upd)
    buildCases cmem ((c,loc):locs)
      = let cmem1 = cmem { riverLocations = insertIfNotPresent loc (RiverLocation Map.empty)
                                            (riverLocations cmem) }
            upd1 = updateFromLoc cmem1 loc
            (cmem2,upd2) = buildCases cmem1 locs
        in (cmem2,mappend upd1 upd2)

applyUpdateRec :: (Ord mloc,Ord ptr,Show mloc,Show ptr) => RiverMemory mloc ptr -> Update mloc ptr -> SMT (RiverMemory mloc ptr)
applyUpdateRec mem upd
  | isNoUpdate upd = return mem
  | otherwise = do
    let mem1 = applyUpdate mem upd
    (upd1,errs) <- foldlM (\(cupd,cerrs) (cond,i) -> do
                              (nupd,nerrs) <- updateInstruction mem1 upd cond i
                              return (mappend cupd nupd,nerrs++cerrs)
                          ) (noUpdate,[]) (riverProgram mem1)
    let upd2 = propagateUpdate (mem1 { riverErrors = errs++(riverErrors mem1) }) upd1
    applyUpdateRec mem1 (mappend upd1 upd2)

updateFromLoc :: Ord mloc => RiverMemory mloc ptr -> mloc -> Update mloc ptr
updateFromLoc mem loc = case Map.lookup loc (riverLocations mem) of
  Just locInfo -> noUpdate { newObjects = Map.singleton loc (riverObjects locInfo) }

updateFromPtr :: Ord ptr => RiverMemory mloc ptr -> ptr -> Update mloc ptr
updateFromPtr mem ptr = case Map.lookup ptr (riverPointers mem) of
  Just ptrInfo -> noUpdate { newPtrReachability = Map.singleton ptr (pointerReachability ptrInfo) }

insertIfNotPresent :: Ord k => k -> a -> Map k a -> Map k a
insertIfNotPresent key entr = Map.alter (\cur -> case cur of
                                            Nothing -> Just entr
                                            Just c -> Just c) key

addError :: ErrorDesc -> SMTExpr Bool -> RiverMemory mloc ptr -> RiverMemory mloc ptr
addError err cond mem = mem { riverErrors = (err,cond):riverErrors mem }

{-
mergeLocation :: SMTExpr Bool -> RiverLocation -> RiverLocation -> SMT (RiverLocation,Map RiverObjectRef RiverReachability)
mergeLocation cond src trg = do
  mp <- sequence $
        Map.mergeWithKey (\_ obj1 obj2 -> Just $ do
                             -- An object which already exists in the target location.
                             -- Make the target object equal to the source object:
                             assert $ cond .=>. (objectEq (objectRepresentation obj1) (objectRepresentation obj2))
                             -- Calculate the merged reachability, and the difference:
                             let (merge,diff) = mergeReachability (objectReachability obj1) (objectReachability obj2)
                             return (obj2 { objectReachability = merge },Just diff)
                         )
        (fmap (\obj -> do
                  nobj <- objectSkel (objectRepresentation obj)
                  assert $ cond .=>. (objectEq (objectRepresentation obj) nobj)
                  return (obj,Nothing))) (fmap (\obj -> return (obj,Nothing))) (riverObjects src) (riverObjects trg)
  let nloc = fmap fst mp
      diffs = Map.mapMaybe (\(_,diff) -> diff) mp
  return (RiverLocation nloc,diffs)
  
locationITE :: SMTExpr Bool -> RiverLocation -> RiverLocation -> RiverLocation
locationITE c loc1 loc2 = RiverLocation { riverObjects = Map.unionWith (\inf1 inf2 -> if inf1==inf2
                                                                                      then inf1
                                                                                      else ObjectInfo { objectRepresentation = objectITE c (objectRepresentation inf1) (objectRepresentation inf2)
                                                                                                      , objectReachability = fst $ mergeReachability (objectReachability inf1) (objectReachability inf2)
                                                                                                      }
                                                                       ) (riverObjects loc1) (riverObjects loc2)
                                        }-}

offsetAdd :: Offset -> Offset -> Offset
offsetAdd off1 off2 = Offset { staticOffset = (staticOffset off1) + (staticOffset off2)
                             , dynamicOffset = case dynamicOffset off1 of
                                  Nothing -> dynamicOffset off2
                                  Just d1 -> case dynamicOffset off2 of
                                    Nothing -> Just d1
                                    Just d2 -> Just $ bvadd d1 d2
                             }

buildOffset :: Integer -> Map String [TypeDesc] -> TypeDesc -> [DynNum] -> Offset
buildOffset ptrWidth structs tp (i:is)
  = let offRest = buildOffset' tp is
        off = case i of
          Left i' -> Offset { staticOffset = i'*(typeWidth ptrWidth structs tp)
                            , dynamicOffset = Nothing }
          Right i' -> Offset { staticOffset = 0
                             , dynamicOffset = Just $ bvmul i' (constantAnn (BitVector $ typeWidth ptrWidth structs tp) (extractAnnotation i'))
                             }
    in offsetAdd off offRest
  where
    buildOffset' _ [] = Offset { staticOffset = 0
                               , dynamicOffset = Nothing }
    buildOffset' tp (i:is) = let offRest = buildOffset' tp' is
                                 (off,tp') = case (tp,i) of
                                   (StructType n,Left i') -> let tps = case n of
                                                                   Left name -> structs!name
                                                                   Right tps' -> tps'
                                                                 (skip,tp:_) = genericSplitAt i' tps
                                                                 skipWidth = sum $ fmap (typeWidth ptrWidth structs) skip
                                                             in (Offset { staticOffset = skipWidth
                                                                        , dynamicOffset = Nothing },tp)
                                   (ArrayType _ tp,i) -> (case i of
                                                             Left i' -> Offset { staticOffset = i'*(typeWidth ptrWidth structs tp)
                                                                               , dynamicOffset = Nothing }
                                                             Right i' -> Offset { staticOffset = 0
                                                                                , dynamicOffset = Just $ bvmul i' (constantAnn (BitVector $ typeWidth ptrWidth structs tp) (extractAnnotation i'))
                                                                                },tp)
                             in offsetAdd off offRest

objRepr :: Integer -> RiverObjectRef -> SMTExpr (BitVector BVUntyped)
objRepr w (RiverObjectRef ref) = constantAnn (BitVector ref) (w*8)

offRepr :: Integer -> Integer -> Integer -> SMTExpr (BitVector BVUntyped)
offRepr ptrWidth ptrOffset off = constantAnn (BitVector off) ((ptrWidth - ptrOffset)*8)

newPointer :: Integer -> Integer -> TypeDesc -> SMT PointerInfo
newPointer width off tp = do
  p <- varNamedAnn "ptrObj" (off*8)
  o <- varNamedAnn "ptrOff" ((width-off)*8)
  return $ PointerInfo { pointerObject = p
                       , pointerOffset = o
                       , pointerReachability = Map.empty
                       , pointerType = tp }

getPointer :: Ord ptr => RiverMemory mloc ptr -> Map ptr TypeDesc -> ptr -> SMT (PointerInfo,RiverMemory mloc ptr)
getPointer mem mp ptr = case Map.lookup ptr (riverPointers mem) of
  Just info -> return (info,mem)
  Nothing -> do
    let Just tp = Map.lookup ptr mp
    info <- newPointer (riverPointerWidth mem) (riverPointerOffset mem) tp
    return (info,mem { riverPointers = Map.insert ptr info (riverPointers mem) })

getLocation :: Ord mloc => RiverMemory mloc ptr -> mloc -> RiverLocation -> (RiverLocation,RiverMemory mloc ptr)
getLocation mem loc def = case Map.lookup loc (riverLocations mem) of
  Just cont -> (cont,mem)
  Nothing -> (def,mem { riverLocations = Map.insert loc def (riverLocations mem) })

mkGlobal :: Integer -> Map String [TypeDesc] -> TypeDesc -> MemContent -> SMT RiverObject
mkGlobal pw structs tp (MemCell w v) = do
  obj <- defConstNamed "global" (constantAnn (BitVector v) w)
  return $ StaticObject tp obj
mkGlobal pw structs tp (MemArray els) = do
  let w = case els of
        (MemCell w _):_ -> w
      tp' = case tp of
        ArrayType _ t -> t
        VectorType _ t -> t
  arr <- varNamedAnn "global" (64,w)
  let obj = DynamicObject tp' arr (Left $ genericLength els)
      (obj',_) = foldl (\(cobj,idx) (MemCell w v) -> (fst $ storeObject pw structs (constant True) (constantAnn (BitVector v) w) cobj (Offset { staticOffset = idx
                                                                                                                                              , dynamicOffset = Nothing }),
                                                      idx+(w `div` 8))
                       ) (obj,0) els
  return obj'

offsetToExpr :: Integer -> Offset -> SMTExpr (BitVector BVUntyped)
offsetToExpr width off
  = case dynamicOffset off of
    Nothing -> constantAnn (BitVector $ staticOffset off) (width*8)
    Just dynOff -> let rwidth = extractAnnotation dynOff
                       dynOff' = case compare rwidth (width*8) of
                          EQ -> dynOff
                          LT -> bvconcat (constantAnn (BitVector 0) (width*8-rwidth) :: SMTExpr (BitVector BVUntyped)) dynOff
                          GT -> bvextract' 0 (width*8) dynOff
                    in if staticOffset off==0
                       then dynOff'
                       else bvadd (constantAnn (BitVector $ staticOffset off) (width*8)) dynOff'

compareOffsets :: Integer -> Offset -> Offset -> Either Bool (SMTExpr Bool)
compareOffsets width off1 off2 = case (dynamicOffset off1,dynamicOffset off2) of
  (Nothing,Nothing) -> Left $ (staticOffset off1) == (staticOffset off2)
  _ -> Right $ (offsetToExpr width off1) .==. (offsetToExpr width off2)

loadObject :: SMTExpr Bool -> Integer -> RiverObject -> Offset -> (Maybe (SMTExpr (BitVector BVUntyped)),[(ErrorDesc,SMTExpr Bool)])
loadObject act width (StaticObject _ obj) off = case dynamicOffset off of
  Nothing
    | objSize >= extractStart
      -> if staticOffset off==0 &&
            width == objSize `div` 8
         then (Just obj,[])
         else (Just $ bvextract' (objSize-extractStart) (width*8) obj,[])
    | otherwise -> (Nothing,[(Overrun,act)])
  where
    objSize = extractAnnotation obj
    extractStart = (staticOffset off+width)*8
loadObject act width (DynamicObject _ arr limit) off = case compare el_width (width*8) of
    EQ -> (Just $ select arr off',errs)
    LT -> (Just $ bvextract' 0 width (select arr off'),errs)
    GT -> let (num_els,rest) = width `divMod` el_width
          in (Just $ foldl1 bvconcat ([ select arr (off' `bvadd` (constantAnn (BitVector i) idx_width)) | i <- [0..(num_els-1)] ]++
                                      (if rest==0
                                       then []
                                       else [ bvextract' 0 rest ((select arr (offsetToExpr idx_width off)) `bvadd` (constantAnn (BitVector num_els) idx_width)) ])),errs)
  where
    (idx_width,el_width) = extractAnnotation arr
    elSize = el_width `div` 8
    byteOff = (offsetToExpr (idx_width `div` 8) off)
    off' = byteOff `bvudiv` (constantAnn (BitVector $ el_width `div` 8) idx_width)
    errs = checkLimits act elSize idx_width limit off

storeObject :: Integer -> Map String [TypeDesc] -> SMTExpr Bool -> SMTExpr (BitVector BVUntyped) -> RiverObject -> Offset -> (RiverObject,[(ErrorDesc,SMTExpr Bool)])
storeObject pw structs act word o@(StaticObject tp obj) off = case dynamicOffset off of
  Nothing
    | staticOffset off+size <= objSize
      -> (if staticOffset off==0
          then (if size==objSize
                then StaticObject tp word
                else StaticObject tp $ bvconcat word (bvextract' 0 ((objSize-size)*8) obj))
          else (if (staticOffset off)+size==objSize
                then StaticObject tp $ bvconcat (bvextract' (size*8) ((objSize-size)*8) obj) word
                else StaticObject tp $ bvconcat
                     (bvextract' ((objSize-staticOffset off)*8) ((staticOffset off)*8) obj)
                     (bvconcat word (bvextract' 0 ((objSize-(staticOffset off)-size)*8) obj))),[])
    | otherwise -> (StaticObject tp obj,[(Overrun,act)])
    where
      size = (extractAnnotation word) `div` 8
      objSize = (extractAnnotation obj) `div` 8
  Just _ -> let (nobj,errs) = storeObject pw structs act word (toDynObj pw structs o) off
            in (toStaticObj nobj,errs)
storeObject _ _ act word (DynamicObject tp arr limit) off = case compare el_width (extractAnnotation word) of
  EQ -> (DynamicObject tp (store arr off' word) limit,errs)
  _ -> error $ "Can't store object of size "++(show $ extractAnnotation word)++" to array with element size "++show el_width
  where
    (idx_width,el_width) = extractAnnotation arr
    off' = (offsetToExpr (idx_width `div` 8) off) `bvudiv` (constantAnn (BitVector $ el_width `div` 8) idx_width)
    errs = checkLimits act (el_width `div` 8) idx_width limit off

checkLimits :: SMTExpr Bool -> Integer -> Integer -> Either Integer (SMTExpr (BitVector BVUntyped)) -> Offset -> [(ErrorDesc,SMTExpr Bool)]
checkLimits act elSize idx_width limit off
  = case limit of
    Left sz -> case dynamicOffset off of
      Nothing -> (if sz > ((staticOffset off) `div` elSize)
                  then []
                  else [(Overrun,act)])++
                 (if (staticOffset off) < 0
                  then [(Underrun,act)]
                  else [])
      Just _ -> [(Overrun,act .&&. (bvsge off' limitExpr))
                ,(Underrun,act .&&. (bvslt off' (constantAnn (BitVector 0) idx_width)))]
    Right _ -> [(Overrun,act .&&. (bvsge off' limitExpr))
               ,(Underrun,act .&&. (bvslt off' (constantAnn (BitVector 0) idx_width)))]
  where
    byteOff = (offsetToExpr (idx_width `div` 8) off)
    off' = byteOff `bvudiv` (constantAnn (BitVector elSize) idx_width)
    limitExpr = case limit of
      Left limit' -> constantAnn (BitVector limit') idx_width
      Right limit' -> let limit_width = extractAnnotation limit'
                      in case compare idx_width limit_width of
                        EQ -> limit'
                        GT -> bvconcat (constantAnn (BitVector 0) (idx_width-limit_width) :: SMTExpr (BitVector BVUntyped)) limit'

simplifyObject :: RiverObject -> SMT RiverObject
simplifyObject (StaticObject tp obj) = do
  obj' <- simplify obj
  return (StaticObject tp obj')
simplifyObject (DynamicObject tp arr limit) = do
  arr' <- simplify arr
  limit' <- case limit of
    Left l -> return (Left l)
    Right l -> simplify l >>= return.Right
  return (DynamicObject tp arr' limit')

objectITE :: SMTExpr Bool -> RiverObject -> RiverObject -> RiverObject
objectITE cond (StaticObject tp w1) (StaticObject _ w2)
  = if w1==w2
    then StaticObject tp w1
    else StaticObject tp $ ite cond w1 w2
objectITE cond (DynamicObject tp arr1 limit1) (DynamicObject _ arr2 limit2)
  = DynamicObject tp narr nlimit
  where
    narr = if arr1==arr2
           then arr1
           else ite cond arr1 arr2
    nlimit = if limit1==limit2
             then limit1
             else Right (ite cond (dynNumExpr 64 limit1) (dynNumExpr 64 limit2))

objectEq :: RiverObject -> RiverObject -> SMTExpr Bool
objectEq (StaticObject _ w1) (StaticObject _ w2) = w1 .==. w2
objectEq (DynamicObject _ arr1 _) (DynamicObject _ arr2 _) = arr1 .==. arr2

objectSkel :: RiverObject -> SMT RiverObject
objectSkel (StaticObject tp w) = do
  v <- varAnn (extractAnnotation w)
  return (StaticObject tp v)
objectSkel (DynamicObject tp arr limit) = do
  arr' <- varAnn (extractAnnotation arr)
  limit' <- varAnn 64
  return $ DynamicObject tp arr' (Right limit')

toDynObj :: Integer -> Map String [TypeDesc] -> RiverObject -> RiverObject
toDynObj pw structs (StaticObject tp w) = case tp of
  ArrayType sz tp' -> let elSize = typeWidth pw structs tp'
                          arr = foldl (\arr idx -> store arr (constantAnn (BitVector idx) 64) (bvextract' (idx*elSize*8) (elSize*8) w)
                                      ) (constArray (constantAnn (BitVector 0) (elSize*8)) 64) [0..(sz-1)]
                          limit = Left sz
                      in DynamicObject tp' arr limit
toDynObj _ _ obj = obj

toStaticObj :: RiverObject -> RiverObject
toStaticObj (DynamicObject tp arr (Left sz))
  = let (idxWidth,elWidth) = extractAnnotation arr
        tp' = ArrayType sz tp
        word = foldl1 bvconcat [ select arr (constantAnn (BitVector idx) idxWidth) | idx <- [0..(sz-1)] ]
    in StaticObject tp' word
toStaticObj obj = obj

debugRiver :: (Show mloc,Show ptr) => RiverMemory mloc ptr -> String
debugRiver mem
  = unlines $
    ("Pointers:":
     [ "  "++show ptr++" ~> "++show (pointerObject info,pointerOffset info)++" "
       ++ showReach (pointerReachability info)
     | (ptr,info) <- Map.toList (riverPointers mem) ]) ++
    ("Locations:":
     concat [ ("  "++show loc++":"):
              [ "    "++show obj++" ~> "++show (objectRepresentation objInfo)++" "++showReach (objectReachability objInfo)
              | (RiverObjectRef obj,objInfo) <- Map.toList $ riverObjects info ]
            | (loc,info) <- Map.toList $ riverLocations mem ])
  where
    showReach reach = "{"++ unwords [ "("++show obj++" "++(case reachObjs of
                                                              Nothing -> "dyn"
                                                              Just set -> show (Set.toList set))++")"
                                    | (RiverObjectRef obj,reachObjs) <- Map.toList reach ]++"}"

simplifyRiver :: RiverMemory mloc ptr -> SMT (RiverMemory mloc ptr)
simplifyRiver mem = do
  nlocs <- mapM (\loc -> do
                    nobjs <- mapM (\objInfo -> do
                                      nrep <- simplifyObject (objectRepresentation objInfo)
                                      return $ objInfo { objectRepresentation = nrep }
                                  ) (riverObjects loc)
                    return $ RiverLocation nobjs
                ) (riverLocations mem)
  nptrs <- mapM (\info -> do
                    nobj <- simplify (pointerObject info)
                    noff <- simplify (pointerOffset info)
                    return $ info { pointerObject = nobj
                                  , pointerOffset = noff }
                ) (riverPointers mem)
  return $ mem { riverLocations = nlocs
               , riverPointers = nptrs }
