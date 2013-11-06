{-# LANGUAGE MultiParamTypeClasses #-}
module MemoryModel.Rivers where

import Data.Map.Strict (Map,(!))
import qualified Data.Map.Strict as Map
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
import MemoryModel.MemoryGraph
import TypeDesc
import SMTHelper

import Debug.Trace

data RiverMemory mloc ptr
  = RiverMemory { riverPointerWidth :: Integer
                , riverPointerOffset :: Integer
                , riverPointers :: Map ptr PointerInfo
                , riverNextObject :: RiverObjectRef
                , riverObjectTypes :: Map RiverObjectRef (TypeDesc,DynNum)
                , riverLocations :: Map mloc RiverLocation
                , riverGlobals :: RiverLocation
                , riverProgram :: MemoryGraph mloc ptr
                , riverConnections :: Map mloc (Set mloc)
                , riverPointerConnections :: Map ptr (Set ptr)
                , riverStructs :: Map String [TypeDesc]
                , riverErrors :: [(ErrorDesc,SMTExpr Bool)]
                }

newtype RiverObjectRef = RiverObjectRef Integer deriving (Eq,Ord,Enum)

instance Show RiverObjectRef where
  show (RiverObjectRef i) = "%"++show i

type RiverReachability = Map RiverObjectRef (Maybe (Set Integer))

data RiverLocation = RiverLocation { riverObjects :: Map RiverObjectRef ObjectInfo } deriving Show

data PointerInfo = PointerInfo { pointerObject :: SMTExpr (BitVector BVUntyped)
                               , pointerOffset :: SMTExpr (BitVector BVUntyped)
                               , pointerReachability :: RiverReachability
                               , pointerType :: TypeDesc
                               }

data ObjectInfo = ObjectInfo { objectRepresentation :: !RiverObject
                             , objectReachability :: !RiverReachability
                             } deriving (Show,Eq)

data Offset = Offset { staticOffset :: Integer
                     , dynamicOffset :: Maybe (SMTExpr (BitVector BVUntyped))
                     } deriving Show

data RiverObject = StaticObject TypeDesc [SMTExpr (BitVector BVUntyped)]
                 | DynamicObject TypeDesc (SMTExpr (SMTArray (SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped)))
                   (Either Integer (SMTExpr (BitVector BVUntyped)))
                 deriving (Show,Eq)

nullObj :: RiverObjectRef
nullObj = RiverObjectRef 0

instance (Ord ptr,Ord mloc,Show ptr,Show mloc) => MemoryModel (RiverMemory mloc ptr) mloc ptr where
  memNew prx ptrWidth allTps structs globals = do
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
    gr <- memNew prx ptrWidth allTps structs globals
    return $ RiverMemory { riverPointerWidth = ptrWidth
                         , riverPointerOffset = ptrOffset
                         , riverPointers = ptrs
                         , riverNextObject = RiverObjectRef next
                         , riverObjectTypes = Map.empty
                         , riverLocations = Map.empty
                         , riverGlobals = globs
                         , riverProgram = gr
                         , riverConnections = Map.empty
                         , riverPointerConnections = Map.empty
                         , riverStructs = structs
                         , riverErrors = []
                         }
  makeEntry _ mem loc = return $ mem { riverLocations = Map.insert loc (riverGlobals mem) (riverLocations mem) }
  addProgram mem cond prev is ptrs = do
    --trace ("Add program: "++show is) (return ())
    let is' = fmap (\i -> (cond,i)) is
    gr' <- addProgram (riverProgram mem) cond prev is ptrs
    addInstructions ptrs (mem { riverProgram = gr' }) is' {->>= simplifyRiver-}
  connectLocation mem prx cond locFrom locTo = do
    --trace ("Connect location: "++show cond++" "++show locFrom++" ~> "++show locTo) (return ())
    nprog <- connectLocation (riverProgram mem) prx cond locFrom locTo
    let mem1 = mem { riverLocations = insertIfNotPresent locFrom (RiverLocation Map.empty) $
                                      insertIfNotPresent locTo (RiverLocation Map.empty) $
                                      riverLocations mem
                   , riverConnections = Map.insertWith Set.union locFrom (Set.singleton locTo) (riverConnections mem)
                   , riverProgram = nprog
                   }
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
  connectPointer mem prx cond ptrSrc ptrTrg = do
    --trace ("Connect pointer: "++show cond++" "++show ptrSrc++" ~> "++show ptrTrg) (return ())
    nprog <- connectPointer (riverProgram mem) prx cond ptrSrc ptrTrg
    let mem0 = mem { riverProgram = nprog }
        Just ptrSrc' = Map.lookup ptrSrc (riverPointers mem0)
    (ptrTrg',mem1) <- case Map.lookup ptrTrg (riverPointers mem0) of
      Nothing -> do
        info <- newPointer (riverPointerWidth mem0) (riverPointerOffset mem0) (pointerType ptrSrc')
        return (info,mem0 { riverPointers = Map.insert ptrTrg info (riverPointers mem0) })
      Just info -> return (info,mem0)
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

data Update mloc ptr
  = Update { newPtrReachability :: Map ptr RiverReachability                       -- ^ New reachability information for pointers
           , newObjReachability :: Map mloc (Map RiverObjectRef RiverReachability) -- ^ New reachability information for objects
           , newObjects :: Map mloc (Map RiverObjectRef ObjectInfo)                -- ^ New reachable objects
           }

instance (Show mloc,Show ptr) => Show (Update mloc ptr) where
  show upd = "{"++(if Map.null (newPtrReachability upd)
                   then ""
                   else "Pointer reachability: ["++
                        (List.intercalate ", " [ "$"++show ptr++" ~> "++showReachability reach
                                               | (ptr,reach) <- Map.toList (newPtrReachability upd) ])
                        ++"] ")++
             (if Map.null (newObjReachability upd)
              then ""
              else "Object reachability: ["++
                   (List.intercalate ", " [ "@"++show loc++": ["++
                                            (List.intercalate ", " [ show objRef++" ~> "++showReachability reach
                                                                   | (objRef,reach) <- Map.toList locInfo ])++
                                            "]" | (loc,locInfo) <- Map.toList $ newObjReachability upd ])++"] ")++
             (if Map.null (newObjects upd)
              then ""
              else "New objects: ["++
                   (List.intercalate ", " [ "@"++show loc++": ["++
                                            (List.intercalate ", " [ show objRef++" ~> "++show info
                                                                   | (objRef,info) <- Map.toList locInfo ])++
                                            "]" | (loc,locInfo) <- Map.toList $ newObjects upd ])++
                   "]")++"}"

showReachability :: RiverReachability -> String
showReachability reach = "["++List.intercalate ", " [ show obj++(case off of
                                                                    Nothing -> "[all]"
                                                                    Just offs -> show (Set.toList offs))
                                                    | (obj,off) <- Map.toList reach ]++"]"

noUpdate :: Update mloc ptr
noUpdate = Update Map.empty Map.empty Map.empty

isNoUpdate :: (Ord mloc,Ord ptr) => Update mloc ptr -> Bool
isNoUpdate upd = Map.null (newPtrReachability upd) &&
                 Map.null (newObjReachability upd) &&
                 (all Map.null (newObjects upd))

instance (Ord ptr,Ord mloc) => Monoid (Update mloc ptr) where
  mempty = noUpdate
  mappend = mergeUpdates Nothing

mergeUpdates :: (Ord ptr,Ord mloc) => Maybe (SMTExpr Bool) -> Update mloc ptr -> Update mloc ptr -> Update mloc ptr
mergeUpdates cond u1 u2
  = Update { newPtrReachability = Map.unionWith unionReachability (newPtrReachability u1) (newPtrReachability u2)
           , newObjReachability = Map.unionWith (Map.unionWith unionReachability) (newObjReachability u1) (newObjReachability u2)
           , newObjects = case cond of
                Nothing -> Map.unionWith Map.union (newObjects u1) (newObjects u2)
                Just cond' -> Map.unionWith (Map.unionWith (\o1 o2
                                                            -> ObjectInfo { objectRepresentation = objectITE cond' (objectRepresentation o1)
                                                                                                   (objectRepresentation o2)
                                                                          , objectReachability = unionReachability (objectReachability o1)
                                                                                                 (objectReachability o2)
                                                                          })) (newObjects u1) (newObjects u2)
           }

getObject :: Ord mloc => RiverMemory mloc ptr -> mloc -> RiverObjectRef -> SMT (ObjectInfo,RiverMemory mloc ptr)
getObject mem loc ref = case Map.lookup ref (riverObjectTypes mem) of
  Just (tp,sz) -> case Map.lookup loc (riverLocations mem) of
    Nothing -> do
      obj <- allocateObject mem "obj" tp sz
      let info = ObjectInfo { objectRepresentation = obj
                            , objectReachability = Map.empty }
      return (info,mem { riverLocations = Map.insert loc
                                          (RiverLocation $ Map.singleton ref info)
                                          (riverLocations mem) })
    Just objs -> case Map.lookup ref (riverObjects objs) of
      Nothing -> do
        obj <- allocateObject mem "obj" tp sz
        let info = ObjectInfo { objectRepresentation = obj
                              , objectReachability = Map.empty }
        return (info,mem { riverLocations = Map.insert loc (objs { riverObjects = Map.insert ref info
                                                                                  (riverObjects objs) })
                                            (riverLocations mem)
                         })
      Just obj -> return (obj,mem)

unionReachability :: RiverReachability -> RiverReachability -> RiverReachability
unionReachability = Map.unionWith (\reach1 reach2 -> case (reach1,reach2) of
                                      (Just r1,Just r2) -> Just (Set.union r1 r2)
                                      _ -> Nothing)

updateInstruction :: (Ord mloc,Ord ptr) => Update mloc ptr -> RiverMemory mloc ptr -> SMT (Update mloc ptr,[(ErrorDesc,SMTExpr Bool)])
updateInstruction upd mem = do
  let allocObjReachMp = Map.intersectionWith
                        (\allocs nreach
                         -> Map.foldlWithKey'
                            (\cupd mto _ -> Map.insert mto nreach cupd)
                            Map.empty allocs
                        ) (allocsBySrcLoc $ riverProgram mem)
                        (newObjReachability upd)
      allocNewObjsMp = Map.intersectionWith
                       (\allocs nobjs
                         -> Map.foldlWithKey'
                            (\cupd mto _ -> Map.insert mto nobjs cupd)
                            Map.empty allocs
                       ) (allocsBySrcLoc $ riverProgram mem)
                       (newObjects upd)
      allocUpds = noUpdate { newObjReachability = Map.foldl' Map.union Map.empty allocObjReachMp
                           , newObjects = Map.foldl' Map.union Map.empty allocNewObjsMp
                           }
  loadErrs
    <- sequence $ Map.intersectionWithKey
       (\ptr loads nreach -> do
           let Just ptrInfo = Map.lookup ptr (riverPointers mem)
           errs <- sequence $ Map.mapWithKey (\mfrom (res,act) -> do
                                                 let Just locInfo = Map.lookup mfrom (riverLocations mem)
                                                 updateLoad ptrInfo locInfo res act nreach
                                             ) loads
           return $ concat errs
       ) (loadsBySrcPtr $ riverProgram mem) (newPtrReachability upd)
  let loadErrs' = foldl' (++) [] loadErrs
  loadPtrMp
    <- sequence $ Map.intersectionWithKey
       (\ptrSrc loads nreach -> do
           let Just ptrFromInfo = Map.lookup ptrSrc (riverPointers mem)
           Map.foldlWithKey'
             (\cur mfrom (ptrTrg,act) -> do
                 (cupd,cerrs) <- cur
                 let Just ptrToInfo = Map.lookup ptrTrg (riverPointers mem)
                     Just locInfo = Map.lookup mfrom (riverLocations mem)
                 (nreach',errs) <- updatePtrLoad ptrFromInfo locInfo ptrToInfo act nreach
                 return (Map.insert ptrTrg nreach' cupd,errs++cerrs)
             ) (return (Map.empty,[])) loads
       ) (ptrLoadsBySrcPtr $ riverProgram mem) (newPtrReachability upd)
  let (loadPtrUpds,loadPtrErrs) = Map.foldl' (\(cups,cerrs) (nups,nerrs)
                                              -> (Map.unionWith unionReachability cups nups,
                                                  nerrs++cerrs)
                                             ) (Map.empty,[]) loadPtrMp
      storeMp = Map.intersectionWithKey
                (\ptrTrg stores nreach
                 -> let Just ptrTrgInfo = Map.lookup ptrTrg (riverPointers mem)
                    in Map.foldlWithKey'
                       (\(cupd,errs) (mfrom,mto) (bv,act)
                        -> let Just locFrom = Map.lookup mfrom (riverLocations mem)
                               newObjs1 = Map.findWithDefault Map.empty mfrom (newObjects upd)
                               (newObjs2,nerrs) = updateStore bv locFrom ptrTrgInfo act nreach
                           in (Map.insert mto (Map.union newObjs2 newObjs1) cupd,nerrs++errs)
                       ) (Map.empty,[]) stores
                ) (storesByTrgPtr $ riverProgram mem) (newPtrReachability upd)
      (storeUpds,storeErrs) = Map.foldl' (\(cupd,cerr) (nupd,nerr) -> (Map.union cupd nupd,nerr++cerr)
                                         ) (Map.empty,[]) storeMp
      ptrStoreMp = Map.intersectionWithKey
                   (\ptrTrg stores nreach
                    -> let Just ptrTrgInfo = Map.lookup ptrTrg (riverPointers mem)
                       in Map.foldlWithKey'
                          (\(cupd,errs) (mfrom,mto) (ptrSrc,act)
                           -> let Just ptrSrcInfo = Map.lookup ptrSrc (riverPointers mem)
                                  Just locFrom = Map.lookup mfrom (riverLocations mem)
                                  bv = bvconcat (pointerObject ptrSrcInfo) (pointerOffset ptrSrcInfo)
                                  newObjs1 = Map.findWithDefault Map.empty mfrom (newObjects upd)
                                  (newObjs2,nerrs) = updateStore bv locFrom ptrTrgInfo act nreach
                              in (Map.insert mto (Map.union newObjs2 newObjs1) cupd,nerrs++errs)
                          ) (Map.empty,[]) stores
                   ) (ptrStoresByTrgPtr $ riverProgram mem) (newPtrReachability upd)
      (ptrStoreUpds,ptrStoreErrs) = Map.foldl' (\(cupd,cerr) (nupd,nerr) -> (Map.union cupd nupd,nerr++cerr)
                                               ) (Map.empty,[]) ptrStoreMp
      noStoreUpds = Map.foldl' (Map.foldlWithKey'
                                (\cupd (mfrom,mto) _ -> case Map.lookup mfrom (newObjects upd) of
                                    Nothing -> cupd
                                    Just nobjs -> Map.insert mto nobjs cupd
                                )
                               ) Map.empty $
                    Map.difference (storesByTrgPtr $ riverProgram mem) (newPtrReachability upd)
      noPtrStoreUpds = Map.foldl' (Map.foldlWithKey'
                                   (\cupd (mfrom,mto) _ -> case Map.lookup mfrom (newObjects upd) of
                                       Nothing -> cupd
                                       Just nobjs -> Map.insert mto nobjs cupd
                                   )
                                  ) Map.empty $
                       Map.difference (ptrStoresByTrgPtr $ riverProgram mem) (newPtrReachability upd)
      newObjReachStoreMp = Map.intersectionWithKey
                           (\ptrSrc stores nreach
                            -> let Just ptrSrcInfo = Map.lookup ptrSrc (riverPointers mem)
                               in Map.foldlWithKey'
                                  (\cupd (mfrom,mto) (ptrTrg,act)
                                   -> let Just ptrTrgInfo = Map.lookup ptrTrg (riverPointers mem)
                                      in Map.insert mto (fmap (const nreach) (pointerReachability ptrTrgInfo)) cupd
                                  ) Map.empty stores
                           ) (ptrStoresBySrcPtr $ riverProgram mem)
                           (newPtrReachability upd)
      newObjReachStore = Map.foldl' Map.union Map.empty newObjReachStoreMp
      newPtrReachLoadsMp = Map.intersectionWithKey
                           (\mfrom loads nreach
                             -> foldl' (\cupd (src,trg,act)
                                        -> let Just srcInfo = Map.lookup src (riverPointers mem)
                                               nreach' = Map.foldlWithKey'
                                                         (\cupd' reachObj _
                                                          -> case Map.lookup reachObj nreach of
                                                            Nothing -> cupd'
                                                            Just nreach' -> unionReachability cupd' nreach'
                                                         ) Map.empty (pointerReachability srcInfo)
                                           in if Map.null nreach'
                                              then cupd
                                              else Map.insertWith unionReachability trg nreach' cupd
                                      ) Map.empty loads
                           ) (ptrLoadsBySrcLoc $ riverProgram mem) (newObjReachability upd)
      newPtrReachLoads = Map.foldl' (Map.unionWith unionReachability) Map.empty newPtrReachLoadsMp
      newPtrReachSelect = Map.foldl' (Map.unionWith unionReachability) Map.empty $
                          Map.intersectionWith
                          (\trgs nreach
                           -> Map.foldlWithKey' (\cupd pto _ -> Map.insertWith unionReachability pto nreach cupd
                                                ) Map.empty trgs
                          ) (ptrPhisBySrc $ riverProgram mem) (newPtrReachability upd)
      newPtrReachCast = Map.foldl' (Map.unionWith unionReachability) Map.empty $
                        Map.intersectionWith
                        (\trgs nreach
                          -> Map.foldlWithKey' (\cupd pto _ -> Map.insertWith unionReachability pto nreach cupd
                                               ) Map.empty trgs
                        ) (ptrCastsBySrc $ riverProgram mem) (newPtrReachability upd)
      newPtrReachIdx = Map.foldl' (Map.unionWith unionReachability) Map.empty $
                       Map.intersectionWith
                       (\trgs nreach
                        -> Map.foldlWithKey' (\cupd pto (tpFrom,tpTo,idx)
                                              -> let off = buildOffset (riverPointerWidth mem) (riverStructs mem) tpFrom idx
                                                     nreach' = fmap (\reach' -> case reach' of
                                                                        Nothing -> Nothing
                                                                        Just offs -> case dynamicOffset off of
                                                                          Nothing -> Just $ Set.map (\soff -> soff + (staticOffset off)) offs
                                                                          Just _ -> Nothing) nreach
                                                 in Map.insertWith unionReachability pto nreach' cupd
                                             ) Map.empty trgs
                       ) (ptrIdxBySrc $ riverProgram mem) (newPtrReachability upd)
      newObjsPhi = fmap snd $
                   foldl' (Map.unionWith
                           (\(_,cur) (c,new) -> (c,Map.unionWith (\oldInfo newInfo
                                                                  -> ObjectInfo { objectRepresentation = objectITE c
                                                                                                         (objectRepresentation newInfo)
                                                                                                         (objectRepresentation oldInfo)
                                                                                , objectReachability = unionReachability
                                                                                                       (objectReachability newInfo)
                                                                                                       (objectReachability oldInfo)
                                                                                }) cur new
                           )))
                   Map.empty $
                   Map.intersectionWith
                   (\trgs nobjs
                    -> fmap (\c -> (c,nobjs)) trgs
                   ) (locPhisBySrc $ riverProgram mem) (newObjects upd)
      newObjReachPhi = foldl' Map.union Map.empty $
                       Map.intersectionWith
                       (\trgs nreach
                        -> fmap (const nreach) trgs
                       ) (locPhisBySrc $ riverProgram mem) (newObjReachability upd)
  return (allocUpds `mappend`
          (noUpdate { newPtrReachability = loadPtrUpds }) `mappend`
          (noUpdate { newObjects = storeUpds }) `mappend`
          (noUpdate { newObjects = noStoreUpds }) `mappend`
          (noUpdate { newObjects = ptrStoreUpds }) `mappend`
          (noUpdate { newObjects = noPtrStoreUpds }) `mappend`
          (noUpdate { newObjReachability = newObjReachStore }) `mappend`
          (noUpdate { newPtrReachability = newPtrReachLoads }) `mappend`
          (noUpdate { newPtrReachability = newPtrReachSelect }) `mappend`
          (noUpdate { newPtrReachability = newPtrReachCast }) `mappend`
          (noUpdate { newPtrReachability = newPtrReachIdx }) `mappend`
          (noUpdate { newObjects = newObjsPhi }) `mappend`
          (noUpdate { newObjReachability = newObjReachPhi }),
          loadErrs'++loadPtrErrs++storeErrs++ptrStoreErrs)
  where
    updateMem :: (SMTExpr Bool -> ObjectInfo -> Offset -> (Maybe ObjectInfo,a,[(ErrorDesc,SMTExpr Bool)]))
                 -> PointerInfo -> RiverLocation -> SMTExpr Bool
                 -> RiverReachability -> (Map RiverObjectRef ObjectInfo,[a],[(ErrorDesc,SMTExpr Bool)])
    updateMem f ptrInfo locInfo act nreach
      = let (newObjs,res,errs)
              = Map.foldlWithKey'
                (\(objs,allRes,allErrs) objRef reach
                 -> let Just obj = Map.lookup objRef (riverObjects locInfo)
                    in case reach of
                      Nothing -> let off = Offset { staticOffset = 0
                                                  , dynamicOffset = Just $ pointerOffset ptrInfo
                                                  }
                                     cond = (pointerObject ptrInfo) .==. objRepr (riverPointerOffset mem) objRef
                                     (nobj,res,errs) = f (act .&&. cond) obj off
                                 in (case nobj of
                                        Nothing -> newObjs
                                        Just nobj' -> Map.insert objRef nobj' newObjs,
                                     res:allRes,
                                     errs++allErrs)
                      Just offs
                        -> let (nobj,ress,errs)
                                 = foldl' (\(cobj,res,cerrs) soff
                                           -> let off = Offset { staticOffset = soff
                                                               , dynamicOffset = Nothing }
                                                  cond = ((pointerObject ptrInfo) .==.
                                                          objRepr (riverPointerOffset mem) objRef) .&&.
                                                         ((pointerOffset ptrInfo) .==.
                                                          offRepr (riverPointerWidth mem)
                                                          (riverPointerOffset mem) soff)
                                                  (obj',res',errs') = f (act .&&. cond) obj off
                                                  nobj = case obj' of
                                                    Nothing -> cobj
                                                    Just o -> case cobj of
                                                      Nothing -> Just o
                                                      Just o' -> Just $ ObjectInfo { objectRepresentation = objectITE cond
                                                                                                            (objectRepresentation o)
                                                                                                            (objectRepresentation o')
                                                                                   , objectReachability = unionReachability
                                                                                                          (objectReachability o)
                                                                                                          (objectReachability o') }
                                              in (nobj,res':res,errs'++cerrs)
                                          ) (Nothing,[],[]) offs
                           in (case nobj of
                                  Nothing -> objs
                                  Just nobj' -> Map.insert objRef nobj' objs,
                               ress++allRes,
                               errs++allErrs)
                ) (Map.empty,[],[]) (Map.delete nullObj nreach)
            nullError = if Map.member nullObj nreach
                        then [(NullDeref,act .&&. ((pointerObject ptrInfo) .==.
                                                   objRepr (riverPointerOffset mem) nullObj))]
                        else []
        in (newObjs,res,nullError++errs)
    updateLoad :: PointerInfo -> RiverLocation -> SMTExpr (BitVector BVUntyped) -> SMTExpr Bool
                  -> RiverReachability -> SMT [(ErrorDesc,SMTExpr Bool)]
    updateLoad ptrInfo locInfo res act nreach = do
      let (_,loads,errs) = updateMem (\cond obj off
                                       -> let (loadRes,errs) = loadObject cond ((extractAnnotation res) `div` 8) (objectRepresentation obj) off
                                              action = case loadRes of
                                                Nothing -> return ()
                                                Just loadRes' -> assert $ cond .=>. (res .==. loadRes')
                                          in (Nothing,action,errs)
                                     ) ptrInfo locInfo act nreach
      sequence loads
      return errs
    updatePtrLoad :: PointerInfo -> RiverLocation -> PointerInfo -> SMTExpr Bool
                     -> RiverReachability -> SMT (RiverReachability,[(ErrorDesc,SMTExpr Bool)])
    updatePtrLoad ptrFromInfo locInfo ptrToInfo act nreach = do
      let (_,loads,errs) = updateMem (\cond obj off
                                       -> let (loadRes,errs) = loadObject (act .&&. cond) (riverPointerWidth mem)
                                                               (objectRepresentation obj) off
                                              action = case loadRes of
                                                Nothing -> return ()
                                                Just loadRes' -> assert $ cond .=>. ((bvconcat (pointerObject ptrToInfo)
                                                                                      (pointerOffset ptrToInfo)) .==. loadRes')
                                          in (Nothing,(action,objectReachability obj),errs)
                                     ) ptrFromInfo locInfo act nreach
      sequence $ fmap fst loads
      return (foldl unionReachability Map.empty $ fmap snd loads,errs)
    updateStore :: SMTExpr (BitVector BVUntyped) -> RiverLocation -> PointerInfo -> SMTExpr Bool
                   -> RiverReachability -> (Map RiverObjectRef ObjectInfo,[(ErrorDesc,SMTExpr Bool)])
    updateStore word locFrom ptr' act nreach
      = let (newObjs,_,errs) = updateMem (\cond obj off
                                          -> let (obj',errs') = storeObject
                                                                (riverPointerWidth mem)
                                                                (riverStructs mem)
                                                                cond word (objectRepresentation obj) off
                                             in (Just $ obj { objectRepresentation = obj' },(),errs')
                                         ) ptr' locFrom act nreach
        in (newObjs,errs)

applyUpdate :: (Ord mloc,Ord ptr,Show mloc,Show ptr) => RiverMemory mloc ptr -> Update mloc ptr -> RiverMemory mloc ptr
applyUpdate mem upd
  = let mem1 = Map.foldlWithKey' (\cmem loc newObjs
                                  -> cmem { riverLocations = Map.adjust (\(RiverLocation locInfo)
                                                                         -> RiverLocation $
                                                                            Map.union locInfo newObjs
                                                                        ) loc (riverLocations cmem)
                                          }) mem (newObjects upd)
        mem2 = Map.foldlWithKey' (\cmem ptr nreach -> cmem { riverPointers = Map.adjust (\info -> info { pointerReachability = unionReachability (pointerReachability info) nreach
                                                                                                       }) ptr (riverPointers cmem) }
                                 ) mem1 (newPtrReachability upd)
        mem3 = Map.foldlWithKey' (\cmem loc objReaches
                                  -> cmem { riverLocations = Map.adjust (\(RiverLocation locInfo)
                                                                         -> RiverLocation $
                                                                            Map.differenceWith
                                                                            (\objInfo nreach -> Just $ objInfo { objectReachability = unionReachability (objectReachability objInfo) nreach
                                                                                                              }
                                                                            ) locInfo objReaches
                                                                        ) loc (riverLocations cmem) }
                                 ) mem2 (newObjReachability upd)
    in mem3

restrictUpdate :: (Ord mloc,Ord ptr,Show mloc,Show ptr) => RiverMemory mloc ptr -> Update mloc ptr -> Update mloc ptr
restrictUpdate mem upd
  = Update { newPtrReachability = Map.differenceWith
                                  (\reach info -> let nreach = Map.differenceWith
                                                               reachDiff
                                                               reach (pointerReachability info)
                                                  in if Map.null nreach
                                                     then Nothing
                                                     else Just nreach
                                  ) (newPtrReachability upd) (riverPointers mem)
           , newObjReachability = Map.differenceWith
                                  (\objReach (RiverLocation loc)
                                   -> let nobjReach = Map.differenceWith
                                                      (\reachNew info
                                                       -> let nreach = Map.differenceWith reachDiff
                                                                       reachNew (objectReachability info)
                                                          in if Map.null nreach
                                                             then Nothing
                                                             else Just nreach)
                                                      objReach loc
                                      in if Map.null nobjReach
                                         then Nothing
                                         else Just nobjReach
                                  ) (newObjReachability upd) (riverLocations mem)
           , newObjects = newObjects upd }
  where
    reachDiff reachNew reachOld = case reachOld of
      Nothing -> Nothing
      Just offsOld -> case reachNew of
        Nothing -> Just Nothing
        Just offsNew -> let offsDiff = Set.difference offsNew offsOld
                        in if Set.null offsDiff
                           then Nothing
                           else Just (Just offsDiff)

allocateObject :: RiverMemory mloc ptr -> String -> TypeDesc -> DynNum -> SMT RiverObject
allocateObject mem name tp sz = case sz of
  Left 1 -> do
    v <- allocaSimple tp
    return $ StaticObject tp v
  Right sz -> do
    v <- varNamedAnn name (64,bitWidth ((riverPointerWidth mem)*8) (riverStructs mem) tp)
    return $ DynamicObject tp v (Right sz)
  where
    allocaSimple (StructType descr) = do
      let tps = case descr of
            Left name -> (riverStructs mem)!name
            Right tps' -> tps'
      res <- mapM allocaSimple tps
      return $ concat res
    allocaSimple (ArrayType sz tp) = do
      res <- sequence $ List.genericReplicate sz (allocaSimple tp)
      return $ concat res
    allocaSimple tp = do
      v <- varNamedAnn name (bitWidth ((riverPointerWidth mem)*8) (riverStructs mem) tp)
      return [v]

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
  newObj <- allocateObject mem "alloc" tp sz
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
                 , riverObjectTypes = Map.insert (riverNextObject mem) (tp,sz) (riverObjectTypes mem)
                 }
      upd = updateFromLoc mem1 mfrom
  (upd',errs) <- updateInstruction upd (mem1 { riverProgram = addInstruction act instr memGraphEmpty })
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
  (upd',errs) <- updateInstruction upd (mem2 { riverProgram = addInstruction act instr memGraphEmpty })
  return (mem2 { riverErrors = errs++(riverErrors mem2) },upd')
initUpdate ptrs mem act instr@(MILoadPtr mfrom ptrFrom ptrTo) = do
  (_,mem1) <- getPointer mem ptrs ptrFrom
  (ptrInfo,mem2) <- getPointer mem1 ptrs ptrTo
  let mem3 = mem2 { riverLocations = insertIfNotPresent mfrom (RiverLocation Map.empty)
                                     (riverLocations mem2) }
      upd1 = updateFromPtr mem3 ptrFrom
      upd2 = updateFromPtr mem3 ptrTo
  (upd3,errs) <- updateInstruction (mappend upd1 upd2) (mem3 { riverProgram = addInstruction act instr memGraphEmpty })
  return (mem3 { riverErrors = errs++(riverErrors mem3) },upd3)
initUpdate ptrs mem act instr@(MIStore mfrom word ptr mto) = do
  (ptrInfo,mem1) <- getPointer mem ptrs ptr
  let mem2 = mem1 { riverLocations = insertIfNotPresent mfrom (RiverLocation Map.empty) $
                                     insertIfNotPresent mto (RiverLocation Map.empty) $
                                     riverLocations mem1
                  }
      upd1 = updateFromLoc mem2 mfrom
      upd2 = updateFromPtr mem2 ptr
  (upd3,errs) <- updateInstruction (mappend upd1 upd2) (mem2 { riverProgram = addInstruction act instr memGraphEmpty })
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
  (upd5,errs) <- updateInstruction upd4 (mem3 { riverProgram = addInstruction act instr memGraphEmpty })
  return (mem3 { riverErrors = errs++(riverErrors mem3) },upd5)
initUpdate ptrs mem _ (MICompare ptr1 ptr2 res) = do
  (info1,mem1) <- getPointer mem ptrs ptr1
  (info2,mem2) <- getPointer mem1 ptrs ptr2
  assert $ res .==. (((pointerObject info1) .==. (pointerObject info2)) .&&.
                     ((pointerOffset info1) .==. (pointerOffset info2)))
  return (mem2,noUpdate)
initUpdate ptrs mem act instr@(MISelect cases ptr) = do
  (obj',off',mem1,upd) <- buildCases mem cases
  let objOpt = optimizeExpr' obj'
      offOpt = optimizeExpr' off'
  obj <- if isComplexExpr objOpt
         then defConstNamed "ptrObj" objOpt
         else return objOpt
  off <- if isComplexExpr offOpt
         then defConstNamed "ptrOff" offOpt
         else return offOpt
  let mem2 = mem1 { riverPointers = Map.insert ptr (PointerInfo { pointerObject = obj
                                                                , pointerOffset = off
                                                                , pointerReachability = Map.empty
                                                                , pointerType = ptrs!ptr
                                                                }) (riverPointers mem1)
                  }
  (upd2,errs) <- updateInstruction upd (mem2 { riverProgram = addInstruction act instr memGraphEmpty })
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
  (upd',errs) <- updateInstruction upd (mem2 { riverProgram = addInstruction act instr memGraphEmpty })
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
  (upd',errs) <- updateInstruction upd (mem2 { riverProgram = addInstruction act instr memGraphEmpty })
  return (mem2 { riverErrors = errs++(riverErrors mem2) },upd')
initUpdate ptrs mem act instr@(MIPhi cases mto) = do
  let (mem1,upd) = buildCases (mem { riverLocations = insertIfNotPresent mto (RiverLocation Map.empty)
                                                      (riverLocations mem)
                                   }) cases
  (upd',errs) <- updateInstruction upd (mem1 { riverProgram = addInstruction act instr memGraphEmpty })
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
        in (cmem2,mergeUpdates (Just c) upd1 upd2)

applyUpdateRec :: (Ord mloc,Ord ptr,Show mloc,Show ptr) => RiverMemory mloc ptr -> Update mloc ptr -> SMT (RiverMemory mloc ptr)
applyUpdateRec mem upd
  | isNoUpdate upd' = return mem
  | otherwise = do
    let mem1 = applyUpdate mem upd'
    (upd1,errs) <- updateInstruction upd' mem1
    let mem2 = mem1 { riverErrors = errs++(riverErrors mem1) }
    applyUpdateRec mem2 upd1
  where
    upd' = restrictUpdate mem upd

updateFromLoc :: Ord mloc => RiverMemory mloc ptr -> mloc -> Update mloc ptr
updateFromLoc mem loc = case Map.lookup loc (riverLocations mem) of
  Just locInfo -> noUpdate { newObjects = Map.singleton loc (riverObjects locInfo) }

updateFromPtr :: Ord ptr => RiverMemory mloc ptr -> ptr -> Update mloc ptr
updateFromPtr mem ptr = case Map.lookup ptr (riverPointers mem) of
  Just ptrInfo -> if Map.null (pointerReachability ptrInfo)
                  then noUpdate
                  else noUpdate { newPtrReachability = Map.singleton ptr (pointerReachability ptrInfo) }

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
  return $ StaticObject tp [obj]
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
  Nothing -> case extractWord (staticOffset off*8) (width*8) obj of
    Nothing -> (Nothing,[(Overrun,act)])
    Just [w] -> (Just w,[])
    Just ws -> (Just $ foldl1 bvconcat ws,[])
  where
    objSize = sum $ fmap extractAnnotation obj
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

extractWord :: Integer -> Integer -> [SMTExpr (BitVector BVUntyped)] -> Maybe [SMTExpr (BitVector BVUntyped)]
extractWord start len (w:ws)
  | start==0 && len == wlen = Just [w]
  | start >= wlen = extractWord (start-wlen) len ws
  | start+len <= wlen = Just [bvextract' start len w]
  | otherwise = case extractWord 0 (len-wlen) ws of
    Just ws' -> Just $ (bvextract' start (wlen-start) w):ws'
    Nothing -> Nothing
  where
    wlen = extractAnnotation w

storeWord :: Integer -> SMTExpr (BitVector BVUntyped) -> [SMTExpr (BitVector BVUntyped)] -> Maybe [SMTExpr (BitVector BVUntyped)]
storeWord start bv (w:ws)
  | start==0 && bvlen==wlen = Just $ bv:ws
  | start==0 && bvlen<=wlen = Just $ (bvconcat bv (bvextract' 0 (wlen-bvlen) w)):ws
  | start+bvlen<=wlen = Just $ (bvconcat (bvextract' (wlen-start) start w)
                                (bvconcat bv (bvextract' 0 (wlen-bvlen-start) w))):ws
  | start >= wlen = case storeWord (start-wlen) bv ws of
    Nothing -> Nothing
    Just ws' -> Just $ w:ws'
  where
    bvlen = extractAnnotation bv
    wlen = extractAnnotation w

storeObject :: Integer -> Map String [TypeDesc] -> SMTExpr Bool -> SMTExpr (BitVector BVUntyped) -> RiverObject -> Offset -> (RiverObject,[(ErrorDesc,SMTExpr Bool)])
storeObject pw structs act word o@(StaticObject tp obj) off = case dynamicOffset off of
  Nothing -> case storeWord (staticOffset off*8) word obj of
    Nothing -> (StaticObject tp obj,[(Overrun,act)])
    Just nobj -> (StaticObject tp nobj,[])
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
  obj' <- mapM simplify obj
  return (StaticObject tp obj')
simplifyObject (DynamicObject tp arr limit) = do
  arr' <- simplify arr
  limit' <- case limit of
    Left l -> return (Left l)
    Right l -> simplify l >>= return.Right
  return (DynamicObject tp arr' limit')

objectITE :: SMTExpr Bool -> RiverObject -> RiverObject -> RiverObject
objectITE cond (StaticObject tp w1) (StaticObject _ w2)
  = case ites w1 w2 of
  Just nobj -> StaticObject tp nobj
  Nothing -> StaticObject tp [ite cond (foldl1 bvconcat w1) (foldl1 bvconcat w2)]
  where
    ites [] [] = Just []
    ites (x:xs) (y:ys) = case ites xs ys of
      Nothing -> Nothing
      Just rest -> if extractAnnotation x == extractAnnotation y
                   then (if x==y
                         then Just $ x:rest
                         else Just $ (ite cond x y):rest)
                   else Nothing
    ites _ _ = Nothing
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
objectEq (StaticObject _ w1) (StaticObject _ w2) = case eqs w1 w2 of
  Nothing -> (foldl1 bvconcat w1) .==. (foldl1 bvconcat w2)
  Just res -> app and' res
  where
    eqs [x] [y] = if extractAnnotation x==extractAnnotation y
                  then Just [x .==. y]
                  else Nothing
    eqs (x:xs) (y:ys) = case eqs xs ys of
      Nothing -> Nothing
      Just rest -> Just $ (x .==. y):rest
    eqs _ _ = Nothing
objectEq (DynamicObject _ arr1 _) (DynamicObject _ arr2 _) = arr1 .==. arr2

objectSkel :: RiverObject -> SMT RiverObject
objectSkel (StaticObject tp ws) = do
  v <- mapM (\w -> varAnn (extractAnnotation w)) ws
  return (StaticObject tp v)
objectSkel (DynamicObject tp arr limit) = do
  arr' <- varAnn (extractAnnotation arr)
  limit' <- varAnn 64
  return $ DynamicObject tp arr' (Right limit')

toDynObj :: Integer -> Map String [TypeDesc] -> RiverObject -> RiverObject
toDynObj pw structs (StaticObject tp w) = case tp of
  ArrayType sz tp' -> case mkArr 0 w startArr of
    Nothing -> DynamicObject tp' arr limit
    Just arr -> DynamicObject tp' arr limit
    where
      elSize = typeWidth pw structs tp'
      concatWord = foldl1 bvconcat w
      startArr = constArray (constantAnn (BitVector 0) (elSize*8)) 64
      arr = foldl (\arr idx -> store arr (constantAnn (BitVector idx) 64) (bvextract' (idx*elSize*8) (elSize*8) concatWord)
                  ) startArr [0..(sz-1)]
      limit = Left sz
      mkArr idx [] arr = Just arr
      mkArr idx (w:ws) arr = case mkArr (idx+1) ws arr of
        Nothing -> Nothing
        Just arr' -> if extractAnnotation w==elSize*8
                     then Just $ store arr' (constantAnn (BitVector idx) 64) w
                     else Nothing
toDynObj _ _ obj = obj

toStaticObj :: RiverObject -> RiverObject
toStaticObj (DynamicObject tp arr (Left sz))
  = let (idxWidth,elWidth) = extractAnnotation arr
        tp' = ArrayType sz tp
        word = [ select arr (constantAnn (BitVector idx) idxWidth) | idx <- [0..(sz-1)] ]
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
