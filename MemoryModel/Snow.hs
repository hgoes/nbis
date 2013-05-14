{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses,GADTs,RankNTypes #-}
module MemoryModel.Snow where

import MemoryModel
import DecisionTree
import TypeDesc

import Language.SMTLib2
--import qualified Data.Graph.Inductive as Gr
import Data.Map as Map hiding (foldl)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable
import Data.Traversable
import Prelude hiding (foldl1,foldl,mapM_,concat,mapM)
import Data.Bits
import Control.Monad.Trans
import Data.Maybe (catMaybes)
import Data.Monoid
import Debug.Trace

import MemoryModel.Snow.Object

type BVPtr = BV64
type BVByte = BitVector BVUntyped

data SnowMemory mloc ptr
  = SnowMemory { snowStructs :: Map String [TypeDesc]
               , snowProgram :: MemoryProgram mloc ptr
               , snowGlobal :: SnowLocation ptr
               , snowLocations :: Map mloc (SnowLocation ptr)
               , snowPointerConnections :: Map ptr [(ptr,SMTExpr Bool)]
               , snowLocationConnections :: Map mloc [(mloc,SMTExpr Bool)]
               , snowNextObject :: Integer
               }

data AssignState a = AssignStatic a
                   | AssignDynamic [(SMTExpr Bool,a)]
                   deriving (Eq,Show)

data SnowLocation ptr
  = SnowLocation { snowObjects :: Map Integer (AssignState (Object ptr))
                 , snowPointer :: Map ptr (AssignState (Maybe (Integer,PtrIndex)))
                 }

mergeAssign :: (Eq a,Show a) => AssignState a -> AssignState a -> AssignState a
mergeAssign (AssignStatic x) (AssignStatic y) = if x==y
                                                then AssignStatic x
                                                else AssignStatic y --error $ "Static assignments differ ("++show x++" vs. "++show y++")"
mergeAssign (AssignDynamic x) (AssignDynamic y) = AssignDynamic (x++y)

assignList :: AssignState a -> [(SMTExpr Bool,a)]
assignList (AssignStatic x) = [(constant True,x)]
assignList (AssignDynamic xs) = xs

instance (Ord ptr,Show ptr) => Monoid (SnowLocation ptr) where
  mempty = SnowLocation { snowObjects = Map.empty
                        , snowPointer = Map.empty }
  mappend l1 l2 = SnowLocation { snowObjects = Map.unionWith mergeAssign (snowObjects l1) (snowObjects l2)
                               , snowPointer = Map.unionWith mergeAssign (snowPointer l1) (snowPointer l2)
                               }

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

instance (Ord mloc,Ord ptr,Show ptr,Show mloc) => MemoryModel (SnowMemory mloc ptr) mloc ptr where
  memNew _ _ structs globals = do
    (globs,next) <- foldlM (\(loc,next) (ptr,tp,cont) -> do
                               glob <- case cont of
                                 Just cont' -> mkGlobal cont'
                               return (loc { snowObjects = Map.insert next (AssignStatic glob) (snowObjects loc)
                                           , snowPointer = Map.insert ptr (AssignStatic (Just (next,[(tp,[])]))) (snowPointer loc)
                                           },succ next)
                           ) (SnowLocation Map.empty Map.empty,0) globals
    trace (unlines $ snowDebugLocation "globals" globs) $ return ()
    return $ SnowMemory { snowStructs = structs
                        , snowProgram = []
                        , snowLocations = Map.empty
                        , snowPointerConnections = Map.empty
                        , snowLocationConnections = Map.empty
                        , snowGlobal = globs
                        , snowNextObject = next
                        }
  addProgram mem act start_loc prog = do
    trace ("Adding program "++show start_loc++": "++show prog) $ return ()
    let mem' = mem { snowProgram = prog++(snowProgram mem) }
        (objs,ptrs) = case snowProgram mem of
          [] -> (snowObjects $ snowGlobal mem',snowPointer $ snowGlobal mem')
          _ -> (Map.empty,Map.empty)
    initLocation (snowStructs mem') start_loc objs ptrs mem'
  connectLocation mem cond loc_from loc_to ptrs = do
    trace ("Connecting "++show loc_from++" with "++show loc_to++" "++show ptrs) $ return ()
    let cloc = case Map.lookup loc_from (snowLocations mem) of
          Just l -> l
          Nothing -> error $ "Couldn't find location "++show loc_from --SnowLocation Map.empty Map.empty
        mem1 = mem { snowPointerConnections = foldl (\mp (p1,p2) -> Map.insertWith (++) p1 [(p2,cond)] mp) (snowPointerConnections mem) ptrs
                   , snowLocationConnections = Map.insertWith (++) loc_from [(loc_to,cond)] (snowLocationConnections mem)
                   }
    (obj_upd,ptr_upd,nlocs,nnext) <- updateLocation' (snowStructs mem1) (Just cond) loc_to 
                                     (fmap (\obj -> AssignDynamic $ assignList obj) $ snowObjects cloc)
                                     (Map.union (snowPointer cloc)
                                      (Map.fromList [ (p2,v1) | (p1,p2) <- ptrs, let Just v1 = Map.lookup p1 (snowPointer cloc) ]))
                                     (snowPointerConnections mem1)
                                     (snowLocationConnections mem1)
                                     (snowNextObject mem1)
                                     (snowProgram mem1)
    let mem2 = applyUpdate loc_from loc_to (fmap (\(obj_p,obj) -> (obj_p,assignList obj)) obj_upd) ptr_upd mem1
        emptyLike :: [a] -> [a]
        emptyLike _ = []
    mem3 <- foldlM (\cmem (cloc,cond') -> connectLocation cmem (cond .&&. cond') loc_to cloc (emptyLike ptrs))
            (mem2 { snowNextObject = nnext }) nlocs
    return mem3
  debugMem mem _ _ = snowDebug mem

applyUpdate :: (Ord mloc,Ord ptr,Show ptr,Show mloc)
               => mloc
               -> mloc
               -> [(Integer,[(SMTExpr Bool,Object ptr)])]
               -> [(ptr,AssignState (Maybe (Integer,PtrIndex)))]
               -> SnowMemory mloc ptr
               -> SnowMemory mloc ptr
applyUpdate loc_from loc_to obj_upd ptr_upd mem
  = trace ("Apply update "++show obj_upd++" "++show ptr_upd) $
    case Map.lookup loc_from (snowLocations mem) of
    Just loc_from' -> mem { snowLocations = Map.insertWith mappend loc_to
                                            (SnowLocation { snowObjects = Map.union 
                                                                          (fmap AssignDynamic $ Map.fromList obj_upd)
                                                                          (snowObjects loc_from')
                                                          , snowPointer = Map.union
                                                                          (Map.fromList ptr_upd)
                                                                          (snowPointer loc_from')
                                                          }) (snowLocations mem)
                          }
    Nothing -> error $ "Couldn't find location "++show loc_from++" to apply update"

initLocation :: (Eq ptr,Ord ptr,Show ptr,Eq mloc,Ord mloc,Show mloc)
                => Map String [TypeDesc]
                -> mloc
                -> Map Integer (AssignState (Object ptr))
                -> Map ptr (AssignState (Maybe (Integer,PtrIndex)))
                -> SnowMemory mloc ptr
                -> SMT (SnowMemory mloc ptr)
initLocation structs loc objs ptrs mem = do
  (obj_upd,ptr_upd,loc_upd,next') <- updateLocation' structs Nothing loc objs ptrs (snowPointerConnections mem) (snowLocationConnections mem) (snowNextObject mem) (snowProgram mem)
  let nptrs = Map.union (Map.fromList ptr_upd) ptrs
      nobjs = Map.union (Map.fromList obj_upd) objs
      loc_cont = SnowLocation { snowObjects = nobjs
                              , snowPointer = nptrs
                              }
      mem' = mem { snowLocations = Map.insertWith mappend loc
                                   loc_cont (snowLocations mem)
                 , snowNextObject = next'
                 }
  foldlM (\cmem (nloc,cond') -> initLocation structs nloc
                                nobjs
                                nptrs
                                cmem -- cond' must be TRUE
         ) mem' loc_upd

connectPointerUpdate :: Ord ptr 
                         => Map ptr [(ptr,SMTExpr Bool)] 
                         -> (ptr,AssignState (Maybe (Integer,PtrIndex)))
                         -> [(ptr,AssignState (Maybe (Integer,PtrIndex)))]
connectPointerUpdate conns x@(ptr,assign) = case Map.lookup ptr conns of
  Nothing -> [x]
  Just ptrs -> x:[ (ptr',case assign of
                       AssignStatic trg -> AssignDynamic [(cond',trg)]
                       AssignDynamic trgs -> AssignDynamic [(cond' .&&. cond,trg)
                                                           | (cond,trg) <- trgs ])
                 | (ptr',cond') <- ptrs ]

connectLocationUpdate :: Ord mloc
                         => Map mloc [(mloc,SMTExpr Bool)]
                         -> mloc
                         -> [(mloc,SMTExpr Bool)]
connectLocationUpdate mp loc = case Map.lookup loc mp of
  Nothing -> [(loc,constant True)]
  Just locs -> (loc,constant True):locs

updateLocation' :: (Eq ptr,Ord ptr,Show ptr,Eq mloc,Ord mloc,Show mloc)
                  => Map String [TypeDesc]
                  -> Maybe (SMTExpr Bool)
                  -> mloc
                  -> Map Integer (AssignState (Object ptr))
                  -> Map ptr (AssignState (Maybe (Integer,PtrIndex)))
                  -> Map ptr [(ptr,SMTExpr Bool)]
                  -> Map mloc [(mloc,SMTExpr Bool)]
                  -> Integer
                  -> [MemoryInstruction mloc ptr]
                  -> SMT ([(Integer,AssignState (Object ptr))],
                          [(ptr,AssignState (Maybe (Integer,PtrIndex)))],
                          [(mloc,SMTExpr Bool)],
                          Integer)
updateLocation' structs cond loc objs ptrs conns_ptr conns_loc next instrs = do
  foldlM (\(obj_upd,ptr_upd,loc_upd,cnext) instr -> do
             trace ("Update loc "++show loc++" for "++show instr++(case cond of
                                                                      Nothing -> ""
                                                                      Just cond' -> " if "++show cond')
                   ) $ return ()
             (obj_upd',ptr_upd',loc_upd',next') <- updateLocation structs cond loc objs ptrs cnext instr
             return (obj_upd'++obj_upd,
                     case ptr_upd' of
                       Nothing -> ptr_upd
                       Just upd -> (connectPointerUpdate conns_ptr upd)++ptr_upd,
                     case loc_upd' of
                       Nothing -> loc_upd
                       Just upd -> (connectLocationUpdate conns_loc upd)++loc_upd,
                     next')
           ) ([],[],[],next) instrs

updateLocation :: (Eq ptr,Ord ptr,Show ptr,Eq mloc,Ord mloc,Show mloc)
                  => Map String [TypeDesc]
                  -> Maybe (SMTExpr Bool)
                  -> mloc
                  -> Map Integer (AssignState (Object ptr))
                  -> Map ptr (AssignState (Maybe (Integer,PtrIndex)))
                  -> Integer
                  -> MemoryInstruction mloc ptr
                  -> SMT ([(Integer,AssignState (Object ptr))],
                          Maybe (ptr,AssignState (Maybe (Integer,PtrIndex))),
                          Maybe mloc,
                          Integer)
updateLocation structs cond loc objs ptrs next_obj instr = case instr of
  MINull mfrom tp ptr mto
    | mfrom==loc -> case cond of
      Just _ -> return ([],Nothing,Just mto,next_obj)
      Nothing -> trace ("Initialize nulling of "++show ptr++" at "++show mfrom) $ 
                 return ([],Just (ptr,AssignStatic Nothing),Just mto,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MIAlloc mfrom tp num ptr mto
    | mfrom==loc -> case cond of
      Just _ -> return ([],Nothing,Just mto,next_obj)
      Nothing -> do
        obj <- allocaObject structs tp num
        trace ("Initialize allocation of "++show ptr++" at "++show mfrom) $ return ()
        return ([(next_obj,AssignStatic obj)],
                Just (ptr,AssignStatic (Just (next_obj,[(tp,[])]))),
                Just mto,succ next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MILoad mfrom ptr res
    | mfrom==loc -> case Map.lookup ptr ptrs of
      Just (AssignStatic src) -> do
        let sz = extractAnnotation res
        case src of
          Nothing -> return ()
          Just (obj_p,idx) -> do
            let ObjAccessor access = ptrIndexGetAccessor structs idx
            case Map.lookup obj_p objs of
              Just (AssignStatic obj) -> case cond of
                Nothing -> do
                  let (_,loaded,errs) = access
                                        (\obj' -> let (res,errs) = loadObject sz obj'
                                                  in (obj',res,errs)
                                        ) obj
                  comment $ "Initial load from "++show src
                  assert $ res .==. loaded
                Just cond' -> comment $ "Skipping static load to "++show res
              Just (AssignDynamic objs') -> do
                mapM_ (\(cond'',obj) -> do
                          let (_,loaded,errs) = access 
                                                (\obj' -> let (res,errs) = loadObject sz obj'
                                                          in (obj',res,errs)
                                                ) obj
                          comment $ (case cond of
                                        Nothing -> "Initial "
                                        Just _ -> "")++"Load from "++show ptr
                          assert $ (and' `app` ((case cond of
                                                    Nothing -> id
                                                    Just cond' -> (cond':)
                                                ) [cond''])) .=>. (res .==. loaded)
                      ) objs'
        return ([],Nothing,Nothing,next_obj)
      Just (AssignDynamic srcs) -> do
        trace ("Updating loading from "++show ptr++" at "++show mfrom) $ return ()
        let sz = extractAnnotation res
        let icond = case cond of
              Just c -> c
        mapM_ (\(cond',src) -> case src of
                  Nothing -> return ()
                  Just (obj_p,idx) -> do
                    let ObjAccessor access = ptrIndexGetAccessor structs idx
                    case Map.lookup obj_p objs of
                      Just objs' -> do
                        mapM_ (\(cond'',obj) -> do
                                  let (_,loaded,errs) = access 
                                                        (\obj' -> let (res,errs) = loadObject sz obj'
                                                                  in (obj',res,errs)
                                                        ) obj
                                  comment $ (case cond of
                                                Nothing -> "Initial "
                                                Just _ -> "")++"Load from "++show ptr
                                  assert $ (and' `app` ([icond,cond',cond''])) .=>. (res .==. loaded)
                              ) (assignList objs')
                      _ -> error $ "Failed to find object "++show obj_p++" for loading from "++show ptr++"."
              ) srcs
        return ([],Nothing,Nothing,next_obj)
      Nothing -> case cond of
        Nothing -> return ([],Nothing,Nothing,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MILoadPtr mfrom ptr_from ptr_to mto
    | mfrom==loc -> case Map.lookup ptr_from ptrs of
      Just (AssignStatic src) -> case cond of
        Nothing -> case src of
          Nothing -> return ([],Nothing,Just mto,next_obj)
          Just (obj_p,idx) -> do
            let ObjAccessor access = ptrIndexGetAccessor structs idx
            case Map.lookup obj_p objs of
              Just (AssignStatic obj)
                -> let (_,loaded,errs) = access
                                         (\obj' -> let (res,errs) = loadPtr obj'
                                                   in (obj',res,errs)
                                         ) obj
                   in case loaded of
                     Nothing -> return ([],Just (ptr_to,AssignStatic Nothing),Just mto,next_obj)
                     Just p -> case Map.lookup p ptrs of
                       Just (AssignStatic dest) -> return ([],Just (ptr_to,AssignStatic dest),Just mto,next_obj)
        Just _ -> return ([],Nothing,Just mto,next_obj)
      Just (AssignDynamic srcs) -> do
        let icond = case cond of
              Just c -> c
            nptr = fmap (\(cond',src) 
                         -> case src of
                           Just (obj_p,idx)
                             -> let ObjAccessor access = ptrIndexGetAccessor structs idx
                                in case Map.lookup obj_p objs of
                                  Just (AssignDynamic objs')
                                    -> fmap (\(cond'',obj)
                                             -> let (_,loaded,errs) = access
                                                                      (\obj' -> let (res,errs) = loadPtr obj'
                                                                                in (obj',res,errs)
                                                                      ) obj
                                                in case loaded of
                                                  Nothing -> [(and' `app` ([icond,cond',cond'']),Nothing)]
                                                  Just p -> case Map.lookup p ptrs of
                                                    Just (AssignDynamic dests)
                                                      -> [(and' `app` ([icond,cond',cond'',c]),d)
                                                         | (c,d) <- dests ]
                                                    Just (AssignStatic dest)
                                                      -> [(and' `app` [icond,cond',cond''],dest)]
                                            ) objs'
                                  Just (AssignStatic obj)
                                    -> let (_,loaded,errs) = access
                                                             (\obj' -> let (res,errs) = loadPtr obj'
                                                                       in (obj',res,errs)
                                                             ) obj
                                       in [case loaded of
                                              Nothing -> [(and' `app` ([icond,cond']),Nothing)]
                                              Just p -> case Map.lookup p ptrs of
                                                Just (AssignDynamic dests)
                                                  -> [(and' `app` [icond,cond',c],d)
                                                     | (c,d) <- dests ]
                                                Just (AssignStatic dest) -> [(and' `app` [icond,cond'],dest)]
                                          ]
                           Nothing -> []
                        ) srcs
        return ([],Just (ptr_to,AssignDynamic $ concat $ concat nptr),Just mto,next_obj)
      Nothing -> case cond of
        Just _ -> error $ "Failed to find pointer "++show ptr_from++" for loading @ "++show mfrom++"."
        Nothing -> return ([],Nothing,Just mto,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MIStore mfrom val ptr_to mto
    | mfrom==loc -> case Map.lookup ptr_to ptrs of
      Just (AssignStatic dest) -> case cond of
        Nothing -> trace ("Initial storing of "++show val++" to "++show ptr_to) $ case dest of
          Nothing -> return ([],Nothing,Just mto,next_obj)
          Just (obj_p,idx) -> do
            let ObjAccessor access = ptrIndexGetAccessor structs idx
                Just (AssignStatic obj) = Map.lookup obj_p objs
                (nobj,_,errs) = access (\obj' -> let (res,errs) = storeObject val obj'
                                                 in (res,(),errs)
                                       ) obj
            return ([(obj_p,AssignStatic nobj)],Nothing,Just mto,next_obj)
        Just _ -> return ([],Nothing,Just mto,next_obj)
      Just (AssignDynamic dests)
        -> return ([ (obj_p,AssignDynamic
                            [ (c,nobj)
                            | (c,obj) <- assignList objs',
                              let (nobj,_,errs) = access (\obj' -> let (res,errs) = storeObject val obj'
                                                                   in (res,(),errs)
                                                         ) obj
                            ])
                   | (c,Just (obj_p,idx)) <- dests,
                     let ObjAccessor access = ptrIndexGetAccessor structs idx
                         Just objs' = Map.lookup obj_p objs
                   ],Nothing,Just mto,next_obj)
      Nothing -> case cond of
        Nothing -> return ([],Nothing,Nothing,next_obj)
        Just _ -> error $ "Failed to find pointer "++show ptr_to++" for storing @ "++show mfrom
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MIStorePtr mfrom ptr_from ptr_to mto
    | mfrom==loc -> case Map.lookup ptr_to ptrs of
      Just (AssignStatic dest) -> case cond of
        Nothing -> case dest of
          Nothing -> return ([],Nothing,Just mto,next_obj)
          Just (obj_p,idx) -> do
            let ObjAccessor access = ptrIndexGetAccessor structs idx
                Just (AssignStatic obj) = Map.lookup obj_p objs
                (nobj,_,errs) = access (\obj' -> let (res,errs) = storePtr ptr_from obj'
                                                 in (res,(),errs)
                                       ) obj
            return ([(obj_p,AssignStatic nobj)],Nothing,Just mto,next_obj)
        Just _ -> return ([],Nothing,Just mto,next_obj)
      Just (AssignDynamic dests)
        -> return ([ (obj_p,AssignDynamic
                            [ (c,nobj)
                            | (c,obj) <- objs',
                              let (nobj,_,errs) = access (\obj' -> let (res,errs) = storePtr ptr_from obj'
                                                                   in (res,(),errs)
                                                         ) obj
                            ])
                   | (c,Just (obj_p,idx)) <- dests,
                     let ObjAccessor access = ptrIndexGetAccessor structs idx
                         Just (AssignDynamic objs') = Map.lookup obj_p objs
                   ],Nothing,Just mto,next_obj)
      Nothing -> case cond of
        Nothing -> return ([],Nothing,Just mto,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MICompare mfrom p1 p2 res
    | mfrom==loc -> case (Map.lookup p1 ptrs,Map.lookup p2 ptrs) of
      (Nothing,_) -> case cond of
        Nothing -> return ([],Nothing,Nothing,next_obj)
      (_,Nothing) -> case cond of
        Nothing -> return ([],Nothing,Nothing,next_obj)
      (Just (AssignStatic s1),Just (AssignStatic s2)) -> case cond of
        Just _ -> return ([],Nothing,Nothing,next_obj)
        Nothing -> case (s1,s2) of
          (Nothing,Nothing) -> do
            assert res
            return ([],Nothing,Nothing,next_obj)
          (Just (o1,i1),Just (o2,i2)) -> do
            if o1==o2
              then (case ptrIndexEq i1 i2 of
                       Left x -> assert $ res .==. constant x
                       Right c -> assert $ res .==. c)
              else assert $ not' res
            return ([],Nothing,Nothing,next_obj)
          _ -> do
            assert $ not' res
            return ([],Nothing,Nothing,next_obj)
      (Just a1,Just a2) -> do
        let clist = [ case (ptr1,ptr2) of
                         (Nothing,Nothing) -> Just (c1 .&&. c2)
                         (Just (o1,i1),Just (o2,i2))
                           -> if o1==o2
                              then (case ptrIndexEq i1 i2 of
                                       Left True -> Just (c1 .&&. c2)
                                       Left False -> Nothing
                                       Right c -> Just (and' `app` [c1,c2,c]))
                              else Nothing
                         (_,_) -> Nothing
                    | (c1,ptr1) <- assignList a1,
                      (c2,ptr2) <- assignList a2 ]
        case cond of
          Just c -> assert $ c .=>. (res .==. (or' `app` (catMaybes clist)))
        return ([],Nothing,Nothing,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MISelect mfrom cases ptr_to mto
    | mfrom==loc -> case cond of
      Nothing -> return ([],Nothing,Just mto,next_obj)
      Just cond' -> do
        let nptr = fmap (\(c,p) -> case Map.lookup p ptrs of
                            Nothing -> []
                            Just srcs -> fmap (\(c',p') -> (c .&&. c',p')) (assignList srcs)
                        ) cases
        case concat nptr of
          [] -> return ([],Nothing,Just mto,next_obj)
          xs -> return ([],Just (ptr_to,AssignDynamic xs),Just mto,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MICast mfrom tp_from tp_to ptr_from ptr_to mto
    | mfrom==loc -> case Map.lookup ptr_from ptrs of
      Nothing -> case cond of
        Nothing -> return ([],Nothing,Just mto,next_obj)
      Just (AssignStatic src) -> case cond of
        Just _ -> return ([],Nothing,Just mto,next_obj)
        Nothing -> case src of
          Nothing -> return ([],Just (ptr_to,AssignStatic Nothing),Just mto,next_obj)
          Just (obj_p,idx) -> return ([],Just (ptr_to,AssignStatic (Just (obj_p,ptrIndexCast structs tp_to idx))),Just mto,next_obj)
      Just (AssignDynamic srcs) -> do
        trace ("Updating cast of "++show ptr_from++" at "++show mfrom) $ return ()
        let nptr = fmap (\(c,src) -> case src of
                            Nothing -> (c,Nothing)
                            Just (obj_p,idx) -> (c,Just (obj_p,ptrIndexCast structs tp_to idx))
                        ) srcs
        return ([],Just (ptr_to,AssignDynamic nptr),Just mto,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MIIndex mfrom idx ptr_from ptr_to mto
    | mfrom==loc -> case Map.lookup ptr_from ptrs of
      Nothing -> case cond of
        Nothing -> return ([],Nothing,Just mto,next_obj)
        Just _ -> return ([],Nothing,Just mto,next_obj)
      Just (AssignStatic src) -> case cond of
        Just _ -> return ([],Nothing,Just mto,next_obj)
        Nothing -> case src of
          Nothing -> return ([],Just (ptr_to,AssignStatic Nothing),Just mto,next_obj)
          Just (obj_p,idx') -> return ([],Just (ptr_to,AssignStatic (Just (obj_p,ptrIndexIndex idx idx'))),Just mto,next_obj)
      Just (AssignDynamic srcs) -> do
        trace ("Updating indexing of "++show ptr_from++" at "++show mfrom) $ return ()
        let nptr = fmap (\(c,src) -> case src of
                            Nothing -> (c,Nothing)
                            Just (obj_p,idx') -> (c,Just (obj_p,ptrIndexIndex idx idx'))
                        ) srcs
        return ([],Just (ptr_to,AssignDynamic nptr),Just mto,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)

snowDebugLocation :: Show ptr => String -> SnowLocation ptr -> [String]
snowDebugLocation loc_name cont
  = listHeader (loc_name++":") $
    ["Objects"]++
    (concat [ case obj of
                 AssignStatic obj' -> ["  "++show obj_p++" = "++show obj']
                 AssignDynamic objs -> listHeader ("  "++show obj_p++":")
                                       [ show cond++" ~> "++show obj'
                                       | (cond,obj') <- objs ]
            | (obj_p,obj) <- Map.toList (snowObjects cont) ])++
    ["Pointers"]++
    (concat [ case cases of
                 AssignStatic ptr' -> ["  "++show ptr++" = "++show ptr']
                 AssignDynamic cases' -> listHeader ("  "++show ptr++":")
                                         [show cond++" ~> "++show ptr'
                                         | (cond,ptr') <- cases' ]
            | (ptr,cases) <- Map.toList (snowPointer cont) ])
  where
    listHeader :: String -> [String] -> [String]
    listHeader x [] = []
    listHeader x (y:ys) = let l = (length x)+1
                          in (x++" "++y):(fmap ((replicate l ' ')++) ys)

snowDebug :: (Show ptr,Show mloc) => SnowMemory mloc ptr -> String
snowDebug mem = unlines $ concat
                [ snowDebugLocation (show loc) cont
                | (loc,cont) <- Map.toList (snowLocations mem)
                ]