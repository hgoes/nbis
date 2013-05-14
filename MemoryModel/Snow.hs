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
import Prelude hiding (foldl1,foldl,mapM_,concat,mapM,sequence_)
import Data.Bits
import Control.Monad.Trans
import Data.Maybe (catMaybes)
import Data.Monoid
import qualified Data.List as List
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

data SnowLocation ptr
  = SnowLocation { snowObjects :: Map Integer [(SMTExpr Bool,Object ptr)]
                 , snowPointer :: Map ptr [(SMTExpr Bool,Maybe (Integer,PtrIndex))]
                 }

instance (Ord ptr,Show ptr) => Monoid (SnowLocation ptr) where
  mempty = SnowLocation { snowObjects = Map.empty
                        , snowPointer = Map.empty }
  mappend l1 l2 = SnowLocation { snowObjects = Map.unionWith (++) (snowObjects l1) (snowObjects l2)
                               , snowPointer = Map.unionWith (++) (snowPointer l1) (snowPointer l2)
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
                               return (loc { snowObjects = Map.insert next [(constant True,glob)] (snowObjects loc)
                                           , snowPointer = Map.insert ptr [(constant True,Just (next,[(tp,[])]))] (snowPointer loc)
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
                                     (snowObjects cloc)
                                     (Map.union (snowPointer cloc)
                                      (Map.fromList [ (p2,v1) | (p1,p2) <- ptrs, let Just v1 = Map.lookup p1 (snowPointer cloc) ]))
                                     (snowPointerConnections mem1)
                                     (snowLocationConnections mem1)
                                     (snowNextObject mem1)
                                     (snowProgram mem1)
    let mem2 = applyUpdate loc_from loc_to obj_upd ptr_upd mem1
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
               -> [(ptr,[(SMTExpr Bool,Maybe (Integer,PtrIndex))])]
               -> SnowMemory mloc ptr
               -> SnowMemory mloc ptr
applyUpdate loc_from loc_to obj_upd ptr_upd mem
  = trace ("Apply update "++show obj_upd++" "++show ptr_upd) $
    case Map.lookup loc_from (snowLocations mem) of
    Just loc_from' -> mem { snowLocations = Map.insertWith mappend loc_to
                                            (SnowLocation { snowObjects = Map.union 
                                                                          (Map.fromList obj_upd)
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
                -> Map Integer [(SMTExpr Bool,Object ptr)]
                -> Map ptr [(SMTExpr Bool,Maybe (Integer,PtrIndex))]
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
                         -> (ptr,[(SMTExpr Bool,Maybe (Integer,PtrIndex))])
                         -> [(ptr,[(SMTExpr Bool,Maybe (Integer,PtrIndex))])]
connectPointerUpdate conns x@(ptr,assign) = case Map.lookup ptr conns of
  Nothing -> [x]
  Just ptrs -> x:[ (ptr',[(cond' .&&. cond,trg)
                         | (cond,trg) <- assign ])
                 | (ptr',cond') <- ptrs ]

connectLocationUpdate :: Ord mloc
                         => Map mloc [(mloc,SMTExpr Bool)]
                         -> mloc
                         -> [(mloc,SMTExpr Bool)]
connectLocationUpdate mp loc = case Map.lookup loc mp of
  Nothing -> [(loc,constant True)]
  Just locs -> (loc,constant True):locs

updatePointer :: (Show ptr,Eq mloc,Ord ptr)
                 => Map String [TypeDesc]                             -- ^ All struct types
                 -> mloc                                              -- ^ The location to be updated
                 -> Map ptr [(SMTExpr Bool,Maybe (Integer,PtrIndex))] -- ^ All the pointers at the location (needed for pointer comparisons)
                 -> Map Integer [(SMTExpr Bool,Object ptr)]           -- ^ All objects at the location
                 -> ptr                                               -- ^ The pointer to be updated
                 -> [(SMTExpr Bool,Maybe (Integer,PtrIndex))]         -- ^ The new assignments of this pointer
                 -> MemoryInstruction mloc ptr
                 -> SMT ([(Integer,[(SMTExpr Bool,Object ptr)])],
                         [(ptr,[(SMTExpr Bool,Maybe (Integer,PtrIndex))])])
updatePointer structs loc all_ptrs all_objs new_ptr new_conds instr = case instr of
  MILoad mfrom ptr res
    | mfrom==loc && ptr==new_ptr -> do
      let sz = extractAnnotation res
      mapM_ (\(cond,src) -> case src of
                Nothing -> return () -- Nullpointer (TODO: Error reporting)
                Just (obj_p,idx) -> do
                  let ObjAccessor access = ptrIndexGetAccessor structs idx
                  case Map.lookup obj_p all_objs of
                    Just objs -> do
                      mapM_ (\(cond',obj) -> do
                                let (_,loaded,errs) = access 
                                                      (\obj' -> let (res,errs) = loadObject sz obj'
                                                                in (obj',res,errs)
                                                      ) obj
                                comment $ "Load from "++show ptr
                                assert $ (and' `app` [cond,cond']
                                         ) .=>. (res .==. loaded)
                            ) objs
            ) new_conds
      return ([],[])
    | otherwise -> return ([],[])
  MILoadPtr mfrom ptr_from ptr_to mto
    | mfrom==loc && ptr_from==new_ptr -> do
      let nptr = fmap (\(cond,src) -> case src of
                          Nothing -> [] -- Nullpointer (TODO: Error reporting)
                          Just (obj_p,idx)
                            -> let ObjAccessor access = ptrIndexGetAccessor structs idx
                               in case Map.lookup obj_p all_objs of
                                 Just objs'
                                   -> fmap (\(cond',obj)
                                            -> let (_,loaded,errs) = access
                                                                      (\obj' -> let (res,errs) = loadPtr obj'
                                                                                in (obj',res,errs)
                                                                      ) obj
                                                in case loaded of
                                                  Nothing -> [(and' `app` ([cond,cond']),Nothing)]
                                                  Just p -> case Map.lookup p all_ptrs of
                                                    Just dests
                                                      -> [(and' `app` ([cond,cond',c]),d)
                                                         | (c,d) <- dests ]
                                           ) objs'
                      ) new_conds
      return ([],[(ptr_to,concat $ concat nptr)])
    | otherwise -> return ([],[])
  MIStore mfrom val ptr_to mto
    | mfrom==loc && ptr_to==new_ptr
      -> return ([ (obj_p,[ (cond .&&. cond',nobj)
                          | (cond',obj) <- objs',
                            let (nobj,_,errs) = access (\obj' -> let (res,errs) = storeObject val obj'
                                                                 in (res,(),errs)
                                                       ) obj
                          ])
                 | (cond,Just (obj_p,idx)) <- new_conds,
                   let ObjAccessor access = ptrIndexGetAccessor structs idx
                       Just objs' = Map.lookup obj_p all_objs
                 ],[])
    | otherwise -> return ([],[])
  MIStorePtr mfrom ptr_from ptr_to mto
    | mfrom==loc && ptr_from==new_ptr -> case Map.lookup ptr_to all_ptrs of
      Just dests -> return ([ (obj_p,[ (cond .&&. cond',nobj)
                                     | (cond',obj) <- objs',
                                       let (nobj,_,errs) = access (\obj' -> let (res,errs) = storePtr ptr_from obj'
                                                                            in (res,(),errs)
                                                                  ) obj
                                     ])
                            | (cond,Just (obj_p,idx)) <- dests,
                              let ObjAccessor access = ptrIndexGetAccessor structs idx
                                  Just objs' = Map.lookup obj_p all_objs
                            ],[])
    | mfrom==loc && ptr_to==new_ptr
      -> return ([ (obj_p,[ (cond .&&. cond',nobj)
                          | (cond',obj) <- objs',
                            let (nobj,_,errs) = access (\obj' -> let (res,errs) = storePtr ptr_from obj'
                                                                 in (res,(),errs)
                                                       ) obj
                          ])
                 | (cond,Just (obj_p,idx)) <- new_conds,
                   let ObjAccessor access = ptrIndexGetAccessor structs idx
                       Just objs' = Map.lookup obj_p all_objs
                 ],[])
    | otherwise -> return ([],[])
  MICompare mfrom p1 p2 res
    | mfrom==loc && p1==new_ptr -> case Map.lookup p2 all_ptrs of
      Just a2 -> compare' new_conds a2
    | mfrom==loc && p2==new_ptr -> case Map.lookup p1 all_ptrs of
      Just a1 -> compare' new_conds a1
    | otherwise -> return ([],[])
    where
      compare' a1 a2 = do
        sequence_ [ assert $ (c1 .&&. c2) .=>. 
                    (case (ptr1,ptr2) of
                        (Nothing,Nothing) -> res
                        (Just (o1,i1),Just (o2,i2))
                          -> if o1==o2
                             then (case ptrIndexEq i1 i2 of
                                      Left True -> res
                                      Left False -> not' res
                                      Right c -> res .==. c)
                             else not' res
                        (_,_) -> not' res)
                  | (c1,ptr1) <- a1,
                    (c2,ptr2) <- a2 ]
        return ([],[])
  MISelect mfrom cases ptr_to mto
    | mfrom==loc -> case List.find (\(_,ptr_from) -> ptr_from==new_ptr) cases of
      Nothing -> return ([],[])
      Just (cond,_) -> return ([],[(ptr_to,[(cond .&&. cond',src)
                                           | (cond',src) <- new_conds ])])
    | otherwise -> return ([],[])
  MICast mfrom tp_from tp_to ptr_from ptr_to mto
    | mfrom==loc -> return ([],[(ptr_to,[ case src of
                                             Nothing -> (c,Nothing)
                                             Just (obj_p,idx) -> (c,Just (obj_p,ptrIndexCast structs tp_to idx))
                                        | (c,src) <- new_conds ])])
    | otherwise -> return ([],[])

updateLocation' :: (Eq ptr,Ord ptr,Show ptr,Eq mloc,Ord mloc,Show mloc)
                  => Map String [TypeDesc]
                  -> Maybe (SMTExpr Bool)
                  -> mloc
                  -> Map Integer [(SMTExpr Bool,Object ptr)]
                  -> Map ptr [(SMTExpr Bool,Maybe (Integer,PtrIndex))]
                  -> Map ptr [(ptr,SMTExpr Bool)]
                  -> Map mloc [(mloc,SMTExpr Bool)]
                  -> Integer
                  -> [MemoryInstruction mloc ptr]
                  -> SMT ([(Integer,[(SMTExpr Bool,Object ptr)])],
                          [(ptr,[(SMTExpr Bool,Maybe (Integer,PtrIndex))])],
                          [(mloc,SMTExpr Bool)],
                          Integer)
updateLocation' structs cond loc objs ptrs conns_ptr conns_loc next instrs = do
  foldlM (\(obj_upd,ptr_upd,loc_upd,cnext) instr -> do
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
                  -> Map Integer [(SMTExpr Bool,Object ptr)]
                  -> Map ptr [(SMTExpr Bool,Maybe (Integer,PtrIndex))]
                  -> Integer
                  -> MemoryInstruction mloc ptr
                  -> SMT ([(Integer,[(SMTExpr Bool,Object ptr)])],
                          Maybe (ptr,[(SMTExpr Bool,Maybe (Integer,PtrIndex))]),
                          Maybe mloc,
                          Integer)
updateLocation structs cond loc objs ptrs next_obj instr = case instr of
  MINull mfrom tp ptr mto
    | mfrom==loc -> case cond of
      Just _ -> return ([],Nothing,Just mto,next_obj)
      Nothing -> trace ("Initialize nulling of "++show ptr++" at "++show mfrom) $ 
                 return ([],Just (ptr,[(constant True,Nothing)]),Just mto,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MIAlloc mfrom tp num ptr mto
    | mfrom==loc -> case cond of
      Just _ -> return ([],Nothing,Just mto,next_obj)
      Nothing -> do
        obj <- allocaObject structs tp num
        trace ("Initialize allocation of "++show ptr++" at "++show mfrom) $ return ()
        return ([(next_obj,[(constant True,obj)])],
                Just (ptr,[(constant True,Just (next_obj,[(tp,[])]))]),
                Just mto,succ next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MILoad mfrom ptr res
    | mfrom==loc -> case Map.lookup ptr ptrs of
      Just srcs -> do
        trace ("Updating loading from "++show ptr++" at "++show mfrom) $ return ()
        let sz = extractAnnotation res
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
                                  assert $ (and' `app` (case cond of
                                                           Nothing -> [cond',cond'']
                                                           Just rcond -> [rcond,cond',cond'']
                                                       )) .=>. (res .==. loaded)
                              ) objs'
                      _ -> error $ "Failed to find object "++show obj_p++" for loading from "++show ptr++"."
              ) srcs
        return ([],Nothing,Nothing,next_obj)
      Nothing -> case cond of
        Nothing -> return ([],Nothing,Nothing,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MILoadPtr mfrom ptr_from ptr_to mto
    | mfrom==loc -> case Map.lookup ptr_from ptrs of
      Just srcs -> do
        let icond = case cond of
              Just c -> c
              Nothing -> constant True
            nptr = fmap (\(cond',src) 
                         -> case src of
                           Just (obj_p,idx)
                             -> let ObjAccessor access = ptrIndexGetAccessor structs idx
                                in case Map.lookup obj_p objs of
                                  Just objs'
                                    -> fmap (\(cond'',obj)
                                             -> let (_,loaded,errs) = access
                                                                      (\obj' -> let (res,errs) = loadPtr obj'
                                                                                in (obj',res,errs)
                                                                      ) obj
                                                in case loaded of
                                                  Nothing -> [(and' `app` ([icond,cond',cond'']),Nothing)]
                                                  Just p -> case Map.lookup p ptrs of
                                                    Just dests
                                                      -> [(and' `app` ([icond,cond',cond'',c]),d)
                                                         | (c,d) <- dests ]
                                            ) objs'
                           Nothing -> []
                        ) srcs
        return ([],Just (ptr_to,concat $ concat nptr),Just mto,next_obj)
      Nothing -> case cond of
        Just _ -> error $ "Failed to find pointer "++show ptr_from++" for loading @ "++show mfrom++"."
        Nothing -> return ([],Nothing,Just mto,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MIStore mfrom val ptr_to mto
    | mfrom==loc -> case Map.lookup ptr_to ptrs of
      Just dests
        -> return ([ (obj_p,[ (c,nobj)
                            | (c,obj) <- objs',
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
      Just dests
        -> return ([ (obj_p,[ (c,nobj)
                            | (c,obj) <- objs',
                              let (nobj,_,errs) = access (\obj' -> let (res,errs) = storePtr ptr_from obj'
                                                                   in (res,(),errs)
                                                         ) obj
                            ])
                   | (c,Just (obj_p,idx)) <- dests,
                     let ObjAccessor access = ptrIndexGetAccessor structs idx
                         Just objs' = Map.lookup obj_p objs
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
                    | (c1,ptr1) <- a1,
                      (c2,ptr2) <- a2 ]
        case cond of
          Just c -> assert $ c .=>. (res .==. (or' `app` (catMaybes clist)))
          Nothing -> assert (res .==. (or' `app` (catMaybes clist)))
        return ([],Nothing,Nothing,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MISelect mfrom cases ptr_to mto
    | mfrom==loc -> case cond of
      Nothing -> return ([],Nothing,Just mto,next_obj)
      Just cond' -> do
        let nptr = fmap (\(c,p) -> case Map.lookup p ptrs of
                            Nothing -> []
                            Just srcs -> fmap (\(c',p') -> (c .&&. c',p')) srcs
                        ) cases
        case concat nptr of
          [] -> return ([],Nothing,Just mto,next_obj)
          xs -> return ([],Just (ptr_to,xs),Just mto,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MICast mfrom tp_from tp_to ptr_from ptr_to mto
    | mfrom==loc -> case Map.lookup ptr_from ptrs of
      Nothing -> case cond of
        Nothing -> return ([],Nothing,Just mto,next_obj)
      Just srcs -> do
        trace ("Updating cast of "++show ptr_from++" at "++show mfrom) $ return ()
        let nptr = fmap (\(c,src) -> case src of
                            Nothing -> (c,Nothing)
                            Just (obj_p,idx) -> (c,Just (obj_p,ptrIndexCast structs tp_to idx))
                        ) srcs
        return ([],Just (ptr_to,nptr),Just mto,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)
  MIIndex mfrom idx ptr_from ptr_to mto
    | mfrom==loc -> case Map.lookup ptr_from ptrs of
      Nothing -> case cond of
        Nothing -> return ([],Nothing,Just mto,next_obj)
        Just _ -> return ([],Nothing,Just mto,next_obj)
      Just srcs -> do
        trace ("Updating indexing of "++show ptr_from++" at "++show mfrom) $ return ()
        let nptr = fmap (\(c,src) -> case src of
                            Nothing -> (c,Nothing)
                            Just (obj_p,idx') -> (c,Just (obj_p,ptrIndexIndex idx idx'))
                        ) srcs
        return ([],Just (ptr_to,nptr),Just mto,next_obj)
    | otherwise -> return ([],Nothing,Nothing,next_obj)

snowDebugLocation :: Show ptr => String -> SnowLocation ptr -> [String]
snowDebugLocation loc_name cont
  = listHeader (loc_name++":") $
    ["Objects"]++
    (concat [ listHeader ("  "++show obj_p++":")
              [ show cond++" ~> "++show obj'
              | (cond,obj') <- obj ]
            | (obj_p,obj) <- Map.toList (snowObjects cont) ])++
    ["Pointers"]++
    (concat [ listHeader ("  "++show ptr++":")
              [show cond++" ~> "++show ptr'
              | (cond,ptr') <- cases ]
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