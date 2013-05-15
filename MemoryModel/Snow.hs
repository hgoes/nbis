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
    let mem1 = mem { snowProgram = prog++(snowProgram mem)
                   , snowLocations = case snowProgram mem of
                        [] -> Map.insert start_loc (snowGlobal mem) (snowLocations mem)
                        _ -> snowLocations mem
                   }
    foldlM (\cmem instr -> do
               (obj_upd',ptr_upd',next) <- initUpdates (snowStructs cmem) (snowNextObject cmem) instr
               let cmem1 = cmem { snowNextObject = next }
               applyUpdates
                 (case ptr_upd' of
                     Nothing -> []
                     Just up -> [up])
                 (case obj_upd' of
                     Nothing -> []
                     Just up -> [up]) (snowProgram cmem1) cmem1
           ) mem1 prog
  connectLocation mem cond loc_from loc_to ptrs = do
    trace ("Connecting "++show loc_from++" with "++show loc_to++" "++show ptrs) $ return ()
    let cloc = case Map.lookup loc_from (snowLocations mem) of
          Just l -> l
          Nothing -> error $ "Couldn't find location "++show loc_from --SnowLocation Map.empty Map.empty
        mem1 = mem { snowPointerConnections = foldl (\mp (p1,p2) -> Map.insertWith (++) p1 [(p2,cond)] mp) (snowPointerConnections mem) ptrs
                   , snowLocationConnections = Map.insertWith (++) loc_from [(loc_to,cond)] (snowLocationConnections mem)
                   }
        ptr_upd = [ (loc_to,ptr,assign) | (ptr,assign) <- Map.toList $ snowPointer cloc ]
        obj_upd = [ (loc_to,obj,assign) | (obj,assign) <- Map.toList $ snowObjects cloc ]
    applyUpdates ptr_upd obj_upd (snowProgram mem1) mem1
  debugMem mem _ _ = snowDebug mem

applyUpdates :: (Ord ptr,Ord mloc,Show mloc,Show ptr) => [PointerUpdate mloc ptr] -> [ObjectUpdate mloc ptr] -> [MemoryInstruction mloc ptr] -> SnowMemory mloc ptr -> SMT (SnowMemory mloc ptr)
applyUpdates ptr_upds obj_upds instrs mem = applyUpdates' ptr_upds obj_upds [] instrs mem
  --mem1 <- foldlM (\cmem obj_upd -> applyObjectUpdate obj_upd cmem) mem (concat $ fmap (connectObjectUpdate (snowLocationConnections mem)) obj_upds)
  --mem2 <- foldlM (\cmem ptr_upd -> applyPointerUpdate ptr_upd cmem) mem1 (concat $ fmap (connectPointerUpdate (snowLocationConnections mem1) (snowPointerConnections mem1)) ptr_upds)
  --return mem2

applyUpdates' :: (Ord ptr,Ord mloc,Show mloc,Show ptr) => [PointerUpdate mloc ptr] -> [ObjectUpdate mloc ptr] -> [MemoryInstruction mloc ptr] -> [MemoryInstruction mloc ptr] -> SnowMemory mloc ptr -> SMT (SnowMemory mloc ptr)
applyUpdates' _ _ _ [] mem = return mem
applyUpdates' ptr_upds obj_upds done (i:is) mem = do
  let loc = memInstrSrc i
      (loc_objs,loc_ptrs) = case Map.lookup loc (snowLocations mem) of
        Just (SnowLocation { snowObjects = x
                           , snowPointer = y }) -> (x,y)
        Nothing -> (Map.empty,Map.empty)
  r1 <- foldlM (\(cobj_up,cptr_up) ptr_upd -> do
                   (obj_upd',ptr_upd') <- updatePointer (snowStructs mem) loc_ptrs loc_objs ptr_upd i
                   return (obj_upd'++cobj_up,
                           case ptr_upd' of
                             Nothing -> cptr_up
                             Just up -> up:cptr_up)
               ) ([],[]) ptr_upds
  (nobj_upd,nptr_upd) <- foldlM (\(cobj_up,cptr_up) obj_upd -> do
                                    (obj_upd',ptr_upd') <- updateObject (snowStructs mem) loc_ptrs loc_objs obj_upd i
                                    return (obj_upd'++cobj_up,
                                            case ptr_upd' of
                                              Nothing -> cptr_up
                                              Just up -> up:cptr_up)
                                ) r1 obj_upds
  let nobj_upd' = concat $ fmap (connectObjectUpdate (snowLocationConnections mem)) nobj_upd
      nptr_upd' = concat $ fmap (connectPointerUpdate (snowLocationConnections mem) (snowPointerConnections mem)) nptr_upd
  mem1 <- applyUpdates nptr_upd' nobj_upd' done mem
  applyUpdates' (ptr_upds++nptr_upd') (obj_upds++nobj_upd') (done++[i]) is mem1

connectPointerUpdate :: (Ord ptr,Ord mloc)
                         => Map mloc [(mloc,SMTExpr Bool)]
                         -> Map ptr [(ptr,SMTExpr Bool)]
                         -> PointerUpdate mloc ptr
                         -> [PointerUpdate mloc ptr]
connectPointerUpdate conns_loc conns_ptr x@(loc,ptr,assign)
  = let res_loc = case Map.lookup loc conns_loc of
          Nothing -> []
          Just locs -> [ (loc',ptr,assign)
                       | (loc',_) <- locs ]
        res_ptr = case Map.lookup ptr conns_ptr of
          Nothing -> []
          Just ptrs -> [ (loc,ptr',[(cond' .&&. cond,trg)
                                   | (cond,trg) <- assign ])
                       | (ptr',cond') <- ptrs ]
    in x:(concat $ fmap (connectPointerUpdate conns_loc conns_ptr) (res_loc++res_ptr))

connectObjectUpdate :: Ord mloc
                       => Map mloc [(mloc,SMTExpr Bool)]
                       -> ObjectUpdate mloc ptr
                       -> [ObjectUpdate mloc ptr]
connectObjectUpdate mp x@(loc,obj_p,assign) = case Map.lookup loc mp of
  Nothing -> [x]
  Just locs -> x:(concat $ fmap (connectObjectUpdate mp) 
                  [ (loc',obj_p,assign) | (loc',_) <- locs ])

type ObjectUpdate mloc ptr = (mloc,Integer,[(SMTExpr Bool,Object ptr)])
type PointerUpdate mloc ptr = (mloc,ptr,[(SMTExpr Bool,Maybe (Integer,PtrIndex))])

initUpdates :: Map String [TypeDesc]
                -> Integer
                -> MemoryInstruction mloc ptr
                -> SMT (Maybe (ObjectUpdate mloc ptr),
                        Maybe (PointerUpdate mloc ptr),
                        Integer)
initUpdates structs next_obj instr = case instr of
  MINull mfrom tp ptr mto -> return (Nothing,Just (mto,ptr,[(constant True,Nothing)]),next_obj)
  MIAlloc mfrom tp num ptr mto -> do
    obj <- allocaObject structs tp num
    return (Just (mto,next_obj,[(constant True,obj)]),
            Just (mto,ptr,[(constant True,Just (next_obj,[(tp,[])]))]),
            succ next_obj)
  _ -> return (Nothing,Nothing,next_obj)

updatePointer :: (Show ptr,Show mloc,Eq mloc,Ord ptr)
                 => Map String [TypeDesc]                             -- ^ All struct types
                 -> Map ptr [(SMTExpr Bool,Maybe (Integer,PtrIndex))] -- ^ All the pointers at the location (needed for pointer comparisons)
                 -> Map Integer [(SMTExpr Bool,Object ptr)]           -- ^ All objects at the location
                 -> PointerUpdate mloc ptr                            -- ^ The pointer update to be applied
                 -> MemoryInstruction mloc ptr
                 -> SMT ([ObjectUpdate mloc ptr],
                         Maybe (PointerUpdate mloc ptr))
updatePointer structs all_ptrs all_objs (loc,new_ptr,new_conds) instr = case instr of
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
      return ([],Nothing)
    | otherwise -> return ([],Nothing)
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
      case concat $ concat nptr of
        [] -> return ([],Nothing)
        xs -> return ([],Just (mto,ptr_to,xs))
    | otherwise -> return ([],Nothing)
  MIStore mfrom val ptr_to mto
    | mfrom==loc && ptr_to==new_ptr
      -> return ([ (mto,obj_p,[ (cond .&&. cond',nobj)
                              | (cond',obj) <- objs',
                                let (nobj,_,errs) = access (\obj' -> let (res,errs) = storeObject val obj'
                                                                     in (res,(),errs)
                                                           ) obj
                              ])
                 | (cond,Just (obj_p,idx)) <- new_conds,
                   let ObjAccessor access = ptrIndexGetAccessor structs idx
                       objs' = case Map.lookup obj_p all_objs of
                         Just x -> x
                         Nothing -> error $ "Can't find object "++show obj_p++" in "++show all_objs++" @"++show loc
                 ],Nothing)
    | otherwise -> return ([],Nothing)
  MIStorePtr mfrom ptr_from ptr_to mto
    | mfrom==loc && ptr_from==new_ptr -> case Map.lookup ptr_to all_ptrs of
      Just dests -> return ([ (mto,obj_p,[ (cond .&&. cond',nobj)
                                         | (cond',obj) <- objs',
                                           let (nobj,_,errs) = access (\obj' -> let (res,errs) = storePtr ptr_from obj'
                                                                                in (res,(),errs)
                                                                      ) obj
                                         ])
                            | (cond,Just (obj_p,idx)) <- dests,
                              let ObjAccessor access = ptrIndexGetAccessor structs idx
                                  Just objs' = Map.lookup obj_p all_objs
                            ],Nothing)
      Nothing -> return ([],Nothing)
    | mfrom==loc && ptr_to==new_ptr
      -> return ([ (mto,obj_p,[ (cond .&&. cond',nobj)
                              | (cond',obj) <- objs',
                                let (nobj,_,errs) = access (\obj' -> let (res,errs) = storePtr ptr_from obj'
                                                                     in (res,(),errs)
                                                           ) obj
                              ])
                 | (cond,Just (obj_p,idx)) <- new_conds,
                   let ObjAccessor access = ptrIndexGetAccessor structs idx
                       Just objs' = Map.lookup obj_p all_objs
                 ],Nothing)
    | otherwise -> return ([],Nothing)
  MICompare mfrom p1 p2 res
    | mfrom==loc && p1==new_ptr -> case Map.lookup p2 all_ptrs of
      Just a2 -> compare' new_conds a2
      Nothing -> return ([],Nothing)
    | mfrom==loc && p2==new_ptr -> case Map.lookup p1 all_ptrs of
      Just a1 -> compare' new_conds a1
      Nothing -> return ([],Nothing)
    | otherwise -> return ([],Nothing)
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
        return ([],Nothing)
  MISelect mfrom cases ptr_to mto
    | mfrom==loc -> case List.find (\(_,ptr_from) -> ptr_from==new_ptr) cases of
      Nothing -> return ([],Nothing)
      Just (cond,_) -> return ([],Just (mto,ptr_to,[(cond .&&. cond',src)
                                                   | (cond',src) <- new_conds ]))
    | otherwise -> return ([],Nothing)
  MICast mfrom tp_from tp_to ptr_from ptr_to mto
    | mfrom==loc && ptr_from==new_ptr 
      -> return ([],Just (mto,ptr_to,[ case src of
                                          Nothing -> (c,Nothing)
                                          Just (obj_p,idx) -> (c,Just (obj_p,ptrIndexCast structs tp_to idx))
                                     | (c,src) <- new_conds ]))
    | otherwise -> return ([],Nothing)
  MIIndex mfrom idx ptr_from ptr_to mto
    | mfrom==loc && ptr_from==new_ptr
      -> return ([],Just (mto,ptr_to,[ case src of
                                          Nothing -> (c,Nothing)
                                          Just (obj_p,idx') -> (c,Just (obj_p,ptrIndexIndex idx idx'))
                                     | (c,src) <- new_conds ]))
    | otherwise -> return ([],Nothing)
  _ -> return ([],Nothing)

updateObject :: (Eq mloc,Ord ptr,Show ptr)
                => Map String [TypeDesc]
                -> Map ptr [(SMTExpr Bool,Maybe (Integer,PtrIndex))]
                -> Map Integer [(SMTExpr Bool,Object ptr)]
                -> ObjectUpdate mloc ptr
                -> MemoryInstruction mloc ptr
                -> SMT ([ObjectUpdate mloc ptr],Maybe (PointerUpdate mloc ptr))
updateObject structs all_ptrs all_objs (loc,new_obj,new_conds) instr = case instr of
  MILoad mfrom ptr res
    | mfrom==loc -> case Map.lookup ptr all_ptrs of
      Just srcs -> do
        let sz = extractAnnotation res
        mapM_ (\(cond,src) -> case src of
                  Nothing -> return ()
                  Just (obj_p,idx) -> if obj_p==new_obj
                                      then mapM_ (\(cond',obj) -> do
                                                     let ObjAccessor access = ptrIndexGetAccessor structs idx
                                                         (_,loaded,errs) = access 
                                                                           (\obj' -> let (res,errs) = loadObject sz obj'
                                                                                     in (obj',res,errs)
                                                                           ) obj
                                                     assert $ (cond .&&. cond') .=>. (res .==. loaded)
                                                 ) new_conds
                                      else return ()
              ) srcs
        return ([],Nothing)
    | otherwise -> return ([],Nothing)
  MILoadPtr mfrom ptr_from ptr_to mto
    | mfrom==loc -> case Map.lookup ptr_from all_ptrs of
      Just srcs -> do
        let nptr = [ case src of
                        Nothing -> []
                        Just (obj_p,idx) -> if obj_p==new_obj
                                            then [ case loaded of
                                                      Nothing -> [(cond .&&. cond',Nothing)]
                                                      Just p -> case Map.lookup p all_ptrs of
                                                        Just dests -> [ (and' `app` [cond,cond',cond''],dest) 
                                                                      | (cond'',dest) <- dests ]
                                                 | (cond',obj) <- new_conds
                                                 , let ObjAccessor access = ptrIndexGetAccessor structs idx
                                                       (_,loaded,errs) = access
                                                                         (\obj' -> let (res,errs) = loadPtr obj'
                                                                                   in (obj',res,errs)
                                                                         ) obj
                                                 ]
                                            else []
                   | (cond,src) <- srcs
                   ]
        return ([(mto,new_obj,new_conds)],
                case concat $ concat nptr of
                  [] -> Nothing
                  xs -> Just (mto,ptr_to,xs))
    | otherwise -> return ([],Nothing)
  MIStore mfrom val ptr mto
    | mfrom==loc -> case Map.lookup ptr all_ptrs of
      Just trgs -> return
                   ([(mto,new_obj,concat
                                  [ if obj_p==new_obj
                                    then concat
                                         [ [((not' cond) .&&. cond',obj)
                                           ,(cond .&&. cond',nobj)]
                                         | (cond',obj) <- new_conds
                                         , let (nobj,_,errs) = access (\obj' -> let (res,errs) = storeObject val obj'
                                                                                in (res,(),errs)
                                                                      ) obj
                                         ]
                                    else [ (cond .&&. cond',obj) | (cond',obj) <- new_conds ]
                                  | (cond,Just (obj_p,idx)) <- trgs
                                  , let ObjAccessor access = ptrIndexGetAccessor structs idx ])],Nothing)
      Nothing -> return ([(mto,new_obj,new_conds)],Nothing)
    | otherwise -> return ([],Nothing)
  _ -> return $ if memInstrSrc instr == loc
                then (case memInstrTrg instr of
                         Nothing -> ([],Nothing)
                         Just trg -> ([(trg,new_obj,new_conds)],Nothing))
                else ([],Nothing)

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