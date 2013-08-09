{- | A circuit in a graph is a circle in which no node is contained more than once.
     The algorithm here is adapted from the paper "Finding all the elementary
     circuits of a directed graph" by Donald B. Johnson.
-}
module Circuit (circuits,safeMergePoints) where

import Data.Graph.Inductive as Gr
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Traversable
import Data.Ord (comparing)

-- | Finds all elementary circuits of a given graph.
circuits :: Graph gr => gr a b -> [[Node]]
circuits gr = concat $ fmap (\nd -> let (circs,_,_) = circuit gr nd nd [] Set.empty Map.empty in circs) (Gr.nodes gr)

circuit :: Graph gr => gr a b -> Node -> Node -> [Node] -> Set Node -> Map Node (Set Node) -> ([[Node]],Set Node,Map Node (Set Node))
circuit gr start v stack blocked b = (res,nnblocked,nnb)
  where
    succs = Gr.suc gr v
    
    (nnblocked,nnb) = if List.null res
                      then (nblocked,foldl (\cb w -> if w<start
                                                     then cb
                                                     else Map.alter (\el -> case el of
                                                                        Nothing -> Just $ Set.singleton v
                                                                        Just el' -> Just $ Set.insert v el'
                                                                    ) w cb
                                           ) nb succs)
                      else unblock v nblocked nb
    
    (res,nblocked,nb) = circuit' (v:stack) (Set.insert v blocked) b succs
    
    circuit' :: [Node] -> Set Node -> Map Node (Set Node) -> [Node] -> ([[Node]],Set Node,Map Node (Set Node))
    circuit' stack blocked b [] = ([],blocked,b)
    circuit' stack blocked b (w:ws)
      | w<start = circuit' stack blocked b ws
      | w==start = let (res,blocked',b') = circuit' stack blocked b ws
                   in (stack:res,blocked',b')
      | not $ Set.member w blocked = let (res,blocked',b') = circuit gr start w stack blocked b
                                         (res',blocked'',b'') = circuit' stack blocked' b' ws
                                     in (res++res',blocked'',b'')
      | otherwise = circuit' stack blocked b ws

unblock :: Node -> Set Node -> Map Node (Set Node) -> (Set Node,Map Node (Set Node))
unblock u blocked b = case Map.updateLookupWithKey (\_ _ -> Nothing) u b of
  (Just cb,nb) -> unblock' (Set.delete u blocked) nb cb
  (Nothing,_) -> (Set.delete u blocked,b)
  where
    unblock' blocked' b' = Set.foldl (\(cblocked,cb) w -> if Set.member w cblocked
                                                          then unblock w cblocked cb
                                                          else (cblocked,cb)
                                     ) (blocked',b')

-- | Find all nodes which can be reached within one step from a circuit, but aren't part of it
circuitExits :: Graph gr => gr a b -> [Node] -> [Node]
circuitExits gr circ = exits' circ
  where
    exits' [] = []
    exits' (x:xs) = (filter (\nd -> not $ elem nd circ) $ Gr.suc gr x) ++ (exits' xs)

safeMergePoints :: Graph gr => gr a b -> [Node]
safeMergePoints gr = get_merges possible_merges
  where
    circs = circuits gr
    possible_merges = [ [ circ_succ | circ_nd <- circ
                                    , circ_succ <- Gr.suc gr circ_nd
                                    , not $ elem circ_succ circ
                                    , all (\circ' -> if elem circ_succ circ'
                                                     then all (\circ_nd' -> elem circ_nd' circ') circ
                                                     else True
                                          ) circs ]
                      | circ <- circs ]
    count_apperance = foldl (foldl (\cmp' nd -> Map.insertWith (+) nd 1 cmp')) Map.empty
    get_most_appering mp = fst $ List.maximumBy (comparing $ \(_,n) -> n) $ Map.toList mp
    remove_merge nd (x:xs) = if elem nd x
                             then remove_merge nd xs
                             else x:remove_merge nd xs
    remove_merge nd [] = []
    get_merges lst = case filter (not . null) lst of
      [] -> []
      xs -> let nd = get_most_appering (count_apperance lst)
                lst' = remove_merge nd lst
            in nd:get_merges lst'

-- | The test graph from the paper "Enumerating Circuits and Loops in Graphs with Self-Arcs and Multiple-Arcs".
testGraph1 :: Gr.Gr () ()
testGraph1 = Gr.mkGraph
             [ (nd,()) | nd <- [0..15] ]
             [ (n1,n2,()) | (n1,n2) <- [(0,2),(0,10),(0,14)
                                       ,(1,5),(1,8)
                                       ,(2,7),(2,9)
                                       ,(3,3),(3,4),(3,6)
                                       ,(4,5),(4,13),(4,15)
                                       ,(6,13)
                                       ,(8,8),(8,0),(8,4)
                                       ,(9,9)
                                       ,(10,11),(10,7)
                                       ,(11,6)
                                       ,(12,12),(12,14),(12,10),(12,2),(12,1)
                                       ,(13,3),(13,12),(13,15)
                                       ,(14,11)
                                       ,(15,0)]]

correctness :: Bool
correctness = (circuits testGraph1) == [[15,13,6,11,14,0],[15,4,8,1,12,13,6,11,14,0],[8,1,12,13,6,11,14,0],[15,4,3,13,6,11,14,0],[15,13,6,11,10,0],[15,4,8,1,12,13,6,11,10,0],[8,1,12,13,6,11,10,0],[15,4,3,13,6,11,10,0],[12,13,4,8,1],[13,6,3],[13,4,3],[3],[11,14,12,13,6],[11,10,12,13,6],[8],[9],[12]]