{- | A circuit in a graph is a circle in which no node is contained more than once.
     The algorithm here is adapted from the paper "Finding all the elementary
     circuits of a directed graph" by Donald B. Johnson.
-}
module Circuit (circuits) where

import Data.Graph.Inductive as Gr
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Traversable

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