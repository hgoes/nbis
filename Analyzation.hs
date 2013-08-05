module Analyzation where

import Data.Map as Map hiding (foldl,foldr)
import Data.Set as Set hiding (foldl,foldr)
import Prelude hiding (foldl,foldr,concat,all,any,elem)
import Data.Foldable
import Data.List as List (mapAccumL,lookup,find,filter)
import InstrDesc
import TypeDesc
import LLVM.FFI.Instruction
import LLVM.FFI.BasicBlock
import LLVM.FFI.Value
import Foreign.Ptr
import qualified Data.Graph.Inductive as Gr

foldInstrs :: (a -> Ptr BasicBlock -> Integer -> InstrDesc Operand -> a) -> a -> [(Ptr BasicBlock,[[InstrDesc Operand]])] -> a
foldInstrs f = foldl (\x1 (blk,sblks) 
                      -> snd $ foldl (\(sblk,x2) instrs
                                      -> (sblk+1,foldl (\x3 instr -> f x3 blk sblk instr) x2 instrs)
                                     ) (0,x1) sblks
                     )

getDefiningBlocks :: (String -> Bool) -> [(Ptr BasicBlock,Maybe String,[[InstrDesc Operand]])] -> Map (Ptr Instruction) (Ptr BasicBlock,Integer)
getDefiningBlocks isIntr
  = foldl (\mp1 (blk,_,sblks)
           -> foldl (\mp2 (instrs,sblk)
                     -> foldl (\mp3 instr -> case instr of
                                  IAssign trg _ _ -> Map.insert trg (blk,sblk) mp3
                                  ITerminator (ICall trg fun _) -> case operandDesc fun of
                                    ODFunction _ fname _ -> if isIntr fname
                                                            then Map.insert trg (blk,sblk) mp3
                                                            else Map.insert trg (blk,sblk+1) mp3
                                  _ -> mp3
                              ) mp2 instrs
                    ) mp1 (zip sblks [0..])
          ) Map.empty

getPhis :: [InstrDesc a] -> Map (Ptr Instruction) [(Ptr BasicBlock,a)]
getPhis = foldl (\mp instr -> case instr of
                    IAssign trg _ (IPhi blks) -> Map.insert trg blks mp
                    _ -> mp) Map.empty

data ProgramGraph gr = ProgramGraph { programGraph :: gr (Ptr BasicBlock,Maybe String,Integer,[InstrDesc Operand]) ()
                                    , nodeMap :: Map (Ptr BasicBlock,Integer) Gr.Node
                                    , arguments :: [(Ptr Argument,TypeDesc)]
                                    }

programAsGraph :: Gr.DynGraph gr => [(Ptr BasicBlock,Maybe String,[[InstrDesc Operand]])]
               -> [(Ptr Argument,TypeDesc)]
               -> ProgramGraph gr
programAsGraph prog args = createEdges $ createNodes (ProgramGraph Gr.empty Map.empty args) prog
  where
    createNodes res [] = res
    createNodes res ((blk,blk_name,sblks):rest)
      = createNodes (foldl (\cgr (instrs,sblk)
                            -> let [nnode] = Gr.newNodes 1 (programGraph cgr)
                               in cgr { programGraph = Gr.insNode (nnode,(blk,blk_name,sblk,instrs)) (programGraph cgr)
                                      , nodeMap = Map.insert (blk,sblk) nnode (nodeMap cgr) }
                           ) res (zip sblks [0..])
                    ) rest

    createEdges gr = gr { programGraph = Gr.ufold (\(_,node,(blk,blk_name,sblk,instrs),_) cgr
                                                   -> case last instrs of
                                                     ITerminator term -> case term of
                                                       IRetVoid -> cgr
                                                       IRet _ -> cgr
                                                       IBr trg -> case Map.lookup (trg,0) (nodeMap gr) of
                                                         Just tnd -> Gr.insEdge (node,tnd,()) cgr
                                                       IBrCond _ l r -> case (Map.lookup (l,0) (nodeMap gr),Map.lookup (r,0) (nodeMap gr)) of
                                                         (Just t1,Just t2) -> Gr.insEdges [(node,t1,()),(node,t2,())] cgr
                                                       ISwitch _ def cases -> case Map.lookup (def,0) (nodeMap gr) of
                                                         Just tdef -> Gr.insEdge (node,tdef,())
                                                                      (foldl (\cgr' (_,c) -> case Map.lookup (c,0) (nodeMap gr) of
                                                                                 Just t -> Gr.insEdge (node,t,()) cgr'
                                                                             ) cgr cases)
                                                       ICall _ _ _ -> case Map.lookup (blk,sblk+1) (nodeMap gr) of
                                                         Just trg -> Gr.insEdge (node,trg,()) cgr
                                                  ) (programGraph gr) (programGraph gr) }

programSCCs :: Gr.Graph gr => ProgramGraph gr -> [[Gr.Node]]
programSCCs pgr = let sccs = Gr.scc (programGraph pgr)
                  in List.filter (\comp -> case comp of
                                     [nd] -> nd `elem` (Gr.suc (programGraph pgr) nd)
                                     _ -> True) sccs

programOrder :: Gr.Graph gr => ProgramGraph gr -> [Gr.Node]
programOrder gr = case Gr.dff [0] (programGraph gr) of
  [dfs_tree] -> reverse $ Gr.postorder dfs_tree

-- | Can there ever only be one connection between two nodes?
singletonConnection :: Gr.Graph gr => Gr.Node -> Gr.Node -> [[Gr.Node]] -> gr a b -> Bool
singletonConnection nfrom nto sccs gr = case List.find (elem nfrom) sccs of
  Nothing -> True
  Just comp -> isLoopCenter nfrom comp gr || isLoopCenter nto comp gr

isLoopCenter :: Gr.Graph gr => Gr.Node -> [Gr.Node] -> gr a b -> Bool
isLoopCenter nd comp gr = returnsOnlyTo nd Set.empty
  where
    returnsOnlyTo cur seen = all (\succ -> if succ==nd
                                           then True
                                           else (if elem succ comp
                                                 then (if Set.member succ seen
                                                       then False
                                                       else returnsOnlyTo succ (Set.insert cur seen))
                                                 else False)
                                 ) (Gr.suc gr cur)

isSelfLoop :: Gr.Graph gr => Gr.Node -> gr a b -> Bool
isSelfLoop nd gr = any (==nd) (Gr.suc gr nd)

getReachability :: Gr.DynGraph gr => gr a b -> gr (a,Map Gr.Node (Set [Gr.Node])) b
getReachability gr = getReachability' (Gr.nmap (\x -> (x,Map.empty)) gr) [(t,Map.singleton f (Set.singleton [])) | (f,t) <- Gr.edges gr]
  where
    getReachability' gr [] = gr
    getReachability' gr ((x,new):xs)
      = let (Just (inc,_,(el,reach),out),gr') = Gr.match x gr
            reach' = Map.unionWith Set.union reach new
            hasnew = size' reach /= size' reach'
            nxs = if hasnew
                  then fmap (\(_,s) -> (s,fmap (Set.map (x:) . Set.filter (not . elem s)) reach')
                            ) out ++ xs
                  else xs
            ngr = (inc,x,(el,reach'),out) Gr.& gr'
        in getReachability' ngr nxs
    size' mp = foldl (\i s -> i+Set.size s) 0 mp

hasLoopWithout :: Gr.Graph gr => (a -> Map Gr.Node (Set [Gr.Node])) -> Gr.Node -> Gr.Node -> gr a b -> Bool
hasLoopWithout f without nd gr = case Map.lookup nd (f cont) of
  Nothing -> False
  Just paths -> any (\path -> not $ without `elem` path) paths
  where
    Just cont = Gr.lab gr nd

data VariableInfo = VariableInfo
                    { variablesTransient :: Set (Ptr Instruction)
                    }

getVariableInfo :: Gr.DynGraph gr => (a -> [InstrDesc Operand]) -> (Ptr Instruction -> Gr.Node) -> gr (a,Map Gr.Node (Set [Gr.Node])) b -> gr (a,Map Gr.Node (Set [Gr.Node]),VariableInfo) b
getVariableInfo f g gr = updateGraph (Gr.nmap (\(nd,reach) -> (nd,reach,VariableInfo Set.empty)) gr) (Gr.nodes gr)
  where
    updateGraph gr [] = gr
    updateGraph gr (nd:nds)
      = let Just (x,reach,info) = Gr.lab gr nd
            instrs = f x
            deps = Map.keys $ getInstrsDeps instrs
            ngr = foldl (\gr1 dep
                         -> let Just paths = Map.lookup (g dep) reach
                            in foldl (foldl (\gr3 nd -> let (Just (inc,_,(i,reach',info'),out),gr4) = Gr.match nd gr3
                                                        in (inc,nd,(i,reach',info' { variablesTransient = Set.insert dep (variablesTransient info') }),out) Gr.& gr4
                                            )
                                     ) gr1 paths
                        ) gr deps
        in updateGraph ngr nds
