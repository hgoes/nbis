module Analyzation where

import Data.Map as Map hiding (foldl,foldr)
import Data.Set as Set hiding (foldl,foldr)
import Prelude hiding (foldl,foldr,concat,all,any)
import Data.Foldable
import Data.List as List (mapAccumL,lookup,elem)
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

programAsGraph :: Gr.DynGraph gr => [(Ptr BasicBlock,Maybe String,[[InstrDesc Operand]])]
                  -> (gr (Ptr BasicBlock,Maybe String,Integer,[InstrDesc Operand]) (),Map (Ptr BasicBlock,Integer) Gr.Node)
programAsGraph prog = createEdges $ createNodes (Gr.empty,Map.empty) prog
  where
    createNodes res [] = res
    createNodes res ((blk,blk_name,sblks):rest)
      = createNodes (foldl (\(cgr,cmp) (instrs,sblk)
                            -> let [nnode] = Gr.newNodes 1 cgr
                               in (Gr.insNode (nnode,(blk,blk_name,sblk,instrs)) cgr,Map.insert (blk,sblk) nnode cmp)
                           ) res (zip sblks [0..])
                    ) rest

    createEdges (gr,mp) = (Gr.ufold (\(_,node,(blk,blk_name,sblk,instrs),_) cgr
                                     -> case last instrs of
                                       ITerminator term -> case term of
                                         IRetVoid -> cgr
                                         IRet _ -> cgr
                                         IBr trg -> case Map.lookup (trg,0) mp of
                                           Just tnd -> Gr.insEdge (node,tnd,()) cgr
                                         IBrCond _ l r -> case (Map.lookup (l,0) mp,Map.lookup (r,0) mp) of
                                           (Just t1,Just t2) -> Gr.insEdges [(node,t1,()),(node,t2,())] cgr
                                         ISwitch _ def cases -> case Map.lookup (def,0) mp of
                                           Just tdef -> Gr.insEdge (node,tdef,())
                                                        (foldl (\cgr' (_,c) -> case Map.lookup (c,0) mp of
                                                                   Just t -> Gr.insEdge (node,t,()) cgr'
                                                               ) cgr cases)
                                         ICall _ _ _ -> case Map.lookup (blk,sblk+1) mp of
                                           Just trg -> Gr.insEdge (node,trg,()) cgr
                                    ) gr gr,mp)

isLoopCenter :: Gr.Graph gr => Gr.Node -> [Gr.Node] -> gr a b -> Bool
isLoopCenter nd comp gr = returnsOnlyTo nd Set.empty
  where
    returnsOnlyTo cur seen = all (\succ -> if succ==nd
                                           then True
                                           else (if List.elem succ comp
                                                 then (if Set.member succ seen
                                                       then False
                                                       else returnsOnlyTo succ (Set.insert cur seen))
                                                 else False)
                                 ) (Gr.suc gr cur)

isSelfLoop :: Gr.Graph gr => Gr.Node -> gr a b -> Bool
isSelfLoop nd gr = any (==nd) (Gr.suc gr nd)