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

data BlockSig = BlockSig 
                { blockPhis :: Map (Ptr Instruction) (TypeDesc,Set (Ptr BasicBlock))
                , blockInputs :: Map (Ptr Instruction) TypeDesc
                , blockInputArguments :: Map (Ptr Argument) TypeDesc
                , blockOutputs :: Map (Ptr Instruction) TypeDesc
                , blockJumps :: Set (Ptr BasicBlock,Integer)
                , blockOrigins :: Set (Ptr BasicBlock,Integer)
                } deriving (Show)

emptyBlockSig :: BlockSig
emptyBlockSig = BlockSig { blockPhis = Map.empty
                         , blockInputs = Map.empty
                         , blockInputArguments = Map.empty
                         , blockOutputs = Map.empty
                         , blockJumps = Set.empty
                         , blockOrigins = Set.empty
                         }

mergeBlockSig :: BlockSig -> BlockSig -> BlockSig
mergeBlockSig b1 b2 = BlockSig { blockPhis = Map.unionWith (\(tp,s1) (_,s2) 
                                                            -> (tp,Set.union s1 s2)
                                                           ) (blockPhis b1) (blockPhis b2)
                               , blockInputs = Map.union (blockInputs b1) (blockInputs b2)
                               , blockInputArguments = Map.union (blockInputArguments b1) (blockInputArguments b2)
                               , blockOutputs = Map.union (blockOutputs b1) (blockOutputs b2)
                               , blockJumps = Set.union (blockJumps b1) (blockJumps b2)
                               , blockOrigins = Set.union (blockOrigins b1) (blockOrigins b2)
                               }

showBlockSig :: String -> BlockSig -> [String]
showBlockSig fname sig
  = fname:
    (renderMap "inputs" renderType (blockInputs sig)) ++
    (renderMap "phis" (\name (tp,from) -> show name++" : "++show tp++" <- "++show (Set.toList from)) (blockPhis sig)) ++
    (renderMap "outputs" renderType (blockOutputs sig))++
    --(renderMap "globals" renderType (blockGlobals sig))++
    (renderMap "arguments" renderType (blockInputArguments sig))++
    (renderSet "jumps" renderBlk (blockJumps sig))++
    (renderSet "origins" renderBlk (blockOrigins sig))
  where
    renderType name tp = show name++" : "++show tp
    renderBlk blk 0 = show blk
    renderBlk blk sblk = show blk++"."++show sblk
    renderList :: String -> (b -> c -> String) -> [(b,c)] -> [String]
    renderList name f [] = []
    renderList name f lst = ("  "++name):["    " ++ f iname cont | (iname,cont) <- lst ]
    renderMap name f mp = renderList name f (Map.toList mp)
    renderSet name f st = renderList name f (Set.toList st)

mkBlockSigs :: [(Ptr BasicBlock,[[InstrDesc Operand]])] 
               -> Map (Ptr BasicBlock,Integer) BlockSig
mkBlockSigs instrs
  = let (origins,(preds,succs),phis) 
          = foldInstrs (\(orig,succ,phi) blk sblk instr 
                        -> (getVariableOrigins orig blk sblk instr,
                            getSuccessors succ blk sblk instr,
                            getPhis' phi blk sblk instr)
                       ) (Map.empty,(Map.empty,Map.empty),Map.empty) instrs
        (_,(inps,args,outps)) = foldInstrs (getInputOutput origins succs) (Set.empty,(Map.empty,Map.empty,Map.empty)) instrs
        sigs_preds = fmap (\pred -> emptyBlockSig { blockOrigins = pred }) preds
        sigs_succs = fmap (\succ -> emptyBlockSig { blockJumps = succ }) succs
        sigs_inps = fmap (\inp -> emptyBlockSig { blockInputs = inp }) inps
        sigs_outps = fmap (\outp -> emptyBlockSig { blockOutputs = outp }) outps
        sigs_phis = fmap (\phi -> emptyBlockSig { blockPhis = phi }) phis
        sigs_args = fmap (\arg -> emptyBlockSig { blockInputArguments = arg }) args
    in Map.unionsWith mergeBlockSig [sigs_preds,sigs_succs,sigs_inps,sigs_outps,sigs_phis,sigs_args]

getVariableOrigins :: Map (Ptr Instruction) (Ptr BasicBlock,Integer) -> Ptr BasicBlock -> Integer -> InstrDesc Operand
                      -> Map (Ptr Instruction) (Ptr BasicBlock,Integer)
getVariableOrigins mp blk sblk instr
  = case instr of
    IAssign trg _ _ -> Map.insert trg (blk,sblk) mp
    ITerminator (ICall trg _ _) -> Map.insert trg (blk,sblk) mp
    _ -> mp

getSuccessors :: (Map (Ptr BasicBlock,Integer) (Set (Ptr BasicBlock,Integer)),Map (Ptr BasicBlock,Integer) (Set (Ptr BasicBlock,Integer))) -> Ptr BasicBlock -> Integer -> InstrDesc Operand
                 -> (Map (Ptr BasicBlock,Integer) (Set (Ptr BasicBlock,Integer)),Map (Ptr BasicBlock,Integer) (Set (Ptr BasicBlock,Integer)))
getSuccessors mp blk sblk instr
  = case instr of
    ITerminator (IBr trg) -> jump blk sblk (Set.singleton (trg,0)) mp
    ITerminator (IBrCond _ t1 t2) -> jump blk sblk (Set.fromList [(t1,0),(t2,0)]) mp      
    ITerminator (ISwitch _ def cases) -> jump blk sblk (Set.fromList $ (def,0):(fmap (\(_,trg) -> (trg,0)) cases)) mp
    ITerminator (ICall _ _ _) -> jump blk sblk (Set.singleton (blk,sblk+1)) mp
    _ -> mp
    where
      jump blk sblk trgs (pred,succ) = (foldl (\pred' (blk',sblk') -> Map.insertWith Set.union (blk',sblk') (Set.singleton (blk,sblk)) pred') pred trgs,
                                        Map.insertWith Set.union (blk,sblk) trgs succ)

getPhis' :: Map (Ptr BasicBlock,Integer) (Map (Ptr Instruction) (TypeDesc,Set (Ptr BasicBlock))) -> Ptr BasicBlock -> Integer -> InstrDesc Operand
           -> Map (Ptr BasicBlock,Integer) (Map (Ptr Instruction) (TypeDesc,Set (Ptr BasicBlock)))
getPhis' mp blk sblk instr = case instr of
  IAssign trg _ (IPhi froms) -> let ((_,e1):_) = froms
                                in Map.insertWith Map.union (blk,sblk)
                                   (Map.singleton trg (operandType e1,Set.fromList $ fmap fst froms)) mp
  _ -> mp

intermediateBlocks :: (Ptr BasicBlock,Integer) -> (Ptr BasicBlock,Integer) -> Map (Ptr BasicBlock,Integer) (Set (Ptr BasicBlock,Integer)) -> Set (Ptr BasicBlock,Integer)
intermediateBlocks from to mp = case Map.lookup from mp of
  Nothing -> Set.empty
  Just succ -> fst $ foldl (\(connected,visited) cur 
                            -> inter cur Set.empty connected visited
                           ) (Set.empty,Set.empty) succ
  where
    inter cur path connected visited 
      | Set.member cur connected = (Set.union connected path,visited)
      | cur == to && Set.member cur visited = (Set.union connected path,visited)
      | cur == to = foldl (\(connected',visited') cur'
                           -> inter cur' (Set.singleton to) connected' visited'
                          ) (Set.union connected path,Set.insert cur visited)
                    (case Map.lookup cur mp of
                        Nothing -> Set.empty
                        Just succ -> succ)
      | Set.member cur visited = (connected,visited)
      | otherwise = foldl (\(connected',visited') cur'
                           -> inter cur' (Set.insert cur path) connected' visited'
                          ) (connected,Set.insert cur visited)
                    (case Map.lookup cur mp of
                        Nothing -> Set.empty
                        Just succ -> succ)

getInputOutput :: Map (Ptr Instruction) (Ptr BasicBlock,Integer)
                  -> Map (Ptr BasicBlock,Integer) (Set (Ptr BasicBlock,Integer)) 
                  -> (Set (Ptr Instruction),(Map (Ptr BasicBlock,Integer) (Map (Ptr Instruction) TypeDesc),
                                             Map (Ptr BasicBlock,Integer) (Map (Ptr Argument) TypeDesc),
                                             Map (Ptr BasicBlock,Integer) (Map (Ptr Instruction) TypeDesc)))
                  -> Ptr BasicBlock -> Integer -> InstrDesc Operand
                  -> (Set (Ptr Instruction),(Map (Ptr BasicBlock,Integer) (Map (Ptr Instruction) TypeDesc),
                                             Map (Ptr BasicBlock,Integer) (Map (Ptr Argument) TypeDesc),
                                             Map (Ptr BasicBlock,Integer) (Map (Ptr Instruction) TypeDesc)))
getInputOutput origins succ (local,mp) blk sblk instr
  = case instr of
    ITerminator IRetVoid -> (Set.empty,mp)
    ITerminator (IRet e) -> (Set.empty,addExpr e mp)
    ITerminator (IBr _) -> (Set.empty,mp)
    ITerminator (IBrCond cond _ _) -> (Set.empty,addExpr cond mp)
    ITerminator (ISwitch val _ cases) -> (Set.empty,addExpr val $ foldr addExpr mp (fmap fst cases))
    IAssign trg _ expr -> (Set.insert trg local,case expr of
                              IBinaryOperator _ lhs rhs -> addExpr lhs $
                                                           addExpr rhs mp
                              IFCmp _ lhs rhs -> addExpr lhs $
                                                 addExpr rhs mp
                              IICmp _ lhs rhs -> addExpr lhs $
                                                 addExpr rhs mp
                              IGetElementPtr ptr idx -> addExpr ptr $ foldr addExpr mp idx
                              IPhi cases -> foldr addExpr mp (fmap snd cases)
                              ISelect x y z -> addExpr x $
                                               addExpr y $
                                               addExpr z mp
                              ILoad ptr -> addExpr ptr mp
                              IBitCast _ p -> addExpr p mp
                              ISExt _ p -> addExpr p mp
                              ITrunc _ p -> addExpr p mp
                              IZExt _ p -> addExpr p mp
                              IAlloca _ sz -> case sz of
                                Nothing -> mp
                                Just sz' -> addExpr sz' mp
                              IMalloc _ sz _ -> addExpr sz mp
                          )
    IStore e ptr -> (local,addExpr e $ addExpr ptr mp)
    ITerminator (ICall _ _ args) -> (Set.empty,foldr addExpr mp args)
    _ -> error $ "Implement getInputOutput for "++show instr
    where
      addExpr :: Operand -> (Map (Ptr BasicBlock,Integer) (Map (Ptr Instruction) TypeDesc),
                             Map (Ptr BasicBlock,Integer) (Map (Ptr Argument) TypeDesc),
                             Map (Ptr BasicBlock,Integer) (Map (Ptr Instruction) TypeDesc))
                 -> (Map (Ptr BasicBlock,Integer) (Map (Ptr Instruction) TypeDesc),
                     Map (Ptr BasicBlock,Integer) (Map (Ptr Argument) TypeDesc),
                     Map (Ptr BasicBlock,Integer) (Map (Ptr Instruction) TypeDesc))
      addExpr e mp@(inp,args,outp) = case operandDesc e of
        ODInstr name _ _
          -> if Set.member name local
             then mp
             else case Map.lookup name origins of
               Nothing -> mp
               Just (blk',sblk') -> foldl (\(inp',args',outp') inter -> (Map.insertWith Map.union inter (Map.singleton name (operandType e)) inp',
                                                                         args',
                                                                         Map.insertWith Map.union inter (Map.singleton name (operandType e)) outp')
                                          ) 
                                    (Map.insertWith Map.union (blk,sblk) (Map.singleton name (operandType e)) inp,
                                     args,
                                     Map.insertWith Map.union (blk',sblk') (Map.singleton name (operandType e)) outp)
                                    (intermediateBlocks (blk',sblk') (blk,sblk) succ)
        ODArgument arg -> (inp,Map.insertWith Map.union (blk,sblk) (Map.singleton arg (operandType e)) args,outp)
        ODGlobal _ -> mp
        ODInt _ -> mp
        ODUndef -> mp
        ODNull -> mp
        ODMetaData _ -> mp
        ODGetElementPtr ptr idx -> foldr addExpr (addExpr ptr mp) idx
        e' -> error $ "Implement addExpr for "++show e'

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