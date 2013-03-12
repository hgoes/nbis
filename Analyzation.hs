module Analyzation where

import LLVM.Core hiding ((&))
import Data.Map as Map hiding (foldl,foldr)
import Data.Set as Set hiding (foldl,foldr)
import Prelude hiding (foldl,foldr,concat)
import Data.Foldable
import Data.List as List (mapAccumL,lookup)

data BlockSig = BlockSig 
                { blockPhis :: Map String (TypeDesc,Set String)
                , blockInputs :: Map String TypeDesc
                , blockInputArguments :: Map String TypeDesc
                , blockOutputs :: Map String TypeDesc
                , blockJumps :: Set (String,Integer)
                , blockOrigins :: Set (String,Integer)
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
    (renderMap "phis" (\name (tp,from) -> name++" : "++show tp++" <- "++show (Set.toList from)) (blockPhis sig)) ++
    (renderMap "outputs" renderType (blockOutputs sig))++
    --(renderMap "globals" renderType (blockGlobals sig))++
    (renderMap "arguments" renderType (blockInputArguments sig))++
    (renderSet "jumps" renderBlk (blockJumps sig))++
    (renderSet "origins" renderBlk (blockOrigins sig))
  where
    renderType name tp = name++" : "++show tp
    renderBlk blk 0 = blk
    renderBlk blk sblk = blk++"."++show sblk
    renderList name f [] = []
    renderList name f lst = ("  "++name):["    " ++ f iname cont | (iname,cont) <- lst ]
    renderMap name f mp = renderList name f (Map.toList mp)
    renderSet name f st = renderList name f (Set.toList st)

mkBlockSigs :: Set String -> [(String,[[Instruction]])] 
               -> Map (String,Integer) BlockSig
mkBlockSigs arguments instrs
  = let (origins,(preds,succs),phis) 
          = foldInstrs (\(orig,succ,phi) blk sblk instr 
                        -> (getVariableOrigins orig blk sblk instr,
                            getSuccessors succ blk sblk instr,getPhis phi blk sblk instr)
                       ) (Map.empty,(Map.empty,Map.empty),Map.empty) instrs
        (_,(inps,args,outps)) = foldInstrs (getInputOutput origins arguments succs) (Set.empty,(Map.empty,Map.empty,Map.empty)) instrs
        sigs_preds = fmap (\pred -> emptyBlockSig { blockOrigins = pred }) preds
        sigs_succs = fmap (\succ -> emptyBlockSig { blockJumps = succ }) succs
        sigs_inps = fmap (\inp -> emptyBlockSig { blockInputs = inp }) inps
        sigs_outps = fmap (\outp -> emptyBlockSig { blockOutputs = outp }) outps
        sigs_phis = fmap (\phi -> emptyBlockSig { blockPhis = phi }) phis
        sigs_args = fmap (\arg -> emptyBlockSig { blockInputArguments = arg }) args
    in Map.unionsWith mergeBlockSig [sigs_preds,sigs_succs,sigs_inps,sigs_outps,sigs_phis,sigs_args]

getVariableOrigins :: Map String (String,Integer) -> String -> Integer -> Instruction -> Map String (String,Integer)
getVariableOrigins mp blk sblk instr
  = case instr of
    IAssign trg _ -> Map.insert trg (blk,sblk) mp
    IAlloca trg _ _ _ -> Map.insert trg (blk,sblk) mp
    ILoad trg _ _ -> Map.insert trg (blk,sblk) mp
    IPhi trg _ -> Map.insert trg (blk,sblk) mp
    ICall _ trg _ _ _ -> Map.insert trg (blk,sblk) mp
    _ -> mp

getSuccessors :: (Map (String,Integer) (Set (String,Integer)),Map (String,Integer) (Set (String,Integer))) -> String -> Integer -> Instruction 
                 -> (Map (String,Integer) (Set (String,Integer)),Map (String,Integer) (Set (String,Integer)))
getSuccessors mp blk sblk instr
  = case instr of
    IBr trg -> jump blk sblk (Set.singleton (trg,0)) mp
    IBrCond _ t1 t2 -> jump blk sblk (Set.fromList [(t1,0),(t2,0)]) mp      
    ISwitch _ def cases -> jump blk sblk (Set.fromList $ (def,0):(fmap (\(_,trg) -> (trg,0)) cases)) mp
    ICall _ _ _ _ _ -> jump blk sblk (Set.singleton (blk,sblk+1)) mp
    _ -> mp
    where
      jump blk sblk trgs (pred,succ) = (foldl (\pred' (blk',sblk') -> Map.insertWith Set.union (blk',sblk') (Set.singleton (blk,sblk)) pred') pred trgs,
                                        Map.insertWith Set.union (blk,sblk) trgs succ)

getPhis :: Map (String,Integer) (Map String (TypeDesc,Set String)) -> String -> Integer -> Instruction
           -> Map (String,Integer) (Map String (TypeDesc,Set String))
getPhis mp blk sblk instr = case instr of
  IPhi trg froms -> let ((e1,_):_) = froms
                    in Map.insertWith Map.union (blk,sblk) 
                       (Map.singleton trg (exprType e1,Set.fromList $ fmap snd froms)) mp
  _ -> mp

intermediateBlocks :: (String,Integer) -> (String,Integer) -> Map (String,Integer) (Set (String,Integer)) -> Set (String,Integer)
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

getInputOutput :: Map String (String,Integer)
                  -> Set String
                  -> Map (String,Integer) (Set (String,Integer)) 
                  -> (Set String,(Map (String,Integer) (Map String TypeDesc),Map (String,Integer) (Map String TypeDesc),Map (String,Integer) (Map String TypeDesc)))
                  -> String -> Integer -> Instruction
                  -> (Set String,(Map (String,Integer) (Map String TypeDesc),Map (String,Integer) (Map String TypeDesc),Map (String,Integer) (Map String TypeDesc)))
getInputOutput origins arguments succ (local,mp) blk sblk instr
  = case instr of
    IRetVoid -> (Set.empty,mp)
    IRet e -> (Set.empty,addExpr e mp)
    IBr _ -> (Set.empty,mp)
    IBrCond cond _ _ -> (Set.empty,addExpr cond mp)
    ISwitch val _ cases -> (Set.empty,addExpr val $ foldr addExpr mp (fmap fst cases))
    IAssign trg expr -> (Set.insert trg local,addExpr expr mp)
    IAlloca trg _ sz _ -> (Set.insert trg local,addExpr sz mp)
    ILoad trg ptr _ -> (Set.insert trg local,addExpr ptr mp)
    IStore e ptr _ -> (local,addExpr e $ addExpr ptr mp)
    IPhi trg cases -> (Set.insert trg local,foldr addExpr mp (fmap fst cases))
    ICall _ _ _ _ args -> (Set.empty,foldr addExpr mp args)
    where
      addExpr e mp@(inp,args,outp) = case exprDesc e of
        EDNamed name -> if Set.member name local
                        then mp
                        else case Map.lookup name origins of
                          Nothing -> if Set.member name arguments
                                     then (inp,Map.insertWith Map.union (blk,sblk) (Map.singleton name (exprType e)) args,outp)
                                     else mp
                          Just (blk',sblk') -> foldl (\(inp',args',outp') inter -> (Map.insertWith Map.union inter (Map.singleton name (exprType e)) inp',
                                                                                    args',
                                                                                    Map.insertWith Map.union inter (Map.singleton name (exprType e)) outp')
                                                     ) 
                                               (Map.insertWith Map.union (blk,sblk) (Map.singleton name (exprType e)) inp,
                                                args,
                                                Map.insertWith Map.union (blk',sblk') (Map.singleton name (exprType e)) outp)
                                               (intermediateBlocks (blk',sblk') (blk,sblk) succ)
        EDUnOp _ arg -> addExpr arg mp
        EDICmp _ lhs rhs -> addExpr lhs $ addExpr rhs mp
        EDBinOp _ lhs rhs -> addExpr lhs $ addExpr rhs mp
        EDGetElementPtr expr args -> addExpr expr $ foldr addExpr mp args
        EDSelect cond lhs rhs -> addExpr cond $ addExpr lhs $ addExpr rhs mp
        EDInt _ -> mp
        EDUndef -> mp
        EDNull -> mp
        e' -> error $ "Implement addExpr for "++show e'

foldInstrs :: (a -> String -> Integer -> Instruction -> a) -> a -> [(String,[[Instruction]])] -> a
foldInstrs f = foldl (\x1 (blk,sblks) 
                      -> snd $ foldl (\(sblk,x2) instrs
                                      -> (sblk+1,foldl (\x3 instr -> f x3 blk sblk instr) x2 instrs)
                                     ) (0,x1) sblks
                     )

predictMallocUse :: [Instruction] -> Map String TypeDesc
predictMallocUse = predict' Map.empty Set.empty
  where
    predict' mp act [] = Map.union mp (Map.fromList [ (entr,TDInt False 8) | entr <- Set.toList act ])
    predict' mp act (instr:instrs) = case instr of
      ICall _ name _ (Expr { exprDesc = EDNamed "malloc" }) _ -> predict' mp (Set.insert name act) instrs
      IAssign _ (Expr { exprDesc = EDGetElementPtr (Expr { exprDesc = EDNamed name })  _ }) -> if Set.member name act
                                                                                               then predict' (Map.insert name (TDInt False 8) mp) (Set.delete name act) instrs
                                                                                               else predict' mp act instrs
      IAssign _ (Expr { exprDesc = EDUnOp UOBitcast (Expr { exprDesc = EDNamed name })
                      , exprType = TDPtr tp }) -> if Set.member name act
                                                  then predict' (Map.insert name tp mp) (Set.delete name act) instrs
                                                  else predict' mp act instrs
      ILoad _ (Expr { exprDesc = EDNamed name }) _ -> if Set.member name act
                                                      then predict' (Map.insert name (TDInt False 8) mp) (Set.delete name act) instrs
                                                      else predict' mp act instrs
      _ -> predict' mp act instrs
