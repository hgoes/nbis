module Unrollment where

import Language.SMTLib2
import LLVM.FFI.BasicBlock
import LLVM.FFI.Instruction
import LLVM.FFI.Value
import LLVM.FFI.Constant

import Value
import Realization
import Program
import Analyzation
import TypeDesc

import Data.Map as Map
import Data.Set as Set
import Foreign.Ptr
import qualified Data.Graph.Inductive as Gr
import Data.Traversable
import Prelude hiding (sequence,mapM)

type BlockOrder = [Ptr BasicBlock]

data MergeNode ptr = MergeNode { mergeActivationProxy :: SMTExpr Bool
                               , mergeInputs :: Map (Ptr Instruction) (Either Val ptr)
                               }

data UnrollEnv mem ptr = UnrollEnv { unrollNextMem :: mem
                                   , unrollNextPtr :: ptr
                                   , unrollGlobals :: Map (Ptr GlobalVariable) ptr
                                   }

data UnrollContext ptr = UnrollContext { unrollCtxFunction :: String
                                       , unrollCtxArgs :: Map (Ptr Argument) (Either Val ptr)
                                       , currentMergeNodes :: Map (Ptr BasicBlock) (MergeNode ptr)
                                       , nextMergeNodes :: Map (Ptr BasicBlock) (MergeNode ptr)
                                       , realizationQueue :: [(Ptr BasicBlock,Integer,[(Ptr BasicBlock,SMTExpr Bool,Map (Ptr Instruction) (Either Val ptr))])]
                                       , outgoingEdges :: [(Ptr BasicBlock,[(SMTExpr Bool,Map (Ptr Instruction) (Either Val ptr))])]
                                       }

stepUnrollCtx :: (Gr.Graph gr,Enum ptr,Enum mem) => (String -> Ptr BasicBlock -> Integer -> Bool) -> Map String [TypeDesc] -> Map String (ProgramGraph gr) -> UnrollEnv mem ptr -> UnrollContext ptr -> SMT (UnrollEnv mem ptr,UnrollContext ptr)
stepUnrollCtx doMerge structs program env cur = case realizationQueue cur of
  (blk,sblk,inc):rest -> do
    let pgr = program!(unrollCtxFunction cur)
        node = (nodeMap pgr)!(blk,sblk)
        Just (_,name,_,instrs) = Gr.lab (programGraph pgr) node
        (info,realize) = preRealize (realizeInstructions instrs)
        mkMerge = doMerge (unrollCtxFunction cur) blk sblk
        blk_name = (case name of
                               Nothing -> show blk
                               Just rname -> rname)++"_"++show sblk
    (act,inp,phis,merge_node,nenv) <- if mkMerge                
                                      then (do
                                               act_proxy <- varNamed $ "proxy_"++blk_name
                                               act_static <- defConstNamed ("act_"++blk_name) (app or' ([ act | (_,act,_) <- inc ]++[act_proxy]))
                                               let (nenv,mp) = Map.mapAccumWithKey (\env' vname (tp,name) -> case tp of
                                                                                       PointerType _ -> (env' { unrollNextPtr = succ $ unrollNextPtr env' },return (Right $ unrollNextPtr env'))
                                                                                       _ -> (env',do
                                                                                                let rname = case name of
                                                                                                      Nothing -> show vname
                                                                                                      Just n -> n
                                                                                                v <- valNew rname tp
                                                                                                return (Left v))
                                                                                   ) env (rePossibleInputs info)
                                               inp <- sequence mp
                                               phis <- mapM (\blk' -> do
                                                                phi <- varNamed "phi"
                                                                return (blk',phi)
                                                            ) (Set.toList $ rePossiblePhis info)
                                               return (act_static,inp,Map.fromList phis,
                                                       Just $ MergeNode { mergeActivationProxy = act_proxy
                                                                        , mergeInputs = inp },nenv))
                                      else undefined
    (fin,nst,outp) <- postRealize (RealizationEnv { reFunction = unrollCtxFunction cur
                                                  , reBlock = blk
                                                  , reSubblock = sblk
                                                  , reActivation = act
                                                  , reGlobals = unrollGlobals nenv
                                                  , reArgs = unrollCtxArgs cur
                                                  , reInputs = inp
                                                  , rePhis = phis
                                                  , reStructs = structs })
                      (unrollNextMem nenv)
                      (unrollNextPtr nenv)
                      realize
    return (nenv { unrollNextPtr = reNextPtr nst
                 , unrollNextMem = reCurMemLoc nst },cur)