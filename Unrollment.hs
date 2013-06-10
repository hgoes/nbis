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
import MemoryModel

import Data.Map as Map
import Data.Set as Set
import Foreign.Ptr
import qualified Data.Graph.Inductive as Gr
import Data.Traversable
import Data.Foldable
import Data.Proxy
import Prelude hiding (sequence,mapM,mapM_)

data MergeNode mloc ptr = MergeNode { mergeActivationProxy :: SMTExpr Bool
                                    , mergeInputs :: Map (Ptr Instruction) (Either Val ptr)
                                    , mergePhis :: Map (Ptr BasicBlock) (SMTExpr Bool)
                                    , mergeLoc :: mloc
                                    }

data UnrollEnv mem mloc ptr = UnrollEnv { unrollNextMem :: mloc
                                        , unrollNextPtr :: ptr
                                        , unrollGlobals :: Map (Ptr GlobalVariable) ptr
                                        , unrollMemory :: mem
                                        }

data UnrollContext mloc ptr = UnrollContext { unrollCtxFunction :: String
                                            , unrollCtxArgs :: Map (Ptr Argument) (Either Val ptr)
                                            , currentMergeNodes :: Map (Ptr BasicBlock,Integer) (MergeNode mloc ptr)
                                            , nextMergeNodes :: Map (Ptr BasicBlock,Integer) (MergeNode mloc ptr)
                                            , realizationQueue :: [(Ptr BasicBlock,Integer,[(Ptr BasicBlock,SMTExpr Bool,Map (Ptr Instruction) (Either Val ptr),mloc)])]
                                            , outgoingEdges :: [(Ptr BasicBlock,[(SMTExpr Bool,Map (Ptr Instruction) (Either Val ptr))])]
                                            }

data UnrollConfig = UnrollCfg { unrollOrder :: [Ptr BasicBlock]
                              , unrollDoMerge :: String -> Ptr BasicBlock -> Integer -> Bool
                              , unrollStructs :: Map String [TypeDesc]
                              }

unrollProxies :: UnrollEnv mem mloc ptr -> (Proxy mloc,Proxy ptr)
unrollProxies _ = (Proxy,Proxy)

stepUnrollCtx :: (Gr.Graph gr,MemoryModel mem mloc ptr,Enum ptr,Enum mloc)
                 => UnrollConfig
                 -> Map String (ProgramGraph gr)
                 -> UnrollEnv mem mloc ptr
                 -> UnrollContext mloc ptr
                 -> SMT (UnrollEnv mem mloc ptr,UnrollContext mloc ptr)
stepUnrollCtx cfg program env cur = case realizationQueue cur of
  (blk,sblk,inc):rest -> case Map.lookup (blk,sblk) (currentMergeNodes cur) of
    Nothing -> do
      let pgr = program!(unrollCtxFunction cur)
          node = (nodeMap pgr)!(blk,sblk)
          Just (_,name,_,instrs) = Gr.lab (programGraph pgr) node
          (info,realize) = preRealize (realizeInstructions instrs)
          mkMerge = unrollDoMerge cfg (unrollCtxFunction cur) blk sblk
          blk_name = (case name of
                         Nothing -> show blk
                         Just rname -> rname)++"_"++show sblk
          mergedInps = Map.unionsWith (++) (fmap (\(_,cond,i,_) -> fmap (\v -> [(cond,v)]) i) inc)
      (act,inp,phis,loc,merge_node,nenv,mem_instr,ptr_eqs,mem_eqs)
        <- if mkMerge
           then (do
                    act_proxy <- varNamed $ "proxy_"++blk_name
                    act_static <- defConstNamed ("act_"++blk_name) (app or' ([ act | (_,act,_,_) <- inc ]++[act_proxy]))
                    let (nenv1,mp) = Map.mapAccumWithKey (\env' vname (tp,name) -> case tp of
                                                             PointerType _ -> (env' { unrollNextPtr = succ $ unrollNextPtr env' },return (Right $ unrollNextPtr env'))
                                                             _ -> (env',do
                                                                      let rname = case name of
                                                                            Nothing -> show vname
                                                                            Just n -> n
                                                                      v <- valNew rname tp
                                                                      return (Left v))
                                                         ) env (rePossibleInputs info)
                        nenv2 = nenv1 { unrollNextMem = succ $ unrollNextMem nenv1 }
                        loc = unrollNextMem nenv1
                    inp <- sequence mp
                    ptr_eqs <- sequence $
                               Map.intersectionWith (\trg src -> case trg of
                                                        Left trg_v -> do
                                                          mapM_ (\(cond,Left src_v) -> assert $ cond .=>. (valEq trg_v src_v)) src
                                                          return Nothing
                                                        Right trg_p -> return (Just (trg_p,fmap (\(cond,Right src_p) -> (cond,src_p)) src))
                                                    ) inp mergedInps
                    phis <- fmap Map.fromList $
                            mapM (\blk' -> do
                                     phi <- varNamed "phi"
                                     return (blk',phi)
                                 ) (Set.toList $ rePossiblePhis info)
                    return (act_static,inp,phis,loc,
                            Just $ MergeNode { mergeActivationProxy = act_proxy
                                             , mergeInputs = inp
                                             , mergePhis = phis
                                             , mergeLoc = loc },nenv2,
                            [],[ (cond,src_p,trg_p) | (_,Just (trg_p,src_ps)) <- Map.toList ptr_eqs
                                                    , (cond,src_p) <- src_ps ],
                            [ (act',loc',loc) | (_,act',_,loc') <- inc ]))
           else (do
                    act <- defConstNamed ("act_"++blk_name) (app or' [ act | (_,act,_,_) <- inc ])
                    let (val_eqs,ptr_eqs) = Map.mapEither id $ Map.intersectionWith (\(tp,name) src -> case tp of
                                                                                        PointerType _ -> Right (fmap (\(cond,Right src_p) -> (cond,src_p)) src)
                                                                                        _ -> Left (name,fmap (\(cond,Left src_v) -> (src_v,cond)) src)
                                                                                    ) (rePossibleInputs info) mergedInps
                        (nenv1,ptr_eqs') = Map.mapAccum (\env' ptrs -> (env' { unrollNextPtr = succ $ unrollNextPtr env' },(unrollNextPtr env',ptrs))) env ptr_eqs
                        nenv2 = nenv1 { unrollNextMem = succ $ unrollNextMem nenv1 }
                        loc = unrollNextMem nenv1
                    val_eqs' <- sequence $ Map.mapWithKey (\inp (name,vals) -> do
                                                              let rname = "inp_"++(case name of
                                                                                      Nothing -> show inp
                                                                                      Just n -> n)
                                                              valCopy rname (valSwitch vals)
                                                          ) val_eqs
                    phis <- mapM (\blk' -> do
                                     phi <- defConstNamed "phi" (app or' [ act | (blk'',cond,_,_) <- inc, blk''==blk' ])
                                     return (blk',phi)
                                 ) (Set.toList $ rePossiblePhis info)
                    return (act,Map.union (fmap Left val_eqs') (fmap (Right . fst) ptr_eqs'),
                            Map.fromList phis,loc,Nothing,nenv2,
                            [MISelect choices trg | (trg,choices) <- Map.elems ptr_eqs' ]++
                            [MIPhi [ (act',loc') | (_,act',_,loc') <- inc ] loc],
                            [],[]))
      (fin,nst,outp) <- postRealize (RealizationEnv { reFunction = unrollCtxFunction cur
                                                    , reBlock = blk
                                                    , reSubblock = sblk
                                                    , reActivation = act
                                                    , reGlobals = unrollGlobals nenv
                                                    , reArgs = unrollCtxArgs cur
                                                    , reInputs = inp
                                                    , rePhis = phis
                                                    , reStructs = unrollStructs cfg })
                        loc
                        (unrollNextMem nenv)
                        (unrollNextPtr nenv)
                        realize
      let (prx_loc,prx_ptr) = unrollProxies nenv
      nmem1 <- addProgram (unrollMemory nenv) act loc (mem_instr++(reMemInstrs outp))
      nmem2 <- foldlM (\cmem (cond,src,trg) -> connectLocation cmem prx_ptr cond src trg
                      ) nmem1 mem_eqs
      nmem3 <- foldlM (\cmem (cond,src_p,trg_p)
                       -> connectPointer cmem prx_loc cond src_p trg_p
                      ) nmem2 ptr_eqs
      return (nenv { unrollNextPtr = reNextPtr nst
                   , unrollNextMem = reCurMemLoc nst
                   , unrollMemory = nmem3 },cur)
    Just mn -> do
      nprx <- varNamed "proxy"
      assert $ (mergeActivationProxy mn) .==. (app or' ([ act | (_,act,_,_) <- inc ]++[nprx]))
      nmem1 <- foldlM (\cmem (blk',act',inp',_)
                       -> foldlM (\cmem (trg,src)
                                  -> case trg of
                                    Left trg_v -> case src of
                                      Left src_v -> do
                                        assert $ act' .=>. (valEq trg_v src_v)
                                        return cmem
                                    Right trg_p -> case src of
                                      Right src_p -> do
                                        let (prx_mloc,_) = unrollProxies env
                                        connectPointer cmem prx_mloc act' src_p trg_p
                                 ) cmem (Map.intersectionWith (\trg src -> (trg,src)) (mergeInputs mn) inp')
                      ) (unrollMemory env) inc
      let (_,prx_ptr) = unrollProxies env
      nmem2 <- foldlM (\cmem (_,act,_,loc) -> connectLocation cmem prx_ptr act loc (mergeLoc mn)) nmem1 inc
      return (env { unrollMemory = nmem2 },
              cur { currentMergeNodes = Map.insert (blk,sblk)
                                        (mn { mergeActivationProxy = nprx })
                                        (currentMergeNodes cur) })