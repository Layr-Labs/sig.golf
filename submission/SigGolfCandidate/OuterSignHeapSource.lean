import SigGolfCandidate.OuterSignTree
import SigGolfCandidate.OuterForestBudget
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignHeapSource
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (M Digest)
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open SigGolfCandidate.Research ClaudeWCT ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedCoordinate

theorem order (c : Nat) :
    (List.range' 0 (SharedTree.count c)).map (fun k=>127-k)=
      (List.range' 4 124).reverse++(if SharedLeaf.first c then [] else [3,2]) := by
  by_cases hf : SharedLeaf.first c=true
  · have hf' : SharedTail.first c=true := hf
    simp only [SharedTree.count,SharedTail.limit,hf',if_true,hf,List.append_nil]
    decide +kernel
  · have hf' : SharedTail.first c=false := Bool.eq_false_iff.mpr hf
    have hf'' : SharedLeaf.first c=false := hf'
    simp only [SharedTree.count,SharedTail.limit,hf',Bool.false_eq_true,if_false,hf'']
    decide +kernel

theorem inner_step (c index h : Nat) (hc : c<9) (hh4 : 4≤h) (hh128 : h<128)
    (pads : Nat→SharedForest.PairRoot) (nodes : Array Digest) :
    OuterSignTree.stepProgram index c (rightPads pads) nodes h=
      heapStep (SharedLeaf.first c) index c pads nodes h := by
  unfold OuterSignTree.stepProgram
  rw [OuterSignNodeModel.hashProgram,if_neg (by omega),hashProgram_source c index h hc (by have:=SharedTree.limit_bounds c;omega)]
  rfl

theorem inner (c index : Nat) (hc : c<9) (pads : Nat→SharedForest.PairRoot) (leaves : List Digest) :
    ((List.range' 4 124).reverse.foldlM (fun nodes h=>OuterSignTree.stepProgram index c (rightPads pads) nodes h)
      ((List.replicate 128 (0:Digest)++leaves).toArray))=
      OuterInnerMoment.innerHeap (SharedLeaf.first c) index c pads leaves := by
  unfold OuterInnerMoment.innerHeap
  apply WCT9.foldlM_congr_mem
  intro nodes h hh
  have hb : 4≤h ∧ h<128 := by simpa only [List.mem_reverse,List.mem_range'_1] using hh
  exact inner_step c index h hc hb.1 hb.2 pads nodes

theorem tail (c index : Nat) (pads : Nat→SharedForest.PairRoot) (nodes : Array Digest) :
    ([3,2].foldlM (fun nodes h=>OuterSignTree.stepProgram index c (rightPads pads) nodes h) nodes)=
      OuterHeapMoment.finish c index nodes := by
  simp only [List.foldlM_cons,List.foldlM_nil,OuterSignTree.stepProgram,OuterSignNodeModel.hashProgram,
    show (3:Nat)=2 ∨ 3=3 from Or.inr rfl,show (2:Nat)=2 ∨ 2=3 from Or.inl rfl,if_true,
    or_true,true_or,Nat.reduceMul,Nat.reduceAdd,map_eq_bind_pure_comp,Function.comp_def,bind_assoc,pure_bind,bind_pure]
  unfold OuterHeapMoment.finish
  apply bind_congr
  intro a
  rw [WCT9.getD_set_other _ _ _ _ (by decide : (3:Nat)≠4),WCT9.getD_set_other _ _ _ _ (by decide : (3:Nat)≠5)]

theorem heap (c index : Nat) (hc : c<9) (pads : Nat→SharedForest.PairRoot) (leaves : List Digest) :
    OuterSignTree.heapProgram index c (rightPads pads) leaves=
      (if SharedLeaf.first c then OuterInnerMoment.innerHeap true index c pads leaves else OuterHeapMoment.heap c index pads leaves) := by
  unfold OuterSignTree.heapProgram
  rw [←List.foldlM_map,order,List.foldlM_append,inner c index hc]
  by_cases hf : SharedLeaf.first c=true
  · simp only [hf,if_true,List.foldlM_nil,bind_pure]
  · have hf' : SharedLeaf.first c=false := Bool.eq_false_iff.mpr hf
    simp only [hf',Bool.false_eq_true,if_false]
    unfold OuterHeapMoment.heap
    apply bind_congr
    intro nodes
    exact tail c index pads nodes
#print axioms order
#print axioms inner_step
#print axioms inner
#print axioms tail
#print axioms heap
end OuterSignHeapSource
