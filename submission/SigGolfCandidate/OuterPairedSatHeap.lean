import SigGolfCandidate.OuterCanonicalHeapFold
import SigGolfCandidate.OuterGroundDeterministic
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterPairedStructural
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.WCT9 ClaudeWCT.WCT9.Wots ClaudeWCT.W9.T3M
open SigGolfCandidate.Research SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.Wots.PairedStructural
attribute [local irreducible] OuterExtractModel.nodes OuterExtractModel.pads
variable (T : Answers) (index : Nat) (hidx : index<2^31)
theorem sharedNodes_actual (coord : Coord) :
    OuterCanonicalModel.nodes T (Extract.Paired.first coord.val) index coord.val (OuterExtractModel.pads T index coord.val)=
      OuterExtractModel.nodes T index coord.val := (OuterExtractModel.nodes_shared T index coord.val coord.isLt).symm
 include hidx in
set_option maxHeartbeats 800000 in
theorem sat_sharedHeap (coord : Coord) :
    QueriesSat T (HonestQuery T)
      (OuterCanonicalModel.heap (Extract.Paired.first coord.val) index coord.val
        (OuterExtractModel.pads T index coord.val)
        (SharedForest.sharedLeaves T (Extract.Paired.first coord.val) index coord.val
          (OuterExtractModel.pads T index coord.val))) := by
  have hg:=OuterCanonicalNode.graph T (Extract.Paired.first coord.val) index coord.val
    (OuterExtractModel.pads T index coord.val)
  rw [sharedNodes_actual T index coord] at hg
  obtain ⟨hsize,hleaf,hnode⟩:=hg
  have hcut:=SharedForest.heapCut_bounds (Extract.Paired.first coord.val)
  rw [OuterCanonicalModel.heap_fold]
  change QueriesSat T (HonestQuery T) ((List.range' (SharedForest.heapCut (Extract.Paired.first coord.val))
    (128-SharedForest.heapCut (Extract.Paired.first coord.val))).reverse.foldlM _ _)
  refine QueriesSat.foldlM_list _ _ (ClaudeWCT.WCT9.Wots.Structural.HeapAgree (OuterExtractModel.nodes T index coord.val)) _ ?_ ?_
  · refine ⟨by simp [SharedForest.sharedLeaves],?_⟩
    intro j hj
    by_cases hj':j<256
    · simp only [Array.getD_eq_getD_getElem?,List.getElem?_toArray,←List.getD_eq_getElem?_getD]
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate];omega),
        List.length_replicate,←hleaf j hj hj']
      simp only [Array.getD_eq_getD_getElem?]
    · have h1 : ((List.replicate 128 (0:Digest)++
          SharedForest.sharedLeaves T (Extract.Paired.first coord.val) index coord.val
            (OuterExtractModel.pads T index coord.val)).toArray).getD j 0=0 := by
        simp only [Array.getD_eq_getD_getElem?,List.getElem?_toArray]
        rw [List.getElem?_eq_none (by simp [SharedForest.sharedLeaves];omega)]
        rfl
      have h2:(OuterExtractModel.nodes T index coord.val).getD j 0=0 := by
        simp only [Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_none (by omega)]
        rfl
      rw [h1,h2]
  · intro done hdone nodes ⟨hsz,hagree⟩
    have hd:done<128-SharedForest.heapCut (Extract.Paired.first coord.val) := by
      simpa only [List.length_reverse,List.length_range'] using hdone
    rw [SharedForest.shared_heap_order _ done hd]
    obtain ⟨ha,hb,hc⟩ := sharedHeap_arithmetic _ _ hcut.1 hd
    obtain ⟨hl2,hr2,hs⟩ := sharedHeap_child_arithmetic _ _ hcut.1 hd
    have hl:nodes.getD (2*(127-done)) 0=(OuterExtractModel.nodes T index coord.val).getD (2*(127-done)) 0 :=
      hagree (2*(127-done)) hl2
    have hr:nodes.getD (2*(127-done)+1) 0=(OuterExtractModel.nodes T index coord.val).getD (2*(127-done)+1) 0 :=
      hagree (2*(127-done)+1) hr2
    refine ⟨?_,?_⟩
    · refine QueriesSat.bind ?_ (QueriesSat.pure' _)
      rw [hl,hr]
      exact sat_sharedNode T index hidx coord (127-done) ha hb
    · simp only [OuterCanonicalModel.step,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
      refine ⟨by rw [Array.size_set!,hsz],?_⟩
      intro j hj
      by_cases he:j=127-done
      · subst he
        rw [getD_set_self nodes (127-done) _ (by rw [hsz]; exact hs),hl,hr]
        exact (hnode (127-done) ha hb hc).symm
      · rw [getD_set_other nodes _ _ _ (Ne.symm he)]
        exact hagree j (sharedHeap_other_arithmetic done j (lt_of_lt_of_le hd (Nat.sub_le _ _)) hj he)

#print axioms sat_sharedHeap
end OuterPairedStructural
