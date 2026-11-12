import SigGolfCandidate.OuterNodeReference
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterNodeReference
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.Research
open ClaudeWCT
open ClaudeWCT.W9.T3M.Extract.Paired

theorem eval_nonGround (answers : Answers) (index coord level nd : Nat)
    (hb : Bounded (.wctNode index coord level nd)) (h3 : ¬OuterExtractGround.ftsNonceLevel coord level)
    (left right : Digest) :
    evalWithAnswerFn answers (OuterCanonicalNode.node (first coord) coord index (2^(6-level)+nd)
      (OuterExtractModel.pads answers index coord) left right)=
      proj (.wctNode index coord level nd) (answers (.inl (.inr (pad64 (WCT9.wctTopInput coord index
        (2^(6-level)+nd) left (if level=4 then (OuterExtractModel.pads answers index coord ((2^(6-level)+nd)/2-2)).2 else 0) right))))) := by
  obtain ⟨⟨hi,hc,hl,hn⟩,hu⟩:=hb
  rw [OuterExtractGround.sharedNode_eq_nodeProgramP index coord level nd hc hl
    (by simpa only [show 7-level-1=6-level by omega] using hn) hu
    (OuterExtractModel.pads answers index coord) left right h3,eval_nodeProgram]
theorem reference (answers : Answers) (index coord level node : Nat)
    (hb : Bounded (.wctNode index coord level node)) :
    proj (.wctNode index coord level node)
      (answers (.inl (.inr (OuterExtractModel.honestInput answers (.wctNode index coord level node))))) =
      (OuterExtractModel.nodes answers index coord).getD (2^(6-level)+node) 0 := by
  have hb' := hb
  obtain ⟨⟨hi,hc,hl,hn⟩,hu⟩ := hb'
  by_cases h5 : level=5
  · subst level
    exact outer answers index coord node hc
      (Bool.eq_false_iff.mpr (fun h=>by have hh:=hu h;omega)) (by norm_num at hn;omega)
  have hfirst : OuterExtractModel.first coord=first coord:=rfl
  have hg := OuterExtractModel.nodes_graph answers index coord hc
  rw [hfirst] at hg
  have hc' := SharedForest.heapCut_bounds (first coord)
  have hheap : SharedForest.heapCut (first coord)≤2^(6-level)+node ∧ 2^(6-level)+node<128 := by
    by_cases hf : first coord=true
    · have hl' := hu hf
      simp only [SharedForest.heapCut, hf, if_true]
      interval_cases level <;> norm_num at hn ⊢ <;> omega
    · have hff := Bool.eq_false_iff.mpr hf
      simp only [SharedForest.heapCut, hff, Bool.false_eq_true, if_false]
      interval_cases level <;> norm_num at hn ⊢ <;> omega
  have href := hg.2.2 (2^(6-level)+node) hheap.1 hheap.2 (by omega)
  by_cases h3 : ftsNonceLevel coord level
  · have hn6 : node < 2^(6-level) := by simpa only [show 7-level-1=6-level by omega] using hn
    have hg := (ftsNonceLevel_node (coord := coord) (by omega) hn6).mp h3
    have h23 := ftsNonceLevel_le h3
    rw [OuterCanonicalNodeGround.groundG (first coord) coord index (2^(6-level)+node) (OuterExtractModel.pads answers index coord) hg] at href
    unfold WCT9.ftsNodeG at href
    rw [evalWithAnswerFn_map, eval_ftsNodeAt_groundG answers hg] at href
    rw [href, proj_wctNode_packed index coord level node h23.2 hn6]
    have hin : OuterExtractModel.honestInput answers (.wctNode index coord level node) = pad64 (WCT9.wctTopInput coord index
        (2^(6-level)+node) ((OuterExtractModel.nodes answers index coord).getD (2*(2^(6-level)+node)) 0)
        (BitVec.ofNat 128 ((evalWithAnswerFn answers (WCT9.ftsNodeAt coord index (2^(6-level)+node)
          ((OuterExtractModel.nodes answers index coord).getD (2*(2^(6-level)+node)) 0)
          ((OuterExtractModel.nodes answers index coord).getD (2*(2^(6-level)+node)+1) 0))).1 % 2^64))
        ((OuterExtractModel.nodes answers index coord).getD (2*(2^(6-level)+node)+1) 0)) := by
      simp only [OuterExtractModel.honestInput]
      rw [if_neg (show level ≠ 4 by omega), if_pos (show OuterExtractGround.ftsNonceLevel coord level from Or.inl h3)]
      unfold OuterExtractModel.honestFtsNonce OuterExtractGround.nodeAt
      rw [if_neg (by have hh:=WCT9.ftsGround_ge8 hg;omega)]
    rw [hin]
  rw [eval_nonGround answers index coord level node hb (by intro h;rcases h with h|h;exact h3 h;exact h5 h.1)] at href
  rw [href]
  have hin : OuterExtractModel.honestInput answers (.wctNode index coord level node) = pad64 (WCT9.wctTopInput coord index
      (2^(6-level)+node) ((OuterExtractModel.nodes answers index coord).getD (2*(2^(6-level)+node)) 0)
      (if level=4 then (OuterExtractModel.pads answers index coord ((2^(6-level)+node)/2-2)).2 else 0)
      ((OuterExtractModel.nodes answers index coord).getD (2*(2^(6-level)+node)+1) 0)) := by
    simp only [OuterExtractModel.honestInput]
    rw [if_neg (show ¬OuterExtractGround.ftsNonceLevel coord level by
      intro h;rcases h with h|h;exact h3 h;exact h5 h.1)]
  rw [hin]


#print axioms reference
end OuterNodeReference
