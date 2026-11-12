import SigGolfCandidate.OuterResidualProjection
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualValueLaws
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase
open OuterResidualValues
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual (wTrialCoord trialCoord selNonceV_congr selNonceV_cap_one)
theorem wSelNonceV_lt (v : Coord → Digest) (n : WctNodePos) :
    wSelNonceV v n < Paired.wTrialCap n.1.coord.val n.1.level.val := by
  have hc := Paired.wTrialCap_pos n.1.coord.val n.1.level.val
  unfold wSelNonceV
  cases hf : (List.range (Paired.wTrialCap n.1.coord.val n.1.level.val)).find? fun j => !decide (wTrialFailsV v n j) with
  | none => simp only [Option.getD_none]; omega
  | some j =>
      simp only [Option.getD_some]
      exact List.mem_range.mp (List.mem_of_find?_eq_some hf)
theorem wSelNonceV_congr {v w : Coord → Digest} {n : WctNodePos}
    (h : ∀ j < Paired.wTrialCap n.1.coord.val n.1.level.val, v (wTrialCoord n j) = w (wTrialCoord n j)) :
    wSelNonceV v n = wSelNonceV w n := by
  unfold wSelNonceV
  congr 1
  apply find?_congr'
  intro j hj
  rw [List.mem_range] at hj
  have hiff : wTrialFailsV v n j ↔ wTrialFailsV w n j := by unfold wTrialFailsV; rw [h j hj]
  simp only [decide_eq_decide.mpr hiff]
theorem wSelNonceV_cap_one {v : Coord → Digest} {n : WctNodePos} (h : Paired.wTrialCap n.1.coord.val n.1.level.val = 1) :
    wSelNonceV v n = 0 := by
  have := wSelNonceV_lt v n; omega
theorem wActiveV_congr {v w : Coord → Digest} {n : WctNodePos}
    (h : Paired.wTrialCap n.1.coord.val n.1.level.val ≠ 1 →
      ∀ j < Paired.wTrialCap n.1.coord.val n.1.level.val, v (wTrialCoord n j) = w (wTrialCoord n j)) :
    WActiveV v n ↔ WActiveV w n := by
  unfold WActiveV wTrialFailsV
  by_cases h1 : Paired.wTrialCap n.1.coord.val n.1.level.val = 1
  · rw [h1]
    constructor <;> rintro ⟨hn, -⟩ <;> exact ⟨hn, fun j hj => by omega⟩
  · constructor <;> rintro ⟨hn, hj⟩ <;> refine ⟨hn, fun j hjn => ?_⟩
    · rw [← h h1 j (by omega)]; exact hj j hjn
    · rw [h h1 j (by omega)]; exact hj j hjn
theorem selCoordV_congr {v w : Coord → Digest} (c : Coord)
    (h : ∀ n : TreeNode, c = .inl (.node n) → trialCap n.1.lay n.1.level.val ≠ 1 →
      ∀ j < trialCap n.1.lay n.1.level.val, v (trialCoord n j) = w (trialCoord n j))
    (hw : ∀ n : WctNodePos, c = .inl (.wctNode n) → Paired.wTrialCap n.1.coord.val n.1.level.val ≠ 1 →
      ∀ j < Paired.wTrialCap n.1.coord.val n.1.level.val, v (wTrialCoord n j) = w (wTrialCoord n j)) :
    selCoordV v c = selCoordV w c := by
  cases c with
  | inr s=>rfl
  | inl n=>
    cases n with
    | node n=>
      change Sum.inl (Node.node (withNonce n (OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.selNonceV v n)))=
        Sum.inl (Node.node (withNonce n (OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.selNonceV w n)))
      by_cases h1 : trialCap n.1.lay n.1.level.val=1
      · rw [selNonceV_cap_one h1,selNonceV_cap_one h1]
      · rw [selNonceV_congr (h n rfl h1)]
    | wctNode n=>
      change Sum.inl (Node.wctNode (Paired.wWithNonce n (wSelNonceV v n)))=
        Sum.inl (Node.wctNode (Paired.wWithNonce n (wSelNonceV w n)))
      by_cases h1 : Paired.wTrialCap n.1.coord.val n.1.level.val=1
      · rw [wSelNonceV_cap_one h1,wSelNonceV_cap_one h1]
      · rw [wSelNonceV_congr (hw n rfl h1)]
    | _=>rfl

#print axioms selCoordV_congr
end OuterResidualValueLaws
