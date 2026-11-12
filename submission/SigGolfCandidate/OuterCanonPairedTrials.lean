import SigGolfCandidate.OuterCanonPairedCore
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3

theorem wTrialCap_off {coord level : Nat} (h : ¬OuterExtractGround.ftsNonceLevel coord level) :
    wTrialCap coord level=1 := by
  have houter : ¬(level=5 ∧ Extract.Paired.first coord=false):=fun ho=>h (Or.inr ho)
  have ho : ¬Extract.Paired.ftsNonceLevel coord level:=fun ho=>h (Or.inl ho)
  simp only [wTrialCap,if_neg houter,OuterCanonBase.wTrialCap,if_neg ho]
theorem wTrialFails_congr {left right : Labels} {n : WctNodePos} {j : Nat}
    (h : left (.wctNode (wWithNonce n j)) = right (.wctNode (wWithNonce n j))) :
    wTrialFails left n j ↔ wTrialFails right n j := by
  unfold wTrialFails; rw [h]
theorem wSelNonce_congr {left right : Labels} {n : WctNodePos}
    (h : ∀ j < wTrialCap n.1.coord.val n.1.level.val,
      left (.wctNode (wWithNonce n j)) = right (.wctNode (wWithNonce n j))) :
    wSelNonce left n = wSelNonce right n := by
  unfold wSelNonce
  congr 1
  apply find?_congr'
  intro j hj
  rw [List.mem_range] at hj
  simp only [decide_eq_decide.mpr (wTrialFails_congr (h j hj))]
theorem wSelNonce_lt (labels : Labels) (n : WctNodePos) :
    wSelNonce labels n < wTrialCap n.1.coord.val n.1.level.val := by
  have hc := wTrialCap_pos n.1.coord.val n.1.level.val
  unfold wSelNonce
  cases hf : (List.range (wTrialCap n.1.coord.val n.1.level.val)).find? fun j => !decide (wTrialFails labels n j) with
  | none => simp only [Option.getD_none]; omega
  | some j =>
      simp only [Option.getD_some]
      exact List.mem_range.mp (List.mem_of_find?_eq_some hf)
theorem wSelNode_congr {left right : Labels} {n : WctNodePos}
    (h : ∀ j < wTrialCap n.1.coord.val n.1.level.val,
      left (.wctNode (wWithNonce n j)) = right (.wctNode (wWithNonce n j))) :
    wSelNode left n = wSelNode right n := by
  unfold wSelNode; rw [wSelNonce_congr h]
theorem wSelNode_label_congr {left right : Labels} {n : WctNodePos}
    (h : ∀ j < wTrialCap n.1.coord.val n.1.level.val,
      left (.wctNode (wWithNonce n j)) = right (.wctNode (wWithNonce n j))) :
    left (.wctNode (wSelNode left n)) = right (.wctNode (wSelNode right n)) := by
  rw [wSelNode_congr h]
  exact h _ (wSelNonce_lt right n)
theorem wSelNonce_of_cap_one {labels : Labels} {n : WctNodePos} (h : wTrialCap n.1.coord.val n.1.level.val = 1) :
    wSelNonce labels n = 0 := by
  have := wSelNonce_lt labels n; omega
theorem wSelNode_of_cap_one {labels : Labels} {n : WctNodePos} (h : wTrialCap n.1.coord.val n.1.level.val = 1)
    (h0 : n.1.nonce.val = 0) : wSelNode labels n = n := by
  unfold wSelNode
  rw [wSelNonce_of_cap_one h, ← h0, wWithNonce_self]
theorem wSelNonce_withNonce (labels : Labels) (n : WctNodePos) (k : Nat) :
    wSelNonce labels (wWithNonce n k) = wSelNonce labels n := rfl
theorem wTrialFails_withNonce (labels : Labels) (n : WctNodePos) (k j : Nat) :
    wTrialFails labels (wWithNonce n k) j ↔ wTrialFails labels n j := Iff.rfl
theorem wSelNonce_spec (labels : Labels) (n : WctNodePos) :
    (∀ j < wSelNonce labels n, wTrialFails labels n j) ∧
      (¬ wTrialFails labels n (wSelNonce labels n) ∨
        wSelNonce labels n = wTrialCap n.1.coord.val n.1.level.val - 1) := by
  unfold wSelNonce
  cases hf : (List.range (wTrialCap n.1.coord.val n.1.level.val)).find?
      (fun j => !decide (wTrialFails labels n j)) with
  | none =>
      have hall : ∀ i, i < wTrialCap n.1.coord.val n.1.level.val → wTrialFails labels n i := by
        intro i hi
        have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
        simpa using this
      have hpos := wTrialCap_pos n.1.coord.val n.1.level.val
      refine ⟨fun j hj => hall j ?_, Or.inr rfl⟩
      simp only [Option.getD_none] at hj
      omega
  | some i =>
      rw [List.find?_range_eq_some] at hf
      obtain ⟨hp, -, hlt⟩ := hf
      simp only [Option.getD_some]
      exact ⟨fun j hj => by simpa using hlt j hj, Or.inl (by simpa using hp)⟩
/-- Every FTS trial up to the selected one is active. -/
theorem wActive_trial_of_le {labels : Labels} {n : WctNodePos} {k : Nat} (hk : k ≤ wSelNonce labels n) :
    WActive labels (wWithNonce n k) := by
  have hs := wSelNonce_lt labels n
  have hc := wTrialCap_le n.1.coord.val n.1.level.val
  refine ⟨?_, fun j hj => ?_⟩
  · rw [wWithNonce_nonce n (by omega)]; exact lt_of_le_of_lt hk hs
  · rw [wWithNonce_nonce n (by omega)] at hj
    exact (wTrialFails_withNonce labels n k j).2 ((wSelNonce_spec labels n).1 j (by omega))
/-- A nonce-0 FTS trial is active. -/
theorem wActive_zero (labels : Labels) (n : WctNodePos) (h0 : n.1.nonce.val = 0) : WActive labels n :=
  ⟨by rw [h0]; exact wTrialCap_pos _ _, fun j hj => by rw [h0] at hj; omega⟩
theorem nonce_pad_zero : BitVec.ofNat 128 (0 % 2 ^ 64) = (0 : Digest) := rfl
theorem wActiveCongr (left right : Labels) (n : WctNodePos)
    (h : ∀ j < n.1.nonce.val, left (.wctNode (wWithNonce n j)) = right (.wctNode (wWithNonce n j))) :
    WActive left n ↔ WActive right n := by
  unfold WActive
  exact and_congr_right fun _ => forall_congr' fun j => imp_congr_right fun hj => wTrialFails_congr (h j hj)

#print axioms wActive_trial_of_le
#print axioms wSelNonce_spec
end OuterCanonBase.Paired
