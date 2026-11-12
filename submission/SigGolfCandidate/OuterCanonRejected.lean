import SigGolfCandidate.OuterCanonCapFailDefs
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option maxErrors 30
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired
open ClaudeWCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
attribute [local instance low] Classical.propDecidable
theorem sel_base (labels : Labels) (m : Node) : m.base.sel labels = m.sel labels := by
  cases m <;> rfl
theorem sel_eq_of_toPos (labels : Labels) {m m' : Node} (h : m.toPos = m'.toPos) : m.sel labels = m'.sel labels := by
  rw [← sel_base labels m, ← sel_base labels m', toPos_injective_base h]
/-- A hit (equal used halves) between a non-selected, non-phantom node and the selected trial of its position is a
rejected active trial whose zero test failed while the selected one passed, impossible unless every trial of that
top position failed (`CapFail`). -/
theorem rejected_hit_capFail {labels : Labels} {m node : Node} (hpos : m.toPos = node.toPos)
    (hp : ¬ PhantomAt m labels) (hne : m ≠ node.sel labels)
    (heq : Extract.Paired.proj node.toPos (labels m) = Extract.Paired.proj node.toPos (labels (node.sel labels))) :
    CapFail labels := by
  have hsel := sel_eq_of_toPos labels hpos
  cases m with
  | node mn =>
      have ha : Active labels mn := active_of_not_phantomAt hp
      rw [← hsel] at hne heq
      rw [← hpos] at heq
      change Extract.Paired.proj (Node.node mn).toPos (labels (.node mn)) =
        Extract.Paired.proj (Node.node mn).toPos (labels (.node (selNode labels mn))) at heq
      rw [show Extract.Paired.proj (Node.node mn).toPos=(Node.node mn).toPos.proj from Extract.Paired.proj_node _ _ _ _] at heq
      have hk : mn.1.nonce.val ≠ selNonce labels mn := by
        intro hk
        apply hne
        change Node.node mn = Node.node (withNonce mn (selNonce labels mn))
        rw [← hk, withNonce_self]
      have hspec := selNonce_spec labels mn
      have hS := selNonce_lt labels mn
      have hcapmax := trialCap_le mn.1.lay mn.1.level.val
      -- the selected trial fails exactly when trial `k = mn.nonce` does (equal used halves)
      have hfail_eq : trialFails labels mn (selNonce labels mn) ↔ trialFails labels mn mn.1.nonce.val := by
        unfold trialFails
        rw [withNonce_self]
        change _ ↔ trialZeroOk _ _ ((Node.node mn).toPos.proj (labels (.node mn))) = false
        rw [heq]
        rfl
      rcases Nat.lt_or_gt_of_ne hk with hlt | hgt
      · have hfk : trialFails labels mn mn.1.nonce.val := hspec.1 _ hlt
        have hfS := hfail_eq.2 hfk
        rcases hspec.2 with hpass | hlast
        · exact absurd hfS hpass
        · have hcap2 : 1 < trialCap mn.1.lay mn.1.level.val := by omega
          have htop := trialCap_ne_one (show trialCap mn.1.lay mn.1.level.val ≠ 1 by omega)
          refine Or.inl ⟨withNonce mn 0, htop, withNonce_nonce mn (by omega), fun j hj => ?_⟩
          change trialFails labels mn j
          rcases Nat.lt_or_ge j (selNonce labels mn) with hj' | hj'
          · exact hspec.1 j hj'
          · have : j = selNonce labels mn := by
              change j < trialCap mn.1.lay mn.1.level.val at hj
              omega
            rw [this]; exact hfS
      · have hfS : trialFails labels mn (selNonce labels mn) := ha.2 _ hgt
        rcases hspec.2 with hpass | hlast
        · exact absurd hfS hpass
        · exfalso
          have := ha.1
          omega
  | wctNode mn =>
      have ha : WActive labels mn := wActive_of_not_phantomAt hp
      rw [← hsel] at hne heq
      rw [← hpos] at heq
      change Extract.Paired.proj (Node.wctNode mn).toPos (labels (.wctNode mn)) =
        Extract.Paired.proj (Node.wctNode mn).toPos (labels (.wctNode (wSelNode labels mn))) at heq
      have hk : mn.1.nonce.val ≠ wSelNonce labels mn := by
        intro hk
        apply hne
        change Node.wctNode mn = Node.wctNode (wWithNonce mn (wSelNonce labels mn))
        rw [← hk, wWithNonce_self]
      have hspec := wSelNonce_spec labels mn
      have hS := wSelNonce_lt labels mn
      have hcapmax := wTrialCap_le mn.1.coord.val mn.1.level.val
      by_cases h3 : OuterExtractGround.ftsNonceLevel mn.1.coord.val mn.1.level.val
      · have hfail_eq : wTrialFails labels mn (wSelNonce labels mn) ↔ wTrialFails labels mn mn.1.nonce.val := by
          unfold wTrialFails
          rw [wWithNonce_self]
          simp only [wSelNode] at heq
          rw [← heq]
        rcases Nat.lt_or_gt_of_ne hk with hlt | hgt
        · have hfk : wTrialFails labels mn mn.1.nonce.val := hspec.1 _ hlt
          have hfS := hfail_eq.2 hfk
          rcases hspec.2 with hpass | hlast
          · exact absurd hfS hpass
          · refine Or.inr ⟨wWithNonce mn 0, h3, wWithNonce_nonce mn (by omega), fun j hj => ?_⟩
            change wTrialFails labels mn j
            rcases Nat.lt_or_ge j (wSelNonce labels mn) with hj' | hj'
            · exact hspec.1 j hj'
            · have : j = wSelNonce labels mn := by
                change j < wTrialCap mn.1.coord.val mn.1.level.val at hj
                omega
              rw [this]; exact hfS
        · have hfS : wTrialFails labels mn (wSelNonce labels mn) := ha.2 _ hgt
          rcases hspec.2 with hpass | hlast
          · exact absurd hfS hpass
          · exfalso
            have := ha.1
            omega
      · exfalso
        have h1 := wTrialCap_off (coord := mn.1.coord.val) h3
        have := ha.1
        omega
  | _ =>
      exfalso
      apply hne
      rw [← hsel]
      rfl
#print axioms rejected_hit_capFail
end OuterCanonBase.Paired
