import SigGolfCandidate.OuterResidualMessageDeps
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualMessageLaws
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase OuterResidualValues
open OuterResidualPadModel (coordTrialDeps msgDeps)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual (msgSlots trialDeps trialCoord wTrialDeps wTrialCoord mem_trialDeps mem_wTrialDeps selNonceV_cap_one selNonceV_lt)
attribute [local instance] Classical.propDecidable

theorem msgFits_msgVals (v : Coord → Digest) (L : EncLeaf) : ClaudeWCT.W9.T3M.Extract.msgFits L.1.lay (msgVals v L) := by
  unfold msgVals
  split_ifs <;> trivial

theorem msgSlot_nonce_zero {L : EncLeaf} {cs : Coord×Nat} (hc : cs∈msgSlots L) :
    (∀n : TreeNode,cs.1=.inl (.node n) → n.1.nonce.val=0) ∧
    (∀n : WctNodePos,cs.1=.inl (.wctNode n) → n.1.nonce.val=0) := by
  constructor <;> intro n hn
  all_goals
    unfold msgSlots at hc
    split_ifs at hc <;> simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hc <;>
      rcases hc with hc|hc <;> subst cs <;> cases hn <;> rfl

theorem msgVals_congr (v w : Coord → Digest) (L : EncLeaf) (h : ∀c∈msgDeps L,v c=w c) :
    msgVals v L=msgVals w L := by
  have hsel : ∀cs∈msgSlots L,selVals v cs.1=selVals w cs.1 := by
    intro cs hcs
    have hs : ∀n : TreeNode,cs.1=.inl (.node n) → trialCap n.1.lay n.1.level.val≠1 →
        ∀j<trialCap n.1.lay n.1.level.val,v (trialCoord n j)=w (trialCoord n j) := by
      intro n hn h1 j hj
      apply h
      apply List.mem_append_right
      refine List.mem_flatMap.mpr ⟨cs,hcs,?_⟩
      rw [hn]
      exact mem_trialDeps h1 hj
    have hw : ∀n : WctNodePos,cs.1=.inl (.wctNode n) → Paired.wTrialCap n.1.coord.val n.1.level.val≠1 →
        ∀j<Paired.wTrialCap n.1.coord.val n.1.level.val,v (wTrialCoord n j)=w (wTrialCoord n j) := by
      intro n hn h1 j hj
      apply h
      apply List.mem_append_right
      refine List.mem_flatMap.mpr ⟨cs,hcs,?_⟩
      rw [hn]
      exact mem_wTrialDeps h1 hj
    unfold selVals
    rw [OuterResidualValueLaws.selCoordV_congr cs.1 hs hw]
    apply h
    have hraw : cs.1∈msgDeps L:=List.mem_append_left _ (List.mem_map.mpr ⟨cs,hcs,rfl⟩)
    have hz:=msgSlot_nonce_zero hcs
    obtain ⟨c,b⟩:=cs
    cases c with
    | inr s=>exact hraw
    | inl N=>
      cases N with
      | node n=>
        change Sum.inl (Node.node (withNonce n (OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.selNonceV w n)))∈msgDeps L
        by_cases h1 : trialCap n.1.lay n.1.level.val=1
        · rw [selNonceV_cap_one h1]
          have h0:=hz.1 n rfl
          have hn:=withNonce_self n
          rw [h0] at hn
          rw [hn]
          exact hraw
        · apply List.mem_append_right
          refine List.mem_flatMap.mpr ⟨(.inl (.node n),b),hcs,?_⟩
          exact mem_trialDeps h1 (selNonceV_lt w n)
      | wctNode n=>
        change Sum.inl (Node.wctNode (Paired.wWithNonce n (wSelNonceV w n)))∈msgDeps L
        by_cases h1 : Paired.wTrialCap n.1.coord.val n.1.level.val=1
        · rw [OuterResidualValueLaws.wSelNonceV_cap_one h1]
          have h0:=hz.2 n rfl
          have hn:=Paired.wWithNonce_self n
          rw [h0] at hn
          rw [hn]
          exact hraw
        · apply List.mem_append_right
          refine List.mem_flatMap.mpr ⟨(.inl (.wctNode n),b),hcs,?_⟩
          exact mem_wTrialDeps h1 (OuterResidualValueLaws.wSelNonceV_lt w n)
      | _=>exact hraw
  unfold msgVals
  unfold msgSlots at hsel
  split_ifs with hl
  · rw [dif_pos hl] at hsel
    rw [hsel _ List.mem_cons_self,hsel _ (List.mem_cons_of_mem _ List.mem_cons_self)]
  · rw [dif_neg hl] at hsel
    rw [hsel _ List.mem_cons_self,hsel _ (List.mem_cons_of_mem _ List.mem_cons_self)]
#print axioms msgVals_congr
end OuterResidualMessageLaws
