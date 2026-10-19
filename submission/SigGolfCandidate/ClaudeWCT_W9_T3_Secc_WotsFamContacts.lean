import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamRef
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamTot
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsContacts

/-! # Family restart, step P6a: the normalized contacts layer charged to family errors (r3-lean-seedfam)

Family port of the normalized `Contacts` (`twoEdgeAt_cost_le`, `contactAt_cost_le`, `reference_twoEdge_le`,
`reference_contacts_cost_le`): the per-chain error `Core.errC` becomes `FamLift.errCF S`, the total `Contacts.errTot`
becomes `FamTot.errTotF S` (summed over `sourceChains`; it agrees with the sum over `Contacts.sourceChains7` since
`errCF` vanishes off `SourceChain7`, `errTot7F_eq`). The leaf-independent parts (`twoEdge_mix_R`, `contact_mix_R`,
`twoEdgeAt_iff_sample`, `contactAt_iff_sample`, `prefixCount_sum_le`, `expected_contactCount`) are reused.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamContacts
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun realRun
  idealRun lazyRun TwoEdgeEvent Contact)
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme FamCaps)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame

/-- Family total over `sourceChains7` (the index set of the leaf consumers). -/
noncomputable def errTot7F (S : FamScheme) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ℝ≥0∞ :=
  ∑ a ∈ Normalized.Contacts.sourceChains7, FamLift.errCF S adversary q a

/-- `errCF` vanishes off `SourceChain7`, so the totals over `sourceChains7` and `sourceChains` agree. -/
theorem errTot7F_eq (S : FamScheme) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    errTot7F S adversary q = FamTot.errTotF S adversary q := by
  unfold errTot7F FamTot.errTotF Normalized.Contacts.sourceChains7
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : WotsExtract.SourceChain7 a
  · rw [if_pos h]
  · rw [if_neg h, FamLift.errCF, dif_neg h]

theorem errTot7F_le {S : FamScheme} {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    errTot7F S adversary q ≤ ENNReal.ofReal (Core.errConst q) * ((Cmax : ℝ≥0∞) * q) := by
  rw [errTot7F_eq]
  exact FamTot.errTotF_le H adversary q hq

section PerChain
variable {S : FamScheme} {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
include H

/-- Per chain, two-edge cost with the family seed-test error. -/
theorem twoEdgeAt_cost_leF (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q] ≤
      twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
        (1 + twoEdgeRate q * q) * FamLift.errCF S adversary q a := by
  have hv := FamRef.view_prob_leF (adversary := adversary) S H.grp_le H.caps H.width H.points q ha
    PrefixView.TwoEdge (fun z h => by
    have := h.1; simp [Leaf.runViewD] at this)
  have hc := FamRef.view_count_leF (adversary := adversary) S H.grp_le H.caps H.width H.points q ha
  simp only [runView_twoEdge] at hv
  rw [Normalized.Contacts.twoEdgeAt_iff_sample]
  set M := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[fun r => TwoEdgeEvent r.2.2 r.1 |
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)]
  set C := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞)
  have hMC : (1 - (q : ENNReal) / 2 ^ 128) * M ≤ twoEdgeRate q * C := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro R
    rw [mul_left_comm, mul_left_comm (twoEdgeRate q)]
    exact mul_le_mul' le_rfl (Normalized.Contacts.twoEdge_mix_R adversary q hq a R)
  have hx1 : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => (sampleView a s).TwoEdge | PairedReference.referenceExperiment adversary q]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (M + FamLift.errCF S adversary q a) := mul_le_mul' le_rfl hv
    _ ≤ (1 - (q : ENNReal) / 2 ^ 128) * M + FamLift.errCF S adversary q a := by
        rw [mul_add]; exact add_le_add le_rfl (mul_le_of_le_one_left bot_le hx1)
    _ ≤ twoEdgeRate q * C + FamLift.errCF S adversary q a := add_le_add hMC le_rfl
    _ ≤ twoEdgeRate q * (∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
          q * FamLift.errCF S adversary q a) + FamLift.errCF S adversary q a :=
        add_le_add (mul_le_mul' le_rfl hc) le_rfl
    _ = _ := by ring

/-- Per chain, contact cost with the family seed-test error. -/
theorem contactAt_cost_leF (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q] ≤
      (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
        (1 + (2 / 2 ^ 128) * q) * FamLift.errCF S adversary q a := by
  have hv := FamRef.view_prob_leF (adversary := adversary) S H.grp_le H.caps H.width H.points q ha
    PrefixView.Contact (fun z h => by
    have := h.1; simp [Leaf.runViewD] at this)
  have hc := FamRef.view_count_leF (adversary := adversary) S H.grp_le H.caps H.width H.points q ha
  simp only [runView_contact] at hv
  rw [Normalized.Contacts.contactAt_iff_sample]
  set M := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[fun r => Contact r.2.2 r.1 |
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)]
  set C := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞)
  have hMC : (1 - (q : ENNReal) / 2 ^ 128) * M ≤ (2 / 2 ^ 128) * C := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro R
    rw [mul_left_comm, mul_left_comm (2 / 2 ^ 128 : ENNReal)]
    exact mul_le_mul' le_rfl (Normalized.Contacts.contact_mix_R adversary q hq a R)
  have hx1 : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => (sampleView a s).Contact | PairedReference.referenceExperiment adversary q]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (M + FamLift.errCF S adversary q a) := mul_le_mul' le_rfl hv
    _ ≤ (1 - (q : ENNReal) / 2 ^ 128) * M + FamLift.errCF S adversary q a := by
        rw [mul_add]; exact add_le_add le_rfl (mul_le_of_le_one_left bot_le hx1)
    _ ≤ (2 / 2 ^ 128) * C + FamLift.errCF S adversary q a := add_le_add hMC le_rfl
    _ ≤ (2 / 2 ^ 128) * (∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
          q * FamLift.errCF S adversary q a) + FamLift.errCF S adversary q a :=
        add_le_add (mul_le_mul' le_rfl hc) le_rfl
    _ = _ := by ring

/-- **Two-edge bound, family charge.** -/
theorem reference_twoEdge_leF (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
        CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
        PairedReference.referenceExperiment adversary q] ≤
      (twoEdgeRate q * (∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.prefixClassCount s : ENNReal)) +
        (1 + twoEdgeRate q * q) * FamTot.errTotF S adversary q) /
        (1 - (q : ENNReal) / 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  apply (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl (by finiteness))).mpr
  rw [← errTot7F_eq]
  have hunion : Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
        CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
        PairedReference.referenceExperiment adversary q] ≤
      ∑ a ∈ Normalized.Contacts.sourceChains7, Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
        PairedReference.referenceExperiment adversary q] := by
    refine le_trans (le_of_eq ?_) (probEvent_exists_finset_le_sum Normalized.Contacts.sourceChains7
      (PairedReference.referenceExperiment adversary q)
      (fun a s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a))
    congr 1
    funext s
    apply propext
    constructor
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (Normalized.Contacts.mem_sourceChains7 a).mpr ha, h⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (Normalized.Contacts.mem_sourceChains7 a).mp ha, h⟩
  calc Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
          CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q] * (1 - (q : ENNReal) / 2 ^ 128)
      ≤ (∑ a ∈ Normalized.Contacts.sourceChains7, Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q]) * (1 - (q : ENNReal) / 2 ^ 128) :=
        mul_le_mul' hunion le_rfl
    _ = ∑ a ∈ Normalized.Contacts.sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
            PairedReference.referenceExperiment adversary q] := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ Normalized.Contacts.sourceChains7, (twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s *
          (prefixCount a s : ENNReal) + (1 + twoEdgeRate q * q) * FamLift.errCF S adversary q a) :=
        Finset.sum_le_sum fun a ha => twoEdgeAt_cost_leF H adversary q hq a ((Normalized.Contacts.mem_sourceChains7 a).mp ha)
    _ = twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s *
          ((∑ a ∈ Normalized.Contacts.sourceChains7, prefixCount a s : ℕ) : ENNReal) +
          (1 + twoEdgeRate q * q) * errTot7F S adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        congr 2
        rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
        apply tsum_congr
        intro s
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.prefixClassCount s : ENNReal) +
          (1 + twoEdgeRate q * q) * errTot7F S adversary q := by
        apply add_le_add _ le_rfl
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro s
        apply mul_le_mul' le_rfl
        exact_mod_cast Normalized.Contacts.prefixCount_sum_le s

/-- **Expected contact count bound, family charge.** -/
theorem reference_contacts_cost_leF (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (hq : q < 2 ^ 128) :
    ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.contactCount s : ENNReal) ≤
      ((2 / 2 ^ 128) * (∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.prefixClassCount s : ENNReal)) +
        (1 + (2 / 2 ^ 128) * q) * FamTot.errTotF S adversary q) /
        (1 - (q : ENNReal) / 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  apply (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl (by finiteness))).mpr
  rw [Normalized.Contacts.expected_contactCount, ← errTot7F_eq]
  calc (∑ a ∈ Normalized.Contacts.sourceChains7, Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q]) * (1 - (q : ENNReal) / 2 ^ 128)
      = ∑ a ∈ Normalized.Contacts.sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a |
            PairedReference.referenceExperiment adversary q] := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ Normalized.Contacts.sourceChains7, ((2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s *
          (prefixCount a s : ENNReal) + (1 + (2 / 2 ^ 128) * q) * FamLift.errCF S adversary q a) :=
        Finset.sum_le_sum fun a ha => contactAt_cost_leF H adversary q hq a ((Normalized.Contacts.mem_sourceChains7 a).mp ha)
    _ = (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s *
          ((∑ a ∈ Normalized.Contacts.sourceChains7, prefixCount a s : ℕ) : ENNReal) +
          (1 + (2 / 2 ^ 128) * q) * errTot7F S adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        congr 2
        rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
        apply tsum_congr
        intro s
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.prefixClassCount s : ENNReal) +
          (1 + (2 / 2 ^ 128) * q) * errTot7F S adversary q := by
        apply add_le_add _ le_rfl
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro s
        apply mul_le_mul' le_rfl
        exact_mod_cast Normalized.Contacts.prefixCount_sum_le s
end PerChain

#print axioms errTot7F_eq
#print axioms twoEdgeAt_cost_leF
#print axioms contactAt_cost_leF
#print axioms reference_twoEdge_leF
#print axioms reference_contacts_cost_leF
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamContacts
