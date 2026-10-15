import SigGolfCandidate.T3.Secc.WotsContacts
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTwoEdge

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
/-- Per rest table: the contact event of the `realRun` mixture against its prefix cost. -/
theorem contact_mix_R (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (R : RefTables adversary) :
    (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => Contact r.2.2 r.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)] ≤
      (2 / 2 ^ 128) * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) := by
  have hsmall : q < Fintype.card Digest := by simpa using hq
  have hcharge := fun endpoint result h => le_of_eq (seedGame_charge adversary q a R endpoint result h)
  have hreal := seedGame_real_cost adversary q a R
  have h2 := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_contact_le_cap_cost
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R) (seedCost a R) q
    hcharge hreal hsmall
  have h3 := SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_cap_spent_lower
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R) (seedCost a R) q
    hcharge hreal
  rw [card_digest] at h2 h3
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => Contact r.2.2 r.1 |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
            (fun _ _ => none)]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * ((2 / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) :=
        mul_le_mul' le_rfl h2
    _ = (2 / 2 ^ 128) * ((1 - (q : ENNReal) / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) := by ring
    _ ≤ (2 / 2 ^ 128) * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) :=
        mul_le_mul' le_rfl (h3.trans (counted_le_cost adversary q a R))
theorem contactAt_iff_sample (adversary : AdversaryP) (q : Nat) (a : ChainAddr) :
    Pr[fun s => ContactAt s.answers s.trace a | referenceExperiment adversary q] =
      Pr[fun s => (sampleView a s).Contact | referenceExperiment adversary q] := by
  apply pmf_probEvent_congr
  intro s hs
  obtain ⟨qs, hqs⟩ := reference_support_trace adversary q s hs
  exact contactAt_iff_view a s qs hqs
/-- Per chain, with the seed-test error (every source chain; top leaves are families since T8D). -/
theorem contactAt_cost_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => ContactAt s.answers s.trace a | referenceExperiment adversary q] ≤
      (2 / 2 ^ 128) * ∑' s, referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
        (1 + (2 / 2 ^ 128) * q) * Leaf.errC adversary q a := by
  have hv := Leaf.view_prob_le (adversary := adversary) q ha PrefixView.Contact (fun z h => by
    have := h.1; simp [Leaf.runViewD] at this)
  have hc := Leaf.view_count_le (adversary := adversary) q ha
  simp only [runView_contact] at hv
  rw [contactAt_iff_sample]
  set M := ∑' R, restLaw adversary R * Pr[fun r => Contact r.2.2 r.1 |
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
        (fun _ _ => none)]
  set C := ∑' R, restLaw adversary R * ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞)
  have hMC : (1 - (q : ENNReal) / 2 ^ 128) * M ≤ (2 / 2 ^ 128) * C := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro R
    rw [mul_left_comm, mul_left_comm (2 / 2 ^ 128 : ENNReal)]
    exact mul_le_mul' le_rfl (contact_mix_R adversary q hq a R)
  have hx1 : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun s => (sampleView a s).Contact | referenceExperiment adversary q]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (M + Leaf.errC adversary q a) := mul_le_mul' le_rfl hv
    _ ≤ (1 - (q : ENNReal) / 2 ^ 128) * M + Leaf.errC adversary q a := by
        rw [mul_add]; exact add_le_add le_rfl (mul_le_of_le_one_left bot_le hx1)
    _ ≤ (2 / 2 ^ 128) * C + Leaf.errC adversary q a := add_le_add hMC le_rfl
    _ ≤ (2 / 2 ^ 128) * (∑' s, referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
          q * Leaf.errC adversary q a) + Leaf.errC adversary q a := add_le_add (mul_le_mul' le_rfl hc) le_rfl
    _ = _ := by ring
noncomputable def contactCount (s : RefSample) : Nat :=
  (sourceChains.filter fun a => ContactAt s.answers s.trace a).card
theorem expected_contactCount (adversary : AdversaryP) (q : Nat) :
    ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) =
      ∑ a ∈ sourceChains, Pr[fun s => ContactAt s.answers s.trace a | referenceExperiment adversary q] := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  apply tsum_congr
  intro s
  unfold contactCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : ContactAt s.answers s.trace a
  · rw [if_pos h, if_pos h, Nat.cast_one, mul_one]
  · rw [if_neg h, if_neg h, Nat.cast_zero, mul_zero]
theorem reference_contacts_cost_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) ≤
      ((2 / 2 ^ 128) * (∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)) +
        (1 + (2 / 2 ^ 128) * q) * Leaf.errTot adversary q) /
        (1 - (q : ENNReal) / 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  apply (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl (by finiteness))).mpr
  rw [expected_contactCount]
  calc (∑ a ∈ sourceChains, Pr[fun s => ContactAt s.answers s.trace a | referenceExperiment adversary q]) *
        (1 - (q : ENNReal) / 2 ^ 128)
      = ∑ a ∈ sourceChains, (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => ContactAt s.answers s.trace a | referenceExperiment adversary q] := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ sourceChains, ((2 / 2 ^ 128) * ∑' s, referenceExperiment adversary q s *
          (prefixCount a s : ENNReal) + (1 + (2 / 2 ^ 128) * q) * Leaf.errC adversary q a) :=
        Finset.sum_le_sum fun a ha => contactAt_cost_le adversary q hq a ((mem_sourceChains a).mp ha)
    _ = (2 / 2 ^ 128) * ∑' s, referenceExperiment adversary q s *
          ((∑ a ∈ sourceChains, prefixCount a s : ℕ) : ENNReal) +
          (1 + (2 / 2 ^ 128) * q) * Leaf.errTot adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        congr 2
        rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
        apply tsum_congr
        intro s
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ (2 / 2 ^ 128) * ∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal) +
          (1 + (2 / 2 ^ 128) * q) * Leaf.errTot adversary q := by
        apply add_le_add _ le_rfl
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro s
        apply mul_le_mul' le_rfl
        exact_mod_cast prefixCount_sum_le s
end ClaudeWCT.W9.T3.Security.Wots
