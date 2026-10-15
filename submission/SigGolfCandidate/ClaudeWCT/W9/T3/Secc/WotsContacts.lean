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

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Contacts
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
noncomputable def sourceChains7 : Finset ChainAddr :=
  SigGolfCandidate.T3.Security.Wots.sourceChains.filter WotsExtract.SourceChain7

theorem mem_sourceChains7 (a : ChainAddr) : a ∈ sourceChains7 ↔ WotsExtract.SourceChain7 a := by
  rw [sourceChains7, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    exact ⟨(SigGolfCandidate.T3.Security.Wots.mem_sourceChains a).mpr ⟨⟨by have := h.1.tree_lt; omega, h.1.2⟩, h.2⟩, h⟩

def PrefixRow (answers : Answers) : T3.Spec.Domain → Prop
  | .inl (.inr input) => ∃ a, WotsExtract.SourceChain7 a ∧ PrefixRowAt answers a input
  | _ => False
noncomputable def prefixClassCount (s : RefSample) : Nat :=
  (s.trace.filter fun e => decide (PrefixRow s.answers (.inl (.inr e.1)))).length
theorem prefixRowAt_unique {answers : Answers} {a b : ChainAddr} (ha : WotsExtract.SourceChain7 a)
    (hb : WotsExtract.SourceChain7 b) {input : HashInput} (hia : PrefixRowAt answers a input)
    (hib : PrefixRowAt answers b input) : a = b := by
  obtain ⟨s, v, hs, rfl⟩ := hia
  obtain ⟨s', v', hs', he⟩ := hib
  have h7a := CanonicalRef.Mask.depth_le_seven answers (sourceMessages answers) a
  have h7b := CanonicalRef.Mask.depth_le_seven answers (sourceMessages answers) b
  have hca : a.chain < 2 ^ 24 := by have := ha.2; have := Mask.chainCount_le a.key.lay; omega
  have hcb : b.chain < 2 ^ 24 := by have := hb.2; have := Mask.chainCount_le b.key.lay; omega
  have h := Mask.chainInput_eq_chainRow (a := b) hca hcb (by omega) (by omega) ((Mask.chainRow_eq a s v).symm.trans he)
  have hkey := h.1.eq_of_lt (by have := ha.1.tree_lt; omega)
    (by have := ha.1.2; have : 2 ^ height a.key.lay ≤ 2 ^ 32 :=
      Nat.pow_le_pow_right (by norm_num) (by have := height_le a.key.lay; omega); omega)
    (by have := hb.1.tree_lt; omega)
    (by have := hb.1.2; have : 2 ^ height b.key.lay ≤ 2 ^ 32 :=
      Nat.pow_le_pow_right (by norm_num) (by have := height_le b.key.lay; omega); omega)
  cases a; cases b
  simp only at hkey h ⊢
  rw [h.2.1, ← hkey]
theorem prefixCount_sum_le (s : RefSample) :
    ∑ a ∈ sourceChains7, prefixCount a s ≤ prefixClassCount s := by
  unfold prefixCount prefixClassCount
  simp only [← List.countP_eq_length_filter]
  have h := SphincsSecurity.QueryCap.calls_sum_le sourceChains7
    (fun a (e : Entry) => PrefixRowAt s.answers a e.1) (fun e => PrefixRow s.answers (.inl (.inr e.1)))
    ?_ s.trace
  · simpa only [SphincsSecurity.QueryCap.calls] using h
  · intro e
    by_cases hP : PrefixRow s.answers (.inl (.inr e.1))
    · rw [if_pos hP]
      obtain ⟨b, hb, hbe⟩ := hP
      rw [Finset.sum_eq_single b]
      · rw [if_pos hbe]
      · intro a ha hab
        rw [if_neg]
        intro hae
        exact hab (prefixRowAt_unique ((mem_sourceChains7 a).mp ha) hb hae hbe)
      · intro hb'
        exact absurd ((mem_sourceChains7 b).mpr hb) hb'
    · rw [if_neg hP]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro a ha
      rw [if_neg]
      intro hae
      exact hP ⟨a, (mem_sourceChains7 a).mp ha, hae⟩
noncomputable def errTot (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) : ℝ≥0∞ :=
  ∑ a ∈ sourceChains7, Core.errC adversary q a

theorem errTot_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1) :
    errTot adversary q ≤ ENNReal.ofReal (Core.errConst q) * (54*q) := by
  refine le_trans ?_ (Core.errC_sum_le (adversary := adversary) q hq)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => bot_le)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Contacts

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Contacts
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
theorem counted_le_cost (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) :
    ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (fun endpoint => SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint))
        (fun _ _ => none) r * (r.2.1.2 : ENNReal) ≤
      ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) := by
  conv_rhs => rw [← SphincsSecurity.Concrete.PartialChainEndpoint.realRun_counted_forget,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  apply ENNReal.tsum_le_tsum
  intro r
  by_cases hr : r ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (fun endpoint => SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint))
      (fun _ _ => none)).support
  · apply mul_le_mul' le_rfl
    have hlazy := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_support_lazy _ _ _ r hr
    have hmem := PrefixGame.lazyRun_mem_support _ _ _ hlazy
    exact_mod_cast le_of_eq (seedGame_charge (referenceInputs_subset adversary) adversary q a R r.1 r.2.1 hmem)
  · rw [(PMF.apply_eq_zero_iff _ r).mpr hr, zero_mul, zero_mul]
/-- Per rest table: the two-edge event of the `realRun` mixture against its prefix cost. -/
theorem twoEdge_mix_R (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) :
    (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => TwoEdgeEvent r.2.2 r.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
          (fun _ _ => none)] ≤
      twoEdgeRate q * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) := by
  have hsmall : q < Fintype.card Digest := by simpa using hq
  have hcharge := fun endpoint result h => le_of_eq (seedGame_charge (referenceInputs_subset adversary) adversary q a R endpoint result h)
  have hreal := seedGame_real_cost (referenceInputs_subset adversary) adversary q a R
  have h1 := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdgeEvent_le_cap_cost
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R) (seedCost a R) q
    hcharge hreal hsmall
  have h3 := SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_cap_spent_lower
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R) (seedCost a R) q
    hcharge hreal
  rw [card_digest] at h1 h3
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => TwoEdgeEvent r.2.2 r.1 |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
            (fun _ _ => none)]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (twoEdgeRate q * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) :=
        mul_le_mul' le_rfl h1
    _ = twoEdgeRate q * ((1 - (q : ENNReal) / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) := by ring
    _ ≤ twoEdgeRate q * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) :=
        mul_le_mul' le_rfl (h3.trans (counted_le_cost adversary q a R))
theorem twoEdgeAt_iff_sample (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr) :
    Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] =
      Pr[fun s => (sampleView a s).TwoEdge | PairedReference.referenceExperiment adversary q] := by
  apply pmf_probEvent_congr
  intro s hs
  obtain ⟨qs, hqs⟩ := reference_support_trace adversary q s hs
  exact twoEdgeAt_iff_view a s qs hqs
/-- Per chain, with the seed-test error (every source chain; top leaves are families since T8D). -/
theorem twoEdgeAt_cost_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr)
    (ha : WotsExtract.SourceChain7 a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] ≤
      twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
        (1 + twoEdgeRate q * q) * Core.errC adversary q a := by
  have hv := LeafView.view_prob_le (adversary := adversary) q ha PrefixView.TwoEdge (fun z h => by
    have := h.1; simp [Leaf.runViewD] at this)
  have hc := LeafView.view_count_le (adversary := adversary) q ha
  simp only [runView_twoEdge] at hv
  rw [twoEdgeAt_iff_sample]
  set M := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[fun r => TwoEdgeEvent r.2.2 r.1 |
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none)]
  set C := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞)
  have hMC : (1 - (q : ENNReal) / 2 ^ 128) * M ≤ twoEdgeRate q * C := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro R
    rw [mul_left_comm, mul_left_comm (twoEdgeRate q)]
    exact mul_le_mul' le_rfl (twoEdge_mix_R adversary q hq a R)
  have hx1 : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun s => (sampleView a s).TwoEdge | PairedReference.referenceExperiment adversary q]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (M + Core.errC adversary q a) := mul_le_mul' le_rfl hv
    _ ≤ (1 - (q : ENNReal) / 2 ^ 128) * M + Core.errC adversary q a := by
        rw [mul_add]; exact add_le_add le_rfl (mul_le_of_le_one_left bot_le hx1)
    _ ≤ twoEdgeRate q * C + Core.errC adversary q a := add_le_add hMC le_rfl
    _ ≤ twoEdgeRate q * (∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
          q * Core.errC adversary q a) + Core.errC adversary q a := add_le_add (mul_le_mul' le_rfl hc) le_rfl
    _ = _ := by ring
/-- Per rest table: the contact event of the `realRun` mixture against its prefix cost. -/
theorem contact_mix_R (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) :
    (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => Contact r.2.2 r.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
          (fun _ _ => none)] ≤
      (2 / 2 ^ 128) * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) := by
  have hsmall : q < Fintype.card Digest := by simpa using hq
  have hcharge := fun endpoint result h => le_of_eq (seedGame_charge (referenceInputs_subset adversary) adversary q a R endpoint result h)
  have hreal := seedGame_real_cost (referenceInputs_subset adversary) adversary q a R
  have h2 := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_contact_le_cap_cost
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R) (seedCost a R) q
    hcharge hreal hsmall
  have h3 := SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_cap_spent_lower
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R) (seedCost a R) q
    hcharge hreal
  rw [card_digest] at h2 h3
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => Contact r.2.2 r.1 |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
            (fun _ _ => none)]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * ((2 / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) :=
        mul_le_mul' le_rfl h2
    _ = (2 / 2 ^ 128) * ((1 - (q : ENNReal) / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) := by ring
    _ ≤ (2 / 2 ^ 128) * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) :=
        mul_le_mul' le_rfl (h3.trans (counted_le_cost adversary q a R))
theorem contactAt_iff_sample (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr) :
    Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] =
      Pr[fun s => (sampleView a s).Contact | PairedReference.referenceExperiment adversary q] := by
  apply pmf_probEvent_congr
  intro s hs
  obtain ⟨qs, hqs⟩ := reference_support_trace adversary q s hs
  exact contactAt_iff_view a s qs hqs
/-- Per chain, with the seed-test error (every source chain; top leaves are families since T8D). -/
theorem contactAt_cost_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr)
    (ha : WotsExtract.SourceChain7 a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] ≤
      (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
        (1 + (2 / 2 ^ 128) * q) * Core.errC adversary q a := by
  have hv := LeafView.view_prob_le (adversary := adversary) q ha PrefixView.Contact (fun z h => by
    have := h.1; simp [Leaf.runViewD] at this)
  have hc := LeafView.view_count_le (adversary := adversary) q ha
  simp only [runView_contact] at hv
  rw [contactAt_iff_sample]
  set M := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[fun r => Contact r.2.2 r.1 |
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none)]
  set C := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞)
  have hMC : (1 - (q : ENNReal) / 2 ^ 128) * M ≤ (2 / 2 ^ 128) * C := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro R
    rw [mul_left_comm, mul_left_comm (2 / 2 ^ 128 : ENNReal)]
    exact mul_le_mul' le_rfl (contact_mix_R adversary q hq a R)
  have hx1 : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun s => (sampleView a s).Contact | PairedReference.referenceExperiment adversary q]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (M + Core.errC adversary q a) := mul_le_mul' le_rfl hv
    _ ≤ (1 - (q : ENNReal) / 2 ^ 128) * M + Core.errC adversary q a := by
        rw [mul_add]; exact add_le_add le_rfl (mul_le_of_le_one_left bot_le hx1)
    _ ≤ (2 / 2 ^ 128) * C + Core.errC adversary q a := add_le_add hMC le_rfl
    _ ≤ (2 / 2 ^ 128) * (∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
          q * Core.errC adversary q a) + Core.errC adversary q a := add_le_add (mul_le_mul' le_rfl hc) le_rfl
    _ = _ := by ring

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Contacts

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Contacts
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
theorem reference_twoEdge_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] ≤
      (twoEdgeRate q * (∑' s, PairedReference.referenceExperiment adversary q s * (prefixClassCount s : ENNReal)) +
        (1 + twoEdgeRate q * q) * errTot adversary q) /
        (1 - (q : ENNReal) / 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  apply (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl (by finiteness))).mpr
  have hunion : Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
        PairedReference.referenceExperiment adversary q] ≤
      ∑ a ∈ sourceChains7, Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] := by
    refine le_trans (le_of_eq ?_) (probEvent_exists_finset_le_sum sourceChains7 (PairedReference.referenceExperiment adversary q)
      (fun a s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a))
    congr 1
    funext s
    apply propext
    constructor
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (mem_sourceChains7 a).mpr ha, h⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (mem_sourceChains7 a).mp ha, h⟩
  calc Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] *
        (1 - (q : ENNReal) / 2 ^ 128)
      ≤ (∑ a ∈ sourceChains7, Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q]) *
          (1 - (q : ENNReal) / 2 ^ 128) := mul_le_mul' hunion le_rfl
    _ = ∑ a ∈ sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ sourceChains7, (twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s *
          (prefixCount a s : ENNReal) + (1 + twoEdgeRate q * q) * Core.errC adversary q a) :=
        Finset.sum_le_sum fun a ha => twoEdgeAt_cost_le adversary q hq a ((mem_sourceChains7 a).mp ha)
    _ = twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s *
          ((∑ a ∈ sourceChains7, prefixCount a s : ℕ) : ENNReal) + (1 + twoEdgeRate q * q) * errTot adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        congr 2
        rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
        apply tsum_congr
        intro s
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s * (prefixClassCount s : ENNReal) +
          (1 + twoEdgeRate q * q) * errTot adversary q := by
        apply add_le_add _ le_rfl
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro s
        apply mul_le_mul' le_rfl
        exact_mod_cast prefixCount_sum_le s
noncomputable def contactCount (s : RefSample) : Nat :=
  (sourceChains7.filter fun a => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a).card
theorem expected_contactCount (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s * (contactCount s : ENNReal) =
      ∑ a ∈ sourceChains7, Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  apply tsum_congr
  intro s
  unfold contactCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a
  · rw [if_pos h, if_pos h, Nat.cast_one, mul_one]
  · rw [if_neg h, if_neg h, Nat.cast_zero, mul_zero]
theorem reference_contacts_cost_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    ∑' s, PairedReference.referenceExperiment adversary q s * (contactCount s : ENNReal) ≤
      ((2 / 2 ^ 128) * (∑' s, PairedReference.referenceExperiment adversary q s * (prefixClassCount s : ENNReal)) +
        (1 + (2 / 2 ^ 128) * q) * errTot adversary q) /
        (1 - (q : ENNReal) / 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  apply (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl (by finiteness))).mpr
  rw [expected_contactCount]
  calc (∑ a ∈ sourceChains7, Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q]) *
        (1 - (q : ENNReal) / 2 ^ 128)
      = ∑ a ∈ sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ sourceChains7, ((2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s *
          (prefixCount a s : ENNReal) + (1 + (2 / 2 ^ 128) * q) * Core.errC adversary q a) :=
        Finset.sum_le_sum fun a ha => contactAt_cost_le adversary q hq a ((mem_sourceChains7 a).mp ha)
    _ = (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s *
          ((∑ a ∈ sourceChains7, prefixCount a s : ℕ) : ENNReal) +
          (1 + (2 / 2 ^ 128) * q) * errTot adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        congr 2
        rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
        apply tsum_congr
        intro s
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (prefixClassCount s : ENNReal) +
          (1 + (2 / 2 ^ 128) * q) * errTot adversary q := by
        apply add_le_add _ le_rfl
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro s
        apply mul_le_mul' le_rfl
        exact_mod_cast prefixCount_sum_le s

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Contacts
