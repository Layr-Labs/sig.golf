import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_FinalG
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamRestart2
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamContacts
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamHyps

/-! # The live security theorem through the family seed-error charge (r3-lean-seedfam, P6b)

Copies of the Final.lean blocks that charge the WOTS seed test per chain (`Core.errC`, `Contacts.errTot`, the
per-chain restart `Restart.source_contactAfterStop_charge` / `source_markerFirst_at_le`), suffixed `Fam`, with the
family charge `FamLift.errCF S` / `FamTot.errTotF S` for any `FamScheme S` with `H : FamTot.FamHyps S Cmax`
(`FamRestart2.*F`, `FamContacts.*F`). The closing is FinalG's (`799/1000`, `grouped_middle_closing`) with the seed
error `FamTot.seedErrorBoundF H hC` (`Cmax ≤ 305`); the large route is `LargeCoupling.Paired.large_bound`.
`t3_securityP_fam S Cmax H hC : SecurityP`; `t3_securityP_layout` instantiates the scheme's layout (v6). -/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun Contact)
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme FamCaps)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL

/-- Other contacts are invariant under the family congruence of a source chain's family. -/
theorem otherContact_stopLFam (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (a : ChainAddr)
    (ha : WotsExtract.SourceChain7 a) :
    ∀ T T', FamGame.FamCongr S (sourceMessages T) (FamSum.famOf S a.key) T T' → ∀ trace,
      OtherContact a T' trace ↔ OtherContact a T trace := by
  intro T T' hC trace
  have hFok := FamLift.famOk_of_source S hgrp ha.1
  unfold OtherContact
  exact exists_congr fun b => and_congr_right fun hb => and_congr_right fun _ =>
    FamRestartN.contactAt_famCongr hC hFok.leaf hFok.tree trace hb

theorem reference_twoContacts_le_rawFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] ≤
      (((2 * q : ℕ) : ENNReal) *
          (((2 / 2 ^ 128) * (∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.prefixClassCount s : ENNReal)) +
              (1 + (2 / 2 ^ 128) * q) * FamTot.errTotF S adversary q) /
            (1 - (q : ENNReal) / 2 ^ 128)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamTot.errTotF S adversary q) /
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hne : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hpos (by simp)
  apply (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl (by finiteness))).mpr
  have hunion : Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] ≤
      ∑ a ∈ Contacts.sourceChains7, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
        PairedReference.referenceExperiment adversary q] := by
    refine le_trans ?_ (probEvent_exists_finset_le_sum Contacts.sourceChains7 (PairedReference.referenceExperiment adversary q)
        (fun a s => ContactAfterStop (OtherContact a) s.answers s.trace a))
    apply pmf_probEvent_mono
    rintro s - ⟨a, b, ha, hb, hab, hca, hcb⟩
    rcases twoContacts_cases s.answers s.trace a b ha hb hab hca hcb with h | h
    · exact ⟨a, (Contacts.mem_sourceChains7 a).mpr ha, h⟩
    · exact ⟨b, (Contacts.mem_sourceChains7 b).mpr hb, h⟩
  have hcharge := fun a (ha : a ∈ Contacts.sourceChains7) =>
    FamRestart2.source_contactAfterStop_chargeF (adversary := adversary) S H.grp_le H.caps H.width H.points q
      ((Contacts.mem_sourceChains7 a).mp ha) (OtherContact a)
      (otherContact_maskAt a ((Contacts.mem_sourceChains7 a).mp ha))
      (otherContact_stopLFam S H.grp_le a ((Contacts.mem_sourceChains7 a).mp ha)) hq
  have halloc : ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s *
        (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) ≤
      ((2 * q : ℕ) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.contactCount s : ENNReal) := by
    rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro s
    by_cases hs : s ∈ (PairedReference.referenceExperiment adversary q).support
    · rw [← Finset.mul_sum]
      have hpoint : ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0) ≤
          ((2 * q : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
        calc ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) *
              (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
            ≤ ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
              apply Finset.sum_le_sum
              intro a _
              apply mul_le_mul' le_rfl
              by_cases h : ∃ k, OtherContact a s.answers (s.trace.take k)
              · rw [if_pos h]
                exact_mod_cast otherContact_take_count s a h
              · rw [if_neg h]
                exact bot_le
          _ = ((2 * ∑ a ∈ Contacts.sourceChains7, prefixCount a s : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
              rw [← Finset.sum_mul, Finset.mul_sum, Nat.cast_sum]
          _ ≤ ((2 * q : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
              apply mul_le_mul' _ le_rfl
              have h1 := Contacts.prefixCount_sum_le s
              have h2 := prefixClassCount_le_length s
              have h3 := Core.ref_trace_length_le adversary q s hs
              exact_mod_cast (by omega : 2 * ∑ a ∈ Contacts.sourceChains7, prefixCount a s ≤ 2 * q)
      calc PairedReference.referenceExperiment adversary q s * ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
          ≤ PairedReference.referenceExperiment adversary q s * (((2 * q : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal)) :=
            mul_le_mul' le_rfl hpoint
        _ = ((2 * q : ℕ) : ENNReal) * (PairedReference.referenceExperiment adversary q s * (Contacts.contactCount s : ENNReal)) := by ring
    · rw [(PMF.apply_eq_zero_iff _ s).mpr hs]
      simp only [zero_mul, Finset.sum_const_zero, mul_zero, le_refl]
  calc Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] *
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
      ≤ (∑ a ∈ Contacts.sourceChains7, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
          PairedReference.referenceExperiment adversary q]) * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := mul_le_mul' hunion le_rfl
    _ = ∑ a ∈ Contacts.sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) *
          Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a | PairedReference.referenceExperiment adversary q]) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ Contacts.sourceChains7, (∑' s, PairedReference.referenceExperiment adversary q s *
          (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a) :=
        Finset.sum_le_sum fun a ha => hcharge a ha
    _ = ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s *
          (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamTot.errTotF S adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← FamContacts.errTot7F_eq]
        rfl
    _ ≤ ((2 * q : ℕ) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.contactCount s : ENNReal) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamTot.errTotF S adversary q := add_le_add halloc le_rfl
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl (FamContacts.reference_contacts_cost_leF H adversary q hq)) le_rfl

theorem reference_twoContacts_leFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] ≤
      (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) *
          (∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.prefixClassCount s : ENNReal)) /
        (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) * FamTot.errTotF S adversary q := by
  refine (reference_twoContacts_le_rawFam S H adversary q hq).trans (le_of_eq ?_)
  rw [ENNReal.add_div, big_div_mul]
  set E := ∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.prefixClassCount s : ENNReal)
  set T := FamTot.errTotF S adversary q
  set y := 1 - (q : ENNReal) / 2 ^ 128
  have hy0 : y ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hyt : y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt), pow_two, ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt)]
  push_cast
  ring

set_option linter.constructorNameAsVariable false in
theorem sum_errC_chainOf_leFam (S : FamScheme) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑ p : CanonGraph.LeafPos × Fin 58, FamLift.errCF S adversary q (Enc.chainAt p) ≤ FamTot.errTotF S adversary q := by
  have h1 : ∑ p : CanonGraph.LeafPos × Fin 58, FamLift.errCF S adversary q (Enc.chainAt p) =
      ∑ a ∈ Finset.univ.image Enc.chainAt, FamLift.errCF S adversary q a :=
    (Finset.sum_image (fun p _ p' _ h => chainOf_injective h)).symm
  have h2 : ∑ a ∈ Finset.univ.image Enc.chainAt, FamLift.errCF S adversary q a ≤
      ∑ a ∈ (Finset.univ.image Enc.chainAt).filter WotsExtract.SourceChain7, FamLift.errCF S adversary q a := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun a _ => ?_
    split_ifs with h
    · exact le_rfl
    · rw [FamLift.errCF, dif_neg h]
  have h3 : (Finset.univ.image Enc.chainAt).filter WotsExtract.SourceChain7 ⊆ Contacts.sourceChains7 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact (Contacts.mem_sourceChains7 a).mpr ha.2
  rw [← FamContacts.errTot7F_eq, h1]
  exact h2.trans (Finset.sum_le_sum_of_subset h3)

theorem reference_markerFirst_sum_le_ofFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hMS : ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkerAt s.answers s.trace (Enc.chainAt p) | PairedReference.referenceExperiment adversary q] ≤
      (5022/(2:ENNReal)^128) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal)) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst s.answers s.trace a | PairedReference.referenceExperiment adversary q] ≤
      2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
        ((5022 / 2 ^ 128 : ENNReal) * (∑' s, PairedReference.referenceExperiment adversary q s * (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal))) +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) * FamTot.errTotF S adversary q := by
  have hu0 : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hutop : (1 - (q : ENNReal) / 2 ^ 128) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hun0 : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hu0 (by simp)
  have huntop : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ ⊤ := ENNReal.mul_ne_top hutop (by simp)
  have hper : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerFirst s.answers s.trace (Enc.chainAt p) |
          PairedReference.referenceExperiment adversary q] ≤
        2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt s.answers s.trace (Enc.chainAt p) |
            PairedReference.referenceExperiment adversary q] +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
          FamLift.errCF S adversary q (Enc.chainAt p) := by
    intro p
    by_cases hs : WotsExtract.SourceChain7 (Enc.chainAt p)
    · simp only [hs, true_and]
      have hC := FamRestart2.source_markerFirst_at_leF (adversary := adversary) S H.grp_le H.caps H.width H.points
        q hq (Enc.chainAt p) hs
      set PF := Pr[fun s => ContactAfterStop (fun T trace => MarkerAt T trace (Enc.chainAt p)) s.answers s.trace
        (Enc.chainAt p) | PairedReference.referenceExperiment adversary q]
      set PM := Pr[fun s => MarkerAt s.answers s.trace (Enc.chainAt p) | PairedReference.referenceExperiment adversary q]
      set EC := FamLift.errCF S adversary q (Enc.chainAt p)
      have hrhs : 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) * PM =
          (((2 * q : ℕ) : ENNReal) * PM) / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
        generalize hu : (1 - (q : ENNReal) / 2 ^ 128) = u at hu0 hutop ⊢
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hu0) (Or.inl hutop)]
        push_cast
        ring
      rw [hrhs, ← big_div_mul, ENNReal.div_add_div_same]
      apply (ENNReal.le_div_iff_mul_le (Or.inl hun0) (Or.inl huntop)).mpr
      calc PF * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
          = (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * PF) := by ring
        _ ≤ ((2 * q : ℕ) : ENNReal) * PM + ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * EC := hC
    · simp only [hs, false_and]
      simp
  calc Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst s.answers s.trace a | PairedReference.referenceExperiment adversary q]
      ≤ Pr[fun s => ∃ p ∈ (Finset.univ : Finset (CanonGraph.LeafPos × Fin 58)),
          WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerFirst s.answers s.trace (Enc.chainAt p) |
          PairedReference.referenceExperiment adversary q] := by
        apply probEvent_mono''
        rintro s ⟨a, ha, hmf⟩
        obtain ⟨p, rfl⟩ := exists_chainAt ha
        exact ⟨p, by simp, ha, hmf⟩
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58,
          Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerFirst s.answers s.trace (Enc.chainAt p) |
            PairedReference.referenceExperiment adversary q] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58, (2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt s.answers s.trace (Enc.chainAt p) |
            PairedReference.referenceExperiment adversary q] +
          (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
            FamLift.errCF S adversary q (Enc.chainAt p)) :=
        Finset.sum_le_sum fun p _ => hper p
    _ = 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          ∑ p : CanonGraph.LeafPos × Fin 58,
            Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt s.answers s.trace (Enc.chainAt p) |
              PairedReference.referenceExperiment adversary q] +
          (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
            ∑ p : CanonGraph.LeafPos × Fin 58, FamLift.errCF S adversary q (Enc.chainAt p) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl hMS) (mul_le_mul' le_rfl (sum_errC_chainOf_leFam S adversary q))

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open CanonicalRef.Normalized
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem reference_primitive_leFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q<2^128)
 (w v : ENNReal) (hwv : w+v=1) :
 Pr[Combined | PairedReference.referenceExperiment adversary q] ≤
 Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] + (2^142:ENNReal)⁻¹ +
 prefixCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.prefixClassCount s:ENNReal)) +
 encodingCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(encodingCount s:ENNReal)) +
 (2^128:ENNReal)⁻¹*(∑'s,PairedReference.referenceExperiment adversary q s*(PairedReference.otherCount s:ENNReal)) +
 errCoeff q w v*FamTot.errTotF S adversary q := by
 -- top-nonce layer (r3-lean-nonsec): the structural bound carries Pr[CapFail] ≤ (2^142)⁻¹; fold it into the
 -- other-mass argument of weighted_union_le as (2^128)⁻¹ * (EO + 2^128 * (2^142)⁻¹).
 have hcancel : ∀ x : ENNReal, (2^128:ENNReal)⁻¹ * (x + 2^128 * (2^142:ENNReal)⁻¹) =
     (2^128:ENNReal)⁻¹ * x + (2^142:ENNReal)⁻¹ := fun x => by
   rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]
 have key : Pr[Combined | PairedReference.referenceExperiment adversary q] ≤
     Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] +
     prefixCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.prefixClassCount s:ENNReal)) +
     encodingCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(encodingCount s:ENNReal)) +
     (2^128:ENNReal)⁻¹*((∑'s,PairedReference.referenceExperiment adversary q s*(PairedReference.otherCount s:ENNReal)) + 2^128 * (2^142:ENNReal)⁻¹) +
     errCoeff q w v*FamTot.errTotF S adversary q := by
  refine weighted_union_le (PairedReference.referenceExperiment adversary q)
    Combined ReferenceFailed EncodingMatch Structural TwoEdge TwoContacts MarkerFirstEvent ContactFirstEvent
    q w v _ _ _ _ hwv combined_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact CanonicalRef.reference_encodingMatch_le adversary q
  · rw [hcancel]
    exact structural_reference_le adversary q (PairedReference.reference_structural_in_le adversary q)
  · exact FamContacts.reference_twoEdge_leF H adversary q hq
  · exact Restart.reference_twoContacts_leFam S H adversary q hq
  · exact Restart.reference_markerFirst_sum_le_ofFam S H adversary q hq (CanonicalRef.reference_marker_sum_le adversary q)
  · exact (CanonicalRef.Contact93.reference_contactFirst_le adversary q).trans
      (mul_le_mul' le_rfl (FamContacts.reference_contacts_cost_leF H adversary q hq))
  · exact (nonstructural_reference_le adversary q).trans (FamContacts.reference_contacts_cost_leF H adversary q hq)
 refine key.trans (le_of_eq ?_)
 rw [hcancel]
 ring

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem errTotF_ne_topFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q<2^128) :
    FamTot.errTotF S adversary q≠⊤ :=
  ne_top_of_le_ne_top (by finiteness) (FamTot.errTotF_le H adversary q hq)

theorem primitive_real_of_rawFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax) (hC : Cmax ≤ 305)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q<2^128)
    (hy : (q:ℝ)/2^128≤3/2500) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1)
    (hp:prefixMass adversary q≠⊤) (he:encodingMass adversary q≠⊤)
    (eventProbability otherMass : ENNReal) (ho:otherMass≠⊤)
    (hraw : eventProbability ≤ 1/(2:ENNReal)^139+(2^142:ENNReal)⁻¹+
      prefixCoeff q w v/2^128*prefixMass adversary q+
      encodingCoeff q w v/2^128*encodingMass adversary q+
      (2^128:ENNReal)⁻¹*otherMass+errCoeff q w v*FamTot.errTotF S adversary q)
    (theta : ℝ) (hprefix:canonicalPrefix ((q:ℝ)/2^128) w.toReal≤theta)
    (hencoding:canonicalEncoding ((q:ℝ)/2^128) w.toReal≤theta)
    (herror:canonicalError ((q:ℝ)/2^128) w.toReal≤1061/1000) :
    eventProbability.toReal ≤
      theta*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128)+
      otherMass.toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) := by
  have hc1:=prefixCoeff_ne_top q hq w v hw hv
  have hc2:=encodingCoeff_ne_top q hq w v hw
  have hc3:=errCoeff_ne_top q hq w v hw hv
  have hfin:=errTotF_ne_topFam S H adversary q hq
  have h:=ENNReal.toReal_mono (by finiteness) hraw
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_inv,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    prefixCoeff_toReal q hq w v hw hv hwv,encodingCoeff_toReal q hq w v hw,
    errCoeff_toReal q hq w v hw hv hwv] at h
  have he0 : 0≤canonicalError ((q:ℝ)/2^128) w.toReal := by
    rw [←errCoeff_toReal q hq w v hw hv hwv]
    exact ENNReal.toReal_nonneg
  have hseed := FamTot.seedErrorBoundF H hC adversary q hq hy
  have herr:=grouped_weighted_error ((q:ℝ)/2^128) (FamTot.errTotF S adversary q).toReal
    (canonicalError ((q:ℝ)/2^128) w.toReal) he0 herror hseed
  have hp' := mul_le_mul_of_nonneg_right hprefix (show 0≤(prefixMass adversary q).toReal/2^128 by positivity)
  have he' := mul_le_mul_of_nonneg_right hencoding (show 0≤(encodingMass adversary q).toReal/2^128 by positivity)
  simp only [div_eq_mul_inv] at h hp' he' herr ⊢
  nlinarith

theorem primitive_real_of_failureFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax) (hC : Cmax ≤ 305)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤3/2500) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1)
    (hfailed : Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139)
    (theta : ℝ) (hprefix:canonicalPrefix ((q:ℝ)/2^128) w.toReal≤theta)
    (hencoding:canonicalEncoding ((q:ℝ)/2^128) w.toReal≤theta)
    (herror:canonicalError ((q:ℝ)/2^128) w.toReal≤1061/1000) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      theta*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) := by
  have hqN : q<2^128 := by omega
  have hf := PairedSmallT.masses_finite adversary q hq
  have hraw := (reference_primitive_leFam S H adversary q hqN w v hwv).trans
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hfailed le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
  exact primitive_real_of_rawFam S H hC adversary q hqN hy w v hw hv hwv hf.1 hf.2.1
    _ (PairedSmallT.otherMass adversary q) hf.2.2.1 hraw theta hprefix hencoding herror

theorem primitive_middle_real_of_failureFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤3/2500)
    (hfailed : Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (99847/50000)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) := by
  have hc := middle_coefficients_t ((q:ℝ)/2^128) (by positivity) hy
  apply primitive_real_of_failureFam S H hC adversary q hq hy (1023/50000) (48977/50000)
    (by finiteness) (by finiteness) (by norm_num [ENNReal.div_add_div_same]; exact ENNReal.div_self (by norm_num) (by finiteness)) hfailed
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.2

theorem primitive_tiny_real_of_failureFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤1/2^28)
    (hfailed : Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (249/125)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) := by
  have hc := tiny_coefficients_t ((q:ℝ)/2^128) (by positivity) hy
  apply primitive_real_of_failureFam S H hC adversary q hq (hy.trans (by norm_num)) (3/100) (97/100)
    (by finiteness) (by finiteness) (by norm_num [ENNReal.div_add_div_same]; exact ENNReal.div_self (by norm_num) (by finiteness)) hfailed
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.2

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false

theorem primitive_middle_realFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤3/2500) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (99847/50000)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) :=
  primitive_middle_real_of_failureFam S H hC adversary q hq hy (reference_failed_le adversary q)

theorem primitive_tiny_realFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤1/2^28) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (249/125)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) :=
  primitive_tiny_real_of_failureFam S H hC adversary q hq hy (reference_failed_le adversary q)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem middle_boundFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow:1/(2:ℝ)^28≤(q:ℝ)/2^128) (hhigh:(q:ℝ)/2^128≤3/2500) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  apply clean_outer_ennrealG adversary q hq
  apply middle_clean_closingG adversary q hq hlow hhigh (1153/1000000) le_rfl ?_
    (completed_partial_certifiedG adversary q hq)
  have hp:=CanonicalWeighted.primitive_middle_realFam S H hC adversary q hq hhigh
  have h:=clean_probability_real_ofG adversary q hq (completed_split_canonical adversary q hq)
    (99847/50000) (1153/1000000) (by finiteness) (by finiteness) (by
      simpa (disch:=positivity) only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (by norm_num : (1:ℝ)/1024≤99847/50000))
    excess_middle_actualG (by simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using! hp)
    (completed_incomplete_bound adversary q hq)
    (by simpa only [one_div] using FtsOverflow.Paired.cleanWin_noOverflow_le adversary q hq)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using h

theorem tiny_boundFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive:1≤q) (hhigh:(q:ℝ)/2^128≤1/2^28) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  apply clean_outer_ennrealG adversary q hq
  apply tiny_clean_closingG adversary q hq hpositive hhigh (18/5000) le_rfl ?_
    (completed_partial_certifiedG adversary q hq)
  have hp:=CanonicalWeighted.primitive_tiny_realFam S H hC adversary q hq hhigh
  have h:=clean_probability_real_ofG adversary q hq (completed_split_canonical adversary q hq)
    (249/125) (18/5000) (by finiteness) (by finiteness) (by
      simpa (disch:=positivity) only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (by norm_num : (1:ℝ)/1024≤249/125))
    excess_tiny_actualG (by simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using! hp)
    (completed_incomplete_bound adversary q hq)
    (by simpa only [one_div] using FtsOverflow.Paired.cleanWin_noOverflow_le adversary q hq)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using h

theorem small_boundFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive:1≤q) (hhigh:(q:ℝ)/2^128≤3/2500) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  by_cases ht:(q:ℝ)/2^128≤1/2^28
  · exact tiny_boundFam S H hC adversary q hq hpositive ht
  · exact middle_boundFam S H hC adversary q hq (le_of_lt (lt_of_not_ge ht)) hhigh

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Secc.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3M.Final.Paired
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme layoutScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- **The live security theorem through the family seed-error charge**: any family scheme with the family-restart
hypotheses and per-test charge `Cmax ≤ 305`. -/
theorem t3_securityP_fam (S : FamScheme) (Cmax : Nat)
    (H : ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot.FamHyps S Cmax) (hC : Cmax ≤ 305) :
    ClaudeWCT.W9.T3M.Final.Paired.SecurityP := by
  apply PairedOuter.PaddedGame.securityP_of_clean_bound
  intro adversary q hpositive hq
  by_cases hsmall : (q:ℝ)/2^128 ≤ 3/2500
  · exact Wots.PairedSmallT.small_boundFam S H hC adversary q hq hpositive hsmall
  · exact LargeCoupling.Paired.large_bound adversary q hq (le_of_not_ge hsmall)

/-- **The live security theorem of the v6 scheme** (the `Correctness` layout: lower 7-leaf families, charge 301). -/
theorem t3_securityP_layout : ClaudeWCT.W9.T3M.Final.Paired.SecurityP :=
  t3_securityP_fam layoutScheme 301 ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot.layoutHyps
    (by norm_num)

end ClaudeWCT.W9.T3.Secc.Paired
