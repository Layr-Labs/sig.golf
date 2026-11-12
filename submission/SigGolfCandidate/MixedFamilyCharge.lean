import SigGolfCandidate.Merge112
import SigGolfCandidate.MixedSeedBudget
set_option debug.skipKernelTC false
namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamSum
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized (depth_eq)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
open SphincsSecurity.QueryCap (recorded counted calls)
open SigGolfCandidate.T3.Security.Wots.Mask (chainCount_le)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable (S : FamScheme)

/-- Restricting source chains preserves the family charge bound with the selected maximum. -/
theorem card_famChains_subset_le (L : Finset ChainAddr)
    (hsub : L ⊆ SigGolfCandidate.T3.Security.Wots.sourceChains) (Cmax : Nat)
    (hC : ∀ a ∈ L, S.grp a.key.lay * chainCount a.key.lay ≤ Cmax) (F : FamAddr) :
    (L.filter fun a => famOf S a.key = F).card ≤ Cmax := by
  classical
  by_cases he : ∃ a ∈ L, famOf S a.key = F
  · obtain ⟨a, ha, hF⟩ := he
    have hlay : a.key.lay = F.lay := congrArg FamAddr.lay hF
    calc (L.filter fun a => famOf S a.key = F).card
        ≤ (SigGolfCandidate.T3.Security.Wots.sourceChains.filter fun a => famOf S a.key = F).card := by
          apply Finset.card_le_card
          intro c hc
          obtain ⟨hc, he⟩ := Finset.mem_filter.mp hc
          exact Finset.mem_filter.mpr ⟨hsub hc, he⟩
      _ ≤ S.grp F.lay * chainCount F.lay := card_famChains_le S F
      _ ≤ Cmax := by simpa only [← hlay] using hC a ha
  · have hempty : (L.filter fun a => famOf S a.key = F) = ∅ := by
      apply Finset.filter_false_of_mem
      intro a ha hF
      exact he ⟨a, ha, hF⟩
    simp only [hempty, Finset.card_empty]; exact Nat.zero_le _

theorem sum_NL_leF_subset (L : Finset ChainAddr)
    (hsub : L ⊆ SigGolfCandidate.T3.Security.Wots.sourceChains) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (Cmax : Nat) (hC : ∀ a ∈ L, S.grp a.key.lay * chainCount a.key.lay ≤ Cmax)
    (s : RefSample) :
    ∑ a ∈ L, NLaF S a s ≤ Cmax * s.trace.length := by
  classical
  let test : FamAddr → Entry → Prop := fun F e =>
    StepZeroUnrevF S F s.answers e.1 ∧ ∃ L, WotsExtract.SourceLeaf L ∧ famOf S L = F
  have hcongr : ∀ a ∈ L, NLaF S a s =
      (s.trace.filter fun e => decide (test (famOf S a.key) e)).length := by
    intro a ha
    have hs := (SigGolfCandidate.T3.Security.Wots.mem_sourceChains a).mp (hsub ha)
    unfold NLaF NLF
    congr 1
    apply List.filter_congr
    intro e _
    simp only [test, decide_eq_decide]
    exact ⟨fun h => ⟨h, a.key, hs.1, rfl⟩, fun h => h.1⟩
  rw [Finset.sum_congr rfl hcongr]
  exact ClaudeWCT.Arith.SideChannel.GroupedFamily.sum_charge_le L
    (fun a => famOf S a.key) test Cmax
    (fun e F F' h h' => by
      obtain ⟨h1, L, hL, rfl⟩ := h
      obtain ⟨h1', L', hL', rfl⟩ := h'
      exact stepZero_fam_unique S hgrp hL hL' h1 h1')
    (fun F => card_famChains_subset_le S L hsub Cmax hC F) s.trace

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamSum

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf chainOfF FamData FamOkS)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW gptS)
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
noncomputable local instance : Fintype Coordinate := coordinateFintype
open SphincsSecurity.QueryCap (recorded counted calls)
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame

theorem errC_leF_bound (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
    (hws : ∀ lay, chainCount lay ≤ S.stride lay)
    (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
    (q : ℕ) (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1) (a : ChainAddr)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ R : Tables (PairedReference.referenceInputs adversary), FamCore.restartFactor S (FamSum.famOf S a.key) R q ≤ B) :
    errCF S adversary q a ≤ ENNReal.ofReal (B / (1 - (Fintype.card Digest : ℝ)⁻¹ * q)) *
      ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLaF S a s : ℝ≥0∞) := by
  unfold errCF
  split_ifs with h
  · have hF := famOk_of_source S hgrp h.1
    unfold FamSum.NLaF
    rw [← frozenCount_eqF S hF h.1.1 (caOf S a h.2) (chainOf_caOf S a h.2) (real_caOf S h) q h]
    exact errAR_sum_leF_bound (referenceInputs_subset adversary) hF h.1.1 (caOf S a h.2) (chainOf_caOf S a h.2)
      (fun T => PairedReference.referenceGame T adversary q) (fun T T' h' => GDseed_fam S hF q T T' h') q
      (fun T => Core.GDseed_queryBound q T) C (hws _) (hb _) hq B hB0 hB
  · exact bot_le


theorem errC_sum_leF_subset (S : FamScheme) (L : Finset ChainAddr)
    (hsub : L ⊆ SigGolfCandidate.T3.Security.Wots.sourceChains) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (Cmax : ℕ)
    (hC : ∀ a ∈ L, S.grp a.key.lay * chainCount a.key.lay ≤ Cmax) (C : FamCaps S)
    (hws : ∀ lay, chainCount lay ≤ S.stride lay)
    (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
    (q : ℕ) (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ a ∈ L, ∀ R : Tables (PairedReference.referenceInputs adversary),
      FamCore.restartFactor S (FamSum.famOf S a.key) R q ≤ B) :
    ∑ a ∈ L, errCF S adversary q a ≤
      ENNReal.ofReal (B / (1 - (Fintype.card Digest : ℝ)⁻¹ * q)) * ((Cmax : ℝ≥0∞) * q) := by
  calc ∑ a ∈ L, errCF S adversary q a
      ≤ ∑ a ∈ L, ENNReal.ofReal (B / (1 - (Fintype.card Digest : ℝ)⁻¹ * q)) *
          ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLaF S a s : ℝ≥0∞) :=
        Finset.sum_le_sum fun a ha => errC_leF_bound S hgrp C hws hb q hq a B hB0 (hB a ha)
    _ = ENNReal.ofReal (B / (1 - (Fintype.card Digest : ℝ)⁻¹ * q)) * ∑' s, PairedReference.referenceExperiment adversary q s *
          ((∑ a ∈ L, FamSum.NLaF S a s : ℕ) : ℝ≥0∞) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine tsum_congr fun s => ?_
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ ENNReal.ofReal (B / (1 - (Fintype.card Digest : ℝ)⁻¹ * q)) * ((Cmax : ℝ≥0∞) * q) := by
        refine mul_le_mul' le_rfl ?_
        calc ∑' s, PairedReference.referenceExperiment adversary q s *
              ((∑ a ∈ L, FamSum.NLaF S a s : ℕ) : ℝ≥0∞)
            ≤ ∑' s, PairedReference.referenceExperiment adversary q s * ((Cmax : ℝ≥0∞) * q) := by
              refine ENNReal.tsum_le_tsum fun s => ?_
              by_cases hs : s ∈ (PairedReference.referenceExperiment adversary q).support
              · refine mul_le_mul' le_rfl ?_
                have h1 := FamSum.sum_NL_leF_subset S L hsub hgrp Cmax hC s
                have h2 := Core.ref_trace_length_le adversary q s hs
                have : ∑ a ∈ L, FamSum.NLaF S a s ≤ Cmax * q := by
                  calc _ ≤ Cmax * s.trace.length := h1
                    _ ≤ Cmax * q := Nat.mul_le_mul_left Cmax h2
                exact_mod_cast this
              · rw [(PMF.apply_eq_zero_iff _ s).mpr hs, zero_mul, zero_mul]
          _ = (Cmax : ℝ≥0∞) * q := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]


noncomputable def topChains : Finset ChainAddr := SigGolfCandidate.T3.Security.Wots.sourceChains.filter fun a => a.key.lay = 0
noncomputable def lowerChains : Finset ChainAddr := SigGolfCandidate.T3.Security.Wots.sourceChains.filter fun a => a.key.lay ≠ 0

theorem layout_top_error (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1) :
    ∑ a ∈ topChains, errCF layoutScheme adversary q a ≤
      ENNReal.ofReal (ClaudeWCT.Arith.SideChannel.Mixed.oldFactor q / (1 - (Fintype.card Digest : ℝ)⁻¹*q)) *
        ((216 : ℝ≥0∞)*q) := by
  refine errC_sum_leF_subset layoutScheme topChains (Finset.filter_subset _ _) FamTot.layoutHyps.grp_le 216
    ?_ layoutCaps FamTot.layoutHyps.width FamTot.layoutHyps.points q hq
    (ClaudeWCT.Arith.SideChannel.Mixed.oldFactor q)
    (ClaudeWCT.Arith.SideChannel.Mixed.factor_nonneg false q) ?_
  · intro a ha
    have hl := (Finset.mem_filter.mp ha).2
    change WCT9.famGrp a.key.lay * chainCount a.key.lay ≤ 216
    rw [hl]
    decide
  · intro a _ R
    exact FamCore.restartFactor_le_old layoutScheme (FamSum.famOf layoutScheme a.key) R q

theorem layout_lower_error (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1) :
    ∑ a ∈ lowerChains, errCF layoutScheme adversary q a ≤
      ENNReal.ofReal (ClaudeWCT.Arith.SideChannel.Mixed.fourFactor q / (1 - (Fintype.card Digest : ℝ)⁻¹*q)) *
        ((688 : ℝ≥0∞)*q) := by
  refine errC_sum_leF_subset layoutScheme lowerChains (Finset.filter_subset _ _) FamTot.layoutHyps.grp_le 688
    ?_ layoutCaps FamTot.layoutHyps.width FamTot.layoutHyps.points q hq
    (ClaudeWCT.Arith.SideChannel.Mixed.fourFactor q) (by unfold ClaudeWCT.Arith.SideChannel.Mixed.fourFactor; positivity) ?_
  · intro a ha
    have hl := (Finset.mem_filter.mp ha).2
    change WCT9.famGrp a.key.lay * chainCount a.key.lay ≤ 688
    simp [WCT9.famGrp, FamTot.chainCount_cases, hl]
  · intro a ha R
    have hl := (Finset.mem_filter.mp ha).2
    exact FamCore.restartFactor_lower (FamSum.famOf layoutScheme a.key) R q hl


theorem layout_total_error (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (hq : q < 2^128) :
    FamTot.errTotF layoutScheme adversary q ≤
      ENNReal.ofReal (ClaudeWCT.Arith.SideChannel.Mixed.oldFactor q / (1 - (Fintype.card Digest : ℝ)⁻¹*q)) * ((216 : ℝ≥0∞)*q) +
      ENNReal.ofReal (ClaudeWCT.Arith.SideChannel.Mixed.fourFactor q / (1 - (Fintype.card Digest : ℝ)⁻¹*q)) * ((688 : ℝ≥0∞)*q) := by
  have hh := ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted.query_card_lt_one q hq
  unfold FamTot.errTotF
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun a : ChainAddr => a.key.lay = 0)]
  exact add_le_add (layout_top_error adversary q hh) (layout_lower_error adversary q hh)

theorem layout_total_error_toReal (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (hq : q < 2^128) :
    (FamTot.errTotF layoutScheme adversary q).toReal ≤
      (432*((q:ℝ)/2^128)^3+22016*((q:ℝ)/2^128)^4)/(1-(q:ℝ)/2^128) := by
  have hcard : (Fintype.card Digest : ℝ) = 2^128 := by rw [Fintype.card_bitVec]; norm_num
  have hpos : 0 < 1-(q:ℝ)/2^128 := by
    have hqr : (q:ℝ) < 2^128 := by exact_mod_cast hq
    exact sub_pos.mpr ((div_lt_one (by positivity)).2 hqr)
  have hold : 0 ≤ ClaudeWCT.Arith.SideChannel.Mixed.oldFactor q :=
    ClaudeWCT.Arith.SideChannel.Mixed.factor_nonneg false q
  have hfour : 0 ≤ ClaudeWCT.Arith.SideChannel.Mixed.fourFactor q := by
    unfold ClaudeWCT.Arith.SideChannel.Mixed.fourFactor
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 4)) (pow_nonneg (Nat.cast_nonneg _) 3)
  have hden : 0 ≤ 1-(Fintype.card Digest : ℝ)⁻¹*q := by
    rw [hcard]; simpa [div_eq_mul_inv, mul_comm] using hpos.le
  have h := ENNReal.toReal_mono (by finiteness) (layout_total_error adversary q hq)
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (div_nonneg hold hden), ENNReal.toReal_ofReal (div_nonneg hfour hden),
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at h
  unfold ClaudeWCT.Arith.SideChannel.Mixed.oldFactor ClaudeWCT.Arith.SideChannel.Mixed.fourFactor at h
  rw [hcard] at h
  have hk := ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted.kconst_le_sq q
  have hnn : 0 ≤ (q:ℝ) := Nat.cast_nonneg q
  have hscale : 0 ≤ (2*((2:ℝ)^128)⁻¹^3/(1-((2:ℝ)^128)⁻¹*q))*((216:ℝ)*q) := by
    apply mul_nonneg
    · apply div_nonneg
      · exact mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) 128)) 3)
      · simpa [div_eq_mul_inv, mul_comm] using hpos.le
    · exact mul_nonneg (by norm_num) hnn
  have hmul := mul_le_mul_of_nonneg_right hk hscale
  calc (FamTot.errTotF layoutScheme adversary q).toReal
      ≤ (2*((2:ℝ)^128)⁻¹^3*(q:ℝ)^2/(1-((2:ℝ)^128)⁻¹*q))*((216:ℝ)*q) +
          (32*((2:ℝ)^128)⁻¹^4*(q:ℝ)^3/(1-((2:ℝ)^128)⁻¹*q))*((688:ℝ)*q) := by
        apply h.trans
        refine add_le_add ?_ le_rfl
        convert hmul using 1 <;> ring
    _ = _ := by ring


theorem layout_seed_error (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (hq : q < 2^128) (hy : (q:ℝ)/2^128 ≤ 1251/1000000) :
    (FamTot.errTotF layoutScheme adversary q).toReal ≤ (755/1000)*((q:ℝ)/2^128)^2 := by
  refine (layout_total_error_toReal adversary q hq).trans ?_
  simpa only [show (2:ℝ)*216=432 by norm_num, show (32:ℝ)*688=22016 by norm_num] using
    MixedSeedBudget.seed_error ((q:ℝ)/2^128) (by positivity) hy

theorem layout_seed_error_split (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (hq : q < 2^128) (hy : (q:ℝ)/2^128 ≤ 2163/1000000) :
    (FamTot.errTotF layoutScheme adversary q).toReal ≤ (261/200)*((q:ℝ)/2^128)^2 := by
  refine (layout_total_error_toReal adversary q hq).trans ?_
  simpa only [show (2:ℝ)*216=432 by norm_num, show (32:ℝ)*688=22016 by norm_num] using
    MixedSeedBudget.seed_error_split ((q:ℝ)/2^128) (by positivity) hy

#print axioms layout_seed_error
#print axioms layout_seed_error_split
#print axioms layout_total_error_toReal
#print axioms layout_top_error
#print axioms layout_lower_error
#print axioms errC_sum_leF_subset
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
