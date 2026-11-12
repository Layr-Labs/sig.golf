import SigGolfCandidate.Merge111
import SigGolfCandidate.QueryOverflow40
import SigGolfCandidate.OverflowScalar
set_option debug.skipKernelTC false
namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 2048
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem clean_probability_real_overflow (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hsplit : ∀ z,z∈(PairedSeccLaw.completedExperiment adversary q hq).support →
      QueryRecorded.CleanWin q z.1 → CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z)
    (theta rate : ENNReal) (htheta:theta≠⊤) (hratefin:rate≠⊤) (hmin:28883/2500000≤theta)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-(theta-28883/2500000))≤rate)
    (errq : ℝ)
    (hprimitive : (Pr[fun s=>combinedEvent.holds s.answers s.trace |
      PairedReference.referenceExperiment adversary q]).toReal ≤
        theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128)+
        (otherMass adversary q).toReal/2^128+errq*((q:ℝ)/2^128)^2+(1/2^139+1/2^142))
    (hincomplete : Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^138)
    (overflow : ENNReal) (hoverflowfin : overflow ≠ ⊤)
    (hoverflow : Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq]≤overflow) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate.toReal+errq*((q:ℝ)/2^128)^2+(1/2^139+1/2^142+1/2^138)+overflow.toReal := by
  have hf := full_probability_real theta rate htheta hratefin hmin adversary q hq hrate
  have hinc := ENNReal.toReal_mono (by finiteness) hincomplete
  have hov := ENNReal.toReal_mono hoverflowfin hoverflow
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at hinc hov
  have hevent {α:Type} (law:PMF α) (P:α→Prop) : Pr[P|law]≠⊤ := ne_top_of_le_ne_top (by simp) probEvent_le_one
  have h:=ENNReal.toReal_mono (by exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩)
    (cleanWin_le_union_cases_of_split adversary q hq hsplit)
  simp only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (hevent _ _) (hevent _ _)] at h
  nlinarith


noncomputable def tinyOverflowBound (q : Nat) : ENNReal :=
  if q < 256 then (2^137)⁻¹ else (q : ENNReal)/2^136

theorem tinyOverflowBound_finite (q : Nat) : tinyOverflowBound q ≠ ⊤ := by
  unfold tinyOverflowBound; split_ifs <;> finiteness

theorem tinyOverflowBound_real (q : Nat) :
    (tinyOverflowBound q).toReal = if q < 256 then (1:ℝ)/2^137 else ((q:ℝ)/2^128)/256 := by
  unfold tinyOverflowBound
  split_ifs <;> simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_div, ENNReal.toReal_natCast]
  · ring
  · norm_num; ring

theorem completed_tinyOverflow (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤ tinyOverflowBound q := by
  by_cases hs : q < 256
  · simpa only [tinyOverflowBound, if_pos hs] using
      QueryChargeResearch.ValidPotential40.cleanWin_noOverflow_small adversary q hq hs
  · simpa only [tinyOverflowBound, if_neg hs] using
      QueryChargeResearch.ValidPotential40.cleanWin_noOverflow_query adversary q hq

theorem tiny_clean_closing_overflow (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive : 1≤q) (hhigh : (q:ℝ)/2^128≤1/2^28)
    (rate : ℝ) (hrate : rate≤18/5000)
    (hclean : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      (249/125)*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate+(802/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142+1/2^138)+(tinyOverflowBound q).toReal)
    (hpartial : Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*((22894/50)+28883/2500000)/(2*2^128)+BPair.pairTerm q) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128) := by
  by_cases hs : q < 256
  · apply tiny_clean_closingG adversary q hq hpositive hhigh rate hrate ?_ hpartial
    have he := tinyOverflowBound_real q
    rw [if_pos hs] at he
    have habs : (1:ℝ)/2^139+1/2^142+1/2^138+1/2^137 ≤ 1/2^136 := by norm_num
    rw [he] at hclean
    linarith
  ·
    have hsmall : (q:ℝ)/2^128≤2163/1000000 := hhigh.trans (by norm_num)
    have hlow : 1/(2:ℝ)^128≤(q:ℝ)/2^128 := div_le_div_of_nonneg_right (by exact_mod_cast hpositive) (by positivity)
    have hquad := paired_partial_denominatorRC _ _ hsmall (partial_probability_real adversary q hq hpartial)
    have hcost := completed_partial_normalized adversary q hq
    change (1-(q:ℝ)/2^128)*_≤(otherMass adversary q).toReal/2^128 at hcost
    rw [mul_comm] at hcost
    have hbudget := tiny_class_budgetRC _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
      (masses_normalized adversary q hq) hhigh ENNReal.toReal_nonneg hcost hquad
    have h256 : (256:ℝ)/2^128 ≤ (q:ℝ)/2^128 :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_of_not_gt hs) (by positivity)
    have he : (tinyOverflowBound q).toReal ≤ ((q:ℝ)/2^128)/256 := by
      rw [tinyOverflowBound_real, if_neg hs]
    have hbound := QueryChargeResearch.OverflowClosing.tiny_above256 ((q:ℝ)/2^128) rate
      (tinyOverflowBound q).toReal h256 hhigh hrate he
    nlinarith [sq_nonneg ((q:ℝ)/2^128)]

theorem middle_clean_closing_overflow (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow : 1/(2:ℝ)^28≤(q:ℝ)/2^128) (hhigh : (q:ℝ)/2^128≤2163/1000000)
    (rate : ℝ) (hrate : rate≤2143/1000000)
    (hclean : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      (397071/200000)*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate+(1850/1000)*((q:ℝ)/2^128)^2+1/2^87)
    (hpartial : Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*((22894/50)+28883/2500000)/(2*2^128)+BPair.pairTerm q) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128) := by
  have hquad := paired_partial_denominatorRC _ _ hhigh (partial_probability_real adversary q hq hpartial)
  have hcost := completed_partial_normalized adversary q hq
  change (1-(q:ℝ)/2^128)*_≤(otherMass adversary q).toReal/2^128 at hcost
  rw [mul_comm] at hcost
  have hbudget := class_budgetRC _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    (masses_normalized adversary q hq) hhigh ENNReal.toReal_nonneg hcost hquad
  have hbound := QueryChargeResearch.OverflowClosing.middle_absolute88 ((q:ℝ)/2^128) rate hlow hhigh hrate
  linarith

#print axioms clean_probability_real_overflow
#print axioms tiny_clean_closing_overflow
#print axioms middle_clean_closing_overflow
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
