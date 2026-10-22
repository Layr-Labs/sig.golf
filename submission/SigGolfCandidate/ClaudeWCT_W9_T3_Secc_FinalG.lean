import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_Final
import SigGolfCandidate.ClaudeWCT_Arith_GroupedFamily

/-! # The live small route parametrized by the seed-error bound (r3-lean-seedfam, family closing for `g ≤ 7`)

`SeedErrorBound`: on the small window `y = q/2^128 ≤ 3/2500`, `errTot ≤ (733/1000) y²`. It holds for every per-test
chain charge `C ≤ 305` once `errTot ≤ 2 C y³ / (1 - y)` (the one-sided side-channel constant, `kconst q = q²`):
`seedErrorBound_of_charge`. Today's leaf families (`C = 54`, `errTot_toReal_sharp`) satisfy it
(`seedErrorBound_current`); `g = 7` lower families (`C = 43·7 = 301`) need `errTot ≤ 602 y³/(1-y)` from the family
restart. Copies of the Paired small-route chain (`…G`) use the weighted error `799/1000` (`grouped_weighted_error`)
and the middle closing `grouped_middle_closing` (`767/1000 + 799/1000`); the large route is unchanged.
`t3_securityP_of_seedError` : `SeedErrorBound → SecurityP`, and `t3_securityP_kappa2` instantiates it today.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open ENNReal SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
/-- The seed-error hypothesis of the small route. -/
def SeedErrorBound : Prop :=
  ∀ (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat), q < 2 ^ 128 → (q : ℝ) / 2 ^ 128 ≤ 3 / 2500 →
    (CanonicalRef.Normalized.Contacts.errTot adversary q).toReal ≤ (733 / 1000) * ((q : ℝ) / 2 ^ 128) ^ 2

/-- Any per-test chain charge `C ≤ 305` with `errTot ≤ 2 C y³/(1-y)` gives the seed-error bound. -/
theorem seedErrorBound_of_charge (C : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ 305)
    (h : ∀ (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat), q < 2 ^ 128 →
      (CanonicalRef.Normalized.Contacts.errTot adversary q).toReal ≤
        2 * C * ((q : ℝ) / 2 ^ 128) ^ 3 / (1 - (q : ℝ) / 2 ^ 128)) : SeedErrorBound :=
  fun adversary q hq hy => (h adversary q hq).trans (grouped_seed_error C _ hC0 hC (by positivity) hy)

/-- `g = 7`: the family restart must deliver `errTot ≤ 602 y³/(1-y)`. -/
theorem seedErrorBound_g7
    (h : ∀ (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat), q < 2 ^ 128 →
      (CanonicalRef.Normalized.Contacts.errTot adversary q).toReal ≤
        602 * ((q : ℝ) / 2 ^ 128) ^ 3 / (1 - (q : ℝ) / 2 ^ 128)) : SeedErrorBound :=
  seedErrorBound_of_charge 301 (by norm_num) (by norm_num) fun adversary q hq =>
    (h adversary q hq).trans (le_of_eq (by ring))
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem clean_probability_real_ofG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hsplit : ∀ z,z∈(PairedSeccLaw.completedExperiment adversary q hq).support →
      QueryRecorded.CleanWin q z.1 → CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z)
    (theta rate : ENNReal) (htheta:theta≠⊤) (hratefin:rate≠⊤) (hmin:1/1024≤theta)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-(theta-1/1024))≤rate)
    (hprimitive : (Pr[fun s=>combinedEvent.holds s.answers s.trace |
      PairedReference.referenceExperiment adversary q]).toReal ≤
        theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128)+
        (otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142))
    (hincomplete : Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^138)
    (hoverflow : Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^137) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate.toReal+(778/1000)*((q:ℝ)/2^128)^2+1/2^136 := by
  have hf := full_probability_real theta rate htheta hratefin hmin adversary q hq hrate
  have hinc := ENNReal.toReal_mono (by finiteness) hincomplete
  have hov := ENNReal.toReal_mono (by finiteness) hoverflow
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
  -- top-nonce layer (r3-lean-nonsec): the primitive constant carries Pr[CapFail] ≤ 1/2^142
  have habs : (1:ℝ)/2^139+1/2^142+1/2^138+1/2^137≤1/2^136 := by norm_num
  nlinarith


end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem middle_clean_closingG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow : 1/(2:ℝ)^28≤(q:ℝ)/2^128) (hhigh : (q:ℝ)/2^128≤3/2500)
    (rate : ℝ) (hrate : rate≤1153/1000000)
    (hclean : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      (99847/50000)*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate+(778/1000)*((q:ℝ)/2^128)^2+1/2^136)
    (hpartial : Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(378+1/1024)/(2*2^128)+BPair.pairTerm q) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128) := by
  have hquad := paired_partial_denominatorRC _ _ hhigh (partial_probability_real adversary q hq hpartial)
  have hcost := completed_partial_normalized adversary q hq
  change (1-(q:ℝ)/2^128)*_≤(otherMass adversary q).toReal/2^128 at hcost
  rw [mul_comm] at hcost
  have hbudget := class_budgetRC _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    (masses_normalized adversary q hq) hhigh ENNReal.toReal_nonneg hcost hquad
  have hbound := grouped_middle_closingRC ((q:ℝ)/2^128) rate hlow hhigh hrate
  linarith

theorem tiny_clean_closingG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive : 1≤q) (hhigh : (q:ℝ)/2^128≤1/2^28)
    (rate : ℝ) (hrate : rate≤18/5000)
    (hclean : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      (249/125)*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate+(778/1000)*((q:ℝ)/2^128)^2+1/2^136)
    (hpartial : Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(378+1/1024)/(2*2^128)+BPair.pairTerm q) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128) := by
  have hsmall : (q:ℝ)/2^128≤3/2500 := hhigh.trans (by norm_num)
  have hlow : 1/(2:ℝ)^128≤(q:ℝ)/2^128 := div_le_div_of_nonneg_right (by exact_mod_cast hpositive) (by positivity)
  have hquad := paired_partial_denominatorRC _ _ hsmall (partial_probability_real adversary q hq hpartial)
  have hcost := completed_partial_normalized adversary q hq
  change (1-(q:ℝ)/2^128)*_≤(otherMass adversary q).toReal/2^128 at hcost
  rw [mul_comm] at hcost
  have hbudget := tiny_class_budgetRC _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    (masses_normalized adversary q hq) hhigh ENNReal.toReal_nonneg hcost hquad
  have hbound := tiny_closing_rows18 ((q:ℝ)/2^128) rate hlow hhigh hrate
  nlinarith [sq_nonneg ((q:ℝ)/2^128)]

theorem clean_outer_ennrealG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (h : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128)) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  have hevent : Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]≠⊤ :=
    ne_top_of_le_ne_top (by simp) probEvent_le_one
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_div,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast,Nat.cast_pow,Nat.cast_ofNat]
  convert h using 1 <;> norm_num <;> ring




end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_partial_certifiedG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(378+1/1024)/(2*2^128)+BPair.pairTerm q := by
  apply completed_partial_bound ClaudeWCT.Bank.Paired.nearLawSpec
    ClaudeWCT.Bank.Paired.nearLawSpec_producer rfl ClaudeWCT.Bank.Paired.nearCovered_mono
    (fun X N h => by
      obtain ⟨k,t,h⟩:=h
      exact WPair.Paired.nearCovered_bank X N k t h)
    378 ClaudeWCT.Bank.Paired.nearLawSpec_mean adversary q hq

theorem excess_middle_actualG :
    ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-((99847:ENNReal)/50000-1/1024))≤1153/1000000 := by
  have h:=ClaudeWCT.Bank.Paired.excess_middle_certified
  simpa (disch:=positivity) only [ENNReal.ofReal_sub,ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using h

theorem excess_tiny_actualG :
    ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-((249:ENNReal)/125-1/1024))≤18/5000 := by
  have h:=ClaudeWCT.Bank.Paired.excess_tiny_certified
  simpa (disch:=positivity) only [ENNReal.ofReal_sub,ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using h

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Secc.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3M.Final.Paired
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Secc.Paired
