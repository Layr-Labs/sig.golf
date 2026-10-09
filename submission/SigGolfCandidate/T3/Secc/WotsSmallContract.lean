import SigGolfCandidate.T3.Secc.WotsTransportSplit
import SigGolfCandidate.T3.Secc.PairGuessWorld

section
namespace SigGolfResearch.Gate3Closing115
open ENNReal SigGolfResearch.Gate6.Moments.Numeric
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
theorem mean_bound :
    (2:ENNReal)^128*poissonEnvelope meanCoeffs (proposalLength/2^31)/2^234≤37/64 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [meanCoeffs,proposalLength,Finset.sum_range_succ]
theorem variance_excess : (18400/100000000:ℚ)*(8/13)≤15200/100000000 := by norm_num
theorem reuse_bound : SigGolfResearch.Gate6.Budget.p0≤(1/64:ℚ) := by
  norm_num [SigGolfResearch.Gate6.Budget.p0]
theorem prefix_rate :
    ((3/2:ℚ)+4*329/2097152+2*(329/2097152)^2)*(2097152/2096823)+4*329/2097152*(2097152/2096823)^2+
      2*57*329/2097152*(2097152/2096823)≤1900/1000 := by norm_num
theorem encoding_rate : (1:ℚ)+2*2865*329/2097152*(2097152/2096823)≤1900/1000 := by norm_num
theorem small_excess_rate : (201:ℚ)*(15200/100000000)≤31/1000 := by norm_num
theorem near_rate : (2097152/2096823:ℚ)*(404+21*201/2^25)≤405 := by norm_num
theorem small_first_rate : (1900/1000:ℚ)+31/1000+1/1000≤1932/1000 := by norm_num
theorem pointwise_excess (v m : ℝ) (hm : m≤37/64) :
    (13/8)*max 0 (v-63/64)+2*m*v≤v^2+m^2 := by
  rcases le_total v (63/64) with hv|hv
  · rw [max_eq_left (sub_nonpos.mpr hv)];nlinarith [sq_nonneg (v-m)]
  · rw [max_eq_right (sub_nonneg.mpr hv)]
    nlinarith [sq_nonneg (v-m-13/16)]
theorem small_closing_real (y : ℝ) (hlow : 1 / 2 ^ 128 ≤ y) (hhigh : y ≤ 329 / 2097152) :
    1932 / 1000 * y + 407 * y ^ 2 + 1 / 2 ^ 132 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 572 := by
    have : (1 : ℝ) / 2 ^ 700 = (1 / 2 ^ 128) / 2 ^ 572 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 24 := by
    have : (1 : ℝ) / 2 ^ 152 = (1 / 2 ^ 128) / 2 ^ 24 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have hy18 : y / 2 ^ 18 ≤ y / 65536 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  have hy572 : y / 2 ^ 572 ≤ y / 65536 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  have hy24 : y / 2 ^ 24 ≤ y / 65536 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  have hy128 : y / 2 ^ 128 ≤ y / 65536 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  by_cases hs : y ≤ 1 / 2 ^ 20
  · have hsq : 407 * y ^ 2 ≤ y / 2048 := by
      nlinarith [mul_le_mul_of_nonneg_left hs hn]
    have habs : (1 : ℝ) / 2 ^ 132 ≤ y / 16 := by
      have : (1 : ℝ) / 2 ^ 132 = (1 / 2 ^ 128) / 16 := by ring
      rw [this]
      exact div_le_div_of_nonneg_right hlow (by norm_num)
    linarith
  · have hsq : 407 * y ^ 2 ≤ 133903 / 2097152 * y := by
      nlinarith [mul_le_mul_of_nonneg_left hhigh hn]
    have habs : (1 : ℝ) / 2 ^ 132 ≤ y / 65536 := by
      have : (1 : ℝ) / 2 ^ 132 ≤ (1 / 2 ^ 20) / 65536 := by norm_num
      exact this.trans (div_le_div_of_nonneg_right (le_of_lt (lt_of_not_ge hs)) (by norm_num))
    linarith
theorem large_closing_real (y : ℝ) (hlow : 329 / 2097152 ≤ y) :
    (2 * y - y ^ 2) + y * (15200 / 100000000) + y * (1 / 2 ^ 25) + y * (1 / 2 ^ 20) + 1 / 2 ^ 132 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have hsq : y * (329 / 2097152) ≤ y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlow hn
    nlinarith
  have hl : (1 : ℝ) / 2 ^ 16 ≤ y := by
    norm_num at hlow ⊢
    linarith
  have habs : (1 : ℝ) / 2 ^ 132 ≤ y / 2 ^ 100 := by
    calc (1 : ℝ) / 2 ^ 132 = (1 / 2 ^ 16) / 2 ^ 116 := by norm_num
      _ ≤ y / 2 ^ 116 := div_le_div_of_nonneg_right hl (by positivity)
      _ ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 100 := by
    calc (1 : ℝ) / 2 ^ 700 = (1 / 2 ^ 16) / 2 ^ 684 := by norm_num
      _ ≤ y / 2 ^ 684 := div_le_div_of_nonneg_right hl (by positivity)
      _ ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 100 := by
    calc (1 : ℝ) / 2 ^ 152 = (1 / 2 ^ 16) / 2 ^ 136 := by norm_num
      _ ≤ y / 2 ^ 136 := div_le_div_of_nonneg_right hl (by positivity)
      _ ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  have hy128 : y / 2 ^ 128 ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  norm_num at hsq habs h700 h152 hy128 ⊢
  nlinarith
end SigGolfResearch.Gate3Closing115
#print axioms SigGolfResearch.Gate3Closing115.mean_bound
#print axioms SigGolfResearch.Gate3Closing115.variance_excess
#print axioms SigGolfResearch.Gate3Closing115.reuse_bound
#print axioms SigGolfResearch.Gate3Closing115.prefix_rate
#print axioms SigGolfResearch.Gate3Closing115.encoding_rate
#print axioms SigGolfResearch.Gate3Closing115.small_excess_rate
#print axioms SigGolfResearch.Gate3Closing115.near_rate
#print axioms SigGolfResearch.Gate3Closing115.small_first_rate
#print axioms SigGolfResearch.Gate3Closing115.pointwise_excess
#print axioms SigGolfResearch.Gate3Closing115.small_closing_real
#print axioms SigGolfResearch.Gate3Closing115.large_closing_real
end
section
namespace SigGolfCandidate.T3.Security.SeccClosing
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option exponentiation.threshold 1024
noncomputable irreducible_def excessRate : ENNReal := 15200 / 100000000
noncomputable irreducible_def cacheRate : ENNReal := ((2 : ENNReal) ^ 25)⁻¹
noncomputable irreducible_def largeReserveRate : ENNReal := ((2 : ENNReal) ^ 20)⁻¹
noncomputable irreducible_def largeReserveAbsolute : ENNReal := ((2 : ENNReal) ^ 132)⁻¹
noncomputable def largeBound (q : Nat) : ENNReal :=
  ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) + (q : ENNReal) * excessRate / 2 ^ 128 +
    (q : ENNReal) * cacheRate / 2 ^ 128 + (q : ENNReal) * largeReserveRate / 2 ^ 128 + largeReserveAbsolute
theorem probEvent_le_contact_add {β : Type} (law : PMF β) (win contact : β → Prop) (count : β → Prop)
    (hcount : ∀ value, win value → count value) :
    Pr[win | law] ≤ Pr[fun value => count value ∧ contact value | law] +
      Pr[fun value => win value ∧ ¬contact value | law] := by
  classical
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases hw : win value
  · have hc := hcount value hw
    by_cases hk : contact value
    · simp [hw, hc, hk]
    · simp [hw, hc, hk]
  · simp only [hw, if_false, zero_le]
end SigGolfCandidate.T3.Security.SeccClosing
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
def IsDigestQuery (input : T3.Spec.Domain) : Prop :=
  ∃ (rho : Digest) (message : Message) (counter : BitVec 32),
    input = .inl (.inr (pad64 (digestInput rho message counter)))
def digestClass : SeccLaw.SampleClass := fun _ input => IsDigestQuery input
def signRatio : Nat := 201
end SigGolfCandidate.T3.Security.Wots
end
