import SigGolfCandidate.T3.Gate6.SourceBudget

namespace ClaudeWCT.W9.T3.BaseAudit.V5
open SigGolfCandidate.T3.BaseAudit (zU)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
def J : ℕ := 51560838624306633002850832035711699557452288
/-- Density-aware digest acceptance: gate 1353/2^14, fields 563/1024 (rank = field), cap fraction J(783) / 72064^9:
`1353 * 563^9 * J / (2^104 * 72064^9) = 1353 * J / 2^167`. -/
def p0 : ℚ := 1353 * J / 2 ^ 167
def b0 : ℚ := 1014384999801306513 / 1000000000000000000
theorem step_0 : zU * ((1 - p0) * b0 + p0) ≤ b0 := by norm_num [zU, p0, b0, J]
theorem probability_floor : 1 / 5026 ≤ p0 ∧ p0 ≤ 1 / 2471 := by norm_num [p0, J]
theorem p0_ge_5026 : 1 / 5026 ≤ p0 := by norm_num [p0, J]
theorem p0_nonneg : 0 ≤ p0 := by norm_num [p0, J]
theorem p0_le_one : p0 ≤ 1 := by norm_num [p0, J]
/-- Campaign T8D (NF17, 51 r5 + 3 r8): accepted top encodings at target 144 with credit floor 8 (about 1/2907). -/
def topCount144 : ℕ := 113151284379417370579638218549543970
def lowerCount197 : ℕ := 140610462347261096978771217394878840
def lowerCount198 : ℕ := 113470737483767875195512089978341656
def lowerCount199 : ℕ := 87860897096037675585104420890976996
def lowerCount200 : ℕ := 72766719968968561634032082840784641
/-- B4 accepted lower199/f5/z5 encodings, including checksum. -/
def lowerCount199f5 : ℕ := 87421058181341847220388848563308770
/-- B4 accepted lower199/f4/z5 encodings, including checksum. -/
def lowerCount199f4 : ℕ := 90649243438620156062228389214105950
/-- B4 accepted lower200/f4/z5 encodings, including checksum. -/
def lowerCount200f4 : ℕ := 72459682149134130685732695915636483
def p1 : ℚ := topCount144 / 2 ^ 128
def b1 : ℚ := 1016160613718328085 / 1000000000000000000
theorem step_1 : zU * ((1 - p1) * b1 + p1) ≤ b1 := by norm_num [zU, p1, b1, topCount144]
def p2 : ℚ := lowerCount199f5 / 2 ^ 128
def b2 : ℚ := 1021017057799314038 / 1000000000000000000
theorem step_2 : zU * ((1 - p2) * b2 + p2) ≤ b2 := by norm_num [zU, p2, b2, lowerCount199f5]
def p3 : ℚ := lowerCount199f5 / 2 ^ 128
def b3 : ℚ := 1021017057799314038 / 1000000000000000000
theorem step_3 : zU * ((1 - p3) * b3 + p3) ≤ b3 := by norm_num [zU, p3, b3, lowerCount199f5]
def p4 : ℚ := lowerCount200f4 / 2 ^ 128
def b4 : ℚ := 1025467147693740505 / 1000000000000000000
theorem step_4 : zU * ((1 - p4) * b4 + p4) ≤ b4 := by norm_num [zU, p4, b4, lowerCount200f4]
theorem zU_nonneg : (0 : ℚ) ≤ zU := by norm_num [zU]
theorem step_mono {p q b : ℚ} (hb : 1 ≤ b) (hpq : p ≤ q) (h : zU * ((1 - p) * b + p) ≤ b) :
    zU * ((1 - q) * b + q) ≤ b := by
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_left _ zU_nonneg
  nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hb)]
/-- T8 FTS signing compressions (family seeds, 6 chains of 4 steps): `9 * (27 + 128 * (24 + 2) + 126) + 5`. -/
def ftsSign : ℕ := 31334
theorem ftsSign_eq : ftsSign = 9 * (27 + 128 * (24 + 2) + 126) + 5 := by norm_num [ftsSign]
/-- B4 lower layers: eight coefficients packed into four halves per leaf. -/
def layerFixed : ℕ := 81314
theorem layerFixed_eq : layerFixed + 4611 = 85925 := by norm_num [layerFixed]
def fixedSign : ℕ := 112652
theorem fixedSign_eq : fixedSign = 2 + 2 + ftsSign + layerFixed := by norm_num [fixedSign, ftsSign, layerFixed]
theorem rpow_two_ge_cubic (y : ℝ) (hy : 0 ≤ y) :
    1 + 0.6931471803 * y + (0.6931471803 * y) ^ 2 / 2 + (0.6931471803 * y) ^ 3 / 6 ≤ (2 : ℝ) ^ y := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hl := Real.log_two_gt_d9
  have ht0 : 0 ≤ 0.6931471803 * y := by positivity
  have hts : 0.6931471803 * y ≤ Real.log 2 * y := mul_le_mul_of_nonneg_right hl.le hy
  have h := Real.sum_le_exp_of_nonneg (ht0.trans hts) 4
  have e : ∑ i ∈ Finset.range 4, (Real.log 2 * y) ^ i / (i.factorial : ℝ) =
      1 + Real.log 2 * y + (Real.log 2 * y) ^ 2 / 2 + (Real.log 2 * y) ^ 3 / 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [show (0 : ℕ).factorial = 1 from rfl, show (1 : ℕ).factorial = 1 from rfl,
      show (2 : ℕ).factorial = 2 from rfl, show (3 : ℕ).factorial = 6 from rfl]
    push_cast
    ring
  rw [e] at h
  have h2 : (0.6931471803 * y) ^ 2 ≤ (Real.log 2 * y) ^ 2 := pow_le_pow_left₀ ht0 hts 2
  have h3 : (0.6931471803 * y) ^ 3 ≤ (Real.log 2 * y) ^ 3 := pow_le_pow_left₀ ht0 hts 3
  linarith
theorem signing_envelope_le :
    (2 : ℝ) ^ ((112652 : ℝ) / 131072) * ((b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤
      2 := by
  have hsplit : (2 : ℝ) ^ ((112652 : ℝ) / 131072) = 2 / (2 : ℝ) ^ ((18420 : ℝ) / 131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  have hlo := rpow_two_ge_cubic (18420 / 131072) (by norm_num)
  have hn : 2 * ((b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤
      2 * (1 + 0.6931471803 * (18420 / 131072) + (0.6931471803 * (18420 / 131072)) ^ 2 / 2 +
        (0.6931471803 * (18420 / 131072)) ^ 3 / 6) := by
    norm_num [b0, b1, b2, b3, b4]
  rw [hsplit, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  exact hn.trans (mul_le_mul_of_nonneg_left hlo (by norm_num))
theorem signing_envelope :
    (2 : ℝ) ^ ((112652 : ℝ) / 131072) * ((b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤ 2 :=
  signing_envelope_le.trans (by norm_num)
theorem rate_top_1000 : (1000 : ℚ) * 0.6931471808 ≤ 2 ^ 22 * p1 := by norm_num [p1, topCount144]
/-- Lower searches (about 3.9k / 3.7k trials per hit at (target, floor) = (199, 5) / (199, 4)) with fuel 2^21 fail
with probability at most 2^-600 each. -/
theorem rate_lower199f5_600 : (600 : ℚ) * 0.6931471808 ≤ 2 ^ 21 * p3 := by norm_num [p3, lowerCount199f5]
theorem rate_lower199f4_600 : (600 : ℚ) * 0.6931471808 ≤ 2 ^ 21 * p2 := by norm_num [p2, lowerCount199f5]
theorem rate_lower200f4_600 : (600 : ℚ) * 0.6931471808 ≤ 2 ^ 21 * p4 := by norm_num [p4, lowerCount200f4]
/-- Digest search (about 2472 trials per hit) with fuel 2^21: failure at most 2^-900 (2^21 p0 ≈ 848). -/
theorem rate_digest_900 : (900 : ℚ) * 0.6931471808 ≤ 2 ^ 21 * p0 := by norm_num [p0, J]
theorem rates_ge_8192 : 1 / 8192 ≤ p1 ∧ 1 / 8192 ≤ p2 ∧ 1 / 8192 ≤ p3 ∧ 1 / 8192 ≤ p4 := by
  norm_num [p1, p2, p3, p4, topCount144, lowerCount199f5, lowerCount199f5, lowerCount200f4]
theorem completeness_union :
    (2 : ℝ) ^ 256 * (1 / 2 ^ 450) + 2 ^ 301 * (1 / 2 ^ 600) ≤ 1 / 2 ^ 193 := by
  set_option exponentiation.threshold 2048 in norm_num
theorem expandFixed_le : 140 + 466 ≤ 622 := by norm_num
end ClaudeWCT.W9.T3.BaseAudit.V5

/-! Local research only: floor ten cannot reuse the present signing-envelope
certificate unchanged. This rational obstruction concerns this proof route;
it is not an impossibility theorem for the signature scheme. -/
namespace ClaudeWCT.W9.T3.BaseAudit.V5.FloorTenResearch
open SigGolfCandidate.T3.BaseAudit (zU)
set_option maxHeartbeats 1000000

def pTen : ℚ := 106604407169019379465023907866097170 / 2 ^ 128
def minB : ℚ := zU * pTen / (1 - zU * (1 - pTen))
def bLower : ℚ := 1017170123383518813 / 1000000000000000000

theorem denominator_pos : 0 < 1 - zU * (1 - pTen) := by
  norm_num [zU, pTen]

theorem step_requires_minB (b : ℚ)
    (h : zU * ((1 - pTen) * b + pTen) ≤ b) : minB ≤ b := by
  rw [minB, div_le_iff₀ denominator_pos]
  nlinarith

theorem minB_gt_lower : bLower < minB := by
  norm_num [bLower, minB, zU, pTen]

theorem floor_ten_exceeds_current_cubic_certificate :
    1 + 0.6931471803 * (18420 / 131072 : ℚ) +
      (0.6931471803 * (18420 / 131072 : ℚ)) ^ 2 / 2 +
      (0.6931471803 * (18420 / 131072 : ℚ)) ^ 3 / 6 <
      b0 * bLower * b2 * b3 * b4 := by
  norm_num [b0, bLower, b2, b3, b4]

/-- Even the actual real exponential allowance is below a necessary top
geometric factor times the other four unchanged factors. The cubic comparison
above is not being used as an upper bound on the exponential. -/
theorem floor_ten_exceeds_real_allowance :
    (2 : ℝ) ^ (18420 / 131072 : ℝ) <
      (b0 : ℝ) * (bLower : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ) := by
  have hx : 0 ≤ (0.6931471808 * (18420 / 131072 : ℝ)) := by norm_num
  have hx1 : (0.6931471808 * (18420 / 131072 : ℝ)) ≤ 1 := by norm_num
  have hp : (2 : ℝ) ^ (18420 / 131072 : ℝ) ≤
      Real.exp (0.6931471808 * (18420 / 131072 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right Real.log_two_lt_d9.le (by norm_num))
  have he := Real.exp_bound' hx hx1 (n := 4) (by norm_num)
  have hn :
      (∑ m ∈ Finset.range 4,
        (0.6931471808 * (18420 / 131072 : ℝ)) ^ m / m.factorial) +
      (0.6931471808 * (18420 / 131072 : ℝ)) ^ 4 * (4 + 1) / ((Nat.factorial 4 : ℝ) * 4) <
      (b0 : ℝ) * (bLower : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial, b0, bLower, b2, b3, b4]
  exact lt_of_le_of_lt (hp.trans he) hn

/-- No replacement top factor satisfying the same geometric step can close the
present real signing-envelope inequality, while all other factors stay fixed. -/
theorem no_top_factor_for_current_signing_envelope (b : ℚ)
    (hstep : zU * ((1 - pTen) * b + pTen) ≤ b) :
    ¬ (2 : ℝ) ^ (112652 / 131072 : ℝ) *
      ((b0 : ℝ) * (b : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤ 2 := by
  have hb : (bLower : ℝ) < (b : ℝ) := by
    exact_mod_cast lt_of_lt_of_le minB_gt_lower (step_requires_minB b hstep)
  have ht : (2 : ℝ) ^ (18420 / 131072 : ℝ) <
      (b0 : ℝ) * (b : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ) := by
    apply lt_trans floor_ten_exceeds_real_allowance
    have h0 : (0 : ℝ) < (b0 : ℝ) := by norm_num [b0]
    have h2 : (0 : ℝ) < (b2 : ℝ) := by norm_num [b2]
    have h3 : (0 : ℝ) < (b3 : ℝ) := by norm_num [b3]
    have h4 : (0 : ℝ) < (b4 : ℝ) := by norm_num [b4]
    gcongr
  have hs : (2 : ℝ) ^ (112652 / 131072 : ℝ) *
      (2 : ℝ) ^ (18420 / 131072 : ℝ) = 2 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  intro h
  have hp : (0 : ℝ) < (2 : ℝ) ^ (112652 / 131072 : ℝ) := by positivity
  have hm := mul_lt_mul_of_pos_left ht hp
  rw [hs] at hm
  exact (not_lt_of_ge h) hm

#print axioms step_requires_minB
#print axioms floor_ten_exceeds_current_cubic_certificate
#print axioms no_top_factor_for_current_signing_envelope

/-- Saving only 121 fixed compressions is still insufficient for floor ten
through the present geometric-envelope route. -/
theorem floor_ten_needs_more_than_121_fixed_savings :
    (2 : ℝ) ^ (18541 / 131072 : ℝ) <
      (b0 : ℝ) * (bLower : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ) := by
  have hx : 0 ≤ (0.6931471808 * (18541 / 131072 : ℝ)) := by norm_num
  have hx1 : (0.6931471808 * (18541 / 131072 : ℝ)) ≤ 1 := by norm_num
  have hp : (2 : ℝ) ^ (18541 / 131072 : ℝ) ≤
      Real.exp (0.6931471808 * (18541 / 131072 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right Real.log_two_lt_d9.le (by norm_num))
  have he := Real.exp_bound' hx hx1 (n := 6) (by norm_num)
  have hn :
      (∑ m ∈ Finset.range 6,
        (0.6931471808 * (18541 / 131072 : ℝ)) ^ m / m.factorial) +
      (0.6931471808 * (18541 / 131072 : ℝ)) ^ 6 * (6 + 1) /
        ((Nat.factorial 6 : ℝ) * 6) <
      (b0 : ℝ) * (bLower : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial, b0, bLower, b2, b3, b4]
  exact lt_of_le_of_lt (hp.trans he) hn

/-- Any fixed cost at least 112531 is incompatible with the same factors and
the floor-ten step. The present fixed cost is 112652: at least 122 fixed
compressions must be saved before this particular certificate route can work. -/
theorem no_top_factor_above_fixed_threshold (fixed : ℕ) (hfixed : 112531 ≤ fixed)
    (b : ℚ) (hstep : zU * ((1 - pTen) * b + pTen) ≤ b) :
    ¬ (2 : ℝ) ^ ((fixed : ℝ) / 131072) *
      ((b0 : ℝ) * (b : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤ 2 := by
  have hb : (bLower : ℝ) < (b : ℝ) := by
    exact_mod_cast lt_of_lt_of_le minB_gt_lower (step_requires_minB b hstep)
  have ht : (2 : ℝ) ^ (18541 / 131072 : ℝ) <
      (b0 : ℝ) * (b : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ) := by
    apply lt_trans floor_ten_needs_more_than_121_fixed_savings
    have h0 : (0 : ℝ) < (b0 : ℝ) := by norm_num [b0]
    have h2 : (0 : ℝ) < (b2 : ℝ) := by norm_num [b2]
    have h3 : (0 : ℝ) < (b3 : ℝ) := by norm_num [b3]
    have h4 : (0 : ℝ) < (b4 : ℝ) := by norm_num [b4]
    gcongr
  have hs : (2 : ℝ) ^ (112531 / 131072 : ℝ) *
      (2 : ℝ) ^ (18541 / 131072 : ℝ) = 2 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hfr : (112531 : ℝ) ≤ fixed := by exact_mod_cast hfixed
  have hf : (2 : ℝ) ^ (112531 / 131072 : ℝ) ≤
      (2 : ℝ) ^ ((fixed : ℝ) / 131072) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (div_le_div_of_nonneg_right hfr (by norm_num))
  have hbpos : 0 ≤ (b0 : ℝ) * (b : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ) := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ (18541 / 131072 : ℝ) := by positivity
    linarith
  intro h
  have hsmall := (mul_le_mul_of_nonneg_right hf hbpos).trans h
  have hp : (0 : ℝ) < (2 : ℝ) ^ (112531 / 131072 : ℝ) := by positivity
  have hm := mul_lt_mul_of_pos_left ht hp
  rw [hs] at hm
  exact (not_lt_of_ge hsmall) hm

#print axioms no_top_factor_above_fixed_threshold

def bUpper : ℚ := 1017170123383518814 / 1000000000000000000

theorem floor_ten_step_upper : zU * ((1 - pTen) * bUpper + pTen) ≤ bUpper := by
  norm_num [zU, pTen, bUpper]

/-- Conversely, 122 saved fixed compressions suffice for this numerical
envelope, using one more Taylor term than the existing cubic certificate.
This does not establish a machine implementation saving those compressions. -/
theorem floor_ten_envelope_after_122_fixed_savings :
    (2 : ℝ) ^ (112530 / 131072 : ℝ) *
      ((b0 : ℝ) * (bUpper : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤ 2 := by
  have hx : 0 ≤ (0.6931471803 * (18542 / 131072 : ℝ)) := by norm_num
  have hp : Real.exp (0.6931471803 * (18542 / 131072 : ℝ)) ≤
      (2 : ℝ) ^ (18542 / 131072 : ℝ) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right Real.log_two_gt_d9.le (by norm_num))
  have he := Real.sum_le_exp_of_nonneg hx 5
  have hn : (b0 : ℝ) * (bUpper : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ) ≤
      ∑ m ∈ Finset.range 5,
        (0.6931471803 * (18542 / 131072 : ℝ)) ^ m / m.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial, b0, bUpper, b2, b3, b4]
  have hb := hn.trans (he.trans hp)
  have hs : (2 : ℝ) ^ (112530 / 131072 : ℝ) *
      (2 : ℝ) ^ (18542 / 131072 : ℝ) = 2 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hb
    (show (0 : ℝ) ≤ (2 : ℝ) ^ (112530 / 131072 : ℝ) by positivity)
  rwa [hs] at hm

#print axioms floor_ten_envelope_after_122_fixed_savings
end ClaudeWCT.W9.T3.BaseAudit.V5.FloorTenResearch

/-! Consequences of the adjacent-pair private-hash savings; conditional
numerical bounds only, not a changed producer or compression certificate. -/
namespace ClaudeWCT.W9.T3.BaseAudit.V5.FloorTenResearch

theorem floor_ten_envelope_after_128_fixed_savings :
    (2 : ℝ) ^ (112524 / 131072 : ℝ) *
      ((b0 : ℝ) * (bUpper : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤ 2 := by
  have hb := floor_ten_envelope_after_122_fixed_savings
  have he : (2 : ℝ) ^ (112524 / 131072 : ℝ) ≤ (2 : ℝ) ^ (112530 / 131072 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  exact (mul_le_mul_of_nonneg_right he (by norm_num [b0, bUpper, b2, b3, b4])).trans hb

theorem floor_ten_envelope_after_192_fixed_savings :
    (2 : ℝ) ^ (112460 / 131072 : ℝ) *
      ((b0 : ℝ) * (bUpper : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤ 2 := by
  have hb := floor_ten_envelope_after_122_fixed_savings
  have he : (2 : ℝ) ^ (112460 / 131072 : ℝ) ≤ (2 : ℝ) ^ (112530 / 131072 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  exact (mul_le_mul_of_nonneg_right he (by norm_num [b0, bUpper, b2, b3, b4])).trans hb

#print axioms floor_ten_envelope_after_128_fixed_savings
#print axioms floor_ten_envelope_after_192_fixed_savings
end ClaudeWCT.W9.T3.BaseAudit.V5.FloorTenResearch
