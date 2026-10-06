import SigGolfCandidate.T3.Gate6.SourceBudget

namespace ClaudeWCT.W9.T3.BaseAudit.V5
open SigGolfCandidate.T3.BaseAudit (zU)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
def J : ℕ := 91047568710745042769519422244938706921193472
def p0 : ℚ := 1091 * 27 ^ 9 * J / 2 ^ 210
def b0 : ℚ := 15806857617 / 15625000000
theorem step_0 : zU * ((1 - p0) * b0 + p0) ≤ b0 := by norm_num [zU, p0, b0, J]
theorem probability_floor : 1 / 2173 ≤ p0 ∧ p0 ≤ 1 / 2172 := by norm_num [p0, J]
theorem p0_ge_5026 : 1 / 5026 ≤ p0 := by norm_num [p0, J]
theorem p0_nonneg : 0 ≤ p0 := by norm_num [p0, J]
theorem p0_le_one : p0 ≤ 1 := by norm_num [p0, J]
def topCount129 : ℕ := 97816978632729252580178283386927154
def lowerCount197 : ℕ := 140610462347261096978771217394878840
def lowerCount198 : ℕ := 113470737483767875195512089978341656
def p1 : ℚ := topCount129 / 2 ^ 128
def b1 : ℚ := 254685379249 / 250000000000
theorem step_1 : zU * ((1 - p1) * b1 + p1) ≤ b1 := by norm_num [zU, p1, b1, topCount129]
def p2 : ℚ := lowerCount197 / 2 ^ 128
def b2 : ℚ := 126620471019 / 125000000000
theorem step_2 : zU * ((1 - p2) * b2 + p2) ≤ b2 := by norm_num [zU, p2, b2, lowerCount197]
def p3 : ℚ := lowerCount197 / 2 ^ 128
def b3 : ℚ := 126620471019 / 125000000000
theorem step_3 : zU * ((1 - p3) * b3 + p3) ≤ b3 := by norm_num [zU, p3, b3, lowerCount197]
def p4 : ℚ := lowerCount198 / 2 ^ 128
def b4 : ℚ := 1016114383741 / 1000000000000
theorem step_4 : zU * ((1 - p4) * b4 + p4) ≤ b4 := by norm_num [zU, p4, b4, lowerCount198]
theorem zU_nonneg : (0 : ℚ) ≤ zU := by norm_num [zU]
theorem step_mono {p q b : ℚ} (hb : 1 ≤ b) (hpq : p ≤ q) (h : zU * ((1 - p) * b + p) ≤ b) :
    zU * ((1 - q) * b + q) ≤ b := by
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_left _ zU_nonneg
  nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hb)]
def ftsSign : ℕ := 31667
theorem ftsSign_eq : ftsSign + 576 = 32243 := by norm_num [ftsSign]
def layerFixed : ℕ := 85797
theorem layerFixed_eq : layerFixed + 128 = 85925 := by norm_num [layerFixed]
def fixedSign : ℕ := 117468
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
    (2 : ℝ) ^ ((117468 : ℝ) / 131072) * ((b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤
      19999 / 10000 := by
  have hsplit : (2 : ℝ) ^ ((117468 : ℝ) / 131072) = 2 / (2 : ℝ) ^ ((13604 : ℝ) / 131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  have hlo := rpow_two_ge_cubic (13604 / 131072) (by norm_num)
  have hn : 2 * ((b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤
      19999 / 10000 * (1 + 0.6931471803 * (13604 / 131072) + (0.6931471803 * (13604 / 131072)) ^ 2 / 2 +
        (0.6931471803 * (13604 / 131072)) ^ 3 / 6) := by
    norm_num [b0, b1, b2, b3, b4]
  rw [hsplit, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  exact hn.trans (mul_le_mul_of_nonneg_left hlo (by norm_num))
theorem signing_envelope :
    (2 : ℝ) ^ ((117468 : ℝ) / 131072) * ((b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤ 2 :=
  signing_envelope_le.trans (by norm_num)
theorem rate_top_1000 : (1000 : ℚ) * 0.6931471808 ≤ 2 ^ 22 * p1 := by norm_num [p1, topCount129]
theorem rate_lower197_1000 : (1000 : ℚ) * 0.6931471808 ≤ 2 ^ 21 * p2 := by norm_num [p2, lowerCount197]
theorem rate_lower198_1000 : (1000 : ℚ) * 0.6931471808 ≤ 2 ^ 21 * p4 := by norm_num [p4, lowerCount198]
theorem rate_digest_1300 : (1300 : ℚ) * 0.6931471808 ≤ 2 ^ 21 * p0 := by norm_num [p0, J]
theorem rates_ge_4096 : 1 / 4096 ≤ p1 ∧ 1 / 4096 ≤ p2 ∧ 1 / 4096 ≤ p4 := by
  norm_num [p1, p2, p4, topCount129, lowerCount197, lowerCount198]
theorem completeness_union :
    (2 : ℝ) ^ 256 * (1 / 2 ^ 450) + 2 ^ 301 * (1 / 2 ^ 1000) ≤ 1 / 2 ^ 193 := by
  set_option exponentiation.threshold 2048 in norm_num
theorem expandFixed_le : 131 + 473 ≤ 622 := by norm_num
end ClaudeWCT.W9.T3.BaseAudit.V5
