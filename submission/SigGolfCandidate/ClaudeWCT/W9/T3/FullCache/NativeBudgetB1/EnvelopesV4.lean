import SigGolfCandidate.T3.Gate6.SourceBudget

namespace ClaudeWCT.W9.T3.BaseAudit.V4
open SigGolfCandidate.T3.BaseAudit (zU)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
def J : ℕ := 10063883596882232320104833
def p0 : ℚ := 2047 * 27 ^ 9 * J / 2 ^ 148
def b0 : ℚ := 506078769657 / 500000000000
theorem step_0 : zU * ((1 - p0) * b0 + p0) ≤ b0 := by norm_num [zU, p0, b0, J]
theorem probability_floor : 1 / 2272 ≤ p0 ∧ p0 ≤ 1 / 2271 := by norm_num [p0, J]
theorem p0_ge_5026 : 1 / 5026 ≤ p0 := by norm_num [p0, J]
theorem p0_nonneg : 0 ≤ p0 := by norm_num [p0, J]
theorem p0_le_one : p0 ≤ 1 := by norm_num [p0, J]
def topCount128 : ℕ := 115848238762295281832019488595518415
def lowerCount198 : ℕ := 115663871454869880991236461657470944
def lowerCount197 : ℕ := 143468572474466315422327516384120300
def p1 : ℚ := topCount128 / 2 ^ 128
def b1 : ℚ := 253944614357 / 250000000000
theorem step_1 : zU * ((1 - p1) * b1 + p1) ≤ b1 := by norm_num [zU, p1, b1, topCount128]
def p2 : ℚ := lowerCount198 / 2 ^ 128
def b2 : ℚ := 1015804005649 / 1000000000000
theorem step_2 : zU * ((1 - p2) * b2 + p2) ≤ b2 := by norm_num [zU, p2, b2, lowerCount198]
def p3 : ℚ := lowerCount198 / 2 ^ 128
def b3 : ℚ := 1015804005649 / 1000000000000
theorem step_3 : zU * ((1 - p3) * b3 + p3) ≤ b3 := by norm_num [zU, p3, b3, lowerCount198]
def p4 : ℚ := lowerCount197 / 2 ^ 128
def b4 : ℚ := 253175557477 / 250000000000
theorem step_4 : zU * ((1 - p4) * b4 + p4) ≤ b4 := by norm_num [zU, p4, b4, lowerCount197]
def ftsSign : ℕ := 31667
theorem ftsSign_eq : ftsSign + 576 = 32243 := by norm_num [ftsSign]
def layerFixed : ℕ := 85796
theorem layerFixed_eq : layerFixed + 128 = 85924 := by norm_num [layerFixed]
def fixedSign : ℕ := 117467
theorem fixedSign_eq : fixedSign = 2 + 2 + ftsSign + layerFixed := by norm_num [fixedSign, ftsSign, layerFixed]
theorem signing_envelope_le :
    (2 : ℝ) ^ ((117467 : ℝ) / 131072) * ((b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤
      19997 / 10000 := by
  have hsplit : (2 : ℝ) ^ ((117467 : ℝ) / 131072) = 2 / (2 : ℝ) ^ ((13605 : ℝ) / 131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  have hlo := SigGolfCandidate.Budget.rpow_two_ge (13605 / 131072) (by norm_num)
  have hn : 2 * ((b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤
      19997 / 10000 * (1 + 0.6931471803 * (13605 / 131072) + (0.6931471803 * (13605 / 131072)) ^ 2 / 2) := by
    norm_num [b0, b1, b2, b3, b4]
  rw [hsplit, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  exact hn.trans (mul_le_mul_of_nonneg_left hlo (by norm_num))
theorem signing_envelope :
    (2 : ℝ) ^ ((117467 : ℝ) / 131072) * ((b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤ 2 :=
  signing_envelope_le.trans (by norm_num)
theorem completeness_union :
    (2 : ℝ) ^ 256 * (1 / 2 ^ 450) + 2 ^ 301 * (1 / 2 ^ 1024) ≤ 1 / 2 ^ 193 := by
  set_option exponentiation.threshold 2048 in norm_num
theorem expandFixed_le : 131 + 473 ≤ 622 := by norm_num
end ClaudeWCT.W9.T3.BaseAudit.V4
