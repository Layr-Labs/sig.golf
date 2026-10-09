import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Scalar closing packet (campaign X1 stage A: small absolute 2^-136, large reserve absolute 2^-131, both
covering the FTS overflow mass 2^-137). -/
namespace SigGolfCandidate.Research.V7Composed198Closing
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

theorem small_closing_real (y : ℝ) (hlow : 1 / 2 ^ 128 ≤ y) (hhigh : y ≤ 705 / 1048576) :
    1906 / 1000 * y + (136) * y ^ 2 + 5 / 2 ^ 139 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have h139 : (5 : ℝ) / 2 ^ 139 ≤ 5 * y / 2 ^ 11 := by
    have : (5 : ℝ) / 2 ^ 139 = 5 * (1 / 2 ^ 128) / 2 ^ 11 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlow (by positivity)) (by positivity)
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 572 := by
    have : (1 : ℝ) / 2 ^ 700 = (1 / 2 ^ 128) / 2 ^ 572 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 24 := by
    have : (1 : ℝ) / 2 ^ 152 = (1 / 2 ^ 128) / 2 ^ 24 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have hsq : (136 : ℝ) * y ^ 2 ≤ (136) * (705 / 1048576) * y := by
    nlinarith [mul_le_mul_of_nonneg_left hhigh hn]
  linarith
theorem large_closing_real (y : ℝ) (hlow : 705 / 1048576 ≤ y) :
    (2 * y - y ^ 2) + y * (6678 / 10000000) + y * (1 / 2 ^ 25) + y * (1 / 2 ^ 50) + 1 / 2 ^ 131 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by norm_num) hlow
  have hsq : y * (705 / 1048576) ≤ y ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hlow hn]
  have habs : (1 : ℝ) / 2 ^ 131 ≤ y / 2 ^ 109 := by
    have h := div_le_div_of_nonneg_right hlow (show (0:ℝ) ≤ 2 ^ 109 by positivity)
    norm_num at h ⊢
    linarith
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 678 := by
    have h := div_le_div_of_nonneg_right hlow (show (0:ℝ) ≤ 2 ^ 678 by positivity)
    norm_num at h ⊢
    linarith
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 130 := by
    have h := div_le_div_of_nonneg_right hlow (show (0:ℝ) ≤ 2 ^ 130 by positivity)
    norm_num at h ⊢
    linarith
  nlinarith
theorem large_closing_real_high (y : ℝ) (hlow : 1 / 128 ≤ y) :
    (2 * y - y ^ 2) + y * (2435 / 1000000) + y * (1 / 2 ^ 25) + y * (1 / 2 ^ 50) + 1 / 2 ^ 131 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by norm_num) hlow
  have hsq : y * (1 / 128) ≤ y ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hlow hn]
  have habs : (1 : ℝ) / 2 ^ 131 ≤ y / 2 ^ 109 := by
    have h := div_le_div_of_nonneg_right hlow (show (0:ℝ) ≤ 2 ^ 109 by positivity)
    norm_num at h ⊢
    linarith
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 678 := by
    have h := div_le_div_of_nonneg_right hlow (show (0:ℝ) ≤ 2 ^ 678 by positivity)
    norm_num at h ⊢
    linarith
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 130 := by
    have h := div_le_div_of_nonneg_right hlow (show (0:ℝ) ≤ 2 ^ 130 by positivity)
    norm_num at h ⊢
    linarith
  nlinarith
end SigGolfCandidate.Research.V7Composed198Closing

#print axioms SigGolfCandidate.Research.V7Composed198Closing.small_closing_real
#print axioms SigGolfCandidate.Research.V7Composed198Closing.large_closing_real
#print axioms SigGolfCandidate.Research.V7Composed198Closing.large_closing_real_high
