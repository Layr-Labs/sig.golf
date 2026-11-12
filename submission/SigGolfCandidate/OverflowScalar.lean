import SigGolfCandidate.Merge020
import SigGolfCandidate.Merge021
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace QueryChargeResearch.OverflowClosing
/-- The query-dependent overflow fee fits the tiny route once the query budget is at least256. -/
theorem tiny_above256 (y rate overflow : ℝ)
    (hlo : 256 / 2^128 ≤ y) (hhi : y ≤ 1 / 2^28)
    (hr : rate ≤ 18/5000) (he : overflow ≤ y/256) :
    (249/125)*y + y*rate + 3*y^2 + (1/2^139+1/2^142+1/2^138) + overflow +
      (y/2^18 + 1/2^700 + 1/2^152 + y/2^128) ≤ 2*y := by
  have hy0 : 0 ≤ y := le_trans (by positivity) hlo
  have hrate := mul_le_mul_of_nonneg_left hr hy0
  have hsq : y^2 ≤ y/2^28 := by nlinarith [mul_le_mul_of_nonneg_left hhi hy0]
  have habs : (1:ℝ)/2^139+1/2^142+1/2^138 ≤ y/2^17 := by
    have hh := div_le_div_of_nonneg_right hlo (show (0:ℝ) ≤ 2^17 by positivity)
    norm_num at hh ⊢
    linarith
  have h700 : (1:ℝ)/2^700 ≤ y/2^572 := by
    have hh := div_le_div_of_nonneg_right hlo (show (0:ℝ) ≤ 2^572 by positivity)
    norm_num at hh ⊢
    linarith
  have h152 : (1:ℝ)/2^152 ≤ y/2^24 := by
    have hh := div_le_div_of_nonneg_right hlo (show (0:ℝ) ≤ 2^24 by positivity)
    norm_num at hh ⊢
    linarith
  nlinarith

theorem middle_absolute88 (y excess : ℝ) (hlow : 1 / 2 ^ 28 ≤ y)
    (hhigh : y ≤ 2163 / 1000000) (hexcess : excess ≤ 2143 / 1000000) :
    (397071 / 200000) * y + y * excess + (57079 / 10000) * y ^ 2 + 1 / 2 ^ 87 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have he := mul_le_mul_of_nonneg_left hexcess hn
  have hsq : y ^ 2 ≤ (2163 / 1000000) * y := by
    nlinarith [mul_le_mul_of_nonneg_left hhigh hn]
  have habs : (1 : ℝ) / 2 ^ 87 ≤ y / 2 ^ 59 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 59 by positivity)
    norm_num at h ⊢
    linarith
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 672 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 672 by positivity)
    norm_num at h ⊢
    linarith
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 124 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 124 by positivity)
    norm_num at h ⊢
    linarith
  nlinarith

theorem large_absolute88 (y excess : ℝ) (hlow : 2163 / 1000000 ≤ y)
    (hexcess : excess ≤ (99076 / 100000) * y) :
    (2 * y - y ^ 2) + y * excess + y * (1 / 2 ^ 25) +
      y * (1 / 2 ^ 50) + 1 / 2 ^ 87 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by norm_num) hlow
  have he := mul_le_mul_of_nonneg_left hexcess hn
  have hsq : y * (2163 / 1000000) ≤ y ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlow hn]
  have habs : (1 : ℝ) / 2 ^ 87 ≤ y / 2 ^ 77 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 77 by positivity)
    norm_num at h ⊢
    linarith
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 690 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 690 by positivity)
    norm_num at h ⊢
    linarith
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 142 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 142 by positivity)
    norm_num at h ⊢
    linarith
  nlinarith

#print axioms middle_absolute88
#print axioms large_absolute88
#print axioms tiny_above256
end QueryChargeResearch.OverflowClosing
