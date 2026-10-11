import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Scalar closing packet (campaign X1 stage A: small absolute 2^-136, large reserve absolute 2^-131, both
covering the FTS overflow mass 2^-137; campaign T8E: split y0 = 2718 / 2^22, small 19017/10000 y + 75701/500 y^2,
excess 6441e-7 (theta 1919/1024) and 451/200000 (theta 1023/1024)). -/
namespace SigGolfCandidate.Research.V7Composed198Closing
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

theorem small_closing_real (y : ℝ) (hlow : 1 / 2 ^ 128 ≤ y) (hhigh : y ≤ 2718 / 4194304) :
    190185 / 100000 * y + (75701 / 500) * y ^ 2 + 1 / 2 ^ 136 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  -- T8E: the quadratic is charged on the whole window [2^-128, y0] through (y - 2^-128) (y0 - y) ≥ 0 (convexity of
  -- the closing in y); the T8D shortcut 2^-136 ≤ y / 2^8 costs 2^-8 and no longer fits the 1.8e-4 slack at y0.
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have hP := mul_nonneg (sub_nonneg.2 hlow) (sub_nonneg.2 hhigh)
  nlinarith [hP, hn]
theorem large_closing_real (y : ℝ) (hlow : 2718 / 4194304 ≤ y) :
    (2 * y - y ^ 2) + y * (6117 / 10000000) + y * (1 / 2 ^ 25) + y * (1 / 2 ^ 50) + 1 / 2 ^ 131 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by norm_num) hlow
  have hsq : y * (2718 / 4194304) ≤ y ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hlow hn]
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
    (2 * y - y ^ 2) + y * (247 / 100000) + y * (1 / 2 ^ 25) + y * (1 / 2 ^ 50) + 1 / 2 ^ 131 +
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

/-!
# Paired lower-family scalar repair

The old conservative seed-error summand is 0.702 y². Charging 86 rather
than 54 chains per family test and retaining errCoeff ≤ 2 changes it to
1.114 y², for the slightly smaller split 2710/2^22. All other terms below
are unchanged. This is a conditional numerical repair, not an installed
EUF-CMA reduction for shared source families.
-/
namespace SigGolfCandidate.Research.V7Composed198Closing.AdjacentLeafResearch
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

/-- Quadratic 150.1 + 0.6 + 2*0.557 = 151.814. -/
theorem regrouped_quadratic : (1501/10 : ℚ)+6/10+2*(557/1000) = 75907/500 := by norm_num

/-- Blindly keeping the current split fails with the conservative paired
error allowance. It is a failure of this scalar certificate only. -/
theorem old_split_fails_regrouped_closing :
    let y : ℚ := 2718/4194304
    2*y < 190185/100000*y+(75907/500)*y^2+1/2^136+
      (y/2^18+1/2^700+1/2^152+y/2^128) := by norm_num

/-- Updated small route with regrouped seed-error charge. -/
theorem paired_small_closing_real (y : ℝ) (hlow : 1/2^128 ≤ y) (hhigh : y ≤ 2710/4194304) :
    190185/100000*y+(75907/500)*y^2+1/2^136+
      (y/2^18+1/2^700+1/2^152+y/2^128) ≤ 2*y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have hp := mul_nonneg (sub_nonneg.2 hlow) (sub_nonneg.2 hhigh)
  nlinarith [hp,hn]

/-- Unchanged large-route constants already tolerate the lowered split. -/
theorem paired_large_closing_real (y : ℝ) (hlow : 2710/4194304 ≤ y) :
    (2*y-y^2)+y*(6117/10000000)+y*(1/2^25)+y*(1/2^50)+1/2^131+
      (y/2^18+1/2^700+1/2^152+y/2^128) ≤ 2*y := by
  have hn : 0 ≤ y := le_trans (by norm_num) hlow
  have hsq : y*(2710/4194304) ≤ y^2 := by nlinarith [mul_le_mul_of_nonneg_left hlow hn]
  have habs : (1 : ℝ)/2^131 ≤ y/2^109 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2^109 by positivity)
    norm_num at h ⊢
    linarith
  have h700 : (1 : ℝ)/2^700 ≤ y/2^678 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2^678 by positivity)
    norm_num at h ⊢
    linarith
  have h152 : (1 : ℝ)/2^152 ≤ y/2^130 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2^130 by positivity)
    norm_num at h ⊢
    linarith
  nlinarith

/-- The new split is strictly inside the current small-route window, so
all old monotone coefficient estimates remain available there. -/
theorem paired_split_le_old : 2710*2^106 ≤ 2718*2^106 := by norm_num

#print axioms paired_small_closing_real
#print axioms paired_large_closing_real
#print axioms old_split_fails_regrouped_closing
end SigGolfCandidate.Research.V7Composed198Closing.AdjacentLeafResearch
