import Mathlib.Tactic.GCongr
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

/-! Reverse-checksum research: a static chain-53 suffix knows its own digit,
so the last checksum addition can be replaced by comparison against that
existing digit constant. This is a local arithmetic gate, not a certificate
for a changed verification image. -/
namespace SigGolfCandidate.Research.V7Composed198Closing.ReverseChecksum
open BitVec
/-- Forward equality after adding the last digit equals reverse equality
before subtracting it, including modulo-2^64 arithmetic. -/
theorem final_comparison (a d : BitVec 64) :
    a + d = 0#64 ↔ -a = d := by
  constructor
  · intro h
    calc -a = -a + 0#64 := by rw [BitVec.add_zero]
         _ = -a + (a+d) := by rw [h]
         _ = d := by rw [← BitVec.add_assoc, BitVec.add_left_neg, BitVec.zero_add]
  · intro h
    rw [← h, BitVec.add_right_neg]
#print axioms final_comparison
end SigGolfCandidate.Research.V7Composed198Closing.ReverseChecksum

namespace SigGolfCandidate.Research.V7Composed198Closing.WinsorDualHalf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
theorem small_closing_real (y : ℝ) (hlow : 1 / 2 ^ 128 ≤ y) (hhigh : y ≤ 1000 / 4194304) :
    196327 / 100000 * y + (75701 / 500) * y ^ 2 + 1 / 2 ^ 136 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  -- T8E: the quadratic is charged on the whole window [2^-128, y0] through (y - 2^-128) (y0 - y) ≥ 0 (convexity of
  -- the closing in y); the T8D shortcut 2^-136 ≤ y / 2^8 costs 2^-8 and no longer fits the 1.8e-4 slack at y0.
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have hP := mul_nonneg (sub_nonneg.2 hlow) (sub_nonneg.2 hhigh)
  nlinarith [hP, hn]
theorem large_closing_real (y : ℝ) (hlow : 1000 / 4194304 ≤ y) :
    (2 * y - y ^ 2) + y * (23 / 100000) + y * (1 / 2 ^ 25) + y * (1 / 2 ^ 50) + 1 / 2 ^ 131 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by norm_num) hlow
  have hsq : y * (1000 / 4194304) ≤ y ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hlow hn]
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
end SigGolfCandidate.Research.V7Composed198Closing.WinsorDualHalf

/-! Continuous mass pricing. These are reusable scalar lemmas; they do not
certify a changed scheme or change the currently installed security theorem.
The excess of a random price above a threshold is convex in that threshold,
so endpoint certificates can pay for an affine, query-dependent mass price. -/
namespace SigGolfCandidate.Research.V7Composed198Closing.ContinuousPricing
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

theorem positive_part_convex (x a b t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    max 0 (x - ((1 - t) * a + t * b)) ≤
      (1 - t) * max 0 (x - a) + t * max 0 (x - b) := by
  apply max_le
  · exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht1) (le_max_left _ _))
      (mul_nonneg ht0 (le_max_left _ _))
  · have ha := mul_le_mul_of_nonneg_left (le_max_right 0 (x - a))
      (sub_nonneg.mpr ht1)
    have hb := mul_le_mul_of_nonneg_left (le_max_right 0 (x - b)) ht0
    nlinarith

/-- An affine excess envelope follows from its two endpoint bounds.
`E` can be the expectation of the positive part, with convexity obtained
by integrating `positive_part_convex`. -/
theorem affine_endpoint_bound (E : ℝ → ℝ) (lo hi adm rate t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hconvex : ∀ a b s : ℝ, 0 ≤ s → s ≤ 1 →
      E ((1 - s) * a + s * b) ≤ (1 - s) * E a + s * E b)
    (hlo : E (2 - 2 * lo - adm) ≤ rate * lo)
    (hhi : E (2 - 2 * hi - adm) ≤ rate * hi) :
    E (2 - 2 * ((1 - t) * lo + t * hi) - adm) ≤
      rate * ((1 - t) * lo + t * hi) := by
  have hc := hconvex (2 - 2 * lo - adm) (2 - 2 * hi - adm) t ht0 ht1
  have ha := mul_le_mul_of_nonneg_left hlo (sub_nonneg.mpr ht1)
  have hb := mul_le_mul_of_nonneg_left hhi ht0
  have harg : (1 - t) * (2 - 2 * lo - adm) + t * (2 - 2 * hi - adm) =
      2 - 2 * ((1 - t) * lo + t * hi) - adm := by ring
  rw [harg] at hc
  nlinarith

/-- The continuous excess envelope leaves enough quadratic reserve for the
existing cache and secondary-error terms on the large-query interval. -/
theorem large_closing_real (y excess : ℝ) (hlow : 1000 / 4194304 ≤ y)
    (hexcess : excess ≤ (49 / 50) * y) :
    (2 * y - y ^ 2) + y * excess + y * (1 / 2 ^ 25) +
      y * (1 / 2 ^ 50) + 1 / 2 ^ 131 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by norm_num) hlow
  have he := mul_le_mul_of_nonneg_left hexcess hn
  have hsq : y * (1000 / 4194304) ≤ y ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlow hn]
  have habs : (1 : ℝ) / 2 ^ 131 ≤ y / 2 ^ 109 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 109 by positivity)
    norm_num at h ⊢
    linarith
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 678 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 678 by positivity)
    norm_num at h ⊢
    linarith
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 130 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 130 by positivity)
    norm_num at h ⊢
    linarith
  nlinarith

/-- Cap-777 large-query closing: the thinned excess envelope `(993/1000)·y` on `y ≥ 3/2500`. -/
theorem large_closing_real_cap777 (y excess : ℝ) (hlow : 3 / 2500 ≤ y)
    (hexcess : excess ≤ (993 / 1000) * y) :
    (2 * y - y ^ 2) + y * excess + y * (1 / 2 ^ 25) +
      y * (1 / 2 ^ 50) + 1 / 2 ^ 131 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by norm_num) hlow
  have he := mul_le_mul_of_nonneg_left hexcess hn
  have hsq : y * (3 / 2500) ≤ y ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlow hn]
  have habs : (1 : ℝ) / 2 ^ 131 ≤ y / 2 ^ 121 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 121 by positivity)
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

#print axioms positive_part_convex
#print axioms affine_endpoint_bound
#print axioms large_closing_real
#print axioms large_closing_real_cap777
end SigGolfCandidate.Research.V7Composed198Closing.ContinuousPricing

/-! A separate conditional closing packet that retains the query-class
budgets. Applying this packet requires a near-event theorem charged to the
forest query classes; the existing unclassified quadratic bound does not
establish that premise. -/
namespace SigGolfCandidate.Research.V7Composed198Closing.ClassifiedQueries
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

theorem class_budget (p e o m y : ℝ)
    (hp : 0 ≤ p) (he : 0 ≤ e) (ho : 0 ≤ o) (hm : 0 ≤ m)
    (hbudget : p + e + o + m ≤ y) (hy : y ≤ 1 / 1250) :
    (249 / 125) * p + (249 / 125) * e + o + (1701 / 1000) * m +
      350 * y * (o + m) ≤ (249 / 125) * y := by
  have hnear : 350 * y * (o + m) ≤ (7 / 25) * (o + m) := by
    nlinarith [mul_le_mul_of_nonneg_right hy (add_nonneg ho hm)]
  nlinarith

/-- A possible larger small-query window, conditional on the classified
near-event charge and an excess certificate at the chosen bank threshold. -/
theorem small_closing_real (y excess : ℝ) (hlow : 1 / 2 ^ 128 ≤ y)
    (hhigh : y ≤ 1 / 1250) (hexcess : excess ≤ 3 / 1000) :
    (249 / 125) * y + y * excess + (71 / 100) * y ^ 2 + 1 / 2 ^ 136 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have he := mul_le_mul_of_nonneg_left hexcess hn
  have hsq : y ^ 2 ≤ y / 1250 := by
    nlinarith [mul_le_mul_of_nonneg_left hhigh hn]
  have habs : (1 : ℝ) / 2 ^ 136 ≤ y / 256 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 256 by norm_num)
    norm_num at h ⊢
    linarith
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 572 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 572 by positivity)
    norm_num at h ⊢
    linarith
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 24 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 24 by positivity)
    norm_num at h ⊢
    linarith
  nlinarith

#print axioms class_budget
#print axioms small_closing_real
end SigGolfCandidate.Research.V7Composed198Closing.ClassifiedQueries

namespace SigGolfCandidate.Research.V7Composed198Closing.TwoNearBounds
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

/-- Combining a probability bound with a query-cost bound preserves the
unused linear allowance of the forest query class. Both premises are needed. -/
theorem charge (y z near : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 1250)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ z)
    (hquad : near ≤ 160 * y ^ 2) :
    z + near - (249 / 125) * z ≤ (176 / 125) * y ^ 2 := by
  have hny := mul_le_mul_of_nonneg_left hy1 hn
  have hz : z + near - (249 / 125) * z ≤ (11 / 1250) * near := by
    nlinarith
  nlinarith

theorem class_budget (p e o m y near : ℝ)
    (hp : 0 ≤ p) (he : 0 ≤ e) (ho : 0 ≤ o) (hm : 0 ≤ m)
    (hbudget : p + e + o + m ≤ y) (hy : y ≤ 1 / 1250)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ o)
    (hquad : near ≤ 160 * y ^ 2) :
    (249 / 125) * (p + e + m) + o + near ≤
      (249 / 125) * y + (176 / 125) * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hc := charge y o near hy0 hy hn hcost hquad
  nlinarith

/-- Scalar closing for the two-bound route. This is conditional research:
the query-cost bound must be transported to the same experiment as the
quadratic near-event bound before the preceding lemma applies. -/
theorem small_closing_real (y excess : ℝ) (hlow : 1 / 2 ^ 128 ≤ y)
    (hhigh : y ≤ 1 / 1250) (hexcess : excess ≤ 1 / 1000) :
    (249 / 125) * y + y * excess + (2118 / 1000) * y ^ 2 + 1 / 2 ^ 136 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have he := mul_le_mul_of_nonneg_left hexcess hn
  have hsq : y ^ 2 ≤ y / 1250 := by
    nlinarith [mul_le_mul_of_nonneg_left hhigh hn]
  have habs : (1 : ℝ) / 2 ^ 136 ≤ y / 256 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 256 by norm_num)
    norm_num at h ⊢
    linarith
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 572 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 572 by positivity)
    norm_num at h ⊢
    linarith
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 24 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 24 by positivity)
    norm_num at h ⊢
    linarith
  nlinarith

#print axioms charge
#print axioms class_budget
#print axioms small_closing_real
end SigGolfCandidate.Research.V7Composed198Closing.TwoNearBounds

/-! The canonical ancestor-only producer needs a larger small-query window.
The tiny-query interval is treated separately so its absolute failure term
does not consume the linear allowance throughout the larger interval. -/
namespace SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

theorem charge (y z near : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 3 / 2500)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ z)
    (hquad : near ≤ 180 * y ^ 2) :
    z + near - (99847 / 50000) * z ≤ (767 / 1000) * y ^ 2 := by
  have hny := mul_le_mul_of_nonneg_left hy1 hn
  have hz : z + near - (99847 / 50000) * z ≤ (426 / 100000) * near := by
    nlinarith
  nlinarith [sq_nonneg y]

theorem class_budget (p e o m y near : ℝ)
    (hp : 0 ≤ p) (he : 0 ≤ e) (ho : 0 ≤ o) (hm : 0 ≤ m)
    (hbudget : p + e + o + m ≤ y) (hy : y ≤ 3 / 2500)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ o)
    (hquad : near ≤ 180 * y ^ 2) :
    (99847 / 50000) * (p + e + m) + o + near ≤
      (99847 / 50000) * y + (767 / 1000) * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hc := charge y o near hy0 hy hn hcost hquad
  nlinarith

theorem tiny_closing (y excess : ℝ) (hlow : 1 / 2 ^ 128 ≤ y)
    (hhigh : y ≤ 1 / 2 ^ 28) (hexcess : excess ≤ 2 / 1000) :
    (249 / 125) * y + y * excess + 3 * y ^ 2 + 1 / 2 ^ 136 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have he := mul_le_mul_of_nonneg_left hexcess hn
  have hsq : y ^ 2 ≤ y / 2 ^ 28 := by
    nlinarith [mul_le_mul_of_nonneg_left hhigh hn]
  have habs : (1 : ℝ) / 2 ^ 136 ≤ y / 256 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 256 by norm_num)
    norm_num at h ⊢
    linarith
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 572 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 572 by positivity)
    norm_num at h ⊢
    linarith
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 24 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 24 by positivity)
    norm_num at h ⊢
    linarith
  nlinarith

theorem middle_closing (y excess : ℝ) (hlow : 1 / 2 ^ 28 ≤ y)
    (hhigh : y ≤ 3 / 2500) (hexcess : excess ≤ 23 / 20000) :
    (99847 / 50000) * y + y * excess + (1477 / 1000) * y ^ 2 + 1 / 2 ^ 136 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have he := mul_le_mul_of_nonneg_left hexcess hn
  have hsq : y ^ 2 ≤ (3 / 2500) * y := by
    nlinarith [mul_le_mul_of_nonneg_left hhigh hn]
  have habs : (1 : ℝ) / 2 ^ 136 ≤ y / 2 ^ 108 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 108 by positivity)
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

#print axioms charge
#print axioms class_budget
#print axioms tiny_closing
#print axioms middle_closing
end SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow

namespace SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
theorem middle_closing_rows18 (y excess : ℝ) (hlow : 1 / 2 ^ 28 ≤ y)
    (hhigh : y ≤ 3 / 2500) (hexcess : excess ≤ 149 / 125000) :
    (99847 / 50000) * y + y * excess + (1477 / 1000) * y ^ 2 + 1 / 2 ^ 136 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have he := mul_le_mul_of_nonneg_left hexcess hn
  have hsq : y ^ 2 ≤ (3 / 2500) * y := by
    nlinarith [mul_le_mul_of_nonneg_left hhigh hn]
  have habs : (1 : ℝ) / 2 ^ 136 ≤ y / 2 ^ 108 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 108 by positivity)
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

#print axioms middle_closing_rows18
end SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow

namespace SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1024

/-- The paired near bank, including the birth charge, retains ample room
under the common quadratic envelope after triangular query-pair charging. -/
theorem paired_near_quadratic (y near : ℝ)
    (h : near ≤ (350 + 1 / 1024) / 2 * y ^ 2) :
    near ≤ 180 * y ^ 2 := by nlinarith [sq_nonneg y]

theorem tiny_charge (y z near : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2 ^ 28)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ z)
    (hquad : near ≤ 180 * y ^ 2) :
    z + near - (249 / 125) * z ≤ (3 / 2) * y ^ 2 := by
  have hny := mul_le_mul_of_nonneg_left hy1 hn
  have hz : z + near - (249 / 125) * z ≤ (1 / 120) * near := by
    nlinarith
  nlinarith [sq_nonneg y]

theorem tiny_class_budget (p e o m y near : ℝ)
    (hp : 0 ≤ p) (he : 0 ≤ e) (ho : 0 ≤ o) (hm : 0 ≤ m)
    (hbudget : p + e + o + m ≤ y) (hy : y ≤ 1 / 2 ^ 28)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ o)
    (hquad : near ≤ 180 * y ^ 2) :
    (249 / 125) * (p + e + m) + o + near ≤
      (249 / 125) * y + (3 / 2) * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hc := tiny_charge y o near hy0 hy hn hcost hquad
  nlinarith

#print axioms paired_near_quadratic
#print axioms tiny_charge
#print axioms tiny_class_budget
end SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow

namespace SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
/-- The first-hit denominator remains within the paired quadratic allowance
through the entire small-query window. -/
theorem paired_near_denominator (y near : ℝ) (hy : y ≤ 3 / 2500)
    (h : near ≤ (350 + 1 / 1024) / (2 * (1 - y)) * y ^ 2) :
    near ≤ 180 * y ^ 2 := by
  have hd : 0 < 2 * (1 - y) := by linarith
  have hc : (350 + (1 : ℝ) / 1024) / (2 * (1 - y)) ≤ 180 := by
    apply (div_le_iff₀ hd).2
    linarith
  exact h.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg y))
#print axioms paired_near_denominator
end SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow

namespace SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

theorem paired_partial_denominator (y pwin : ℝ) (hy : y≤3/2500)
    (h : pwin≤((351+1/1024)/(2*(1-y))+1/(2*(1-y)^2))*y^2) :
    pwin≤180*y^2 := by
  have hd : 0<2*(1-y) := by linarith
  have hn : (351+(1:ℝ)/1024)/(2*(1-y))≤176 := by
    apply (div_le_iff₀ hd).2
    linarith
  have hbase : 0<1-y := by linarith
  have hs : 0<2*(1-y)^2 := by positivity
  have hp : (1:ℝ)/(2*(1-y)^2)≤1 := by
    apply (div_le_iff₀ hs).2
    have hz : (997:ℝ)/1000≤1-y := by linarith
    nlinarith [sq_nonneg (1-y-(997:ℝ)/1000)]
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg y))

#print axioms paired_partial_denominator
end SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow

namespace SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

noncomputable def canonicalPrefix (y w : ℝ) : ℝ :=
  w*((3/2+4*y+2*y^2)/(1-y)+4*y/(1-y)^2+186*y/(1-y))+(1-w)*2/(1-y)
noncomputable def canonicalEncoding (y w : ℝ) : ℝ := 7/4+w*10044*y/(1-y)
noncomputable def canonicalError (y w : ℝ) : ℝ :=
  w*((1+(3/2+4*y+2*y^2)*y)/(1-y)+2*y*(1+2*y)/(1-y)^2+
    2*(1+2*y)/(1-y)+93*y*(1+2*y)/(1-y))+(1-w)*(1+2*y)/(1-y)

theorem canonicalPrefix_mono {x y w : ℝ} (hx : 0≤x) (hxy : x≤y) (hy : y<1)
    (hw : 0≤w) (hw1 : w≤1) : canonicalPrefix x w≤canonicalPrefix y w := by
  unfold canonicalPrefix
  have hy0 : 0≤y := hx.trans hxy
  have hd : 0<1-y := by linarith
  have hdx : 0<1-x := by linarith
  have hv : 0≤1-w := by linarith
  gcongr <;> first | positivity | linarith

theorem canonicalEncoding_mono {x y w : ℝ} (hx : 0≤x) (hxy : x≤y) (hy : y<1)
    (hw : 0≤w) : canonicalEncoding x w≤canonicalEncoding y w := by
  unfold canonicalEncoding
  have hy0 : 0≤y := hx.trans hxy
  have hd : 0<1-y := by linarith
  have hdx : 0<1-x := by linarith
  gcongr <;> first | positivity | linarith

theorem canonicalError_mono {x y w : ℝ} (hx : 0≤x) (hxy : x≤y) (hy : y<1)
    (hw : 0≤w) (hw1 : w≤1) : canonicalError x w≤canonicalError y w := by
  unfold canonicalError
  have hy0 : 0≤y := hx.trans hxy
  have hd : 0<1-y := by linarith
  have hdx : 0<1-x := by linarith
  have hv : 0≤1-w := by linarith
  gcongr <;> first | positivity | linarith

theorem middle_coefficients (y : ℝ) (hy0 : 0≤y) (hy : y≤3/2500) :
    canonicalPrefix y (1023/50000)≤99847/50000 ∧
    canonicalEncoding y (1023/50000)≤99847/50000 ∧
    canonicalError y (1023/50000)≤109/100 := by
  refine ⟨(canonicalPrefix_mono hy0 hy (by norm_num) (by norm_num) (by norm_num)).trans ?_,
    (canonicalEncoding_mono hy0 hy (by norm_num) (by norm_num)).trans ?_,
    (canonicalError_mono hy0 hy (by norm_num) (by norm_num) (by norm_num)).trans ?_⟩ <;>
    norm_num [canonicalPrefix,canonicalEncoding,canonicalError]

theorem tiny_coefficients (y : ℝ) (hy0 : 0≤y) (hy : y≤1/2^28) :
    canonicalPrefix y (3/100)≤249/125 ∧ canonicalEncoding y (3/100)≤249/125 ∧
    canonicalError y (3/100)≤109/100 := by
  refine ⟨(canonicalPrefix_mono hy0 hy (by norm_num) (by norm_num) (by norm_num)).trans ?_,
    (canonicalEncoding_mono hy0 hy (by norm_num) (by norm_num)).trans ?_,
    (canonicalError_mono hy0 hy (by norm_num) (by norm_num) (by norm_num)).trans ?_⟩ <;>
    norm_num [canonicalPrefix,canonicalEncoding,canonicalError]

theorem canonical_seed_error (y : ℝ) (hy : y≤3/2500) :
    540*y^3/(1-y)≤(649/1000)*y^2 := by
  have hd : 0<1-y := by linarith
  apply (div_le_iff₀ hd).2
  have hcoef : 540*y≤(649/1000)*(1-y) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg y)]

theorem canonical_weighted_error (y err coefficient : ℝ)
    (hc0 : 0≤coefficient) (hc : coefficient≤109/100)
    (he : err≤(649/1000)*y^2) : coefficient*err≤(710/1000)*y^2 := by
  calc coefficient*err≤coefficient*((649/1000)*y^2) := mul_le_mul_of_nonneg_left he hc0
    _ ≤ (109/100)*((649/1000)*y^2) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := by nlinarith [sq_nonneg y]
#print axioms middle_coefficients
#print axioms tiny_coefficients
#print axioms canonical_seed_error
#print axioms canonical_weighted_error
end SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow

namespace SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
theorem tiny_closing_rows18 (y excess : ℝ) (hlow : 1 / 2 ^ 128 ≤ y)
    (hhigh : y ≤ 1 / 2 ^ 28) (hexcess : excess ≤ 18 / 5000) :
    (249 / 125) * y + y * excess + 3 * y ^ 2 + 1 / 2 ^ 136 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have he := mul_le_mul_of_nonneg_left hexcess hn
  have hsq : y ^ 2 ≤ y / 2 ^ 28 := by
    nlinarith [mul_le_mul_of_nonneg_left hhigh hn]
  have habs : (1 : ℝ) / 2 ^ 136 ≤ y / 256 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 256 by norm_num)
    norm_num at h ⊢
    linarith
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 572 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 572 by positivity)
    norm_num at h ⊢
    linarith
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 24 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 24 by positivity)
    norm_num at h ⊢
    linarith
  nlinarith

#print axioms tiny_closing_rows18
end SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
