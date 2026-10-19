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

#print axioms SigGolfCandidate.Research.V7Composed198Closing.large_closing_real_high

/-!
# Paired lower-family scalar repair

The old conservative seed-error summand is 0.702 y². Charging 86 rather
than 54 chains per family test and retaining errCoeff ≤ 2 changes it to
1.114 y², for the slightly smaller split 2710/2^22. All other terms below
are unchanged. This is a conditional numerical repair, not an installed
EUF-CMA reduction for shared source families.
-/

/-! Reverse-checksum research: a static chain-53 suffix knows its own digit,
so the last checksum addition can be replaced by comparison against that
existing digit constant. This is a local arithmetic gate, not a certificate
for a changed verification image. -/

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

#print axioms large_closing_real
end SigGolfCandidate.Research.V7Composed198Closing.ContinuousPricing

/-! A separate conditional closing packet that retains the query-class
budgets. Applying this packet requires a near-event theorem charged to the
forest query classes; the existing unclassified quadratic bound does not
establish that premise. -/


/-! The canonical ancestor-only producer needs a larger small-query window.
The tiny-query interval is treated separately so its absolute failure term
does not consume the linear allowance throughout the larger interval. -/


namespace SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

noncomputable def canonicalPrefix (y w : ℝ) : ℝ :=
  w*((3/2+4*y+2*y^2)/(1-y)+4*y/(1-y)^2+180*y/(1-y))+(1-w)*2/(1-y)
noncomputable def canonicalEncoding (y w : ℝ) : ℝ := 7/4+w*9360*y/(1-y)
noncomputable def canonicalError (y w : ℝ) : ℝ :=
  w*((1+(3/2+4*y+2*y^2)*y)/(1-y)+2*y*(1+2*y)/(1-y)^2+
    2*(1+2*y)/(1-y)+90*y*(1+2*y)/(1-y))+(1-w)*(1+2*y)/(1-y)

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

/-! Route C at gate 804 (R6 campaign, stream RC): the near bank grows from 350 to at most 385
(near moment 382.4 at gate 804), so the quadratic near allowance becomes `194 y^2` and the middle
coefficient `1537/1000`. The excess budget `147/125000` is unchanged. -/
namespace SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindowRC
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

theorem paired_partial_denominator (y pwin nb : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 3 / 2500) (hnb : nb ≤ 385)
    (h : pwin ≤ ((nb + 1 / 1024) / (2 * (1 - y)) + 1 / (2 * (1 - y) ^ 2)) * y ^ 2) :
    pwin ≤ 194 * y ^ 2 := by
  have hd : 0 < 2 * (1 - y) := by linarith
  have hn : (nb + (1 : ℝ) / 1024) / (2 * (1 - y)) ≤ 1931 / 10 := by
    apply (div_le_iff₀ hd).2
    nlinarith
  have hbase : 0 < 1 - y := by linarith
  have hs : 0 < 2 * (1 - y) ^ 2 := by positivity
  have hp : (1 : ℝ) / (2 * (1 - y) ^ 2) ≤ 51 / 100 := by
    apply (div_le_iff₀ hs).2
    have hz : (997 : ℝ) / 1000 ≤ 1 - y := by linarith
    nlinarith [sq_nonneg (1 - y - (997 : ℝ) / 1000)]
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg y))

theorem charge (y z near : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 3 / 2500)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ z) (hquad : near ≤ 194 * y ^ 2) :
    z + near - (99847 / 50000) * z ≤ (827 / 1000) * y ^ 2 := by
  have hny := mul_le_mul_of_nonneg_left hy1 hn
  have hz : z + near - (99847 / 50000) * z ≤ (426 / 100000) * near := by
    nlinarith
  nlinarith [sq_nonneg y]

theorem class_budget (p e o m y near : ℝ)
    (hp : 0 ≤ p) (he : 0 ≤ e) (ho : 0 ≤ o) (hm : 0 ≤ m)
    (hbudget : p + e + o + m ≤ y) (hy : y ≤ 3 / 2500)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ o) (hquad : near ≤ 194 * y ^ 2) :
    (99847 / 50000) * (p + e + m) + o + near ≤ (99847 / 50000) * y + (827 / 1000) * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hc := charge y o near hy0 hy hn hcost hquad
  nlinarith

theorem middle_closing (y excess : ℝ) (hlow : 1 / 2 ^ 28 ≤ y)
    (hhigh : y ≤ 3 / 2500) (hexcess : excess ≤ 147 / 125000) :
    (99847 / 50000) * y + y * excess + (1537 / 1000) * y ^ 2 + 1 / 2 ^ 136 +
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

theorem tiny_charge (y z near : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2 ^ 28)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ z) (hquad : near ≤ 194 * y ^ 2) :
    z + near - (249 / 125) * z ≤ (17 / 10) * y ^ 2 := by
  have hny := mul_le_mul_of_nonneg_left hy1 hn
  have hz : z + near - (249 / 125) * z ≤ (1 / 120) * near := by
    nlinarith
  nlinarith [sq_nonneg y]

theorem tiny_class_budget (p e o m y near : ℝ)
    (hp : 0 ≤ p) (he : 0 ≤ e) (ho : 0 ≤ o) (hm : 0 ≤ m)
    (hbudget : p + e + o + m ≤ y) (hy : y ≤ 1 / 2 ^ 28)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ o) (hquad : near ≤ 194 * y ^ 2) :
    (249 / 125) * (p + e + m) + o + near ≤ (249 / 125) * y + (17 / 10) * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hc := tiny_charge y o near hy0 hy hn hcost hquad
  nlinarith

#print axioms paired_partial_denominator
#print axioms charge
#print axioms class_budget
#print axioms middle_closing
#print axioms tiny_charge
#print axioms tiny_class_budget
end SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindowRC
