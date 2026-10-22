import Mathlib.Tactic

/- Copied from nconsigny public submission 235d7b1d-d94d-4773-bd05-54e244f3b66f,
   isolated for native kernel checking. These are conditional arithmetic closing
   lemmas, not a signature-security certificate. -/
/-! RC938 closing at gate 791 (route C): near bank `378`, paired quadratic `18973/100`, charge `8077/10000`
(factor `4257/10^6 ≥ 1 - (θ-1)(1-y_s)`), middle quadratic `8077/10000 + 778/1000 = 15857/10000`, middle excess
budget `1153/10^6`; tiny class budget `18973/12000` (`+ 778/1000 ≤ 3`). -/
namespace SigGolfCandidate.Research.RouteCSmallClosing
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

theorem paired_partial_denominatorRC (y pwin : ℝ) (hy : y≤3/2500)
    (h : pwin≤((378+1/1024)/(2*(1-y))+1/(2*(1-y)^2))*y^2) :
    pwin≤(18973/100)*y^2 := by
  have hd : 0<2*(1-y) := by linarith
  have hn : (378+(1:ℝ)/1024)/(2*(1-y))≤1892276/10000 := by
    apply (div_le_iff₀ hd).2
    linarith
  have hbase : (2497:ℝ)/2500≤1-y := by linarith
  have hs : 0<2*(1-y)^2 := by positivity
  have hp : (1:ℝ)/(2*(1-y)^2)≤5013/10000 := by
    apply (div_le_iff₀ hs).2
    nlinarith [sq_nonneg (1-y-(2497:ℝ)/2500)]
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg y))

theorem chargeRC (y z near : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 3 / 2500)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ z)
    (hquad : near ≤ (18973 / 100) * y ^ 2) :
    z + near - (99847 / 50000) * z ≤ (8077 / 10000) * y ^ 2 := by
  have hny := mul_le_mul_of_nonneg_left hy1 hn
  have hz : z + near - (99847 / 50000) * z ≤ (4257 / 1000000) * near := by
    nlinarith
  nlinarith [sq_nonneg y]

theorem class_budgetRC (p e o m y near : ℝ)
    (hp : 0 ≤ p) (he : 0 ≤ e) (ho : 0 ≤ o) (hm : 0 ≤ m)
    (hbudget : p + e + o + m ≤ y) (hy : y ≤ 3 / 2500)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ o)
    (hquad : near ≤ (18973 / 100) * y ^ 2) :
    (99847 / 50000) * (p + e + m) + o + near ≤
      (99847 / 50000) * y + (8077 / 10000) * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hc := chargeRC y o near hy0 hy hn hcost hquad
  nlinarith

/-- Live middle window at gate 791: quadratic `8077/10000 + 778/1000 = 15857/10000`, excess `1153/10^6`. -/
theorem grouped_middle_closingRC (y excess : ℝ) (hlow : 1 / 2 ^ 28 ≤ y)
    (hhigh : y ≤ 3 / 2500) (hexcess : excess ≤ 1153 / 1000000) :
    (99847 / 50000) * y + y * excess + (15857 / 10000) * y ^ 2 + 1 / 2 ^ 136 +
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

theorem tiny_chargeRC (y z near : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2 ^ 28)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ z)
    (hquad : near ≤ (18973 / 100) * y ^ 2) :
    z + near - (249 / 125) * z ≤ (18973 / 12000) * y ^ 2 := by
  have hny := mul_le_mul_of_nonneg_left hy1 hn
  have hz : z + near - (249 / 125) * z ≤ (1 / 120) * near := by
    nlinarith
  nlinarith [sq_nonneg y]

theorem tiny_class_budgetRC (p e o m y near : ℝ)
    (hp : 0 ≤ p) (he : 0 ≤ e) (ho : 0 ≤ o) (hm : 0 ≤ m)
    (hbudget : p + e + o + m ≤ y) (hy : y ≤ 1 / 2 ^ 28)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ o)
    (hquad : near ≤ (18973 / 100) * y ^ 2) :
    (249 / 125) * (p + e + m) + o + near ≤
      (249 / 125) * y + (18973 / 12000) * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hc := tiny_chargeRC y o near hy0 hy hn hcost hquad
  nlinarith

theorem grouped_tiny_quadraticRC : (18973 / 12000 : ℝ) + 778 / 1000 ≤ 3 := by norm_num

#print axioms paired_partial_denominatorRC
#print axioms class_budgetRC
#print axioms grouped_middle_closingRC
#print axioms tiny_class_budgetRC
end SigGolfCandidate.Research.RouteCSmallClosing

