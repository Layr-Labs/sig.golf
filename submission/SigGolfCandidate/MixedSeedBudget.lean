import Mathlib
set_option debug.skipKernelTC false
namespace MixedSeedBudget
/-- Conditional scalar closing lemma. Scheme-level aggregation is still required. -/
theorem seed_error (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 1251 / 1000000) :
    (2 * 216 * y^3 + 32 * 688 * y^4) / (1-y) ≤ (755/1000) * y^2 := by
  have hd : 0 < 1-y := by linarith
  apply (div_le_iff₀ hd).2
  have hs : y^2 ≤ (1251/1000000 : ℝ)*y := by nlinarith
  have hc : 432*y + 22016*y^2 ≤ (755/1000 : ℝ)*(1-y) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg y)
  nlinarith
theorem seed_error_split (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 2163 / 1000000) :
    (2 * 216 * y^3 + 32 * 688 * y^4) / (1-y) ≤ (261/200) * y^2 := by
  have hd : 0 < 1-y := by linarith
  apply (div_le_iff₀ hd).2
  have hs : y^2 ≤ (2163/1000000 : ℝ)*y := by nlinarith
  have hc : 432*y + 22016*y^2 ≤ (261/200 : ℝ)*(1-y) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg y)
  nlinarith

#print axioms seed_error
#print axioms seed_error_split
end MixedSeedBudget
