import VCVio.EvalDist.Defs.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Hölder's inequality for `expectedValue` (r3-lean-topbytes, img-v6 expand moment)

`E[f·g] ≤ E[f^p]^(1/p) · E[g^q]^(1/q)` for conjugate exponents, for the discrete expectation
`expectedValue mx g = ∑' x, Pr[= x | mx] * g x`. Proof: write the expectation as a lower Lebesgue integral against the
discrete measure `∑ x, Pr[= x | mx] • dirac x` (on the ⊤ σ-algebra) and apply `ENNReal.lintegral_mul_le_Lp_mul_Lq`. -/

namespace ClaudeWCT.Arith.ExpectHolder
open OracleComp OracleComp.EvalDist ENNReal MeasureTheory

section
variable {m : Type → Type} [MonadLiftT m SPMF] {α : Type}

theorem expectedValue_eq_lintegral (mx : m α) (g : α → ℝ≥0∞) :
    letI : MeasurableSpace α := ⊤
    expectedValue mx g = ∫⁻ x, g x ∂(Measure.sum fun x => Pr[= x | mx] • Measure.dirac x) := by
  letI : MeasurableSpace α := ⊤
  haveI : MeasurableSingletonClass α := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  rw [lintegral_sum_measure]
  unfold expectedValue
  congr 1
  funext x
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- **Hölder** for `expectedValue`. -/
theorem expectedValue_mul_le (mx : m α) (f g : α → ℝ≥0∞) {p q : ℝ} (hpq : p.HolderConjugate q) :
    expectedValue mx (fun x => f x * g x) ≤
      expectedValue mx (fun x => f x ^ p) ^ (1 / p) * expectedValue mx (fun x => g x ^ q) ^ (1 / q) := by
  letI : MeasurableSpace α := ⊤
  rw [expectedValue_eq_lintegral, expectedValue_eq_lintegral, expectedValue_eq_lintegral]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable

/-- **Expand moment from the sign moment (Hölder, p = 8, q = 8/7).** If the signer's count `S` has
`E[2^(S/2^17)] ≤ 2` and the expander's excess `D = E ∸ S` has `E[2^((8/7)·D/2^20)] ≤ 2`, then
`E[2^(E/2^20)] ≤ 2^(1/8) · 2^(7/8) = 2`. No independence between `S` and `D` is needed. -/
theorem expand_moment_of_holder (mx : m α) (S E : α → ℕ)
    (hS : expectedValue mx (fun x => (2 : ℝ≥0∞) ^ ((S x : ℝ) / 131072)) ≤ 2)
    (hD : expectedValue mx (fun x => (2 : ℝ≥0∞) ^ ((8 / 7 : ℝ) * ((E x - S x : ℕ) : ℝ) / 1048576)) ≤ 2) :
    expectedValue mx (fun x => (2 : ℝ≥0∞) ^ ((E x : ℝ) / 1048576)) ≤ 2 := by
  have hpq : (8 : ℝ).HolderConjugate (8 / 7) := ⟨by norm_num, by norm_num, by norm_num⟩
  have hpt : ∀ x, (2 : ℝ≥0∞) ^ ((E x : ℝ) / 1048576) ≤
      (2 : ℝ≥0∞) ^ ((S x : ℝ) / 1048576) * (2 : ℝ≥0∞) ^ (((E x - S x : ℕ) : ℝ) / 1048576) := by
    intro x
    rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
    apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (E x : ℝ) ≤ (S x : ℝ) + ((E x - S x : ℕ) : ℝ) := by
      exact_mod_cast (by omega : E x ≤ S x + (E x - S x))
    rw [← add_div]
    exact div_le_div_of_nonneg_right this (by norm_num)
  refine (expectedValue_mono mx hpt).trans ((expectedValue_mul_le mx _ _ hpq).trans ?_)
  have h1 : (fun x => ((2 : ℝ≥0∞) ^ ((S x : ℝ) / 1048576)) ^ (8 : ℝ)) =
      fun x => (2 : ℝ≥0∞) ^ ((S x : ℝ) / 131072) := by
    funext x; rw [← ENNReal.rpow_mul]; congr 1; ring
  have h2 : (fun x => ((2 : ℝ≥0∞) ^ (((E x - S x : ℕ) : ℝ) / 1048576)) ^ (8 / 7 : ℝ)) =
      fun x => (2 : ℝ≥0∞) ^ ((8 / 7 : ℝ) * ((E x - S x : ℕ) : ℝ) / 1048576) := by
    funext x; rw [← ENNReal.rpow_mul]; congr 1; ring
  rw [h1, h2]
  calc expectedValue mx (fun x => (2 : ℝ≥0∞) ^ ((S x : ℝ) / 131072)) ^ (1 / (8 : ℝ)) *
        expectedValue mx (fun x => (2 : ℝ≥0∞) ^ ((8 / 7 : ℝ) * ((E x - S x : ℕ) : ℝ) / 1048576)) ^ (1 / (8 / 7 : ℝ))
      ≤ (2 : ℝ≥0∞) ^ (1 / (8 : ℝ)) * (2 : ℝ≥0∞) ^ (1 / (8 / 7 : ℝ)) := by
        gcongr
    _ = 2 := by
        rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
        norm_num

end
end ClaudeWCT.Arith.ExpectHolder
