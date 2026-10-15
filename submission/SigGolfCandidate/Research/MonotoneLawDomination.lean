import SigGolfCandidate.ClaudeWCT.Numerics.LawAverage

/-!
Research-only helper for a tighter near-price certificate.  This module is not
imported by Solution and changes neither the declared scheme nor its bounds.
Compilation is deliberately delegated to the hosted Lean verifier.

A density bound on whole payoffs pays a factor on the baseline as well as on
the increment.  For insertion-monotone payoffs we can instead dominate a marked
step by increasing its arrival probability, without inflating the baseline.
The Poisson coupling and its finite rational checker are NOT supplied here.
-/

namespace ClaudeWCT.Numerics.Law
open ENNReal Finset

section DensityDomination
variable {β : Type} [Fintype β]

/-- One monotone step under a dominated mark law is bounded by a more frequent
step under the dominating law. Both laws must be normalized. -/
theorem monotone_mixture_density_le
    (v u : β → ENNReal) (hv : ∑ b, v b = 1) (hu : ∑ b, u b = 1)
    (p κ : ENNReal) (hp : p ≤ 1) (hκp : κ * p ≤ 1)
    (hdensity : ∀ b, v b ≤ κ * u b)
    (a : ENNReal) (b : β → ENNReal) (hab : ∀ x, a ≤ b x) :
    (1 - p) * a + p * ∑ x, v x * b x ≤
      (1 - κ * p) * a + (κ * p) * ∑ x, u x * b x := by
  classical
  choose d hd using fun x => exists_add_of_le (hab x)
  have mix (w : β → ENNReal) (hw : ∑ x, w x = 1)
      (q : ENNReal) (hq : q ≤ 1) :
      (1 - q) * a + q * ∑ x, w x * b x =
        a + q * ∑ x, w x * d x := by
    simp_rw [hd, mul_add]
    rw [sum_add_distrib, ← sum_mul, hw, one_mul, mul_add,
      ← add_assoc, ← add_mul, tsub_add_cancel_of_le hq, one_mul]
  rw [mix v hv p hp, mix u hu (κ * p) hκp]
  apply add_le_add_left
  calc
    p * ∑ x, v x * d x ≤ p * ∑ x, (κ * u x) * d x :=
      mul_le_mul' le_rfl (sum_le_sum fun x _ => mul_le_mul' (hdensity x) le_rfl)
    _ = (κ * p) * ∑ x, u x * d x := by
      simp_rw [mul_assoc]
      rw [← mul_sum]
      ring

/-- Iterate the monotone-step comparison. Arbitrary insertion monotonicity is
needed: the induction also evaluates payoffs with an already fixed prefix.
This theorem compares marked binomial averages, not Poisson averages. -/
theorem coordAverage_density_le
    (v u : β → ENNReal) (hv : ∑ b, v b = 1) (hu : ∑ b, u b = 1)
    (p κ : ENNReal) (hp : p ≤ 1) (hκp : κ * p ≤ 1)
    (hdensity : ∀ b, v b ≤ κ * u b)
    (T : ℕ) (f : List β → ENNReal)
    (hf : ∀ L b R, f (L ++ R) ≤ f (L ++ b :: R)) :
    coordAverage p v T f ≤ coordAverage (κ * p) u T f := by
  induction T generalizing f with
  | zero => exact le_rfl
  | succ T ih =>
    rw [coordAverage_succ, coordAverage_succ]
    have hprefix (b : β) :
        coordAverage p v T (fun L => f (b :: L)) ≤
          coordAverage (κ * p) u T (fun L => f (b :: L)) := by
      apply ih
      intro L a R
      exact hf (b :: L) a R
    calc
      (1 - p) * coordAverage p v T f +
          p * ∑ b, v b * coordAverage p v T (fun L => f (b :: L)) ≤
        (1 - p) * coordAverage (κ * p) u T f +
          p * ∑ b, v b * coordAverage (κ * p) u T (fun L => f (b :: L)) :=
        add_le_add (mul_le_mul' le_rfl (ih f hf))
          (mul_le_mul' le_rfl
            (sum_le_sum fun b _ => mul_le_mul' le_rfl (hprefix b)))
      _ ≤ (1 - κ * p) * coordAverage (κ * p) u T f +
          (κ * p) * ∑ b, u b * coordAverage (κ * p) u T (fun L => f (b :: L)) := by
        apply monotone_mixture_density_le v u hv hu p κ hp hκp hdensity
        intro b
        apply coordAverage_mono
        intro L
        exact hf [] b L

end DensityDomination
end ClaudeWCT.Numerics.Law
