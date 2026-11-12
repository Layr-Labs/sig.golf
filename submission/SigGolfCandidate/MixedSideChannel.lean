import SigGolfCandidate.FourSideChannel
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
open Finset
open SigGolfCandidate.T3 (Digest)
namespace ClaudeWCT.Arith.SideChannel.Mixed
noncomputable def oldFactor (D : Nat) : ℝ :=
  2 * ((Fintype.card Digest : ℝ)⁻¹)^3 * kconst D
noncomputable def fourFactor (D : Nat) : ℝ :=
  32 * ((Fintype.card Digest : ℝ)⁻¹)^4 * (D : ℝ)^3
noncomputable def factor (lower : Bool) (D : Nat) : ℝ :=
  if lower then min (oldFactor D) (fourFactor D) else oldFactor D

theorem factor_nonneg (lower : Bool) (D : Nat) : 0 ≤ factor lower D := by
  unfold factor oldFactor fourFactor
  split_ifs <;> positivity

theorem factor_le_old (lower : Bool) (D : Nat) : factor lower D ≤ oldFactor D := by
  unfold factor
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem factor_le_four (D : Nat) : factor true D ≤ fourFactor D := min_le_right _ _

variable {C : Type} [Fintype C] [DecidableEq C] {n : Nat} {pt : C → Nat} {Rev : Finset C}
variable (hpt : Function.Injective pt) (hsmall : ∀ c, pt c < 1024)
  (hRev : Rev.card + 3 ≤ n) (lower : Bool) (hFour : lower = true → Rev.card + 4 ≤ n)

include hpt hsmall hRev hFour in
theorem family_test_le (a : Free Rev) {α : Type} (A : (C → Digest) → α → Prop)
    (tr : (C → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : Nat) (hD : ∀ r, tdepth (tr r) ≤ D) :
    (∑ K : Fin n → Digest, prT (seedsY pt Rev K) (A (seedsR pt Rev K)) (tr (seedsR pt Rev K))) ≤ (∑ K : Fin n → Digest, (∑ s, prT (seedsH pt Rev a K s) (A (seedsR pt Rev K)) (tr (seedsR pt Rev K))) / Fintype.card Digest) + factor lower D * ∑ K : Fin n → Digest, amLen (tr (seedsR pt Rev K)) := by
  cases lower with
  | false =>
    simpa [factor, oldFactor] using ClaudeWCT.Arith.SideChannel.family_test_le hpt hsmall hRev a A tr D hD
  | true =>
    by_cases h : oldFactor D ≤ fourFactor D
    · rw [show factor true D = oldFactor D from min_eq_left h]
      exact ClaudeWCT.Arith.SideChannel.family_test_le hpt hsmall hRev a A tr D hD
    · rw [show factor true D = fourFactor D from min_eq_right (le_of_not_ge h)]
      exact Four.family_test_le Rev hpt hsmall (hFour rfl) a A tr D hD

include hpt hsmall hRev hFour in
theorem family_test_ge (a : Free Rev) {α : Type} (A : (C → Digest) → α → Prop)
    (tr : (C → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : Nat) (hD : ∀ r, tdepth (tr r) ≤ D) :
    (∑ K : Fin n → Digest, (∑ s, prT (seedsH pt Rev a K s) (A (seedsR pt Rev K)) (tr (seedsR pt Rev K))) / Fintype.card Digest) ≤ (∑ K : Fin n → Digest, prT (seedsY pt Rev K) (A (seedsR pt Rev K)) (tr (seedsR pt Rev K))) + factor lower D * ∑ K : Fin n → Digest, amLen (tr (seedsR pt Rev K)) := by
  cases lower with
  | false =>
    simpa [factor, oldFactor] using ClaudeWCT.Arith.SideChannel.family_test_ge hpt hsmall hRev a A tr D hD
  | true =>
    by_cases h : oldFactor D ≤ fourFactor D
    · rw [show factor true D = oldFactor D from min_eq_left h]
      exact ClaudeWCT.Arith.SideChannel.family_test_ge hpt hsmall hRev a A tr D hD
    · rw [show factor true D = fourFactor D from min_eq_right (le_of_not_ge h)]
      exact Four.family_test_ge Rev hpt hsmall (hFour rfl) a A tr D hD

#print axioms family_test_le
#print axioms family_test_ge
end ClaudeWCT.Arith.SideChannel.Mixed
