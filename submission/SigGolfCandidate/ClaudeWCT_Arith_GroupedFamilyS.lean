import SigGolfCandidate.ClaudeWCT_Arith_FamilyTest
set_option Elab.async false

/-! # Family side channel with a point stride (r3-lean-seedfam)

`g` leaves of `w` chains, points `l·s + c + 1` with stride `s ≥ w` (lower `s = w = 43`; top `s = 64`, `w = 54`).
Injective, and below `1024` when `(g - 1)·s + w < 1024`. -/

namespace ClaudeWCT.Arith.SideChannel.GroupedFamily
open SigGolfCandidate.T3 (Digest)
open Finset

/-- Point of family chain `(l, c)` with stride `s`. -/
def gptS (s : ℕ) {g w : ℕ} (c : Fin g × Fin w) : ℕ := c.1.val * s + c.2.val + 1

theorem gptS_injective {s g w : ℕ} (hws : w ≤ s) : Function.Injective (gptS s (g := g) (w := w)) := by
  intro c c' h
  unfold gptS at h
  have h1 := c.2.isLt; have h2 := c'.2.isLt
  have e1 : c.1.val = c'.1.val := by
    rcases Nat.lt_trichotomy c.1.val c'.1.val with hlt | heq | hgt
    · exfalso
      have : c.1.val * s + s ≤ c'.1.val * s := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
      omega
    · exact heq
    · exfalso
      have : c'.1.val * s + s ≤ c.1.val * s := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hgt
      omega
  have e2 : c.2.val = c'.2.val := by rw [e1] at h; omega
  exact Prod.ext (Fin.ext e1) (Fin.ext e2)

theorem gptS_lt {s g w : ℕ} (hb : (g - 1) * s + w < 1024) (c : Fin g × Fin w) : gptS s c < 1024 := by
  unfold gptS
  have h1 := c.1.isLt; have h2 := c.2.isLt
  have : c.1.val * s ≤ (g - 1) * s := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **Family side channel with a stride.** -/
theorem family_test_le_groupedS {s g w n : ℕ} (hws : w ≤ s) (hb : (g - 1) * s + w < 1024)
    (Rev : Finset (Fin g × Fin w)) (hRev : Rev.card + 3 ≤ n) (a : Free Rev) {α : Type}
    (A : (Fin g × Fin w → Digest) → α → Prop)
    (tr : (Fin g × Fin w → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : ℕ) (hD : ∀ r, tdepth (tr r) ≤ D) :
    ∑ K : Fin n → Digest, prT (seedsY (gptS s) Rev K) (A (seedsR (gptS s) Rev K)) (tr (seedsR (gptS s) Rev K)) ≤
      ∑ K : Fin n → Digest,
          (∑ x, prT (seedsH (gptS s) Rev a K x) (A (seedsR (gptS s) Rev K)) (tr (seedsR (gptS s) Rev K))) /
            Fintype.card Digest +
        2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * kconst D *
          ∑ K : Fin n → Digest, amLen (tr (seedsR (gptS s) Rev K)) :=
  family_test_le (gptS_injective hws) (gptS_lt hb) hRev a A tr D hD

theorem family_test_ge_groupedS {s g w n : ℕ} (hws : w ≤ s) (hb : (g - 1) * s + w < 1024)
    (Rev : Finset (Fin g × Fin w)) (hRev : Rev.card + 3 ≤ n) (a : Free Rev) {α : Type}
    (A : (Fin g × Fin w → Digest) → α → Prop)
    (tr : (Fin g × Fin w → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : ℕ) (hD : ∀ r, tdepth (tr r) ≤ D) :
    ∑ K : Fin n → Digest,
        (∑ x, prT (seedsH (gptS s) Rev a K x) (A (seedsR (gptS s) Rev K)) (tr (seedsR (gptS s) Rev K))) /
          Fintype.card Digest ≤
      ∑ K : Fin n → Digest, prT (seedsY (gptS s) Rev K) (A (seedsR (gptS s) Rev K)) (tr (seedsR (gptS s) Rev K)) +
        2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * kconst D *
          ∑ K : Fin n → Digest, amLen (tr (seedsR (gptS s) Rev K)) :=
  family_test_ge (gptS_injective hws) (gptS_lt hb) hRev a A tr D hD

theorem family_amLen_le_groupedS {s g w n : ℕ} (hws : w ≤ s) (hb : (g - 1) * s + w < 1024)
    (Rev : Finset (Fin g × Fin w)) (hRev : Rev.card + 3 ≤ n) {α : Type}
    (tr : (Fin g × Fin w → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : ℕ) (hD : ∀ r, tdepth (tr r) ≤ D) :
    (∑ K : Fin n → Digest, amLen (tr (seedsR (gptS s) Rev K))) * (1 - (Fintype.card Digest : ℝ)⁻¹ * D) ≤
      ∑ K : Fin n → Digest, enT (seedsY (gptS s) Rev K) (tr (seedsR (gptS s) Rev K)) :=
  family_amLen_le (gptS_injective hws) (gptS_lt hb) hRev tr D hD

/-- v6 shapes: lower `7 × 43`, stride 43 (`6·43 + 43 = 301`); top `4 × 54`, stride 64 (`3·64 + 54 = 246`). -/
theorem v6_points : (7 - 1) * 43 + 43 < 1024 ∧ (4 - 1) * 64 + 54 < 1024 := by decide

#print axioms family_test_le_groupedS
#print axioms family_test_ge_groupedS
end ClaudeWCT.Arith.SideChannel.GroupedFamily
