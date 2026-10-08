import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

/-!
# Generating polynomial of the FTS-overflow potential

The overflow potential (campaign X1, stream A6) for one digest index is
`G k c r a b = [X^k] (1+X)^c (1 + pIdx X)^r (1 + pNonce X)^a (1 + pQuery X)^b`, the expected value of
`choose (c + S) k` when `S` is a sum of independent Bernoulli variables: `r` with mean `pIdx = 2^-31` (future fresh
signings), `a` with mean `pNonce = 2^-128` (cached digest entries of unsigned messages, hit when the nonce equals
their `rho`), `b` with mean `pQuery = 2^-159` (future charged queries that may create such an entry). Only the
recurrences below are used; the final bound is `G k 0 r 0 b · k! ≤ (r pIdx + b pQuery)^k`.
-/

namespace ClaudeWCT.W9.T3.Security.FtsOverflow
open Polynomial ENNReal

/-- Probability that a fresh digest output carries a given 31-bit index. -/
noncomputable def pIdx : ℝ≥0∞ := (2 ^ 31)⁻¹
/-- Probability that a fresh 128-bit nonce equals a given value. -/
noncomputable def pNonce : ℝ≥0∞ := (2 ^ 128)⁻¹
/-- Per-query charge: a query creates an entry for a given index with probability `pIdx`, hit with `pNonce`. -/
noncomputable def pQuery : ℝ≥0∞ := pIdx * pNonce

/-- The generating polynomial of the potential. -/
noncomputable def genPoly (c r a b : ℕ) : Polynomial ℝ≥0∞ :=
  (1 + X) ^ c * (1 + C pIdx * X) ^ r * (1 + C pNonce * X) ^ a * (1 + C pQuery * X) ^ b

/-- The potential coefficient. -/
noncomputable def G (k c r a b : ℕ) : ℝ≥0∞ := (genPoly c r a b).coeff k

theorem coeff_mul_lin (P : Polynomial ℝ≥0∞) (h : ℝ≥0∞) (k : ℕ) :
    (P * (1 + C h * X)).coeff (k + 1) = P.coeff (k + 1) + h * P.coeff k := by
  rw [mul_add, mul_one, coeff_add, ← mul_assoc, coeff_mul_X, coeff_mul_C, mul_comm]

theorem coeff_mul_lin_zero (P : Polynomial ℝ≥0∞) (h : ℝ≥0∞) :
    (P * (1 + C h * X)).coeff 0 = P.coeff 0 := by
  rw [mul_add, mul_one, coeff_add, ← mul_assoc, coeff_mul_X_zero, add_zero]

theorem coeff_le_mul_lin (P : Polynomial ℝ≥0∞) (h : ℝ≥0∞) (k : ℕ) :
    P.coeff k ≤ (P * (1 + C h * X)).coeff k := by
  cases k with
  | zero => rw [coeff_mul_lin_zero]
  | succ k => rw [coeff_mul_lin]; exact le_self_add

theorem genPoly_c (c r a b : ℕ) : genPoly (c + 1) r a b = genPoly c r a b * (1 + C 1 * X) := by
  simp only [genPoly, map_one, one_mul]; ring

theorem genPoly_r (c r a b : ℕ) : genPoly c (r + 1) a b = genPoly c r a b * (1 + C pIdx * X) := by
  simp only [genPoly]; ring

theorem genPoly_a (c r a b : ℕ) : genPoly c r (a + 1) b = genPoly c r a b * (1 + C pNonce * X) := by
  simp only [genPoly]; ring

theorem genPoly_b (c r a b : ℕ) : genPoly c r a (b + 1) = genPoly c r a b * (1 + C pQuery * X) := by
  simp only [genPoly]; ring

theorem G_c (k c r a b : ℕ) : G (k + 1) (c + 1) r a b = G (k + 1) c r a b + G k c r a b := by
  simp only [G, genPoly_c, coeff_mul_lin, one_mul]

theorem G_r (k c r a b : ℕ) : G (k + 1) c (r + 1) a b = G (k + 1) c r a b + pIdx * G k c r a b := by
  simp only [G, genPoly_r, coeff_mul_lin]

theorem G_a (k c r a b : ℕ) : G (k + 1) c r (a + 1) b = G (k + 1) c r a b + pNonce * G k c r a b := by
  simp only [G, genPoly_a, coeff_mul_lin]

theorem G_b (k c r a b : ℕ) : G (k + 1) c r a (b + 1) = G (k + 1) c r a b + pQuery * G k c r a b := by
  simp only [G, genPoly_b, coeff_mul_lin]

theorem G_mono_c (k c r a b : ℕ) : G k c r a b ≤ G k (c + 1) r a b := by
  simp only [G, genPoly_c]; exact coeff_le_mul_lin _ _ _

theorem G_mono_r (k c r a b : ℕ) : G k c r a b ≤ G k c (r + 1) a b := by
  simp only [G, genPoly_r]; exact coeff_le_mul_lin _ _ _

theorem G_mono_a (k c r a b : ℕ) : G k c r a b ≤ G k c r (a + 1) b := by
  simp only [G, genPoly_a]; exact coeff_le_mul_lin _ _ _

theorem G_mono_b (k c r a b : ℕ) : G k c r a b ≤ G k c r a (b + 1) := by
  simp only [G, genPoly_b]; exact coeff_le_mul_lin _ _ _

/-- `G` is monotone in all four counts. -/
theorem G_mono {k c r a b c' r' a' b' : ℕ} (hc : c ≤ c') (hr : r ≤ r') (ha : a ≤ a') (hb : b ≤ b') :
    G k c r a b ≤ G k c' r' a' b' := by
  have h1 : ∀ c c', c ≤ c' → G k c r a b ≤ G k c' r a b := fun c c' h => by
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (G_mono_c _ _ _ _ _)
  have h2 : ∀ r r', r ≤ r' → G k c' r a b ≤ G k c' r' a b := fun r r' h => by
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (G_mono_r _ _ _ _ _)
  have h3 : ∀ a a', a ≤ a' → G k c' r' a b ≤ G k c' r' a' b := fun a a' h => by
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (G_mono_a _ _ _ _ _)
  have h4 : ∀ b b', b ≤ b' → G k c' r' a' b ≤ G k c' r' a' b' := fun b b' h => by
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (G_mono_b _ _ _ _ _)
  exact (h1 c c' hc).trans ((h2 r r' hr).trans ((h3 a a' ha).trans (h4 b b' hb)))

/-- Consuming one fresh-signing slot together with the `d` cached entries of the signed message dominates a
single Bernoulli of mean `pIdx + d·pNonce`. -/
theorem G_slot (k c r a d b : ℕ) :
    G (k + 1) c r a b + (pIdx + d * pNonce) * G k c r a b ≤ G (k + 1) c (r + 1) (a + d) b := by
  induction d with
  | zero => simp [G_r]
  | succ d ih =>
      rw [← add_assoc a d 1, G_a]
      calc G (k + 1) c r a b + (pIdx + ((d + 1 : ℕ) : ℝ≥0∞) * pNonce) * G k c r a b
          = (G (k + 1) c r a b + (pIdx + d * pNonce) * G k c r a b) + pNonce * G k c r a b := by
            push_cast; ring
        _ ≤ G (k + 1) c (r + 1) (a + d) b + pNonce * G k c (r + 1) (a + d) b :=
            add_le_add ih (mul_le_mul' le_rfl (G_mono le_rfl (Nat.le_succ r) (Nat.le_add_right a d) le_rfl))

/-- The potential dominates the overflow count. -/
theorem choose_le_G (k c r a b : ℕ) : (c.choose k : ℝ≥0∞) ≤ G k c r a b := by
  have h0 : G k c 0 0 0 = c.choose k := by
    simp only [G, genPoly, pow_zero, mul_one, add_comm (1 : Polynomial ℝ≥0∞) X]
    rw [coeff_X_add_one_pow]
  rw [← h0]
  exact G_mono le_rfl (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

theorem G_zero (c r a b : ℕ) : G 0 c r a b = 1 := by
  induction b with
  | succ b ih => simp only [G, genPoly_b, coeff_mul_lin_zero] at ih ⊢; exact ih
  | zero =>
    induction a with
    | succ a ih => simp only [G, genPoly_a, coeff_mul_lin_zero] at ih ⊢; exact ih
    | zero =>
      induction r with
      | succ r ih => simp only [G, genPoly_r, coeff_mul_lin_zero] at ih ⊢; exact ih
      | zero =>
        induction c with
        | succ c ih => simp only [G, genPoly_c, coeff_mul_lin_zero] at ih ⊢; exact ih
        | zero => simp [G, genPoly]

theorem add_pow_ge (s t : ℝ≥0∞) (k : ℕ) : s ^ (k + 1) + (k + 1) * t * s ^ k ≤ (s + t) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc s ^ (k + 2) + ((k + 1 : ℕ) + 1 : ℝ≥0∞) * t * s ^ (k + 1)
          ≤ (s ^ (k + 1) + (k + 1) * t * s ^ k) * (s + t) := by
            have : (s ^ (k + 1) + (k + 1) * t * s ^ k) * (s + t) =
                s ^ (k + 2) + ((k + 1 : ℕ) + 1 : ℝ≥0∞) * t * s ^ (k + 1) +
                  (k + 1) * t * s ^ k * t := by push_cast; ring
            rw [this]; exact le_self_add
        _ ≤ (s + t) ^ (k + 1) * (s + t) := mul_le_mul' ih le_rfl
        _ = (s + t) ^ (k + 1 + 1) := (pow_succ _ _).symm

/-- Maclaurin bound for the initial potential: `k! · G k 0 r 0 b ≤ (r pIdx + b pQuery)^k`. -/
theorem G_initial_le (k r b : ℕ) :
    (k.factorial : ℝ≥0∞) * G k 0 r 0 b ≤ (r * pIdx + b * pQuery) ^ k := by
  induction r generalizing k with
  | zero =>
    induction b generalizing k with
    | zero =>
      cases k with
      | zero => simp [G_zero]
      | succ k =>
        have : G (k + 1) 0 0 0 0 = 0 := by simp [G, genPoly, coeff_one]
        simp [this]
    | succ b ih =>
      cases k with
      | zero => simp [G_zero]
      | succ k =>
        rw [G_b, mul_add, Nat.factorial_succ, Nat.cast_mul]
        calc ((k + 1 : ℕ) : ℝ≥0∞) * k.factorial * G (k + 1) 0 0 0 b +
              ((k + 1 : ℕ) : ℝ≥0∞) * k.factorial * (pQuery * G k 0 0 0 b)
            = (((k + 1).factorial : ℕ) : ℝ≥0∞) * G (k + 1) 0 0 0 b +
                (k + 1) * pQuery * ((k.factorial : ℝ≥0∞) * G k 0 0 0 b) := by
              rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; ring
          _ ≤ ((0 : ℕ) * pIdx + b * pQuery) ^ (k + 1) + (k + 1) * pQuery * ((0 : ℕ) * pIdx + b * pQuery) ^ k :=
              add_le_add (ih (k + 1)) (mul_le_mul' le_rfl (ih k))
          _ ≤ ((0 : ℕ) * pIdx + b * pQuery + pQuery) ^ (k + 1) := add_pow_ge _ _ k
          _ = ((0 : ℕ) * pIdx + ((b + 1 : ℕ) : ℝ≥0∞) * pQuery) ^ (k + 1) := by push_cast; ring
  | succ r ih =>
    cases k with
    | zero => simp [G_zero]
    | succ k =>
      rw [G_r, mul_add, Nat.factorial_succ, Nat.cast_mul]
      calc ((k + 1 : ℕ) : ℝ≥0∞) * k.factorial * G (k + 1) 0 r 0 b +
            ((k + 1 : ℕ) : ℝ≥0∞) * k.factorial * (pIdx * G k 0 r 0 b)
          = (((k + 1).factorial : ℕ) : ℝ≥0∞) * G (k + 1) 0 r 0 b +
              (k + 1) * pIdx * ((k.factorial : ℝ≥0∞) * G k 0 r 0 b) := by
            rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; ring
        _ ≤ (r * pIdx + b * pQuery) ^ (k + 1) + (k + 1) * pIdx * (r * pIdx + b * pQuery) ^ k :=
            add_le_add (ih (k + 1)) (mul_le_mul' le_rfl (ih k))
        _ ≤ (r * pIdx + b * pQuery + pIdx) ^ (k + 1) := add_pow_ge _ _ k
        _ = (((r + 1 : ℕ) : ℝ≥0∞) * pIdx + b * pQuery) ^ (k + 1) := by push_cast; ring

/-- The overflow constant: `2^31` indices, `2^32` signing slots (a winning run logs at most `2^32` requests),
`2^127` charged queries. -/
noncomputable def overflowConst : ℝ≥0∞ := 2 ^ 31 * G 51 0 (2 ^ 32) 0 (2 ^ 127)

theorem overflowConst_le_real : overflowConst ≤ 2 ^ 31 * ((2 + (2 ^ 32)⁻¹) ^ 51 / (Nat.factorial 51 : ℝ≥0∞)) := by
  unfold overflowConst
  refine mul_le_mul' le_rfl ?_
  have hS : (((2 ^ 32 : ℕ) : ℝ≥0∞) * pIdx + ((2 ^ 127 : ℕ) : ℝ≥0∞) * pQuery) = 2 + (2 ^ 32)⁻¹ := by
    have h1 : ((2 ^ 32 : ℕ) : ℝ≥0∞) * pIdx = 2 := by
      rw [pIdx, Nat.cast_pow, Nat.cast_ofNat, show (2 : ℝ≥0∞) ^ 32 = 2 * 2 ^ 31 by ring, mul_assoc,
        ENNReal.mul_inv_cancel (by positivity) (by finiteness), mul_one]
    have h2 : ((2 ^ 127 : ℕ) : ℝ≥0∞) * pQuery = (2 ^ 32)⁻¹ := by
      rw [pQuery, pIdx, pNonce, Nat.cast_pow, Nat.cast_ofNat, ← ENNReal.mul_inv (by left; positivity)
        (by left; finiteness), ← pow_add, show 31 + 128 = 127 + 32 by rfl, pow_add,
        ENNReal.mul_inv (by left; positivity) (by left; finiteness), ← mul_assoc,
        ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]
    rw [h1, h2]
  have h := G_initial_le 51 (2 ^ 32) (2 ^ 127)
  rw [hS] at h
  rw [ENNReal.le_div_iff_mul_le (by left; exact_mod_cast (Nat.factorial_pos 51).ne') (by left; finiteness),
    mul_comm]
  exact h

/-- `overflowConst ≤ 2^-137` (it is `2^-137.88`). -/
theorem overflowConst_le : overflowConst ≤ (2 ^ 137)⁻¹ := by
  refine overflowConst_le_real.trans ?_
  have hf : (Nat.factorial 51 : ℝ≥0∞) = (1551118753287382280224243016469303211063259720016986112000000000000 : ℕ) := by
    rw [Nat.factorial]; rfl
  rw [hf]
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  norm_num

end ClaudeWCT.W9.T3.Security.FtsOverflow
