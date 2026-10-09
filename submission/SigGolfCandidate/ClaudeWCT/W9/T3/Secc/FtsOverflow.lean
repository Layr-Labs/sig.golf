import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import SigGolfCandidate.ClaudeWCT.WCT9.Core
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccSufSigned
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCSplit

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

/-!
# The W9 digest index is uniform and independent of producer admissibility

`WCT9.digestIndex` reads bits 33..63 of the digest output; `WCT9.producerAdmissible` reads only bits outside
33..63 (children 0..6, 64.., fields 7..16, 71.., gate 242..255). XOR with `j·2^33` (`j < 2^31`) therefore preserves
admissibility and shifts the index by `j`, so every index fibre of an admissible-invariant event has the same size:
`2^31 · #{P ∧ idx = i} = #{P}`. Expectation forms: `expect_idx` (a fresh output's index is uniform) and
`expect_adm_le` (a fresh output stops the digest search at a uniform index).
-/

namespace ClaudeWCT.W9.T3.Security.FtsOverflow
open SigGolfCandidate.T3 ENNReal OracleComp OracleSpec OracleComp.EvalDist

/-- The W9 digest index as an element of `Fin (2^31)`. -/
def idxF (o : HashOutput) : Fin (2 ^ 31) := ⟨WCT9.digestIndex o, WCT9.digestIndex_lt o⟩

/-- The XOR mask moving the index field by `j`. -/
def idxMask (j : ℕ) : HashOutput := BitVec.ofNat 256 (j * 2 ^ 33)

theorem read_xor (x j b w : ℕ) (hj : j < 2 ^ 31) (h : b + w ≤ 33 ∨ 64 ≤ b) :
    (x ^^^ j * 2 ^ 33) / 2 ^ b % 2 ^ w = x / 2 ^ b % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor, Nat.testBit_mul_two_pow]
  by_cases hi : i < w
  · simp only [hi, decide_true, Bool.true_and]
    rcases h with h | h
    · have : ¬ 33 ≤ i + b := by omega
      simp [this]
    · have hlt : j.testBit (i + b - 33) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hlt]
  · simp [hi]

theorem toNat_xor_idxMask (o : HashOutput) {j : ℕ} (hj : j < 2 ^ 31) :
    (o ^^^ idxMask j).toNat = o.toNat ^^^ j * 2 ^ 33 := by
  rw [BitVec.toNat_xor, idxMask, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem childBase_ok (k : ℕ) : WCT9.childBase k + 7 ≤ 33 ∨ 64 ≤ WCT9.childBase k := by
  rcases Nat.lt_or_ge k 9 with hk | hk
  · interval_cases k <;> decide
  · left
    simp only [WCT9.childBase, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega)]
    simp

theorem fieldBase_ok (k : ℕ) : WCT9.fieldBase k + 10 ≤ 33 ∨ 64 ≤ WCT9.fieldBase k := by
  rcases Nat.lt_or_ge k 9 with hk | hk
  · interval_cases k <;> decide
  · left
    simp only [WCT9.fieldBase, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega)]
    simp

theorem child_xor (o : HashOutput) {j : ℕ} (hj : j < 2 ^ 31) (coord : WCT9.Coord) :
    WCT9.child (o ^^^ idxMask j) coord = WCT9.child o coord := by
  apply Fin.ext
  simp only [WCT9.child, toNat_xor_idxMask o hj]
  exact read_xor _ _ _ 7 hj (childBase_ok coord.val)

theorem field_xor (o : HashOutput) {j : ℕ} (hj : j < 2 ^ 31) (coord : WCT9.Coord) :
    WCT9.field (o ^^^ idxMask j) coord = WCT9.field o coord := by
  simp only [WCT9.field, toNat_xor_idxMask o hj]
  exact read_xor _ _ _ 10 hj (fieldBase_ok coord.val)

theorem producerAdmissible_xor (o : HashOutput) {j : ℕ} (hj : j < 2 ^ 31) :
    WCT9.producerAdmissible (o ^^^ idxMask j) = WCT9.producerAdmissible o := by
  have hrank : ∀ coord, WCT9.rank (o ^^^ idxMask j) coord = WCT9.rank o coord := fun coord => by
    simp only [WCT9.rank, field_xor o hj]
  have hcost : WCT9.jointCost (o ^^^ idxMask j) = WCT9.jointCost o := by
    simp only [WCT9.jointCost, WCT9.coordCost, hrank, child_xor o hj]
  have hadm : WCT9.admissible (o ^^^ idxMask j) = WCT9.admissible o := by
    simp only [WCT9.admissible, toNat_xor_idxMask o hj, read_xor _ _ 242 14 hj (Or.inr (by norm_num))]
    congr 1
    apply List.all_congr rfl
    intro coord
    rw [read_xor _ _ _ 10 hj (fieldBase_ok coord)]
  simp only [WCT9.producerAdmissible, WCT9.capOk, hcost, hadm]

theorem idxF_xor (o : HashOutput) {j : ℕ} (hj : j < 2 ^ 31) :
    (idxF (o ^^^ idxMask j)).val = (idxF o).val ^^^ j := by
  simp only [idxF, WCT9.digestIndex, toNat_xor_idxMask o hj]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor, Nat.testBit_mul_two_pow]
  by_cases hi : i < 31
  · simp [hi, show 33 ≤ i + 33 by omega]
  · have : j.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hi, this, show 33 ≤ i + 33 by omega]

theorem xor_idxMask_involutive (o : HashOutput) (j : ℕ) : o ^^^ idxMask j ^^^ idxMask j = o := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Index fibres of a mask-invariant event have equal size. -/
theorem fiber_card (P : HashOutput → Prop) [DecidablePred P]
    (hP : ∀ o j, j < 2 ^ 31 → (P (o ^^^ idxMask j) ↔ P o)) (i : Fin (2 ^ 31)) :
    2 ^ 31 * (Finset.univ.filter fun o => P o ∧ idxF o = i).card = (Finset.univ.filter P).card := by
  have heq : ∀ i i' : Fin (2 ^ 31), (Finset.univ.filter fun o => P o ∧ idxF o = i).card ≤
      (Finset.univ.filter fun o => P o ∧ idxF o = i').card := by
    intro i i'
    have hj : i.val ^^^ i'.val < 2 ^ 31 := Nat.xor_lt_two_pow i.isLt i'.isLt
    refine Finset.card_le_card_of_injOn (fun o => o ^^^ idxMask (i.val ^^^ i'.val)) ?_ ?_
    · intro o ho
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at ho ⊢
      refine ⟨(hP o _ hj).2 ho.1, Fin.ext ?_⟩
      rw [idxF_xor o hj, ho.2, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    · intro o _ o' _ h
      have := congrArg (fun x => x ^^^ idxMask (i.val ^^^ i'.val)) h
      simpa only [xor_idxMask_involutive] using this
  have hall : ∀ i i' : Fin (2 ^ 31), (Finset.univ.filter fun o => P o ∧ idxF o = i).card =
      (Finset.univ.filter fun o => P o ∧ idxF o = i').card := fun i i' => le_antisymm (heq i i') (heq i' i)
  have hsum : (Finset.univ.filter P).card = ∑ i' : Fin (2 ^ 31), (Finset.univ.filter fun o => P o ∧ idxF o = i').card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := idxF) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro i' _
    rw [Finset.filter_filter]
  rw [hsum, Finset.sum_congr rfl (fun i' _ => hall i' i), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

theorem card_idx (i : Fin (2 ^ 31)) : (Finset.univ.filter fun o : HashOutput => idxF o = i).card = 2 ^ 225 := by
  have h := fiber_card (fun _ : HashOutput => True) (fun _ _ _ => Iff.rfl) i
  simp only [true_and, Finset.filter_true_of_mem (fun (_ : HashOutput) _ => trivial), Finset.card_univ,
    Fintype.card_bitVec] at h
  omega

theorem expect_uniform (F : HashOutput → ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) F = (2 ^ 256)⁻¹ * ∑ o, F o := by
  rw [expectedValue_def, tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  rw [probOutput_uniformSample, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]

theorem pIdx_eq : pIdx = (2 ^ 256)⁻¹ * 2 ^ 225 := by
  rw [pIdx, show (2 : ℝ≥0∞) ^ 256 = 2 ^ 31 * 2 ^ 225 by ring, ENNReal.mul_inv (by left; positivity)
    (by left; finiteness), mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by finiteness), mul_one]

/-- A fresh output's index is uniform. -/
theorem expect_idx (X : Fin (2 ^ 31) → ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun o => X (idxF o)) = ∑ i, pIdx * X i := by
  rw [expect_uniform, ← Finset.sum_fiberwise Finset.univ idxF (fun o => X (idxF o)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_congr rfl (fun o ho => by rw [(Finset.mem_filter.1 ho).2]), Finset.sum_const, nsmul_eq_mul,
    show (Finset.univ.filter fun o : HashOutput => idxF o = i) = Finset.filter (fun o => idxF o = i) Finset.univ
      from rfl, card_idx, pIdx_eq]
  push_cast
  ring

/-- One fresh step of a search whose stop predicate `adm` ignores the index bits: it stops at a uniform index,
or continues. (Stated for a variable predicate: the kernel must never see closed cardinalities of `HashOutput`
sets in Nat arithmetic, which it would try to evaluate.) -/
theorem expect_adm_le_gen (adm : HashOutput → Bool) (hadm : ∀ o j, j < 2 ^ 31 → adm (o ^^^ idxMask j) = adm o)
    (X : Fin (2 ^ 31) → ℝ≥0∞) (Y M : ℝ≥0∞) (hX : ∑ i, pIdx * X i ≤ M) (hY : Y ≤ M) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun o => if adm o = true then X (idxF o) else Y) ≤ M := by
  set A := (Finset.univ.filter fun o : HashOutput => adm o = true).card
  set B := (Finset.univ.filter fun o : HashOutput => ¬ adm o = true).card
  have hAB : A + B = 2 ^ 256 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_bitVec]
  rw [expect_uniform, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun o => adm o = true)]
  have h1 : ∑ o ∈ Finset.univ.filter (fun o => adm o = true),
      (if adm o = true then X (idxF o) else Y) = ∑ i, (A : ℝ≥0∞) * pIdx * X i := by
    rw [Finset.sum_congr rfl (fun o ho => if_pos (Finset.mem_filter.1 ho).2),
      ← Finset.sum_fiberwise _ idxF (fun o => X (idxF o))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_congr rfl (fun o ho => by rw [(Finset.mem_filter.1 ho).2]), Finset.sum_const, nsmul_eq_mul,
      Finset.filter_filter]
    have hc := fiber_card (fun o => adm o = true) (fun o j hj => by rw [hadm o j hj]) i
    have h : (((Finset.univ.filter fun o : HashOutput => adm o = true ∧ idxF o = i).card : ℕ) : ℝ≥0∞) =
        ((2 ^ 31 * (Finset.univ.filter fun o : HashOutput => adm o = true ∧ idxF o = i).card : ℕ) : ℝ≥0∞) *
          pIdx := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pIdx, mul_comm (2 ^ 31 : ℝ≥0∞), mul_assoc,
        ENNReal.mul_inv_cancel (by positivity) (by finiteness), mul_one]
    rw [hc] at h
    rw [h]
  have h2 : ∑ o ∈ Finset.univ.filter (fun o => ¬ adm o = true),
      (if adm o = true then X (idxF o) else Y) = (B : ℝ≥0∞) * Y := by
    rw [Finset.sum_congr rfl (fun o ho => if_neg (Finset.mem_filter.1 ho).2), Finset.sum_const, nsmul_eq_mul]
  rw [h1, h2]
  have hsum : ∑ i, (A : ℝ≥0∞) * pIdx * X i = A * ∑ i, pIdx * X i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  calc (2 ^ 256 : ℝ≥0∞)⁻¹ * (A * ∑ i, pIdx * X i + B * Y)
      ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ * (A * M + B * M) := by gcongr
    _ = (2 ^ 256 : ℝ≥0∞)⁻¹ * ((A + B : ℕ) : ℝ≥0∞) * M := by push_cast; ring
    _ = M := by
      rw [hAB, Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]

/-- One fresh step of the W9 digest search stops at a uniform index or continues. -/
theorem expect_adm_le (X : Fin (2 ^ 31) → ℝ≥0∞) (Y M : ℝ≥0∞) (hX : ∑ i, pIdx * X i ≤ M) (hY : Y ≤ M) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun o => if WCT9.producerAdmissible o = true then X (idxF o) else Y) ≤ M :=
  expect_adm_le_gen WCT9.producerAdmissible (fun o _ hj => producerAdmissible_xor o hj) X Y M hX hY

end ClaudeWCT.W9.T3.Security.FtsOverflow

/-!
# FTS overflow: no digest index is the honest index of 51 distinct signed messages (campaign X1, stream A6)

With arithmetic chain seeds (stage A) each `(index, coordinate)` FTS family has 102 coefficients; 51 distinct
signatures on one index would reveal ≥ 102 points and make the family public. This file bounds the probability of
that event in the experiment the security closings use.

**Event.** `honestIdx s m` is the index of the first producer-admissible digest output of message `m` read from the
lazy state `s` (nonce from the private table, digest outputs from the public cache). `FtsOverflow z` holds when some
index carries ≥ 51 distinct messages.

**Proof.** A potential argument on the lazy game (`CountedPrivate.run`), not the BPORS proposal model (see NOTES.md
[A6]): `pot q r n s = Σ_i G 51 (cnt s i) r (pend s i) (q - n)` (`FtsOverflowAlg.G`), with `r` the remaining signing
slots (a winning run logs ≤ 2^32 requests), `pend s i` the cached admissible-at-`i` digest entries of messages whose
nonce is still hidden (adversary pre-queries; each is hit with probability 2^-128 when the nonce is drawn) and
`q - n` the remaining charged queries (each creates such an entry with probability ≤ 2^-31). Each oracle call is a
supermartingale step; the initial value is `overflowConst ≤ 2^-137`.
-/

namespace ClaudeWCT.W9.T3.Security.FtsOverflow
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The digest-search limit of the W9 signer. -/
abbrev lim : ℕ := WCT9.digestAttemptLimit

/-- The public-cache key of the digest query `(rho, m, c)`. -/
def digestKey (rho : Digest) (m : Message) (c : ℕ) : HashInput := pad64 (digestInput rho m (BitVec.ofNat 32 c))

/-- The nonce (`rho`) derived from a private nonce-table value. -/
def rhoOf (h : HashOutput) : Digest := h.extractLsb' 0 128

/-- The private coordinate of the nonce of `m`. -/
def nonceCoord (m : Message) : Coordinate := .inr (.inl m)

/-- The digest search read from a public cache: `none` if it reaches an uncached query, `some none` if it exhausts
its fuel, `some (some o)` if it stops at the admissible output `o`. -/
def walk (rc : Sampling.RCache) (rho : Digest) (m : Message) : ℕ → ℕ → Option (Option HashOutput)
  | _, 0 => some none
  | c, f + 1 => match rc (digestKey rho m c) with
    | none => none
    | some o => if WCT9.producerAdmissible o = true then some (some o) else walk rc rho m (c + 1) f

/-- The honest digest index of `m` in the lazy state (if `m` was signed and its search stopped). -/
def honestIdx (s : LazyPrivate.State) (m : Message) : Option (Fin (2 ^ 31)) :=
  match (s.1 (nonceCoord m) : Option HashOutput) with
  | none => none
  | some h => match walk s.2 (rhoOf h) m 0 lim with
    | some (some o) => some (idxF o)
    | _ => none

/-- `x` is a cached admissible output with index `i`. -/
def admAt (x : Option HashOutput) (i : Fin (2 ^ 31)) : Bool :=
  match x with
  | none => false
  | some o => WCT9.producerAdmissible o && decide (idxF o = i)

/-- Cached admissible-at-`i` digest entries `(rho, m, c)` with `c0 ≤ c < lim`. -/
noncomputable def hits (rc : Sampling.RCache) (rho : Digest) (m : Message) (c0 : ℕ) (i : Fin (2 ^ 31)) : ℕ :=
  (Finset.univ.filter fun c : Fin lim => c0 ≤ c.val ∧ admAt (rc (digestKey rho m c.val)) i = true).card

/-- Pending mass at index `i`: cached admissible-at-`i` digest entries of messages with a hidden nonce. -/
noncomputable def pend (s : LazyPrivate.State) (i : Fin (2 ^ 31)) : ℕ :=
  ∑ m ∈ Finset.univ.filter (fun m : Message => (s.1 (nonceCoord m) : Option HashOutput) = none),
    ∑ rho : Digest, hits s.2 rho m 0 i

/-- Number of signed messages whose honest index is `i`. -/
noncomputable def cnt (s : LazyPrivate.State) (i : Fin (2 ^ 31)) : ℕ :=
  (Finset.univ.filter fun m : Message => honestIdx s m = some i).card

/-- `cnt` without the message `m₀`. -/
noncomputable def cntEx (s : LazyPrivate.State) (m₀ : Message) (i : Fin (2 ^ 31)) : ℕ :=
  (Finset.univ.filter fun m : Message => m ≠ m₀ ∧ honestIdx s m = some i).card

/-- The overflow potential: `r` signing slots and `q - n` charged queries left. -/
noncomputable def pot (q r n : ℕ) (s : LazyPrivate.State) : ℝ≥0∞ :=
  if n ≤ q then ∑ i, G 51 (cnt s i) r (pend s i) (q - n) else 0

/-- Every signed message's digest search is fully cached (true between oracle calls). -/
def Settled (s : LazyPrivate.State) : Prop :=
  ∀ m h, (s.1 (nonceCoord m) : Option HashOutput) = some h → walk s.2 (rhoOf h) m 0 lim ≠ none

/-- The FTS overflow event on a lazy state. -/
def Overflow (s : LazyPrivate.State) : Prop := ∃ i, 51 ≤ cnt s i

/-! ### Cache facts -/

/-- Cache extension. -/
def Ext (rc rc' : Sampling.RCache) : Prop := ∀ k o, rc k = some o → rc' k = some o

theorem ext_cacheQuery (rc : Sampling.RCache) (k : HashInput) (o : HashOutput) (hk : rc k = none) :
    Ext rc (rc.cacheQuery k o) := by
  intro k' o' h
  have hne : k' ≠ k := fun he => by rw [he, hk] at h; cases h
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact h

theorem walk_ext {rc rc' : Sampling.RCache} (he : Ext rc rc') (rho : Digest) (m : Message) :
    ∀ f c, walk rc rho m c f ≠ none → walk rc' rho m c f = walk rc rho m c f := by
  intro f
  induction f with
  | zero => intro c _; rfl
  | succ f ih =>
    intro c h
    simp only [walk] at h ⊢
    cases hc : rc (digestKey rho m c) with
    | none => rw [hc] at h; exact absurd rfl h
    | some o =>
      rw [hc] at h
      rw [he _ _ hc]
      simp only at h ⊢
      split_ifs with ha
      · rfl
      · rw [if_neg ha] at h; exact ih _ h

theorem digestInput_len (rho : Digest) (m : Message) (c : BitVec 32) : (digestInput rho m c).length = 64 := by
  simp only [digestInput, List.length_append, SphincsSecurity.bytesLE_length]

theorem pad64_digestInput (rho : Digest) (m : Message) (c : BitVec 32) :
    pad64 (digestInput rho m c) = digestInput rho m c := by
  unfold pad64; rw [digestInput_len]; simp

theorem digestKey_injective {rho rho' : Digest} {m m' : Message} {c c' : ℕ} (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (h : digestKey rho m c = digestKey rho' m' c') : rho = rho' ∧ m = m' ∧ c = c' := by
  unfold digestKey at h
  rw [pad64_digestInput, pad64_digestInput] at h
  obtain ⟨h1, h2, h3⟩ := SigGolfCandidate.T3.digestInput_injective h
  refine ⟨h1, h2, ?_⟩
  have := congrArg BitVec.toNat h3
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at this
  exact this

/-! ### Effect of one query on the counts -/

theorem honestIdx_ext {pc : LazyPrivate.PCache} {rc rc' : Sampling.RCache} (he : Ext rc rc')
    (hs : Settled (pc, rc)) (m : Message) : honestIdx (pc, rc') m = honestIdx (pc, rc) m := by
  unfold honestIdx
  dsimp only
  cases hm : (pc (nonceCoord m) : Option HashOutput) with
  | none => rfl
  | some h => dsimp only; rw [walk_ext he _ m lim 0 (hs m h hm)]

theorem settled_ext {pc : LazyPrivate.PCache} {rc rc' : Sampling.RCache} (he : Ext rc rc')
    (hs : Settled (pc, rc)) : Settled (pc, rc') := by
  intro m h hm
  rw [walk_ext he _ m lim 0 (hs m h hm)]
  exact hs m h hm

theorem cnt_ext {pc : LazyPrivate.PCache} {rc rc' : Sampling.RCache} (he : Ext rc rc')
    (hs : Settled (pc, rc)) (i : Fin (2 ^ 31)) : cnt (pc, rc') i = cnt (pc, rc) i := by
  unfold cnt
  simp only [honestIdx_ext he hs]

/-- Nonce entries unchanged: honest indices, pending mass and settledness are unchanged. -/
theorem nonce_same {pc pc' : LazyPrivate.PCache} (rc : Sampling.RCache)
    (h : ∀ m, (pc' (nonceCoord m) : Option HashOutput) = pc (nonceCoord m)) :
    honestIdx (pc', rc) = honestIdx (pc, rc) ∧ pend (pc', rc) = pend (pc, rc) ∧ (Settled (pc', rc) ↔ Settled (pc, rc)) := by
  refine ⟨funext fun m => ?_, funext fun i => ?_, ?_⟩
  · unfold honestIdx; simp only [h]
  · unfold pend; simp only [h]
  · unfold Settled; simp only [h]

theorem hits_insert_le (rc : Sampling.RCache) (k : HashInput) (o : HashOutput)
    (rho : Digest) (m : Message) (c0 : ℕ) (i : Fin (2 ^ 31)) :
    hits (rc.cacheQuery k o) rho m c0 i ≤ hits rc rho m c0 i +
      (Finset.univ.filter fun c : Fin lim => digestKey rho m c.val = k ∧ idxF o = i).card := by
  unfold hits
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hc ⊢
  by_cases hkc : digestKey rho m c.val = k
  · right
    refine ⟨hkc, ?_⟩
    have := hc.2
    rw [hkc, QueryCache.cacheQuery_self] at this
    simp only [admAt, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  · left
    refine ⟨hc.1, ?_⟩
    have := hc.2
    rwa [QueryCache.cacheQuery_of_ne _ _ hkc] at this

theorem key_mass_le (S : Finset Message) (k : HashInput) (o : HashOutput) (i : Fin (2 ^ 31)) :
    ∑ m ∈ S, ∑ rho : Digest, (Finset.univ.filter fun c : Fin lim => digestKey rho m c.val = k ∧ idxF o = i).card ≤
      (if idxF o = i then 1 else 0) := by
  by_cases hi : idxF o = i
  · rw [if_pos hi]
    have hle : ∀ m ∈ S, ∑ rho : Digest, (Finset.univ.filter fun c : Fin lim =>
        digestKey rho m c.val = k ∧ idxF o = i).card =
        (((Finset.univ : Finset Digest) ×ˢ (Finset.univ : Finset (Fin lim))).filter
          (fun p : Digest × Fin lim => digestKey p.1 m p.2.val = k)).card := by
      intro m _
      rw [Finset.card_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro rho _
      rw [Finset.card_filter]
      exact Finset.sum_congr rfl (fun c _ => by simp only [hi, and_true])
    rw [Finset.sum_congr rfl hle]
    have hcard : ∑ m ∈ S, (((Finset.univ : Finset Digest) ×ˢ (Finset.univ : Finset (Fin lim))).filter
        (fun p : Digest × Fin lim => digestKey p.1 m p.2.val = k)).card =
        ((S ×ˢ ((Finset.univ : Finset Digest) ×ˢ (Finset.univ : Finset (Fin lim)))).filter
          (fun p : Message × Digest × Fin lim => digestKey p.2.1 p.1 p.2.2.val = k)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.card_filter]
    rw [hcard]
    apply Finset.card_le_one.2
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    have hl : lim < 2 ^ 32 := by norm_num [lim, WCT9.digestAttemptLimit]
    obtain ⟨h1, h2, h3⟩ := digestKey_injective (lt_trans a.2.2.isLt hl) (lt_trans b.2.2.isLt hl)
      (ha.2.trans hb.2.symm)
    exact Prod.ext h2 (Prod.ext h1 (Fin.ext h3))
  · rw [if_neg hi]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro m _
    apply Finset.sum_eq_zero
    intro rho _
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ h
    exact hi h.2

theorem pend_insert_le (pc : LazyPrivate.PCache) (rc : Sampling.RCache) (k : HashInput) (o : HashOutput)
    (i : Fin (2 ^ 31)) :
    pend (pc, rc.cacheQuery k o) i ≤ pend (pc, rc) i + (if idxF o = i then 1 else 0) := by
  unfold pend
  refine le_trans ?_ (Nat.add_le_add_left
    (key_mass_le (Finset.univ.filter fun m : Message => (pc (nonceCoord m) : Option HashOutput) = none) k o i) _)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro m _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro rho _
  exact hits_insert_le rc k o rho m 0 i

/-! ### One query -/

theorem sum_pIdx : ∑ _j : Fin (2 ^ 31), pIdx = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pIdx, Nat.cast_pow, Nat.cast_ofNat,
    ENNReal.mul_inv_cancel (by positivity) (by finiteness)]

theorem G_a_ite (k c r a b : ℕ) (P : Prop) [Decidable P] :
    G (k + 1) c r (a + if P then 1 else 0) b = G (k + 1) c r a b + if P then pNonce * G k c r a b else 0 := by
  split_ifs
  · exact G_a k c r a b
  · simp

theorem pot_mono_n (q r n : ℕ) (s : LazyPrivate.State) : pot q r (n + 1) s ≤ pot q r n s := by
  unfold pot
  split_ifs with h1 h2
  · exact Finset.sum_le_sum fun i _ => G_mono le_rfl le_rfl le_rfl (by omega)
  · omega
  · exact bot_le
  · exact le_rfl

theorem pot_mono_r (q r n : ℕ) (s : LazyPrivate.State) : pot q r n s ≤ pot q (r + 1) n s := by
  unfold pot
  split_ifs
  · exact Finset.sum_le_sum fun i _ => G_mono le_rfl (Nat.le_succ r) le_rfl le_rfl
  · exact le_rfl

theorem run_query_public (y : SphincsSecurity.OracleWorld.Domain) (n : ℕ) (s : LazyPrivate.State) :
    CountedPrivate.run (liftM (SigGolfCandidate.T3.Spec.query (.inl y))) (n, s) =
      (fun res => (res.1, (n + FullGame.queryCharge (.inl y), (s.1, res.2)))) <$>
        (SphincsSecurity.romImpl y).run s.2 := by
  rw [CountedPrivate.run_query, LazyPrivate.run_query]
  simp only [PrivateTable.lazyImpl, StateT.run_mk, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]; rfl

theorem run_query_private (c : Coordinate) (n : ℕ) (s : LazyPrivate.State) :
    CountedPrivate.run (liftM (SigGolfCandidate.T3.Spec.query (.inr c))) (n, s) =
      (fun res => (res.1, (n + 1, (res.2, s.2)))) <$>
        (randomOracle (spec := Coordinate →ₒ HashOutput) c).run s.1 := by
  rw [CountedPrivate.run_query, LazyPrivate.run_query]
  simp only [PrivateTable.lazyImpl, StateT.run_mk, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]; rfl

theorem romImpl_unif_run (u : unifSpec.Domain) (rc : Sampling.RCache) :
    (SphincsSecurity.romImpl (.inl u)).run rc = (fun v => (v, rc)) <$> (liftM (unifSpec.query u) : ProbComp _) := by
  have hrun := unifFwdImpl.simulateQ_run (hashSpec := SphincsSecurity.HashSpec)
    (liftM (unifSpec.query u) : ProbComp _) rc
  simp only [simulateQ_spec_query] at hrun
  exact hrun

theorem private_support (c : Coordinate) (pc : LazyPrivate.PCache)
    (res : HashOutput × LazyPrivate.PCache)
    (hres : res ∈ support ((randomOracle (spec := Coordinate →ₒ HashOutput) c).run pc)) :
    ∀ c', c' ≠ c → res.2 c' = pc c' := by
  intro c' hne
  rw [randomOracle.run_eq] at hres
  cases hc : pc c with
  | some v =>
    rw [hc] at hres
    simp only [support_pure, Set.mem_singleton_iff] at hres
    subst hres; rfl
  | none =>
    rw [hc] at hres
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
    obtain ⟨v, _, rfl⟩ := hres
    exact QueryCache.cacheQuery_of_ne _ _ hne

/-- A query that is not a nonce query is a supermartingale step for `pot` and keeps `Settled`. -/
theorem query_step (q r : ℕ) (x : SigGolfCandidate.T3.Spec.Domain) (hx : ∀ m, x ≠ .inr (nonceCoord m))
    (n : ℕ) (s : LazyPrivate.State) (hs : Settled s) :
    expectedValue (CountedPrivate.run (liftM (SigGolfCandidate.T3.Spec.query x)) (n, s))
        (fun res => pot q r res.2.1 res.2.2) ≤ pot q r n s ∧
      ∀ res ∈ support (CountedPrivate.run (liftM (SigGolfCandidate.T3.Spec.query x)) (n, s)), Settled res.2.2 := by
  rcases s with ⟨pc, rc⟩
  rcases x with (u | k) | c
  · rw [run_query_public, romImpl_unif_run]
    simp only [Functor.map_map]
    refine ⟨?_, ?_⟩
    · rw [expectedValue_map]
      apply expectedValue_le_of_support
      intro v _
      simp [FullGame.queryCharge, Derivation.charged]
    · intro res hres
      rw [support_map] at hres
      obtain ⟨v, _, rfl⟩ := hres
      exact hs
  · rw [run_query_public]
    change expectedValue ((fun res => (res.1, (n + 1, (pc, res.2)))) <$> (randomOracle k).run rc) _ ≤ _ ∧
      ∀ res ∈ support ((fun res => (res.1, (n + 1, (pc, res.2)))) <$> (randomOracle k).run rc), _
    rw [randomOracle.run_eq]
    cases hk : rc k with
    | some v =>
      simp only [map_pure, expectedValue_pure, support_pure, Set.mem_singleton_iff, forall_eq]
      exact ⟨pot_mono_n q r n _, hs⟩
    | none =>
      simp only [map_bind, map_pure, expectedValue_bind, expectedValue_pure, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff]
      have hext : ∀ o, Ext rc (rc.cacheQuery k o) := fun o => ext_cacheQuery rc k o hk
      refine ⟨?_, ?_⟩
      · by_cases hq : n + 1 ≤ q
        · have hpt : ∀ o : HashOutput, pot q r (n + 1) (pc, rc.cacheQuery k o) ≤
              ∑ i, G 51 (cnt (pc, rc) i) r (pend (pc, rc) i) (q - (n + 1)) +
                pNonce * G 50 (cnt (pc, rc) (idxF o)) r (pend (pc, rc) (idxF o)) (q - (n + 1)) := by
            intro o
            unfold pot
            rw [if_pos hq]
            calc ∑ i, G 51 (cnt (pc, rc.cacheQuery k o) i) r (pend (pc, rc.cacheQuery k o) i) (q - (n + 1))
                ≤ ∑ i, G 51 (cnt (pc, rc) i) r (pend (pc, rc) i + if idxF o = i then 1 else 0) (q - (n + 1)) := by
                  apply Finset.sum_le_sum
                  intro i _
                  rw [cnt_ext (hext o) hs]
                  exact G_mono le_rfl le_rfl (pend_insert_le pc rc k o i) le_rfl
              _ = _ := by
                  simp only [G_a_ite, Finset.sum_add_distrib]
                  rw [Finset.sum_ite_eq]
                  simp
          calc expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun o => pot q r (n + 1) (pc, rc.cacheQuery k o))
              ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun o =>
                  ∑ i, G 51 (cnt (pc, rc) i) r (pend (pc, rc) i) (q - (n + 1)) +
                    pNonce * G 50 (cnt (pc, rc) (idxF o)) r (pend (pc, rc) (idxF o)) (q - (n + 1))) :=
                expectedValue_mono _ hpt
            _ = ∑ j, pIdx * (∑ i, G 51 (cnt (pc, rc) i) r (pend (pc, rc) i) (q - (n + 1)) +
                  pNonce * G 50 (cnt (pc, rc) j) r (pend (pc, rc) j) (q - (n + 1))) :=
                expect_idx (fun j => ∑ i, G 51 (cnt (pc, rc) i) r (pend (pc, rc) i) (q - (n + 1)) +
                  pNonce * G 50 (cnt (pc, rc) j) r (pend (pc, rc) j) (q - (n + 1)))
            _ = ∑ j, G 51 (cnt (pc, rc) j) r (pend (pc, rc) j) (q - (n + 1) + 1) := by
                simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_pIdx, one_mul, G_b, pQuery,
                  ← mul_assoc]
            _ = pot q r n (pc, rc) := by
                unfold pot
                rw [if_pos (by omega), show q - (n + 1) + 1 = q - n by omega]
        · have h0 : ∀ o : HashOutput, pot q r (n + 1) (pc, rc.cacheQuery k o) = 0 := fun o => by
            unfold pot; rw [if_neg hq]
          simp only [h0]
          exact expectedValue_le_of_support fun _ _ => bot_le
      · rintro res ⟨o, _, rfl⟩
        exact settled_ext (hext o) hs
  · rw [run_query_private]
    have hc : ∀ m, c ≠ nonceCoord m := fun m he => hx m (by rw [he])
    have hsame : ∀ res ∈ support ((randomOracle (spec := Coordinate →ₒ HashOutput) c).run pc),
        ∀ m, (res.2 (nonceCoord m) : Option HashOutput) = pc (nonceCoord m) :=
      fun res hres m => private_support c pc res hres _ (hc m).symm
    refine ⟨?_, ?_⟩
    · rw [expectedValue_map]
      apply expectedValue_le_of_support
      intro res hres
      have hn := nonce_same rc (hsame res hres)
      refine le_trans (le_of_eq ?_) (pot_mono_n q r n (pc, rc))
      unfold pot cnt
      rw [hn.1, hn.2.1]
    · intro res hres
      rw [support_map] at hres
      obtain ⟨res, hres, rfl⟩ := hres
      exact (nonce_same rc (hsame res hres)).2.2.2 hs

/-! ### Programs without nonce queries -/

/-- The query is not a nonce query. -/
def NotNonce (x : SigGolfCandidate.T3.Spec.Domain) : Prop := ∀ m, x ≠ .inr (nonceCoord m)

/-- A program without nonce queries is a supermartingale for `pot` and keeps `Settled`. -/
theorem prog_step {α : Type} (q r : ℕ) (P : M α) (hP : AllQueriesSatisfy P NotNonce) :
    ∀ (n : ℕ) (s : LazyPrivate.State), Settled s →
      expectedValue (CountedPrivate.run P (n, s)) (fun res => pot q r res.2.1 res.2.2) ≤ pot q r n s ∧
      ∀ res ∈ support (CountedPrivate.run P (n, s)), Settled res.2.2 := by
  induction P using OracleComp.inductionOn with
  | pure a =>
    intro n s hs
    simp only [CountedPrivate.run_pure, expectedValue_pure, support_pure, Set.mem_singleton_iff, forall_eq]
    exact ⟨le_rfl, hs⟩
  | query_bind x next ih =>
    intro n s hs
    rw [allQueriesSatisfy_query_bind_iff] at hP
    obtain ⟨hx, hnext⟩ := hP
    have hq := query_step q r x hx n s hs
    rw [CountedPrivate.run_bind]
    refine ⟨?_, ?_⟩
    · rw [expectedValue_bind]
      exact le_trans (expectedValue_mono_of_support fun res hres =>
        (ih res.1 (hnext res.1) res.2.1 res.2.2 (hq.2 res hres)).1) hq.1
    · intro res hres
      rw [mem_support_bind_iff] at hres
      obtain ⟨mid, hmid, hres⟩ := hres
      exact (ih mid.1 (hnext mid.1) mid.2.1 mid.2.2 (hq.2 mid hmid)).2 res hres

theorem notNonce_of_avoids {α : Type} (P : M α) (h : ∀ m, NonceFreshness.Avoids m P) :
    AllQueriesSatisfy P NotNonce := by
  induction P using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind x next ih =>
    rw [allQueriesSatisfy_query_bind_iff]
    refine ⟨fun m he => ?_, fun u => ih u fun m => ?_⟩
    · have := (allQueriesSatisfy_query_bind_iff _ _ _).1 (h m)
      exact this.1 he
    · exact ((allQueriesSatisfy_query_bind_iff _ _ _).1 (h m)).2 u

/-! ### The digest search of a freshly drawn nonce -/

/-- Every signed message other than `m₀` is settled. -/
def SettledEx (s : LazyPrivate.State) (m₀ : Message) : Prop :=
  ∀ m h, m ≠ m₀ → (s.1 (nonceCoord m) : Option HashOutput) = some h → walk s.2 (rhoOf h) m 0 lim ≠ none

/-- The first `c` digest queries of `(rho, m)` are cached and not admissible. -/
def Prefix (rc : Sampling.RCache) (rho : Digest) (m : Message) (c : ℕ) : Prop :=
  ∀ c' < c, ∃ o, rc (digestKey rho m c') = some o ∧ WCT9.producerAdmissible o = false

/-- The potential during the digest search of `m₀` (nonce `rho`) at counter `c`. -/
noncomputable def mid (q r : ℕ) (m₀ : Message) (rho : Digest) (c n : ℕ) (s : LazyPrivate.State) : ℝ≥0∞ :=
  if n ≤ q then ∑ i, (G 51 (cntEx s m₀ i) r (pend s i) (q - n) +
    (pIdx + hits s.2 rho m₀ c i) * G 50 (cntEx s m₀ i) r (pend s i) (q - n)) else 0

theorem lim_lt : lim < 2 ^ 32 := by norm_num [lim, WCT9.digestAttemptLimit]

theorem cnt_split (s : LazyPrivate.State) (m₀ : Message) (i : Fin (2 ^ 31)) :
    cnt s i = cntEx s m₀ i + if honestIdx s m₀ = some i then 1 else 0 := by
  unfold cnt cntEx
  rw [Finset.card_filter, Finset.card_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ m₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ m₀)]
  have hsum : ∑ m ∈ Finset.univ.erase m₀, (if honestIdx s m = some i then 1 else 0) =
      ∑ m ∈ Finset.univ.erase m₀, (if m ≠ m₀ ∧ honestIdx s m = some i then 1 else 0) :=
    Finset.sum_congr rfl fun m hm => by simp [Finset.ne_of_mem_erase hm]
  rw [hsum]
  simp only [ne_eq, not_true_eq_false, false_and, if_false, zero_add]
  ring

theorem walk_prefix (rc : Sampling.RCache) (rho : Digest) (m : Message) :
    ∀ c, c ≤ lim → Prefix rc rho m c → walk rc rho m 0 lim = walk rc rho m c (lim - c) := by
  intro c
  induction c with
  | zero => intro _ _; rfl
  | succ c ih =>
    intro hc hp
    rw [ih (by omega) (fun c' hc' => hp c' (by omega)), show lim - c = (lim - (c + 1)) + 1 by omega]
    obtain ⟨o, ho, hna⟩ := hp c (by omega)
    simp only [walk, ho, hna, Bool.false_eq_true, if_false]

theorem honestIdx_ext_ex {pc : LazyPrivate.PCache} {rc rc' : Sampling.RCache} (he : Ext rc rc') {m₀ : Message}
    (hs : SettledEx (pc, rc) m₀) (m : Message) (hm : m ≠ m₀) : honestIdx (pc, rc') m = honestIdx (pc, rc) m := by
  unfold honestIdx
  dsimp only
  cases hh : (pc (nonceCoord m) : Option HashOutput) with
  | none => rfl
  | some h => dsimp only; rw [walk_ext he _ m lim 0 (hs m h hm hh)]

theorem cntEx_ext {pc : LazyPrivate.PCache} {rc rc' : Sampling.RCache} (he : Ext rc rc') {m₀ : Message}
    (hs : SettledEx (pc, rc) m₀) (i : Fin (2 ^ 31)) : cntEx (pc, rc') m₀ i = cntEx (pc, rc) m₀ i := by
  unfold cntEx
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro m _
  constructor
  · rintro ⟨hm, h⟩; exact ⟨hm, (honestIdx_ext_ex he hs m hm) ▸ h⟩
  · rintro ⟨hm, h⟩; exact ⟨hm, (honestIdx_ext_ex he hs m hm).symm ▸ h⟩

theorem settledEx_ext {pc : LazyPrivate.PCache} {rc rc' : Sampling.RCache} (he : Ext rc rc') {m₀ : Message}
    (hs : SettledEx (pc, rc) m₀) : SettledEx (pc, rc') m₀ := by
  intro m h hm hh
  rw [walk_ext he _ m lim 0 (hs m h hm hh)]
  exact hs m h hm hh

theorem pend_insert_own (pc : LazyPrivate.PCache) (rc : Sampling.RCache) {m₀ : Message} {h₀ : HashOutput}
    (hn : (pc (nonceCoord m₀) : Option HashOutput) = some h₀) (rho : Digest) {c : ℕ} (hc : c < lim)
    (o : HashOutput) (i : Fin (2 ^ 31)) :
    pend (pc, rc.cacheQuery (digestKey rho m₀ c) o) i = pend (pc, rc) i := by
  unfold pend hits
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
  have hne : m ≠ m₀ := fun he => by rw [he] at hm; rw [hm] at hn; cases hn
  apply Finset.sum_congr rfl
  intro rho' _
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c' _
  have hk : digestKey rho' m c'.val ≠ digestKey rho m₀ c := fun he =>
    hne (digestKey_injective (lt_trans c'.isLt lim_lt) (lt_trans hc lim_lt) he).2.1
  simp only [QueryCache.cacheQuery_of_ne _ _ hk]

theorem hits_succ_eq (rc : Sampling.RCache) (rho : Digest) (m : Message) (c : ℕ) (i : Fin (2 ^ 31))
    (h : admAt (rc (digestKey rho m c)) i = false) : hits rc rho m (c + 1) i = hits rc rho m c i := by
  unfold hits
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c' _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases Nat.lt_or_ge c c'.val with hlt | hge
    · omega
    · have : c'.val = c := by omega
      rw [this, h] at h2; cases h2

theorem hits_insert_succ (rc : Sampling.RCache) (rho : Digest) (m : Message) {c : ℕ} (hc : c < lim)
    (o : HashOutput) (i : Fin (2 ^ 31)) :
    hits (rc.cacheQuery (digestKey rho m c) o) rho m (c + 1) i = hits rc rho m (c + 1) i := by
  unfold hits
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c' _
  constructor
  · rintro ⟨h1, h2⟩
    have hk : digestKey rho m c'.val ≠ digestKey rho m c := fun he =>
      absurd (digestKey_injective (lt_trans c'.isLt lim_lt) (lt_trans hc lim_lt) he).2.2 (by omega)
    rw [QueryCache.cacheQuery_of_ne _ _ hk] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hk : digestKey rho m c'.val ≠ digestKey rho m c := fun he =>
      absurd (digestKey_injective (lt_trans c'.isLt lim_lt) (lt_trans hc lim_lt) he).2.2 (by omega)
    rw [QueryCache.cacheQuery_of_ne _ _ hk]
    exact ⟨h1, h2⟩

theorem hits_pos (rc : Sampling.RCache) (rho : Digest) (m : Message) {c : ℕ} (hc : c < lim) {o : HashOutput}
    (ho : rc (digestKey rho m c) = some o) (ha : WCT9.producerAdmissible o = true) :
    1 ≤ hits rc rho m c (idxF o) := by
  unfold hits
  apply Finset.card_pos.2
  refine ⟨⟨c, hc⟩, ?_⟩
  simp [ho, admAt, ha]

theorem cnt_le_G_stop (q r n : ℕ) (s : LazyPrivate.State) (m₀ : Message) (j : Fin (2 ^ 31))
    (hidx : honestIdx s m₀ = some j) :
    ∑ i, G 51 (cnt s i) r (pend s i) (q - n) =
      ∑ i, G 51 (cntEx s m₀ i) r (pend s i) (q - n) + G 50 (cntEx s m₀ j) r (pend s j) (q - n) := by
  have : ∀ i, G 51 (cnt s i) r (pend s i) (q - n) =
      G 51 (cntEx s m₀ i) r (pend s i) (q - n) + if j = i then G 50 (cntEx s m₀ i) r (pend s i) (q - n) else 0 := by
    intro i
    rw [cnt_split s m₀ i, hidx]
    by_cases hji : j = i
    · subst hji; simp [G_c]
    · simp [hji]
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

theorem charge_public (k : HashInput) : FullGame.queryCharge (.inl (.inr k)) = 1 := by
  simp [FullGame.queryCharge, Derivation.charged]

theorem digestSearch_succ_eq (rho : Digest) (m : Message) (c f : ℕ) : WCT9.digestSearch rho m c (f + 1) =
    (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr (digestKey rho m c)))) >>= fun output =>
      if WCT9.producerAdmissible output = true then pure (some (BitVec.ofNat 32 c, output))
      else WCT9.digestSearch rho m (c + 1) f) := rfl

theorem walk_stop (rc : Sampling.RCache) (rho : Digest) (m : Message) {c : ℕ} (hc : c < lim)
    (hp : Prefix rc rho m c) {o : HashOutput} (ho : rc (digestKey rho m c) = some o)
    (ha : WCT9.producerAdmissible o = true) : walk rc rho m 0 lim = some (some o) := by
  rw [walk_prefix rc rho m c hc.le hp, show lim - c = (lim - c - 1) + 1 by omega]
  simp only [walk, ho, ha, if_true]

theorem honestIdx_of_walk {pc : LazyPrivate.PCache} {rc : Sampling.RCache} {m₀ : Message} {h₀ : HashOutput}
    (hn : (pc (nonceCoord m₀) : Option HashOutput) = some h₀) {o : HashOutput}
    (hw : walk rc (rhoOf h₀) m₀ 0 lim = some (some o)) : honestIdx (pc, rc) m₀ = some (idxF o) := by
  unfold honestIdx; dsimp only; rw [hn]; dsimp only; rw [hw]

theorem settled_of_ex {pc : LazyPrivate.PCache} {rc : Sampling.RCache} {m₀ : Message} {h₀ : HashOutput}
    (hn : (pc (nonceCoord m₀) : Option HashOutput) = some h₀) (hse : SettledEx (pc, rc) m₀)
    (hw : walk rc (rhoOf h₀) m₀ 0 lim ≠ none) : Settled (pc, rc) := by
  intro m h hh
  by_cases hm : m = m₀
  · subst hm
    have : h = h₀ := by
      have h2 : (pc (nonceCoord m) : Option HashOutput) = some h := hh
      rw [hn] at h2; exact (Option.some.inj h2).symm
    subst this; exact hw
  · exact hse m h hm hh

/-- The potential after stopping at index `j`. -/
theorem pot_stop (q r n : ℕ) (s : LazyPrivate.State) (m₀ : Message) (j : Fin (2 ^ 31))
    (hidx : honestIdx s m₀ = some j) :
    pot q r n s = if n ≤ q then ∑ i, G 51 (cntEx s m₀ i) r (pend s i) (q - n) +
      G 50 (cntEx s m₀ j) r (pend s j) (q - n) else 0 := by
  unfold pot
  split_ifs
  · exact cnt_le_G_stop q r n s m₀ j hidx
  · rfl

theorem mid_mono_n (q r : ℕ) (m₀ : Message) (rho : Digest) (c n : ℕ) (s : LazyPrivate.State) :
    mid q r m₀ rho c (n + 1) s ≤ mid q r m₀ rho c n s := by
  unfold mid
  split_ifs with h1 h2
  · apply Finset.sum_le_sum
    intro i _
    exact add_le_add (G_mono le_rfl le_rfl le_rfl (by omega))
      (mul_le_mul' le_rfl (G_mono le_rfl le_rfl le_rfl (by omega)))
  · omega
  · exact bot_le
  · exact le_rfl

theorem stop_le_mid (q r n : ℕ) (s : LazyPrivate.State) (m₀ : Message) (rho : Digest) (c : ℕ) (j : Fin (2 ^ 31))
    (hpos : 1 ≤ hits s.2 rho m₀ c j) :
    (if n + 1 ≤ q then ∑ i, G 51 (cntEx s m₀ i) r (pend s i) (q - (n + 1)) +
      G 50 (cntEx s m₀ j) r (pend s j) (q - (n + 1)) else 0) ≤ mid q r m₀ rho c n s := by
  unfold mid
  split_ifs with h1 h2
  · rw [Finset.sum_add_distrib]
    refine add_le_add (Finset.sum_le_sum fun i _ => G_mono le_rfl le_rfl le_rfl (by omega)) ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => (pIdx + (hits s.2 rho m₀ c i : ℝ≥0∞)) *
      G 50 (cntEx s m₀ i) r (pend s i) (q - n)) (fun _ _ => bot_le) (Finset.mem_univ j))
    calc G 50 (cntEx s m₀ j) r (pend s j) (q - (n + 1)) ≤ 1 * G 50 (cntEx s m₀ j) r (pend s j) (q - n) := by
          rw [one_mul]; exact G_mono le_rfl le_rfl le_rfl (by omega)
      _ ≤ _ := by
          refine mul_le_mul' ?_ le_rfl
          exact le_add_left (by exact_mod_cast hpos)
  · omega
  · exact bot_le
  · exact le_rfl

/-- The digest search of a freshly drawn nonce: the potential is bounded by `mid`, and every signed message is
settled afterwards. -/
theorem search_step (q r : ℕ) (m₀ : Message) (h₀ : HashOutput) :
    ∀ (f c : ℕ), c + f = lim → ∀ (n : ℕ) (pc : LazyPrivate.PCache) (rc : Sampling.RCache),
      (pc (nonceCoord m₀) : Option HashOutput) = some h₀ → SettledEx (pc, rc) m₀ →
      Prefix rc (rhoOf h₀) m₀ c →
      expectedValue (CountedPrivate.run (WCT9.digestSearch (rhoOf h₀) m₀ c f) (n, (pc, rc)))
          (fun res => pot q r res.2.1 res.2.2) ≤ mid q r m₀ (rhoOf h₀) c n (pc, rc) ∧
        ∀ res ∈ support (CountedPrivate.run (WCT9.digestSearch (rhoOf h₀) m₀ c f) (n, (pc, rc))),
          Settled res.2.2 := by
  intro f
  induction f with
  | zero =>
    intro c hc n pc rc hn hse hpre
    have hcl : c = lim := by omega
    have hw : walk rc (rhoOf h₀) m₀ 0 lim = some none := by
      rw [walk_prefix rc _ m₀ c (by omega) hpre, hcl, Nat.sub_self]; rfl
    have hidx : honestIdx (pc, rc) m₀ = none := by
      unfold honestIdx; dsimp only; rw [hn]; dsimp only; rw [hw]
    rw [show WCT9.digestSearch (rhoOf h₀) m₀ c 0 = pure none from rfl, CountedPrivate.run_pure]
    simp only [expectedValue_pure, support_pure, Set.mem_singleton_iff, forall_eq]
    refine ⟨?_, settled_of_ex hn hse (by rw [hw]; simp)⟩
    unfold pot mid
    split_ifs with hq
    · apply Finset.sum_le_sum
      intro i _
      rw [cnt_split _ m₀ i, hidx]
      simp only [reduceCtorEq, if_false, add_zero]
      exact le_self_add
    · exact le_rfl
  | succ f ih =>
    intro c hc n pc rc hn hse hpre
    have hcl : c < lim := by omega
    rw [digestSearch_succ_eq, CountedPrivate.run_bind, run_query_public, bind_map_left, charge_public]
    change expectedValue ((randomOracle (digestKey (rhoOf h₀) m₀ c)).run rc >>= _) _ ≤ _ ∧
      ∀ res ∈ support ((randomOracle (digestKey (rhoOf h₀) m₀ c)).run rc >>= _), _
    rw [randomOracle.run_eq]
    cases hk : rc (digestKey (rhoOf h₀) m₀ c) with
    | some o =>
      simp only [pure_bind]
      by_cases ha : WCT9.producerAdmissible o = true
      · simp only [ha, if_true, CountedPrivate.run_pure, expectedValue_pure, support_pure,
          Set.mem_singleton_iff, forall_eq]
        have hw := walk_stop rc (rhoOf h₀) m₀ hcl hpre hk ha
        have hidx := honestIdx_of_walk hn hw
        refine ⟨?_, settled_of_ex hn hse (by rw [hw]; simp)⟩
        rw [pot_stop q r (n + 1) _ m₀ _ hidx]
        exact stop_le_mid q r n _ m₀ _ c _ (hits_pos rc _ m₀ hcl hk ha)
      · simp only [ha, Bool.false_eq_true, if_false]
        have hna : WCT9.producerAdmissible o = false := by simpa using ha
        have hpre' : Prefix rc (rhoOf h₀) m₀ (c + 1) := by
          intro c' hc'
          rcases Nat.lt_or_ge c' c with h | h
          · exact hpre c' h
          · have : c' = c := by omega
            subst this; exact ⟨o, hk, hna⟩
        have hih := ih (c + 1) (by omega) (n + 1) pc rc hn hse hpre'
        refine ⟨le_trans hih.1 (le_trans (le_of_eq ?_) (mid_mono_n q r m₀ _ c n _)), hih.2⟩
        have hh : ∀ i, hits rc (rhoOf h₀) m₀ (c + 1) i = hits rc (rhoOf h₀) m₀ c i :=
          fun i => hits_succ_eq rc _ m₀ c i (by simp [hk, admAt, hna])
        unfold mid
        simp only [hh]
    | none =>
      simp only [bind_assoc, pure_bind, expectedValue_bind, mem_support_bind_iff]
      have hext : ∀ o, Ext rc (rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o) := fun o => ext_cacheQuery rc _ o hk
      have hcont : ∀ o, WCT9.producerAdmissible o = false →
          expectedValue (CountedPrivate.run (WCT9.digestSearch (rhoOf h₀) m₀ (c + 1) f)
            (n + 1, (pc, rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o))) (fun res => pot q r res.2.1 res.2.2) ≤
              mid q r m₀ (rhoOf h₀) c (n + 1) (pc, rc) ∧
          ∀ res ∈ support (CountedPrivate.run (WCT9.digestSearch (rhoOf h₀) m₀ (c + 1) f)
            (n + 1, (pc, rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o))), Settled res.2.2 := by
        intro o hna
        have hpre' : Prefix (rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o) (rhoOf h₀) m₀ (c + 1) := by
          intro c' hc'
          rcases Nat.lt_or_ge c' c with h | h
          · obtain ⟨o', ho', hna'⟩ := hpre c' h
            exact ⟨o', hext o _ _ ho', hna'⟩
          · have : c' = c := by omega
            subst this; exact ⟨o, QueryCache.cacheQuery_self _ _ _, hna⟩
        have hih := ih (c + 1) (by omega) (n + 1) pc _ hn (settledEx_ext (hext o) hse) hpre'
        refine ⟨le_trans hih.1 (le_of_eq ?_), hih.2⟩
        have hh : ∀ i, hits rc (rhoOf h₀) m₀ (c + 1) i = hits rc (rhoOf h₀) m₀ c i :=
          fun i => hits_succ_eq rc _ m₀ c i (by simp [hk, admAt])
        unfold mid
        simp only [cntEx_ext (hext o) hse, pend_insert_own pc rc hn _ hcl, hits_insert_succ rc _ m₀ hcl, hh]
      have hstop : ∀ o, WCT9.producerAdmissible o = true →
          pot q r (n + 1) (pc, rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o) =
            if n + 1 ≤ q then ∑ i, G 51 (cntEx (pc, rc) m₀ i) r (pend (pc, rc) i) (q - (n + 1)) +
              G 50 (cntEx (pc, rc) m₀ (idxF o)) r (pend (pc, rc) (idxF o)) (q - (n + 1)) else 0 := by
        intro o ha
        have hw := walk_stop (rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o) (rhoOf h₀) m₀ hcl
          (fun c' hc' => by obtain ⟨o', ho', hna'⟩ := hpre c' hc'; exact ⟨o', hext o _ _ ho', hna'⟩)
          (QueryCache.cacheQuery_self _ _ _) ha
        rw [pot_stop q r (n + 1) _ m₀ _ (honestIdx_of_walk hn hw)]
        simp only [cntEx_ext (hext o) hse, pend_insert_own pc rc hn _ hcl]
      refine ⟨?_, ?_⟩
      · refine le_trans ?_ (mid_mono_n q r m₀ _ c n _)
        refine le_trans (expectedValue_mono _ (g := fun o => _)
          (h := fun o => if WCT9.producerAdmissible o = true then
            (if n + 1 ≤ q then ∑ i, G 51 (cntEx (pc, rc) m₀ i) r (pend (pc, rc) i) (q - (n + 1)) +
              G 50 (cntEx (pc, rc) m₀ (idxF o)) r (pend (pc, rc) (idxF o)) (q - (n + 1)) else 0)
            else mid q r m₀ (rhoOf h₀) c (n + 1) (pc, rc)) fun o => ?_) ?_
        · by_cases ha : WCT9.producerAdmissible o = true
          · simp only [ha, if_true, CountedPrivate.run_pure, expectedValue_pure]
            exact le_of_eq (hstop o ha)
          · have hna : WCT9.producerAdmissible o = false := by simpa using ha
            simp only [hna, Bool.false_eq_true, if_false]
            exact (hcont o hna).1
        · change expectedValue ($ᵗ HashOutput : ProbComp HashOutput) _ ≤ _
          refine expect_adm_le (fun j => if n + 1 ≤ q then
            ∑ i, G 51 (cntEx (pc, rc) m₀ i) r (pend (pc, rc) i) (q - (n + 1)) +
              G 50 (cntEx (pc, rc) m₀ j) r (pend (pc, rc) j) (q - (n + 1)) else 0) _ _ ?_ le_rfl
          unfold mid
          split_ifs with hq
          · simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_pIdx, one_mul]
            refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => mul_le_mul' le_self_add le_rfl)
          · simp
      · rintro res ⟨o, _, hres⟩
        by_cases ha : WCT9.producerAdmissible o = true
        · simp only [ha, if_true, CountedPrivate.run_pure, support_pure, Set.mem_singleton_iff] at hres
          subst hres
          have hw := walk_stop (rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o) (rhoOf h₀) m₀ hcl
            (fun c' hc' => by obtain ⟨o', ho', hna'⟩ := hpre c' hc'; exact ⟨o', hext o _ _ ho', hna'⟩)
            (QueryCache.cacheQuery_self _ _ _) ha
          exact settled_of_ex hn (settledEx_ext (hext o) hse) (by rw [hw]; simp)
        · have hna : WCT9.producerAdmissible o = false := by simpa using ha
          simp only [hna, Bool.false_eq_true, if_false] at hres
          exact (hcont o hna).2 res hres

/-! ### Drawing a fresh nonce -/

/-- The nonce of a fresh private value is uniform on `Digest`. -/
theorem expect_rho (f : Digest → ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun h => f (rhoOf h)) = pNonce * ∑ rho, f rho := by
  have h1 : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun h => f (rhoOf h)) =
      expectedValue ((fun output => BitVec.extractLsb' 0 128 output) <$> ($ᵗ SphincsSecurity.HashOutput)) f := by
    rw [expectedValue_map]; rfl
  have hlaw := SphincsSecurity.evalDist_hashOutput_extract_uniform (width := 128) (by decide)
  have hp : ∀ x, Pr[= x | (fun output => BitVec.extractLsb' 0 128 output) <$> ($ᵗ SphincsSecurity.HashOutput)] =
      Pr[= x | ($ᵗ BitVec 128 : ProbComp (BitVec 128))] := fun x => by rw [probOutput_def, probOutput_def, hlaw]
  rw [h1]
  unfold expectedValue
  simp only [hp]
  rw [tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _
  rw [probOutput_uniformSample, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat, pNonce]

theorem nonceCoord_injective {m m' : Message} (h : nonceCoord m = nonceCoord m') : m = m' := by
  unfold nonceCoord at h
  exact Sum.inl.inj (Sum.inr.inj h)

theorem sum_pNonce_const (x : ℝ≥0∞) : pNonce * ∑ _rho : Digest, x = x := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_bitVec, nsmul_eq_mul, ← mul_assoc, pNonce, Nat.cast_pow,
    Nat.cast_ofNat, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]

/-- Drawing the nonce of a fresh message consumes one signing slot and the message's pending entries. -/
theorem nonce_fresh_step (q r : ℕ) (m₀ : Message) (n : ℕ) (pc : LazyPrivate.PCache) (rc : Sampling.RCache)
    (hfresh : (pc (nonceCoord m₀) : Option HashOutput) = none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun h => mid q r m₀ (rhoOf h) 0 (n + 1) (pc.cacheQuery (nonceCoord m₀) h, rc)) ≤ pot q (r + 1) n (pc, rc) := by
  set S := Finset.univ.filter fun m : Message => (pc (nonceCoord m) : Option HashOutput) = none with hS
  set A' : Fin (2 ^ 31) → ℕ := fun i => ∑ m ∈ S.erase m₀, ∑ rho : Digest, hits rc rho m 0 i with hA'
  set D : Fin (2 ^ 31) → ℕ := fun i => ∑ rho : Digest, hits rc rho m₀ 0 i with hD
  have hsame : ∀ h m, m ≠ m₀ → ((pc.cacheQuery (nonceCoord m₀) h) (nonceCoord m) : Option HashOutput) =
      pc (nonceCoord m) := fun h m hm => QueryCache.cacheQuery_of_ne _ _ fun he => hm (nonceCoord_injective he)
  have hidx0 : honestIdx (pc, rc) m₀ = none := by unfold honestIdx; dsimp only; rw [hfresh]
  have hcnt : ∀ h i, cntEx (pc.cacheQuery (nonceCoord m₀) h, rc) m₀ i = cnt (pc, rc) i := by
    intro h i
    rw [cnt_split (pc, rc) m₀ i, hidx0]
    simp only [reduceCtorEq, if_false, add_zero]
    unfold cntEx
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro m _
    constructor
    · rintro ⟨hm, hh⟩
      refine ⟨hm, ?_⟩
      rw [← hh]; unfold honestIdx; dsimp only; rw [hsame h m hm]
    · rintro ⟨hm, hh⟩
      refine ⟨hm, ?_⟩
      rw [← hh]; unfold honestIdx; dsimp only; rw [hsame h m hm]
  have hpend : ∀ h i, pend (pc.cacheQuery (nonceCoord m₀) h, rc) i = A' i := by
    intro h i
    unfold pend
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hS]
    by_cases hm : m = m₀
    · subst hm; simp [QueryCache.cacheQuery_self]
    · simp [hm, hsame h m hm]
  have hpend0 : ∀ i, pend (pc, rc) i = A' i + D i := by
    intro i
    unfold pend
    rw [← Finset.sum_erase_add _ _ (show m₀ ∈ S by simp [hS, hfresh])]
  obtain ⟨F, hF⟩ : ∃ F : Digest → ℝ≥0∞, F = fun rho => if n + 1 ≤ q then ∑ i, (G 51 (cnt (pc, rc) i) r (A' i)
      (q - (n + 1)) + (pIdx + hits rc rho m₀ 0 i) * G 50 (cnt (pc, rc) i) r (A' i) (q - (n + 1))) else 0 := ⟨_, rfl⟩
  have hmid : (fun h => mid q r m₀ (rhoOf h) 0 (n + 1) (pc.cacheQuery (nonceCoord m₀) h, rc)) =
      fun h => F (rhoOf h) := by
    funext h
    rw [hF]
    unfold mid
    simp only [hcnt h, hpend h]
  rw [hmid, expect_rho, hF]
  by_cases hq : n + 1 ≤ q
  · simp only [hq, if_true]
    rw [Finset.sum_comm, Finset.mul_sum]
    unfold pot
    rw [if_pos (by omega)]
    apply Finset.sum_le_sum
    intro i _
    simp only [Finset.sum_add_distrib, add_mul, mul_add, sum_pNonce_const]
    calc G 51 (cnt (pc, rc) i) r (A' i) (q - (n + 1)) + (pIdx * G 50 (cnt (pc, rc) i) r (A' i) (q - (n + 1)) +
          pNonce * ∑ rho : Digest, (hits rc rho m₀ 0 i : ℝ≥0∞) * G 50 (cnt (pc, rc) i) r (A' i) (q - (n + 1)))
        = G 51 (cnt (pc, rc) i) r (A' i) (q - (n + 1)) +
            (pIdx + (D i : ℝ≥0∞) * pNonce) * G 50 (cnt (pc, rc) i) r (A' i) (q - (n + 1)) := by
          rw [← Finset.sum_mul, hD]; push_cast; ring
      _ ≤ G 51 (cnt (pc, rc) i) (r + 1) (A' i + D i) (q - (n + 1)) := G_slot 50 _ r _ _ _
      _ ≤ G 51 (cnt (pc, rc) i) (r + 1) (pend (pc, rc) i) (q - n) := by
          rw [hpend0 i]; exact G_mono le_rfl le_rfl le_rfl (by omega)
  · simp only [hq, if_false, Finset.sum_const_zero, mul_zero]
    exact bot_le

/-! ### One signing request -/

/-- The signer after its digest search. -/
def payloadCont (cache : SigGolfCandidate.T3.Cache) (rho : Digest) :
    Option (BitVec 32 × HashOutput) → M (Option ClaudeWCT.W9.T3.Security.Signature)
  | some (_, output) => do
      let forest ← WCT9.signForest (WCT9.digestIndex output) output
      let some pieces ← WCT9.signLayersBC cache (WCT9.digestIndex output) 4 (.forest forest.2) | pure none
      pure (some (WCT9.assembledSignature rho forest.1 pieces))
  | none => pure none

theorem payloadForNonce_eq (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (m : Message) :
    ClaudeWCT.W9.T3.Security.BPB.payloadForNonce cache rho m =
      WCT9.digestSearch rho m 0 lim >>= payloadCont cache rho := by
  unfold ClaudeWCT.W9.T3.Security.BPB.payloadForNonce
  congr 1
  funext found
  rcases found with _ | ⟨_, output⟩ <;> rfl

theorem notNonce_public (input : HashInput) : NotNonce (.inl (.inr input)) := fun _ h => by cases h

theorem notNonce_pair (tweak : BitVec 128) : NotNonce (.inr (.inl tweak)) := fun _ h => by
  simp [nonceCoord] at h

theorem payloadCont_notNonce (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (found : Option (BitVec 32 × HashOutput)) :
    AllQueriesSatisfy (payloadCont cache rho found) NotNonce := by
  rcases found with _ | ⟨_, output⟩
  · exact allQueriesSatisfy_pure _ _
  · simp only [payloadCont]
    apply SourceQueries.bind_allowed NotNonce
    · unfold WCT9.signForest WCT9.forestRows
      apply SourceQueries.bind_allowed NotNonce
      · apply SourceQueries.foldlM_allowed NotNonce
        intro state coord
        unfold WCT9.openingStep
        refine SourceQueries.bind_allowed NotNonce (ClaudeWCT.W9.T3.Security.Signer.buildCoordinateF_allowed NotNonce
          notNonce_public (fun _ _ _ _ => notNonce_pair _) _ _ _ _) fun x => ?_
        rcases x with ⟨levels, values⟩
        exact SourceQueries.pure_allowed _ _
      · intro state
        exact SourceQueries.bind_allowed NotNonce (ClaudeWCT.W9.T3.Security.Signer.forestPk_allowed NotNonce
          notNonce_public _ _) fun _ => SourceQueries.pure_allowed _ _
    · intro forest
      refine SourceQueries.bind_allowed NotNonce (ClaudeWCT.W9.T3.Security.Signer.signLayersBC_allowed NotNonce
        notNonce_public cache
        (ClaudeWCT.W9.T3.Security.Signer.buildTreeP_allowed NotNonce notNonce_public (fun _ _ _ => notNonce_pair _))
        (fun leaf digits => notNonce_of_avoids _ fun m => NonceFreshness.avoids_signTop m cache leaf digits) _ _ _)
        fun x => ?_
      rcases x with _ | pieces <;> exact SourceQueries.pure_allowed _ _

theorem payloadForNonce_notNonce (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (m : Message) :
    AllQueriesSatisfy (ClaudeWCT.W9.T3.Security.BPB.payloadForNonce cache rho m) NotNonce := by
  rw [payloadForNonce_eq]
  exact SourceQueries.bind_allowed _ (ClaudeWCT.W9.T3.Security.Signer.digestSearch_allowed _ notNonce_public _ _ _ _)
    (payloadCont_notNonce cache rho)

/-- Signing one message uses at most one signing slot. -/
theorem payload_step (q r : ℕ) (cache : SigGolfCandidate.T3.Cache) (m : Message) (n : ℕ) (s : LazyPrivate.State)
    (hs : Settled s) :
    expectedValue (CountedPrivate.run (WCT9.Rev3.signPayload cache m) (n, s)) (fun res => pot q r res.2.1 res.2.2) ≤
        pot q (r + 1) n s ∧
      ∀ res ∈ support (CountedPrivate.run (WCT9.Rev3.signPayload cache m) (n, s)), Settled res.2.2 := by
  rcases s with ⟨pc, rc⟩
  rw [ClaudeWCT.W9.T3.Security.BPB.signPayload_nonce,
    show privateNonce m = (liftM (SigGolfCandidate.T3.Spec.query (.inr (nonceCoord m))) >>= fun h =>
      pure (rhoOf h)) from rfl, bind_assoc]
  simp only [pure_bind]
  rw [CountedPrivate.run_bind, run_query_private, bind_map_left, randomOracle.run_eq]
  split
  next h hk =>
    simp only [pure_bind]
    have := prog_step q r _ (payloadForNonce_notNonce cache (rhoOf h) m) (n + 1) (pc, rc) hs
    exact ⟨this.1.trans ((pot_mono_n q r n _).trans (pot_mono_r q r n _)), this.2⟩
  next hk =>
    simp only [bind_assoc, pure_bind, expectedValue_bind, mem_support_bind_iff]
    have hk' : (pc (nonceCoord m) : Option HashOutput) = none := hk
    have hstep : ∀ h : HashOutput, expectedValue (CountedPrivate.run
        (ClaudeWCT.W9.T3.Security.BPB.payloadForNonce cache (rhoOf h) m) (n + 1, (pc.cacheQuery (nonceCoord m) h, rc)))
          (fun res => pot q r res.2.1 res.2.2) ≤ mid q r m (rhoOf h) 0 (n + 1) (pc.cacheQuery (nonceCoord m) h, rc) ∧
        ∀ res ∈ support (CountedPrivate.run (ClaudeWCT.W9.T3.Security.BPB.payloadForNonce cache (rhoOf h) m)
          (n + 1, (pc.cacheQuery (nonceCoord m) h, rc))), Settled res.2.2 := by
      intro h
      have hex : SettledEx (pc.cacheQuery (nonceCoord m) h, rc) m := by
        intro m' h' hm' hh
        have : ((pc.cacheQuery (nonceCoord m) h) (nonceCoord m') : Option HashOutput) = pc (nonceCoord m') :=
          QueryCache.cacheQuery_of_ne _ _ fun he => hm' (nonceCoord_injective he)
        have hh' : (pc (nonceCoord m') : Option HashOutput) = some h' := by rw [← this]; exact hh
        exact hs m' h' hh'
      have hsr := search_step q r m h lim 0 (by simp) (n + 1) (pc.cacheQuery (nonceCoord m) h) rc
        (QueryCache.cacheQuery_self _ _ _) hex (fun c' hc' => absurd hc' (Nat.not_lt_zero _))
      rw [payloadForNonce_eq, CountedPrivate.run_bind]
      refine ⟨?_, ?_⟩
      · rw [expectedValue_bind]
        exact le_trans (expectedValue_mono_of_support fun res hres =>
          (prog_step q r _ (payloadCont_notNonce cache _ res.1) res.2.1 res.2.2 (hsr.2 res hres)).1) hsr.1
      · intro res hres
        rw [mem_support_bind_iff] at hres
        obtain ⟨mid', hmid', hres⟩ := hres
        exact (prog_step q r _ (payloadCont_notNonce cache _ mid'.1) mid'.2.1 mid'.2.2 (hsr.2 mid' hmid')).2 res hres
    refine ⟨?_, ?_⟩
    · change expectedValue ($ᵗ HashOutput : ProbComp HashOutput) _ ≤ _
      exact le_trans (expectedValue_mono _ fun h => (hstep h).1) (nonce_fresh_step q r m n pc rc hk')
    · rintro res ⟨h, _, hres⟩
      exact (hstep h).2 res hres

/-- A signing request (authenticated W9 signer) uses at most one signing slot. -/
theorem sign_step (q r : ℕ) (published : SigGolfCandidate.T3.Cache) (request : Request) (n : ℕ)
    (s : LazyPrivate.State) (hs : Settled s) :
    expectedValue (CountedPrivate.run (ClaudeWCT.W9.T3.Security.FullGame.authenticatedSign published request) (n, s))
        (fun res => pot q r res.2.1 res.2.2) ≤ pot q (r + 1) n s ∧
      ∀ res ∈ support (CountedPrivate.run (ClaudeWCT.W9.T3.Security.FullGame.authenticatedSign published request)
        (n, s)), Settled res.2.2 := by
  unfold ClaudeWCT.W9.T3.Security.FullGame.authenticatedSign
  rw [CountedPrivate.run_bind]
  have hmac := prog_step q (r + 1) _ (notNonce_of_avoids _ fun m =>
    NonceFreshness.avoids_privateMac m request.cache.region) n s hs
  refine ⟨?_, ?_⟩
  · rw [expectedValue_bind]
    refine le_trans (expectedValue_mono_of_support fun res hres => ?_) hmac.1
    have hs' := hmac.2 res hres
    rcases Classical.em (request.cache = published) with hc | hc
    · rw [if_pos hc]; exact (payload_step q r _ _ res.2.1 res.2.2 hs').1
    · rw [if_neg hc]
      simp only [CountedPrivate.run_pure, expectedValue_pure]
      exact pot_mono_r q r _ _
  · intro res' hres'
    rw [mem_support_bind_iff] at hres'
    obtain ⟨res, hres, hres'⟩ := hres'
    have hs' := hmac.2 res hres
    rcases Classical.em (request.cache = published) with hc | hc
    · rw [if_pos hc] at hres'; exact (payload_step q r _ _ res.2.1 res.2.2 hs').2 res' hres'
    · rw [if_neg hc] at hres'
      simp only [CountedPrivate.run_pure, support_pure, Set.mem_singleton_iff] at hres'
      subst hres'; exact hs'

/-! ### The adversary's interaction -/

/-- The potential after `len` of the `r` signing slots were used. -/
noncomputable def potL (q r len n : ℕ) (s : LazyPrivate.State) : ℝ≥0∞ :=
  if len ≤ r then pot q (r - len) n s else 0

theorem handler_run (x : SigGolfCandidate.T3.Spec.Domain) (st : CountedPrivate.State) :
    (CountedPrivate.handler x).run st = CountedPrivate.run (liftM (SigGolfCandidate.T3.Spec.query x)) st := rfl

/-- The whole interaction: each signing request uses one of `r` slots (the log records it). -/
theorem interaction_step {α : Type} (q : ℕ) (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp ClaudeWCT.W9.T3.Security.LazyPrivate.Interaction α) :
    ∀ (r n : ℕ) (s : LazyPrivate.State), Settled s →
      expectedValue (ClaudeWCT.W9.T3.Security.RequestHop.run (fun input => CountedPrivate.handler (.inl input))
          (fun request => simulateQ CountedPrivate.handler
            (ClaudeWCT.W9.T3.Security.FullGame.authenticatedSign published request)) program (n, s))
        (fun res => potL q r res.1.2.length res.2.1 res.2.2) ≤ pot q r n s ∧
      ∀ res ∈ support (ClaudeWCT.W9.T3.Security.RequestHop.run (fun input => CountedPrivate.handler (.inl input))
          (fun request => simulateQ CountedPrivate.handler
            (ClaudeWCT.W9.T3.Security.FullGame.authenticatedSign published request)) program (n, s)),
        Settled res.2.2 := by
  induction program using OracleComp.inductionOn with
  | pure a =>
    intro r n s hs
    rw [ClaudeWCT.W9.T3.Security.RequestHop.run_pure]
    simp only [expectedValue_pure, support_pure, Set.mem_singleton_iff, forall_eq, potL, List.length_nil,
      Nat.zero_le, if_true, Nat.sub_zero]
    exact ⟨le_rfl, hs⟩
  | query_bind x next ih =>
    intro r n s hs
    rcases x with input | request
    · rw [ClaudeWCT.W9.T3.Security.RequestHop.run_public, handler_run]
      have hq := query_step q r (.inl input) (fun m h => by cases h) n s hs
      refine ⟨?_, ?_⟩
      · rw [expectedValue_bind]
        exact le_trans (expectedValue_mono_of_support fun res hres =>
          (ih res.1 r res.2.1 res.2.2 (hq.2 res hres)).1) hq.1
      · intro res hres
        rw [mem_support_bind_iff] at hres
        obtain ⟨mid', hmid', hres⟩ := hres
        exact (ih mid'.1 r mid'.2.1 mid'.2.2 (hq.2 mid' hmid')).2 res hres
    · rw [ClaudeWCT.W9.T3.Security.RequestHop.run_request, CountedPrivate.run_simulate]
      refine ⟨?_, fun res hres => ?_⟩
      swap
      · rw [mem_support_bind_iff] at hres
        obtain ⟨mid', hmid', hres⟩ := hres
        rw [support_map] at hres
        obtain ⟨tail, htail, rfl⟩ := hres
        exact (ih mid'.1 r mid'.2.1 mid'.2.2 ((sign_step q r published request n s hs).2 mid' hmid')).2 tail htail
      rcases r with _ | r
      · have h0 : ∀ res : (α × QueryLog ClaudeWCT.W9.T3.Security.Requests) × CountedPrivate.State,
            potL q 0 (res.1.2.length + 1) res.2.1 res.2.2 = 0 := fun res => by
          simp [potL]
        rw [expectedValue_bind]
        simp only [expectedValue_map, List.length_cons, h0]
        exact le_trans (expectedValue_le_of_support fun _ _ => (expectedValue_le_of_support fun _ _ => le_rfl)) bot_le
      · have hsign := sign_step q r published request n s hs
        rw [expectedValue_bind]
        simp only [expectedValue_map, List.length_cons]
        refine le_trans (expectedValue_mono_of_support fun res hres => ?_) hsign.1
        have hih := (ih res.1 r res.2.1 res.2.2 (hsign.2 res hres)).1
        refine le_of_eq_of_le ?_ hih
        congr 1
        funext tail
        simp only [potL, Nat.add_le_add_iff_right, Nat.add_sub_add_right]

/-! ### The experiment -/

theorem allQ_mono' {α : Type} {P Q : SigGolfCandidate.T3.Spec.Domain → Prop} (h : ∀ x, P x → Q x) (p : M α)
    (hp : AllQueriesSatisfy p P) : AllQueriesSatisfy p Q := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind x next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hp ⊢
    exact ⟨h x hp.1, fun u => ih u (hp.2 u)⟩

theorem keygen_notNonce : AllQueriesSatisfy SigGolfCandidate.T3.keygen NotNonce :=
  notNonce_of_avoids _ fun m => SigGolfCandidate.T3.Security.NonceFreshness.avoids_keygen m

theorem verdict_notNonce (pk : Digest) (result : Option ClaudeWCT.W9.T3M.Final.ForgeryP ×
    QueryLog ClaudeWCT.W9.T3.Security.Requests) :
    AllQueriesSatisfy (ClaudeWCT.W9.T3.Security.GameWith.verdict ClaudeWCT.W9.T3.Security.PaddedGame.checker pk result)
      NotNonce :=
  allQ_mono' (fun x hx m he => by subst he; exact hx) _ (ClaudeWCT.W9.T3.Security.PaddedGame.verdict_public pk result)

theorem verdict_win_len {Forgery : Type} (checker : ClaudeWCT.W9.T3.Security.GameWith.Checker Forgery) (pk : Digest)
    (result : Option Forgery × QueryLog ClaudeWCT.W9.T3.Security.Requests) (st : CountedPrivate.State)
    (res : Bool × CountedPrivate.State)
    (hres : res ∈ support (CountedPrivate.run (ClaudeWCT.W9.T3.Security.GameWith.verdict checker pk result) st))
    (hwin : res.1 = true) : result.2.length ≤ 2 ^ 32 := by
  unfold ClaudeWCT.W9.T3.Security.GameWith.verdict at hres
  split at hres
  · rw [CountedPrivate.run_bind, mem_support_bind_iff] at hres
    obtain ⟨mid', _, hres⟩ := hres
    rw [CountedPrivate.run_pure, support_pure, Set.mem_singleton_iff] at hres
    subst hres
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
    exact hwin.1
  · rw [CountedPrivate.run_pure, support_pure, Set.mem_singleton_iff] at hres
    subst hres
    cases hwin

theorem settled_empty : Settled (∅, ∅) := fun m h hh => by cases hh

theorem pot_empty_le (q : ℕ) (hq : q ≤ 2 ^ 127) : pot q (2 ^ 32) 0 (∅, ∅) ≤ overflowConst := by
  have hcnt : ∀ i, cnt (∅, ∅) i = 0 := by
    intro i
    unfold cnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _ h
    unfold honestIdx at h
    cases h
  have hpend : ∀ i, pend (∅, ∅) i = 0 := by
    intro i
    unfold pend hits
    apply Finset.sum_eq_zero
    intro m _
    apply Finset.sum_eq_zero
    intro rho _
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ h
    cases h.2
  unfold pot overflowConst
  rw [if_pos (Nat.zero_le _)]
  simp only [hcnt, hpend, Nat.sub_zero]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_le_mul' le_rfl (G_mono le_rfl le_rfl le_rfl hq)

theorem one_le_pot {q r n : ℕ} {s : LazyPrivate.State} (hn : n ≤ q) (ho : Overflow s) : 1 ≤ pot q r n s := by
  obtain ⟨j, hj⟩ := ho
  unfold pot
  rw [if_pos hn]
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => G 51 (cnt s i) r (pend s i) (q - n))
    (fun _ _ => bot_le) (Finset.mem_univ j))
  refine le_trans ?_ (choose_le_G 51 (cnt s j) r (pend s j) (q - n))
  exact_mod_cast Nat.choose_pos hj

/-- The overflow bound in the counted lazy game. -/
theorem counted_overflow_le (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127) :
    Pr[fun res => res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 |
      ClaudeWCT.W9.T3.Security.GameWith.Counted.experiment ClaudeWCT.W9.T3.Security.PaddedGame.checker adversary] ≤
      overflowConst := by
  classical
  unfold ClaudeWCT.W9.T3.Security.GameWith.Counted.experiment ClaudeWCT.W9.T3.Security.GameWith.idealGame
  rw [← expectedValue_ite_one]
  refine le_trans ?_ (pot_empty_le q hq)
  have hkg := prog_step q (2 ^ 32) _ keygen_notNonce 0 (∅, ∅) settled_empty
  rw [CountedPrivate.run_bind, expectedValue_bind]
  refine le_trans (expectedValue_mono_of_support fun kg hkg' => ?_) hkg.1
  have hs := hkg.2 kg hkg'
  rw [CountedPrivate.run_bind, expectedValue_bind, ← CountedPrivate.run_simulate,
    ClaudeWCT.W9.T3.Security.FullGame.loggedWith_interpretation]
  have hint := interaction_step q kg.1.2 (adversary kg.1.1 kg.1.2) (2 ^ 32) kg.2.1 kg.2.2 hs
  refine le_trans (expectedValue_mono_of_support fun ir hir => ?_) hint.1
  have hset := hint.2 ir hir
  by_cases hlen : ir.1.2.length ≤ 2 ^ 32
  · rw [potL, if_pos hlen]
    refine le_trans (expectedValue_mono _ fun res => ?_)
      (prog_step q (2 ^ 32 - ir.1.2.length) _ (verdict_notNonce _ _) ir.2.1 ir.2.2 hset).1
    split_ifs with hE
    · exact one_le_pot hE.2.1 hE.2.2
    · exact bot_le
  · apply expectedValue_le_of_support
    intro res hres
    rw [if_neg]
    · exact bot_le
    · intro hE
      exact hlen (verdict_win_len _ _ _ _ _ hres hE.1)

/-! ### The closings' experiments -/

theorem pmf_mono {α : Type} (p : PMF α) {F G : α → Prop} (h : ∀ x, F x → G x) : Pr[F | p] ≤ Pr[G | p] := by
  classical
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hF : F x
  · simp [hF, h x hF]
  · simp [hF]

theorem traced_counted (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127) :
    (fun z : ClaudeWCT.W9.T3.Security.PaddedGame.TraceResult => (z.1, z.2.2.base.source)) <$>
        ClaudeWCT.W9.T3.Security.PaddedGame.tracedExperiment adversary q hq =
      (liftM (ClaudeWCT.W9.T3.Security.GameWith.Counted.experiment ClaudeWCT.W9.T3.Security.PaddedGame.checker
        adversary) : PMF _) := by
  unfold ClaudeWCT.W9.T3.Security.PaddedGame.tracedExperiment
  rw [← ClaudeWCT.W9.T3.Security.GameWith.Monitored.experiment_erasure, liftM_map,
    ← ClaudeWCT.W9.T3.Security.GameWith.Monitored.tracedExperiment_erasure,
    ← ClaudeWCT.W9.T3.Security.GameWith.Recorded.traced_base_erasure]
  simp only [Functor.map_map]
  rfl

/-! ### Settledness of final states and the answers form -/

theorem counted_settled (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) :
    ∀ res ∈ support (ClaudeWCT.W9.T3.Security.GameWith.Counted.experiment
      ClaudeWCT.W9.T3.Security.PaddedGame.checker adversary), Settled res.2.2 := by
  intro res hres
  unfold ClaudeWCT.W9.T3.Security.GameWith.Counted.experiment ClaudeWCT.W9.T3.Security.GameWith.idealGame at hres
  rw [CountedPrivate.run_bind, mem_support_bind_iff] at hres
  obtain ⟨kg, hkg, hres⟩ := hres
  have hs := (prog_step 0 0 _ keygen_notNonce 0 (∅, ∅) settled_empty).2 kg hkg
  rw [CountedPrivate.run_bind, mem_support_bind_iff, ← CountedPrivate.run_simulate,
    ClaudeWCT.W9.T3.Security.FullGame.loggedWith_interpretation] at hres
  obtain ⟨ir, hir, hres⟩ := hres
  have hs' := (interaction_step 0 kg.1.2 (adversary kg.1.1 kg.1.2) 0 kg.2.1 kg.2.2 hs).2 ir hir
  exact (prog_step 0 0 _ (verdict_notNonce _ _) ir.2.1 ir.2.2 hs').2 res hres

theorem traced_settled (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127)
    (z : ClaudeWCT.W9.T3.Security.PaddedGame.TraceResult)
    (hz : z ∈ (ClaudeWCT.W9.T3.Security.PaddedGame.tracedExperiment adversary q hq).support) :
    Settled z.2.2.base.source.2 := by
  have hmem : (z.1, z.2.2.base.source) ∈ ((fun z : ClaudeWCT.W9.T3.Security.PaddedGame.TraceResult =>
      (z.1, z.2.2.base.source)) <$> ClaudeWCT.W9.T3.Security.PaddedGame.tracedExperiment adversary q hq).support := by
    rw [PMF.monad_map_eq_map, PMF.support_map]
    exact ⟨z, hz, rfl⟩
  rw [traced_counted adversary q hq, MonitoredPrivate.pmf_support] at hmem
  exact counted_settled adversary _ hmem

/-- The honest index of `m` computed from completed answers: first producer-admissible digest output under the
nonce `A(nonce m)`. -/
def answerIdx (A : Correctness.Answers) (m : Message) : Option (Fin (2 ^ 31)) :=
  (evalWithAnswerFn A (WCT9.digestSearch (rhoOf (A (.inr (nonceCoord m)))) m 0 lim)).map fun p => idxF p.2

theorem eval_digestSearch_walk (A : Correctness.Answers) (rc : Sampling.RCache)
    (hA : ∀ k o, rc k = some o → A (.inl (.inr k)) = o) (rho : Digest) (m : Message) :
    ∀ f c w, walk rc rho m c f = some w →
      (evalWithAnswerFn A (WCT9.digestSearch rho m c f)).map Prod.snd = w := by
  intro f
  induction f with
  | zero => intro c w h; simp only [walk, Option.some.injEq] at h; subst h; rfl
  | succ f ih =>
    intro c w h
    rw [digestSearch_succ_eq, evalWithAnswerFn_bind]
    simp only [walk] at h
    cases hk : rc (digestKey rho m c) with
    | none => rw [hk] at h; cases h
    | some o =>
      rw [hk] at h
      simp only at h
      have ho : (evalWithAnswerFn A (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr (digestKey rho m c))))) :
          HashOutput) = o := by
        rw [← hA _ _ hk]; rfl
      simp only [ho]
      split_ifs at h ⊢ with ha
      · cases h; rfl
      · exact ih (c + 1) w h

theorem honestIdx_eq_answerIdx (A : Correctness.Answers) (s : LazyPrivate.State)
    (hA : ∀ input answer, SourceReplay.known s input = some answer → A input = answer) (hs : Settled s)
    (m : Message) (hm : (s.1 (nonceCoord m) : Option HashOutput) ≠ none) :
    honestIdx s m = answerIdx A m := by
  obtain ⟨h, hh⟩ := Option.ne_none_iff_exists'.mp hm
  have hAn : A (.inr (nonceCoord m)) = h := hA (.inr (nonceCoord m)) h hh
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp (hs m h hh)
  have he := eval_digestSearch_walk A s.2 (fun k o hk => hA (.inl (.inr k)) o hk) (rhoOf h) m lim 0 w hw
  unfold honestIdx answerIdx
  rw [hh]
  dsimp only
  rw [hw, hAn]
  cases w with
  | none =>
    simp only
    cases he' : evalWithAnswerFn A (WCT9.digestSearch (rhoOf h) m 0 lim) with
    | none => rfl
    | some p => rw [he'] at he; cases he
  | some o =>
    simp only
    cases he' : evalWithAnswerFn A (WCT9.digestSearch (rhoOf h) m 0 lim) with
    | none => rw [he'] at he; cases he
    | some p => rw [he'] at he; simp only [Option.map_some, Option.some.injEq] at he; rw [Option.map_some, he]

end ClaudeWCT.W9.T3.Security.FtsOverflow

namespace ClaudeWCT.W9.T3.Security
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security.FtsOverflow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- **FTS overflow event** of a traced run: some digest index is the honest index of ≥ 51 distinct signed messages,
read from the final lazy state (`FtsOverflow.honestIdx`: nonce from the private table, first producer-admissible
digest output from the public cache). On the support of `SeccLaw.completedExperiment` the cached values agree
with the completed answers (`SeccLaw.completed_agrees`). -/
def FtsOverflow (z : PaddedGame.TraceResult) : Prop := FtsOverflow.Overflow z.2.2.base.source.2

/-- **FTS overflow bound** in the traced experiment of the closings. -/
theorem traced_ftsOverflow_le (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z ∧ FtsOverflow z | PaddedGame.tracedExperiment adversary q hq] ≤
      overflowConst := by
  classical
  calc Pr[fun z => QueryRecorded.CleanWin q z ∧ FtsOverflow z | PaddedGame.tracedExperiment adversary q hq]
      ≤ Pr[fun z : PaddedGame.TraceResult =>
          (z.1, z.2.2.base.source).1 = true ∧ (z.1, z.2.2.base.source).2.1 ≤ q ∧
            Overflow (z.1, z.2.2.base.source).2.2 | PaddedGame.tracedExperiment adversary q hq] :=
        pmf_mono _ fun z hz => ⟨hz.1.1, hz.1.2.1, hz.2⟩
    _ = Pr[fun res => res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 |
          (liftM (GameWith.Counted.experiment PaddedGame.checker adversary) : PMF _)] := by
        rw [← traced_counted adversary q hq, probEvent_map]
        rfl
    _ = Pr[fun res => res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 |
          GameWith.Counted.experiment PaddedGame.checker adversary] := by
        simp only [probEvent_eq_tsum_ite]
        rfl
    _ ≤ overflowConst := counted_overflow_le adversary q hq

/-- **FTS overflow bound** in `SeccLaw.completedExperiment` (the hook of `cleanWin_le_cases`, `small_route` and
`large_cert_bound`): at most `2^31 G(51; 2^32 signing slots, 2^127 queries) ≤ 2^31 (2 + 2^-32)^51 / 51! ≤ 2^-137`. -/
theorem fts_overflow_le (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ FtsOverflow z.1 | SeccLaw.completedExperiment adversary q hq] ≤
      (2 ^ 137)⁻¹ := by
  rw [SeccLaw.completed_trace_event adversary q hq (fun z => QueryRecorded.CleanWin q z ∧ FtsOverflow z)]
  exact (traced_ftsOverflow_le adversary q hq).trans overflowConst_le

/-- Answers form for the consumers: off the overflow event, in every completed run each digest index is the
honest index (computed from the completed answers) of at most 50 distinct signed messages (messages whose nonce
was drawn). -/
theorem ftsOverflow_answers (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hno : ¬FtsOverflow z.1) (i : Fin (2 ^ 31)) :
    (Finset.univ.filter fun m : Message =>
      (z.1.2.2.base.source.2.1 (nonceCoord m) : Option HashOutput) ≠ none ∧ answerIdx z.2 m = some i).card ≤ 50 := by
  obtain ⟨htr, hagree⟩ := SeccLaw.completed_agrees adversary q hq z hz
  have hs := traced_settled adversary q hq z.1 htr
  have hle : cnt z.1.2.2.base.source.2 i ≤ 50 := by
    by_contra h
    exact hno ⟨i, by omega⟩
  refine le_trans (le_of_eq ?_) hle
  unfold cnt
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro m _
  constructor
  · rintro ⟨hm, hi⟩
    rw [honestIdx_eq_answerIdx z.2 _ hagree hs m hm]
    exact hi
  · intro hi
    have hm : (z.1.2.2.base.source.2.1 (nonceCoord m) : Option HashOutput) ≠ none := by
      intro hn
      unfold honestIdx at hi
      rw [hn] at hi
      cases hi
    exact ⟨hm, (honestIdx_eq_answerIdx z.2 _ hagree hs m hm) ▸ hi⟩

/-! ### Bridge to the interaction log (case C's `NoOverflow`) -/

/-- The log-level overflow guard of case C: no digest index carries ≥ 51 distinct honest signed outputs among the
logged signatures. -/
def LogNoOverflow (answers : Correctness.Answers) (log : QueryLog Requests) : Prop :=
  ∀ j : Fin (2 ^ 31),
    ((WPair.loggedOutputs answers log).toFinset.filter fun out => ClaudeWCT.Bank.WCT.outIdx out = j).card ≤ 50

/-- A signature that resolves on the lazy state was produced after drawing the nonce of its message. -/
theorem resolves_sign_nonce (s : LazyPrivate.State) (A : Correctness.Answers)
    (hA : ∀ input answer, SourceReplay.known s input = some answer → A input = answer)
    (published : SigGolfCandidate.T3.Cache) (request : Request) (σ : ClaudeWCT.W9.T3.Security.Signature)
    (hres : SourceReplay.Resolves s (ClaudeWCT.W9.T3.Security.FullGame.authenticatedSign published request)
      (some σ)) :
    (s.1 (nonceCoord request.message) : Option HashOutput) ≠ none ∧
      σ.rho = rhoOf (A (.inr (nonceCoord request.message))) := by
  classical
  have hrho : ∀ A' : Correctness.Answers,
      (∀ input answer, SourceReplay.known s input = some answer → A' input = answer) →
        σ.rho = rhoOf (A' (.inr (nonceCoord request.message))) := by
    intro A' hA'
    have he := hres.eval A' hA'
    exact (BPB.authenticatedSign_payload A' published request σ he).2.1
  refine ⟨fun hnone => ?_, hrho A hA⟩
  let h' : HashOutput := if σ.rho = 0 then 1 else 0
  have hne : rhoOf h' ≠ σ.rho := by
    by_cases h0 : σ.rho = 0
    · simp only [h', h0, if_true]; decide
    · simp only [h', h0, if_false]; exact fun h => h0 (h.symm.trans (by decide))
  let A' : Correctness.Answers := Function.update A (.inr (nonceCoord request.message)) h'
  have hA' : ∀ input answer, SourceReplay.known s input = some answer → A' input = answer := by
    intro input answer hk
    have hx : input ≠ .inr (nonceCoord request.message) := by
      rintro rfl
      simp only [SourceReplay.known] at hk
      rw [hnone] at hk
      cases hk
    simp only [A', Function.update_of_ne hx]
    exact hA input answer hk
  have := hrho A' hA'
  simp only [A', Function.update_self] at this
  exact hne this.symm

/-- Off the FTS overflow event, the interaction log of a completed run satisfies `LogNoOverflow`
(distinct honest signed outputs ≤ distinct signed messages ≤ 50 per index). -/
theorem logNoOverflow_of_not_ftsOverflow (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hno : ¬FtsOverflow z.1) (g : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache))
    (i : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.ForgeryP × QueryLog Requests)) (c : FirstHit.Recorded Bool)
    (hs : CaseC.GameSplit adversary (QueryRecorded.recordedTrace z.1) g i c) :
    LogNoOverflow z.2 i.value.2 := by
  classical
  intro j
  obtain ⟨-, hagree⟩ := SeccLaw.completed_agrees adversary q hq z hz
  have hstate : c.state = z.1.2.2.base.source.2 := (congrArg FirstHit.Recorded.state hs.2.2.2).symm
  have hirun := FirstHit.recorded_support _ _ _ hs.2.1
  have hcrun := FirstHit.recorded_support _ _ _ hs.2.2.1
  have hext : SourceReplay.Extends i.state c.state := SourceReplay.run_extends _ i.state _ hcrun
  have hagree' : ∀ input answer, SourceReplay.known c.state input = some answer → z.2 input = answer := by
    rw [hstate]; exact hagree
  -- every honest output of index j comes from a signed message counted by `ftsOverflow_answers`
  have hmsg : ∀ out ∈ (WPair.loggedOutputs z.2 i.value.2).toFinset.filter
      (fun out => ClaudeWCT.Bank.WCT.outIdx out = j), ∃ m : Message,
        (z.1.2.2.base.source.2.1 (nonceCoord m) : Option HashOutput) ≠ none ∧ answerIdx z.2 m = some j ∧
        (evalWithAnswerFn z.2 (WCT9.digestSearch (rhoOf (z.2 (.inr (nonceCoord m)))) m 0 lim)).map Prod.snd =
          some out := by
    intro out hout
    simp only [Finset.mem_filter, List.mem_toFinset] at hout
    obtain ⟨hmem, hidx⟩ := hout
    obtain ⟨entry, he, σ, hσ, hout⟩ := WPair.mem_loggedOutputs.mp hmem
    have hres := (BPB.logged_resolves g.value.2 (adversary g.value.1 g.value.2) g.state _ hirun entry he).mono hext
    rw [hσ] at hres
    obtain ⟨hn, hr⟩ := resolves_sign_nonce c.state z.2 hagree' g.value.2 entry.1 σ hres
    refine ⟨entry.1.message, by rw [← hstate]; exact hn, ?_, ?_⟩
    · unfold answerIdx
      have : (evalWithAnswerFn z.2 (WCT9.digestSearch (rhoOf (z.2 (.inr (nonceCoord entry.1.message))))
          entry.1.message 0 lim)).map Prod.snd = some out := by
        rw [← hr]; exact hout
      cases hx : evalWithAnswerFn z.2 (WCT9.digestSearch (rhoOf (z.2 (.inr (nonceCoord entry.1.message))))
          entry.1.message 0 lim) with
      | none => rw [hx] at this; cases this
      | some p =>
        rw [hx] at this
        simp only [Option.map_some, Option.some.injEq] at this ⊢
        rw [this]
        exact hidx
    · rw [← hr]; exact hout
  choose! f hf using hmsg
  have hcard := ftsOverflow_answers adversary q hq z hz hno j
  refine le_trans (Finset.card_le_card_of_injOn f ?_ ?_) hcard
  · intro out hout
    obtain ⟨h1, h2, _⟩ := hf out hout
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact ⟨h1, h2⟩
  · intro out hout out' hout' heq
    have e1 := (hf out hout).2.2
    have e2 := (hf out' hout').2.2
    rw [heq] at e1
    exact Option.some.inj (e1.symm.trans e2)

/-- Glue for case C: a clean win whose interaction log violates `LogNoOverflow` is an FTS overflow, so its
probability is at most `2^-137`. -/
theorem cleanWin_logOverflow_le (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬(∀ g i c, CaseC.GameSplit adversary (QueryRecorded.recordedTrace z.1)
        g i c → LogNoOverflow z.2 i.value.2) | SeccLaw.completedExperiment adversary q hq] ≤ (2 ^ 137)⁻¹ := by
  classical
  refine le_trans ?_ (fts_overflow_le adversary q hq)
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support
  · by_cases hE : QueryRecorded.CleanWin q z.1 ∧ ¬(∀ g i c, CaseC.GameSplit adversary
        (QueryRecorded.recordedTrace z.1) g i c → LogNoOverflow z.2 i.value.2)
    · have hF : QueryRecorded.CleanWin q z.1 ∧ FtsOverflow z.1 := by
        refine ⟨hE.1, by_contra fun hno => hE.2 fun g i c hs => ?_⟩
        exact logNoOverflow_of_not_ftsOverflow adversary q hq z hz hno g i c hs
      rw [if_pos hE, if_pos hF]
    · simp only [hE, if_false]; exact bot_le
  · have hz0 : (SeccLaw.completedExperiment adversary q hq) z = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hz
    simp only [PMF.probOutput_eq_apply, hz0, ite_self, le_refl]

end ClaudeWCT.W9.T3.Security
