import SigGolfCandidate.ClaudeWCT.Arith.GF128

/-!
# Limb-level facts for the sign machine's GF(2^128) Horner routine (campaign X1, stage A)

The routine keeps a 128-bit value in two 64-bit limbs and a product of up to 138 bits in three limbs. `lim2`/`lim3`
read limbs as a natural number. The lemmas relate one machine bit-step (conditional xor of the shifted multiplicand,
shift by one) to `clmulSmall`, the fold to `gfFold`, and the Horner step to `familyEval`.
-/

namespace ClaudeWCT.W9.Machine.Sign.Gf
open ClaudeWCT.Arith

/-- Two limbs as a number. -/
def lim2 (a b : BitVec 64) : Nat := a.toNat + 2 ^ 64 * b.toNat
/-- Three limbs as a number. -/
def lim3 (a b c : BitVec 64) : Nat := a.toNat + 2 ^ 64 * (b.toNat + 2 ^ 64 * c.toNat)

theorem xor_split {k x y x' y' : Nat} (hx : x < 2 ^ k) (hx' : x' < 2 ^ k) :
    (x + 2 ^ k * y) ^^^ (x' + 2 ^ k * y') = (x ^^^ x') + 2 ^ k * (y ^^^ y') := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.add_comm x, Nat.add_comm x', Nat.add_comm (x ^^^ x'),
    Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hx',
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hx hx')]
  split <;> simp [Nat.testBit_xor]

theorem lim2_xor (a b a' b' : BitVec 64) : lim2 (a ^^^ a') (b ^^^ b') = lim2 a b ^^^ lim2 a' b' := by
  unfold lim2
  rw [BitVec.toNat_xor, BitVec.toNat_xor, xor_split a.isLt a'.isLt]

theorem lim3_xor (a b c a' b' c' : BitVec 64) :
    lim3 (a ^^^ a') (b ^^^ b') (c ^^^ c') = lim3 a b c ^^^ lim3 a' b' c' := by
  unfold lim3
  rw [BitVec.toNat_xor, BitVec.toNat_xor, BitVec.toNat_xor, xor_split a.isLt a'.isLt,
    xor_split b.isLt b'.isLt]

theorem toNat_shl1_or (b a : BitVec 64) :
    ((b <<< 1) ||| (a >>> 63)).toNat = 2 * (b.toNat % 2 ^ 63) + a.toNat / 2 ^ 63 := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have ha := a.isLt
  have h1 : b.toNat * 2 ^ 1 % 2 ^ 64 = 2 ^ 1 * (b.toNat % 2 ^ 63) := by omega
  have h2 : a.toNat / 2 ^ 63 < 2 ^ 1 := by omega
  rw [h1, ← Nat.two_pow_add_eq_or_of_lt h2]

theorem toNat_shl1 (a : BitVec 64) : (a <<< 1).toNat = 2 * (a.toNat % 2 ^ 63) := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- One shift of the three-limb multiplicand. -/
theorem lim3_shl1 (a b c : BitVec 64) (hc : c.toNat < 2 ^ 63) :
    lim3 (a <<< 1) ((b <<< 1) ||| (a >>> 63)) ((c <<< 1) ||| (b >>> 63)) = 2 * lim3 a b c := by
  unfold lim3
  rw [toNat_shl1_or, toNat_shl1_or, toNat_shl1]
  have := a.isLt
  have := b.isLt
  omega

theorem lim3_lt (a b c : BitVec 64) {n : Nat} (h : lim3 a b c < 2 ^ (128 + n)) : c.toNat < 2 ^ n := by
  unfold lim3 at h
  rw [Nat.pow_add] at h
  have : 2 ^ 128 * c.toNat < 2 ^ 128 * 2 ^ n := by
    calc 2 ^ 128 * c.toNat = 2 ^ 64 * (2 ^ 64 * c.toNat) := by rw [← Nat.mul_assoc]; rfl
      _ ≤ a.toNat + 2 ^ 64 * (b.toNat + 2 ^ 64 * c.toNat) := by
        have := Nat.mul_le_mul_left (2 ^ 64) (Nat.le_add_left (2 ^ 64 * c.toNat) b.toNat)
        omega
      _ < 2 ^ 128 * 2 ^ n := h
  exact Nat.lt_of_mul_lt_mul_left this

theorem clmulSmall_succ (a d k : Nat) :
    clmulSmall a d (k + 1) = (if d.testBit k then a <<< k else 0) ^^^ clmulSmall a d k := rfl

theorem shl_lt {a m : Nat} (ha : a < 2 ^ m) (n : Nat) : a <<< n < 2 ^ (m + n) := by
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos n)

/-- Terms `a <<< k` for `k ≤ n` only: the product with `n + 1` bits of `d` has at most `m + n` bits. -/
theorem clmulSmall_lt {a m : Nat} (ha : a < 2 ^ m) (d : Nat) : ∀ n, clmulSmall a d (n + 1) < 2 ^ (m + n)
  | 0 => by
    rw [clmulSmall_succ]
    simp only [clmulSmall, Nat.xor_zero, Nat.add_zero]
    split
    · rw [Nat.shiftLeft_zero]; exact ha
    · exact Nat.two_pow_pos _
  | n + 1 => by
    rw [clmulSmall_succ]
    have ih := clmulSmall_lt ha d n
    refine Nat.xor_lt_two_pow ?_ (lt_of_lt_of_le ih (Nat.pow_le_pow_right (by norm_num) (by omega)))
    split
    · exact shl_lt ha (n + 1)
    · exact Nat.two_pow_pos _

theorem clmulSmall_stable (a : Nat) {d n : Nat} (hd : d < 2 ^ n) : ∀ m, n ≤ m → clmulSmall a d m = clmulSmall a d n
  | m, hm => by
    induction m with
    | zero => have : n = 0 := by omega
              subst this; rfl
    | succ m ih =>
      by_cases h : n = m + 1
      · subst h; rfl
      · rw [clmulSmall_succ, ih (by omega), Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hd (Nat.pow_le_pow_right (by norm_num) (by omega)))]
        simp

/-- The bit-step: conditional xor of the multiplicand into the product. -/
theorem clmul_step (a d k : Nat) (P : Nat) (hP : P = clmulSmall a d k) (bit : Bool)
    (hbit : bit = d.testBit k) :
    (if bit then P ^^^ a * 2 ^ k else P) = clmulSmall a d (k + 1) := by
  subst hP hbit
  rw [clmulSmall_succ, Nat.shiftLeft_eq]
  split
  · exact Nat.xor_comm _ _
  · simp

theorem testBit_eq_div (d k : Nat) : d.testBit k = decide (d / 2 ^ k % 2 = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]

theorem clmulSmall_87 (x : Nat) :
    clmulSmall x 0x87 8 = x <<< 7 ^^^ (x <<< 2 ^^^ (x <<< 1 ^^^ x)) := by
  simp only [clmulSmall, show Nat.testBit 135 0 = true by decide, show Nat.testBit 135 1 = true by decide,
    show Nat.testBit 135 2 = true by decide, show Nat.testBit 135 3 = false by decide,
    show Nat.testBit 135 4 = false by decide, show Nat.testBit 135 5 = false by decide,
    show Nat.testBit 135 6 = false by decide, show Nat.testBit 135 7 = true by decide, if_true,
    Bool.false_eq_true, if_false, Nat.shiftLeft_zero, Nat.xor_zero, Nat.zero_xor]

/-- The machine's fold of the high limb (bits 0, 1, 2, 7 of 0x87) into the low limb. -/
def foldLo (r0 r2 : BitVec 64) : BitVec 64 := (((r0 ^^^ r2 <<< 1) ^^^ r2 <<< 2) ^^^ r2 <<< 7) ^^^ r2

theorem shl_small_lt (x k : Nat) (hk : k ≤ 7) (hx : x < 2 ^ 9) : x <<< k < 2 ^ 64 := by
  have h1 := shl_lt hx k
  have h2 : 2 ^ (9 + k) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem toNat_shl_small (x : BitVec 64) (k : Nat) (hk : k ≤ 7) (hx : x.toNat < 2 ^ 9) :
    (x <<< k).toNat = x.toNat <<< k := by
  rw [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt (shl_small_lt _ k hk hx)]

theorem foldLo_toNat (r0 r2 : BitVec 64) (h2 : r2.toNat < 2 ^ 9) :
    (foldLo r0 r2).toNat = r0.toNat ^^^ clmulSmall r2.toNat 0x87 8 := by
  unfold foldLo
  simp only [BitVec.toNat_xor]
  rw [toNat_shl_small r2 1 (by norm_num) h2, toNat_shl_small r2 2 (by norm_num) h2,
    toNat_shl_small r2 7 (by norm_num) h2, clmulSmall_87]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases r0.toNat.testBit i <;> cases (r2.toNat <<< 1).testBit i <;> cases (r2.toNat <<< 2).testBit i <;>
    cases (r2.toNat <<< 7).testBit i <;> cases r2.toNat.testBit i <;> rfl

theorem clmul87_lt (x : Nat) (hx : x < 2 ^ 9) : clmulSmall x 0x87 8 < 2 ^ 64 := by
  rw [clmulSmall_87]
  have h0 : x < 2 ^ 64 := lt_of_lt_of_le hx (by norm_num)
  exact Nat.xor_lt_two_pow (shl_small_lt x 7 (by norm_num) hx) (Nat.xor_lt_two_pow (shl_small_lt x 2 (by norm_num) hx)
    (Nat.xor_lt_two_pow (shl_small_lt x 1 (by norm_num) hx) h0))

/-- The fold, on limbs. -/
theorem lim2_fold (r0 r1 r2 : BitVec 64) (h2 : r2.toNat < 2 ^ 9) :
    lim2 (foldLo r0 r2) r1 = gfFold (lim3 r0 r1 r2) := by
  unfold gfFold lim2
  have hmod : lim3 r0 r1 r2 % 2 ^ 128 = r0.toNat + 2 ^ 64 * r1.toNat := by
    unfold lim3; have := r0.isLt; have := r1.isLt; omega
  have hdiv : lim3 r0 r1 r2 >>> 128 = r2.toNat := by
    rw [Nat.shiftRight_eq_div_pow]; unfold lim3; have := r0.isLt; have := r1.isLt; omega
  rw [hmod, hdiv, foldLo_toNat r0 r2 h2]
  have h := xor_split (k := 64) (y := r1.toNat) (y' := 0) r0.isLt (clmul87_lt _ h2)
  rw [Nat.mul_zero, Nat.add_zero, Nat.xor_zero] at h
  exact h.symm

theorem gfMulSmall_lt {a : Nat} (ha : a < 2 ^ 128) (d : Nat) : gfMulSmall a d < 2 ^ 128 := by
  unfold gfMulSmall gfFold
  have hc := clmulSmall_lt ha d 9
  refine Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _)) ?_
  have h9 : clmulSmall a d 10 >>> 128 < 2 ^ 9 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hc)
  have := clmul87_lt _ h9
  exact lt_of_lt_of_le this (by norm_num)

theorem lim2_toNat (x : BitVec 128) : lim2 (x.extractLsb' 0 64) (x.extractLsb' 64 64) = x.toNat := by
  unfold lim2
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  have := x.isLt
  omega

theorem limbs_of_lim2 {a b : BitVec 64} {x : BitVec 128} (h : lim2 a b = x.toNat) :
    a = x.extractLsb' 0 64 ∧ b = x.extractLsb' 64 64 := by
  have ha := a.isLt
  have hb := b.isLt
  unfold lim2 at h
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one] <;>
    omega

theorem familyEval_cons (c : BitVec 128) (rest : List (BitVec 128)) (pt : Nat) :
    familyEval (c :: rest) pt = gfMulPt (familyEval rest pt) pt ^^^ c := rfl

/-- One Horner step on limbs: product limbs `r` of `acc * d`, coefficient limbs `c0 c1`. -/
theorem horner_limbs {acc c : BitVec 128} {d : Nat} {r0 r1 r2 c0 c1 : BitVec 64}
    (hr : lim3 r0 r1 r2 = clmulSmall acc.toNat d 10) (hc : lim2 c0 c1 = c.toNat) :
    lim2 (foldLo r0 r2 ^^^ c0) (r1 ^^^ c1) = (gfMulPt acc d ^^^ c).toNat := by
  have hlt := clmulSmall_lt acc.isLt d 9
  have h2 : r2.toNat < 2 ^ 9 := lim3_lt r0 r1 r2 (n := 9) (by rw [hr]; exact hlt)
  rw [lim2_xor, lim2_fold r0 r1 r2 h2, hr, hc, BitVec.toNat_xor]
  unfold gfMulPt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (gfMulSmall_lt acc.isLt d)]
  rfl

end ClaudeWCT.W9.Machine.Sign.Gf
