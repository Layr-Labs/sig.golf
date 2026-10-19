import RiscvZkvm.Rv64.Word
set_option Elab.async false

/-! # Bit-level facts for the img-v6 expand pre-pass (words 43250 .. 43333)

Pure `BitVec 64` / `Nat` lemmas: the per-node half-word clear, the top-bit extraction, the 55-bit
accumulator `X`, the `sb` of `X % 2^8` into byte 7 of dword 5232 and the dword written at 5240. -/

namespace ClaudeWCT.W9.Machine.Expand.PrePass
open RiscvZkvm.Rv64

/-- Dword address (absolute) holding the top half of path node `i` (digest `168 + i`). -/
def pA (i : Nat) : Nat := 31368 + 16 * i
/-- `X` field offset of path node `i`. -/
def xo (i : Nat) : Nat := i * (i - 1) / 2

/-- `lhu` of the top half-word of a dword. -/
def hu (W : BitVec 64) : BitVec 64 := (extractHalfword W 3).zeroExtend 64
/-- The top `i` bits of a dword (`srli t1, t3, 16 - i`). -/
def topW (i : Nat) (W : BitVec 64) : BitVec 64 := hu W >>> (16 - i)
/-- The dword after `sh` of the half-word with its top `i` bits cleared. -/
def clrW (i : Nat) (W : BitVec 64) : BitVec 64 :=
  replaceHalfword W 3 (((hu W <<< (48 + i)) >>> (48 + i)).truncate 16)
/-- The accumulator `t2` after the ten nodes. -/
def xW (M : BitVec 64 → BitVec 64) : BitVec 64 :=
  (((((((((0#64 ||| topW 1 (M (BitVec.ofNat 64 (pA 1)))) |||
    (topW 2 (M (BitVec.ofNat 64 (pA 2))) <<< 1)) |||
    (topW 3 (M (BitVec.ofNat 64 (pA 3))) <<< 3)) |||
    (topW 4 (M (BitVec.ofNat 64 (pA 4))) <<< 6)) |||
    (topW 5 (M (BitVec.ofNat 64 (pA 5))) <<< 10)) |||
    (topW 6 (M (BitVec.ofNat 64 (pA 6))) <<< 15)) |||
    (topW 7 (M (BitVec.ofNat 64 (pA 7))) <<< 21)) |||
    (topW 8 (M (BitVec.ofNat 64 (pA 8))) <<< 28)) |||
    (topW 9 (M (BitVec.ofNat 64 (pA 9))) <<< 36)) |||
    (topW 10 (M (BitVec.ofNat 64 (pA 10))) <<< 45)
/-- The dword stored at 5240. -/
def dW (X : BitVec 64) : BitVec 64 := (((X >>> 8) <<< 30) >>> 30) ||| ((X >>> 42) <<< 48)

/-- The 55-bit field, as a natural number, from the ten top dwords. -/
def xN (M : BitVec 64 → BitVec 64) : Nat :=
  (M (BitVec.ofNat 64 (pA 1))).toNat / 2 ^ 63 +
  (M (BitVec.ofNat 64 (pA 2))).toNat / 2 ^ 62 * 2 ^ 1 +
  (M (BitVec.ofNat 64 (pA 3))).toNat / 2 ^ 61 * 2 ^ 3 +
  (M (BitVec.ofNat 64 (pA 4))).toNat / 2 ^ 60 * 2 ^ 6 +
  (M (BitVec.ofNat 64 (pA 5))).toNat / 2 ^ 59 * 2 ^ 10 +
  (M (BitVec.ofNat 64 (pA 6))).toNat / 2 ^ 58 * 2 ^ 15 +
  (M (BitVec.ofNat 64 (pA 7))).toNat / 2 ^ 57 * 2 ^ 21 +
  (M (BitVec.ofNat 64 (pA 8))).toNat / 2 ^ 56 * 2 ^ 28 +
  (M (BitVec.ofNat 64 (pA 9))).toNat / 2 ^ 55 * 2 ^ 36 +
  (M (BitVec.ofNat 64 (pA 10))).toNat / 2 ^ 54 * 2 ^ 45

theorem toNat_or_shift (a b : BitVec 64) (k : Nat) (ha : a.toNat < 2 ^ k)
    (hb : b.toNat * 2 ^ k < 2 ^ 64) : (a ||| (b <<< k)).toNat = a.toNat + b.toNat * 2 ^ k := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hb, Nat.or_comm,
    Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ha, Nat.mul_comm, Nat.add_comm]

theorem hu_toNat (W : BitVec 64) : (hu W).toNat = W.toNat / 2 ^ 48 := by
  have h := W.isLt
  simp only [hu, extractHalfword, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  omega

theorem topW_toNat (i : Nat) (hi : i ≤ 16) (W : BitVec 64) :
    (topW i W).toNat = W.toNat / 2 ^ (64 - i) := by
  simp only [topW, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hu_toNat,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 2
  omega

theorem topW_lt (i : Nat) (hi : i ≤ 16) (W : BitVec 64) : (topW i W).toNat < 2 ^ i := by
  rw [topW_toNat i hi]
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add, show 64 - i + i = 64 by omega]
  exact W.isLt

theorem mask_hw (W : BitVec 64) : W &&& ~~~(0xFFFF#64 <<< (3 * 16)) = (W.setWidth 48).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have key : ∀ j < 16, (0xFFFF#64).getLsbD j = true := by decide
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : k < 48
  · simp [h, hk]
  · simp [h, hk, key (k - 48) (by omega)]

theorem mask_b (W : BitVec 64) : W &&& ~~~(0xFF#64 <<< (7 * 8)) = (W.setWidth 56).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have key : ∀ j < 8, (0xFF#64).getLsbD j = true := by decide
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : k < 56
  · simp [h, hk]
  · simp [h, hk, key (k - 56) (by omega)]

theorem clrW_toNat (i : Nat) (hi : 1 ≤ i ∧ i ≤ 10) (W : BitVec 64) :
    (clrW i W).toNat = W.toNat % 2 ^ (64 - i) := by
  have h := W.isLt
  have hx : ((((hu W <<< (48 + i)) >>> (48 + i))).truncate 16 : BitVec 16).toNat =
      W.toNat / 2 ^ 48 % 2 ^ (16 - i) := by
    have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
        Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, hu_toNat] <;> omega
  have hb := (BitVec.truncate 16 ((hu W <<< (48 + i)) >>> (48 + i))).isLt
  unfold clrW replaceHalfword
  simp only []
  rw [mask_hw, toNat_or_shift _ _ _ (by simp only [BitVec.toNat_setWidth]; omega)
    (by simp only [BitVec.toNat_setWidth]; omega)]
  simp only [BitVec.toNat_setWidth]
  simp only [BitVec.toNat_setWidth] at hx
  rw [hx]
  have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem replaceByte7 (V : BitVec 64) (c : BitVec 8) :
    (replaceByte V 7 c).toNat = V.toNat % 2 ^ 56 + c.toNat * 2 ^ 56 := by
  have h := V.isLt
  have hc := c.isLt
  unfold replaceByte
  simp only []
  rw [mask_b, toNat_or_shift _ _ _ (by simp only [BitVec.toNat_setWidth]; omega)
    (by simp only [BitVec.toNat_setWidth]; omega)]
  simp only [BitVec.toNat_setWidth]
  omega

theorem dW_toNat (X : BitVec 64) (hX : X.toNat < 2 ^ 55) :
    (dW X).toNat = X.toNat / 2 ^ 8 % 2 ^ 34 + X.toNat / 2 ^ 42 * 2 ^ 48 := by
  unfold dW
  rw [toNat_or_shift _ _ _ (by simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]; omega)
    (by simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem xW_toNat (M : BitVec 64 → BitVec 64) : (xW M).toNat = xN M := by
  have b1 := topW_lt 1 (by omega) (M (BitVec.ofNat 64 (pA 1)))
  have b2 := topW_lt 2 (by omega) (M (BitVec.ofNat 64 (pA 2)))
  have b3 := topW_lt 3 (by omega) (M (BitVec.ofNat 64 (pA 3)))
  have b4 := topW_lt 4 (by omega) (M (BitVec.ofNat 64 (pA 4)))
  have b5 := topW_lt 5 (by omega) (M (BitVec.ofNat 64 (pA 5)))
  have b6 := topW_lt 6 (by omega) (M (BitVec.ofNat 64 (pA 6)))
  have b7 := topW_lt 7 (by omega) (M (BitVec.ofNat 64 (pA 7)))
  have b8 := topW_lt 8 (by omega) (M (BitVec.ofNat 64 (pA 8)))
  have b9 := topW_lt 9 (by omega) (M (BitVec.ofNat 64 (pA 9)))
  have b10 := topW_lt 10 (by omega) (M (BitVec.ofNat 64 (pA 10)))
  have s1 : (0#64 ||| topW 1 (M (BitVec.ofNat 64 (pA 1)))).toNat = (topW 1 (M (BitVec.ofNat 64 (pA 1)))).toNat := by rw [BitVec.zero_or]
  have s2 : ((0#64 ||| topW 1 (M (BitVec.ofNat 64 (pA 1)))) ||| (topW 2 (M (BitVec.ofNat 64 (pA 2))) <<< 1)).toNat = (topW 1 (M (BitVec.ofNat 64 (pA 1)))).toNat + (topW 2 (M (BitVec.ofNat 64 (pA 2)))).toNat * 2 ^ 1 := by
    rw [toNat_or_shift _ _ 1 (by rw [s1]; omega) (by omega), s1]
  have s3 : (((0#64 ||| topW 1 (M (BitVec.ofNat 64 (pA 1)))) ||| (topW 2 (M (BitVec.ofNat 64 (pA 2))) <<< 1)) ||| (topW 3 (M (BitVec.ofNat 64 (pA 3))) <<< 3)).toNat = (topW 1 (M (BitVec.ofNat 64 (pA 1)))).toNat + (topW 2 (M (BitVec.ofNat 64 (pA 2)))).toNat * 2 ^ 1 + (topW 3 (M (BitVec.ofNat 64 (pA 3)))).toNat * 2 ^ 3 := by
    rw [toNat_or_shift _ _ 3 (by rw [s2]; omega) (by omega), s2]
  have s4 : ((((0#64 ||| topW 1 (M (BitVec.ofNat 64 (pA 1)))) ||| (topW 2 (M (BitVec.ofNat 64 (pA 2))) <<< 1)) ||| (topW 3 (M (BitVec.ofNat 64 (pA 3))) <<< 3)) ||| (topW 4 (M (BitVec.ofNat 64 (pA 4))) <<< 6)).toNat = (topW 1 (M (BitVec.ofNat 64 (pA 1)))).toNat + (topW 2 (M (BitVec.ofNat 64 (pA 2)))).toNat * 2 ^ 1 + (topW 3 (M (BitVec.ofNat 64 (pA 3)))).toNat * 2 ^ 3 + (topW 4 (M (BitVec.ofNat 64 (pA 4)))).toNat * 2 ^ 6 := by
    rw [toNat_or_shift _ _ 6 (by rw [s3]; omega) (by omega), s3]
  have s5 : (((((0#64 ||| topW 1 (M (BitVec.ofNat 64 (pA 1)))) ||| (topW 2 (M (BitVec.ofNat 64 (pA 2))) <<< 1)) ||| (topW 3 (M (BitVec.ofNat 64 (pA 3))) <<< 3)) ||| (topW 4 (M (BitVec.ofNat 64 (pA 4))) <<< 6)) ||| (topW 5 (M (BitVec.ofNat 64 (pA 5))) <<< 10)).toNat = (topW 1 (M (BitVec.ofNat 64 (pA 1)))).toNat + (topW 2 (M (BitVec.ofNat 64 (pA 2)))).toNat * 2 ^ 1 + (topW 3 (M (BitVec.ofNat 64 (pA 3)))).toNat * 2 ^ 3 + (topW 4 (M (BitVec.ofNat 64 (pA 4)))).toNat * 2 ^ 6 + (topW 5 (M (BitVec.ofNat 64 (pA 5)))).toNat * 2 ^ 10 := by
    rw [toNat_or_shift _ _ 10 (by rw [s4]; omega) (by omega), s4]
  have s6 : ((((((0#64 ||| topW 1 (M (BitVec.ofNat 64 (pA 1)))) ||| (topW 2 (M (BitVec.ofNat 64 (pA 2))) <<< 1)) ||| (topW 3 (M (BitVec.ofNat 64 (pA 3))) <<< 3)) ||| (topW 4 (M (BitVec.ofNat 64 (pA 4))) <<< 6)) ||| (topW 5 (M (BitVec.ofNat 64 (pA 5))) <<< 10)) ||| (topW 6 (M (BitVec.ofNat 64 (pA 6))) <<< 15)).toNat = (topW 1 (M (BitVec.ofNat 64 (pA 1)))).toNat + (topW 2 (M (BitVec.ofNat 64 (pA 2)))).toNat * 2 ^ 1 + (topW 3 (M (BitVec.ofNat 64 (pA 3)))).toNat * 2 ^ 3 + (topW 4 (M (BitVec.ofNat 64 (pA 4)))).toNat * 2 ^ 6 + (topW 5 (M (BitVec.ofNat 64 (pA 5)))).toNat * 2 ^ 10 + (topW 6 (M (BitVec.ofNat 64 (pA 6)))).toNat * 2 ^ 15 := by
    rw [toNat_or_shift _ _ 15 (by rw [s5]; omega) (by omega), s5]
  have s7 : (((((((0#64 ||| topW 1 (M (BitVec.ofNat 64 (pA 1)))) ||| (topW 2 (M (BitVec.ofNat 64 (pA 2))) <<< 1)) ||| (topW 3 (M (BitVec.ofNat 64 (pA 3))) <<< 3)) ||| (topW 4 (M (BitVec.ofNat 64 (pA 4))) <<< 6)) ||| (topW 5 (M (BitVec.ofNat 64 (pA 5))) <<< 10)) ||| (topW 6 (M (BitVec.ofNat 64 (pA 6))) <<< 15)) ||| (topW 7 (M (BitVec.ofNat 64 (pA 7))) <<< 21)).toNat = (topW 1 (M (BitVec.ofNat 64 (pA 1)))).toNat + (topW 2 (M (BitVec.ofNat 64 (pA 2)))).toNat * 2 ^ 1 + (topW 3 (M (BitVec.ofNat 64 (pA 3)))).toNat * 2 ^ 3 + (topW 4 (M (BitVec.ofNat 64 (pA 4)))).toNat * 2 ^ 6 + (topW 5 (M (BitVec.ofNat 64 (pA 5)))).toNat * 2 ^ 10 + (topW 6 (M (BitVec.ofNat 64 (pA 6)))).toNat * 2 ^ 15 + (topW 7 (M (BitVec.ofNat 64 (pA 7)))).toNat * 2 ^ 21 := by
    rw [toNat_or_shift _ _ 21 (by rw [s6]; omega) (by omega), s6]
  have s8 : ((((((((0#64 ||| topW 1 (M (BitVec.ofNat 64 (pA 1)))) ||| (topW 2 (M (BitVec.ofNat 64 (pA 2))) <<< 1)) ||| (topW 3 (M (BitVec.ofNat 64 (pA 3))) <<< 3)) ||| (topW 4 (M (BitVec.ofNat 64 (pA 4))) <<< 6)) ||| (topW 5 (M (BitVec.ofNat 64 (pA 5))) <<< 10)) ||| (topW 6 (M (BitVec.ofNat 64 (pA 6))) <<< 15)) ||| (topW 7 (M (BitVec.ofNat 64 (pA 7))) <<< 21)) ||| (topW 8 (M (BitVec.ofNat 64 (pA 8))) <<< 28)).toNat = (topW 1 (M (BitVec.ofNat 64 (pA 1)))).toNat + (topW 2 (M (BitVec.ofNat 64 (pA 2)))).toNat * 2 ^ 1 + (topW 3 (M (BitVec.ofNat 64 (pA 3)))).toNat * 2 ^ 3 + (topW 4 (M (BitVec.ofNat 64 (pA 4)))).toNat * 2 ^ 6 + (topW 5 (M (BitVec.ofNat 64 (pA 5)))).toNat * 2 ^ 10 + (topW 6 (M (BitVec.ofNat 64 (pA 6)))).toNat * 2 ^ 15 + (topW 7 (M (BitVec.ofNat 64 (pA 7)))).toNat * 2 ^ 21 + (topW 8 (M (BitVec.ofNat 64 (pA 8)))).toNat * 2 ^ 28 := by
    rw [toNat_or_shift _ _ 28 (by rw [s7]; omega) (by omega), s7]
  have s9 : (((((((((0#64 ||| topW 1 (M (BitVec.ofNat 64 (pA 1)))) ||| (topW 2 (M (BitVec.ofNat 64 (pA 2))) <<< 1)) ||| (topW 3 (M (BitVec.ofNat 64 (pA 3))) <<< 3)) ||| (topW 4 (M (BitVec.ofNat 64 (pA 4))) <<< 6)) ||| (topW 5 (M (BitVec.ofNat 64 (pA 5))) <<< 10)) ||| (topW 6 (M (BitVec.ofNat 64 (pA 6))) <<< 15)) ||| (topW 7 (M (BitVec.ofNat 64 (pA 7))) <<< 21)) ||| (topW 8 (M (BitVec.ofNat 64 (pA 8))) <<< 28)) ||| (topW 9 (M (BitVec.ofNat 64 (pA 9))) <<< 36)).toNat = (topW 1 (M (BitVec.ofNat 64 (pA 1)))).toNat + (topW 2 (M (BitVec.ofNat 64 (pA 2)))).toNat * 2 ^ 1 + (topW 3 (M (BitVec.ofNat 64 (pA 3)))).toNat * 2 ^ 3 + (topW 4 (M (BitVec.ofNat 64 (pA 4)))).toNat * 2 ^ 6 + (topW 5 (M (BitVec.ofNat 64 (pA 5)))).toNat * 2 ^ 10 + (topW 6 (M (BitVec.ofNat 64 (pA 6)))).toNat * 2 ^ 15 + (topW 7 (M (BitVec.ofNat 64 (pA 7)))).toNat * 2 ^ 21 + (topW 8 (M (BitVec.ofNat 64 (pA 8)))).toNat * 2 ^ 28 + (topW 9 (M (BitVec.ofNat 64 (pA 9)))).toNat * 2 ^ 36 := by
    rw [toNat_or_shift _ _ 36 (by rw [s8]; omega) (by omega), s8]
  have s10 : ((((((((((0#64 ||| topW 1 (M (BitVec.ofNat 64 (pA 1)))) ||| (topW 2 (M (BitVec.ofNat 64 (pA 2))) <<< 1)) ||| (topW 3 (M (BitVec.ofNat 64 (pA 3))) <<< 3)) ||| (topW 4 (M (BitVec.ofNat 64 (pA 4))) <<< 6)) ||| (topW 5 (M (BitVec.ofNat 64 (pA 5))) <<< 10)) ||| (topW 6 (M (BitVec.ofNat 64 (pA 6))) <<< 15)) ||| (topW 7 (M (BitVec.ofNat 64 (pA 7))) <<< 21)) ||| (topW 8 (M (BitVec.ofNat 64 (pA 8))) <<< 28)) ||| (topW 9 (M (BitVec.ofNat 64 (pA 9))) <<< 36)) ||| (topW 10 (M (BitVec.ofNat 64 (pA 10))) <<< 45)).toNat = (topW 1 (M (BitVec.ofNat 64 (pA 1)))).toNat + (topW 2 (M (BitVec.ofNat 64 (pA 2)))).toNat * 2 ^ 1 + (topW 3 (M (BitVec.ofNat 64 (pA 3)))).toNat * 2 ^ 3 + (topW 4 (M (BitVec.ofNat 64 (pA 4)))).toNat * 2 ^ 6 + (topW 5 (M (BitVec.ofNat 64 (pA 5)))).toNat * 2 ^ 10 + (topW 6 (M (BitVec.ofNat 64 (pA 6)))).toNat * 2 ^ 15 + (topW 7 (M (BitVec.ofNat 64 (pA 7)))).toNat * 2 ^ 21 + (topW 8 (M (BitVec.ofNat 64 (pA 8)))).toNat * 2 ^ 28 + (topW 9 (M (BitVec.ofNat 64 (pA 9)))).toNat * 2 ^ 36 + (topW 10 (M (BitVec.ofNat 64 (pA 10)))).toNat * 2 ^ 45 := by
    rw [toNat_or_shift _ _ 45 (by rw [s9]; omega) (by omega), s9]
  unfold xW; rw [s10]; unfold xN
  rw [topW_toNat 1 (by omega), topW_toNat 2 (by omega), topW_toNat 3 (by omega), topW_toNat 4 (by omega), topW_toNat 5 (by omega), topW_toNat 6 (by omega), topW_toNat 7 (by omega), topW_toNat 8 (by omega), topW_toNat 9 (by omega), topW_toNat 10 (by omega)]
  try rfl

theorem xN_lt (M : BitVec 64 → BitVec 64) : xN M < 2 ^ 55 := by
  have e := fun i (hi : i ≤ 16) W => topW_toNat i hi W
  have t := fun i (hi : i ≤ 16) W => topW_lt i hi W
  unfold xN
  have b1 := t 1 (by omega) (M (BitVec.ofNat 64 (pA 1))); have b2 := t 2 (by omega) (M (BitVec.ofNat 64 (pA 2)))
  have b3 := t 3 (by omega) (M (BitVec.ofNat 64 (pA 3))); have b4 := t 4 (by omega) (M (BitVec.ofNat 64 (pA 4)))
  have b5 := t 5 (by omega) (M (BitVec.ofNat 64 (pA 5))); have b6 := t 6 (by omega) (M (BitVec.ofNat 64 (pA 6)))
  have b7 := t 7 (by omega) (M (BitVec.ofNat 64 (pA 7))); have b8 := t 8 (by omega) (M (BitVec.ofNat 64 (pA 8)))
  have b9 := t 9 (by omega) (M (BitVec.ofNat 64 (pA 9))); have b10 := t 10 (by omega) (M (BitVec.ofNat 64 (pA 10)))
  rw [e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega),
    e 7 (by omega), e 8 (by omega), e 9 (by omega), e 10 (by omega)] at *
  omega

end ClaudeWCT.W9.Machine.Expand.PrePass
