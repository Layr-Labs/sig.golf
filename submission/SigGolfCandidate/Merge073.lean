import RiscvZkvm.Rv64.Word

-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PrePassBits ====
section

/-! # Bit-level facts for the T51 expand decoder DEC (words 54569 .. 54738)

Pure `BitVec 64` / `Nat` lemmas: the top-bit clear of a path node's high dword (`slli; srli`), the top-bit
extraction, the 29-bit accumulator `X` (`xD`) and the sibling's high dword (`sibHi`: tail bytes 8..10 and
`X % 2^16` at bit 24). -/

namespace ClaudeWCT.W9.Machine.Expand.PrePass
open RiscvZkvm.Rv64

/-- Absolute dword address of the high word of compact digest `165 + j` (the path node of height `j`). -/
def pH (j : Nat) : Nat := 31320 + 16 * j
def aH (j : Nat) : BitVec 64 := BitVec.ofNat 64 (pH j)
/-- `srli t2, t1, 64 - k`: the top `k` bits of a dword. -/
def tb (k : Nat) (W : BitVec 64) : BitVec 64 := W >>> (64 - k)
/-- `slli t1, t1, k; srli t1, t1, k`: the dword with its top `k` bits cleared. -/
def clr (k : Nat) (W : BitVec 64) : BitVec 64 := (W <<< k) >>> k
/-- The accumulator `s2` after D1: `X = Σ_j tb b_j (M (aH j)) << xOff_j`, `j = 3..10`. -/
def xD (M : BitVec 64 → BitVec 64) : BitVec 64 :=
  (((((((0#64 ||| tb 1 (M (aH 3))) ||| (tb 1 (M (aH 4)) <<< 1)) ||| (tb 2 (M (aH 5)) <<< 2)) |||
    (tb 3 (M (aH 6)) <<< 4)) ||| (tb 4 (M (aH 7)) <<< 7)) ||| (tb 5 (M (aH 8)) <<< 11)) |||
    (tb 6 (M (aH 9)) <<< 16)) ||| (tb 7 (M (aH 10)) <<< 22)
/-- `X` as a natural number. -/
def xN (M : BitVec 64 → BitVec 64) : Nat :=
  (M (aH 3)).toNat / 2 ^ 63 + (M (aH 4)).toNat / 2 ^ 63 * 2 ^ 1 + (M (aH 5)).toNat / 2 ^ 62 * 2 ^ 2 +
  (M (aH 6)).toNat / 2 ^ 61 * 2 ^ 4 + (M (aH 7)).toNat / 2 ^ 60 * 2 ^ 7 + (M (aH 8)).toNat / 2 ^ 59 * 2 ^ 11 +
  (M (aH 9)).toNat / 2 ^ 58 * 2 ^ 16 + (M (aH 10)).toNat / 2 ^ 57 * 2 ^ 22
/-- The sibling's high dword (`s4`): tail bytes 8, 9, 10 of the dword `W` and `X % 2^16` at bit 24. -/
def sibHi (W X : BitVec 64) : BitVec 64 :=
  ((((extractByte W 0).zeroExtend 64 ||| ((extractByte W 1).zeroExtend 64 <<< 8)) |||
    ((extractByte W 2).zeroExtend 64 <<< 16)) ||| (((X <<< 48) >>> 48) <<< 24))

theorem toNat_or_shift (a b : BitVec 64) (k : Nat) (ha : a.toNat < 2 ^ k)
    (hb : b.toNat * 2 ^ k < 2 ^ 64) : (a ||| (b <<< k)).toNat = a.toNat + b.toNat * 2 ^ k := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hb, Nat.or_comm,
    Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ha, Nat.mul_comm, Nat.add_comm]

theorem tb_toNat (k : Nat) (W : BitVec 64) : (tb k W).toNat = W.toNat / 2 ^ (64 - k) := by
  simp only [tb, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem tb_lt (k : Nat) (hk : k ≤ 64) (W : BitVec 64) : (tb k W).toNat < 2 ^ k := by
  rw [tb_toNat]
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add, show 64 - k + k = 64 by omega]
  exact W.isLt

theorem clr_toNat (k : Nat) (hk : k ≤ 64) (W : BitVec 64) : (clr k W).toNat = W.toNat % 2 ^ (64 - k) := by
  simp only [clr, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 64 = 2 ^ (64 - k) * 2 ^ k by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos k)]

theorem acc_toNat (a b c d e f g h : BitVec 64) (ha : a.toNat < 2) (hb : b.toNat < 2) (hc : c.toNat < 4)
    (hd : d.toNat < 8) (he : e.toNat < 16) (hf : f.toNat < 32) (hg : g.toNat < 64) (hh : h.toNat < 128) :
    ((((((((0#64 ||| a) ||| (b <<< 1)) ||| (c <<< 2)) ||| (d <<< 4)) ||| (e <<< 7)) ||| (f <<< 11)) |||
      (g <<< 16)) ||| (h <<< 22)).toNat =
      a.toNat + b.toNat * 2 ^ 1 + c.toNat * 2 ^ 2 + d.toNat * 2 ^ 4 + e.toNat * 2 ^ 7 + f.toNat * 2 ^ 11 +
        g.toNat * 2 ^ 16 + h.toNat * 2 ^ 22 := by
  have s1 : (0#64 ||| a).toNat = a.toNat := by rw [BitVec.zero_or]
  have s2 := toNat_or_shift (0#64 ||| a) b 1 (by rw [s1]; omega) (by omega)
  rw [s1] at s2
  have s3 := toNat_or_shift _ c 2 (by rw [s2]; omega) (by omega)
  rw [s2] at s3
  have s4 := toNat_or_shift _ d 4 (by rw [s3]; omega) (by omega)
  rw [s3] at s4
  have s5 := toNat_or_shift _ e 7 (by rw [s4]; omega) (by omega)
  rw [s4] at s5
  have s6 := toNat_or_shift _ f 11 (by rw [s5]; omega) (by omega)
  rw [s5] at s6
  have s7 := toNat_or_shift _ g 16 (by rw [s6]; omega) (by omega)
  rw [s6] at s7
  have s8 := toNat_or_shift _ h 22 (by rw [s7]; omega) (by omega)
  rw [s7] at s8
  exact s8

theorem xD_toNat (M : BitVec 64 → BitVec 64) : (xD M).toNat = xN M := by
  unfold xD
  rw [acc_toNat _ _ _ _ _ _ _ _ (tb_lt 1 (by omega) _) (tb_lt 1 (by omega) _) (tb_lt 2 (by omega) _)
    (tb_lt 3 (by omega) _) (tb_lt 4 (by omega) _) (tb_lt 5 (by omega) _) (tb_lt 6 (by omega) _)
    (tb_lt 7 (by omega) _)]
  simp only [tb_toNat, xN]

theorem xN_lt (M : BitVec 64 → BitVec 64) : xN M < 2 ^ 29 := by
  have h := xD_toNat M
  have b1 := tb_lt 1 (by omega) (M (aH 3)); have b2 := tb_lt 1 (by omega) (M (aH 4))
  have b3 := tb_lt 2 (by omega) (M (aH 5)); have b4 := tb_lt 3 (by omega) (M (aH 6))
  have b5 := tb_lt 4 (by omega) (M (aH 7)); have b6 := tb_lt 5 (by omega) (M (aH 8))
  have b7 := tb_lt 6 (by omega) (M (aH 9)); have b8 := tb_lt 7 (by omega) (M (aH 10))
  simp only [tb_toNat] at b1 b2 b3 b4 b5 b6 b7 b8
  unfold xN
  omega

theorem zext_byte_toNat (W : BitVec 64) (i : Nat) :
    ((extractByte W i).zeroExtend 64).toNat = W.toNat / 2 ^ (i * 8) % 2 ^ 8 := by
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show W.toNat / 2 ^ (i * 8) % 2 ^ 8 < 2 ^ 64 by omega)]

theorem sibHi_toNat (W X : BitVec 64) :
    (sibHi W X).toNat = W.toNat % 2 ^ 24 + X.toNat % 2 ^ 16 * 2 ^ 24 := by
  have hW := W.isLt
  have e0 := zext_byte_toNat W 0
  have e1 := zext_byte_toNat W 1
  have e2 := zext_byte_toNat W 2
  have hx : ((X <<< 48) >>> 48).toNat = X.toNat % 2 ^ 16 := clr_toNat 48 (by omega) X
  unfold sibHi
  have s1 := toNat_or_shift ((extractByte W 0).zeroExtend 64) ((extractByte W 1).zeroExtend 64) 8
    (by rw [e0]; omega) (by rw [e1]; omega)
  have s2 := toNat_or_shift _ ((extractByte W 2).zeroExtend 64) 16 (by rw [s1, e0, e1]; omega) (by rw [e2]; omega)
  have s3 := toNat_or_shift _ ((X <<< 48) >>> 48) 24 (by rw [s2, s1, e0, e1, e2]; omega) (by rw [hx]; omega)
  rw [s3, s2, s1, e0, e1, e2, hx]
  omega

end ClaudeWCT.W9.Machine.Expand.PrePass
end
