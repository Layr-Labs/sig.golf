import SigGolfCandidate.T3M.Search.Basic

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem ofNat_and_mask (a m : Nat) (_hm : m ≤ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 (2 ^ m - 1) = BitVec.ofNat 64 (a % 2 ^ m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and]
  by_cases h : i < m <;> simp [h]
@[simp] theorem ofNat_and7 (a : Nat) : BitVec.ofNat 64 a &&& 7#64 = BitVec.ofNat 64 (a % 8) :=
  ofNat_and_mask a 3 (by decide)
@[simp] theorem ofNat_and3 (a : Nat) : BitVec.ofNat 64 a &&& 3#64 = BitVec.ofNat 64 (a % 4) :=
  ofNat_and_mask a 2 (by decide)
@[simp] theorem ofNat_and255 (a : Nat) : BitVec.ofNat 64 a &&& 255#64 = BitVec.ofNat 64 (a % 256) :=
  ofNat_and_mask a 8 (by decide)
theorem ofNat_ult (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
@[simp] theorem ofNat_and15 (a : Nat) : BitVec.ofNat 64 a &&& 15#64 = BitVec.ofNat 64 (a % 16) :=
  ofNat_and_mask a 4 (by decide)
@[simp] theorem ofNat_and127 (a : Nat) : BitVec.ofNat 64 a &&& 127#64 = BitVec.ofNat 64 (a % 128) :=
  ofNat_and_mask a 7 (by decide)
end SigGolfCandidate.T3M.Search
