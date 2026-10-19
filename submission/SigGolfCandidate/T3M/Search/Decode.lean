import SigGolfCandidate.T3M.Search.Arith
import SigGolfCandidate.T3.Nonbinary.TopFlip

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
theorem ext_shr_mask (v : BitVec 128) (base sh w : Nat) (h : sh + w ≤ 64) :
    (v.extractLsb' base 64 >>> sh) &&& BitVec.ofNat 64 (2 ^ w - 1) =
      BitVec.ofNat 64 (v.toNat / 2 ^ (base + sh) % 2 ^ w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, hi,
    decide_true, Bool.true_and]
  by_cases hw : i < w
  · simp only [hw, decide_true, Bool.and_true, Bool.true_and, show sh + i < 64 by omega, BitVec.testBit_toNat]
    congr 1; omega
  · simp [hw]
@[simp] theorem ext_shr_and7 (v : BitVec 128) (base sh : Nat) (h : sh + 3 ≤ 64) :
    (v.extractLsb' base 64 >>> sh) &&& 7#64 = BitVec.ofNat 64 (v.toNat / 2 ^ (base + sh) % 8) :=
  ext_shr_mask v base sh 3 h
@[simp] theorem ext_and7 (v : BitVec 128) (base : Nat) :
    v.extractLsb' base 64 &&& 7#64 = BitVec.ofNat 64 (v.toNat / 2 ^ base % 8) := by
  simpa using ext_shr_mask v base 0 3 (by omega)
@[simp] theorem ext_shr_and3 (v : BitVec 128) (base sh : Nat) (h : sh + 2 ≤ 64) :
    (v.extractLsb' base 64 >>> sh) &&& 3#64 = BitVec.ofNat 64 (v.toNat / 2 ^ (base + sh) % 4) :=
  ext_shr_mask v base sh 2 h
@[simp] theorem ext_and3 (v : BitVec 128) (base : Nat) :
    v.extractLsb' base 64 &&& 3#64 = BitVec.ofNat 64 (v.toNat / 2 ^ base % 4) := by
  simpa using ext_shr_mask v base 0 2 (by omega)
def lowDigits (v : Digest) : List Nat := (List.range 42).map fun i => v.toNat / 2 ^ T3.lowerShift i % 8
/-- Campaign R6: the 51 top data digits (the checksum digit is `target 0 - sum`). -/
def topDigits (v : Digest) : List Nat := (List.range 51).map (T3.coreDigit 0 v)
theorem dataDigits_low (lay : Layer) (h : lay ≠ 0) (v : Digest) : T3.dataDigits lay v = lowDigits v := by
  simp only [T3.dataDigits, T3.dataCount, h, if_false, lowDigits]
  congr 1
  funext i
  simp [T3.coreDigit, h]
theorem dataDigits_top (v : Digest) : T3.dataDigits 0 v = topDigits v := rfl
theorem lowDigits_length (v : Digest) : (lowDigits v).length = 42 := by simp [lowDigits]
theorem lowDigits_sum (v : Digest) : (lowDigits v).sum =
      v.toNat / 1 % 8 +
      v.toNat / 8 % 8 +
      v.toNat / 64 % 8 +
      v.toNat / 512 % 8 +
      v.toNat / 4096 % 8 +
      v.toNat / 32768 % 8 +
      v.toNat / 262144 % 8 +
      v.toNat / 2097152 % 8 +
      v.toNat / 16777216 % 8 +
      v.toNat / 134217728 % 8 +
      v.toNat / 1073741824 % 8 +
      v.toNat / 8589934592 % 8 +
      v.toNat / 68719476736 % 8 +
      v.toNat / 549755813888 % 8 +
      v.toNat / 4398046511104 % 8 +
      v.toNat / 35184372088832 % 8 +
      v.toNat / 281474976710656 % 8 +
      v.toNat / 2251799813685248 % 8 +
      v.toNat / 18014398509481984 % 8 +
      v.toNat / 144115188075855872 % 8 +
      v.toNat / 1152921504606846976 % 8 +
      v.toNat / 18446744073709551616 % 8 +
      v.toNat / 147573952589676412928 % 8 +
      v.toNat / 1180591620717411303424 % 8 +
      v.toNat / 9444732965739290427392 % 8 +
      v.toNat / 75557863725914323419136 % 8 +
      v.toNat / 604462909807314587353088 % 8 +
      v.toNat / 4835703278458516698824704 % 8 +
      v.toNat / 38685626227668133590597632 % 8 +
      v.toNat / 309485009821345068724781056 % 8 +
      v.toNat / 2475880078570760549798248448 % 8 +
      v.toNat / 19807040628566084398385987584 % 8 +
      v.toNat / 158456325028528675187087900672 % 8 +
      v.toNat / 1267650600228229401496703205376 % 8 +
      v.toNat / 10141204801825835211973625643008 % 8 +
      v.toNat / 81129638414606681695789005144064 % 8 +
      v.toNat / 649037107316853453566312041152512 % 8 +
      v.toNat / 5192296858534827628530496329220096 % 8 +
      v.toNat / 41538374868278621028243970633760768 % 8 +
      v.toNat / 332306998946228968225951765070086144 % 8 +
      v.toNat / 2658455991569831745807614120560689152 % 8 +
      v.toNat / 21267647932558653966460912964485513216 % 8 := by
  simp only [lowDigits, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  norm_num [T3.lowerShift]
theorem decode_low (lay : Layer) (h : lay ≠ 0) (v : Digest) :
    T3.decode lay v =
      if T3.lowerSpare v ∧ (lowDigits v).sum ≤ T3.target lay ∧ T3.target lay - (lowDigits v).sum < 8
      then some (lowDigits v ++ [T3.target lay - (lowDigits v).sum]) else none := by
  have hb : ¬ v.toNat ≥ 2 ^ T3.encodedBits lay := by
    simp only [T3.encodedBits, h, if_false]; have := v.isLt; omega
  unfold T3.decode
  rw [if_neg hb, dataDigits_low lay h]
  simp only [h, if_false]
/-- Campaign R6: the top value decodes iff its fields are valid (spare bit 0, 8 r6 + 9 r5 ranks in range) and the
checksum digit `153 - sum` lies in `[0, 7]`; the digits are the 51 data digits and the checksum digit. -/
theorem decode_top (v : Digest) :
    T3.decode 0 v = if T3.topRanksValid v = true ∧ (topDigits v).sum ≤ 153 ∧ 153 - (topDigits v).sum < 8
      then some (topDigits v ++ [153 - (topDigits v).sum]) else none := by
  unfold T3.decode
  rw [if_neg (show ¬ v.toNat ≥ 2 ^ T3.encodedBits 0 from Nat.not_le.mpr v.isLt)]
  simp only [if_true, dataDigits_top, T3.target]
  rfl
end SigGolfCandidate.T3M.Search
