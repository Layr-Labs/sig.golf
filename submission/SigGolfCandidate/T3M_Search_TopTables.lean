import SigGolfCandidate.T3M_Search_Decode
import SigGolfCandidate.ClaudeWCT_WCT9_Core

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
abbrev TOP_DATA : Nat := 16773120
def rankDigit (r i : Nat) : Nat := r / 5 ^ i % 5
def rankWeight (r : Nat) : Nat := r % 5 + r / 5 % 5 + r / 25 % 5
def rankLookup (r : Nat) : Nat := if r < 125 then rankWeight r else 255
def topRank (v : Digest) (j : Nat) : Nat := v.toNat / 2 ^ (7 * j) % 128
def rankDigits (v : Digest) : List Nat := (List.range 17).map (topRank v)
/-- Campaign T8D (NF17): the raw radix-8 digits of chains 53 (bits 119..121), 51 (122..124) and 52 (125..127). -/
def tailWeight (v : Digest) : Nat := v.toNat / 2 ^ 119 % 8 + v.toNat / 2 ^ 122 % 8 + v.toNat / 2 ^ 125 % 8
def topLookupSum (v : Digest) : Nat := ((rankDigits v).map rankLookup).sum + tailWeight v
def rankCredit (r : Nat) : Nat :=
  (if r % 5 = 3 then 1 else 0) + (if r / 5 % 5 = 3 then 1 else 0) + (if r / 25 % 5 = 3 then 1 else 0)
def tableByte (i : Nat) : BitVec 8 := BitVec.ofNat 8 <|
  if i < 128 then rankLookup i
  else if i < 628 then if (i - 128) % 4 < 3 then rankDigit ((i - 128) / 4) ((i - 128) % 4)
    else rankCredit ((i - 128) / 4)
  else 0
/-- Campaign T8D: the flipped code of `T3.dummyTop` (30 threes, 21 twos, [4,4,5]) stored at TOP_DATA + 632. -/
def dummyDigestNat : Nat := 237591654474925061491741830032548916957
def cfByte (flag : Nat) (i : Nat) : BitVec 8 := BitVec.ofNat 8 <|
  if i = 631 then flag
  else if 632 ≤ i ∧ i < 648 then dummyDigestNat / 256 ^ (i - 632) % 256
  else 0
def CfTableOK (flag : Nat) (s : MachineState) : Prop :=
  ∀ i, 628 ≤ i → i < 648 → s.getByte (BitVec.ofNat 64 (TOP_DATA + i)) = cfByte flag i
theorem CfTableOK.frame {flag : Nat} {s t : MachineState} {W : Nat → Prop} (h : CfTableOK flag s)
    (hf : Frame s t W) (hd : ∀ i, 628 ≤ i → i < 648 → ¬ W ((TOP_DATA + i) / 8 * 8)) : CfTableOK flag t := by
  intro i hi hj
  exact (hf.getByte (by unfold TOP_DATA; omega) (hd i hi hj)).trans (h i hi hj)
def SumTableOK (s : MachineState) : Prop :=
  ∀ i, i < 128 → s.getByte (BitVec.ofNat 64 (TOP_DATA + i)) = BitVec.ofNat 8 (rankLookup i)
def TableOK (s : MachineState) : Prop :=
  ∀ i, i < 628 → s.getByte (BitVec.ofNat 64 (TOP_DATA + i)) = tableByte i
theorem TableOK.sum {s : MachineState} (h : TableOK s) : SumTableOK s := by
  intro i hi
  rw [h i (by omega)]
  simp [tableByte, hi]
theorem TableOK.frame {s t : MachineState} {W : Nat → Prop} (h : TableOK s)
    (hf : Frame s t W) (hd : ∀ i, i < 628 → ¬ W ((TOP_DATA + i) / 8 * 8)) : TableOK t := by
  intro i hi
  exact (hf.getByte (by unfold TOP_DATA; omega) (hd i hi)).trans (h i hi)
theorem SumTableOK.frame {s t : MachineState} {W : Nat → Prop} (h : SumTableOK s)
    (hf : Frame s t W) (hd : ∀ i, i < 128 → ¬ W ((TOP_DATA + i) / 8 * 8)) : SumTableOK t := by
  intro i hi
  exact (hf.getByte (by unfold TOP_DATA; omega) (hd i hi)).trans (h i hi)
theorem rankWeight_le (r : Nat) : rankWeight r ≤ 12 := by unfold rankWeight; omega
theorem rankLookup_le (r : Nat) : rankLookup r ≤ 255 := by
  unfold rankLookup
  split_ifs
  · have := rankWeight_le r; omega
  · omega
theorem rankLookup_bad (r : Nat) (h : ¬ r < 125) : rankLookup r = 255 := by simp [rankLookup, h]


private theorem map_sum_entry_le {xs : List Nat} (f : Nat → Nat) {r : Nat} (h : r ∈ xs) :
    f r ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    simp only [List.mem_cons] at h
    simp only [List.map_cons, List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

end SigGolfCandidate.T3M.Search

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
/-- Campaign T51: the canonical search reads only the choice flag byte (TOP_DATA + 631) of the cf block (the dummy
word at 632..647 of the T51 sign image is the T51 one, `[3]*50 ++ [2]`). -/
def CfFlagOK (flag : Nat) (s : MachineState) : Prop :=
  s.getByte (BitVec.ofNat 64 (TOP_DATA + 631)) = BitVec.ofNat 8 flag
theorem CfFlagOK.frame {flag : Nat} {s t : MachineState} {W : Nat → Prop} (h : CfFlagOK flag s)
    (hf : Frame s t W) (hd : ∀ i, 628 ≤ i → i < 648 → ¬ W ((TOP_DATA + i) / 8 * 8)) : CfFlagOK flag t :=
  (hf.getByte (by unfold TOP_DATA; omega) (hd 631 (by omega) (by omega))).trans h
theorem CfTableOK.flagOK {flag : Nat} {s : MachineState} (h : CfTableOK flag s) : CfFlagOK flag s := by
  unfold CfFlagOK; rw [h 631 (by omega) (by omega)]; unfold cfByte; rw [if_pos rfl]
instance {flag : Nat} {s : MachineState} : Coe (CfTableOK flag s) (CfFlagOK flag s) := ⟨CfTableOK.flagOK⟩
end SigGolfCandidate.T3M.Search

/-! ## T51 top-trial kernel: tables and the spec side (campaign T51, stream SIGNA)
`t51/sign/kernel/{t51kernel.py, t51tables.py}`, PINNED P2/P6. One kernel for sign and expand. -/
section
namespace SigGolfCandidate.T3M.Search.T51
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-! ### Packed tables (`t51tables.py`, 1892 bytes = 473 little-endian 32-bit entries)
Lanes: bits 0..7 score `wc + 4 safe`, 8..13 zero digits, 14..17 `[d_0 = max]` (r6 only), 18..21
`[d_0 + d_1 + d_2 < 3]` (r5 only), 22..30 weight (digit sum; INVALID = weight 256 only).
`T6C` entries 0..295 = `[INVALID]*40 ++ E6(0..215) ++ [INVALID]*40`, `T5` entries 296..423 (`T5[raw7]`, INVALID for
`raw7 < 3`, else `E5(127 - raw7)`), `E7` entries 424..472 (`E7[raw7 - 79] = E7(127 - raw7)`, the r7 pair). -/
def tInvalid : Nat := 256 * 2 ^ 22
def tScore (m a b c : Nat) : Nat :=
  (if a + 1 = m then 1 else 0) + (if b + 1 = m then 1 else 0) + (if c + 1 = m then 1 else 0) +
    4 * ((if a = m ∧ b = m then 1 else 0) + (if b = m ∧ c = m then 1 else 0))
def tZeros (a b c : Nat) : Nat := (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) + (if c = 0 then 1 else 0)
def entry6 (r : Nat) : Nat :=
  (r % 6 + r / 6 % 6 + r / 36) * 2 ^ 22 + (if r % 6 = 5 then 2 ^ 14 else 0) +
    tZeros (r % 6) (r / 6 % 6) (r / 36) * 2 ^ 8 + tScore 5 (r % 6) (r / 6 % 6) (r / 36)
def entry5 (r : Nat) : Nat :=
  (r % 5 + r / 5 % 5 + r / 25) * 2 ^ 22 + (if r % 5 + r / 5 % 5 + r / 25 < 3 then 2 ^ 18 else 0) +
    tZeros (r % 5) (r / 5 % 5) (r / 25) * 2 ^ 8 + tScore 4 (r % 5) (r / 5 % 5) (r / 25)
/-- The r7 pair entry of rank `r = d48 + 7 d49` (`r < 49`). -/
def entry7 (r : Nat) : Nat :=
  (r % 7 + r / 7) * 2 ^ 22 + ((if r % 7 = 0 then 1 else 0) + (if r / 7 = 0 then 1 else 0)) * 2 ^ 8 +
    ((if r % 7 = 5 then 1 else 0) + (if r / 7 = 5 then 1 else 0) + 4 * (if r % 7 = 6 ∧ r / 7 = 6 then 1 else 0))
/-- Entry `k` (`k < 473`) of the packed block. -/
def tEntry (k : Nat) : Nat :=
  if k < 40 then tInvalid else if k < 256 then entry6 (k - 40) else if k < 299 then tInvalid
  else if k < 424 then entry5 (127 - (k - 296)) else entry7 (48 - (k - 424))
/-- Byte `i` of the 1892-byte block. -/
def tByte (i : Nat) : BitVec 8 := BitVec.ofNat 8 (tEntry (i / 4) / 256 ^ (i % 4) % 256)
/-- The table block at `blk`, as the 473 32-bit words the kernel's `lwu` reads. -/
def T51TableW (blk : Nat) (s : MachineState) : Prop :=
  ∀ f, f < 473 → s.getWord32 (BitVec.ofNat 64 (blk + 4 * f)) = BitVec.ofNat 32 (tEntry f)
theorem T51TableW.frame {blk : Nat} {s t : MachineState} {W : Nat → Prop} (h : T51TableW blk s)
    (hf : Frame s t W) (hb8 : blk % 8 = 0) (hb : blk + 1896 < 2 ^ 64) (hd : ∀ k, k < 237 → ¬ W (blk + 8 * k)) :
    T51TableW blk t := by
  intro f hf'
  have h1 := h f hf'
  unfold MachineState.getWord32 at h1 ⊢
  have hal : alignToDword (BitVec.ofNat 64 (blk + 4 * f)) = BitVec.ofNat 64 (blk + 8 * (f / 2)) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]; omega
  rw [hal] at h1 ⊢
  rw [hf.get (by omega) (hd (f / 2) (by omega))]
  exact h1
theorem tEntry_lt : ∀ f < 473, tEntry f < 2 ^ 32 := by decide +kernel
/-- The table block from its 1892 bytes (`tByte`), e.g. the expand data at `0xFF9E00` (`Search.expandData_t51`) or the
sign data at `0xFFF800` (`Search.signData_t51`). -/
theorem T51TableW.of_bytes {blk : Nat} {s : MachineState} (hblk : blk % 8 = 0) (hb : blk + 1896 < 2 ^ 64)
    (h : ∀ i, i < 1892 → s.getByte (BitVec.ofNat 64 (blk + i)) = tByte i) : T51TableW blk s := by
  intro f hf
  have hw : ∀ k, k < 4 → (s.getMem (BitVec.ofNat 64 (blk + 8 * (f / 2)))).toNat / 2 ^ (8 * (4 * (f % 2) + k)) % 256 =
      tEntry f / 256 ^ k % 256 := by
    intro k hk
    have hbk := h (4 * f + k) (by omega)
    rw [getByte_eq_word s (blk + (4 * f + k)) (by omega),
      show (blk + (4 * f + k)) / 8 * 8 = blk + 8 * (f / 2) by omega,
      show (blk + (4 * f + k)) % 8 = 4 * (f % 2) + k by omega] at hbk
    have := congrArg BitVec.toNat hbk
    simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, tByte, BitVec.toNat_ofNat] at this
    rw [show (4 * f + k) / 4 = f by omega, show (4 * f + k) % 4 = k by omega] at this
    rw [show (256 : Nat) = 2 ^ 8 by norm_num] at this ⊢
    rw [show 8 * (4 * (f % 2) + k) = (4 * (f % 2) + k) * 8 by ring]
    simpa [Nat.mod_mod_of_dvd] using this
  unfold MachineState.getWord32
  have hal : alignToDword (BitVec.ofNat 64 (blk + 4 * f)) = BitVec.ofNat 64 (blk + 8 * (f / 2)) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]; omega
  have hbo : byteOffset (BitVec.ofNat 64 (blk + 4 * f)) / 4 = f % 2 := by
    rw [byteOffset_eq, toNat_ofNat_lt (by omega)]; omega
  rw [hal, hbo]
  apply BitVec.eq_of_toNat_eq
  have he := tEntry_lt f hf
  generalize hX : (s.getMem (BitVec.ofNat 64 (blk + 8 * (f / 2)))).toNat = X at hw
  have h0 := hw 0 (by norm_num); have h1 := hw 1 (by norm_num); have h2 := hw 2 (by norm_num)
  have h3 := hw 3 (by norm_num)
  simp only [extractWord32, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, hX, Nat.mod_eq_of_lt he]
  rcases Nat.mod_two_eq_zero_or_one f with hm | hm <;> rw [hm] at h0 h1 h2 h3 ⊢ <;>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.add_zero, pow_zero, Nat.div_one] at h0 h1 h2 h3 ⊢ <;>
    omega
/-- The table block survives a doubleword copy `src -> dst` (237 doublewords), e.g. the expand's KCOPY
(`0xFF9E00 -> 0xA0000`, `KCopy.kcopy_spec`). -/
theorem T51TableW.of_copy {src dst : Nat} {s t : MachineState} (h : T51TableW src s) (hs8 : src % 8 = 0)
    (hd8 : dst % 8 = 0) (hs : src + 1896 < 2 ^ 64) (hd : dst + 1896 < 2 ^ 64)
    (hc : ∀ k, k < 237 → t.getMem (BitVec.ofNat 64 (dst + 8 * k)) = s.getMem (BitVec.ofNat 64 (src + 8 * k))) :
    T51TableW dst t := by
  intro f hf
  have h1 := h f hf
  unfold MachineState.getWord32 at h1 ⊢
  have hal : ∀ b, b % 8 = 0 → b + 1896 < 2 ^ 64 →
      alignToDword (BitVec.ofNat 64 (b + 4 * f)) = BitVec.ofNat 64 (b + 8 * (f / 2)) := by
    intro b hb8 hb
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]; omega
  have hbo : ∀ b, b % 8 = 0 → b + 1896 < 2 ^ 64 → byteOffset (BitVec.ofNat 64 (b + 4 * f)) / 4 = f % 2 := by
    intro b hb8 hb
    rw [byteOffset_eq, toNat_ofNat_lt (by omega)]; omega
  rw [hal src hs8 hs, hbo src hs8 hs] at h1
  rw [hal dst hd8 hd, hbo dst hd8 hd, hc (f / 2) (by omega)]
  exact h1
/-! ### Lanes of the packed entries -/
def eW (f : Nat) : Nat := tEntry f / 2 ^ 22
def eP (f : Nat) : Nat := tEntry f / 2 ^ 18 % 16
def eD (f : Nat) : Nat := tEntry f / 2 ^ 14 % 16
def eZ (f : Nat) : Nat := tEntry f / 2 ^ 8 % 64
def eS (f : Nat) : Nat := tEntry f % 256
theorem tEntry_lanes : ∀ f < 473,
    tEntry f = eW f * 2 ^ 22 + eP f * 2 ^ 18 + eD f * 2 ^ 14 + eZ f * 2 ^ 8 + eS f ∧
      eW f ≤ 256 ∧ eP f ≤ 1 ∧ eD f ≤ 1 ∧ eZ f ≤ 3 ∧ eS f ≤ 8 := by
  decide +kernel
/-- r6 entry of rank `r` (`r < 216`): table index `40 + r`. -/
theorem lanes6 : ∀ r < 216,
    eW (40 + r) = r % 6 + r / 6 % 6 + r / 36 ∧ eZ (40 + r) = tZeros (r % 6) (r / 6 % 6) (r / 36) ∧
      eS (40 + r) = tScore 5 (r % 6) (r / 6 % 6) (r / 36) ∧ eD (40 + r) = (if r % 6 = 5 then 1 else 0) ∧
      eP (40 + r) = 0 := by
  decide +kernel
/-- r5 entry of raw field `raw7 ≥ 3` (rank `127 - raw7 < 125`): table index `296 + raw7`. -/
theorem lanes5 : ∀ raw < 128, 3 ≤ raw →
    eW (296 + raw) = (127 - raw) % 5 + (127 - raw) / 5 % 5 + (127 - raw) / 25 ∧
      eZ (296 + raw) = tZeros ((127 - raw) % 5) ((127 - raw) / 5 % 5) ((127 - raw) / 25) ∧
      eS (296 + raw) = tScore 4 ((127 - raw) % 5) ((127 - raw) / 5 % 5) ((127 - raw) / 25) ∧
      eP (296 + raw) = (if (127 - raw) % 5 + (127 - raw) / 5 % 5 + (127 - raw) / 25 < 3 then 1 else 0) ∧
      eD (296 + raw) = 0 := by
  decide +kernel
/-- r7 entry of raw field `raw7 ≥ 79` (rank `k = 127 - raw7 < 49`): table index `345 + raw7`. -/
theorem lanes7 : ∀ raw < 128, 79 ≤ raw →
    eW (345 + raw) = (127 - raw) % 7 + (127 - raw) / 7 ∧
      eZ (345 + raw) = (if (127 - raw) % 7 = 0 then 1 else 0) + (if (127 - raw) / 7 = 0 then 1 else 0) ∧
      eS (345 + raw) = (if (127 - raw) % 7 + 1 = 6 then 1 else 0) + (if (127 - raw) / 7 + 1 = 6 then 1 else 0) +
        4 * (if (127 - raw) % 7 = 6 ∧ (127 - raw) / 7 = 6 then 1 else 0) ∧
      eP (345 + raw) = 0 ∧ eD (345 + raw) = 0 ∧ (127 - raw) / 7 < 7 := by
  decide +kernel
theorem e_valid0 : ∀ raw < 256, (eW raw = 256 ↔ raw < 40) := by decide +kernel
theorem e_valid6 : ∀ raw < 256, (eW (40 + raw) = 256 ↔ 216 ≤ raw) := by decide +kernel
theorem e_valid5 : ∀ raw < 128, (eW (296 + raw) = 256 ↔ raw < 3) := by decide +kernel
theorem e_r6P : ∀ f < 296, eP f = 0 := by decide +kernel
theorem e_r5D : ∀ f < 473, 296 ≤ f → eD f = 0 := by decide +kernel
theorem e_d0 : ∀ f < 473, tEntry f / 2 ^ 12 &&& 4 = 4 * eD f := by decide +kernel
/-! ### Spec fields vs raw half bits -/
theorem topCode_testBit (v : Digest) (j : Nat) :
    (T3.topCode v).testBit j = (v.toNat.testBit j ^^ decide (56 ≤ j ∧ j < 112)) := by
  unfold T3.topCode T3.topFlip T3.topMask
  rw [BitVec.toNat_xor, Nat.testBit_xor, BitVec.toNat_ofNat]
  congr 1
  by_cases hj : j < 128
  · rw [Nat.mod_eq_of_lt (by norm_num), show (2 : Nat) ^ 112 - 2 ^ 56 = (2 ^ 56 - 1) * 2 ^ 56 by norm_num,
      ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases h1 : 56 ≤ j
    · simp only [h1, decide_true, Bool.true_and]
      by_cases h2 : j < 112
      · simp [h2, show j - 56 < 56 by omega]
      · simp [h2, show ¬ j - 56 < 56 by omega]
    · simp [h1]
  · rw [Nat.mod_eq_of_lt (by norm_num)]
    simp only [show ¬ (56 ≤ j ∧ j < 112) by omega, decide_false]
    apply Nat.testBit_eq_false_of_lt
    calc 2 ^ 112 - 2 ^ 56 < 2 ^ 112 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
theorem r6Raw_eq (v : Digest) (g : Nat) (hg : g ≤ 8) :
    T3.r6Raw v g = v.toNat / 2 ^ T3.r6Shift g % 256 := by
  unfold T3.r6Raw
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (256 : Nat) = 2 ^ 8 by norm_num]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, topCode_testBit]
  by_cases hi : i < 8
  · have : ¬ (56 ≤ i + T3.r6Shift g ∧ i + T3.r6Shift g < 112) := by
      unfold T3.r6Shift; split_ifs <;> omega
    simp [hi, this]
  · simp [hi]
theorem flip7 (v : Digest) (S : Nat) (hS : 56 ≤ S ∧ S + 7 ≤ 112) :
    T3.topCode v / 2 ^ S % 128 = 127 - v.toNat / 2 ^ S % 128 := by
  have key : T3.topCode v / 2 ^ S % 2 ^ 7 = (v.toNat / 2 ^ S % 2 ^ 7) ^^^ (2 ^ 7 - 1) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, topCode_testBit, Nat.testBit_xor,
      Nat.testBit_two_pow_sub_one]
    by_cases hi : i < 7
    · simp [hi, show 56 ≤ i + S ∧ i + S < 112 by omega]
    · simp [hi]
  change T3.topCode v / 2 ^ S % 2 ^ 7 = 127 - v.toNat / 2 ^ S % 2 ^ 7
  rw [key]
  have hlt : v.toNat / 2 ^ S % 2 ^ 7 < 128 := Nat.mod_lt _ (by norm_num)
  generalize v.toNat / 2 ^ S % 2 ^ 7 = n at hlt ⊢
  have : ∀ n < 128, n ^^^ (2 ^ 7 - 1) = 127 - n := by decide
  exact this n hlt
theorem r5Rank_eq (v : Digest) (q : Nat) (hq : 9 ≤ q ∧ q ≤ 15) :
    T3.r5Rank v q = 127 - v.toNat / 2 ^ (7 * q) % 128 := flip7 v (7 * q) (by omega)
theorem r7Rank_eq (v : Digest) : T3.r7Rank v = 127 - v.toNat / 2 ^ 56 % 128 := flip7 v 56 (by omega)
/-! ### Decoded top words -/
theorem decode_top_eq {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    T3.topRanksValid v = true ∧ (T3.dataDigits 0 v).sum ≤ 152 ∧ 152 - (T3.dataDigits 0 v).sum < 6 ∧
      ds = T3.dataDigits 0 v ++ [152 - (T3.dataDigits 0 v).sum] := by
  unfold WCT9.CanonicalPolicy.decode WCT9.CanonicalPolicy.normalLayer T3.decode at h
  simp only [if_true] at h
  split_ifs at h with h1 h2
  · simp only [Option.some.injEq] at h
    exact ⟨h2.1, h2.2.1, h2.2.2, h.symm⟩
theorem decode_length {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    ds.length = 51 := by
  obtain ⟨_, _, _, rfl⟩ := decode_top_eq h
  simp [T3.dataDigits, T3.dataCount]
theorem ds_getD_data {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) (i : Nat)
    (hi : i < 50) : ds.getD i 0 = T3.coreDigit 0 v i := by
  obtain ⟨_, _, _, rfl⟩ := decode_top_eq h
  rw [List.getD_append _ _ _ _ (by simp [T3.dataDigits, T3.dataCount]; omega)]
  simp [T3.dataDigits, T3.dataCount, List.getD_eq_getElem?_getD, hi]
theorem ds_getD_50 {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    ds.getD 50 0 = 152 - (T3.dataDigits 0 v).sum := by
  obtain ⟨_, _, _, rfl⟩ := decode_top_eq h
  rw [List.getD_append_right _ _ _ _ (by simp [T3.dataDigits, T3.dataCount])]
  simp [T3.dataDigits, T3.dataCount]
/-! ### Regrouping the 51 chains: 16 triples, the r7 pair and the checksum -/
theorem sum_triples (f : Nat → Nat) (n : Nat) :
    ∑ i ∈ Finset.range (3 * n), f i = ∑ g ∈ Finset.range n, (f (3 * g) + f (3 * g + 1) + f (3 * g + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring
theorem length_filter_range' (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    ((List.range n).filter fun i => decide (p i)).length = ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]
theorem sum51 (f : Nat → Nat) :
    ∑ i ∈ Finset.range 51, f i =
      ∑ g ∈ Finset.range 16, (f (3 * g) + f (3 * g + 1) + f (3 * g + 2)) + (f 48 + f 49) + f 50 := by
  rw [show (51 : Nat) = 3 * 16 + 1 + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, sum_triples]
  ring
theorem sum50 (f : Nat → Nat) :
    ∑ i ∈ Finset.range 50, f i =
      ∑ g ∈ Finset.range 16, (f (3 * g) + f (3 * g + 1) + f (3 * g + 2)) + (f 48 + f 49) := by
  rw [show (50 : Nat) = 3 * 16 + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ, sum_triples]
  ring
theorem maxDigit_r6 (i : Nat) (hi : i < 27) : T3.maxDigit 0 i = 5 := by simp [T3.maxDigit, hi]
theorem maxDigit_r5 (i : Nat) (hi : 27 ≤ i ∧ i < 48) : T3.maxDigit 0 i = 4 := by
  simp [T3.maxDigit, show ¬ i < 27 by omega, hi.2]
/-- `wordCredit` of a top word: 16 triples, the r7 pair and the checksum term. -/
theorem wordCredit_top (ds : List Nat) :
    WCT9.wordCredit 0 ds = ∑ g ∈ Finset.range 16,
      ((if ds.getD (3 * g) 0 + 1 = T3.maxDigit 0 (3 * g) then 1 else 0) +
       (if ds.getD (3 * g + 1) 0 + 1 = T3.maxDigit 0 (3 * g + 1) then 1 else 0) +
       (if ds.getD (3 * g + 2) 0 + 1 = T3.maxDigit 0 (3 * g + 2) then 1 else 0)) +
      ((if ds.getD 48 0 + 1 = 6 then 1 else 0) + (if ds.getD 49 0 + 1 = 6 then 1 else 0)) +
      (if ds.getD 50 0 + 1 = 5 then 1 else 0) := by
  unfold WCT9.wordCredit
  rw [length_filter_range', show T3.chainCount 0 = 51 from rfl, sum51]
  rfl
theorem safe_top_mid (ds : List Nat) (g : Nat) (hg : g < 16) (j : Nat) (hj : j = 1 ∨ j = 2) :
    WCT9.safeZeroCopy 0 ds (3 * g + j) ↔
      ds.getD (3 * g + j) 0 = T3.maxDigit 0 (3 * g + j) ∧ ds.getD (3 * g + j - 1) 0 = T3.maxDigit 0 (3 * g + j - 1) := by
  unfold WCT9.safeZeroCopy
  constructor
  · rintro ⟨h1, h2 | ⟨h3, _⟩ | ⟨_, _, _, h4⟩⟩
    · omega
    · exact absurd rfl h3
    · exact ⟨h1, h4⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩
theorem safe_top_first (ds : List Nat) (g : Nat) :
    WCT9.safeZeroCopy 0 ds (3 * g) ↔ g = 0 ∧ ds.getD 0 0 = 5 := by
  unfold WCT9.safeZeroCopy
  constructor
  · rintro ⟨h1, h2 | ⟨h3, _⟩ | ⟨_, h5, _⟩⟩
    · have hg : g = 0 := by omega
      subst hg; exact ⟨rfl, by simpa [T3.maxDigit] using h1⟩
    · exact absurd rfl h3
    · omega
  · rintro ⟨rfl, h⟩
    exact ⟨by simpa [T3.maxDigit] using h, Or.inl rfl⟩
theorem safe_top_49 (ds : List Nat) :
    WCT9.safeZeroCopy 0 ds 49 ↔ ds.getD 48 0 = 6 ∧ ds.getD 49 0 = 6 := by
  unfold WCT9.safeZeroCopy
  constructor
  · rintro ⟨h1, h2 | ⟨h3, _⟩ | ⟨_, _, _, h4⟩⟩
    · omega
    · exact absurd rfl h3
    · exact ⟨by simpa [T3.maxDigit] using h4, by simpa [T3.maxDigit] using h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa [T3.maxDigit] using h2, Or.inr (Or.inr ⟨by omega, by omega, by omega,
      by simpa [T3.maxDigit] using h1⟩)⟩
theorem safe_top_50 (ds : List Nat) : ¬ WCT9.safeZeroCopy 0 ds 50 := by
  unfold WCT9.safeZeroCopy
  rintro ⟨_, h2 | ⟨h3, _⟩ | ⟨_, _, h5, _⟩⟩
  · omega
  · exact h3 rfl
  · exact h5 ⟨rfl, rfl⟩
/-- `savedCopies` of a top word: the i = 0 copy, the in-triple copies and the r7 pair copy (chain 49). -/
theorem savedCopies_top (ds : List Nat) :
    WCT9.savedCopies 0 ds = (if ds.getD 0 0 = 5 then 1 else 0) + ∑ g ∈ Finset.range 16,
      ((if ds.getD (3 * g) 0 = T3.maxDigit 0 (3 * g) ∧ ds.getD (3 * g + 1) 0 = T3.maxDigit 0 (3 * g + 1)
          then 1 else 0) +
       (if ds.getD (3 * g + 1) 0 = T3.maxDigit 0 (3 * g + 1) ∧ ds.getD (3 * g + 2) 0 = T3.maxDigit 0 (3 * g + 2)
          then 1 else 0)) + (if ds.getD 48 0 = 6 ∧ ds.getD 49 0 = 6 then 1 else 0) := by
  unfold WCT9.savedCopies
  rw [length_filter_range', show T3.chainCount 0 = 51 from rfl, sum51, if_neg (safe_top_50 ds), add_zero,
    if_congr (safe_top_49 ds) rfl rfl,
    if_neg (show ¬ WCT9.safeZeroCopy 0 ds 48 from fun h => by
      have := (safe_top_first ds 16).1 h; omega)]
  have h1 : ∀ g ∈ Finset.range 16, (if WCT9.safeZeroCopy 0 ds (3 * g + 1) then 1 else 0) =
      (if ds.getD (3 * g) 0 = T3.maxDigit 0 (3 * g) ∧ ds.getD (3 * g + 1) 0 = T3.maxDigit 0 (3 * g + 1)
        then 1 else 0) := fun g hg => by
    rw [if_congr ((safe_top_mid ds g (Finset.mem_range.1 hg) 1 (Or.inl rfl)).trans and_comm) rfl rfl]; rfl
  have h2 : ∀ g ∈ Finset.range 16, (if WCT9.safeZeroCopy 0 ds (3 * g + 2) then 1 else 0) =
      (if ds.getD (3 * g + 1) 0 = T3.maxDigit 0 (3 * g + 1) ∧ ds.getD (3 * g + 2) 0 = T3.maxDigit 0 (3 * g + 2)
        then 1 else 0) := fun g hg => by
    rw [if_congr ((safe_top_mid ds g (Finset.mem_range.1 hg) 2 (Or.inr rfl)).trans and_comm) rfl rfl]; rfl
  have h0 : ∀ g, (if WCT9.safeZeroCopy 0 ds (3 * g) then 1 else 0) =
      (if g = 0 ∧ ds.getD 0 0 = 5 then 1 else 0) := fun g => if_congr (safe_top_first ds g) rfl rfl
  rw [Finset.sum_congr rfl (fun g hg => by rw [h0 g, h1 g hg, h2 g hg])]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun g => if g = 0 ∧ ds.getD 0 0 = 5 then 1 else 0)]
  simp only [Nat.succ_ne_zero, false_and, if_false, Finset.sum_const_zero, zero_add, true_and]
  ring
theorem filter_length_sum (l : List Nat) (p : Nat → Bool) :
    (l.filter p).length = ∑ i ∈ Finset.range l.length, if p (l.getD i 0) then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.filter_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    by_cases h : p a <;> simp [h, ih] <;> ring
/-- Zero digits of a 51-digit top word. -/
theorem zeros_top (ds : List Nat) (hl : ds.length = 51) :
    (ds.filter (· = 0)).length = ∑ g ∈ Finset.range 16,
      ((if ds.getD (3 * g) 0 = 0 then 1 else 0) + (if ds.getD (3 * g + 1) 0 = 0 then 1 else 0) +
       (if ds.getD (3 * g + 2) 0 = 0 then 1 else 0)) +
      ((if ds.getD 48 0 = 0 then 1 else 0) + (if ds.getD 49 0 = 0 then 1 else 0)) +
      (if ds.getD 50 0 = 0 then 1 else 0) := by
  rw [filter_length_sum, hl, sum51]
  simp only [decide_eq_true_eq]
/-- The T51 dispatch penalty: the penalised r5 rows q = 10, 11, 12. -/
theorem penalty_top (ds : List Nat) :
    WCT9.topDispatchPenalty ds =
      (if ds.getD 30 0 + ds.getD 31 0 + ds.getD 32 0 < 3 then 1 else 0) +
      (if ds.getD 33 0 + ds.getD 34 0 + ds.getD 35 0 < 3 then 1 else 0) +
      (if ds.getD 36 0 + ds.getD 37 0 + ds.getD 38 0 < 3 then 1 else 0) := by
  unfold WCT9.topDispatchPenalty
  rw [length_filter_range']
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
/-! ### Groups in chain order: `j < 9` r6 group `g_j`, `9 ≤ j < 16` r5 group `q_j`, `j = 16` the r7 pair -/
/-- Table index read for group `j` of a half `v` (the r7 index is meaningful only for `raw7 ≥ 79`). -/
def gIdx (v : Digest) (j : Nat) : Nat :=
  if j = 0 then v.toNat % 256
  else if j < 9 then 40 + v.toNat / 2 ^ T3.r6Shift j % 256
  else if j < 16 then 296 + v.toNat / 2 ^ (7 * j) % 128
  else 345 + v.toNat / 2 ^ 56 % 128
theorem gIdx_lt (v : Digest) (j : Nat) : gIdx v j < 473 := by
  unfold gIdx; split_ifs <;> omega
theorem coreDigit_r6g (v : Digest) (j k : Nat) (hj : j < 9) (hk : k < 3) :
    T3.coreDigit 0 v (3 * j + k) = T3.r6Rank v j / 6 ^ k % 6 := by
  unfold T3.coreDigit
  simp only [if_true, show 3 * j + k < 27 by omega, show (3 * j + k) / 3 = j by omega,
    show (3 * j + k) % 3 = k by omega]
theorem coreDigit_r5g (v : Digest) (j k : Nat) (hj : 9 ≤ j ∧ j < 16) (hk : k < 3) :
    T3.coreDigit 0 v (3 * j + k) = T3.r5Rank v j / 5 ^ k % 5 := by
  unfold T3.coreDigit
  simp only [if_true, show ¬ 3 * j + k < 27 by omega, show 3 * j + k < 48 by omega, if_false,
    show (3 * j + k) / 3 = j by omega, show (3 * j + k) % 3 = k by omega]
theorem coreDigit_48 (v : Digest) : T3.coreDigit 0 v 48 = T3.r7Rank v % 7 := by
  unfold T3.coreDigit; simp
theorem coreDigit_49 (v : Digest) : T3.coreDigit 0 v 49 = T3.r7Rank v / 7 % 7 := by
  unfold T3.coreDigit; simp
theorem r6Raw_idx (v : Digest) (j : Nat) (h1 : 1 ≤ j) (h8 : j < 9) : gIdx v j = 40 + T3.r6Raw v j := by
  unfold gIdx; rw [if_neg (by omega), if_pos h8, r6Raw_eq v j (by omega)]
/-- The kernel index of an r6 group is `40 + rank` and its validity is `rank < 216`. -/
theorem gIdx_r6 (v : Digest) (j : Nat) (hj : j < 9) :
    (T3.r6Valid v j = true ↔ eW (gIdx v j) ≠ 256) ∧
      (T3.r6Valid v j = true → gIdx v j = 40 + T3.r6Rank v j ∧ T3.r6Rank v j < 216) := by
  have hr := r6Raw_eq v j (by omega)
  unfold T3.r6Valid T3.r6Rank
  by_cases h0 : j = 0
  · subst h0
    simp only [if_true, decide_eq_true_eq]
    rw [hr, show T3.r6Shift 0 = 0 from rfl, pow_zero, Nat.div_one]
    have hlt : v.toNat % 256 < 256 := Nat.mod_lt _ (by norm_num)
    have := e_valid0 _ hlt
    have hg : gIdx v 0 = v.toNat % 256 := rfl
    rw [hg]
    constructor
    · constructor
      · intro h; rw [Ne, this]; omega
      · intro h; rw [Ne, this] at h; omega
    · intro h; constructor <;> omega
  · simp only [h0, if_false, decide_eq_true_eq]
    rw [r6Raw_idx v j (by omega) hj]
    have hlt : T3.r6Raw v j < 256 := by rw [hr]; exact Nat.mod_lt _ (by norm_num)
    have := e_valid6 _ hlt
    refine ⟨⟨fun h => by rw [Ne, this]; omega, fun h => by rw [Ne, this] at h; omega⟩, fun h => ⟨rfl, h⟩⟩
theorem gIdx_r5 (v : Digest) (j : Nat) (hj : 9 ≤ j ∧ j < 16) :
    (T3.r5Rank v j < 125 ↔ eW (gIdx v j) ≠ 256) ∧ gIdx v j = 296 + (127 - T3.r5Rank v j) ∧
      T3.r5Rank v j ≤ 127 := by
  have hr := r5Rank_eq v j ⟨hj.1, by omega⟩
  have hlt : v.toNat / 2 ^ (7 * j) % 128 < 128 := Nat.mod_lt _ (by norm_num)
  unfold gIdx
  simp only [show j ≠ 0 by omega, show ¬ j < 9 by omega, hj.2, if_false, if_true]
  have := e_valid5 _ hlt
  rw [hr]
  refine ⟨⟨fun h => by rw [Ne, this]; omega, fun h => by rw [Ne, this] at h; omega⟩, by omega, by omega⟩
theorem gIdx_r7 (v : Digest) :
    (T3.r7Rank v < 49 ↔ 79 ≤ v.toNat / 2 ^ 56 % 128) ∧ gIdx v 16 = 345 + v.toNat / 2 ^ 56 % 128 ∧
      T3.r7Rank v = 127 - v.toNat / 2 ^ 56 % 128 := by
  have hr := r7Rank_eq v
  have hlt : v.toNat / 2 ^ 56 % 128 < 128 := Nat.mod_lt _ (by norm_num)
  refine ⟨by rw [hr]; omega, rfl, hr⟩
theorem valid_groups {v : Digest} (hv : T3.topRanksValid v = true) :
    (∀ j < 9, T3.r6Valid v j = true) ∧ (∀ j, 9 ≤ j → j < 16 → T3.r5Rank v j < 125) ∧ T3.r7Rank v < 49 := by
  unfold T3.topRanksValid at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, List.mem_range'] at hv
  obtain ⟨⟨h1, h2⟩, h3⟩ := hv
  refine ⟨h1, fun j hj1 hj2 => ?_, h3⟩
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 7 ∧ j = 9 + i := ⟨j - 9, by omega, by omega⟩
  simpa using h2 (9 + i) ⟨i, hi, by ring⟩
/-- Lanes of the entry read for triple group `j < 16` of a valid half, in digit terms. -/
theorem group_lanes {v : Digest} (hv : T3.topRanksValid v = true) (j : Nat) (hj : j < 16) :
    let d := T3.coreDigit 0 v
    let m := T3.maxDigit 0
    eW (gIdx v j) = d (3 * j) + d (3 * j + 1) + d (3 * j + 2) ∧
    eZ (gIdx v j) = (if d (3 * j) = 0 then 1 else 0) + (if d (3 * j + 1) = 0 then 1 else 0) +
      (if d (3 * j + 2) = 0 then 1 else 0) ∧
    eS (gIdx v j) = (if d (3 * j) + 1 = m (3 * j) then 1 else 0) + (if d (3 * j + 1) + 1 = m (3 * j + 1) then 1 else 0) +
      (if d (3 * j + 2) + 1 = m (3 * j + 2) then 1 else 0) +
      4 * ((if d (3 * j) = m (3 * j) ∧ d (3 * j + 1) = m (3 * j + 1) then 1 else 0) +
        (if d (3 * j + 1) = m (3 * j + 1) ∧ d (3 * j + 2) = m (3 * j + 2) then 1 else 0)) ∧
    eP (gIdx v j) = (if 9 ≤ j ∧ d (3 * j) + d (3 * j + 1) + d (3 * j + 2) < 3 then 1 else 0) ∧
    (j = 0 → eD (gIdx v 0) = if d 0 = 5 then 1 else 0) := by
  intro d m
  obtain ⟨h6, h5, _⟩ := valid_groups hv
  by_cases hj9 : j < 9
  · obtain ⟨hidx, hr⟩ := (gIdx_r6 v j hj9).2 (h6 j hj9)
    have c0 := coreDigit_r6g v j 0 hj9 (by norm_num)
    have c1 := coreDigit_r6g v j 1 hj9 (by norm_num)
    have c2 := coreDigit_r6g v j 2 hj9 (by norm_num)
    simp only [add_zero, pow_zero, Nat.div_one, pow_one] at c0 c1 c2
    have m0 := maxDigit_r6 (3 * j) (by omega)
    have m1 := maxDigit_r6 (3 * j + 1) (by omega)
    have m2 := maxDigit_r6 (3 * j + 2) (by omega)
    generalize T3.r6Rank v j = r at hidx hr c0 c1 c2
    obtain ⟨hW, hZ, hS, hD, hP⟩ := lanes6 r hr
    have e36 : r / 6 ^ 2 % 6 = r / 36 := by norm_num; omega
    refine ⟨?_, ?_, ?_, ?_, fun hj0 => ?_⟩
    all_goals try (simp only [d, m, c0, c1, c2, m0, m1, m2, hidx, hW, hZ, hS, hP, e36, show ¬ 9 ≤ j by omega,
      false_and, if_false] <;> first | trivial | rfl | (unfold tScore tZeros; rfl))
    subst hj0
    have c0' : T3.coreDigit 0 v 0 = r % 6 := by simpa using c0
    have hidx' : gIdx v 0 = 40 + r := by simpa using hidx
    simp only [d, c0', hidx', hD]
  · obtain ⟨hiff, hidx, hle⟩ := gIdx_r5 v j ⟨by omega, hj⟩
    have hr := h5 j (by omega) hj
    have c0 := coreDigit_r5g v j 0 ⟨by omega, hj⟩ (by norm_num)
    have c1 := coreDigit_r5g v j 1 ⟨by omega, hj⟩ (by norm_num)
    have c2 := coreDigit_r5g v j 2 ⟨by omega, hj⟩ (by norm_num)
    simp only [add_zero, pow_zero, Nat.div_one, pow_one] at c0 c1 c2
    have m0 := maxDigit_r5 (3 * j) (by omega)
    have m1 := maxDigit_r5 (3 * j + 1) (by omega)
    have m2 := maxDigit_r5 (3 * j + 2) (by omega)
    generalize T3.r5Rank v j = r at hidx hr hle c0 c1 c2
    obtain ⟨hW, hZ, hS, hP, hD⟩ := lanes5 (127 - r) (by omega) (by omega)
    have e127 : 127 - (127 - r) = r := by omega
    have e25 : r / 5 ^ 2 % 5 = r / 25 := by norm_num; omega
    rw [e127] at hW hZ hS hP
    refine ⟨?_, ?_, ?_, ?_, fun hj0 => by omega⟩
    all_goals (simp only [d, m, c0, c1, c2, m0, m1, m2, hidx, hW, hZ, hS, hP, e25, show 9 ≤ j by omega,
      true_and] <;> first | trivial | rfl | (unfold tScore tZeros; rfl))
/-- Lanes of the r7 pair entry of a valid half. -/
theorem pair_lanes {v : Digest} (hv : T3.topRanksValid v = true) :
    let d := T3.coreDigit 0 v
    eW (gIdx v 16) = d 48 + d 49 ∧
    eZ (gIdx v 16) = (if d 48 = 0 then 1 else 0) + (if d 49 = 0 then 1 else 0) ∧
    eS (gIdx v 16) = (if d 48 + 1 = 6 then 1 else 0) + (if d 49 + 1 = 6 then 1 else 0) +
      4 * (if d 48 = 6 ∧ d 49 = 6 then 1 else 0) ∧
    eP (gIdx v 16) = 0 ∧ eD (gIdx v 16) = 0 := by
  intro d
  obtain ⟨_, _, h7⟩ := valid_groups hv
  obtain ⟨hiff, hidx, hr⟩ := gIdx_r7 v
  have hraw := hiff.1 h7
  have hlt : v.toNat / 2 ^ 56 % 128 < 128 := Nat.mod_lt _ (by norm_num)
  obtain ⟨hW, hZ, hS, hP, hD, h77⟩ := lanes7 _ hlt hraw
  have c48 : d 48 = (127 - v.toNat / 2 ^ 56 % 128) % 7 := by simp only [d, coreDigit_48, hr]
  have c49 : d 49 = (127 - v.toNat / 2 ^ 56 % 128) / 7 := by
    simp only [d, coreDigit_49, hr]; omega
  rw [hidx, c48, c49]
  exact ⟨hW, hZ, hS, hP, hD⟩
theorem sum_map_range (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
/-! ### Lane sums over the 17 groups -/
def LW (v : Digest) : Nat := ∑ j ∈ Finset.range 17, eW (gIdx v j)
def LP (v : Digest) : Nat := ∑ j ∈ Finset.range 17, eP (gIdx v j)
def LD (v : Digest) : Nat := ∑ j ∈ Finset.range 17, eD (gIdx v j)
def LZ (v : Digest) : Nat := ∑ j ∈ Finset.range 17, eZ (gIdx v j)
def LS (v : Digest) : Nat := ∑ j ∈ Finset.range 17, eS (gIdx v j)
/-- Penalty lanes of the three penalised r5 groups (the kernel's `a1`). -/
def LPen (v : Digest) : Nat := eP (gIdx v 10) + eP (gIdx v 11) + eP (gIdx v 12)
theorem dataDigits_sum_LW {v : Digest} (hv : T3.topRanksValid v = true) : (T3.dataDigits 0 v).sum = LW v := by
  unfold T3.dataDigits LW
  rw [sum_map_range, show T3.dataCount 0 = 50 from rfl, sum50,
    Finset.sum_range_succ (fun j => eW (gIdx v j)) 16, (pair_lanes hv).1]
  congr 1
  exact Finset.sum_congr rfl (fun j hj => ((group_lanes hv j (Finset.mem_range.1 hj)).1).symm)
theorem decode_some_iff (v : Digest) (ds : List Nat) :
    WCT9.CanonicalPolicy.decode 0 v = some ds ↔
      T3.topRanksValid v = true ∧ LW v ≤ 152 ∧ 152 - LW v < 6 ∧ ds = T3.dataDigits 0 v ++ [152 - LW v] := by
  constructor
  · intro h
    obtain ⟨hv, h1, h2, rfl⟩ := decode_top_eq h
    rw [dataDigits_sum_LW hv] at h1 h2 ⊢
    exact ⟨hv, h1, h2, rfl⟩
  · rintro ⟨hv, h1, h2, rfl⟩
    unfold WCT9.CanonicalPolicy.decode WCT9.CanonicalPolicy.normalLayer T3.decode
    have hlt : ¬ v.toNat ≥ 2 ^ T3.encodedBits 0 := by
      have := v.isLt; unfold T3.encodedBits; omega
    simp only [if_true, hlt, if_false, dataDigits_sum_LW hv, show T3.target 0 = 152 from rfl]
    rw [if_pos ⟨hv, h1, h2⟩]
theorem invalid_LW {v : Digest} (hr7 : 79 ≤ v.toNat / 2 ^ 56 % 128) (hv : T3.topRanksValid v = false) :
    256 ≤ LW v := by
  have hex : ∃ j < 17, eW (gIdx v j) = 256 := by
    by_contra hne
    push Not at hne
    have : T3.topRanksValid v = true := by
      unfold T3.topRanksValid
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, List.mem_range']
      refine ⟨⟨fun j hj => ?_, ?_⟩, (gIdx_r7 v).1.2 hr7⟩
      · exact (gIdx_r6 v j hj).1.2 (hne j (by omega))
      · rintro q ⟨i, hi, rfl⟩
        exact (gIdx_r5 v (9 + 1 * i) ⟨by omega, by omega⟩).1.2 (hne _ (by omega))
    rw [this] at hv; cases hv
  obtain ⟨j, hj, h⟩ := hex
  unfold LW
  calc 256 = eW (gIdx v j) := h.symm
    _ ≤ ∑ j ∈ Finset.range 17, eW (gIdx v j) :=
      Finset.single_le_sum (f := fun j => eW (gIdx v j)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hj)
theorem ds_getD_50' {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    ds.getD 50 0 = 152 - LW v := by
  rw [ds_getD_50 h, dataDigits_sum_LW (decode_top_eq h).1]
theorem zeros_lanes {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    (ds.filter (· = 0)).length = LZ v + (if 152 - LW v = 0 then 1 else 0) := by
  obtain ⟨hv, _, _, hds⟩ := (decode_some_iff v ds).1 h
  rw [zeros_top ds (decode_length h), ds_getD_50' h]
  have hZ : ∀ j ∈ Finset.range 16, ((if ds.getD (3 * j) 0 = 0 then 1 else 0) +
      (if ds.getD (3 * j + 1) 0 = 0 then 1 else 0) + (if ds.getD (3 * j + 2) 0 = 0 then 1 else 0)) =
      eZ (gIdx v j) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [(group_lanes hv j hj').2.1, ds_getD_data h _ (by omega), ds_getD_data h _ (by omega),
      ds_getD_data h _ (by omega)]
  have hP : ((if ds.getD 48 0 = 0 then 1 else 0) + (if ds.getD 49 0 = 0 then 1 else 0)) = eZ (gIdx v 16) := by
    rw [(pair_lanes hv).2.1, ds_getD_data h 48 (by norm_num), ds_getD_data h 49 (by norm_num)]
  rw [Finset.sum_congr rfl hZ, hP]
  unfold LZ
  rw [Finset.sum_range_succ (fun j => eZ (gIdx v j)) 16]
theorem reward_lanes {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    WCT9.CanonicalPolicy.reward 0 ds = LS v + 4 * eD (gIdx v 0) + (if 152 - LW v = 4 then 1 else 0) := by
  obtain ⟨hv, _, _, _⟩ := (decode_some_iff v ds).1 h
  unfold WCT9.CanonicalPolicy.reward
  rw [wordCredit_top, savedCopies_top, ds_getD_50' h]
  have hD := (group_lanes hv 0 (by norm_num)).2.2.2.2 rfl
  rw [hD, ds_getD_data h 0 (by norm_num)]
  unfold LS
  have hS : ∀ j ∈ Finset.range 16, eS (gIdx v j) =
      ((if ds.getD (3 * j) 0 + 1 = T3.maxDigit 0 (3 * j) then 1 else 0) +
       (if ds.getD (3 * j + 1) 0 + 1 = T3.maxDigit 0 (3 * j + 1) then 1 else 0) +
       (if ds.getD (3 * j + 2) 0 + 1 = T3.maxDigit 0 (3 * j + 2) then 1 else 0)) +
      4 * ((if ds.getD (3 * j) 0 = T3.maxDigit 0 (3 * j) ∧ ds.getD (3 * j + 1) 0 = T3.maxDigit 0 (3 * j + 1)
          then 1 else 0) +
       (if ds.getD (3 * j + 1) 0 = T3.maxDigit 0 (3 * j + 1) ∧ ds.getD (3 * j + 2) 0 = T3.maxDigit 0 (3 * j + 2)
          then 1 else 0)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [(group_lanes hv j hj').2.2.1, ds_getD_data h _ (by omega), ds_getD_data h _ (by omega),
      ds_getD_data h _ (by omega)]
  have hP : eS (gIdx v 16) = (if ds.getD 48 0 + 1 = 6 then 1 else 0) + (if ds.getD 49 0 + 1 = 6 then 1 else 0) +
      4 * (if ds.getD 48 0 = 6 ∧ ds.getD 49 0 = 6 then 1 else 0) := by
    rw [(pair_lanes hv).2.2.1, ds_getD_data h 48 (by norm_num), ds_getD_data h 49 (by norm_num)]
  have e5 : (if 152 - LW v + 1 = 5 then 1 else 0) = (if 152 - LW v = 4 then 1 else 0) := by
    split_ifs <;> omega
  rw [Finset.sum_range_succ (fun j => eS (gIdx v j)) 16, Finset.sum_congr rfl hS, hP, e5]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
theorem penalty_lanes {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    WCT9.dispatchPenalty 0 ds = LPen v := by
  obtain ⟨hv, _, _, _⟩ := (decode_some_iff v ds).1 h
  unfold WCT9.dispatchPenalty LPen
  rw [if_pos rfl, penalty_top]
  have p10 := (group_lanes hv 10 (by norm_num)).2.2.2.1
  have p11 := (group_lanes hv 11 (by norm_num)).2.2.2.1
  have p12 := (group_lanes hv 12 (by norm_num)).2.2.2.1
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceLeDiff, true_and] at p10 p11 p12
  rw [p10, p11, p12]
  simp only [ds_getD_data h _ (show 30 < 50 by norm_num), ds_getD_data h _ (show 31 < 50 by norm_num),
    ds_getD_data h _ (show 32 < 50 by norm_num), ds_getD_data h _ (show 33 < 50 by norm_num),
    ds_getD_data h _ (show 34 < 50 by norm_num), ds_getD_data h _ (show 35 < 50 by norm_num),
    ds_getD_data h _ (show 36 < 50 by norm_num), ds_getD_data h _ (show 37 < 50 by norm_num),
    ds_getD_data h _ (show 38 < 50 by norm_num)]
/-- The kernel's acceptance test of a half `v` at threshold `thr` (Nat form of the machine checks). -/
def kAcc (v : Digest) (thr : Nat) : Prop :=
  79 ≤ v.toNat / 2 ^ 56 % 128 ∧ LW v ≤ 152 ∧ 152 - LW v < 6 ∧ LZ v + (if 152 - LW v = 0 then 1 else 0) ≤ 7 ∧
    thr + LPen v ≤ LS v + 4 * eD (gIdx v 0) + (if 152 - LW v = 4 then 1 else 0)
theorem kAcc_decode {v : Digest} {thr : Nat} (h : kAcc v thr) :
    WCT9.CanonicalPolicy.decode 0 v = some (T3.dataDigits 0 v ++ [152 - LW v]) := by
  obtain ⟨hr7, h1, h2, _, _⟩ := h
  have hv : T3.topRanksValid v = true := by
    cases hc : T3.topRanksValid v
    · have := invalid_LW hr7 hc; omega
    · rfl
  exact (decode_some_iff v _).2 ⟨hv, h1, h2, rfl⟩
/-- The canonical top producer predicate is the kernel test at threshold `f - 2 [low]`. -/
theorem producer_some (v : Digest) (f : Nat) (low : Bool) (hf : 2 ≤ f) (ds : List Nat) :
    WCT9.CanonicalPolicy.producerDecodeAt 0 f low v = some ds ↔
      kAcc v (f - if low then 2 else 0) ∧ WCT9.CanonicalPolicy.decode 0 v = some ds := by
  unfold WCT9.CanonicalPolicy.producerDecodeAt
  cases hd : WCT9.CanonicalPolicy.decode 0 v with
  | none => simp
  | some ds' =>
    obtain ⟨hv, h1, h2, _⟩ := (decode_some_iff v ds').1 hd
    have hr7 : 79 ≤ v.toNat / 2 ^ 56 % 128 := (gIdx_r7 v).1.1 (valid_groups hv).2.2
    simp only [Option.some.injEq]
    rw [WCT9.CanonicalPolicy.pathReward_top, reward_lanes hd, penalty_lanes hd]
    have hz : WCT9.canonicalZeroBound 0 ds' ↔ LZ v + (if 152 - LW v = 0 then 1 else 0) ≤ 7 := by
      unfold WCT9.canonicalZeroBound WCT9.producerZeroCap; rw [zeros_lanes hd]; simp
    have hrb : WCT9.producerRankBound 0 v := Or.inl rfl
    unfold kAcc
    obtain ⟨cl, hcl, hfl⟩ : ∃ cl, (if low = true then 2 else 0) = cl ∧ cl ≤ 2 := ⟨_, rfl, by split_ifs <;> omega⟩
    rw [hcl]
    generalize (if 152 - LW v = 4 then 1 else 0) = c4
    generalize (if 152 - LW v = 0 then 1 else 0) = c0 at hz
    constructor
    · intro hh
      split_ifs at hh with hc
      simp only [Option.some.injEq] at hh
      exact ⟨⟨hr7, h1, h2, hz.1 hc.2.1, by omega⟩, hh⟩
    · rintro ⟨⟨_, _, _, hzz, hr⟩, rfl⟩
      rw [if_pos ⟨by omega, hz.2 hzz, hrb⟩]
/-- An accepted producer answer meets its floor on the path-aware credit. -/
theorem producerDecodeOut_floor {f : Nat} {a : BitVec 256} {ds : List Nat} {low : Bool}
    (h : WCT9.CanonicalPolicy.producerDecodeOut 0 f a = some (ds, low)) :
    f ≤ WCT9.CanonicalPolicy.credit 0 low ds := by
  unfold WCT9.CanonicalPolicy.producerDecodeOut at h
  cases hp : WCT9.CanonicalPolicy.producerDecodeAt 0 f (WCT9.lowSelected 0 a) (WCT9.encodingAnswer 0 a) with
  | none => rw [hp] at h; cases h
  | some ds' =>
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold WCT9.CanonicalPolicy.producerDecodeAt at hp
    split at hp
    · split_ifs at hp with hc
      · simp only [Option.some.injEq] at hp
        subst hp
        unfold WCT9.CanonicalPolicy.credit
        omega
    · cases hp
theorem credit_lanes {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) (low : Bool) :
    WCT9.CanonicalPolicy.credit 0 low ds =
      LS v + 4 * eD (gIdx v 0) + (if 152 - LW v = 4 then 1 else 0) + (if low then 2 else 0) - LPen v := by
  rw [WCT9.CanonicalPolicy.credit_top, reward_lanes h, penalty_lanes h]
end SigGolfCandidate.T3M.Search.T51
end
