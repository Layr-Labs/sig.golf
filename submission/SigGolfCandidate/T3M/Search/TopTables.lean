import SigGolfCandidate.T3M.Search.Decode

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
abbrev TOP_DATA : Nat := 16773120
def rankDigit (r i : Nat) : Nat := r / 5 ^ i % 5
def rankWeight (r : Nat) : Nat := r % 5 + r / 5 % 5 + r / 25 % 5
def rankLookup (r : Nat) : Nat := if r < 125 then rankWeight r else 255
def topRank (v : Digest) (j : Nat) : Nat := v.toNat / 2 ^ (7 * j) % 128
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
/-- Campaign R6: the canonical search reads only the choice flag byte (TOP_DATA + 631) of the cf block (the dummy
word at 632..647 is the R6 one in the sign image, `cfByteR6`). -/
def CfFlagOK (flag : Nat) (s : MachineState) : Prop :=
  s.getByte (BitVec.ofNat 64 (TOP_DATA + 631)) = BitVec.ofNat 8 flag
theorem CfFlagOK.frame {flag : Nat} {s t : MachineState} {W : Nat → Prop} (h : CfFlagOK flag s)
    (hf : Frame s t W) (hd : ∀ i, 628 ≤ i → i < 648 → ¬ W ((TOP_DATA + i) / 8 * 8)) : CfFlagOK flag t :=
  (hf.getByte (by unfold TOP_DATA; omega) (hd 631 (by omega) (by omega))).trans h
theorem CfTableOK.flagOK {flag : Nat} {s : MachineState} (h : CfTableOK flag s) : CfFlagOK flag s := by
  unfold CfFlagOK; rw [h 631 (by omega) (by omega)]; unfold cfByte; rw [if_pos rfl]
instance {flag : Nat} {s : MachineState} : Coe (CfTableOK flag s) (CfFlagOK flag s) := ⟨CfTableOK.flagOK⟩
def TableOK (s : MachineState) : Prop :=
  ∀ i, i < 628 → s.getByte (BitVec.ofNat 64 (TOP_DATA + i)) = tableByte i
theorem TableOK.frame {s t : MachineState} {W : Nat → Prop} (h : TableOK s)
    (hf : Frame s t W) (hd : ∀ i, i < 628 → ¬ W ((TOP_DATA + i) / 8 * 8)) : TableOK t := by
  intro i hi
  exact (hf.getByte (by unfold TOP_DATA; omega) (hd i hi)).trans (h i hi)
/-! ### R6 packed top tables (campaign R6; `sign/kernel/r6tables.py`)
One 32-bit entry per field value. Lanes: bits 0..7 score `wc + 4 safe` (`wc` = digits equal to `max - 1`,
`safe` = `#{j ∈ 1,2 : d_j = max ∧ d_(j-1) = max}`), 8..13 zero digits, 14..17 `[d_0 = max]` (r6 only),
18..21 `[d_0 + d_1 + d_2 < 3]` (r5 only), 22..30 weight `d_0 + d_1 + d_2`; INVALID = weight 256 only.
Block (1696 bytes, little endian): `T6C` entries 0..295 = `[INVALID]*40 ++ E6(0..215) ++ [INVALID]*40`, then `T5`
entries 296..423 with `T5[raw7] = INVALID` for `raw7 < 3`, else `E5(127 - raw7)`. -/
def r6Invalid : Nat := 256 * 2 ^ 22
/-- Lanes of a digit triple `(a, b, c)` with largest digit `m`: weight, zero count, score. -/
def r6Score (m a b c : Nat) : Nat :=
  (if a + 1 = m then 1 else 0) + (if b + 1 = m then 1 else 0) + (if c + 1 = m then 1 else 0) +
    4 * ((if a = m ∧ b = m then 1 else 0) + (if b = m ∧ c = m then 1 else 0))
def r6Zeros (a b c : Nat) : Nat := (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) + (if c = 0 then 1 else 0)
def r6Entry6 (r : Nat) : Nat :=
  (r % 6 + r / 6 % 6 + r / 36) * 2 ^ 22 + (if r % 6 = 5 then 2 ^ 14 else 0) +
    r6Zeros (r % 6) (r / 6 % 6) (r / 36) * 2 ^ 8 + r6Score 5 (r % 6) (r / 6 % 6) (r / 36)
def r6Entry5 (r : Nat) : Nat :=
  (r % 5 + r / 5 % 5 + r / 25) * 2 ^ 22 + (if r % 5 + r / 5 % 5 + r / 25 < 3 then 2 ^ 18 else 0) +
    r6Zeros (r % 5) (r / 5 % 5) (r / 25) * 2 ^ 8 + r6Score 4 (r % 5) (r / 5 % 5) (r / 25)
/-- Entry `k` (`k < 424`) of the packed block. -/
def r6Entry (k : Nat) : Nat :=
  if k < 40 then r6Invalid else if k < 256 then r6Entry6 (k - 40) else if k < 296 then r6Invalid
  else if k < 299 then r6Invalid else r6Entry5 (127 - (k - 296))
def r6TableByte (i : Nat) : BitVec 8 := BitVec.ofNat 8 (r6Entry (i / 4) / 256 ^ (i % 4) % 256)
/-- The 1696-byte packed table block at `base`. -/
def R6TableOK (base : Nat) (s : MachineState) : Prop :=
  ∀ i, i < 1696 → s.getByte (BitVec.ofNat 64 (base + i)) = r6TableByte i
theorem R6TableOK.frame {base : Nat} {s t : MachineState} {W : Nat → Prop} (h : R6TableOK base s)
    (hf : Frame s t W) (hb : base + 1696 ≤ 2 ^ 64) (hd : ∀ i, i < 1696 → ¬ W ((base + i) / 8 * 8)) :
    R6TableOK base t := by
  intro i hi
  exact (hf.getByte (by omega) (hd i hi)).trans (h i hi)
/-- R6 dummy word (D1c code of `T3.dummyTop` = `[3]*50 ++ [2] ++ [1]`), stored at TOP_DATA + 632 of the sign image. -/
def dummyDigestNatR6 : Nat := 0x40bb44891224489122818181818181a9
def cfByteR6 (flag : Nat) (i : Nat) : BitVec 8 := BitVec.ofNat 8 <|
  if i = 631 then flag
  else if 632 ≤ i ∧ i < 648 then dummyDigestNatR6 / 256 ^ (i - 632) % 256
  else 0
def CfTableOKR6 (flag : Nat) (s : MachineState) : Prop :=
  ∀ i, 628 ≤ i → i < 648 → s.getByte (BitVec.ofNat 64 (TOP_DATA + i)) = cfByteR6 flag i
theorem CfTableOKR6.frame {flag : Nat} {s t : MachineState} {W : Nat → Prop} (h : CfTableOKR6 flag s)
    (hf : Frame s t W) (hd : ∀ i, 628 ≤ i → i < 648 → ¬ W ((TOP_DATA + i) / 8 * 8)) : CfTableOKR6 flag t := by
  intro i hi hj
  exact (hf.getByte (by unfold TOP_DATA; omega) (hd i hi hj)).trans (h i hi hj)

theorem CfTableOKR6.flagOK {flag : Nat} {s : MachineState} (h : CfTableOKR6 flag s) : CfFlagOK flag s := by
  unfold CfFlagOK; rw [h 631 (by omega) (by omega)]; unfold cfByteR6; rw [if_pos rfl]
instance {flag : Nat} {s : MachineState} : Coe (CfTableOKR6 flag s) (CfFlagOK flag s) := ⟨CfTableOKR6.flagOK⟩

end SigGolfCandidate.T3M.Search
