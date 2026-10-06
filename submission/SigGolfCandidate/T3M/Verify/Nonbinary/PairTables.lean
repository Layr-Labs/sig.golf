import SigGolfCandidate.T3M.Verify.Nonbinary.PairAlgebra

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
abbrev PAIR_DATA : Nat := 0xFFC000
abbrev TAIL_DATA : Nat := 0xFFBFB8
abbrev RAW_DATA : Nat := 0xFFBE40
def tailSum (r : Nat) : Nat := r % 4 + (r / 4) % 4 + r / 16
theorem tailSum_le (r : Nat) (hr : r < 64) : tailSum r ≤ 9 := by unfold tailSum; omega
theorem tailSum_eq (v : Digest) (hv : v.toNat < 2 ^ 125) :
    tailSum (v.toNat / 2 ^ 119) = tailWeight v := by
  unfold tailSum tailWeight
  simp only [Nat.div_div_eq_div_mul]
  norm_num
  omega
def PairTableOK (s : MachineState) : Prop :=
  ∀ r : Nat, r < 16384 → s.getByte (BitVec.ofNat 64 (PAIR_DATA + r)) = BitVec.ofNat 8 (pairLookup r)
def TailTableOK (s : MachineState) : Prop :=
  ∀ r : Nat, r < 64 → s.getByte (BitVec.ofNat 64 (TAIL_DATA + r)) = BitVec.ofNat 8 (128 - tailSum r)
def RawTableOK (s : MachineState) : Prop :=
  ∀ r : Nat, r < 256 → s.getByte (BitVec.ofNat 64 (RAW_DATA + r)) = BitVec.ofNat 8 (rankLookup (r % 128))
structure PackedTables (s : MachineState) : Prop where
  pair : PairTableOK s
  tail : TailTableOK s
  mask : s.getMem (BitVec.ofNat 64 (TAIL_DATA + 64)) = 130048#64
  raw : RawTableOK s
theorem PackedTables.frame {s t : MachineState} (ht : PackedTables s)
    (hf : Frame s t (fun _ => False)) : PackedTables t := by
  constructor
  · intro r hr
    exact (hf.getByte (by unfold PAIR_DATA; omega) (by simp)).trans (ht.pair r hr)
  · intro r hr
    exact (hf.getByte (by unfold TAIL_DATA; omega) (by simp)).trans (ht.tail r hr)
  · exact (hf.get (by unfold TAIL_DATA; omega) (by simp)).trans ht.mask
  · intro r hr
    exact (hf.getByte (by unfold RAW_DATA; omega) (by simp)).trans (ht.raw r hr)
theorem PackedTables.congr {s t : MachineState} (ht : PackedTables s)
    (hm : ∀ A, RAW_DATA ≤ A → A + 8 ≤ 2 ^ 24 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : PackedTables t := by
  constructor
  · intro r hr
    rw [getByte_eq_word _ _ (by unfold PAIR_DATA; omega),
      hm _ (by unfold PAIR_DATA RAW_DATA; omega) (by unfold PAIR_DATA; omega),
      ← getByte_eq_word _ _ (by unfold PAIR_DATA; omega)]
    exact ht.pair r hr
  · intro r hr
    rw [getByte_eq_word _ _ (by unfold TAIL_DATA; omega),
      hm _ (by unfold TAIL_DATA RAW_DATA; omega) (by unfold TAIL_DATA; omega),
      ← getByte_eq_word _ _ (by unfold TAIL_DATA; omega)]
    exact ht.tail r hr
  · exact (hm _ (by unfold TAIL_DATA RAW_DATA; omega) (by unfold TAIL_DATA; omega)).trans ht.mask
  · intro r hr
    rw [getByte_eq_word _ _ (by unfold RAW_DATA; omega),
      hm _ (by unfold RAW_DATA; omega) (by unfold RAW_DATA; omega),
      ← getByte_eq_word _ _ (by unfold RAW_DATA; omega)]
    exact ht.raw r hr
theorem PairTableOK.rank (s : MachineState) (ht : PairTableOK s) (r : Nat) (hr : r < 16384) :
    (s.getByte (BitVec.ofNat 64 (PAIR_DATA + r))).zeroExtend 64 = BitVec.ofNat 64 (pairLookup r) := by
  rw [ht r hr]
  have h := pairWeight_le (r % 128) (r / 128)
  change pairLookup r ≤ 255 at h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
theorem TailTableOK.rank (s : MachineState) (ht : TailTableOK s) (r : Nat) (hr : r < 64) :
    (s.getByte (BitVec.ofNat 64 (TAIL_DATA + r))).zeroExtend 64 = BitVec.ofNat 64 (128 - tailSum r) := by
  rw [ht r hr]
  have h := tailSum_le r hr
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
theorem RawTableOK.rank (s : MachineState) (ht : RawTableOK s) (r : Nat) (hr : r < 256) :
    (s.getByte (BitVec.ofNat 64 (RAW_DATA + r))).zeroExtend 64 = BitVec.ofNat 64 (rankLookup (r % 128)) := by
  rw [ht r hr]
  have h : rankLookup (r % 128) ≤ 255 := by
    unfold rankLookup rankWeight
    split_ifs <;> omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
end SigGolfCandidate.T3M.Verify.Nonbinary
