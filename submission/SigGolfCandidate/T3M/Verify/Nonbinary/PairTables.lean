import SigGolfCandidate.T3M.Verify.Nonbinary.WideTail

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
abbrev PAIR_DATA : Nat := 0xFFC000
abbrev TAIL_DATA : Nat := 0xFFBD40
abbrev TAIL_MASK_DATA : Nat := 0xFFBFF8
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
  ∀ r : Nat, r < 512 → s.getByte (BitVec.ofNat 64 (TAIL_DATA + r)) = BitVec.ofNat 8 (wideTailTarget r)
structure PackedTables (s : MachineState) : Prop where
  pair : PairTableOK s
  tail : TailTableOK s
  mask : s.getMem (BitVec.ofNat 64 TAIL_MASK_DATA) = 130048#64
theorem PackedTables.frame {s t : MachineState} (ht : PackedTables s)
    (hf : Frame s t (fun _ => False)) : PackedTables t := by
  constructor
  · intro r hr
    exact (hf.getByte (by unfold PAIR_DATA; omega) (by simp)).trans (ht.pair r hr)
  · intro r hr
    exact (hf.getByte (by simp only [TAIL_DATA, TAIL_MASK_DATA]; omega) (by simp)).trans (ht.tail r hr)
  · exact (hf.get (by simp only [TAIL_DATA, TAIL_MASK_DATA]; omega) (by simp)).trans ht.mask
theorem PackedTables.congr {s t : MachineState} (ht : PackedTables s)
    (hm : ∀ A, TAIL_DATA ≤ A → A + 8 ≤ 2 ^ 24 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : PackedTables t := by
  constructor
  · intro r hr
    rw [getByte_eq_word _ _ (by unfold PAIR_DATA; omega),
      hm _ (by unfold PAIR_DATA TAIL_DATA; omega) (by unfold PAIR_DATA; omega),
      ← getByte_eq_word _ _ (by unfold PAIR_DATA; omega)]
    exact ht.pair r hr
  · intro r hr
    rw [getByte_eq_word _ _ (by simp only [TAIL_DATA, TAIL_MASK_DATA]; omega),
      hm _ (by simp only [TAIL_DATA, TAIL_MASK_DATA]; omega) (by simp only [TAIL_DATA, TAIL_MASK_DATA]; omega),
      ← getByte_eq_word _ _ (by simp only [TAIL_DATA, TAIL_MASK_DATA]; omega)]
    exact ht.tail r hr
  · exact (hm _ (by simp only [TAIL_DATA, TAIL_MASK_DATA]; omega) (by simp only [TAIL_DATA, TAIL_MASK_DATA]; omega)).trans ht.mask
theorem PairTableOK.rank (s : MachineState) (ht : PairTableOK s) (r : Nat) (hr : r < 16384) :
    (s.getByte (BitVec.ofNat 64 (PAIR_DATA + r))).zeroExtend 64 = BitVec.ofNat 64 (pairLookup r) := by
  rw [ht r hr]
  have h := pairWeight_le (r % 128) (r / 128)
  change pairLookup r ≤ 255 at h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
theorem TailTableOK.rank (s : MachineState) (ht : TailTableOK s) (r : Nat) (hr : r < 512) :
    (s.getByte (BitVec.ofNat 64 (TAIL_DATA + r))).zeroExtend 64 = BitVec.ofNat 64 (wideTailTarget r) := by
  rw [ht r hr]
  have h := wideTailTarget_le r
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
end SigGolfCandidate.T3M.Verify.Nonbinary
