import SigGolfCandidate.T3M.Verify.Nonbinary.PairAlgebra
import SigGolfCandidate.T3M.Mem

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
abbrev PAIR_DATA : Nat := 0xFF8000
abbrev TAIL_DATA : Nat := 0xFF7DF8
abbrev MASK_DATA : Nat := 0xFF7FF8
def tailSum (r : Nat) : Nat := r % 4 + (r / 4) % 4 + r / 16
theorem tailSum_le (r : Nat) (hr : r < 64) : tailSum r ≤ 9 := by unfold tailSum; omega
theorem tailSum_eq (v : Digest) (hv : v.toNat < 2 ^ 125) :
    tailSum (v.toNat / 2 ^ 119) = tailWeight v := by
  unfold tailSum tailWeight
  simp only [Nat.div_div_eq_div_mul]
  norm_num
  omega
def broadTailValue (r : Nat) : Nat := if r < 64 then 126 - tailSum r else 254

theorem broadTail_le (r : Nat) : broadTailValue r ≤ 254 := by
  unfold broadTailValue
  split_ifs <;> omega

def PairTableOK (s : MachineState) : Prop :=
  ∀ r : Nat, r < 16384 → s.getByte (BitVec.ofNat 64 (PAIR_DATA + r)) = BitVec.ofNat 8 (pairLookup r)
def TailTableOK (s : MachineState) : Prop :=
  ∀ r : Nat, r < 512 → s.getByte (BitVec.ofNat 64 (TAIL_DATA + r)) = BitVec.ofNat 8 (broadTailValue r)
structure PackedTables (s : MachineState) : Prop where
  pair : PairTableOK s
  tail : TailTableOK s
  mask : s.getMem (BitVec.ofNat 64 (MASK_DATA)) = 130048#64
  pre0 : s.getMem (BitVec.ofNat 64 (TAIL_DATA - 16)) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56)
  pre1 : s.getMem (BitVec.ofNat 64 (TAIL_DATA - 8)) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + 1 * 2 ^ 48)
theorem PackedTables.frame {s t : MachineState} (ht : PackedTables s)
    (hf : Frame s t (fun _ => False)) : PackedTables t := by
  constructor
  · intro r hr
    exact (hf.getByte (by unfold PAIR_DATA; omega) (by simp)).trans (ht.pair r hr)
  · intro r hr
    exact (hf.getByte (by simp only [TAIL_DATA, MASK_DATA]; omega) (by simp)).trans (ht.tail r hr)
  · exact (hf.get (by simp only [TAIL_DATA, MASK_DATA]; omega) (by simp)).trans ht.mask
  · exact (hf.get (by simp only [TAIL_DATA, MASK_DATA]; omega) (by simp)).trans ht.pre0
  · exact (hf.get (by simp only [TAIL_DATA, MASK_DATA]; omega) (by simp)).trans ht.pre1
theorem PackedTables.congr {s t : MachineState} (ht : PackedTables s)
    (hm : ∀ A, TAIL_DATA - 16 ≤ A → A + 8 ≤ 2 ^ 24 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : PackedTables t := by
  constructor
  · intro r hr
    rw [getByte_eq_word _ _ (by unfold PAIR_DATA; omega),
      hm _ (by unfold PAIR_DATA TAIL_DATA; omega) (by unfold PAIR_DATA; omega),
      ← getByte_eq_word _ _ (by unfold PAIR_DATA; omega)]
    exact ht.pair r hr
  · intro r hr
    rw [getByte_eq_word _ _ (by simp only [TAIL_DATA, MASK_DATA]; omega),
      hm _ (by simp only [TAIL_DATA, MASK_DATA]; omega) (by simp only [TAIL_DATA, MASK_DATA]; omega),
      ← getByte_eq_word _ _ (by simp only [TAIL_DATA, MASK_DATA]; omega)]
    exact ht.tail r hr
  · exact (hm _ (by simp only [TAIL_DATA, MASK_DATA]; omega) (by simp only [TAIL_DATA, MASK_DATA]; omega)).trans ht.mask
  · exact (hm _ (by simp only [TAIL_DATA, MASK_DATA]; omega) (by simp only [TAIL_DATA, MASK_DATA]; omega)).trans ht.pre0
  · exact (hm _ (by simp only [TAIL_DATA, MASK_DATA]; omega) (by simp only [TAIL_DATA, MASK_DATA]; omega)).trans ht.pre1
theorem PairTableOK.rank (s : MachineState) (ht : PairTableOK s) (r : Nat) (hr : r < 16384) :
    (s.getByte (BitVec.ofNat 64 (PAIR_DATA + r))).zeroExtend 64 = BitVec.ofNat 64 (pairLookup r) := by
  rw [ht r hr]
  have h := pairWeight_le (r % 128) (r / 128)
  change pairLookup r ≤ 255 at h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
theorem TailTableOK.rank (s : MachineState) (ht : TailTableOK s) (r : Nat) (hr : r < 512) :
    (s.getByte (BitVec.ofNat 64 (TAIL_DATA + r))).zeroExtend 64 = BitVec.ofNat 64 (broadTailValue r) := by
  rw [ht r hr]
  have h := broadTail_le r
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
theorem compressedSum_gap (f : Nat → Nat) : compressedSum f ≠ 254 := by
  by_cases h : ∀ i, i < 17 → f i < 125
  · rw [compressedSum_good f h]
    have hb : fullSum f ≤ 204 := by
      unfold fullSum
      have H : ∀ l : List Nat, (∀ i ∈ l, f i < 125) →
          (l.map fun i => rankLookup (f i)).sum ≤ l.length * 12 := by
        intro l
        induction l with
        | nil => simp
        | cons i l ih =>
          intro hh
          have hi := hh i (by simp)
          have hr : rankLookup (f i) ≤ 12 := by
            simp only [rankLookup, if_pos hi]
            exact rankWeight_le _
          have ht := ih (fun j hj => hh j (by simp [hj]))
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          omega
      simpa using H (List.range 17) (fun i hi => h i (List.mem_range.mp hi))
    omega
  · push_neg at h
    obtain ⟨i, hi, hb⟩ := h
    have := compressedSum_bad f i hi hb
    omega

theorem broadTail_target (v : Digest) :
    compressedSum (topRank v) = broadTailValue (v.toNat / 2 ^ 119) ↔
      v.toNat < 2 ^ 125 ∧ pairedLookupSum v = 126 := by
  by_cases hv : v.toNat < 2 ^ 125
  · have hr : v.toNat / 2 ^ 119 < 64 := by omega
    simp only [broadTailValue, if_pos hr, tailSum_eq v hv, pairedLookupSum,
      hv, true_and]
    have := tailWeight_le v
    omega
  · have hr : ¬ v.toNat / 2 ^ 119 < 64 := by omega
    simp only [broadTailValue, if_neg hr, hv, false_and]
    exact iff_false_intro (compressedSum_gap _)

theorem broadTail_decode (v : Digest) :
    SigGolfCandidate.T3.decode 0 v =
      if compressedSum (topRank v) = broadTailValue (v.toNat / 2 ^ 119)
        then some (topDigits v) else none := by
  simp only [decode_top_paired, broadTail_target]


end SigGolfCandidate.T3M.Verify.Nonbinary
