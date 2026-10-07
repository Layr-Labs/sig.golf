import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RotateMemory
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ComposeBack
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.RotateWords

namespace ClaudeWCT.W9.Machine.Expand.Rotation
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M (legacyWitList witList legacyWit_words tailWit_words moved_body_word witBody witBody_length_eq)

theorem lwu_counter (c : BitVec 32) :
    LoadKind.wu.fromWord (BitVec.ofNat 64 c.toNat) 0 = BitVec.ofNat 64 c.toNat := by
  apply BitVec.eq_of_toNat_eq
  have h64 : c.toNat < 2 ^ 64 := lt_trans c.isLt (by norm_num)
  simp [LoadKind.fromWord, extractWord32, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt c.isLt, Nat.mod_eq_of_lt h64]

theorem shift_counter (c : BitVec 32) :
    (BitVec.ofNat 64 c.toNat) <<< (32 : Word) = BitVec.ofNat 64 (256 ^ 4 * c.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (show c.toNat < 2 ^ 64 from lt_trans c.isLt (by norm_num))]
  congr 1
  change c.toNat * 2 ^ 32 = 256 ^ 4 * c.toNat
  omega

theorem rotatedWord_witness (N : HashOutput) (w : WCT9.Witness) (s : MachineState)
    (hw : s.readWords (BitVec.ofNat 64 2048) 2729 = wordsOf (legacyWitList N w))
    (i : Nat) (hi : i < 2729) :
    rotatedWord s i = (wordsOf (witList N w)).getD i 0 := by
  have hm : ∀ j < 2729, s.getMem (BitVec.ofNat 64 (2048 + 8 * j)) =
      (wordsOf (legacyWitList N w)).getD j 0 := by
    intro j hj
    rw [← hw, VLib.readWords_ofNat s 2048 2729 (by norm_num)]
    simp [List.getD_eq_getElem?_getD, hj]
  by_cases hb : i < 2725
  · rw [rotatedWord, if_pos hb, hm _ (by omega), moved_body_word N w i hb]
  · have h0 : s.getMem (BitVec.ofNat 64 2048) = w.signature.rho.extractLsb' 0 64 := by
      simpa [legacyWit_words] using hm 0 (by norm_num)
    have h1 : s.getMem (BitVec.ofNat 64 2056) = w.signature.rho.extractLsb' 64 64 := by
      simpa [legacyWit_words] using hm 1 (by norm_num)
    have h2 : s.getMem (BitVec.ofNat 64 2064) = BitVec.ofNat 64 w.digestCounter.toNat := by
      simpa [legacyWit_words] using hm 2 (by norm_num)
    have hl : (wordsOf (witBody N w)).length = 2725 :=
      length_wordsOf 2725 _ (by rw [witBody_length_eq])
    rw [tailWit_words, List.getD_append_right _ _ _ _ (by omega), hl]
    interval_cases i <;> simp [rotatedWord, h0, h1, h2, lwu_counter]

section
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem rotate_witness_spec (N : HashOutput) (w : WCT9.Witness) (s : MachineState)
    (hp : s.pc = pcOf 42144)
    (hw : s.readWords (BitVec.ofNat 64 2048) 2729 = wordsOf (legacyWitList N w)) :
    ∃ t, Steps im s 16368 16368 t ∧ t.pc = pcOf 42161 ∧ t.getReg .x5 = 1 ∧
      t.getReg .x10 = 0 ∧ fetch im t = some (.base .ECALL) ∧
      t.readWords (BitVec.ofNat 64 2048) 2729 = wordsOf (witList N w) := by
  obtain ⟨t, st, pt, t5, t10, ht, mt⟩ := rotate_spec hc s hp
  refine ⟨t, st, pt, t5, t10, ht, ?_⟩
  have hl : (wordsOf (witList N w)).length = 2729 :=
    length_wordsOf 2729 _ (by rw [ClaudeWCT.W9.T3M.witList_length_eq])
  rw [← hl]
  apply readWords_ext t _ 2048
  intro i hi
  rw [hl] at hi
  rw [mt i hi, rotatedWord_witness N w s hw i hi]
end
#print axioms rotate_witness_spec
#print axioms ClaudeWCT.W9.Machine.Expand.front_spec
#print axioms ClaudeWCT.W9.Machine.Expand.front_pre30
end ClaudeWCT.W9.Machine.Expand.Rotation
