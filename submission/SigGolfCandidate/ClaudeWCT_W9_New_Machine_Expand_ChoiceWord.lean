import SigGolfCandidate.ClaudeWCT_W9_T3M_Witness_Honest
set_option Elab.async false

/-! # The choice hint word of the paired witness (configuration e7b, expand readout)

The 8-byte witness word at byte `choiceOff = 21104 = 8 * 2638` is the legacy word with its low byte replaced by
`choiceByte witness.topHigh`; the expand `end` routine produces exactly this with `sb` of the choice flag. -/

namespace ClaudeWCT.W9.T3M.PairedReadout
open RiscvZkvm.Rv64 SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem choiceByte_extract (output : HashOutput) (witness : SharedForest.Witness) :
    (Paired.witEnc output witness).extractLsb' (8 * choiceOff) (8 * 1) = (choiceByte witness.topHigh).toBitVec := by
  have hlen : choiceOff < (Paired.witListBase output witness).length := by
    rw [witListBase_length]; decide
  unfold Paired.witEnc
  rw [extract_readLE _ 22012 choiceOff 1 (by decide)]
  have hd : ((Paired.witList output witness).drop choiceOff).take 1 = [choiceByte witness.topHigh] := by
    unfold Paired.witList
    rw [List.drop_set, if_neg (lt_irrefl _), Nat.sub_self]
    obtain ⟨y, ys, hy⟩ : ∃ y ys, (Paired.witListBase output witness).drop choiceOff = y :: ys := by
      cases h : (Paired.witListBase output witness).drop choiceOff with
      | nil => have := congrArg List.length h; simp at this; omega
      | cons y ys => exact ⟨y, ys, rfl⟩
    rw [hy]; rfl
  rw [hd]
  cases witness.topHigh <;> decide

theorem choiceWord_witEnc (output : HashOutput) (witness : SharedForest.Witness) :
    (Paired.witEnc output witness).extractLsb' (8*(8*2638)) 64 =
      replaceByte ((ClaudeWCT.W9.T3M.witEnc output (Paired.mainWitness witness)).extractLsb' (8*(8*2638)) 64) 0
        (choiceByte witness.topHigh).toBitVec := by
  have hb : (baseEnc output witness).extractLsb' (8*(8*2638)) 64 =
      (ClaudeWCT.W9.T3M.witEnc output (Paired.mainWitness witness)).extractLsb' (8*(8*2638)) 64 :=
    word_prefixEnc _ (Paired.forestBytes_length output witness) _ _ (8*2638) (by norm_num)
  have hc := choiceByte_extract output witness
  rw [← hb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hco : choiceOff = 8*2638 := rfl
  simp only [replaceByte, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    Nat.zero_mul, Nat.sub_zero, show ¬ (i < 0) by omega, decide_false, Bool.not_false]
  by_cases h8 : i < 8
  · have e := congrArg (fun x : BitVec 8 => x.getLsbD i) hc
    simp only [BitVec.getLsbD_extractLsb', show i < 8*1 by omega, decide_true, Bool.true_and, hco] at e
    have h2 : (255 : Nat).testBit i = true := by
      have : (255 : Nat) = 2 ^ 8 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]; simp; omega
    simp [BitVec.getLsbD_ofNat, h2, h8, e]
    all_goals (intros; omega)
  · have h2 : (255 : Nat).testBit i = false := by
      have : (255 : Nat) = 2 ^ 8 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]; simpa using h8
    rw [witEnc_getLsbD _ _ _ (by rw [hco]; omega)]
    simp [BitVec.getLsbD_ofNat, h2, BitVec.getLsbD_of_ge _ i (by omega : 8 ≤ i)]
#print axioms choiceWord_witEnc
end ClaudeWCT.W9.T3M.PairedReadout
