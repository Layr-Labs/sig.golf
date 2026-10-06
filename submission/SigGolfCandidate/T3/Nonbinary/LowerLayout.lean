import SigGolfCandidate.T3.Core

namespace SigGolfCandidate.T3
theorem lowerWord_lt (v : Digest) : lowerWord v < 2 ^ 126 := by
  unfold lowerWord
  have := v.isLt
  norm_num at *
  omega
theorem lowerPack_toNat (n : Nat) :
    (lowerPack n).toNat = n % 2 ^ 63 + 2 ^ 63 + n / 2 ^ 63 % 2 ^ 63 * 2 ^ 64 + 2 ^ 127 := by
  unfold lowerPack
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  norm_num
  omega
theorem lowerSpare_lowerPack (n : Nat) : lowerSpare (lowerPack n) := by
  unfold lowerSpare
  rw [lowerPack_toNat]
  norm_num
  omega
theorem lowerWord_lowerPack {n : Nat} (hn : n < 2 ^ 126) : lowerWord (lowerPack n) = n := by
  unfold lowerWord
  rw [lowerPack_toNat]
  norm_num at *
  omega
theorem lowerPack_lowerWord {v : Digest} (hv : lowerSpare v) : lowerPack (lowerWord v) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [lowerPack_toNat]
  unfold lowerWord
  unfold lowerSpare at hv
  have := v.isLt
  norm_num at *
  omega
theorem testBit_lowerWord (v : Digest) (j : Nat) :
    (lowerWord v).testBit j =
      if j < 63 then v.toNat.testBit j else (decide (j < 126) && v.toNat.testBit (j + 1)) := by
  have h : lowerWord v = 2 ^ 63 * (v.toNat / 2 ^ 64 % 2 ^ 63) + v.toNat % 2 ^ 63 := by unfold lowerWord; ring
  rw [h, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by positivity))]
  split_ifs with hj
  · rw [Nat.testBit_mod_two_pow]; simp [hj]
  · simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    rw [show j - 63 + 64 = j + 1 by omega]
    congr 1
    simp only [decide_eq_decide]
    omega
theorem lowerShift_digit (v : Digest) {i : Nat} (hi : i < 42) :
    v.toNat / 2 ^ lowerShift i % 8 = lowerWord v / 2 ^ (3 * i) % 8 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, testBit_lowerWord]
  by_cases hb : b < 3
  · simp only [hb, decide_true, Bool.true_and]
    unfold lowerShift
    split_ifs with h1 h2 h2
    · rw [Nat.add_comm]
    · omega
    · omega
    · simp only [show b + 3 * i < 126 by omega, decide_true, Bool.true_and]
      congr 1
      omega
  · simp [hb]
theorem coreDigit_lower {lay : Layer} (hl : lay ≠ 0) (v : Digest) {i : Nat} (hi : i < 42) :
    coreDigit lay v i = lowerWord v / 2 ^ (3 * i) % 8 := by
  simp only [coreDigit, hl, if_false]
  exact lowerShift_digit v hi
theorem dataDigits_lowerWord {lay : Layer} (hl : lay ≠ 0) (v : Digest) :
    dataDigits lay v = (List.range 42).map fun i => lowerWord v / 2 ^ (3 * i) % 8 := by
  simp only [dataDigits, dataCount, hl, if_false]
  apply List.map_congr_left
  intro i hi
  exact coreDigit_lower hl v (List.mem_range.mp hi)
theorem decode_lowerWord {lay : Layer} (hl : lay ≠ 0) (v : Digest) :
    decode lay v =
      let digits := (List.range 42).map fun i => lowerWord v / 2 ^ (3 * i) % 8
      if lowerSpare v ∧ digits.sum ≤ target lay ∧ target lay - digits.sum < 8 then
        some (digits ++ [target lay - digits.sum])
      else none := by
  have hb : ¬ v.toNat ≥ 2 ^ encodedBits lay := by
    simp only [encodedBits, hl, if_false]; have := v.isLt; omega
  unfold decode
  rw [if_neg hb, dataDigits_lowerWord hl v]
  simp only [hl, if_false]
def lowerSpareEquiv : {v : Digest // lowerSpare v} ≃ Fin (2 ^ 126) where
  toFun v := ⟨lowerWord v.val, lowerWord_lt v.val⟩
  invFun n := ⟨lowerPack n.val, lowerSpare_lowerPack n.val⟩
  left_inv v := Subtype.ext (lowerPack_lowerWord v.property)
  right_inv n := Fin.ext (lowerWord_lowerPack n.isLt)
theorem card_lowerSpare_filter (P : Nat → Prop) [DecidablePred P] :
    (Finset.univ.filter fun v : Digest => lowerSpare v ∧ P (lowerWord v)).card =
      (Finset.univ.filter fun v : Digest => v.toNat < 2 ^ 126 ∧ P v.toNat).card := by
  classical
  refine Finset.card_bij (fun v _ => BitVec.ofNat 128 (lowerWord v)) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    have h := lowerWord_lt v
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h.trans (by norm_num))]
    exact ⟨h, hv.2⟩
  · intro a ha b hb he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have h := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((lowerWord_lt a).trans (by norm_num)),
      Nat.mod_eq_of_lt ((lowerWord_lt b).trans (by norm_num))] at h
    rw [← lowerPack_lowerWord ha.1, ← lowerPack_lowerWord hb.1, h]
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine ⟨lowerPack w.toNat, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨lowerSpare_lowerPack _, by rw [lowerWord_lowerPack hw.1]; exact hw.2⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, lowerWord_lowerPack hw.1, Nat.mod_eq_of_lt w.isLt]
end SigGolfCandidate.T3
