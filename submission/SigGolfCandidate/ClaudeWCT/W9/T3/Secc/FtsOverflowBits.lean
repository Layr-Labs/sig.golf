import SigGolfCandidate.ClaudeWCT.WCT9.Core
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.FtsOverflowAlg

/-!
# The W9 digest index is uniform and independent of producer admissibility

`WCT9.digestIndex` reads bits 33..63 of the digest output; `WCT9.producerAdmissible` reads only bits outside
33..63 (children 0..6, 64.., fields 7..16, 71.., gate 242..255). XOR with `j·2^33` (`j < 2^31`) therefore preserves
admissibility and shifts the index by `j`, so every index fibre of an admissible-invariant event has the same size:
`2^31 · #{P ∧ idx = i} = #{P}`. Expectation forms: `expect_idx` (a fresh output's index is uniform) and
`expect_adm_le` (a fresh output stops the digest search at a uniform index).
-/

namespace ClaudeWCT.W9.T3.Security.FtsOverflow
open SigGolfCandidate.T3 ENNReal OracleComp OracleSpec OracleComp.EvalDist

/-- The W9 digest index as an element of `Fin (2^31)`. -/
def idxF (o : HashOutput) : Fin (2 ^ 31) := ⟨WCT9.digestIndex o, WCT9.digestIndex_lt o⟩

/-- The XOR mask moving the index field by `j`. -/
def idxMask (j : ℕ) : HashOutput := BitVec.ofNat 256 (j * 2 ^ 33)

theorem read_xor (x j b w : ℕ) (hj : j < 2 ^ 31) (h : b + w ≤ 33 ∨ 64 ≤ b) :
    (x ^^^ j * 2 ^ 33) / 2 ^ b % 2 ^ w = x / 2 ^ b % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor, Nat.testBit_mul_two_pow]
  by_cases hi : i < w
  · simp only [hi, decide_true, Bool.true_and]
    rcases h with h | h
    · have : ¬ 33 ≤ i + b := by omega
      simp [this]
    · have hlt : j.testBit (i + b - 33) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hlt]
  · simp [hi]

theorem toNat_xor_idxMask (o : HashOutput) {j : ℕ} (hj : j < 2 ^ 31) :
    (o ^^^ idxMask j).toNat = o.toNat ^^^ j * 2 ^ 33 := by
  rw [BitVec.toNat_xor, idxMask, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem childBase_ok (k : ℕ) : WCT9.childBase k + 7 ≤ 33 ∨ 64 ≤ WCT9.childBase k := by
  rcases Nat.lt_or_ge k 9 with hk | hk
  · interval_cases k <;> decide
  · left
    simp only [WCT9.childBase, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega)]
    simp

theorem fieldBase_ok (k : ℕ) : WCT9.fieldBase k + 10 ≤ 33 ∨ 64 ≤ WCT9.fieldBase k := by
  rcases Nat.lt_or_ge k 9 with hk | hk
  · interval_cases k <;> decide
  · left
    simp only [WCT9.fieldBase, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega)]
    simp

theorem child_xor (o : HashOutput) {j : ℕ} (hj : j < 2 ^ 31) (coord : WCT9.Coord) :
    WCT9.child (o ^^^ idxMask j) coord = WCT9.child o coord := by
  apply Fin.ext
  simp only [WCT9.child, toNat_xor_idxMask o hj]
  exact read_xor _ _ _ 7 hj (childBase_ok coord.val)

theorem field_xor (o : HashOutput) {j : ℕ} (hj : j < 2 ^ 31) (coord : WCT9.Coord) :
    WCT9.field (o ^^^ idxMask j) coord = WCT9.field o coord := by
  simp only [WCT9.field, toNat_xor_idxMask o hj]
  exact read_xor _ _ _ 10 hj (fieldBase_ok coord.val)

theorem producerAdmissible_xor (o : HashOutput) {j : ℕ} (hj : j < 2 ^ 31) :
    WCT9.producerAdmissible (o ^^^ idxMask j) = WCT9.producerAdmissible o := by
  have hrank : ∀ coord, WCT9.rank (o ^^^ idxMask j) coord = WCT9.rank o coord := fun coord => by
    simp only [WCT9.rank, field_xor o hj]
  have hcost : WCT9.jointCost (o ^^^ idxMask j) = WCT9.jointCost o := by
    simp only [WCT9.jointCost, WCT9.coordCost, hrank, child_xor o hj]
  have hadm : WCT9.admissible (o ^^^ idxMask j) = WCT9.admissible o := by
    simp only [WCT9.admissible, toNat_xor_idxMask o hj, read_xor _ _ 242 14 hj (Or.inr (by norm_num))]
    congr 1
    apply List.all_congr rfl
    intro coord
    rw [read_xor _ _ _ 10 hj (fieldBase_ok coord)]
  simp only [WCT9.producerAdmissible, WCT9.capOk, hcost, hadm]

theorem idxF_xor (o : HashOutput) {j : ℕ} (hj : j < 2 ^ 31) :
    (idxF (o ^^^ idxMask j)).val = (idxF o).val ^^^ j := by
  simp only [idxF, WCT9.digestIndex, toNat_xor_idxMask o hj]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor, Nat.testBit_mul_two_pow]
  by_cases hi : i < 31
  · simp [hi, show 33 ≤ i + 33 by omega]
  · have : j.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hi, this, show 33 ≤ i + 33 by omega]

theorem xor_idxMask_involutive (o : HashOutput) (j : ℕ) : o ^^^ idxMask j ^^^ idxMask j = o := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Index fibres of a mask-invariant event have equal size. -/
theorem fiber_card (P : HashOutput → Prop) [DecidablePred P]
    (hP : ∀ o j, j < 2 ^ 31 → (P (o ^^^ idxMask j) ↔ P o)) (i : Fin (2 ^ 31)) :
    2 ^ 31 * (Finset.univ.filter fun o => P o ∧ idxF o = i).card = (Finset.univ.filter P).card := by
  have heq : ∀ i i' : Fin (2 ^ 31), (Finset.univ.filter fun o => P o ∧ idxF o = i).card ≤
      (Finset.univ.filter fun o => P o ∧ idxF o = i').card := by
    intro i i'
    have hj : i.val ^^^ i'.val < 2 ^ 31 := Nat.xor_lt_two_pow i.isLt i'.isLt
    refine Finset.card_le_card_of_injOn (fun o => o ^^^ idxMask (i.val ^^^ i'.val)) ?_ ?_
    · intro o ho
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at ho ⊢
      refine ⟨(hP o _ hj).2 ho.1, Fin.ext ?_⟩
      rw [idxF_xor o hj, ho.2, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    · intro o _ o' _ h
      have := congrArg (fun x => x ^^^ idxMask (i.val ^^^ i'.val)) h
      simpa only [xor_idxMask_involutive] using this
  have hall : ∀ i i' : Fin (2 ^ 31), (Finset.univ.filter fun o => P o ∧ idxF o = i).card =
      (Finset.univ.filter fun o => P o ∧ idxF o = i').card := fun i i' => le_antisymm (heq i i') (heq i' i)
  have hsum : (Finset.univ.filter P).card = ∑ i' : Fin (2 ^ 31), (Finset.univ.filter fun o => P o ∧ idxF o = i').card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := idxF) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro i' _
    rw [Finset.filter_filter]
  rw [hsum, Finset.sum_congr rfl (fun i' _ => hall i' i), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

theorem card_idx (i : Fin (2 ^ 31)) : (Finset.univ.filter fun o : HashOutput => idxF o = i).card = 2 ^ 225 := by
  have h := fiber_card (fun _ : HashOutput => True) (fun _ _ _ => Iff.rfl) i
  simp only [true_and, Finset.filter_true_of_mem (fun (_ : HashOutput) _ => trivial), Finset.card_univ,
    Fintype.card_bitVec] at h
  omega

theorem expect_uniform (F : HashOutput → ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) F = (2 ^ 256)⁻¹ * ∑ o, F o := by
  rw [expectedValue_def, tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  rw [probOutput_uniformSample, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]

theorem pIdx_eq : pIdx = (2 ^ 256)⁻¹ * 2 ^ 225 := by
  rw [pIdx, show (2 : ℝ≥0∞) ^ 256 = 2 ^ 31 * 2 ^ 225 by ring, ENNReal.mul_inv (by left; positivity)
    (by left; finiteness), mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by finiteness), mul_one]

/-- A fresh output's index is uniform. -/
theorem expect_idx (X : Fin (2 ^ 31) → ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun o => X (idxF o)) = ∑ i, pIdx * X i := by
  rw [expect_uniform, ← Finset.sum_fiberwise Finset.univ idxF (fun o => X (idxF o)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_congr rfl (fun o ho => by rw [(Finset.mem_filter.1 ho).2]), Finset.sum_const, nsmul_eq_mul,
    show (Finset.univ.filter fun o : HashOutput => idxF o = i) = Finset.filter (fun o => idxF o = i) Finset.univ
      from rfl, card_idx, pIdx_eq]
  push_cast
  ring

/-- One fresh step of a search whose stop predicate `adm` ignores the index bits: it stops at a uniform index,
or continues. (Stated for a variable predicate: the kernel must never see closed cardinalities of `HashOutput`
sets in Nat arithmetic, which it would try to evaluate.) -/
theorem expect_adm_le_gen (adm : HashOutput → Bool) (hadm : ∀ o j, j < 2 ^ 31 → adm (o ^^^ idxMask j) = adm o)
    (X : Fin (2 ^ 31) → ℝ≥0∞) (Y M : ℝ≥0∞) (hX : ∑ i, pIdx * X i ≤ M) (hY : Y ≤ M) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun o => if adm o = true then X (idxF o) else Y) ≤ M := by
  set A := (Finset.univ.filter fun o : HashOutput => adm o = true).card
  set B := (Finset.univ.filter fun o : HashOutput => ¬ adm o = true).card
  have hAB : A + B = 2 ^ 256 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_bitVec]
  rw [expect_uniform, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun o => adm o = true)]
  have h1 : ∑ o ∈ Finset.univ.filter (fun o => adm o = true),
      (if adm o = true then X (idxF o) else Y) = ∑ i, (A : ℝ≥0∞) * pIdx * X i := by
    rw [Finset.sum_congr rfl (fun o ho => if_pos (Finset.mem_filter.1 ho).2),
      ← Finset.sum_fiberwise _ idxF (fun o => X (idxF o))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_congr rfl (fun o ho => by rw [(Finset.mem_filter.1 ho).2]), Finset.sum_const, nsmul_eq_mul,
      Finset.filter_filter]
    have hc := fiber_card (fun o => adm o = true) (fun o j hj => by rw [hadm o j hj]) i
    have h : (((Finset.univ.filter fun o : HashOutput => adm o = true ∧ idxF o = i).card : ℕ) : ℝ≥0∞) =
        ((2 ^ 31 * (Finset.univ.filter fun o : HashOutput => adm o = true ∧ idxF o = i).card : ℕ) : ℝ≥0∞) *
          pIdx := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pIdx, mul_comm (2 ^ 31 : ℝ≥0∞), mul_assoc,
        ENNReal.mul_inv_cancel (by positivity) (by finiteness), mul_one]
    rw [hc] at h
    rw [h]
  have h2 : ∑ o ∈ Finset.univ.filter (fun o => ¬ adm o = true),
      (if adm o = true then X (idxF o) else Y) = (B : ℝ≥0∞) * Y := by
    rw [Finset.sum_congr rfl (fun o ho => if_neg (Finset.mem_filter.1 ho).2), Finset.sum_const, nsmul_eq_mul]
  rw [h1, h2]
  have hsum : ∑ i, (A : ℝ≥0∞) * pIdx * X i = A * ∑ i, pIdx * X i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  calc (2 ^ 256 : ℝ≥0∞)⁻¹ * (A * ∑ i, pIdx * X i + B * Y)
      ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ * (A * M + B * M) := by gcongr
    _ = (2 ^ 256 : ℝ≥0∞)⁻¹ * ((A + B : ℕ) : ℝ≥0∞) * M := by push_cast; ring
    _ = M := by
      rw [hAB, Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]

/-- One fresh step of the W9 digest search stops at a uniform index or continues. -/
theorem expect_adm_le (X : Fin (2 ^ 31) → ℝ≥0∞) (Y M : ℝ≥0∞) (hX : ∑ i, pIdx * X i ≤ M) (hY : Y ≤ M) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun o => if WCT9.producerAdmissible o = true then X (idxF o) else Y) ≤ M :=
  expect_adm_le_gen WCT9.producerAdmissible (fun o _ hj => producerAdmissible_xor o hj) X Y M hX hY

end ClaudeWCT.W9.T3.Security.FtsOverflow
