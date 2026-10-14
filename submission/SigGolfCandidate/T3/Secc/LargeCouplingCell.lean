import SigGolfCandidate.T3.Secc.LargeResidualRouter

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem width_ge (lay : Layer) (i : Nat) : 2 ≤ width lay i := by
  unfold width; norm_num
theorem slotValue_append_left (X Y : HashInput) (k : Nat) (hk : 16 * (k + 1) ≤ X.length) :
    slotValue (X ++ Y) k = slotValue X k := by
  unfold slotValue
  congr 1
  rw [List.drop_append_of_le_length (by omega)]
  rw [List.take_append_of_le_length (by simp; omega)]
theorem slotValue_pad64 (X : HashInput) (k : Nat) (hk : 16 * (k + 1) ≤ X.length) :
    slotValue (pad64 X) k = slotValue X k := slotValue_append_left _ _ k hk
theorem slotValue_bytes_cons (x : Digest) (rest : HashInput) : slotValue (bytesLE 16 x ++ rest) 0 = x := by
  unfold slotValue
  simp only [Nat.mul_zero, List.drop_zero]
  rw [List.take_append_of_le_length (by rw [bytesLE_length])]
  rw [List.take_of_length_le (by rw [bytesLE_length])]
  exact Correctness.readDigest_bytesLE x
theorem slotValue_shift (X Y : HashInput) (k : Nat) (hX : X.length = 16) :
    slotValue (X ++ Y) (k + 1) = slotValue Y k := by
  unfold slotValue
  congr 1
  rw [show 16 * (k + 1) = X.length + 16 * k by omega, List.drop_append,
    List.drop_eq_nil_of_le (by omega), List.nil_append]
  simp
theorem slotValue_flatMap (values : List Digest) (rest : HashInput) (j : Nat) (hj : j < values.length) :
    slotValue (values.flatMap (bytesLE 16) ++ rest) j = values.getD j 0 := by
  induction values generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
      rw [List.flatMap_cons, List.append_assoc]
      cases j with
      | zero => exact slotValue_bytes_cons x _
      | succ j =>
          rw [slotValue_shift _ _ j (bytesLE_length _ _)]
          simp only [List.getD_cons_succ]
          exact ih j (by simpa using hj)
theorem slotValue_block4 (a b c d : Digest) :
    slotValue (block4 a b c d) 0 = a ∧ slotValue (block4 a b c d) 2 = c ∧ slotValue (block4 a b c d) 3 = d := by
  have hl : ∀ x : Digest, (bytesLE 16 x).length = 16 := fun x => bytesLE_length 16 x
  unfold block4
  refine ⟨?_, ?_, ?_⟩
  · rw [List.append_assoc, List.append_assoc]; exact slotValue_bytes_cons a _
  · rw [List.append_assoc, List.append_assoc, slotValue_shift _ _ 1 (hl a), slotValue_shift _ _ 0 (hl b)]
    exact slotValue_bytes_cons c _
  · rw [List.append_assoc, List.append_assoc, slotValue_shift _ _ 2 (hl a), slotValue_shift _ _ 1 (hl b),
      slotValue_shift _ _ 0 (hl c)]
    have := slotValue_bytes_cons d []
    simpa using this
theorem slotValue_listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) (i : Nat)
    (hi : i ≤ rest.length) : slotValue (pad64 (Extract.listInput first hdr rest)) (listBlock i) =
      (first :: rest).getD i 0 := by
  have hlen := Extract.listInput_length first hdr rest
  unfold listBlock
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos rfl, slotValue_pad64 _ 0 (by omega)]
    unfold Extract.listInput
    rw [List.append_assoc]
    exact slotValue_bytes_cons first _
  · rw [if_neg h0, slotValue_pad64 _ _ (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    unfold Extract.listInput
    rw [List.append_assoc, show j + 1 + 1 = (j + 1) + 1 from rfl,
      slotValue_shift _ _ (j + 1) (bytesLE_length _ _), slotValue_shift _ _ j (bytesLE_length _ _)]
    simp only [List.getD_cons_succ]
    have := slotValue_flatMap rest [] j (by omega)
    simpa using this
theorem chainRow_block4 (p : ChainGraph.Point) (x : Digest) :
    ChainGraph.row p x = block4 0 (chainHeader p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val p.2.val) 0 x := by
  simp only [ChainGraph.row, chainInput, block4, show zero16 = bytesLE 16 (0 : Digest) by decide]
theorem chainCount_pos (lay : Layer) : 0 < chainCount lay := by fin_cases lay <;> decide
end SigGolfCandidate.T3.Security.LargeResidual
