import SigGolfCandidate.T3M.Extract.Basic

namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem listInput_length (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    (listInput first hdr rest).length = 32 + 16 * rest.length := by
  simp only [listInput, List.length_append, bytesLE_length, digest_list_bytes_length]
theorem hdrBlock_prefix (a h : Digest) (rest : HashInput) :
    hdrBlock (bytesLE 16 a ++ bytesLE 16 h ++ rest) = bytesLE 16 h := by
  unfold hdrBlock
  rw [List.append_assoc, List.drop_left' (bytesLE_length 16 a), List.take_left' (bytesLE_length 16 h)]
theorem hdrBlock_pad64 (input : HashInput) (h : 32 ≤ input.length) : hdrBlock (pad64 input) = hdrBlock input := by
  unfold hdrBlock pad64
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
theorem hdrBlock_block4 (a b c d : Digest) : hdrBlock (block4 a b c d) = bytesLE 16 b := by
  unfold block4
  rw [List.append_assoc]
  exact hdrBlock_prefix a b _
theorem hdrBlock_listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    hdrBlock (pad64 (listInput first hdr rest)) = bytesLE 16 hdr := by
  rw [hdrBlock_pad64 _ (by rw [listInput_length]; omega)]
  exact hdrBlock_prefix first hdr _
theorem leafInput_eq_listInput {lay : Layer} (h0 : lay ≠ 0) (tree leaf : Nat) (ends : List Digest) :
    leafInput lay tree leaf ends = listInput (ends.getD 0 0) (leafTweak lay tree leaf) (ends.drop 1) := by
  simp only [leafInput, T3.leafInput, h0, if_false, listInput]
theorem leafInput_top (tree leaf : Nat) (ends : List Digest) :
    leafInput 0 tree leaf ends = bytesLE 16 (0 : Digest) ++ bytesLE 16 (leafTweak 0 tree leaf) ++
      ends.flatMap (bytesLE 16) := by
  have hz : bytesLE 16 (0 : Digest) = zero16 := by decide
  simp only [leafInput, T3.leafInput, if_true, hz]
theorem hdrBlock_leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    hdrBlock (pad64 (leafInput lay tree leaf ends)) = bytesLE 16 (leafTweak lay tree leaf) := by
  by_cases h0 : lay = 0
  · subst h0
    rw [leafInput_top, hdrBlock_pad64 _ (by simp [bytesLE_length]; omega), List.append_assoc]
    exact hdrBlock_prefix _ _ _
  · rw [leafInput_eq_listInput h0]
    exact hdrBlock_listInput _ _ _
end SigGolfCandidate.T3M.Extract
