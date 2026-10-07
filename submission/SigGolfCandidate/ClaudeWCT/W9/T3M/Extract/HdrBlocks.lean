import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Basic
import SigGolfCandidate.T3M.Extract.HeaderBytes
import SigGolfCandidate.ClaudeWCT.WCT9.Domains

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3M.Extract (canonicalHeader_high_zero canonicalHeader_marker_ne)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem hdrBlock_prefix' (a h : Digest) (rest : HashInput) :
    hdrBlock (bytesLE 16 a ++ bytesLE 16 h ++ rest) = bytesLE 16 h := by
  unfold hdrBlock
  rw [List.append_assoc, List.drop_left' (bytesLE_length 16 a), List.take_left' (bytesLE_length 16 h)]
theorem hdrBlock_pad64' (input : HashInput) (h : 32 ≤ input.length) :
    hdrBlock (pad64 input) = hdrBlock input := by
  unfold hdrBlock pad64
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
theorem hdrBlock_block4' (a b c d : Digest) : hdrBlock (block4 a b c d) = bytesLE 16 b := by
  unfold block4
  rw [List.append_assoc]
  exact hdrBlock_prefix' a b _
theorem hdrBlock_listInput' (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    hdrBlock (pad64 (listInput first hdr rest)) = bytesLE 16 hdr := by
  have hl : 32 ≤ (listInput first hdr rest).length := by
    simp only [listInput, List.length_append, bytesLE_length]; omega
  rw [hdrBlock_pad64' _ hl]
  exact hdrBlock_prefix' first hdr _
theorem bytesLE_zero' : bytesLE 16 (0 : Digest) = zero16 := by decide
theorem wctChainInput_block4 (index coord child t step : Nat) (value : Digest) :
    WCT9.chainInput index coord child t step value =
      block4 0 (WCT9.ftsChainHeader index coord child t step) 0 value := by
  simp only [WCT9.chainInput, block4, bytesLE_zero']
theorem pad64_wctChainInput (index coord child t step : Nat) (value : Digest) :
    pad64 (WCT9.chainInput index coord child t step value) = WCT9.chainInput index coord child t step value := by
  rw [wctChainInput_block4, pad64_block4]
theorem hdrBlock_wctChainInput (index coord child t step : Nat) (value : Digest) :
    hdrBlock (WCT9.chainInput index coord child t step value) =
      bytesLE 16 (WCT9.ftsChainHeader index coord child t step) := by
  rw [wctChainInput_block4, hdrBlock_block4']
theorem hdrBlock_wctLeafInput (index coord child : Nat) (ends : List Digest) :
    hdrBlock (pad64 (wctLeafInput index coord child ends)) = bytesLE 16 (WCT9.ftsLeafHeader index coord child) :=
  hdrBlock_listInput' _ _ _
theorem hdrBlock_forestInput (index : Nat) (pairs : List (Digest × Digest)) :
    hdrBlock (pad64 (forestInput index pairs)) = bytesLE 16 (header 15 0 index 0 0) := by
  have hl : 32 ≤ (forestInput index pairs).length := by
    simp only [forestInput, WCT9.forestInput, zero16, List.length_append, List.length_replicate, bytesLE_length]
    omega
  rw [hdrBlock_pad64' _ hl]
  unfold forestInput WCT9.forestInput
  rw [← bytesLE_zero']
  exact hdrBlock_prefix' 0 _ _
theorem hdrBlock_nodeInputP (tag lay tree heap : Nat) (left pad right : Digest) :
    hdrBlock (pad64 (nodeInputP tag lay tree heap left pad right)) = bytesLE 16 (nodeTweak tag lay tree heap) := by
  rw [pad64_nodeInputP, nodeInputP, hdrBlock_block4']
theorem hdrBlock_wotsChainInput (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    hdrBlock (chainInput lay tree leaf i step value) = bytesLE 16 (chainHeader lay tree leaf i step) :=
  chainInput_header lay tree leaf i step value
theorem hdrBlock_leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    hdrBlock (pad64 (leafInput lay tree leaf ends)) = bytesLE 16 (leafTweak lay tree leaf) := by
  unfold leafInput SigGolfCandidate.T3.leafInput
  split
  · rw [hdrBlock_pad64' _ (by simp [zero16, bytesLE_length]), show zero16 = bytesLE 16 (0 : Digest) from
      bytesLE_zero'.symm, List.append_assoc]
    exact hdrBlock_prefix' 0 _ _
  · rw [hdrBlock_pad64' _ (by simp [bytesLE_length]; omega), List.append_assoc]
    exact hdrBlock_prefix' _ _ _
theorem listInput_length' (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    (listInput first hdr rest).length = 32 + 16 * rest.length := by
  simp only [listInput, List.length_append, bytesLE_length, digest_list_bytes_length]
theorem hdrBlock_honestInput (answers : Answers) (p : Pos) :
    hdrBlock (honestInput answers p) = bytesLE 16 p.hdr := by
  cases p with
  | chain lay tree lf i step =>
      simp only [honestInput, Pos.hdr, chainInput_padded, hdrBlock, chainInput_header]
  | leaf lay tree lf => simp only [honestInput, Pos.hdr]; rw [hdrBlock_leafInput]
  | node lay tree level nd =>
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_nodeInputP]
  | forest index => simp only [honestInput, Pos.hdr]; rw [hdrBlock_forestInput]
  | wctChain index coord child t step =>
      simp only [honestInput, Pos.hdr]; rw [pad64_wctChainInput, hdrBlock_wctChainInput]
  | wctLeaf index coord child =>
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_wctLeafInput]
  | wctNode index coord level nd =>
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_nodeInputP]; rfl
