import SigGolfCandidate.ClaudeWCT_W9_T3M_Extract_Basic
import SigGolfCandidate.T3M_Extract_HeaderBytes
import SigGolfCandidate.ClaudeWCT_WCT9_Domains

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
/-- Witness stack: the FTS step input in either format (G chains 1, 3: `value | header | 0 | 0`). -/
theorem ftsChainInputW_block4 (index coord child t step : Nat) (value : Digest) :
    WCT9.ftsChainInputW index coord child t step value =
      if WCT9.ftsIsG t then block4 value (WCT9.ftsChainHeader index coord child t step) 0 0
      else block4 0 (WCT9.ftsChainHeader index coord child t step) 0 value := by
  unfold WCT9.ftsChainInputW
  split
  · simp only [block4, bytesLE_zero']
  · exact wctChainInput_block4 index coord child t step value
theorem hdrBlock_ftsChainInputW (index coord child t step : Nat) (value : Digest) :
    hdrBlock (WCT9.ftsChainInputW index coord child t step value) =
      bytesLE 16 (WCT9.ftsChainHeader index coord child t step) := by
  rw [ftsChainInputW_block4]
  split <;> exact hdrBlock_block4' _ _ _ _
theorem hdrBlock_wctLeafInput (index coord child : Nat) (ends : List Digest) :
    hdrBlock (pad64 (wctLeafInput index coord child ends)) = bytesLE 16 (WCT9.ftsLeafHeader index coord child) :=
  hdrBlock_listInput' _ _ _
theorem hdrBlock_wctLeafInputP (index coord child : Nat) (pad : Digest) (ends : List Digest) :
    hdrBlock (pad64 (wctLeafInputP index coord child pad ends)) = bytesLE 16 (WCT9.ftsLeafHeader index coord child) :=
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
theorem hdrBlock_merkleNodeInput (lay tree heap : Nat) (left right : Digest) :
    hdrBlock (pad64 (WCT9.merkleNodeInput lay tree heap left right)) = bytesLE 16 (WCT9.merkleTweak lay tree heap) := by
  unfold WCT9.merkleNodeInput
  rw [hdrBlock_pad64' _ (by simp [bytesLE_length, zero16]), List.append_assoc]
  exact hdrBlock_prefix' _ _ _
/-- Top-nonce layer: the nonce slot is the third block, so the header block is the tweak. -/
theorem hdrBlock_merkleNodeInputN (lay tree heap n : Nat) (left right : Digest) :
    hdrBlock (pad64 (WCT9.merkleNodeInputN lay tree heap n left right)) =
      bytesLE 16 (WCT9.merkleTweak lay tree heap) := by
  unfold WCT9.merkleNodeInputN
  rw [hdrBlock_pad64' _ (by simp [bytesLE_length]), List.append_assoc]
  exact hdrBlock_prefix' _ _ _
theorem hdrBlock_wotsChainInput (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    hdrBlock (chainInput lay tree leaf i step value) = bytesLE 16 (chainHeader lay tree leaf i step) :=
  chainInput_header lay tree leaf i step value
theorem hdrBlock_leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    hdrBlock (pad64 (leafInput lay tree leaf ends)) = bytesLE 16 (leafTweak lay tree leaf) := by
  unfold leafInput SigGolfCandidate.T3.leafInput
  split <;>
  · rw [hdrBlock_pad64' _ (by simp [bytesLE_length]; omega), List.append_assoc]
    exact hdrBlock_prefix' _ _ _

theorem listInput_length' (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    (listInput first hdr rest).length = 32 + 16 * rest.length := by
  simp only [listInput, List.length_append, bytesLE_length, digest_list_bytes_length]
theorem hdrBlock_honestInput (answers : Answers) (p : Pos) :
    hdrBlock (honestInput answers p) = bytesLE 16 p.hdr := by
  cases p with
  | chain lay tree lf i step =>
      simp only [honestInput, Pos.hdr, WCT9.chainInputW_padded, hdrBlock, WCT9.chainInputW_header]
  | leaf lay tree lf => simp only [honestInput, Pos.hdr]; rw [hdrBlock_leafInput]
  | node lay tree level nd =>
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_merkleNodeInputN]
  | forest index => simp only [honestInput, Pos.hdr]; rw [hdrBlock_forestInput]
  | wctChain index coord child t step =>
      simp only [honestInput, Pos.hdr]; rw [WCT9.ftsChainInputW_padded, hdrBlock_ftsChainInputW]
  | wctLeaf index coord child =>
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_wctLeafInputP]
  | wctNode index coord level nd =>
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_nodeInputP]; rfl
theorem pad64_length_of_mod {x : HashInput} (h : x.length % 64 = 0) : (pad64 x).length = x.length := by
  unfold pad64; simp [h]
theorem honestInput_length (answers : Answers) (p : Pos) : (honestInput answers p).length = p.len := by
  cases p with
  | chain lay tree leaf i step =>
      simp only [honestInput, Pos.len]
      rw [pad64_length_of_mod] <;> simp [WCT9.chainInputW_length]
  | leaf lay tree leaf =>
      simp only [honestInput, Pos.len, leafInput, SigGolfCandidate.T3.leafInput]
      split
      · rename_i h0
        have hc' : chainCount lay = 51 := by subst h0; rfl
        rw [pad64_length_of_mod] <;>
          simp only [List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop,
            List.length_map, List.length_range, hc'] <;> decide
      · rename_i h0
        have hc' : chainCount lay = 43 := by fin_cases lay <;> simp_all <;> decide
        rw [pad64_length_of_mod] <;>
          simp only [List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop,
            List.length_map, List.length_range, hc'] <;> decide
  | node lay tree level nd =>
      simp only [honestInput, Pos.len]
      rw [WCT9.pad64_merkleNodeInputN, WCT9.merkleNodeInputN_length]
  | forest index =>
      simp only [honestInput, Pos.len]
      have hl : (forestInput index (ftsPairsHonest answers index)).length = 320 := by
        simp only [forestInput, WCT9.forestInput, List.length_append, zero16, List.length_replicate, bytesLE_length,
          List.length_flatMap, ftsPairsHonest, List.map_map]
        simp [Function.comp_def]
      rw [pad64_length_of_mod] <;> rw [hl]
  | wctChain index coord child t step =>
      simp only [honestInput, Pos.len]
      rw [WCT9.ftsChainInputW_padded, WCT9.ftsChainInputW_length]
  | wctLeaf index coord child =>
      simp only [honestInput, Pos.len]
      rw [pad64_length_of_mod] <;> simp [wctLeafInputP, listInput, bytesLE_length, wctEnds]
  | wctNode index coord level nd =>
      simp only [honestInput, Pos.len]
      rw [pad64_length_of_mod] <;> simp [nodeInputP]

theorem tweakLow_eq_low (h : BitVec 128) : tweakLow h = (h.extractLsb' 0 64).toNat := by
  unfold tweakLow; rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
/-- C4: the low word of a 16-byte header is read from its first 8 bytes. -/
theorem readLE_take8 (h : BitVec 128) : readLE ((bytesLE 16 h).take 8) = tweakLow h := by
  have he : h = h.extractLsb' 64 64 ++ h.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := h)).symm
  conv_lhs => rw [he, SigGolfCandidate.T3M.Extract.bytesLE_header_words, List.take_left' (bytesLE_length 8 _)]
  rw [SigGolfCandidate.T3M.readLE_bytesLE, tweakLow_eq_low]
theorem topLow_bytesLE_iff (h : BitVec 128) : TopLow (bytesLE 16 h) ↔ 1 ≤ tweakLow h ∧ tweakLow h < 2 ^ 16 := by
  unfold TopLow; rw [readLE_take8]
