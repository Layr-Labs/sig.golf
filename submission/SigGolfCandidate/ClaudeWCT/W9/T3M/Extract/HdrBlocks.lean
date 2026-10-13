import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Basic
import SigGolfCandidate.T3M.Extract.HeaderBytes
import SigGolfCandidate.ClaudeWCT.WCT9.Domains

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
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
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_wctLeafInputP]
  | wctNode index coord level nd =>
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_nodeInputP]; rfl
theorem length_honestInput (answers : Answers) (p : Pos) : (honestInput answers p).length = p.len := by
  cases p with
  | chain lay tree lf i step =>
      simp only [honestInput, Pos.len, chainInput_padded]
      simp [chainInput, zero16, bytesLE_length]
  | leaf lay tree lf =>
      simp only [honestInput, Pos.len, Cost.pad64_length, leafInput, leafInput_length, List.length_map,
        List.length_range]
      fin_cases lay <;> simp [chainCount]
  | node lay tree level nd =>
      simp only [honestInput, Pos.len, nodeInputP, pad64_block4, block4_length]
  | forest index =>
      simp only [honestInput, Pos.len, Cost.pad64_length, forestInput, WCT9.forestInput, zero16,
        List.length_append, List.length_replicate, bytesLE_length, WCT9.pairs_bytes_length,
        ftsPairsHonest_length]
  | wctChain index coord child t step =>
      simp only [honestInput, Pos.len, wctChainInput_block4, pad64_block4, block4_length]
  | wctLeaf index coord child =>
      simp only [honestInput, Pos.len, Cost.pad64_length, wctLeafInputP, listInput_length', List.length_cons,
        List.length_drop, wctEnds_length]
  | wctNode index coord level nd =>
      simp only [honestInput, Pos.len, nodeInputP, pad64_block4, block4_length]
/-! ### Campaign S1: witness high words of one-word labels -/
theorem nodeTweak_high_hyper {lay : Nat} (h4 : lay < 4) (tree heap : Nat) :
    (nodeTweak 3 lay tree heap).extractLsb' 64 64 = 0 := by
  by_cases h0 : lay = 0
  · subst h0; rw [nodeTweak_top]; exact BitVec.extractLsb'_append_eq_left
  · rw [nodeTweak_lower h0 h4]; exact BitVec.extractLsb'_append_eq_left
/-- A one-word label (honest high word 0) equals its padded version only for the zero pad. -/
theorem withHigh_eq_self {t : BitVec 128} (h0 : t.extractLsb' 64 64 = 0) {hp : BitVec 64}
    (h : withHigh t hp = t) : hp = 0 := by
  unfold withHigh at h
  rw [if_pos h0] at h
  have := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) h
  simp only [BitVec.extractLsb'_append_eq_left] at this
  rw [this, h0]
theorem withHigh_of_high_zero {t : BitVec 128} (h0 : t.extractLsb' 64 64 = 0) (hp : BitVec 64) :
    withHigh t hp = hp ++ t.extractLsb' 0 64 := by
  unfold withHigh; rw [if_pos h0]
/-- The padded node header has the key of the honest header: either the label is a two-word label (FTS levels 4/5,
`withHigh` keeps it) or a one-word label whose low word is a padded label. -/
theorem canonicalHeaderL_withHigh_node {lay : Nat} (h13 : lay < 13) (tree heap : Nat)
    (hheap : 4 ≤ lay → heap % 2 ^ 64 ≠ 0) (hp : BitVec 64) :
    canonicalHeaderL 64 (bytesLE 16 (withHigh (nodeTweak 3 lay tree heap) hp)) =
      canonicalHeaderL 64 (bytesLE 16 (nodeTweak 3 lay tree heap)) := by
  by_cases h0 : (nodeTweak 3 lay tree heap).extractLsb' 64 64 = 0
  · rw [withHigh_of_high_zero h0]
    have ht : nodeTweak 3 lay tree heap =
        (nodeTweak 3 lay tree heap).extractLsb' 64 64 ++ (nodeTweak 3 lay tree heap).extractLsb' 0 64 :=
      (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := nodeTweak 3 lay tree heap)).symm
    conv_rhs => rw [ht]
    apply SigGolfCandidate.T3M.Extract.canonicalHeaderL_high_irrelevant
    have hlow : ((nodeTweak 3 lay tree heap).extractLsb' 0 64).toNat = tweakLow (nodeTweak 3 lay tree heap) := by
      rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]; rfl
    rw [hlow]
    unfold padLabel
    by_cases h4 : lay < 4
    · by_cases hz : lay = 0
      · subst hz; rw [nodeTweak_top_low]
        have := topNodeWord_pos heap; have := topNodeWord_lt heap
        left; omega
      · rw [nodeTweak_lower_low hz h4, lowerNodeWord_toNat]
        right; right
        have := Nat.mod_lt heap (show 0 < 128 by decide)
        have := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
        have := Nat.mod_lt (lay - 1) (show 0 < 256 by decide)
        omega
    · rw [nodeTweak_fts_low (by omega) h13]
      by_cases hn : FtsNew heap
      · rw [if_pos hn]
        right; left
        rw [ftsNodeWordH_toNat]
        obtain ⟨h8, h128⟩ := hn
        omega
      · exfalso
        have hh := congrArg BitVec.toNat h0
        rw [nodeTweak_fts (by omega) h13 tree hn, BitVec.extractLsb'_append_eq_left] at hh
        simp only [BitVec.toNat_ofNat, BitVec.toNat_zero] at hh
        exact hheap (by omega) hh
  · unfold withHigh; rw [if_neg h0]

theorem hdrBlock_merkleInput (tag lay tree h leaf : Nat) (path pads : Nat → Digest) (step : Nat) (value : Digest) :
    hdrBlock (pad64 (merkleInput tag lay tree h leaf path pads step value)) =
      bytesLE 16 (nodeTweak tag lay tree (2 ^ (h - step - 1) + leaf / 2 ^ (step + 1))) := by
  unfold merkleInput
  dsimp only
  split <;> rw [pad64_nodeInputP, nodeInputP, hdrBlock_block4']
theorem sameHeader_merkleInputH (lay tree h leaf : Nat) (h13 : lay < 13) (path pads : Nat → Digest)
    (hpads : Nat → BitVec 64) (step : Nat) (value : Digest) (path' : Nat → Digest) (value' : Digest)
    (hheap : 4 ≤ lay → (2 ^ (h - step - 1) + leaf / 2 ^ (step + 1)) % 2 ^ 64 ≠ 0) :
    SameHeader (pad64 (merkleInputH 3 lay tree h leaf path pads hpads step value))
      (pad64 (merkleInput 3 lay tree h leaf path' (fun _ => 0) step value')) := by
  unfold SameHeader keyOf
  have h1 : (pad64 (merkleInputH 3 lay tree h leaf path pads hpads step value)).length = 64 := by
    unfold merkleInputH; dsimp only; split <;> simp [nodeInputPH]
  have h2 : (pad64 (merkleInput 3 lay tree h leaf path' (fun _ => 0) step value')).length = 64 := by
    unfold merkleInput; dsimp only; split <;> simp [nodeInputP]
  rw [h1, h2, hdrBlock_merkleInput]
  have hb : hdrBlock (pad64 (merkleInputH 3 lay tree h leaf path pads hpads step value)) =
      bytesLE 16 (withHigh (nodeTweak 3 lay tree (2 ^ (h - step - 1) + leaf / 2 ^ (step + 1))) (hpads step)) := by
    unfold merkleInputH nodeInputPH; dsimp only; split <;> rw [pad64_block4, hdrBlock_block4']
  rw [hb, canonicalHeaderL_withHigh_node h13 _ _ hheap]
