import SigGolfCandidate.ClaudeWCT_W9_T3M_Extract_Leaf
import SigGolfCandidate.ClaudeWCT_W9_T3M_Extract_Defs

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open ClaudeWCT.WCT9 (wotsTree wotsSeed wotsEnd wotsValue wotsRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3M.Extract (canonicalHeader_high_irrelevant)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def layerChains (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M (List Digest) :=
  (List.finRange (chainCount lay)).mapM fun i =>
    chainPW lay (route index lay).2 (route index lay).1 i.val (digits.getD i.val 0)
      (maxDigit lay i.val - digits.getD i.val 0) (wchainPads w lay i.val).1 (wchainPads w lay i.val).2
      (wchainHeaderPad w lay i.val) (wvalueFor w lay digits i.val)
theorem layerLeafP_eq (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerLeafP w index lay digits =
      (layerChains w index lay digits >>= WCT9.leafHashW lay (route index lay).2 (route index lay).1 (wtopLeafPad w)
        (wleafHigh w lay)) := rfl
theorem chainCount_pos (lay : Layer) : 0 < chainCount lay := by fin_cases lay <;> decide
theorem merkleNodeInput_top (tree heap : Nat) (left right : Digest) :
    WCT9.merkleNodeInput 0 tree heap left right = nodeInputP 3 0 tree heap left 0 right := by
  unfold WCT9.merkleNodeInput nodeInputP block4
  rw [WCT9.merkleTweak_top, show bytesLE 16 (0 : Digest) = zero16 by decide]
/-- The honest input of a tree node (C2 lower trees, C4 top tree: the packed fold input `merkleInputW`; top-nonce
layer: the honest pads are the keygen nonce digests, 0 on lower trees). -/
theorem merkle_honestInputW' (answers : Answers) (lay : Layer) (tree leaf step : Nat) :
    honestInput answers (.node lay tree step (leaf / 2 ^ (step + 1))) =
      pad64 (merkleInputW lay.val tree (height lay) leaf
        (fun j => treeValue (wotsTree answers lay tree) j (leaf / 2 ^ j ^^^ 1)) (fun _ => 0)
        (honestPads answers lay tree leaf) step
        (treeValue (wotsTree answers lay tree) step (leaf / 2 ^ step))) := by
  unfold merkleInputW honestInput honestPads
  dsimp only
  rw [Correctness.sibling_pair (fun n => treeValue (wotsTree answers lay tree) step n) (leaf / 2 ^ step),
    Correctness.div_pow_succ, WCT9.merkleNodeInputN_eq_lowerNodeInputP]
theorem merkle_honestInputW (answers : Answers) (lay : Layer) (hlay : lay.val ≠ 0) (tree leaf step : Nat) :
    honestInput answers (.node lay tree step (leaf / 2 ^ (step + 1))) =
      pad64 (merkleInputW lay.val tree (height lay) leaf
        (fun j => treeValue (wotsTree answers lay tree) j (leaf / 2 ^ j ^^^ 1)) (fun _ => 0) (fun _ => 0) step
        (treeValue (wotsTree answers lay tree) step (leaf / 2 ^ step))) := by
  rw [merkle_honestInputW', honestPads_lower answers (fun h => hlay (by rw [h]; rfl))]
theorem hdrBlock_merkleInputW (lay tree h leaf : Nat) (path : Nat → Digest) (hpads : Nat → BitVec 64)
    (pads : Nat → Digest) (step : Nat) (value : Digest) :
    hdrBlock (pad64 (merkleInputW lay tree h leaf path hpads pads step value)) =
      bytesLE 16 (hpads step ++ WCT9.merkleWord lay tree (2 ^ (h - step - 1) + leaf / 2 ^ (step + 1))) := by
  unfold merkleInputW
  dsimp only
  split <;> rw [pad64_lowerNodeInputP, WCT9.lowerNodeInputP, List.append_assoc] <;> exact hdrBlock_prefix _ _ _
theorem merkleInputW_length (lay tree h leaf : Nat) (path : Nat → Digest) (hpads : Nat → BitVec 64)
    (pads : Nat → Digest) (step : Nat) (value : Digest) :
    (pad64 (merkleInputW lay tree h leaf path hpads pads step value)).length = 64 := by
  unfold merkleInputW
  dsimp only
  split <;> rw [pad64_lowerNodeInputP, lowerNodeInputP_length]
/-- C4: a top fold input carries the top label (`TopLow`: its low header word is `topNodeWord heap`). -/
theorem topLow_merkleInputW (tree h leaf : Nat) (path : Nat → Digest) (hpads : Nat → BitVec 64)
    (pads : Nat → Digest) (step : Nat) (value : Digest) :
    TopLow (hdrBlock (pad64 (merkleInputW 0 tree h leaf path hpads pads step value))) := by
  rw [hdrBlock_merkleInputW, topLow_bytesLE_iff, tweakLow_eq_low, BitVec.extractLsb'_append_eq_right,
    WCT9.merkleWord_top, topNodeWord_toNat64]
  exact ⟨topNodeWord_pos _, lt_trans (topNodeWord_lt _) (by norm_num)⟩
/-- C4: two top fold inputs of the same step have the same decoding key (the key of a top label keeps only the low
word, which is the label `topNodeWord heap`). -/
theorem merkleInputW_sameHeader_top {tree h leaf step : Nat}
    (path path' : Nat → Digest) (hpads hpads' : Nat → BitVec 64) (pads pads' : Nat → Digest) (value value' : Digest) :
    SameHeader (pad64 (merkleInputW 0 tree h leaf path hpads pads step value))
      (pad64 (merkleInputW 0 tree h leaf path' hpads' pads' step value')) := by
  refine ⟨by rw [merkleInputW_length, merkleInputW_length], ?_⟩
  rw [hdrKey_of_top (merkleInputW_length ..) (topLow_merkleInputW ..),
    hdrKey_of_top (merkleInputW_length ..) (topLow_merkleInputW ..), hdrBlock_merkleInputW, hdrBlock_merkleInputW,
    SigGolfCandidate.T3M.Extract.bytesLE_header_words, SigGolfCandidate.T3M.Extract.bytesLE_header_words,
    List.take_left' (bytesLE_length 8 _), List.take_left' (bytesLE_length 8 _)]
/-- Two fold inputs of the same step have the same decoding key: on the lower trees the high tweak word is ignored
because the packed node word is marked (heap `< 128`), on the top tree (C4) because the label is `TopLow`. -/
theorem merkleInputW_sameHeader {lay tree h leaf step : Nat} (hh : 2 ^ (h - step - 1) + leaf / 2 ^ (step + 1) < 128)
    (path path' : Nat → Digest) (hpads hpads' : Nat → BitVec 64) (pads pads' : Nat → Digest) (value value' : Digest) :
    SameHeader (pad64 (merkleInputW lay tree h leaf path hpads pads step value))
      (pad64 (merkleInputW lay tree h leaf path' hpads' pads' step value')) := by
  by_cases h0 : lay = 0
  · subst h0; exact merkleInputW_sameHeader_top _ _ _ _ _ _ _ _
  refine ⟨by rw [merkleInputW_length, merkleInputW_length], ?_⟩
  have hm : ∀ heap, heap < 128 → 128 ≤ (WCT9.merkleWord lay tree heap).toNat % 256 := by
    intro heap hh'; rw [WCT9.merkleWord_lower h0, WCT9.lowerNodeWord_toNat hh']; omega
  have hn : ∀ (hp : BitVec 64), ¬ TopLow (bytesLE 16 (hp ++ WCT9.merkleWord lay tree
      (2 ^ (h - step - 1) + leaf / 2 ^ (step + 1)))) := by
    intro hp ht
    generalize 2 ^ (h - step - 1) + leaf / 2 ^ (step + 1) = heap at hh ht
    rw [topLow_bytesLE_iff, tweakLow_eq_low, BitVec.extractLsb'_append_eq_right, WCT9.merkleWord_lower h0,
      WCT9.lowerNodeWord_toNat hh] at ht
    omega
  rw [hdrKey_of_len64 (merkleInputW_length ..) (by rw [hdrBlock_merkleInputW]; exact hn _),
    hdrKey_of_len64 (merkleInputW_length ..) (by rw [hdrBlock_merkleInputW]; exact hn _),
    hdrBlock_merkleInputW, hdrBlock_merkleInputW]
  apply canonicalHeader_high_irrelevant
  exact hm _ hh
theorem hdrBlock_merkleInput (tag lay tree h leaf : Nat) (path pads : Nat → Digest) (step : Nat) (value : Digest) :
    hdrBlock (pad64 (merkleInput tag lay tree h leaf path pads step value)) =
      bytesLE 16 (nodeTweak tag lay tree (2 ^ (h - step - 1) + leaf / 2 ^ (step + 1))) := by
  unfold merkleInput
  dsimp only
  split <;> rw [pad64_nodeInputP, nodeInputP, hdrBlock_block4]
theorem merkleInput_length (tag lay tree h leaf : Nat) (path pads : Nat → Digest) (step : Nat) (value : Digest) :
    (pad64 (merkleInput tag lay tree h leaf path pads step value)).length = 64 := by
  unfold merkleInput
  dsimp only
  split <;> simp only [nodeInputP, pad64_block4, block4_length]
theorem hdrBlock_chainInputP (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 : Digest)
    (headerPad : BitVec 64) (value : Digest) :
    hdrBlock (pad64 (chainInputP lay tree leaf i step pad0 pad1 headerPad value)) =
      bytesLE 16 (chainHeaderP lay tree leaf i step headerPad) := by
  rw [pad64_chainInputP, chainInputP_eq_block4, hdrBlock_block4]
private theorem canonicalHeader_replace_high (x : Digest) (pad : BitVec 64)
    (hb : 128 ≤ x.toNat % 256) :
    canonicalHeader (bytesLE 16 (pad ++ x.extractLsb' 0 64)) =
      canonicalHeader (bytesLE 16 x) := by
  have hl : 128 ≤ (x.extractLsb' 0 64).toNat % 256 := by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    omega
  have hx : x.extractLsb' 64 64 ++ x.extractLsb' 0 64 = x :=
    BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := x)
  exact (canonicalHeader_high_irrelevant _ _ _ hl).trans
    (congrArg (fun y => canonicalHeader (bytesLE 16 y)) hx)
theorem canonicalHeader_chainHeaderP (lay : Layer) (tree leaf i step : Nat)
    (headerPad : BitVec 64) :
    canonicalHeader (bytesLE 16 (chainHeaderP lay tree leaf i step headerPad)) =
      canonicalHeader (bytesLE 16 (chainHeader lay tree leaf i step)) := by
  exact canonicalHeader_replace_high _ headerPad (SigGolfCandidate.T3.chainHeader_firstByte lay tree leaf i step)
theorem layerChains_queried (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (leaf tree : Nat) (hleaf : (route index lay).1 = leaf) (htree : (route index lay).2 = tree)
    (i : Nat) (hi : i < chainCount lay) :
    ∀ q ∈ queried answers (chainPW lay tree leaf i (digits.getD i 0)
        (maxDigit lay i - digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalueFor w lay digits i)),
      q ∈ queried answers (layerChains w index lay digits) := by
  subst hleaf htree
  unfold layerChains
  exact queried_mapM_mem answers (fun i : Fin (chainCount lay) =>
    chainPW lay (route index lay).2 (route index lay).1 i.val (digits.getD i.val 0)
      (maxDigit lay i.val - digits.getD i.val 0) (wchainPads w lay i.val).1 (wchainPads w lay i.val).2
      (wchainHeaderPad w lay i.val) (wvalueFor w lay digits i.val))
        (List.finRange (chainCount lay)) ⟨i, hi⟩ (List.mem_finRange _)
theorem map_finRange_val {β : Type} (n : Nat) (g : Nat → β) :
    (List.finRange n).map (fun i => g i.val) = (List.range n).map g := by
  rw [show (fun i : Fin n => g i.val) = g ∘ Fin.val from rfl, ← List.map_map, map_val_finRange]
theorem route_tree_bound (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) : (route index lay).2 < 2 ^ 32 :=
  lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hidx (by norm_num))
theorem route_routed_bound (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 < 2 ^ 32 := by
  unfold route
  dsimp only
  generalize hb : ((![19, 12, 6, 0] : Layer → Nat) lay) = b
  have hd : index / 2 ^ (b + height lay) * 2 ^ height lay + index / 2 ^ b % 2 ^ height lay = index / 2 ^ b := by
    rw [pow_add, ← Nat.div_div_eq_div_mul]
    exact Nat.div_add_mod' _ _
  rw [hd]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hidx (by norm_num))
theorem height_le (lay : Layer) : height lay ≤ 12 := by fin_cases lay <;> decide
theorem chainCount_le (lay : Layer) : chainCount lay ≤ 58 := by fin_cases lay <;> decide
theorem width_le (lay : Layer) (i : Nat) : width lay i ≤ 3 := by unfold width; omega
/-- The chains and the leaf hash of a layer reach the honest WOTS root: either a hit, or the leaf pads are zero and
every chain starts from its honest value (with zero pads when it takes a step). -/
theorem layerLeaf_extract (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits)
    (hv0 : evalWithAnswerFn answers (layerLeafP w index lay digits) =
      wotsRoot answers lay (route index lay).2 (route index lay).1) :
    HitIn answers (queried answers (layerLeafP w index lay digits)) ∨
      ((∀ i, i < chainCount lay →
        wvalueFor w lay digits i = wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
          (digits.getD i 0 < maxDigit lay i →
            wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
        wleafHigh w lay = 0) := by
  classical
  by_cases hH : HitIn answers (queried answers (layerLeafP w index lay digits))
  · exact Or.inl hH
  right
  have hleafB := route_leaf_bound index lay
  have htreeB := route_tree_bound index lay hidx
  have hrouted := route_routed_bound index lay hidx
  have hqC : ∀ q ∈ queried answers (layerChains w index lay digits),
      q ∈ queried answers (layerLeafP w index lay digits) := by
    intro q hq
    rw [layerLeafP_eq, queried_bind]
    exact List.mem_append_left _ hq
  generalize hleaf : (route index lay).1 = leaf at hleafB hrouted hv0 hH hqC ⊢
  generalize htree : (route index lay).2 = tree at htreeB hrouted hv0 hH hqC ⊢
  have htree31 : tree < 2 ^ 31 := by
    rw [← htree]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hidx
  have hleaf12 : leaf < 4096 :=
    lt_of_lt_of_le hleafB (Nat.pow_le_pow_right (by decide) (height_le lay))
  rw [layerLeafP_eq, evalWithAnswerFn_bind, hleaf, htree] at hv0
  have hends : evalWithAnswerFn answers (layerChains w index lay digits) =
      (List.range (chainCount lay)).map (fun i => evalWithAnswerFn answers
        (chainPW lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
          (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalueFor w lay digits i))) := by
    rw [layerChains, Correctness.eval_mapM, hleaf, htree]
    exact map_finRange_val _ (fun i => evalWithAnswerFn answers
        (chainPW lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
          (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalueFor w lay digits i)))
  rcases leafHashW_extract answers lay tree leaf (wtopLeafPad w) (wleafHigh w lay)
      (evalWithAnswerFn answers (layerChains w index lay digits))
      ((List.range (chainCount lay)).map (wotsEnd answers lay tree leaf))
      (by rw [hends]; simp) (by simp) hv0 with ⟨hE, hhi⟩ | ⟨hhit, hsame, hq⟩
  swap
  · exfalso
    apply hH
    refine ⟨.leaf lay tree leaf, _, ⟨hleafB, hrouted⟩, ?_, hhit, hsame⟩
    rw [layerLeafP_eq, queried_bind, hleaf, htree]
    exact List.mem_append_right _ hq
  refine ⟨?_, hhi⟩
  rw [hends] at hE
  have hE' := (List.map_inj_left).mp hE
  intro i hi
  have hd := hvalid i hi
  have hci := hE' i (List.mem_range.mpr hi)
  have hw : maxDigit lay i ≤ 7 := by unfold maxDigit; split_ifs <;> omega
  have hc := chainCount_le lay
  have hreach : pathValueW answers (fun s => WCT9.chainHigh lay i (digits.getD i 0 + s))
      (chainPathInputW lay tree leaf i (digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
        (wchainHeaderPad w lay i)) (wvalueFor w lay digits i) (maxDigit lay i - digits.getD i 0) =
      honestChainValueW answers lay tree leaf i (wotsSeed answers lay tree leaf i)
        (digits.getD i 0 + (maxDigit lay i - digits.getD i 0)) := by
    unfold pathValueW
    rw [← chainPW_eq_hashPathW, hci, Nat.add_sub_cancel' hd]; rfl
  rcases chainPathW_extract answers lay tree leaf i _ _ _ _ _ _ _
      htree31 hleaf12 (by omega) (Or.inr (by omega)) hreach with
      ⟨hval, hpads⟩ | ⟨step, hstep, hq, hhit⟩
  · refine ⟨hval, fun hlt => ?_⟩
    obtain ⟨h0, h1, hh⟩ := hpads (by omega)
    exact ⟨Prod.ext h0 h1, hh⟩
  · exfalso
    apply hH
    have hs6 : digits.getD i 0 + step ≤ 6 := by omega
    refine ⟨.chain lay tree leaf i (digits.getD i 0 + step),
      pad64 (pathInputW answers (fun s => WCT9.chainHigh lay i (digits.getD i 0 + s))
        (chainPathInputW lay tree leaf i (digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i)) (wvalueFor w lay digits i) step),
      ⟨htree31, hleaf12, by omega, by omega⟩, ?_, ?_, ?_⟩
    · apply hqC
      apply layerChains_queried answers w index lay digits leaf tree hleaf htree i hi
      rw [chainPW_eq_hashPathW]; exact hq
    · rw [hashHitAt_iff]
      simp only [honestInput, Pos.high]
      exact hhit
    · refine SameHeader.of_canonical ?_ ?_ ?_
      · rw [honestInput_length, pathInputW, chainPathInputW, pad64_chainInputPW, chainInputPW_length]; simp [Pos.len]
      · rw [honestInput_length]; simp [Pos.len]
      simp only [honestInput]
      rw [pathInputW, chainPathInputW, pad64_chainInputPW, WCT9.chainInputW_padded]
      change canonicalHeader (((chainInputPW _ _ _ _ _ _ _ _ _).drop 16).take 16) =
        canonicalHeader (((WCT9.chainInputW _ _ _ _ _ _).drop 16).take 16)
      rw [chainInputPW_header, WCT9.chainInputW_header]
      exact canonicalHeader_chainHeaderP _ _ _ _ _ _
theorem foldlM_finRange_eq_hashPathW (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (count : Nat) (initial : Digest) :
    (List.finRange count).foldlM (fun value j => WCT9.halfHash (high j.val) (input j.val value)) initial =
      hashPathW high input count initial := by
  unfold hashPathW
  rw [← map_val_finRange count, List.foldlM_map]
/-- C4: `layerP` (every fold one-word, half by heap parity) as the leaf hash followed by a half-aware hash path of
`height lay` folds. -/
theorem layerP_eq_hashPathW (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerP w index lay digits = (layerLeafP w index lay digits >>= fun value =>
      hashPathW (merkleHighW lay.val (height lay) (route index lay).1)
        (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
          (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
        (height lay) value) := by
  unfold layerP layerLeafP
  rcases route index lay with ⟨leaf, tree⟩
  dsimp only
  rw [bind_assoc]
  congr 1
  funext ends
  congr 1
  funext value
  rw [← foldlM_finRange_eq_hashPathW (merkleHighW lay.val (height lay) leaf)
    (merkleInputW lay.val tree (height lay) leaf (wpath w lay leaf) (wmerkleHigh w lay leaf) (wmerklePad w lay leaf))
    (height lay) value]
  rfl
/-- C4: the top layer's leaf hash and 12 folds as a half-aware hash path (`layerP` is stated for every layer). -/
theorem layerP_extract (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hlay : lay = 0) (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) = honestRoot answers lay (route index lay).2) :
    HitIn answers (queried answers (layerP w index lay digits)) ∨ LayerShaped answers w index lay digits := by
  classical
  by_cases hH : HitIn answers (queried answers (layerP w index lay digits))
  · exact Or.inl hH
  right
  have hl0 : lay.val = 0 := by rw [hlay]; rfl
  have hqL : ∀ q ∈ queried answers (layerLeafP w index lay digits), q ∈ queried answers (layerP w index lay digits) := by
    intro q hq
    rw [layerP_eq_hashPathW, queried_bind]
    exact List.mem_append_left _ hq
  have hqM : ∀ q ∈ queried answers (hashPathW (merkleHighW lay.val (height lay) (route index lay).1)
      (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1 (wpath w lay (route index lay).1)
        (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)) (height lay)
      (evalWithAnswerFn answers (layerLeafP w index lay digits))),
      q ∈ queried answers (layerP w index lay digits) := by
    intro q hq
    rw [layerP_eq_hashPathW, queried_bind]
    exact List.mem_append_right _ hq
  have hleafB := route_leaf_bound index lay
  have htreeB := route_tree_bound index lay hidx
  have hM := merklePathW_extract answers lay.val (route index lay).2 (height lay) (route index lay).1
    (height lay) (wpath w lay (route index lay).1)
    (fun j => treeValue (wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1))
    (fun step => treeValue (wotsTree answers lay (route index lay).2) step ((route index lay).1 / 2 ^ step))
    (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)
    (honestPads answers lay (route index lay).2 (route index lay).1)
    (evalWithAnswerFn answers (layerLeafP w index lay digits))
    (fun step hstep => merkleInputW_wotsTree_reference answers lay (route index lay).2 (route index lay).1 hleafB
      step hstep)
    (by
      have h := reaches
      rw [layerP_eq_hashPathW, evalWithAnswerFn_bind] at h
      unfold pathValueW
      rw [Nat.div_eq_of_lt hleafB]
      exact h)
  rcases hM with ⟨hv0, hpath⟩ | ⟨step, hstep, hq, hhit⟩
  swap
  · exfalso
    apply hH
    refine ⟨.node lay (route index lay).2 step ((route index lay).1 / 2 ^ (step + 1)), pad64 (pathInputW answers
      (merkleHighW lay.val (height lay) (route index lay).1)
      (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1 (wpath w lay (route index lay).1)
        (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
      (evalWithAnswerFn answers (layerLeafP w index lay digits)) step), ⟨htreeB, hstep, Or.inl hlay,
        fun _ => by subst hlay; exact route_top_tree index hidx, ?_⟩, hqM _ hq, ?_, ?_⟩
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · rw [hashHitAt_iff, merkle_honestInputW' answers lay]; exact hhit
    · rw [merkle_honestInputW' answers lay, pathInputW, hl0]
      exact merkleInputW_sameHeader_top _ _ _ _ _ _ _ _
  rw [pow_zero, Nat.div_one, WCT9.wotsTree_leaf answers lay _ _ hleafB] at hv0
  rcases layerLeaf_extract answers w index lay digits hidx hvalid hv0 with hhit | ⟨hchains, hhi⟩
  · exact absurd (hhit.mono hqL) hH
  exact ⟨fun j hj => ⟨(hpath j hj).1, fun _ => (hpath j hj).2.2, fun _ => (hpath j hj).2.1⟩, hchains, hhi⟩

/-- The lower path of `layerPairP` as a half-aware hash path (C2). -/
theorem layerPairP_eq_hashPathW (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerPairP w index lay digits = (layerLeafP w index lay digits >>= fun value =>
      hashPathW (merkleHighW lay.val (height lay) (route index lay).1)
        (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
          (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
        (height lay - 1) value >>= fun top =>
      pure (if (route index lay).1 / 2 ^ (height lay - 1) % 2 = 0
        then (top, wpath w lay (route index lay).1 (height lay - 1))
        else (wpath w lay (route index lay).1 (height lay - 1), top))) := by
  unfold layerPairP layerLeafP
  rcases route index lay with ⟨leaf, tree⟩
  dsimp only
  rw [bind_assoc]
  congr 1
  funext ends
  congr 1
  funext value
  rw [← foldlM_finRange_eq_hashPathW (merkleHighW lay.val (height lay) leaf)
    (merkleInputW lay.val tree (height lay) leaf (wpath w lay leaf) (wmerkleHigh w lay leaf) (wmerklePad w lay leaf))
    (height lay - 1) value]
  rfl
theorem height_pos (lay : Layer) : 1 ≤ height lay := by fin_cases lay <;> decide
theorem height_le7 {lay : Layer} (h0 : lay.val ≠ 0) : height lay ≤ 7 := by
  fin_cases lay <;> simp_all [height]
theorem lower_heap_lt128 {lay : Layer} (h0 : lay.val ≠ 0) {leaf step : Nat} (hleaf : leaf < 2 ^ height lay) :
    2 ^ (height lay - step - 1) + leaf / 2 ^ (step + 1) < 128 := by
  have h7 := height_le7 h0
  have hp : 2 ^ (height lay - step - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
  have hl : leaf < 2 ^ 7 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by decide) h7)
  have hd : leaf / 2 ^ (step + 1) ≤ leaf / 2 := Nat.div_le_div_left (by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (step + 1) := Nat.pow_le_pow_right (by decide) (by omega)) (by decide)
  have h64 : (2 : Nat) ^ 6 = 64 := by norm_num
  have h128 : (2 : Nat) ^ 7 = 128 := by norm_num
  omega
theorem layerPairP_extract (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits) (hlay : lay.val ≠ 0)
    (reaches : evalWithAnswerFn answers (layerPairP w index lay digits) = honestPair answers lay (route index lay).2) :
    HitIn answers (queried answers (layerPairP w index lay digits)) ∨ LayerShaped answers w index lay digits := by
  classical
  by_cases hH : HitIn answers (queried answers (layerPairP w index lay digits))
  · exact Or.inl hH
  right
  have hh := height_pos lay
  have hqL : ∀ q ∈ queried answers (layerLeafP w index lay digits),
      q ∈ queried answers (layerPairP w index lay digits) := by
    intro q hq
    rw [layerPairP_eq_hashPathW, queried_bind]
    exact List.mem_append_left _ hq
  have hqM : ∀ q ∈ queried answers (hashPathW (merkleHighW lay.val (height lay) (route index lay).1)
      (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1 (wpath w lay (route index lay).1)
        (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)) (height lay - 1)
      (evalWithAnswerFn answers (layerLeafP w index lay digits))),
      q ∈ queried answers (layerPairP w index lay digits) := by
    intro q hq
    rw [layerPairP_eq_hashPathW, queried_bind, queried_bind]
    exact List.mem_append_right _ (List.mem_append_left _ hq)
  have hleafB := route_leaf_bound index lay
  have htreeB := route_tree_bound index lay hidx
  have hq2 : (route index lay).1 / 2 ^ (height lay - 1) = 0 ∨ (route index lay).1 / 2 ^ (height lay - 1) = 1 := by
    have hq : (route index lay).1 / 2 ^ (height lay - 1) < 2 := by
      apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
      have he : 2 ^ (height lay - 1) * 2 = 2 ^ height lay := by rw [← pow_succ, Nat.sub_add_cancel hh]
      rw [Nat.mul_comm, he]
      exact hleafB
    generalize (route index lay).1 / 2 ^ (height lay - 1) = q at hq ⊢
    omega
  rw [layerPairP_eq_hashPathW, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at reaches
  generalize htop : evalWithAnswerFn answers (hashPathW (merkleHighW lay.val (height lay) (route index lay).1)
      (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1 (wpath w lay (route index lay).1)
        (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)) (height lay - 1)
      (evalWithAnswerFn answers (layerLeafP w index lay digits))) = top at reaches
  have hpair : top = treeValue (wotsTree answers lay (route index lay).2) (height lay - 1)
        ((route index lay).1 / 2 ^ (height lay - 1)) ∧
      wpath w lay (route index lay).1 (height lay - 1) =
        treeValue (wotsTree answers lay (route index lay).2) (height lay - 1)
          ((route index lay).1 / 2 ^ (height lay - 1) ^^^ 1) := by
    unfold honestPair at reaches
    rcases hq2 with h | h <;> simp only [h] at reaches ⊢ <;>
      simp only [Nat.one_mod, if_true, if_false, Prod.mk.injEq, one_ne_zero] at reaches <;>
      exact ⟨by first | exact reaches.1 | exact reaches.2, by first | exact reaches.2 | exact reaches.1⟩
  have hM := merklePathW_extract answers lay.val (route index lay).2 (height lay) (route index lay).1
    (height lay - 1) (wpath w lay (route index lay).1)
    (fun j => treeValue (wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1))
    (fun step => treeValue (wotsTree answers lay (route index lay).2) step ((route index lay).1 / 2 ^ step))
    (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)
    (honestPads answers lay (route index lay).2 (route index lay).1)
    (evalWithAnswerFn answers (layerLeafP w index lay digits))
    (fun step hstep => merkleInputW_wotsTree_reference answers lay (route index lay).2 (route index lay).1 hleafB
      step (by omega))
    (by unfold pathValueW; rw [htop]; exact hpair.1)
  rcases hM with ⟨hv0, hpath⟩ | ⟨step, hstep, hq, hhit⟩
  swap
  · exfalso
    apply hH
    refine ⟨.node lay (route index lay).2 step ((route index lay).1 / 2 ^ (step + 1)), pad64 (pathInputW answers
      (merkleHighW lay.val (height lay) (route index lay).1)
      (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1 (wpath w lay (route index lay).1)
        (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
      (evalWithAnswerFn answers (layerLeafP w index lay digits)) step), ⟨htreeB, by omega, Or.inr (by omega),
        fun hl => by subst hl; exact route_top_tree index hidx, ?_⟩, hqM _ hq, ?_, ?_⟩
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · rw [hashHitAt_iff, merkle_honestInputW' answers lay]; exact hhit
    · rw [merkle_honestInputW' answers lay, pathInputW]
      exact merkleInputW_sameHeader (lower_heap_lt128 hlay hleafB) _ _ _ _ _ _ _ _
  rw [pow_zero, Nat.div_one, WCT9.wotsTree_leaf answers lay _ _ hleafB] at hv0
  rcases layerLeaf_extract answers w index lay digits hidx hvalid hv0 with hhit | ⟨hchains, hhi⟩
  · exact absurd (hhit.mono hqL) hH
  refine ⟨fun j hj => ?_, hchains, hhi⟩
  by_cases hjt : j < height lay - 1
  · exact ⟨(hpath j hjt).1, fun _ => (hpath j hjt).2.2, fun _ => (hpath j hjt).2.1⟩
  · have hj1 : j = height lay - 1 := by omega
    subst hj1
    exact ⟨hpair.2, fun h => by omega, fun h => by omega⟩

end ClaudeWCT.W9.T3M.Extract
namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open ClaudeWCT.WCT9 (wotsTree wotsSeed wotsEnd wotsValue wotsRoot)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-- Zero chain pads: the verifier chain is the honest chain of the current scheme. -/
theorem chainPW_zero_route (index : Nat) (lay : Layer) (i : Fin (chainCount lay))
    (digit : Nat) (value : Digest) (hindex : index < 2 ^ 31) :
    chainPW lay (route index lay).2 (route index lay).1 i.val digit (maxDigit lay i.val - digit) 0 0 0 value =
      WCT9.chainW lay (route index lay).2 (route index lay).1 i.val digit (maxDigit lay i.val - digit) value := by
  have hi := i.isLt
  have ht : (route index lay).2 < 2 ^ 31 := by fin_cases lay <;> simp [route, height] <;> omega
  have hl : (route index lay).1 < 4096 := by fin_cases lay <;> simp [route, height] <;> omega
  have hi64 : i.val < 64 := by have := chainCount_le lay; omega
  have hm : maxDigit lay i.val ≤ 7 := by unfold maxDigit; split_ifs <;> decide
  unfold chainPW WCT9.chainW
  apply WCT9.foldlM_congr_of_mem
  intro s hs v
  rw [List.mem_range'_1] at hs
  rw [chainInputW_eq_zero _ _ _ _ _ _ ht hl hi64 (by omega)]
/-- Zero leaf pads: the verifier leaf hash is the honest one. -/
theorem leafHashW_shaped {lay : Layer} {tree leaf : Nat} {pad : Digest} {hi : BitVec 64} (hh : hi = 0)
    (ends : List Digest) :
    WCT9.leafHashW lay tree leaf pad hi ends = WCT9.lowerLeafHash lay tree leaf ends := by
  -- T51 ("endpad"): `leafInputW` never reads `pad`
  subst hh
  rfl

theorem layerP_shaped_core (answers : Answers) (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat)
    (hlay : lay.val = 0) (hs : LayerShaped answers w (WCT9.digestIndex N) lay digits)
    -- Top-nonce layer (r3-lean-nonsec): the legacy `recoverLayer` hashes zero node pads; the img-v6 witness interface
    -- (HonestN) supplies this, or replaces this lemma by its nonce-reading top verifier.
    (hpad : ∀ j, j < height lay → wmerklePad w lay (route (WCT9.digestIndex N) lay).1 j = 0) :
    layerP w (WCT9.digestIndex N) lay digits =
      recoverLayer (WCT9.toT3Signature (effectiveSignature (witDecP N w).signature (padDecP N w) digits)) (WCT9.digestIndex N) lay digits := by
  have hl0 : lay = 0 := Fin.ext hlay
  subst hl0
  have hpath : ∀ j : Fin (height 0), ((WCT9.toT3Signature (effectiveSignature (witDecP N w).signature (padDecP N w) digits)).layers 0).path j =
      wpath w 0 (route (WCT9.digestIndex N) 0).1 j.val := fun _ => rfl
  have hvals : ∀ i : Fin (chainCount 0),
      ((WCT9.toT3Signature (effectiveSignature (witDecP N w).signature (padDecP N w) digits)).layers 0).values i = wvalueFor w 0 digits i.val :=
    fun i => valueP_dec N w 0 digits i
  have hindex : WCT9.digestIndex N < 2 ^ 31 := WCT9.digestIndex_lt N
  -- Witness stack: zero pads give the top chain of the current scheme (`chainW 0 0 = topChain = layChain 0`).
  have hzero : ∀ (i : Fin (chainCount 0)) (digit : Nat) (value : Digest),
      chainPW 0 (route (WCT9.digestIndex N) 0).2 (route (WCT9.digestIndex N) 0).1 i.val digit
        (maxDigit 0 i.val - digit) 0 0 0 value =
      layChain 0 (route (WCT9.digestIndex N) 0).2 (route (WCT9.digestIndex N) 0).1 i.val digit
        (maxDigit 0 i.val - digit) value := by
    intro i digit value
    rw [chainPW_zero_route _ 0 i digit value hindex, route_top_tree _ hindex, WCT9.chainW_top_eq, layChain_top]
  have hleaf := leafHashW_shaped (lay := 0) (tree := (route (WCT9.digestIndex N) 0).2)
    (leaf := (route (WCT9.digestIndex N) 0).1) (pad := wtopLeafPad w) hs.2.2
  unfold layerP recoverLayer
  simp only [hpath, hvals, hleaf, WCT9.lowerLeafHash_top]
  have hmz : ∀ j : Fin (height 0), wmerklePad w 0 (route (WCT9.digestIndex N) 0).1 j.val = 0 :=
    fun j => hpad j.val j.isLt
  have hmh : ∀ j : Fin (height 0), wmerkleHigh w 0 (route (WCT9.digestIndex N) 0).1 j.val = 0 :=
    fun j => (hs.1 j.val j.isLt).2.2 (Or.inr hlay)
  generalize hr : route (WCT9.digestIndex N) 0 = r at hs hzero hmz hmh ⊢
  obtain ⟨leaf, tree⟩ := r
  dsimp only at hs hzero hmz hmh ⊢
  have hchains : ((List.finRange (chainCount 0)).mapM fun i =>
      chainPW 0 tree leaf i.val (digits.getD i.val 0) (maxDigit 0 i.val - digits.getD i.val 0)
        (wchainPads w 0 i.val).1 (wchainPads w 0 i.val).2
        (wchainHeaderPad w 0 i.val) (wvalueFor w 0 digits i.val)) =
      ((List.finRange (chainCount 0)).mapM fun i =>
      layChain 0 tree leaf i.val (digits.getD i.val 0) (maxDigit 0 i.val - digits.getD i.val 0)
        (wvalueFor w 0 digits i.val)) := by
    congr 1
    funext i
    by_cases hd : digits.getD i.val 0 < maxDigit 0 i.val
    · rw [((hs.2.1 i.val i.isLt).2 hd).1, ((hs.2.1 i.val i.isLt).2 hd).2]
      exact hzero i _ _
    · have h0 : maxDigit 0 i.val - digits.getD i.val 0 = 0 := by omega
      rw [h0]
      rfl
  rw [hchains]
  congr 1
  funext ends
  congr 1
  funext value
  congr 1
  funext v j
  rw [hmz j, hmh j, ← WCT9.lowerNodeHash_eqP', Fin.val_zero, WCT9.lowerNodeHash_top]

theorem layerPairP_shaped_core (answers : Answers) (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat)
    (hs : LayerShaped answers w (WCT9.digestIndex N) lay digits) (hlay : lay.val ≠ 0) :
    layerPairP w (WCT9.digestIndex N) lay digits =
      WCT9.recoverLayerPair (effectiveSignature (witDecP N w).signature (padDecP N w) digits) (WCT9.digestIndex N) lay digits := by
  have hindex : WCT9.digestIndex N < 2 ^ 31 := WCT9.digestIndex_lt N
  have hzero := chainPW_zero_route (WCT9.digestIndex N) lay
  have hpath : ∀ j : Fin (height lay), ((effectiveSignature (witDecP N w).signature (padDecP N w) digits).layers lay).path j =
      wpath w lay (route (WCT9.digestIndex N) lay).1 j.val := fun _ => rfl
  have hvals : ∀ i : Fin (chainCount lay), ((effectiveSignature (witDecP N w).signature (padDecP N w) digits).layers lay).values i = wvalueFor w lay digits i.val :=
    fun i => valueP_dec N w lay digits i
  have hleaf := leafHashW_shaped (lay := lay) (tree := (route (WCT9.digestIndex N) lay).2)
    (leaf := (route (WCT9.digestIndex N) lay).1) (pad := wtopLeafPad w) hs.2.2
  unfold layerPairP WCT9.recoverLayerPair
  simp only [hpath, hvals, Fin.val_castLE, WCT9.topLevel, hleaf]
  have hmz : ∀ j : Fin (height lay - 1), wmerklePad w lay (route (WCT9.digestIndex N) lay).1 j.val = 0 := by
    intro j
    have h := (hs.1 j.val (by omega)).2.1 (Or.inl (by omega))
    rwa [WCT9.honestNonce_lower answers (fun h0 => hlay (by rw [h0]; rfl)), WCT9.nonceDigest_zero] at h
  have hmh : ∀ j : Fin (height lay - 1), wmerkleHigh w lay (route (WCT9.digestIndex N) lay).1 j.val = 0 :=
    fun j => (hs.1 j.val (by omega)).2.2 (Or.inl (by omega))
  generalize hr : route (WCT9.digestIndex N) lay = r at hs hzero hmz hmh ⊢
  obtain ⟨leaf, tree⟩ := r
  dsimp only at hs hzero hmz hmh ⊢
  have hchains : ((List.finRange (chainCount lay)).mapM fun i =>
      chainPW lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
        (wchainPads w lay i.val).1 (wchainPads w lay i.val).2
        (wchainHeaderPad w lay i.val) (wvalueFor w lay digits i.val)) =
      ((List.finRange (chainCount lay)).mapM fun i =>
      WCT9.chainW lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
        (wvalueFor w lay digits i.val)) := by
    refine congrArg (fun f => (List.finRange (chainCount lay)).mapM f) (funext fun i => ?_)
    by_cases hd : digits.getD i.val 0 < maxDigit lay i.val
    · rw [((hs.2.1 i.val i.isLt).2 hd).1, ((hs.2.1 i.val i.isLt).2 hd).2]
      exact hzero i _ _ hindex
    · have h0 : maxDigit lay i.val - digits.getD i.val 0 = 0 := by omega
      rw [h0]
      simp only [chainPW, WCT9.chainW, List.range'_zero, List.foldlM_nil]
  rw [hchains]
  congr 1
  funext ends
  congr 1
  funext value
  simp only [hmz, hmh, ← WCT9.lowerNodeHash_eqP hlay]

end ClaudeWCT.W9.T3M.Extract
