import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.HdrBlocks
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Queries

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open ClaudeWCT.WCT9 (wotsTree wotsSeed wotsEnd wotsValue wotsRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem flatMap_bytes_injective : ∀ {xs ys : List Digest}, xs.length = ys.length →
    xs.flatMap (bytesLE 16) = ys.flatMap (bytesLE 16) → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, h => by
      simp only [List.flatMap_cons] at h
      obtain ⟨hxy, hrest⟩ := List.append_inj h (by simp only [bytesLE_length])
      rw [bytesLE_injective hxy, flatMap_bytes_injective (by simpa using hlen) hrest]
theorem listInput_length (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    (listInput first hdr rest).length = 32 + 16 * rest.length := by
  simp only [listInput, List.length_append, bytesLE_length, digest_list_bytes_length]
theorem listInput_injective {first first' : Digest} {hdr hdr' : BitVec 128} {rest rest' : List Digest}
    (hlen : rest.length = rest'.length) (h : listInput first hdr rest = listInput first' hdr' rest') :
    first = first' ∧ hdr = hdr' ∧ rest = rest' := by
  unfold listInput at h
  obtain ⟨h, hr⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hf, hh⟩ := List.append_inj h (by simp only [bytesLE_length])
  exact ⟨bytesLE_injective hf, bytesLE_injective hh, flatMap_bytes_injective hlen hr⟩
theorem list_head_drop : ∀ (xs : List Digest), 0 < xs.length → xs.getD 0 0 :: xs.drop 1 = xs
  | _ :: _, _ => rfl
theorem listInput_lists {xs ys : List Digest} {hdr hdr' : BitVec 128} (hlen : xs.length = ys.length)
    (hpos : 0 < ys.length)
    (h : pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)) = pad64 (listInput (ys.getD 0 0) hdr' (ys.drop 1))) :
    xs = ys ∧ hdr = hdr' := by
  have hl : (listInput (xs.getD 0 0) hdr (xs.drop 1)).length = (listInput (ys.getD 0 0) hdr' (ys.drop 1)).length := by
    rw [listInput_length, listInput_length, List.length_drop, List.length_drop, hlen]
  obtain ⟨hf, hh, hr⟩ := listInput_injective (by rw [List.length_drop, List.length_drop, hlen])
    (Sampling.pad64_inj_of_length hl h)
  refine ⟨?_, hh⟩
  rw [← list_head_drop xs (by omega), ← list_head_drop ys hpos, hf, hr]
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
private theorem hdrBlock_forestInput_leaf (index : Nat) (pairs : List (Digest × Digest)) :
    hdrBlock (pad64 (forestInput index pairs)) = bytesLE 16 (header 15 0 index 0 0) := by
  rw [hdrBlock_pad64 _ (by simp only [forestInput, WCT9.forestInput, zero16, List.length_append,
    List.length_replicate, bytesLE_length]; omega)]
  unfold forestInput WCT9.forestInput
  rw [show zero16 = bytesLE 16 (0 : Digest) by decide]
  exact hdrBlock_prefix 0 _ _
theorem leafHash_eq_projHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafHash lay tree leaf ends = projHash (leafHigh leaf) (leafInput lay tree leaf ends) := rfl
theorem forestPk_eq_shortHash (index : Nat) (pairs : List (Digest × Digest)) :
    WCT9.forestPk index pairs = shortHash (forestInput index pairs) := rfl
theorem forestInput_pairs_injective {index : Nat} {ps qs : List (Digest × Digest)} (hl : ps.length = qs.length)
    (h : pad64 (forestInput index ps) = pad64 (forestInput index qs)) : ps = qs := by
  have hlen : (forestInput index ps).length = (forestInput index qs).length := by
    simp only [forestInput, WCT9.forestInput, zero16, List.length_append, List.length_replicate, bytesLE_length,
      WCT9.pairs_bytes_length, hl]
  have h := Sampling.pad64_inj_of_length hlen h
  unfold forestInput WCT9.forestInput at h
  obtain ⟨-, hp⟩ := List.append_inj h (by simp only [zero16, List.length_append, List.length_replicate,
    bytesLE_length])
  exact WCT9.pairs_bytes_injective hl hp
/-- Campaign S1: the padded lower leaf input as a list input (header `hp ++ t3`). -/
theorem lowerLeafInputP_eq_listInput (lay : Layer) (tree leaf : Nat) (hp : BitVec 64) (ends : List Digest) :
    lowerLeafInputP lay tree leaf hp ends =
      listInput (ends.getD 0 0) (hp ++ hyperWord lay.val (tree * 2 ^ height lay + leaf)) (ends.drop 1) := by
  simp only [lowerLeafInputP, listInput]
theorem leafInput_lower_eq_listInput {lay : Layer} (hl : lay ≠ 0) (tree leaf : Nat) (ends : List Digest) :
    leafInput lay tree leaf ends =
      listInput (ends.getD 0 0) (0#64 ++ hyperWord lay.val (tree * 2 ^ height lay + leaf)) (ends.drop 1) := by
  simp only [leafInput, SigGolfCandidate.T3.leafInput, hl, if_false, listInput, leafTweak]
/-- Keys of list inputs with the same low header word and length agree when the low word is a padded label. -/
theorem sameHeader_listInput {first first' : Digest} {hi hi' lo : BitVec 64} {rest rest' : List Digest}
    (hlen : rest.length = rest'.length) (hp : padLabel (32 + 16 * rest.length + (64 - (32 + 16 * rest.length) % 64) % 64)
      lo.toNat) :
    SameHeader (pad64 (listInput first (hi ++ lo) rest)) (pad64 (listInput first' (hi' ++ lo) rest')) := by
  unfold SameHeader keyOf
  have hl1 : (pad64 (listInput first (hi ++ lo) rest)).length =
      32 + 16 * rest.length + (64 - (32 + 16 * rest.length) % 64) % 64 := by
    rw [Cost.pad64_length, listInput_length]
  have hl2 : (pad64 (listInput first' (hi' ++ lo) rest')).length =
      32 + 16 * rest.length + (64 - (32 + 16 * rest.length) % 64) % 64 := by
    rw [Cost.pad64_length, listInput_length, hlen]
  rw [hl1, hl2, hdrBlock_listInput, hdrBlock_listInput,
    SigGolfCandidate.T3M.Extract.canonicalHeaderL_high_irrelevant _ hi hi' lo hp]
theorem lowerLeaf_padLabel (lay : Layer) (tree leaf len : Nat) :
    padLabel len (hyperWord lay.val (tree * 2 ^ height lay + leaf)).toNat := by
  unfold padLabel
  right; right
  rw [hyperWord_toNat]
  have := Nat.mod_lt (tree * 2 ^ height lay + leaf) (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt lay.val (show 0 < 256 by decide)
  omega
/-- Campaign S1 padded lower leaf: either the endpoints and the witness header word are honest, or the query hits
the honest leaf (on the leaf's half). -/
theorem lowerLeafHashP_extract (answers : Answers) {lay : Layer} (hl : lay ≠ 0) (tree leaf : Nat) (hp : BitVec 64)
    (ends honest : List Digest) (hlen : ends.length = honest.length) (hpos : 0 < honest.length)
    (reaches : evalWithAnswerFn answers (lowerLeafHashP lay tree leaf hp ends) =
      evalWithAnswerFn answers (leafHash lay tree leaf honest)) :
    (ends = honest ∧ hp = 0) ∨
      (HashHitP (leafHigh leaf) answers (pad64 (leafInput lay tree leaf honest))
          (pad64 (lowerLeafInputP lay tree leaf hp ends)) ∧
        SameHeader (pad64 (lowerLeafInputP lay tree leaf hp ends)) (pad64 (leafInput lay tree leaf honest)) ∧
        .inl (.inr (pad64 (lowerLeafInputP lay tree leaf hp ends))) ∈
          queried answers (lowerLeafHashP lay tree leaf hp ends)) := by
  rw [lowerLeafInputP_eq_listInput]
  rw [leafInput_lower_eq_listInput hl]
  by_cases heq : pad64 (listInput (ends.getD 0 0) (hp ++ hyperWord lay.val (tree * 2 ^ height lay + leaf))
      (ends.drop 1)) = pad64 (listInput (honest.getD 0 0) (0#64 ++ hyperWord lay.val (tree * 2 ^ height lay + leaf))
      (honest.drop 1))
  · obtain ⟨hE, hH⟩ := listInput_lists hlen hpos heq
    exact Or.inl ⟨hE, (append64_inj hH).1⟩
  · refine Or.inr ⟨⟨heq, ?_⟩, ?_, ?_⟩
    · unfold lowerLeafHashP at reaches
      rw [leafHash_eq_projHash, eval_projHash, eval_projHash, lowerLeafInputP_eq_listInput,
        leafInput_lower_eq_listInput hl] at reaches
      exact reaches
    · exact sameHeader_listInput (by rw [List.length_drop, List.length_drop, hlen]) (lowerLeaf_padLabel _ _ _ _)
    · unfold lowerLeafHashP
      rw [queried_projHash, lowerLeafInputP_eq_listInput]
      exact List.mem_singleton_self _
theorem leafInput_lists {lay : Layer} {tree leaf : Nat} {xs ys : List Digest} (hlen : xs.length = ys.length)
    (hpos : 0 < ys.length)
    (h : pad64 (leafInput lay tree leaf xs) = pad64 (leafInput lay tree leaf ys)) : xs = ys := by
  unfold leafInput SigGolfCandidate.T3.leafInput at h
  split at h
  · have hl : (zero16 ++ bytesLE 16 (leafTweak lay tree leaf) ++ xs.flatMap (bytesLE 16)).length =
        (zero16 ++ bytesLE 16 (leafTweak lay tree leaf) ++ ys.flatMap (bytesLE 16)).length := by
      simp only [List.length_append, digest_list_bytes_length, hlen]
    have h' := Sampling.pad64_inj_of_length hl h
    obtain ⟨-, hr⟩ := List.append_inj h' (by simp only [List.length_append, bytesLE_length])
    exact flatMap_bytes_injective hlen hr
  · exact (listInput_lists (hdr := leafTweak lay tree leaf) (hdr' := leafTweak lay tree leaf) hlen hpos h).1
/-- Top leaf (no pad): the endpoints are honest or the query hits the honest top leaf. -/
theorem leafHash_extract (answers : Answers) (lay : Layer) (tree leaf : Nat) (ends honest : List Digest)
    (hlen : ends.length = honest.length) (hpos : 0 < honest.length)
    (reaches : evalWithAnswerFn answers (leafHash lay tree leaf ends) =
      evalWithAnswerFn answers (leafHash lay tree leaf honest)) :
    ends = honest ∨
      (HashHitP (leafHigh leaf) answers (pad64 (leafInput lay tree leaf honest)) (pad64 (leafInput lay tree leaf ends)) ∧
        SameHeader (pad64 (leafInput lay tree leaf ends)) (pad64 (leafInput lay tree leaf honest)) ∧
        .inl (.inr (pad64 (leafInput lay tree leaf ends))) ∈ queried answers (leafHash lay tree leaf ends)) := by
  by_cases heq : pad64 (leafInput lay tree leaf ends) = pad64 (leafInput lay tree leaf honest)
  · exact Or.inl (leafInput_lists hlen hpos heq)
  · refine Or.inr ⟨⟨heq, ?_⟩, ?_, ?_⟩
    · rw [leafHash_eq_projHash, leafHash_eq_projHash, eval_projHash, eval_projHash] at reaches
      exact reaches
    · unfold SameHeader keyOf
      have hl : (pad64 (leafInput lay tree leaf ends)).length = (pad64 (leafInput lay tree leaf honest)).length := by
        rw [Cost.pad64_length, Cost.pad64_length]
        simp only [leafInput, SigGolfCandidate.T3.leafInput_length, hlen]
      rw [hl, hdrBlock_leafInput, hdrBlock_leafInput]
    · rw [leafHash_eq_projHash, queried_projHash]
      exact List.mem_singleton_self _
theorem forestPk_extract (answers : Answers) (index : Nat) (pairs honest : List (Digest × Digest))
    (hlen : pairs.length = honest.length)
    (reaches : evalWithAnswerFn answers (WCT9.forestPk index pairs) =
      evalWithAnswerFn answers (WCT9.forestPk index honest)) :
    pairs = honest ∨
      (HashHit answers (pad64 (forestInput index honest)) (pad64 (forestInput index pairs)) ∧
        SameHeader (pad64 (forestInput index pairs)) (pad64 (forestInput index honest)) ∧
        .inl (.inr (pad64 (forestInput index pairs))) ∈ queried answers (WCT9.forestPk index pairs)) := by
  by_cases heq : pad64 (forestInput index pairs) = pad64 (forestInput index honest)
  · exact Or.inl (forestInput_pairs_injective hlen heq)
  · refine Or.inr ⟨⟨heq, ?_⟩, ?_, ?_⟩
    · rw [forestPk_eq_shortHash, forestPk_eq_shortHash, eval_shortHash, eval_shortHash] at reaches
      exact reaches
    · unfold SameHeader keyOf
      have hl : (pad64 (forestInput index pairs)).length = (pad64 (forestInput index honest)).length := by
        simp only [Cost.pad64_length, forestInput, WCT9.forestInput, zero16, List.length_append,
          List.length_replicate, bytesLE_length, WCT9.pairs_bytes_length, hlen]
      rw [hl, hdrBlock_forestInput_leaf, hdrBlock_forestInput_leaf]
    · rw [forestPk_eq_shortHash, queried_shortHash]
      exact List.mem_singleton_self _
theorem forestPk_honest_extract (answers : Answers) (index : Nat) (hidx : index < 2 ^ 40)
    (pairs : List (Digest × Digest)) (hlen : pairs.length = 9)
    (reaches : evalWithAnswerFn answers (WCT9.forestPk index pairs) = honestForest answers index) :
    pairs = ftsPairsHonest answers index ∨ HitIn answers (queried answers (WCT9.forestPk index pairs)) := by
  rcases forestPk_extract answers index pairs (ftsPairsHonest answers index)
      (by rw [hlen, ftsPairsHonest_length]) reaches with h | ⟨hh, hs, hq⟩
  · exact Or.inl h
  · exact Or.inr ⟨.forest index, _, hidx, hq, hh, hs⟩
theorem queried_mapM_mem {α β : Type} (answers : Answers) (f : α → M β) :
    ∀ (l : List α), ∀ a ∈ l, ∀ q ∈ queried answers (f a), q ∈ queried answers (l.mapM f)
  | [], _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: xs, a, ha, q, hq => by
      rw [List.mapM_cons, queried_bind, queried_bind]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_append_left _ hq
      · exact List.mem_append_right _ (List.mem_append_left _ (queried_mapM_mem answers f xs a ha q hq))
end ClaudeWCT.W9.T3M.Extract
