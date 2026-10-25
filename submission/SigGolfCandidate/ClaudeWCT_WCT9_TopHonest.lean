import SigGolfCandidate.ClaudeWCT_WCT9_Correctness
import SigGolfCandidate.ClaudeWCT_WCT9_TopNonce

/-! # Top-nonce layer (img-v6): honest node inputs with nonces (r3-lean-nonsec)

The honest input of a tree node `(lay, tree, level, c)` (children at `level`, heap `2^(height lay - level - 1) + c`)
is `left | merkleTweak | nonce | right`. The nonce slot is the keygen nonce search's result on the top tree (levels
0..10, `honestNonce`) and 0 elsewhere (the root and every lower tree). `wotsTree_node_nonce` states the honest node
equation for the top tree with this nonce. -/
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The 16-byte nonce slot of a top node input (`T3.nonceBytes n`) as a digest. -/
def nonceDigest (n : Nat) : Digest := BitVec.ofNat 128 (n % 2 ^ 64)
theorem bytesLE_nonceDigest (n : Nat) : bytesLE 16 (nonceDigest n) = nonceBytes n := rfl
theorem nonceDigest_zero : nonceDigest 0 = 0 := rfl
theorem nonceDigest_inj {n m : Nat} (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) (h : nonceDigest n = nonceDigest m) :
    n = m := by
  unfold nonceDigest at h
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact this

/-- Node input with nonce slot `n` (all layers; `n = 0` is `merkleNodeInput`). -/
def merkleNodeInputN (lay tree heap n : Nat) (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (merkleTweak lay tree heap) ++ bytesLE 16 (nonceDigest n) ++ bytesLE 16 right

theorem merkleNodeInputN_zero (lay tree heap : Nat) (left right : Digest) :
    merkleNodeInputN lay tree heap 0 left right = merkleNodeInput lay tree heap left right := by
  unfold merkleNodeInputN merkleNodeInput
  rw [nonceDigest_zero, bytesLE_zero16]

theorem merkleNodeInputN_length (lay tree heap n : Nat) (left right : Digest) :
    (merkleNodeInputN lay tree heap n left right).length = 64 := by
  simp [merkleNodeInputN, SphincsSecurity.bytesLE_length]

theorem pad64_merkleNodeInputN (lay tree heap n : Nat) (left right : Digest) :
    pad64 (merkleNodeInputN lay tree heap n left right) = merkleNodeInputN lay tree heap n left right := by
  unfold pad64; rw [merkleNodeInputN_length]; simp

theorem merkleNodeInputN_eq_lowerNodeInputP (lay tree heap n : Nat) (left right : Digest) :
    merkleNodeInputN lay tree heap n left right = lowerNodeInputP lay tree heap left 0 (nonceDigest n) right := by
  unfold merkleNodeInputN lowerNodeInputP
  rw [merkleTweak_eq_word]
  rfl

theorem merkleTweak_top0 (tree heap : Nat) : merkleTweak 0 tree heap = nodeTweak 3 0 0 heap := by
  rw [merkleTweak_top]
  unfold nodeTweak
  simp

theorem merkleNodeInputN_top (tree heap n : Nat) (left right : Digest) :
    merkleNodeInputN 0 tree heap n left right = topNodeInput heap n left right := by
  unfold merkleNodeInputN topNodeInput
  rw [merkleTweak_top0, bytesLE_nonceDigest]

/-- The honest nonce of node `(lay, tree, level, c)` (children at `level`): the keygen nonce search on the top tree
(`level < 11`), 0 on the root and on every lower tree. -/
noncomputable def honestNonce (answers : Answers) (lay : Layer) (tree level c : Nat) : Nat :=
  if lay = 0 ∧ level < 11 then
    (evalWithAnswerFn answers (topNodeAt (level + 1) (2 ^ (height lay - level - 1) + c)
      (treeValue (wotsTree answers lay tree) level (2 * c))
      (treeValue (wotsTree answers lay tree) level (2 * c + 1)))).1
  else 0

theorem honestNonce_lower (answers : Answers) {lay : Layer} (h : lay ≠ 0) (tree level c : Nat) :
    honestNonce answers lay tree level c = 0 := by
  unfold honestNonce; rw [if_neg (fun h' => h h'.1)]

theorem honestNonce_root (answers : Answers) (lay : Layer) (tree c : Nat) :
    honestNonce answers lay tree 11 c = 0 := by
  unfold honestNonce; rw [if_neg (fun h' => by omega)]

theorem honestInputN_lower (answers : Answers) {lay : Layer} (h : lay ≠ 0) (tree heap level c : Nat)
    (left right : Digest) :
    merkleNodeInputN lay.val tree heap (honestNonce answers lay tree level c) left right =
      merkleNodeInput lay.val tree heap left right := by
  rw [honestNonce_lower answers h, merkleNodeInputN_zero]

/-- The honest top-tree node equation with nonces: node `c` of level `level + 1` is the used half of the hash of its
honest nonce input. -/
theorem wotsTree_node_nonce (answers : Answers) (tree level c : Nat) (hl : level < 12)
    (hc : c < 2 ^ (11 - level)) :
    treeValue (wotsTree answers 0 tree) (level + 1) c =
      evalWithAnswerFn answers (projHash (lowerHigh 0 (2 ^ (11 - level) + c))
        (merkleNodeInputN 0 tree (2 ^ (11 - level) + c) (honestNonce answers 0 tree level c)
          (treeValue (wotsTree answers 0 tree) level (2 * c))
          (treeValue (wotsTree answers 0 tree) level (2 * c + 1)))) := by
  have hw : wotsTree answers 0 tree =
      evalWithAnswerFn answers (buildTopLevels ((List.range (2 ^ height 0)).map (wotsRoot answers 0 tree))) := by
    unfold wotsTree; rw [if_pos rfl]
  have htree := eval_buildTopLevels_correct answers ((List.range (2 ^ height 0)).map (wotsRoot answers 0 tree))
    (by simp [height])
  rw [← hw] at htree
  have hnode := htree.2.2 level hl c (by simpa [show 12 - (level + 1) = 11 - level by omega] using hc)
  have hheap : 2 ^ (12 - (level + 1)) + c = 2 ^ (11 - level) + c := by
    rw [show 12 - (level + 1) = 11 - level by omega]
  rw [hheap] at hnode
  unfold treeValue
  rw [hnode, merkleNodeInputN_top, lowerHigh_top_eq_nodeHalfHigh]
  unfold topLevelNode
  by_cases h12 : level + 1 = 12
  · rw [if_pos h12]
    have h11 : level = 11 := by omega
    subst h11
    rw [honestNonce_root]
    unfold nodeHash topNodeInput
    rw [show nonceBytes 0 = zero16 from (bytesLE_nonceDigest 0).symm.trans
      (by rw [nonceDigest_zero, bytesLE_zero16])]
  · rw [if_neg h12]
    have hn : honestNonce answers 0 tree level c =
        (evalWithAnswerFn answers (topNodeAt (level + 1) (2 ^ (11 - level) + c)
          ((wotsTree answers 0 tree).getD level [] |>.getD (2 * c) 0)
          ((wotsTree answers 0 tree).getD level [] |>.getD (2 * c + 1) 0))).1 := by
      unfold honestNonce
      rw [if_pos ⟨rfl, by omega⟩]
      rw [show height (0 : Layer) - level - 1 = 11 - level by simp [height]; omega]
      rfl
    rw [hn]
    exact (eval_topNodeAt_hash answers (level + 1) (2 ^ (11 - level) + c) _ _).symm

/-- The honest node equation of every layer, with the honest nonce. -/
theorem wotsTree_node_any (answers : Answers) (lay : Layer) (tree level c : Nat) (hl : level < height lay)
    (hc : c < 2 ^ (height lay - level - 1)) :
    treeValue (wotsTree answers lay tree) (level + 1) c =
      evalWithAnswerFn answers (halfHash (lowerHigh lay.val (2 ^ (height lay - level - 1) + c))
        (merkleNodeInputN lay.val tree (2 ^ (height lay - level - 1) + c)
          (honestNonce answers lay tree level c)
          (treeValue (wotsTree answers lay tree) level (2 * c))
          (treeValue (wotsTree answers lay tree) level (2 * c + 1)))) := by
  by_cases h0 : lay = 0
  · subst h0
    have hh : height (0 : Layer) - level - 1 = 11 - level := by simp [height]; omega
    rw [hh] at hc ⊢
    rw [halfHash_eq_projHash]
    exact wotsTree_node_nonce answers tree level c (by simp [height] at hl; omega) hc
  · obtain ⟨-, -, hnodes⟩ := wotsTree_correct answers h0 tree
    have hsub : height lay - (level + 1) = height lay - level - 1 := by omega
    have hrec := hnodes level hl c (by rw [hsub]; exact hc)
    rw [hsub] at hrec
    unfold treeValue
    rw [hrec, honestInputN_lower answers h0]
    rfl

end ClaudeWCT.WCT9
