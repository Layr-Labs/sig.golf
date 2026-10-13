import SigGolfCandidate.T3M.Witness.Queries
import SigGolfCandidate.T3M.Extract.Normalize
import SigGolfCandidate.ClaudeWCT.WCT9.Correctness

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open ClaudeWCT.WCT9 (wotsTree wotsSeed wotsEnd)
open SphincsSecurity (bytesLE)
export SigGolfCandidate.T3M.Extract (canonicalHeader)
noncomputable def honestRoot (answers : Answers) (lay : Layer) (tree : Nat) : Digest :=
  treeValue (wotsTree answers lay tree) (height lay) 0
noncomputable def honestPair (answers : Answers) (lay : Layer) (tree : Nat) : Digest × Digest :=
  (treeValue (wotsTree answers lay tree) (height lay - 1) 0, treeValue (wotsTree answers lay tree) (height lay - 1) 1)
/-- FTS seed of `(index, coord, child, chain)`: the stage-A seed family of `(index, coord)` at `ftsPoint child chain`
(agrees with `WCT9.seed` by `rfl`). -/
def wctSeed (answers : Answers) (index coord child chain : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval (List.ofFn (WCT9.ftsCoef answers index coord)) (WCT9.ftsPoint child chain)
def wctValue (answers : Answers) (index coord child chain step : Nat) : Digest :=
  evalWithAnswerFn answers (WCT9.chain index coord child chain 0 step (wctSeed answers index coord child chain))
def wctEnds (answers : Answers) (index coord child : Nat) : List Digest :=
  List.ofFn fun t : Fin 6 => wctValue answers index coord child t.val 4
/-- Honest pads of coordinate `coord` (nested FTS r1-1): the honest top pair of `coord - 1`, `(0, 0)` for 0. -/
abbrev ftsPrev (answers : Answers) (index coord : Nat) : Digest × Digest := WCT9.ftsPrev answers index coord
def ftsLeaves (answers : Answers) (index coord : Nat) : List Digest :=
  List.ofFn fun j : Fin 128 => evalWithAnswerFn answers
    (WCT9.leafHashP index coord j.val (ftsPrev answers index coord).1 (wctEnds answers index coord j.val))
def ftsNodes (answers : Answers) (index coord : Nat) : Array Digest :=
  evalWithAnswerFn answers (WCT9.heapBuild index coord (ftsPrev answers index coord).2 (ftsLeaves answers index coord))
def ftsLevels (answers : Answers) (index coord : Nat) : List (List Digest) :=
  WCT9.heapLevels (ftsNodes answers index coord)
def ftsPair (answers : Answers) (index coord : Nat) : Digest × Digest :=
  (treeValue (ftsLevels answers index coord) 6 0, treeValue (ftsLevels answers index coord) 6 1)
def ftsPairsHonest (answers : Answers) (index : Nat) : List (Digest × Digest) :=
  (List.range 9).map (ftsPair answers index)
def listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) : HashInput :=
  bytesLE 16 first ++ bytesLE 16 hdr ++ rest.flatMap (bytesLE 16)
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  SigGolfCandidate.T3.leafInput lay tree leaf ends
/-- Honest FTS leaf input (campaign T8): `end0 | header | zero pad | end1..end5`, i.e. the pad slot is the first
digest of the list part. -/
def wctLeafInput (index coord child : Nat) (ends : List Digest) : HashInput :=
  listInput (ends.getD 0 0) (WCT9.ftsLeafHeader index coord child) (0 :: ends.drop 1)
/-- Padded FTS leaf input (campaign T8): the leaf pad `pad` in the slot after the header. -/
def wctLeafInputP (index coord child : Nat) (pad : Digest) (ends : List Digest) : HashInput :=
  listInput (ends.getD 0 0) (WCT9.ftsLeafHeader index coord child) (pad :: ends.drop 1)
theorem wctLeafInputP_zero (index coord child : Nat) (ends : List Digest) :
    wctLeafInputP index coord child 0 ends = wctLeafInput index coord child ends := rfl
abbrev forestInput (index : Nat) (pairs : List (Digest × Digest)) : HashInput := WCT9.forestInput index pairs
def honestForest (answers : Answers) (index : Nat) : Digest :=
  evalWithAnswerFn answers (WCT9.forestPk index (ftsPairsHonest answers index))
/-- Honest L3 message (nested FTS r1-1): the top pair of coordinate 8. -/
def honestTop (answers : Answers) (index : Nat) : Digest × Digest := ftsPair answers index 8
noncomputable def honestMsg (answers : Answers) (index : Nat) (lay : Layer) : WCT9.LayerMsg :=
  if h : lay.val < 3 then
    .pair (honestPair answers ⟨lay.val + 1, by omega⟩ (route index ⟨lay.val + 1, by omega⟩).2).1
      (honestPair answers ⟨lay.val + 1, by omega⟩ (route index ⟨lay.val + 1, by omega⟩).2).2
  else .pair (honestTop answers index).1 (honestTop answers index).2
/-- Tree index bits per layer (the routed tree of an index below `2 ^ 31`). -/
def treeBits (lay : Layer) : Nat := ![0, 12, 19, 25] lay
theorem treeBits_le (lay : Layer) : treeBits lay ≤ 25 := by fin_cases lay <;> decide
theorem tree_lt_of_treeBits {lay : Layer} {tree : Nat} (ht : tree < 2 ^ treeBits lay) : tree < 2 ^ 31 :=
  lt_of_lt_of_le ht (le_trans (Nat.pow_le_pow_right (by decide) (treeBits_le lay)) (by norm_num))
theorem leaf_lt_4096 {lay : Layer} {leaf : Nat} (hl : leaf < 2 ^ height lay) : leaf < 4096 := by
  fin_cases lay <;> simp [height] at hl ⊢ <;> omega
inductive Pos where
  | chain (lay : Layer) (tree leaf i step : Nat)
  | leaf (lay : Layer) (tree leaf : Nat)
  | node (lay : Layer) (tree level node : Nat)
  | forest (index : Nat)
  | wctChain (index coord child chain step : Nat)
  | wctLeaf (index coord child : Nat)
  | wctNode (index coord level node : Nat)
noncomputable def honestInput (answers : Answers) : Pos → HashInput
  | .chain lay tree leaf i step => pad64 (chainInput lay tree leaf i step
      (honestChainValue answers lay tree leaf i (wotsSeed answers lay tree leaf i) step))
  | .leaf lay tree leaf => pad64 (leafInput lay tree leaf
      ((List.range (chainCount lay)).map (wotsEnd answers lay tree leaf)))
  | .node lay tree level node => pad64 (WCT9.merkleNodeInput lay.val tree (2 ^ (height lay - level - 1) + node)
      (treeValue (wotsTree answers lay tree) level (2 * node))
      (treeValue (wotsTree answers lay tree) level (2 * node + 1)))
  | .forest index => pad64 (forestInput index (ftsPairsHonest answers index))
  | .wctChain index coord child chain step => pad64 (WCT9.chainInput index coord child chain step
      (wctValue answers index coord child chain step))
  | .wctLeaf index coord child => pad64 (wctLeafInputP index coord child (ftsPrev answers index coord).1
      (wctEnds answers index coord child))
  | .wctNode index coord level node => pad64 (nodeInputP 3 (WCT9.nodeLayer coord) index (2 ^ (7 - level - 1) + node)
      (treeValue (ftsLevels answers index coord) level (2 * node))
      (if level = 5 then (ftsPrev answers index coord).2 else 0)
      (treeValue (ftsLevels answers index coord) level (2 * node + 1)))
def Pos.hdr : Pos → BitVec 128
  | .chain lay tree lf i step => chainHeader lay tree lf i step
  | .leaf lay tree lf => leafTweak lay tree lf
  | .node lay tree level nd => WCT9.merkleTweak lay.val tree (2 ^ (height lay - level - 1) + nd)
  | .forest index => header 15 0 index 0 0
  | .wctChain index coord child t step => WCT9.ftsChainHeader index coord child t step
  | .wctLeaf index coord child => WCT9.ftsLeafHeader index coord child
  | .wctNode index coord level nd => WCT9.wctNodeHeader coord index (2 ^ (7 - level - 1) + nd)
def Pos.Bounded : Pos → Prop
  | .chain _ tree lf i step => tree < 2 ^ 31 ∧ lf < 4096 ∧ i < 64 ∧ step < 7
  | .leaf lay tree lf => lf < 2 ^ height lay ∧ tree * 2 ^ height lay + lf < 2 ^ 32
  | .node lay tree level nd => tree < 2 ^ 32 ∧ level < height lay ∧ (lay = 0 ∨ level + 1 < height lay) ∧
      (lay = 0 → tree = 0) ∧ nd < 2 ^ (height lay - level - 1)
  | .forest index => index < 2 ^ 40
  | .wctChain index coord child t step => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6 ∧ step < 4
  | .wctLeaf index coord child => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128
  | .wctNode index coord level nd => index < 2 ^ 31 ∧ coord < 9 ∧ level < 6 ∧ nd < 2 ^ (7 - level - 1)
/-- Whether a position's honest value is the HIGH half of its hash output: FTS leaves and nodes on
`WCT9.ftsHighHeap` heaps (the top pair, nested FTS r1-1, and the even heaps `16..255`, C1), the left children of the
lower trees (C2: lower leaves and nodes of even heap, `WCT9.lowerHigh`) and the last step of lower chain 0 (C3,
`WCT9.chainHigh`). -/
def Pos.high : Pos → Bool
  | .wctNode _ _ level nd => WCT9.ftsHighHeap (2 ^ (7 - level - 1) + nd)
  | .wctLeaf _ _ child => WCT9.ftsHighHeap (128 + child)
  | .leaf lay _ lf => WCT9.lowerHigh lay.val lf
  | .node lay _ level nd => WCT9.lowerHigh lay.val (2 ^ (height lay - level - 1) + nd)
  | .chain lay _ _ i step => WCT9.chainHigh lay i step
  | _ => false
/-- The 128-bit half of an output that a position's honest value uses. For FTS leaves and nodes this is
`WCT9.ftsHalf` of their heap (definitionally). -/
def Pos.proj (p : Pos) : HashOutput → Digest := WCT9.halfOf p.high
theorem Pos.proj_eq (p : Pos) :
    p.proj = fun a => if p.high then a.extractLsb' 128 128 else a.extractLsb' 0 128 := rfl
theorem Pos.proj_of_low {p : Pos} (h : p.high = false) : p.proj = fun a => a.extractLsb' 0 128 := by
  unfold Pos.proj; rw [h]; rfl
theorem Pos.proj_of_high {p : Pos} (h : p.high = true) : p.proj = fun a => a.extractLsb' 128 128 := by
  unfold Pos.proj; rw [h]; rfl
/-- The (padded) length of a position's honest input (S2-2). -/
def Pos.len : Pos → Nat
  | .leaf lay _ _ => if lay = 0 then 896 else 704
  | .wctLeaf .. => 128
  | .forest .. => 320
  | _ => 64
/-- A hit at a position: a different input whose output agrees with the honest one on the used half. -/
def HashHitAt (answers : Answers) (pos : Pos) (honest actual : HashInput) : Prop :=
  actual ≠ honest ∧ pos.proj (answers (.inl (.inr actual))) = pos.proj (answers (.inl (.inr honest)))
theorem hashHitAt_of_low {answers : Answers} {pos : Pos} {honest actual : HashInput}
    (hp : pos.proj = fun a => a.extractLsb' 0 128) (h : HashHit answers honest actual) :
    HashHitAt answers pos honest actual := by
  unfold HashHitAt; rw [hp]; exact h
def hdrBlock (input : HashInput) : HashInput := (input.drop 16).take 16
/-- C3 (FULL, S2-2): the decoding key of an input's header block. Leaf-length inputs (704 or 896 bytes) are keyed by
the low tweak word only (the leaf tweak's high word is a witness pad); every other input by its canonical header. -/
def hdrKey (x : HashInput) : HashInput :=
  if x.length = 704 ∨ x.length = 896 then (hdrBlock x).take 8 ++ List.replicate 8 0 else canonicalHeader (hdrBlock x)
/-- Same length and same decoding key (C3 FULL; S2-2). -/
def SameHeader (actual honest : HashInput) : Prop :=
  actual.length = honest.length ∧ hdrKey actual = hdrKey honest
theorem hdrKey_of_len64 {x : HashInput} (h : x.length = 64) : hdrKey x = canonicalHeader (hdrBlock x) := by
  unfold hdrKey; rw [if_neg (by omega)]
theorem hdrKey_congr {a b : HashInput} (hl : a.length = b.length) (hb : hdrBlock a = hdrBlock b) :
    hdrKey a = hdrKey b := by
  unfold hdrKey; rw [hl, hb]
theorem SameHeader.of_hdrBlock {a b : HashInput} (hl : a.length = b.length) (hb : hdrBlock a = hdrBlock b) :
    SameHeader a b := ⟨hl, hdrKey_congr hl hb⟩
theorem SameHeader.of_canonical {a b : HashInput} (hl : a.length = b.length)
    (hn : ¬ (b.length = 704 ∨ b.length = 896))
    (hc : canonicalHeader (hdrBlock a) = canonicalHeader (hdrBlock b)) : SameHeader a b := by
  refine ⟨hl, ?_⟩
  unfold hdrKey
  rw [if_neg (by rw [hl]; exact hn), if_neg hn, hc]
theorem pad64_length_congr {a b : HashInput} (h : a.length = b.length) : (pad64 a).length = (pad64 b).length := by
  simp only [pad64, List.length_append, List.length_replicate, h]
def HitIn (answers : Answers) (qs : List Spec.Domain) : Prop :=
  ∃ pos actual, pos.Bounded ∧ .inl (.inr actual) ∈ qs ∧ HashHitAt answers pos (honestInput answers pos) actual ∧
    SameHeader actual (honestInput answers pos)
theorem HitIn.mono {answers : Answers} {qs qs' : List Spec.Domain} (h : HitIn answers qs)
    (hsub : ∀ q ∈ qs, q ∈ qs') : HitIn answers qs' := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  exact ⟨pos, actual, hb, hsub _ hq, hh, hs⟩
theorem HitIn.append_left {answers : Answers} {qs : List Spec.Domain} (qs' : List Spec.Domain)
    (h : HitIn answers qs) : HitIn answers (qs ++ qs') :=
  h.mono fun _ hq => List.mem_append_left _ hq
theorem HitIn.append_right {answers : Answers} {qs' : List Spec.Domain} (qs : List Spec.Domain)
    (h : HitIn answers qs') : HitIn answers (qs ++ qs') :=
  h.mono fun _ hq => List.mem_append_right _ hq
theorem ftsPairsHonest_length (answers : Answers) (index : Nat) : (ftsPairsHonest answers index).length = 9 := by
  simp [ftsPairsHonest]
theorem wctEnds_length (answers : Answers) (index coord child : Nat) :
    (wctEnds answers index coord child).length = 6 := by
  simp [wctEnds]
end ClaudeWCT.W9.T3M.Extract
