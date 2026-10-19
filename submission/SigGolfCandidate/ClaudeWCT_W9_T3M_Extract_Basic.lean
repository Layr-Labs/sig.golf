import SigGolfCandidate.T3M_Witness_Queries
import SigGolfCandidate.T3M_Extract_Normalize
import SigGolfCandidate.ClaudeWCT_WCT9_Correctness
import SigGolfCandidate.ClaudeWCT_WCT9_TopHonest
import SigGolfCandidate.Research_V7Composed198Gate

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
/-- The honest chain value of the current scheme after `step` steps (`WCT9.chainW`; pairing stage 1: the G chains'
interior steps keep the high half). -/
def honestChainValueW (answers : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) (step : Nat) : Digest :=
  evalWithAnswerFn answers (WCT9.chainW lay tree leaf i 0 step seed)
inductive Pos where
  | chain (lay : Layer) (tree leaf i step : Nat)
  | leaf (lay : Layer) (tree leaf : Nat)
  | node (lay : Layer) (tree level node : Nat)
  | forest (index : Nat)
  | wctChain (index coord child chain step : Nat)
  | wctLeaf (index coord child : Nat)
  | wctNode (index coord level node : Nat)
noncomputable def honestInput (answers : Answers) : Pos → HashInput
  | .chain lay tree leaf i step => pad64 (WCT9.chainInputW lay tree leaf i step
      (honestChainValueW answers lay tree leaf i (wotsSeed answers lay tree leaf i) step))
  | .leaf lay tree leaf => pad64 (leafInput lay tree leaf
      ((List.range (chainCount lay)).map (wotsEnd answers lay tree leaf)))
  | .node lay tree level node => pad64 (WCT9.merkleNodeInputN lay.val tree (2 ^ (height lay - level - 1) + node)
      (WCT9.honestNonce answers lay tree level node)
      (treeValue (wotsTree answers lay tree) level (2 * node))
      (treeValue (wotsTree answers lay tree) level (2 * node + 1)))
  | .forest index => pad64 (forestInput index (ftsPairsHonest answers index))
  | .wctChain index coord child chain step => pad64 (WCT9.ftsChainInputW index coord child chain step
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
/-- Whether a position's honest value is the HIGH half of its hash output (C2/C3 on the paired tree). The legacy
unpaired FTS positions keep the paired tree's legacy rule (the top FTS nodes, `wctNode` level 5, nested FTS r1-1; the
paired forest's halves live in `Extract.Paired`). The lower trees follow #866: the left children (C2: lower leaves and
nodes of even heap, `WCT9.lowerHigh`) and the last step of lower chain 0 (C3, `WCT9.chainHigh`). -/
def Pos.high : Pos → Bool
  | .wctNode _ _ level _ => decide (level = 5)
  | .leaf lay _ lf => WCT9.lowerHigh lay.val lf
  | .node lay _ level nd => WCT9.lowerHigh lay.val (2 ^ (height lay - level - 1) + nd)
  | .chain lay _ _ i step => WCT9.chainHigh lay i step
  | .wctChain _ _ _ t step => WCT9.ftsChainHigh t step
  | _ => false
/-- The 128-bit half of an output that a position's honest value uses. -/
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
/-- C4: a header block whose low word `W` (its first 8 bytes) satisfies `1 ≤ W < 2 ^ 16`. Among 64-byte positions
only the top folds have such a label (`T3.topNodeWord`, in `[1, 4096)`): the digest has `W = 0`, every FTS word is
`≥ 2 ^ 16` (coordinate nibble `coord + 1`), WOTS chain and lower fold words carry type byte 193. -/
def TopLow (b : HashInput) : Prop := 1 ≤ readLE (b.take 8) ∧ readLE (b.take 8) < 2 ^ 16
instance (b : HashInput) : Decidable (TopLow b) :=
  inferInstanceAs (Decidable (1 ≤ readLE (b.take 8) ∧ readLE (b.take 8) < 2 ^ 16))
/-- C3 (FULL, S2-2) + C4: the decoding key of an input's header block. Leaf-length inputs (704 or 896 bytes) and
64-byte inputs with a top label (`TopLow`) are keyed by the low tweak word only (their high word is a witness pad);
every other input by its canonical header. -/
def hdrKey (x : HashInput) : HashInput :=
  if x.length = 704 ∨ x.length = 896 then (hdrBlock x).take 8 ++ List.replicate 8 0
  else if x.length = 64 ∧ TopLow (hdrBlock x) then (hdrBlock x).take 8 ++ List.replicate 8 0
  else canonicalHeader (hdrBlock x)
/-- Same length and same decoding key (C3 FULL; S2-2). -/
def SameHeader (actual honest : HashInput) : Prop :=
  actual.length = honest.length ∧ hdrKey actual = hdrKey honest
/-- C4: a 64-byte input without a top label is keyed by its canonical header. -/
theorem hdrKey_of_len64 {x : HashInput} (h : x.length = 64) (ht : ¬ TopLow (hdrBlock x)) :
    hdrKey x = canonicalHeader (hdrBlock x) := by
  unfold hdrKey; rw [if_neg (by omega), if_neg (fun h' => ht h'.2)]
/-- C4: a 64-byte input with a top label is keyed by its low word. -/
theorem hdrKey_of_top {x : HashInput} (h : x.length = 64) (ht : TopLow (hdrBlock x)) :
    hdrKey x = (hdrBlock x).take 8 ++ List.replicate 8 0 := by
  unfold hdrKey; rw [if_neg (by omega), if_pos ⟨h, ht⟩]
theorem hdrBlock_length_of_64 {x : HashInput} (h : x.length = 64) : (hdrBlock x).length = 16 := by
  unfold hdrBlock; simp [h]
theorem canonicalHeader_take8 {h : HashInput} (hl : 8 ≤ h.length) : (canonicalHeader h).take 8 = h.take 8 := by
  unfold canonicalHeader
  split
  · rw [List.take_append_of_le_length (by simp; omega)]; simp
  · rfl
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
  rw [if_neg (by rw [hl]; exact hn), if_neg hn]
  by_cases h64 : b.length = 64
  · have ha := hdrBlock_length_of_64 (hl.trans h64)
    have hb := hdrBlock_length_of_64 h64
    have ht : (hdrBlock a).take 8 = (hdrBlock b).take 8 := by
      rw [← canonicalHeader_take8 (by omega : 8 ≤ (hdrBlock a).length), hc,
        canonicalHeader_take8 (by omega : 8 ≤ (hdrBlock b).length)]
    have hT : TopLow (hdrBlock a) ↔ TopLow (hdrBlock b) := by unfold TopLow; rw [ht]
    by_cases hT' : TopLow (hdrBlock b)
    · rw [if_pos ⟨hl.trans h64, hT.mpr hT'⟩, if_pos ⟨h64, hT'⟩, ht]
    · rw [if_neg (fun h => hT' (hT.mp h.2)), if_neg (fun h => hT' h.2), hc]
  · rw [if_neg (fun h => h64 (by rw [← hl]; exact h.1)), if_neg (fun h => h64 h.1), hc]
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


namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The four canonical paired commitments preceding the final singleton. -/
def pairPrev (answers : Answers) (index : Nat) : Nat → SharedForest.PairRoot
  | 0 => ClaudeWCT.WCT9.ftsStart
  | n+1 => SharedForest.expectedPairRoot answers index n (pairPrev answers index n)

def first (coord : Nat) : Bool := decide (coord < 8 ∧ coord % 2 = 0)

def physical (coord raw : Nat) : Nat := SharedForest.physicalChild (first coord) raw

def pads (answers : Answers) (index coord branch : Nat) : SharedForest.PairRoot :=
  if coord = 8 then pairPrev answers index 4
  else if first coord then pairPrev answers index (coord/2)
  else SharedForest.nodesPair
    (SharedForest.firstNodes answers index (coord/2) (pairPrev answers index (coord/2))) branch

def nodes (answers : Answers) (index coord : Nat) : Array Digest :=
  if coord = 8 then SharedForest.sharedNodes answers false index 8 (fun _ => pairPrev answers index 4)
  else if first coord then SharedForest.firstNodes answers index (coord/2) (pairPrev answers index (coord/2))
  else SharedForest.secondNodes answers index (coord/2) (pairPrev answers index (coord/2))

/-- Every used node chooses one fixed balanced128-bit output projection. -/
def highPosition (coord level : Nat) : Prop :=
  coord < 8 ∧ ((coord % 2 = 0 ∧ level = 4) ∨ (coord % 2 = 1 ∧ level = 5))
instance (coord level : Nat) : Decidable (highPosition coord level) := by
  unfold highPosition
  infer_instance

/-- Stage 2 (merged singleton "Cm"): the final singleton's left top node (coordinate 8, level 5, node 0 = heap 2)
keeps the HIGH half of its output (its value lands on `WIT + 0`, the junk low half below the witness, so the C3 row
pad at `WIT + 24` stays witness memory); its right top node (heap 3) keeps the low half. -/
def singletonHigh (coord level node : Nat) : Prop := coord = 8 ∧ level = 5 ∧ node = 0
instance (coord level node : Nat) : Decidable (singletonHigh coord level node) := by
  unfold singletonHigh
  infer_instance

/-- C1 (FTS Merkle half-swap): node `node` of level `level` (heap `2^(6-level) + node`) uses the high half on the
top folds of `highPosition`, on the singleton's left top node (stage 2, `singletonHigh`) and on every even heap
`16..127` (the even nodes of levels `0..2`). -/
def highNodeAt (coord level node : Nat) : Prop :=
  (highPosition coord level ∨ singletonHigh coord level node) ∨ (level ≤ 2 ∧ node % 2 = 0)
instance (coord level node : Nat) : Decidable (highNodeAt coord level node) := by
  unfold highNodeAt
  infer_instance

/-- Stage 2: the top folds (level 5) of the final singleton: heap 2 (node 0) high, heap 3 (node 1) low. -/
theorem highNodeAt_singleton (node : Nat) : highNodeAt 8 5 node ↔ node = 0 := by
  unfold highNodeAt highPosition singletonHigh
  omega

/-- No packed node (`level ≤ 4`) and no A/B top fold is a singleton top node. -/
theorem not_singletonHigh_of_level {coord level node : Nat} (h : level ≠ 5) : ¬singletonHigh coord level node := by
  unfold singletonHigh
  omega

/-- C1: the leaf of raw child `child` (heap `128 + physical`) uses the high half on even physical children. -/
def highLeafAt (coord child : Nat) : Prop := physical coord child % 2 = 0
instance (coord child : Nat) : Decidable (highLeafAt coord child) := by
  unfold highLeafAt
  infer_instance

/-- The used half of a position's output on the paired tree. FTS leaves and nodes follow `highLeafAt` /
`highNodeAt`; the lower-tree positions follow #866's C2/C3 rule (`Extract.Pos.high`: the left children of the lower
trees and the last step of lower chain 0 are high; `proj_lower` states that this is `Pos.proj`); everything else uses
the low half. The lower cases are written as `if`s so that `simp only [proj, ite_apply]` unfolds every case alike. -/
def proj : Pos → HashOutput → Digest
  | .wctNode _ coord level node => if highNodeAt coord level node then
      fun answer => answer.extractLsb' 128 128 else fun answer => answer.extractLsb' 0 128
  | .wctLeaf _ coord child => if highLeafAt coord child then
      fun answer => answer.extractLsb' 128 128 else fun answer => answer.extractLsb' 0 128
  | .chain lay _ _ i step => if ClaudeWCT.WCT9.chainHigh lay i step then
      fun answer => answer.extractLsb' 128 128 else fun answer => answer.extractLsb' 0 128
  | .wctChain _ _ _ t step => if ClaudeWCT.WCT9.ftsChainHigh t step then
      fun answer => answer.extractLsb' 128 128 else fun answer => answer.extractLsb' 0 128
  | .leaf lay _ leaf => if ClaudeWCT.WCT9.lowerHigh lay.val leaf then
      fun answer => answer.extractLsb' 128 128 else fun answer => answer.extractLsb' 0 128
  | .node lay _ level node => if ClaudeWCT.WCT9.lowerHigh lay.val (2 ^ (height lay - level - 1) + node) then
      fun answer => answer.extractLsb' 128 128 else fun answer => answer.extractLsb' 0 128
  | _ => fun answer => answer.extractLsb' 0 128

/-- C2/C3: on every non-FTS position the paired projection is the legacy (#866) `Pos.proj`. -/
theorem proj_lower (position : Pos) (hn : ∀ index coord level node, position ≠ .wctNode index coord level node)
    (hl : ∀ index coord child, position ≠ .wctLeaf index coord child) : proj position = position.proj := by
  funext answer
  rw [Pos.proj_eq]
  cases position with
  | wctNode index coord level node => exact (hn index coord level node rfl).elim
  | wctLeaf index coord child => exact (hl index coord child rfl).elim
  | chain lay tree leaf i step => simp only [proj, Pos.high, ite_apply] <;> rfl
  | leaf lay tree leaf => simp only [proj, Pos.high, ite_apply] <;> rfl
  | node lay tree level node => simp only [proj, Pos.high, ite_apply] <;> rfl
  | forest index => simp only [proj, Pos.high, Bool.false_eq_true, ↓reduceIte]
  | wctChain index coord child t step => simp only [proj, Pos.high, ite_apply] <;> rfl
/-- The main (lower-tree) positions: the paired projection is `Pos.proj` (unconditional forms of `proj_lower`). -/
theorem proj_chain (lay : Layer) (tree leaf i step : Nat) :
    proj (.chain lay tree leaf i step) = (Pos.chain lay tree leaf i step).proj :=
  proj_lower _ (fun _ _ _ _ h => Pos.noConfusion h) (fun _ _ _ h => Pos.noConfusion h)
theorem proj_leaf (lay : Layer) (tree leaf : Nat) : proj (.leaf lay tree leaf) = (Pos.leaf lay tree leaf).proj :=
  proj_lower _ (fun _ _ _ _ h => Pos.noConfusion h) (fun _ _ _ h => Pos.noConfusion h)
theorem proj_node (lay : Layer) (tree level node : Nat) :
    proj (.node lay tree level node) = (Pos.node lay tree level node).proj :=
  proj_lower _ (fun _ _ _ _ h => Pos.noConfusion h) (fun _ _ _ h => Pos.noConfusion h)

/-- C1: a leaf position projects onto the half of its heap `128 + physical`. -/
theorem proj_wctLeaf (index coord child : Nat) :
    proj (.wctLeaf index coord child) = ClaudeWCT.WCT9.ftsHalf (128 + physical coord child) := by
  funext answer
  have hiff := ClaudeWCT.WCT9.ftsHighHeap_iff (show 4 ≤ 128 + physical coord child by omega)
  by_cases h : physical coord child % 2 = 0
  · have ht : ClaudeWCT.WCT9.ftsHighHeap (128 + physical coord child) = true := hiff.mpr ⟨by omega, by omega⟩
    simp [proj, highLeafAt, h, ClaudeWCT.WCT9.ftsHalf, ht]
  · have hf : ClaudeWCT.WCT9.ftsHighHeap (128 + physical coord child) = false :=
      Bool.eq_false_iff.mpr (fun ht => h (by have := (hiff.mp ht).2; omega))
    simp [proj, highLeafAt, h, ClaudeWCT.WCT9.ftsHalf, hf]

/-- C1: below the top folds (`level ≤ 3`, heaps `8..127`) the high nodes are exactly the `ftsHighHeap` heaps. -/
theorem highNodeAt_packed (coord level node : Nat) (hl : level ≤ 3) (hn : node < 2 ^ (6 - level)) :
    ClaudeWCT.WCT9.ftsHighHeap (2 ^ (6 - level) + node) = decide (highNodeAt coord level node) := by
  have hp : ¬(highPosition coord level ∨ singletonHigh coord level node) := by
    unfold highPosition singletonHigh; omega
  have h4 : 4 ≤ 2 ^ (6 - level) + node := by interval_cases level <;> norm_num <;> omega
  have hiff := ClaudeWCT.WCT9.ftsHighHeap_iff h4
  have he : (16 ≤ 2 ^ (6 - level) + node ∧ (2 ^ (6 - level) + node) % 2 = 0) ↔ (level ≤ 2 ∧ node % 2 = 0) := by
    interval_cases level <;> norm_num at hn ⊢ <;> omega
  have hh : highNodeAt coord level node ↔ (level ≤ 2 ∧ node % 2 = 0) := by
    unfold highNodeAt
    exact ⟨fun h => h.resolve_left hp, Or.inr⟩
  by_cases hc : level ≤ 2 ∧ node % 2 = 0
  · rw [decide_eq_true (hh.mpr hc)]
    exact hiff.mpr (he.mpr hc)
  · rw [decide_eq_false (fun h => hc (hh.mp h))]
    exact Bool.eq_false_iff.mpr (fun ht => hc (he.mp (hiff.mp ht)))

/-- C1: below the top folds (`level ≤ 3`, heaps `8..127`) a node position projects onto the half of its heap. -/
theorem proj_wctNode_packed (index coord level node : Nat) (hl : level ≤ 3) (hn : node < 2 ^ (6 - level)) :
    proj (.wctNode index coord level node) = ClaudeWCT.WCT9.ftsHalf (2 ^ (6 - level) + node) := by
  funext answer
  have hh := highNodeAt_packed coord level node hl hn
  by_cases hc : highNodeAt coord level node
  · rw [decide_eq_true hc] at hh
    simp [proj, hc, ClaudeWCT.WCT9.ftsHalf, hh]
  · rw [decide_eq_false hc] at hh
    simp [proj, hc, ClaudeWCT.WCT9.ftsHalf, hh]

/-- C1: a node of level `level` hashes into the half of `highNodeAt coord level node`. -/
def nodeProgram (coord level node : Nat) (input : HashInput) : M Digest :=
  if highNodeAt coord level node then ClaudeWCT.WCT9.highHash input else shortHash input

set_option backward.isDefEq.respectTransparency false in
theorem eval_nodeProgram (answers : Answers) (index coord level node : Nat) (input : HashInput) :
    evalWithAnswerFn answers (nodeProgram coord level node input) =
      proj (.wctNode index coord level node) (answers (.inl (.inr (pad64 input)))) := by
  by_cases hp : highNodeAt coord level node
  · simp only [nodeProgram, proj, if_pos hp]
    rfl
  · simp only [nodeProgram, proj, if_neg hp]
    rfl

/-- Stage 2: an outer node other than the singleton's right top node (heap 3) keeps the high half. -/
theorem sharedOuterHash_of_high {coord heap : Nat} (h : ¬(coord = 8 ∧ heap = 3)) (index : Nat) (left right : Digest) :
    SharedForest.sharedOuterHash coord index heap left right =
      ClaudeWCT.WCT9.highHash (ClaudeWCT.WCT9.wctTopInput coord index heap left 0 right) := by
  unfold SharedForest.sharedOuterHash
  simp only [if_neg h]

/-- Stage 2: the singleton's right top node (heap 3) keeps the low half. -/
theorem sharedOuterHash_of_low {coord heap : Nat} (h : coord = 8 ∧ heap = 3) (index : Nat) (left right : Digest) :
    SharedForest.sharedOuterHash coord index heap left right =
      shortHash (ClaudeWCT.WCT9.wctTopInput coord index heap left 0 right) := by
  unfold SharedForest.sharedOuterHash
  simp only [if_pos h]

set_option backward.isDefEq.respectTransparency false in
/-- C1: the paired node at heap `2^(6-level)+node`, for any branch pads `ps`, is the fixed-projection hash of its
`wctTopInput`. -/
theorem sharedNode_eq_nodeProgramP (index coord level node : Nat) (hc : coord < 9) (hl : level < 6)
    (hn : node < 2^(6-level)) (hu : first coord = true → level < 5) (ps : Nat → SharedForest.PairRoot)
    (left right : Digest) :
    SharedForest.sharedNode (first coord) coord index (2^(6-level)+node) ps left right =
    nodeProgram coord level node (ClaudeWCT.WCT9.wctTopInput coord index (2^(6-level)+node) left
      (if level=4 then (ps ((2^(6-level)+node)/2-2)).2 else 0) right) := by
  have h4 : (2^(6-level)+node<4) ↔ level=5 := by
    interval_cases level <;> norm_num at hn ⊢ <;> omega
  have h8 : (2^(6-level)+node<8) ↔ 4≤level := by
    interval_cases level <;> norm_num at hn ⊢ <;> omega
  simp only [SharedForest.sharedNode, h4, h8]
  by_cases h5 : level=5
  · subst level
    have hnode2 : node < 2 := by
      have h := hn
      norm_num at h
      omega
    have hf : first coord = false := Bool.eq_false_iff.mpr (by intro h; have := hu h; omega)
    have hn : ¬(coord<8 ∧ coord%2=0) := by
      simpa only [first, decide_eq_false_iff_not] using hf
    by_cases hco : coord=8
    · subst coord
      -- Stage 2 (Cm): heap 2 (node 0) keeps the high half, heap 3 (node 1) the low half.
      rcases (show node = 0 ∨ node = 1 by omega) with rfl | rfl
      · have hp : highNodeAt 8 5 0 := (highNodeAt_singleton 0).mpr rfl
        rw [sharedOuterHash_of_high (by decide : ¬((8:Nat) = 8 ∧ 2^(6-5)+0 = 3))]
        simp only [nodeProgram, if_pos hp, ↓reduceIte]
        rfl
      · have hp : ¬highNodeAt 8 5 1 := fun h => absurd ((highNodeAt_singleton 1).mp h) (by decide)
        rw [sharedOuterHash_of_low (by decide : (8:Nat) = 8 ∧ 2^(6-5)+1 = 3)]
        simp only [nodeProgram, if_neg hp, ↓reduceIte]
        rfl
    · have hp : highNodeAt coord 5 node := Or.inl (Or.inl (by unfold highPosition; omega))
      rw [sharedOuterHash_of_high (fun h => hco h.1)]
      simp only [if_pos rfl, nodeProgram, if_pos hp, ↓reduceIte]
      rfl
  · simp only [if_neg h5]
    by_cases hlev : level=4
    · subst level
      simp only [show 4≤4 by decide, if_true, if_pos rfl]
      by_cases hf : first coord=true
      · have hp : highNodeAt coord 4 node := by
          have hc := of_decide_eq_true hf
          exact Or.inl (Or.inl ⟨hc.1,Or.inl ⟨hc.2,rfl⟩⟩)
        simp only [hf, if_true, nodeProgram, if_pos hp, ↓reduceIte]
      · have hp : ¬highNodeAt coord 4 node := by
          intro hp
          rcases hp with (hp|hp)|hp
          · apply hf
            simp only [first, decide_eq_true_eq]
            exact ⟨hp.1, by rcases hp.2 with hp|hp <;> omega⟩
          · exact not_singletonHigh_of_level (by decide) hp
          · omega
        simp only [hf, if_false, nodeProgram, if_neg hp, ↓reduceIte]
        rfl
    · have hlt : level<4 := by omega
      simp only [if_neg (show ¬4≤level by omega), if_neg hlev, ↓reduceIte]
      have hnode : ClaudeWCT.WCT9.wctNodeHashH coord index (2^(6-level)+node) left right =
          ClaudeWCT.WCT9.ftsHash (2^(6-level)+node) (ClaudeWCT.WCT9.wctTopInput coord index (2^(6-level)+node) left 0 right) := by
        unfold ClaudeWCT.WCT9.wctNodeHashH ClaudeWCT.WCT9.wctTopInput
        rw [ClaudeWCT.WCT9.bytesLE_zero16]
      rw [hnode]
      have hpk := highNodeAt_packed coord level node (by omega) hn
      by_cases hh : highNodeAt coord level node
      · rw [decide_eq_true hh] at hpk
        rw [ClaudeWCT.WCT9.ftsHash_of_high hpk]
        simp only [nodeProgram, if_pos hh]
      · rw [decide_eq_false hh] at hpk
        rw [ClaudeWCT.WCT9.ftsHash_of_low hpk]
        simp only [nodeProgram, if_neg hh]


noncomputable def honestInput (answers : Answers) : Pos → HashInput
  | .wctLeaf index coord child => pad64 (wctLeafInputP index coord child
      (pads answers index coord (physical coord child/64)).1 (wctEnds answers index coord child))
  | .wctNode index coord level node =>
      let heap := 2^(6-level)+node
      pad64 (ClaudeWCT.WCT9.wctTopInput coord index heap
        ((nodes answers index coord).getD (2*heap) 0)
        (if level = 4 then (pads answers index coord (heap/2-2)).2 else 0)
        ((nodes answers index coord).getD (2*heap+1) 0))
  | position => Extract.honestInput answers position

/-- Only positions actually constructed by the paired source are charged. -/
def Bounded (position : Pos) : Prop :=
  match position with
  | .forest _ => False
  | .wctNode _ coord level _ => position.Bounded ∧ (first coord = true → level < 5)
  | _ => position.Bounded

theorem Bounded.legacy {position : Pos} (h : Bounded position) : position.Bounded := by
  cases position <;> simp only [Bounded] at h <;> first | exact h | exact h.1

def HashHitAt (answers : Answers) (position : Pos) (honest actual : HashInput) : Prop :=
  actual ≠ honest ∧ proj position (answers (.inl (.inr actual))) =
    proj position (answers (.inl (.inr honest)))

def HitIn (answers : Answers) (queries : List Spec.Domain) : Prop :=
  ∃ position actual, Bounded position ∧ .inl (.inr actual) ∈ queries ∧
    HashHitAt answers position (honestInput answers position) actual ∧
    SameHeader actual (honestInput answers position)

theorem HitIn.mono {answers : Answers} {queries queries' : List Spec.Domain}
    (hit : HitIn answers queries) (hsub : ∀ query ∈ queries, query ∈ queries') :
    HitIn answers queries' := by
  obtain ⟨position, actual, hb, hq, hh, hs⟩ := hit
  exact ⟨position, actual, hb, hsub _ hq, hh, hs⟩

theorem input_eq_of_no_hit {answers : Answers} {queries : List Spec.Domain}
    (hn : ¬HitIn answers queries) (position : Pos) (actual : HashInput)
    (hb : Bounded position) (hq : .inl (.inr actual) ∈ queries)
    (hs : SameHeader actual (honestInput answers position))
    (hout : proj position (answers (.inl (.inr actual))) =
      proj position (answers (.inl (.inr (honestInput answers position))))) :
    actual = honestInput answers position := by
  by_contra he
  exact hn ⟨position, actual, hb, hq, ⟨he,hout⟩, hs⟩

theorem first_even (pair : Nat) (hp : pair < 4) : first (2*pair) = true := by
  simp only [first, decide_eq_true_eq]
  omega

theorem first_odd (pair : Nat) : first (2*pair+1) = false := by
  simp only [first, decide_eq_false_iff_not]
  omega

theorem pads_even (answers : Answers) (index pair branch : Nat) (hp : pair < 4) :
    pads answers index (2*pair) branch = pairPrev answers index pair := by
  simp only [pads, if_neg (show 2*pair ≠ 8 by omega), first_even pair hp, if_true,
    Nat.mul_div_cancel_left pair (by decide : 0<2)]

theorem pads_odd (answers : Answers) (index pair branch : Nat) :
    pads answers index (2*pair+1) branch = SharedForest.nodesPair
      (SharedForest.firstNodes answers index pair (pairPrev answers index pair)) branch := by
  simp only [pads, if_neg (show 2*pair+1 ≠ 8 by omega), first_odd pair, Bool.false_eq_true, if_false]
  rw [show (2*pair+1)/2 = pair by omega]

theorem nodes_even (answers : Answers) (index pair : Nat) (hp : pair < 4) :
    nodes answers index (2*pair) = SharedForest.firstNodes answers index pair (pairPrev answers index pair) := by
  simp only [nodes, if_neg (show 2*pair ≠ 8 by omega), first_even pair hp, if_true,
    Nat.mul_div_cancel_left pair (by decide : 0<2)]

theorem nodes_odd (answers : Answers) (index pair : Nat) :
    nodes answers index (2*pair+1) = SharedForest.secondNodes answers index pair (pairPrev answers index pair) := by
  simp only [nodes, if_neg (show 2*pair+1 ≠ 8 by omega), first_odd pair, Bool.false_eq_true, if_false]
  rw [show (2*pair+1)/2 = pair by omega]

theorem singleton_top (answers : Answers) (index : Nat) :
    ((nodes answers index 8).getD 2 0, (nodes answers index 8).getD 3 0) =
      SharedForest.forestCommitment answers index := by
  rfl

#print axioms input_eq_of_no_hit
end ClaudeWCT.W9.T3M.Extract.Paired
