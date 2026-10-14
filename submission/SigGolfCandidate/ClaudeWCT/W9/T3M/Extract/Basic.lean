import SigGolfCandidate.T3M.Witness.Queries
import SigGolfCandidate.T3M.Extract.Normalize
import SigGolfCandidate.ClaudeWCT.WCT9.Correctness
import SigGolfCandidate.Research.V7Composed198Gate

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
  | .node lay tree level node => pad64 (nodeInputP 3 lay.val tree (2 ^ (height lay - level - 1) + node)
      (treeValue (wotsTree answers lay tree) level (2 * node)) 0
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
  | .node lay tree level nd => nodeTweak 3 lay.val tree (2 ^ (height lay - level - 1) + nd)
  | .forest index => header 15 0 index 0 0
  | .wctChain index coord child t step => WCT9.ftsChainHeader index coord child t step
  | .wctLeaf index coord child => WCT9.ftsLeafHeader index coord child
  | .wctNode index coord level nd => WCT9.wctNodeHeader coord index (2 ^ (7 - level - 1) + nd)
def Pos.Bounded : Pos → Prop
  | .chain _ tree lf i step => tree < 2 ^ 31 ∧ lf < 4096 ∧ i < 64 ∧ step < 8
  | .leaf lay tree lf => lf < 2 ^ height lay ∧ tree * 2 ^ height lay + lf < 2 ^ 32
  | .node lay tree level nd => tree < 2 ^ 32 ∧ level < height lay ∧ (lay = 0 ∨ level + 1 < height lay) ∧
      (lay = 0 → tree = 0) ∧ nd < 2 ^ (height lay - level - 1)
  | .forest index => index < 2 ^ 40
  | .wctChain index coord child t step => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6 ∧ step < 4
  | .wctLeaf index coord child => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128
  | .wctNode index coord level nd => index < 2 ^ 31 ∧ coord < 9 ∧ level < 6 ∧ nd < 2 ^ (7 - level - 1)
/-- The 128-bit half of an output that a position's honest value uses: the high half for the top nodes of an FTS
coordinate (`wctNode` level 5, nested FTS r1-1), the low half everywhere else. -/
def Pos.proj : Pos → HashOutput → Digest
  | .wctNode _ _ level _ => if level = 5 then fun a => a.extractLsb' 128 128 else fun a => a.extractLsb' 0 128
  | _ => fun a => a.extractLsb' 0 128
/-- A hit at a position: a different input whose output agrees with the honest one on the used half. -/
def HashHitAt (answers : Answers) (pos : Pos) (honest actual : HashInput) : Prop :=
  actual ≠ honest ∧ pos.proj (answers (.inl (.inr actual))) = pos.proj (answers (.inl (.inr honest)))
theorem hashHitAt_of_low {answers : Answers} {pos : Pos} {honest actual : HashInput}
    (hp : pos.proj = fun a => a.extractLsb' 0 128) (h : HashHit answers honest actual) :
    HashHitAt answers pos honest actual := by
  unfold HashHitAt; rw [hp]; exact h
def hdrBlock (input : HashInput) : HashInput := (input.drop 16).take 16
def SameHeader (actual honest : HashInput) : Prop :=
  canonicalHeader (hdrBlock actual) = canonicalHeader (hdrBlock honest)
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

def proj : Pos → HashOutput → Digest
  | .wctNode _ coord level _ => if highPosition coord level then
      fun answer => answer.extractLsb' 128 128 else fun answer => answer.extractLsb' 0 128
  | _ => fun answer => answer.extractLsb' 0 128

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
