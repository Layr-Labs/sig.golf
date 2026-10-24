import SigGolfCandidate.T3_SearchCost
import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Pi
import SigGolfCandidate.SphincsSecurity_Proof_Scheme_HashOutputSplit
import SigGolfCandidate.ClaudeWCT_WCT9_Omit
import SigGolfCandidate.ClaudeWCT_WCT9_Cost
import SigGolfCandidate.ClaudeWCT_WCT9_Correctness
import SigGolfCandidate.ClaudeWCT_WCT9_Limits
import SigGolfCandidate.Legacy
import Mathlib.Data.Fintype.Fin
import SigGolfCandidate.ClaudeWCT_WCT9_TopNonce
import Mathlib.Tactic.FinCases
set_option autoImplicit false
namespace SigGolfCandidate.Research.V7Composed198Gate
theorem even_gate (g : Nat) : g / 2 < 1182 ↔ g < 2364 := by omega

theorem gate_shift44_toNat (answer : BitVec 256) :
    (answer.extractLsb' 192 64 >>> 44).toNat =
      (answer.toNat / 2^235 % 2^21) / 2 := by
  rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

theorem gate_ult_shift44 (answer : BitVec 256) :
    BitVec.ult (answer.extractLsb' 192 64 >>> 44) 1182#64 =
      decide (answer.toNat / 2^235 % 2^21 < 2364) := by
  simp only [BitVec.ult, gate_shift44_toNat, show (1182#64 : BitVec 64).toNat = 1182 from rfl,
    even_gate]

/-- T8E gate (14 bits at 242, limit 1353): the top 14 bits of the last 64-bit digest word. -/
theorem gate_shift50_toNat (answer : BitVec 256) :
    (answer.extractLsb' 192 64 >>> 50).toNat = answer.toNat / 2^242 % 2^14 := by
  rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h := BitVec.isLt answer
  omega

theorem gate_ult_shift50 (answer : BitVec 256) :
    BitVec.ult (answer.extractLsb' 192 64 >>> 50) 1353#64 =
      decide (answer.toNat / 2^242 % 2^14 < 1353) := by
  simp only [BitVec.ult, gate_shift50_toNat, show (1353#64 : BitVec 64).toNat = 1353 from rfl]

theorem gate_ult_const (answer : BitVec 256) :
    BitVec.ult (answer.extractLsb' 192 64) 0x1524000000000000#64 =
      decide (answer.toNat / 2^242 % 2^14 < 1353) := by
  rw [← gate_ult_shift50]
  simp only [BitVec.ult, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (0x1524000000000000#64 : BitVec 64).toNat = 1523342573958070272 from rfl,
    show (1353#64 : BitVec 64).toNat = 1353 from rfl, decide_eq_decide]
  omega

end SigGolfCandidate.Research.V7Composed198Gate
/-! Finite layout certificates for the proposed shared-path forest. These definitions
are not connected to the submitted machine image or the scheme parameters. -/
namespace SigGolfCandidate.Research.SharedPathPacking

/-- C1 (FTS Merkle half-swap, stage 1): the fold window bases of child levels `0..4`, in bytes, indexed by the
five low path bits (`plans_merged.json`, the first optimal plan per class of the exhaustive search with the
level-four window pinned at `X = 128`, R pad at 160). -/
def plans : List (List Nat) :=
  [[16,64,208,256,128],
   [0,64,208,256,128],
   [16,192,256,64,128],
   [0,192,256,64,128],
   [16,64,192,256,128],
   [0,64,192,256,128],
   [64,0,192,256,128],
   [0,80,192,256,128],
   [16,64,256,192,128],
   [0,64,256,192,128],
   [16,192,256,80,128],
   [0,192,256,80,128],
   [16,256,192,80,128],
   [0,256,192,80,128],
   [256,192,0,80,128],
   [0,192,272,80,128],
   [16,64,192,240,128],
   [0,64,192,240,128],
   [16,176,240,64,128],
   [256,0,64,192,128],
   [16,64,176,240,128],
   [0,64,176,240,128],
   [64,0,176,240,128],
   [48,0,176,240,128],
   [16,64,240,176,128],
   [0,64,240,176,128],
   [64,0,240,176,128],
   [48,0,240,176,128],
   [64,240,176,0,128],
   [0,64,176,256,128],
   [64,0,176,256,128],
   [0,272,224,176,128]]

def bitAt (j l : Nat) : Nat := j / 2 ^ l % 2
def block (j l : Nat) : Nat := ((plans.getD (j % 32) []).getD l 0)
def current (j l : Nat) : Nat := block j l + 48 * bitAt j l
def sibling (j l : Nat) : Nat := block j l + 48 * (1 - bitAt j l)
def pad (j l : Nat) : Nat := block j l + 32
/-- C1: the high header word `block + 24` stays witness memory on every packed level `0..3` (the verifier writes
only the low header word there); level four writes both header words. -/
def keepsHigh (_j l : Nat) : Bool := decide (l < 4)
/-- C1: the value of level `l` (the leaf for `l = 0`) uses the high half of its hash output on a left input of
levels `0..3` (an even heap `16..255`); the 32-byte answer is then written at `current - 16`, otherwise at
`current`. -/
def highValue (j l : Nat) : Bool := decide (l ≤ 3 ∧ bitAt j l = 0)
def outO (j l : Nat) : Nat := if highValue j l then current j l - 16 else current j l
/-- The eight-byte words written by the time the fold of level `l` reads its window: the 32-byte answer carrying
the level-`l` value, the low header word and, on level four, the high header word. -/
def writes (j l : Nat) : List Nat :=
  [outO j l, outO j l + 8, outO j l + 16, outO j l + 24,
   block j l + 16] ++ (if keepsHigh j l then [] else [block j l + 24])
def priorWrites (j n : Nat) : List Nat := (List.range n).flatMap (writes j)

/-- C1 layout rules. The prior coordinate writes a whole hash answer at 144: its low (junk) half occupies the
level-four header at 144, its high half is the R pad at 160. Every window is 16-aligned inside `[0, 400)`; every
sibling, non-R pad and high header word lies in `[0, 320)` and is still witness memory when its fold reads it; the
R pad survives until the level-four fold; siblings are pairwise distinct and never share a 16-byte granule with a
pad, a high header word or the hand-off granules 144 and 160. -/
def planOK (j : Nat) : Bool :=
  decide (block j 4 = 128) &&
  (List.range 5).all (fun l =>
    decide (block j l % 16 = 0 ∧ block j l + 64 ≤ 400 ∧ sibling j l + 16 ≤ 320 ∧
      (l < 4 → pad j l + 16 ≤ 320 ∧ block j l ≠ 128) ∧ (highValue j l = true → 16 ≤ current j l)) &&
    decide (sibling j l ≠ 144 ∧ sibling j l ≠ 160 ∧
      (l < 4 → pad j l ≠ 144 ∧ pad j l ≠ 160 ∧ block j l + 16 ≠ 144 ∧ block j l + 16 ≠ 160)) &&
    (priorWrites j (l + 1)).all (fun a =>
      decide (a ≠ sibling j l ∧ a ≠ sibling j l + 8 ∧ a ≠ pad j l ∧ a ≠ pad j l + 8)) &&
    (if keepsHigh j l then (priorWrites j (l + 1)).all
      (fun a => decide (a ≠ block j l + 24)) else true)) &&
  (List.range 5).all (fun i => (List.range 5).all (fun l =>
    decide (sibling j i ≠ pad j l ∧ (i ≠ l → sibling j i ≠ sibling j l)) &&
    (if keepsHigh j l then decide (sibling j i ≠ block j l + 16) else true)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem planOK_all : ∀ j : Fin 128, planOK j.val = true := by
  intro j
  fin_cases j <;> decide +kernel

theorem block_four (j : Nat) : block j 4 = 128 := by
  have h : ∀ i, i < 32 → ((plans.getD i []).getD 4 0) = 128 := by decide
  exact h (j % 32) (Nat.mod_lt _ (by decide))

/-- C1: `skips′`, the elided `addi a2` words of a child routine: the levels whose output address equals the
previous one. The final jump to block 832 cannot reuse the output address. -/
def saves (j : Nat) : Nat :=
  ((List.range 4).map fun l => if outO j (l + 1) = outO j l then 1 else 0).sum

/-- The per-class table of `saves` (`2 - saves` is the accounting correction). -/
def savesTable : List Nat :=
  [0,1,1,1,1,2,2,1,1,2,2,2,2,2,2,1,0,1,1,2,1,2,2,1,1,2,2,1,1,1,1,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem saves_table : ∀ j : Fin 128, saves j.val = savesTable.getD (j.val % 32) 0 := by
  intro j; fin_cases j <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem saves_bounds : ∀ j : Fin 128, saves j.val ≤ 2 := by
  intro j; fin_cases j <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem total_saves : ((List.range 32).map saves).sum = 42 := by decide +kernel

end SigGolfCandidate.Research.SharedPathPacking

/-!
Private shared-path construction under development. The executable source
model below is separate from `SigGolf.Challenge.submission`: its machine
refinement and security certificate are not yet installed.

Each pair has two 64-child branches. Both coordinates select the same
branch. The first coordinate supplies a pair of nodes inside that branch;
the second binds those nodes through its leaf and level-four padding and
supplies the outer authentication sibling. This removes one digest per
pair while retaining the original degree-53 private seed families.
-/
namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.WCT9

abbrev PairRoot := Digest × Digest

/-- B tables enumerate physical leaves by rotating the raw child field.
Private seed and chain/leaf addresses retain the original raw child. -/
def rawChild (first : Bool) (physical : Nat) : Nat :=
  if first then physical else 2 * (physical % 64) + physical / 64

def physicalChild (first : Bool) (raw : Nat) : Nat :=
  if first then raw else raw / 2 + 64 * (raw % 2)

theorem physicalChild_lt (first : Bool) (raw : Nat) (h : raw < 128) :
    physicalChild first raw < 128 := by
  cases first <;> simp only [physicalChild, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem raw_physical_child (first : Bool) (raw : Nat) (h : raw < 128) :
    rawChild first (physicalChild first raw) = raw := by
  cases first <;> simp only [rawChild, physicalChild, Bool.false_eq_true, ↓reduceIte] <;> omega

structure Selection where
  branch : Fin 2
  first : Fin 64
  second : Fin 64

def firstChild (s : Selection) : Child :=
  ⟨64 * s.branch.val + s.first.val, by have := s.branch.isLt; have := s.first.isLt; omega⟩

def secondChild (s : Selection) : Child :=
  ⟨64 * s.branch.val + s.second.val, by have := s.branch.isLt; have := s.second.isLt; omega⟩

theorem selected_branch (s : Selection) :
    (firstChild s).val / 64 = (secondChild s).val / 64 := by
  have hb := s.branch.isLt
  have ha := s.first.isLt
  have hc := s.second.isLt
  simp only [firstChild, secondChild]
  omega

structure PairOpening where
  firstValues : Fin 6 → Digest
  firstPath : Fin 6 → Digest
  secondValues : Fin 6 → Digest
  secondPath : Fin 7 → Digest

def nodesPair (nodes : Array Digest) (branch : Nat) : PairRoot :=
  (nodes.getD (4 + 2 * branch) 0, nodes.getD (5 + 2 * branch) 0)

/-- The final singleton writes its top node directly into the layer-three
encoding input: the right top node (heap 3) as the low hash half at `WIT + 48`,
the left top node (heap 2) as the HIGH hash half at `WIT + 0` (stage 2, merged
singleton "Cm": the junk low half lands below the witness, so the C3 row pad at
`WIT + 24` stays witness memory). Paired B coordinates keep the high outer half. -/
def sharedOuterHash (coord index heap : Nat) (left right : Digest) : M Digest :=
  let input := wctTopInput coord index heap left 0 right
  if coord = 8 ∧ heap = 3 then shortHash input else highHash input

/-- Level four carries the preceding right node. An A coordinate uses the
high hash half there; a B coordinate uses the low half and one additional
outer fold. The half choice permits contiguous 32-byte machine writes.
C1 (FTS Merkle half-swap): the packed nodes `8..127` follow `ftsHighHeap`
(`wctNodeHashH`), i.e. the even heaps `16..127` use the high half. -/
def sharedNode (first : Bool) (coord index heap : Nat)
    (pads : Nat → PairRoot) (left right : Digest) : M Digest :=
  if heap < 4 then sharedOuterHash coord index heap left right
  else if heap < 8 then
    let input := wctTopInput coord index heap left (pads (heap / 2 - 2)).2 right
    if first then highHash input else shortHash input
  else wctNodeHashH coord index heap left right

def sharedHeap (first : Bool) (index coord : Nat) (pads : Nat → PairRoot)
    (leaves : List Digest) : M (Array Digest) :=
  (List.range' (if first then 4 else 2) (if first then 124 else 126)).reverse.foldlM
    (fun nodes heap => do
      let value ← sharedNode first coord index heap pads
        (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
      pure (nodes.set! heap value))
    ((List.replicate 128 (0 : Digest) ++ leaves).toArray)

def buildSharedCoordinate (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    M (Array Digest × List Digest) := do
  let coefs ← ftsCoefs index coord
  let state ← (List.range 128).foldlM
    (fun (state : List Digest × List Digest) j => do
      let (root, values) ← buildChildH (128 + j) index coord (rawChild first j) word coefs (pads (j / 64)).1
      pure (state.1 ++ [root], if j = selected.val then values else state.2)) ([], [])
  let nodes ← sharedHeap first index coord pads state.1
  pure (nodes, state.2)

def authAt (nodes : Array Digest) (selected level : Nat) : Digest :=
  nodes.getD (((128 + selected) / 2 ^ level) ^^^ 1) 0

def buildPair (index pair : Nat) (s : Selection) (aWord bWord : Rank)
    (prev : PairRoot) : M (PairOpening × PairRoot) := do
  let a ← buildSharedCoordinate true index (2 * pair) (firstChild s) aWord (fun _ => prev)
  let b ← buildSharedCoordinate false index (2 * pair + 1) (secondChild s) bWord
    (nodesPair a.1)
  pure (⟨fun i => a.2.getD i.val 0, fun i => authAt a.1 (firstChild s).val i.val,
      fun i => b.2.getD i.val 0, fun i => authAt b.1 (secondChild s).val i.val⟩,
    (b.1.getD 2 0, b.1.getD 3 0))

def recoverSharedInner (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest)
    (prev : PairRoot) : M Digest := do
  let ends ← (List.finRange 6).mapM fun i =>
    let deficit := wordDigit word i
    chain index coord (rawChild first selected.val) i.val (4 - deficit) deficit (values i)
  let leaf ← leafHashH (128 + selected.val) index coord (rawChild first selected.val) prev.1 ends
  (List.range 5).foldlM (fun value level => do
    let other := path level
    let lr := if selected.val / 2 ^ level % 2 = 0 then (value, other) else (other, value)
    sharedNode first coord index ((128 + selected.val) / 2 ^ (level + 1))
      (fun _ => prev) lr.1 lr.2) leaf

def recoverPair (index pair : Nat) (s : Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) : M PairRoot := do
  let aChild := firstChild s
  let bChild := secondChild s
  let a ← recoverSharedInner true index (2 * pair) aChild aWord opened.firstValues
    (fun i => opened.firstPath ⟨i % 6, Nat.mod_lt _ (by decide)⟩) prev
  let aPair := if aChild.val / 32 % 2 = 0 then (a, opened.firstPath 5)
    else (opened.firstPath 5, a)
  let b ← recoverSharedInner false index (2 * pair + 1) bChild bWord opened.secondValues
    (fun i => opened.secondPath ⟨i % 7, Nat.mod_lt _ (by decide)⟩) aPair
  let lr := if bChild.val / 32 % 2 = 0 then (b, opened.secondPath 5)
    else (opened.secondPath 5, b)
  let outer ← sharedOuterHash (2 * pair + 1) index (2 + bChild.val / 64) lr.1 lr.2
  pure (if bChild.val / 64 % 2 = 0 then (outer, opened.secondPath 6)
    else (opened.secondPath 6, outer))

def pairOpeningDigests : Nat := 6 + 6 + 6 + 7

theorem pair_saves_one_digest : pairOpeningDigests + 1 = 2 * (6 + 7) := by decide

theorem four_pairs_signature_size : 5310 - 4 * 16 = 5246 := by decide

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def heapCut (first : Bool) : Nat := if first then 4 else 2

def SharedHeapInv (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) (done : Nat) (nodes : Array Digest) : Prop :=
  nodes.size = 256 ∧
    (∀ i, 128 ≤ i → i < 256 → nodes.getD i 0 = leaves.getD (i - 128) 0) ∧
    (∀ i, heapCut first ≤ i → i < 128 → 128 - done ≤ i → nodes.getD i 0 =
      evalWithAnswerFn answers (sharedNode first coord index i pads
        (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0)))

theorem heapCut_bounds (first : Bool) : 2 ≤ heapCut first ∧ heapCut first ≤ 4 := by
  cases first <;> decide

theorem shared_heap_order (first : Bool) (i : Nat) (hi : i < 128 - heapCut first) :
    ((List.range' (heapCut first) (128 - heapCut first)).reverse)[i]'(by simpa using hi) = 127 - i := by
  rw [List.getElem_reverse]
  simp only [List.length_range', List.getElem_range', Nat.one_mul]
  have := heapCut_bounds first
  omega

theorem shared_heap_initial (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) (hlen : leaves.length = 128) :
    SharedHeapInv answers first index coord pads leaves 0
      ((List.replicate 128 (0 : Digest) ++ leaves).toArray) := by
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro i hlo hhi
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      ← List.getD_eq_getElem?_getD]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
    simp only [List.length_replicate]
  · intro i _ hi hlo
    omega

theorem shared_heap_step (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) (done : Nat)
    (hdone : done < 128 - heapCut first) (nodes : Array Digest)
    (hinv : SharedHeapInv answers first index coord pads leaves done nodes) :
    SharedHeapInv answers first index coord pads leaves (done + 1)
      (nodes.set! (127 - done) (evalWithAnswerFn answers
        (sharedNode first coord index (127 - done) pads
          (nodes.getD (2 * (127 - done)) 0) (nodes.getD (2 * (127 - done) + 1) 0)))) := by
  let heap := 127 - done
  let v := evalWithAnswerFn answers (sharedNode first coord index heap pads
    (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0))
  change SharedHeapInv answers first index coord pads leaves (done + 1) (nodes.set! heap v)
  rcases hinv with ⟨hsize, hleaf, hnode⟩
  have hc := heapCut_bounds first
  have hh : heapCut first ≤ heap ∧ heap < 128 := by dsimp only [heap]; omega
  refine ⟨by rw [Array.size_set!, hsize], ?_, ?_⟩
  · intro i hlo hhi
    rw [getD_set_other nodes heap i v (by omega)]
    exact hleaf i hlo hhi
  · intro i hlo hhi hdone'
    have hheap : heap ≤ i := by dsimp only [heap]; omega
    have hl : (nodes.set! heap v).getD (2 * i) 0 = nodes.getD (2 * i) 0 :=
      getD_set_other nodes heap (2 * i) v (by omega)
    have hr : (nodes.set! heap v).getD (2 * i + 1) 0 = nodes.getD (2 * i + 1) 0 :=
      getD_set_other nodes heap (2 * i + 1) v (by omega)
    rw [hl, hr]
    by_cases he : i = heap
    · subst i
      rw [getD_set_self nodes heap v (by omega)]
    · rw [getD_set_other nodes heap i v (Ne.symm he)]
      exact hnode i hlo hhi (by dsimp only [heap] at he hheap; omega)

theorem shared_heap_complete (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) (hlen : leaves.length = 128) :
    SharedHeapInv answers first index coord pads leaves (128 - heapCut first)
      (evalWithAnswerFn answers (sharedHeap first index coord pads leaves)) := by
  have he : sharedHeap first index coord pads leaves =
      (List.range' (heapCut first) (128 - heapCut first)).reverse.foldlM
        (fun nodes heap => do
          let value ← sharedNode first coord index heap pads
            (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
          pure (nodes.set! heap value))
        ((List.replicate 128 (0 : Digest) ++ leaves).toArray) := by
    cases first <;> rfl
  rw [he]
  have h := eval_foldlM_list_inv answers (List.range' (heapCut first) (128 - heapCut first)).reverse
    (fun nodes heap => do
      let value ← sharedNode first coord index heap pads
        (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
      pure (nodes.set! heap value))
    (SharedHeapInv answers first index coord pads leaves) _
    (shared_heap_initial answers first index coord pads leaves hlen) (by
      intro done hdone nodes hinv
      have hd : done < 128 - heapCut first := by
        simpa only [List.length_reverse, List.length_range'] using hdone
      rw [shared_heap_order first done hd]
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      exact shared_heap_step answers first index coord pads leaves done hd nodes hinv)
  simpa only [List.length_reverse, List.length_range'] using h

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9

structure SingletonOpening where
  values : Fin 6 → Digest
  path : Fin 7 → Digest

structure ForestSelection where
  pairs : Fin 4 → Selection
  singleton : Child

structure ForestWords where
  first : Fin 4 → Rank
  second : Fin 4 → Rank
  singleton : Rank

structure ForestOpening where
  pairs : Fin 4 → PairOpening
  singleton : SingletonOpening

structure Signature where
  rho : Digest
  policyHints : BitVec 16
  forest : ForestOpening
  layers : (lay : Layer) → LayerSignature lay

/-- `topHigh`: the restricted top choice hint (witness byte rel 22312, bit 4): the verifier reads the HIGH half of
the top encoding answer when it is set and LOW is not forced. Honest value: the producer chose HIGH. -/
structure Witness where
  signature : Signature
  digestCounter : BitVec 32
  counters : Layer → BitVec 32
  topHigh : Bool
  /-- Top-bytes layer: the re-derived nonces of the top path nodes of heights 1..11 (witness pads). -/
  topNonces : List Nat

def emptyPairOpening : PairOpening := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- The last singleton uses the B node layout, including its level-four pad. -/
def buildSingleton (index : Nat) (selected : Child) (word : Rank) (prev : PairRoot) :
    M (SingletonOpening × PairRoot) := do
  let built ← buildSharedCoordinate false index 8 selected word (fun _ => prev)
  pure (⟨fun i => built.2.getD i.val 0, fun i => authAt built.1 selected.val i.val⟩,
    (built.1.getD 2 0, built.1.getD 3 0))

def recoverSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) : M PairRoot := do
  let inner ← recoverSharedInner false index 8 selected word opened.values
    (fun i => opened.path ⟨i % 7, Nat.mod_lt _ (by decide)⟩) prev
  let lr := if selected.val / 32 % 2 = 0 then (inner, opened.path 5)
    else (opened.path 5, inner)
  let outer ← sharedOuterHash 8 index (2 + selected.val / 64) lr.1 lr.2
  pure (if selected.val / 64 % 2 = 0 then (outer, opened.path 6)
    else (opened.path 6, outer))

def buildForest (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    M (ForestOpening × PairRoot) := do
  let state ← (List.finRange 4).foldlM
    (fun (state : List PairOpening × PairRoot) pair => do
      let built ← buildPair index pair.val (selected.pairs pair)
        (words.first pair) (words.second pair) state.2
      pure (state.1 ++ [built.1], built.2)) ([], ftsStart)
  let last ← buildSingleton index selected.singleton words.singleton state.2
  pure (⟨fun pair => state.1.getD pair.val emptyPairOpening, last.1⟩, last.2)

def recoverForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) : M PairRoot := do
  let prev ← (List.finRange 4).foldlM
    (fun prev pair => recoverPair index pair.val (selected.pairs pair)
      (words.first pair) (words.second pair) (opened.pairs pair) prev) ftsStart
  recoverSingleton index selected.singleton words.singleton opened.singleton prev

/-- Physical B children rotate the raw seven-bit field right by one: the
shared low bit becomes the branch bit, and the next six bits select within it. -/
def selectionFromOutput (output : HashOutput) (pair : Fin 4) : Selection where
  branch := ⟨output.toNat / 2 ^ (64 * pair.val + 6) % 2, Nat.mod_lt _ (by decide)⟩
  first := ⟨output.toNat / 2 ^ (64 * pair.val) % 64, Nat.mod_lt _ (by decide)⟩
  second := ⟨output.toNat / 2 ^ (64 * pair.val + 7) % 64, Nat.mod_lt _ (by decide)⟩

def forestSelectionFromOutput (output : HashOutput) : ForestSelection where
  pairs := selectionFromOutput output
  singleton := ⟨physicalChild false (output.toNat / 2 ^ 229 % 128),
    physicalChild_lt false _ (Nat.mod_lt _ (by decide))⟩

def rankBase (coord : Nat) : Nat := [13, 77, 89, 101, 141, 153, 165, 205, 217].getD coord 0

def rawForestRank (output : HashOutput) (coord : Nat) : Nat :=
  output.toNat / 2 ^ rankBase coord % 1024

/-- Total decoder; the digest acceptance condition separately requires each
raw rank to be below563, in which case this reduction leaves it unchanged. -/
def forestRank (output : HashOutput) (coord : Nat) : Rank :=
  ⟨rawForestRank output coord % 563, Nat.mod_lt _ (by decide)⟩

def forestWordsFromOutput (output : HashOutput) : ForestWords where
  first := fun pair => forestRank output (2 * pair.val)
  second := fun pair => forestRank output (2 * pair.val + 1)
  singleton := forestRank output 8

def forestOpeningDigests : Nat := 4 * pairOpeningDigests + (6 + 7)

theorem forest_opening_size : forestOpeningDigests = 113 := by decide

theorem forest_digest_saving : forestOpeningDigests + 4 = 9 * (6 + 7) := by decide

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def sharedLeaves (answers : Answers) (first : Bool) (index coord : Nat) (pads : Nat → PairRoot) : List Digest :=
  List.ofFn (fun j : Fin 128 =>
    childRootH answers (128 + j.val) index coord (rawChild first j.val) (pads (j.val / 64)).1)

def sharedNodes (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) : Array Digest :=
  evalWithAnswerFn answers (sharedHeap first index coord pads (sharedLeaves answers first index coord pads))

def sharedRows (first : Bool) (index coord : Nat) (selected : Child) (word : Rank)
    (coefs : List Digest) (pads : Nat → PairRoot) : M (List Digest × List Digest) :=
  (List.range 128).foldlM (fun (state : List Digest × List Digest) j => do
    let (root, values) ← buildChildH (128 + j) index coord (rawChild first j) word coefs (pads (j / 64)).1
    pure (state.1 ++ [root], if j = selected.val then values else state.2)) ([], [])

def SharedRows (answers : Answers) (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (pads : Nat → PairRoot) (done : Nat) (rows : List Digest × List Digest) : Prop :=
  rows.1.length = done ∧
    (∀ j, j < done → rows.1.getD j 0 =
      childRootH answers (128 + j) index coord (rawChild first j) (pads (j / 64)).1) ∧
    rows.2 = (if selected.val < done then
      List.ofFn (fun i : Fin 6 => chainValue answers index coord (rawChild first selected.val) word i) else [])

theorem shared_rows_step (answers : Answers) (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (pads : Nat → PairRoot) (done : Nat) (rows : List Digest × List Digest)
    (hrows : SharedRows answers first index coord selected word pads done rows) :
    SharedRows answers first index coord selected word pads (done + 1)
      (rows.1 ++ [childRootH answers (128 + done) index coord (rawChild first done) (pads (done / 64)).1],
       if done = selected.val then
         List.ofFn (fun i : Fin 6 => chainValue answers index coord (rawChild first done) word i) else rows.2) := by
  rcases hrows with ⟨hlen, hroot, hvalues⟩
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro j hj
    rw [ClaudeWCT.WCT9.getD_append_singleton, hlen]
    by_cases hjd : j < done
    · rw [if_pos hjd]; exact hroot j hjd
    · have he : j = done := by omega
      subst j
      simp
  · by_cases hs : done = selected.val
    · subst hs; simp
    · have hs' : selected.val < done + 1 ↔ selected.val < done := by omega
      simp only [if_neg hs, hvalues, hs']

theorem eval_sharedRows (answers : Answers) (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (pads : Nat → PairRoot) :
    SharedRows answers first index coord selected word pads 128
      (evalWithAnswerFn answers (sharedRows first index coord selected word
        (List.ofFn (ftsCoef answers index coord)) pads)) := by
  unfold sharedRows
  refine eval_foldlM_range_inv answers 128 _ (SharedRows answers first index coord selected word pads)
    ([], []) ?_ ?_
  · simp [SharedRows]
  · intro done _ rows hrows
    simp only [evalWithAnswerFn_bind, buildChildH_result, evalWithAnswerFn_pure]
    exact shared_rows_step answers first index coord selected word pads done rows hrows

theorem buildSharedCoordinate_result (answers : Answers) (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    evalWithAnswerFn answers (buildSharedCoordinate first index coord selected word pads) =
      (sharedNodes answers first index coord pads,
       List.ofFn (fun i : Fin 6 => chainValue answers index coord (rawChild first selected.val) word i)) := by
  let rows := evalWithAnswerFn answers (sharedRows first index coord selected word
    (List.ofFn (ftsCoef answers index coord)) pads)
  have hr : SharedRows answers first index coord selected word pads 128 rows :=
    eval_sharedRows answers first index coord selected word pads
  rcases hr with ⟨hlen, hroot, hvalues⟩
  have hroots : rows.1 = sharedLeaves answers first index coord pads := by
    apply List.ext_getElem (by simpa only [sharedLeaves, List.length_ofFn] using hlen)
    intro j hj hk
    simpa only [sharedLeaves, List.getD_eq_getElem _ _ hj, List.getElem_ofFn] using
      hroot j (by omega)
  rw [if_pos selected.isLt] at hvalues
  unfold buildSharedCoordinate
  rw [evalWithAnswerFn_bind, eval_ftsCoefs]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (evalWithAnswerFn answers (sharedHeap first index coord pads rows.1), rows.2) = _
  rw [hroots, hvalues]
  rfl

theorem sharedNodes_graph (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) :
    SharedHeapInv answers first index coord pads (sharedLeaves answers first index coord pads)
      (128 - heapCut first) (sharedNodes answers first index coord pads) :=
  shared_heap_complete answers first index coord pads _ (by simp [sharedLeaves])

/-- All five inner steps stay in the selected64-leaf branch, so replacing
branch pads by the selected branch's pair preserves their hash inputs. -/
theorem sharedNode_selected_pad (first : Bool) (index coord selected level : Nat)
    (hselected : selected < 128) (hlevel : level < 5) (pads : Nat → PairRoot)
    (left right : Digest) :
    sharedNode first coord index ((128 + selected) / 2 ^ (level + 1))
      (fun _ => pads (selected / 64)) left right =
    sharedNode first coord index ((128 + selected) / 2 ^ (level + 1)) pads left right := by
  have hlo : 4 ≤ (128 + selected) / 2 ^ (level + 1) := by
    interval_cases level <;> norm_num <;> omega
  have hbranch : (128 + selected) / 2 ^ (level + 1) < 8 →
      (128 + selected) / 2 ^ (level + 1) / 2 - 2 = selected / 64 := by
    interval_cases level <;> norm_num <;> omega
  have hnot : ¬ (128 + selected) / 2 ^ (level + 1) < 4 := by omega
  simp only [sharedNode, if_neg hnot]
  by_cases hh : (128 + selected) / 2 ^ (level + 1) < 8
  · simp only [if_pos hh, hbranch hh]
  · simp only [if_neg hh]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem heap_path_pair (f : Nat → Digest) (selected level : Nat)
    (hselected : selected < 128) (hlevel : level < 5) :
    (if selected / 2 ^ level % 2 = 0 then
      (f ((128 + selected) / 2 ^ level), f (((128 + selected) / 2 ^ level) ^^^ 1))
    else (f (((128 + selected) / 2 ^ level) ^^^ 1), f ((128 + selected) / 2 ^ level))) =
      (f (2 * ((128 + selected) / 2 ^ (level + 1))),
       f (2 * ((128 + selected) / 2 ^ (level + 1)) + 1)) := by
  have hp : selected / 2 ^ level % 2 = (128 + selected) / 2 ^ level % 2 := by
    interval_cases level <;> norm_num <;> omega
  rw [hp, sibling_pair f ((128 + selected) / 2 ^ level)]
  have hd : (128 + selected) / 2 ^ level / 2 = (128 + selected) / 2 ^ (level + 1) := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [hd]

theorem recoverSharedInner_honest (answers : Answers) (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot)
    (values : Fin 6 → Digest) (path : Nat → Digest)
    (hvalues : ∀ i, values i = chainValue answers index coord (rawChild first selected.val) word i)
    (hpath : ∀ level, level < 5 → path level =
      authAt (sharedNodes answers first index coord pads) selected.val level) :
    evalWithAnswerFn answers (recoverSharedInner first index coord selected word values path
      (pads (selected.val / 64))) =
      (sharedNodes answers first index coord pads).getD ((128 + selected.val) / 32) 0 := by
  let nodes := sharedNodes answers first index coord pads
  have hg := sharedNodes_graph answers first index coord pads
  have hends : (List.finRange 6).map (fun i => evalWithAnswerFn answers
      (chain index coord (rawChild first selected.val) i.val
        (4 - wordDigit word i) (wordDigit word i) (values i))) =
      List.ofFn (fun i : Fin 6 => chainEnd answers index coord (rawChild first selected.val) i) := by
    simp_rw [hvalues, value_completes]
    exact List.ofFn_eq_map.symm
  have hleaf : evalWithAnswerFn answers
      (leafHashH (128 + selected.val) index coord (rawChild first selected.val) (pads (selected.val / 64)).1
        (List.ofFn (fun i : Fin 6 => chainEnd answers index coord (rawChild first selected.val) i))) =
      nodes.getD (128 + selected.val) 0 := by
    have hl := hg.2.1 (128 + selected.val) (by omega) (by have := selected.isLt; omega)
    rw [Nat.add_sub_cancel_left, sharedLeaves,
      List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact selected.isLt), List.getElem_ofFn] at hl
    exact hl.symm
  have hwalk := eval_foldlM_range_inv answers 5
    (fun value level => do
      let other := path level
      let lr := if selected.val / 2 ^ level % 2 = 0 then (value, other) else (other, value)
      sharedNode first coord index ((128 + selected.val) / 2 ^ (level + 1))
        (fun _ => pads (selected.val / 64)) lr.1 lr.2)
    (fun done value => value = nodes.getD ((128 + selected.val) / 2 ^ done) 0)
    (nodes.getD (128 + selected.val) 0) (by simp) (by
      intro level hlevel value hv
      have hb : 4 ≤ (128 + selected.val) / 2 ^ (level + 1) ∧
          (128 + selected.val) / 2 ^ (level + 1) < 128 := by
        have hs := selected.isLt
        interval_cases level <;> norm_num <;> omega
      change evalWithAnswerFn answers (sharedNode first coord index
        ((128 + selected.val) / 2 ^ (level + 1)) (fun _ => pads (selected.val / 64))
        (if selected.val / 2 ^ level % 2 = 0 then (value, path level) else (path level, value)).1
        (if selected.val / 2 ^ level % 2 = 0 then (value, path level) else (path level, value)).2) = _
      rw [hv, hpath level hlevel]
      unfold authAt
      rw [heap_path_pair (fun j => nodes.getD j 0) selected.val level selected.isLt hlevel,
        sharedNode_selected_pad first index coord selected.val level selected.isLt hlevel]
      have hc := heapCut_bounds first
      exact (hg.2.2 ((128 + selected.val) / 2 ^ (level + 1)) (by omega) hb.2 (by omega)).symm)
  unfold recoverSharedInner
  simp only [evalWithAnswerFn_bind, eval_mapM, evalWithAnswerFn_pure]
  rw [hends, hleaf]
  exact hwalk

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem ordered_branch_pair (nodes : Array Digest) (selected : Nat) (hs : selected < 128) :
    (if selected / 32 % 2 = 0 then
      (nodes.getD ((128 + selected) / 32) 0, authAt nodes selected 5)
    else (authAt nodes selected 5, nodes.getD ((128 + selected) / 32) 0)) =
      nodesPair nodes (selected / 64) := by
  have hp : selected / 32 % 2 = (128 + selected) / 32 % 2 := by omega
  unfold authAt nodesPair
  norm_num only [Nat.reducePow]
  rw [hp, sibling_pair (fun j => nodes.getD j 0) ((128 + selected) / 32)]
  have hd : (128 + selected) / 32 / 2 = 2 + selected / 64 := by omega
  rw [hd]
  congr 1 <;> congr 1 <;> omega

theorem ordered_top_pair (nodes : Array Digest) (selected : Nat) (hs : selected < 128) :
    (if selected / 64 % 2 = 0 then
      (nodes.getD (2 + selected / 64) 0, authAt nodes selected 6)
    else (authAt nodes selected 6, nodes.getD (2 + selected / 64) 0)) =
      (nodes.getD 2 0, nodes.getD 3 0) := by
  have hq : selected / 64 = 0 ∨ selected / 64 = 1 := by omega
  have hd : (128 + selected) / 64 = 2 + selected / 64 := by omega
  unfold authAt
  norm_num only [Nat.reducePow]
  rw [hd]
  rcases hq with h | h <;> rw [h] <;> rfl

def recoverSharedOuter (index coord : Nat) (selected : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) : M PairRoot := do
  let inner ← recoverSharedInner false index coord selected word values path prev
  let lr := if selected.val / 32 % 2 = 0 then (inner, path 5) else (path 5, inner)
  let outer ← sharedOuterHash coord index (2 + selected.val / 64) lr.1 lr.2
  pure (if selected.val / 64 % 2 = 0 then (outer, path 6) else (path 6, outer))

theorem recoverSharedOuter_honest (answers : Answers) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot)
    (values : Fin 6 → Digest) (path : Nat → Digest)
    (hvalues : ∀ i, values i = chainValue answers index coord (rawChild false selected.val) word i)
    (hpath : ∀ level, level < 7 → path level =
      authAt (sharedNodes answers false index coord pads) selected.val level) :
    evalWithAnswerFn answers (recoverSharedOuter index coord selected word values path
      (pads (selected.val / 64))) =
      ((sharedNodes answers false index coord pads).getD 2 0,
       (sharedNodes answers false index coord pads).getD 3 0) := by
  let nodes := sharedNodes answers false index coord pads
  have hs := selected.isLt
  have hi := recoverSharedInner_honest answers false index coord selected word pads values path
    hvalues (fun level hlevel => hpath level (by omega))
  have hg := sharedNodes_graph answers false index coord pads
  have hn := hg.2.2 (2 + selected.val / 64) (by simp [heapCut]) (by omega) (by simp [heapCut])
  have hh : 2 + selected.val / 64 < 4 := by omega
  have hm : 2 * (2 + selected.val / 64) = 4 + 2 * (selected.val / 64) := by omega
  simp only [sharedNode, if_pos hh, hm] at hn
  have hm' : 4 + 2 * (selected.val / 64) + 1 = 5 + 2 * (selected.val / 64) := by omega
  rw [hm'] at hn
  unfold recoverSharedOuter
  rw [evalWithAnswerFn_bind, hi]
  rw [hpath 5 (by decide), ordered_branch_pair nodes selected.val hs]
  simp only [nodesPair]
  rw [evalWithAnswerFn_bind, ← hn]
  simp only [evalWithAnswerFn_pure]
  rw [hpath 6 (by decide), ordered_top_pair nodes selected.val hs]

theorem recoverSingleton_eq_outer (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) :
    recoverSingleton index selected word opened prev =
      recoverSharedOuter index 8 selected word opened.values
        (fun i => opened.path ⟨i % 7, Nat.mod_lt _ (by decide)⟩) prev := rfl

theorem recoverSingleton_honest (answers : Answers) (index : Nat) (selected : Child)
    (word : Rank) (prev : PairRoot) :
    let built := evalWithAnswerFn answers (buildSingleton index selected word prev)
    evalWithAnswerFn answers (recoverSingleton index selected word built.1 prev) = built.2 := by
  unfold buildSingleton
  simp only [evalWithAnswerFn_bind, buildSharedCoordinate_result, evalWithAnswerFn_pure]
  rw [recoverSingleton_eq_outer]
  apply recoverSharedOuter_honest answers index 8 selected word (fun _ => prev)
  · intro i
    change (List.ofFn _).getD i.val 0 = _
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  · intro level hl
    simp only [Nat.mod_eq_of_lt hl]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def firstNodes (answers : Answers) (index pair : Nat) (prev : PairRoot) : Array Digest :=
  sharedNodes answers true index (2 * pair) (fun _ => prev)

def secondNodes (answers : Answers) (index pair : Nat) (prev : PairRoot) : Array Digest :=
  sharedNodes answers false index (2 * pair + 1) (nodesPair (firstNodes answers index pair prev))

def expectedPairOpening (answers : Answers) (index pair : Nat) (s : Selection)
    (aWord bWord : Rank) (prev : PairRoot) : PairOpening where
  firstValues := fun i => (List.ofFn (fun j : Fin 6 =>
    chainValue answers index (2 * pair) (rawChild true (firstChild s).val) aWord j)).getD i.val 0
  firstPath := fun i => authAt (firstNodes answers index pair prev) (firstChild s).val i.val
  secondValues := fun i => (List.ofFn (fun j : Fin 6 =>
    chainValue answers index (2 * pair + 1) (rawChild false (secondChild s).val) bWord j)).getD i.val 0
  secondPath := fun i => authAt (secondNodes answers index pair prev) (secondChild s).val i.val

def expectedPairRoot (answers : Answers) (index pair : Nat) (prev : PairRoot) : PairRoot :=
  ((secondNodes answers index pair prev).getD 2 0, (secondNodes answers index pair prev).getD 3 0)

attribute [local irreducible] sharedNodes

theorem buildPair_result (answers : Answers) (index pair : Nat) (s : Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    evalWithAnswerFn answers (buildPair index pair s aWord bWord prev) =
      (expectedPairOpening answers index pair s aWord bWord prev,
       expectedPairRoot answers index pair prev) := by
  simp only [buildPair, evalWithAnswerFn_bind, buildSharedCoordinate_result, evalWithAnswerFn_pure]
  rfl

theorem recoverPair_expected (answers : Answers) (index pair : Nat) (s : Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    evalWithAnswerFn answers (recoverPair index pair s aWord bWord
      (expectedPairOpening answers index pair s aWord bWord prev) prev) =
      expectedPairRoot answers index pair prev := by
  let a := firstNodes answers index pair prev
  let b := secondNodes answers index pair prev
  let opened := expectedPairOpening answers index pair s aWord bWord prev
  have ha := recoverSharedInner_honest answers true index (2 * pair) (firstChild s) aWord
    (fun _ => prev) opened.firstValues
    (fun i => opened.firstPath ⟨i % 6, Nat.mod_lt _ (by decide)⟩)
    (by
      intro i
      change (List.ofFn _).getD i.val 0 = _
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn])
    (by
      intro level hl
      dsimp only [opened, expectedPairOpening, firstNodes]
      rw [Nat.mod_eq_of_lt (by omega)]
      )
  unfold recoverPair
  rw [evalWithAnswerFn_bind, ha]
  change evalWithAnswerFn answers
    (recoverSharedOuter index (2 * pair + 1) (secondChild s) bWord opened.secondValues
      (fun i => opened.secondPath ⟨i % 7, Nat.mod_lt _ (by decide)⟩)
      (if (firstChild s).val / 32 % 2 = 0 then
        (a.getD ((128 + (firstChild s).val) / 32) 0, authAt a (firstChild s).val 5)
      else (authAt a (firstChild s).val 5, a.getD ((128 + (firstChild s).val) / 32) 0))) = _
  rw [ordered_branch_pair a (firstChild s).val (firstChild s).isLt, selected_branch s]
  apply recoverSharedOuter_honest answers index (2 * pair + 1) (secondChild s) bWord (nodesPair a)
  · intro i
    change (List.ofFn _).getD i.val 0 = _
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  · intro level hl
    dsimp only [opened, expectedPairOpening, secondNodes, firstNodes]
    rw [Nat.mod_eq_of_lt hl]
    rfl

theorem recoverPair_honest (answers : Answers) (index pair : Nat) (s : Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    let built := evalWithAnswerFn answers (buildPair index pair s aWord bWord prev)
    evalWithAnswerFn answers (recoverPair index pair s aWord bWord built.1 prev) = built.2 := by
  rw [buildPair_result]
  exact recoverPair_expected answers index pair s aWord bWord prev

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] sharedNodes

/-- The complete four-pair forest and its final B singleton recover the
builder's final commitment under every fixed oracle answer function. -/
theorem recoverForest_honest (answers : Answers) (index : Nat)
    (selected : ForestSelection) (words : ForestWords) :
    let built := evalWithAnswerFn answers (buildForest index selected words)
    evalWithAnswerFn answers (recoverForest index selected words built.1) = built.2 := by
  have hfour : List.finRange 4 = [0, 1, 2, 3] := by decide
  have hv0 : (0 : Fin 4).val = 0 := rfl
  have hv1 : (1 : Fin 4).val = 1 := rfl
  have hv2 : (2 : Fin 4).val = 2 := rfl
  have hv3 : (3 : Fin 4).val = 3 := rfl
  let r0 := expectedPairRoot answers index 0 ftsStart
  let r1 := expectedPairRoot answers index 1 r0
  let r2 := expectedPairRoot answers index 2 r1
  let r3 := expectedPairRoot answers index 3 r2
  simp only [buildForest, hfour, List.foldlM_cons, List.foldlM_nil,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, buildPair_result]
  simp only [recoverForest, hfour, List.foldlM_cons, List.foldlM_nil,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  simp only [hv0, hv1, hv2, hv3, List.nil_append, List.append_assoc, List.cons_append, List.getD_cons_zero,
    List.getD_cons_succ, recoverPair_expected]
  exact recoverSingleton_honest answers index selected.singleton words.singleton r3


end SigGolfCandidate.Research.SharedForest

/-! Private roots-first canonical producer. Retained chain prefixes let the
ancestor-only search choose digits after every lower root has been fixed. -/
namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9

/-- Retain each prefix while evaluating a WOTS chain once, in its ordinary order. Stage 2 (C3, #866): each step
keeps the half `chainHigh lay i start` of its output, as `WCT9.chainW` does (the last step of chain 0 of a lower
layer keeps the HIGH half). -/
def chainPrefixes (lay : Layer) (tree leaf i start : Nat) :
    Nat → Digest → M (List Digest)
  | 0, value => pure [value]
  | count + 1, value => do
      let next ← halfHash (chainHigh lay i start) (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value)
      let tail ← chainPrefixes lay tree leaf i (start + 1) count next
      pure (value :: tail)

def buildLeafPrefixes (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    M ((Digest × List (List Digest)) × List Digest) := do
  let (coefs, carry) ← lowerCoefs lay tree leaf carry
  let prefixes ← (List.range (chainCount lay)).mapM fun i =>
    chainPrefixes lay tree leaf i 0 (maxDigit lay i) (lowerFamilySeed coefs lay leaf i)
  let root ← lowerLeafHash lay tree leaf
    ((List.range (chainCount lay)).map fun i =>
      (prefixes.getD i []).getD (maxDigit lay i) 0)
  pure ((root, prefixes), carry)

structure PreparedLower where
  levels : List (List Digest)
  prefixes : List (List Digest)

/-- Only the selected leaf retains its prefixes; every other leaf uses the
existing full-chain builder. No chain is evaluated again after digit search. -/
def buildTreePrefixes (lay : Layer) (tree selected : Nat) : M PreparedLower := do
  let state ← (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List (List Digest) × List Digest) leaf => do
      let ((root, prefixes), carry) ←
        if leaf = selected then buildLeafPrefixes lay tree leaf state.2.2
        else do
          let ((root, _), carry) ← buildLeafPF lay tree leaf [] state.2.2
          pure ((root, []), carry)
      pure (state.1 ++ [root], if leaf = selected then prefixes else state.2.1, carry))
    ([], [], [])
  let levels ← buildLevelsBelow 3 lay.val tree (height lay) state.1
  pure ⟨levels, state.2.1⟩

def preparedPieces (lay : Layer) (leaf : Nat) (prepared : PreparedLower)
    (digits : List Nat) : Pieces :=
  ((List.range (chainCount lay)).map fun i =>
      (prepared.prefixes.getD i []).getD (digits.getD i 0) 0,
   (List.range (height lay)).map fun level =>
      (prepared.levels.getD level []).getD (leaf / 2 ^ level ^^^ 1) 0)

structure PreparedRoots where
  one : PreparedLower
  two : PreparedLower
  three : PreparedLower

def prepareRoots (index : Nat) : M PreparedRoots := do
  let one ← buildTreePrefixes 1 (route index 1).2 (route index 1).1
  let two ← buildTreePrefixes 2 (route index 2).2 (route index 2).1
  let three ← buildTreePrefixes 3 (route index 3).2 (route index 3).1
  pure ⟨one, two, three⟩

structure CanonicalLayers where
  pieces : List Pieces
  counters : List (BitVec 32)
  digits : List (List Nat)
  /-- The selected half of every layer (`true` = LOW). -/
  lows : List Bool
  residual : Nat
  policyHints : BitVec 16

/-- All thresholds are determined by the canonical ancestors. The lower
tree roots are already fixed, and lower reveals are pure prefix lookups. -/
def searchPreparedLayers (cache : SigGolfCandidate.T3.Cache) (index : Nat) (prepared : PreparedRoots)
    (forest : PairRoot) : M (Option CanonicalLayers) := do
  let pair0 := topPair 1 prepared.one.levels
  let pair1 := topPair 2 prepared.two.levels
  let pair2 := topPair 3 prepared.three.levels
  let some (counter0, digits0, low0) ← CanonicalPolicy.layerCounterSearchAt 0
    (CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit)
    (route index 0).2 (route index 0).1 (.pair pair0.1 pair0.2) 0 (searchLimit 0)
    | pure none
  let residual1 := CanonicalPolicy.nextResidual CanonicalPolicy.totalCredit 0 low0 digits0
  let floor1 := CanonicalPolicy.threshold 1 residual1
  if floor1 ≥ 16 then return none
  let some (counter1, digits1, low1) ← CanonicalPolicy.layerCounterSearchAt 1
    floor1
    (route index 1).2 (route index 1).1 (.pair pair1.1 pair1.2) 0 (searchLimit 1)
    | pure none
  let residual2 := CanonicalPolicy.nextResidual residual1 1 low1 digits1
  let floor2 := CanonicalPolicy.threshold 2 residual2
  if floor2 ≥ 22 then return none
  let some (counter2, digits2, low2) ← CanonicalPolicy.layerCounterSearchAt 2
    floor2
    (route index 2).2 (route index 2).1 (.pair pair2.1 pair2.2) 0 (searchLimit 2)
    | pure none
  let residual3 := CanonicalPolicy.nextResidual residual2 2 low2 digits2
  let floor3 := CanonicalPolicy.threshold 3 residual3
  if floor3 ≥ 22 then return none
  let some (counter3, digits3, low3) ← CanonicalPolicy.layerCounterSearchAt 3
    floor3
    (route index 3).2 (route index 3).1 (.pair forest.1 forest.2) 0 (searchLimit 3)
    | pure none
  let top ← signTop cache (route index 0).1 digits0
  pure (some ⟨[top,
      preparedPieces 1 (route index 1).1 prepared.one digits1,
      preparedPieces 2 (route index 2).1 prepared.two digits2,
      preparedPieces 3 (route index 3).1 prepared.three digits3],
    [counter0, counter1, counter2, counter3], [digits0, digits1, digits2, digits3],
    [low0, low1, low2, low3],
    CanonicalPolicy.nextResidual residual3 3 low3 digits3,
    BitVec.ofNat 16 (484 * floor1 + 22 * floor2 + floor3)⟩)

/-- Source signing continuation after the FTS digest search has selected an
output. The enclosing producer supplies the accepted output and its counter. -/
def signFromOutput (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (digestCounter : BitVec 32)
    (output : HashOutput) : M (Option Witness) := do
  let index := digestIndex output
  let forest ← buildForest index (forestSelectionFromOutput output) (forestWordsFromOutput output)
  let prepared ← prepareRoots index
  let some layers ← searchPreparedLayers cache index prepared forest.2 | pure none
  let signature : Signature := ⟨rho, layers.policyHints, forest.1,
    fun lay => piecesSignature lay (layers.pieces.getD lay.val ([], []))⟩
  pure (some ⟨signature, digestCounter, fun lay => layers.counters.getD lay.val 0, !(layers.lows.getD 0 true), []⟩)

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness

theorem lower_chain_succ_first (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    SigGolfCandidate.T3.chain lay tree leaf i start (count + 1) value = (do
      let next ← shortHash (SigGolfCandidate.T3.chainInput lay tree leaf i start value)
      SigGolfCandidate.T3.chain lay tree leaf i (start + 1) count next) := by
  rw [show count + 1 = 1 + count by omega, SigGolfCandidate.T3.Correctness.chain_add]
  rfl

/-- Stage 2 (C3): `lower_chain_succ_first` for the chain of the current scheme. -/
theorem lower_chainW_succ_first (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    ClaudeWCT.WCT9.chainW lay tree leaf i start (count + 1) value = (do
      let next ← ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i start)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value)
      ClaudeWCT.WCT9.chainW lay tree leaf i (start + 1) count next) := by
  rw [show count + 1 = 1 + count by omega, ClaudeWCT.WCT9.chainW_add]
  have h1 : ClaudeWCT.WCT9.chainW lay tree leaf i start 1 value =
      ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i start)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value) := by
    unfold ClaudeWCT.WCT9.chainW
    simp only [List.range'_one, List.foldlM_cons, List.foldlM_nil, bind_pure]
  rw [h1]

theorem eval_chainPrefixes_length (answers : Answers) (lay : Layer)
    (tree leaf i start count : Nat) (value : Digest) :
    (evalWithAnswerFn answers (chainPrefixes lay tree leaf i start count value)).length = count + 1 := by
  induction count generalizing start value with
  | zero => simp [chainPrefixes, evalWithAnswerFn_pure]
  | succ count ih =>
    simp only [chainPrefixes, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_cons, ih]

theorem eval_chainPrefixes_getD (answers : Answers) (lay : Layer)
    (tree leaf i start count : Nat) (value : Digest) (j : Nat) (hj : j ≤ count) :
    (evalWithAnswerFn answers (chainPrefixes lay tree leaf i start count value)).getD j 0 =
      evalWithAnswerFn answers (ClaudeWCT.WCT9.chainW lay tree leaf i start j value) := by
  induction count generalizing start value j with
  | zero =>
    have hz : j = 0 := by omega
    subst j
    rfl
  | succ count ih =>
    cases j with
    | zero =>
      simp only [chainPrefixes, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.getD_cons_zero]
      rfl
    | succ j =>
      simp only [chainPrefixes, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.getD_cons_succ]
      rw [ih _ _ _ (by omega), lower_chainW_succ_first, evalWithAnswerFn_bind]

end SigGolfCandidate.Research.SharedForest

/-! Shared-forest digest selection and the exact producer cap. The selector
bit shared by each pair does not enter either child's variable cycle count. -/
namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

def firstCoord (coord : Nat) : Bool := decide (coord < 8 ∧ coord % 2 = 0)
def rawChildBase (coord : Nat) : Nat := [0, 6, 64, 70, 128, 134, 192, 198, 229].getD coord 0

def rawChildFromOutput (output : HashOutput) (coord : Fin 9) : Child :=
  ⟨output.toNat / 2 ^ rawChildBase coord.val % 128, Nat.mod_lt _ (by decide)⟩

def physicalChildFromOutput (output : HashOutput) (coord : Fin 9) : Child :=
  ⟨physicalChild (firstCoord coord.val) (rawChildFromOutput output coord).val,
    physicalChild_lt _ _ (rawChildFromOutput output coord).isLt⟩

/-- C1 (stage 1): the per-child cycle correction `2 - skips′` of the physical child's class (A routines fit
their 32-word slots, so there is no spill term). -/
def accountingCorrection (coord : Nat) (raw : Child) : Nat :=
  2 - SharedPathPacking.saves (physicalChild (firstCoord coord) raw.val)

def coordinateAccountingCost (output : HashOutput) (coord : Fin 9) : Nat :=
  routineCost (forestRank output coord.val) + accountingCorrection coord.val (rawChildFromOutput output coord)

def jointAccountingCost (output : HashOutput) : Nat :=
  ((List.finRange 9).map (coordinateAccountingCost output)).sum

def ranksAccepted (output : HashOutput) : Bool :=
  (List.finRange 9).all (fun coord => decide (rawForestRank output coord.val < 563))

/-- Joint cap 777 (`P(joint ≤ 777 | gate, ranks) = 0.990672`). -/
def digestAccepted (output : HashOutput) : Bool :=
  decide (output.toNat / 2 ^ 242 % 16384 < 791) && ranksAccepted output &&
    decide (jointAccountingCost output ≤ 777)

theorem firstCoord_eq_shared (coord : Nat) : firstCoord coord = decide (coord < 8 ∧ coord % 2 = 0) := rfl

theorem ranksAccepted_iff (output : HashOutput) : ranksAccepted output = true ↔
    ∀ coord : Fin 9, rawForestRank output coord.val < 563 := by
  simp [ranksAccepted, List.all_eq_true]

theorem accepted_conditions (output : HashOutput) (h : digestAccepted output = true) :
    output.toNat / 2 ^ 242 % 16384 < 791 ∧
    (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
    jointAccountingCost output ≤ 777 := by
  simpa only [digestAccepted, Bool.and_eq_true, decide_eq_true_eq, ranksAccepted_iff,
    and_assoc] using h
end SigGolfCandidate.Research.SharedForest

/-! The compact signature carries explicit canonical policy hints. All128 nonce
bits are retained; the hints are checked again after bottom-up recovery. -/
namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9

/-- Policy hint bound (img-v4/v6 mixed radix): h = 484·f1 + 22·f2 + f3 with f1 ≤ 15, f2, f3 ≤ 21, h < 7744. -/
def policyHintBound : Nat := 7744

def hintFloor (hints : BitVec 16) (lay : Layer) : Nat :=
  if lay = 0 then CanonicalPolicy.topFloor else hints.toNat / 22 ^ (3 - lay.val) % 22

def policyHintsValid (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool) : Bool :=
  let residual1 := CanonicalPolicy.nextResidual CanonicalPolicy.totalCredit 0 (lows.getD 0 true) (digits.getD 0 [])
  let residual2 := CanonicalPolicy.nextResidual residual1 1 (lows.getD 1 true) (digits.getD 1 [])
  let residual3 := CanonicalPolicy.nextResidual residual2 2 (lows.getD 2 true) (digits.getD 2 [])
  decide (hints.toNat < 7744 ∧ digits.length = 4 ∧
    hintFloor hints 1 = CanonicalPolicy.threshold 1 residual1 ∧
    hintFloor hints 2 = CanonicalPolicy.threshold 2 residual2 ∧
    hintFloor hints 3 = CanonicalPolicy.threshold 3 residual3)

/-- Adapter for the unchanged main-tree recovery kernels. The forest opening
is recovered separately; no dummy opening is inspected by those kernels. -/
def mainSignature (sig : Signature) : ClaudeWCT.WCT9.Signature :=
  ⟨sig.rho, fun _ => ⟨fun _ => 0, fun _ => 0⟩, sig.layers⟩

def fillTopSignature (sig : Signature) (c : Nat) : Signature :=
  { sig with layers := fun lay => fillLayer lay (sig.layers lay) c }

/-- Normal form of a top path node at height `j`: the compact codec does not store the zero-test bits
(`T3.topZeroOk`): T51 (5,195 bytes): the top `topZeroBits j` bits for `j = 1..10`; for the top sibling (`j = 11`) bits
104..127 (104..111 zero-test bits, 112..127 brute-forced). (#938 img-v6, 5,239 bytes: top `j` bits, sibling 98..127.) -/
def normPathD (j : Nat) (d : Digest) : Digest :=
  if 1 ≤ j ∧ j ≤ 10 then BitVec.ofNat 128 (d.toNat % 2 ^ (128 - topZeroBits j))
  else if j = 11 then BitVec.ofNat 128 (d.toNat % 2 ^ 104) else d

def normLayer (lay : Layer) (ls : LayerSignature lay) : LayerSignature lay :=
  ⟨ls.values, fun j => if lay.val = 0 then normPathD j.val (ls.path j) else ls.path j⟩

/-- What the compact codec keeps (13-bit hint, normalized top path; T51: 5,195 bytes); `expand` applies it first. -/
def normTop (sig : Signature) : Signature :=
  { sig with policyHints := BitVec.ofNat 16 (sig.policyHints.toNat % 2 ^ 13)
             layers := fun lay => normLayer lay (sig.layers lay) }

/-- The honest top path passes its zero tests (no nonce search hit its cap). -/
def TopPathOK (sig : Signature) : Prop :=
  ∀ j : Fin (height 0), 1 ≤ j.val → topZeroOk j.val ((sig.layers 0).path j) = true

structure RecoveredLayers where
  foldedTop : Digest
  root : Digest
  counters : List (BitVec 32)
  digits : List (List Nat)
  /-- The selected half of every layer (`true` = LOW), top first. -/
  lows : List Bool
  /-- Top-bytes layer: the nonces of the top path nodes of heights 1..11 (re-derived by `topFoldN`). -/
  nonces : List Nat

/-- Hints allow one bottom-up pass. The final check compares these hints with
the unique ancestor policy, so alternate hint encodings are rejected. -/
def recoverHintedLayers (sig : Signature) (index : Nat) (other : Digest) :
    Nat → LayerMsg → M (Option RecoveredLayers)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let some (counter, digits, low) ← CanonicalPolicy.layerCounterSearchAt lay
        (hintFloor sig.policyHints lay) tree leaf msg 0 (searchLimit lay) | pure none
      if n = 0 then
        let (folded, nonces) ← topFoldN (mainSignature sig) index digits
        let root ← topNode index folded other
        pure (some ⟨folded, root, [counter], [digits], [low], nonces⟩)
      else
        let pair ← recoverLayerPair (mainSignature sig) index lay digits
        let some previous ← recoverHintedLayers sig index other n (.pair pair.1 pair.2) | pure none
        pure (some { previous with
          counters := previous.counters ++ [counter]
          digits := previous.digits ++ [digits]
          lows := previous.lows ++ [low] })

def sharedDigestSearch (rho : Digest) (message : Message) (counter : Nat) :
    Nat → M (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel + 1 => do
      let output ← digest rho message (BitVec.ofNat 32 counter)
      if digestAccepted output then return some (BitVec.ofNat 32 counter, output)
      sharedDigestSearch rho message (counter + 1) fuel

def signPayload (cache : SigGolfCandidate.T3.Cache) (message : Message) : M (Option Signature) := do
  let rho ← privateNonce message
  let some (counter, output) ← sharedDigestSearch rho message 0 digestAttemptLimit | pure none
  let some witness ← signFromOutput cache rho counter output | pure none
  pure (some witness.signature)

def sign (cache : SigGolfCandidate.T3.Cache) (message : Message) : M (Option Signature) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return none
  signPayload cache message

/-- The pre-v6 expansion kernel (hint check, top sibling field cleared, brute force). -/
def expandFill (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) := do
  if sig.policyHints.toNat ≥ 7744 then return none
  let sig0 := fillTopSignature sig 0
  let some (counter, output) ← sharedDigestSearch sig0.rho message 0 digestAttemptLimit | pure none
  let index := digestIndex output
  let forest ← recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) sig0.forest
  let some layers ← recoverHintedLayers sig0 index ((sig0.layers 0).path topJ)
    4 (.pair forest.1 forest.2) | pure none
  if !policyHintsValid sig0.policyHints layers.digits layers.lows then return none
  if layers.root = pk then
    return some ⟨sig0, counter, fun lay => layers.counters.getD lay.val 0, !(layers.lows.getD 0 true),
      layers.nonces⟩
  let some c ← searchTop index layers.foldedTop ((sig0.layers 0).path topJ) pk searchFuel 1 | pure none
  pure (some ⟨fillTopSignature sig0 c, counter, fun lay => layers.counters.getD lay.val 0,
    !(layers.lows.getD 0 true), layers.nonces⟩)

/-- img-v6 expansion: normalize to what the 5,239-byte codec keeps, then the old kernel. -/
def expand (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) :=
  expandFill message pk (normTop sig)

theorem nonce_retained (sig : Signature) (c : Nat) :
    (fillTopSignature sig c).rho = sig.rho := rfl

theorem hints_retained (sig : Signature) (c : Nat) :
    (fillTopSignature sig c).policyHints = sig.policyHints := rfl

theorem ofNat_mod_pow_idem (n m x : Nat) (hm : m ≤ n) :
    BitVec.ofNat n ((BitVec.ofNat n (x % 2 ^ m)).toNat % 2 ^ m) = BitVec.ofNat n (x % 2 ^ m) := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hm), Nat.mod_mod]

theorem normPathD_idem (j : Nat) (d : Digest) : normPathD j (normPathD j d) = normPathD j d := by
  unfold normPathD
  by_cases h1 : 1 ≤ j ∧ j ≤ 10
  · simp only [if_pos h1]
    exact ofNat_mod_pow_idem 128 (128 - topZeroBits j) d.toNat (by omega)
  · by_cases h11 : j = 11
    · simp only [if_neg h1, if_pos h11]
      exact ofNat_mod_pow_idem 128 104 d.toNat (by omega)
    · simp only [if_neg h1, if_neg h11]

theorem normPathD_setTop (d : Digest) (c : Nat) : normPathD 11 (setTop d c) = normPathD 11 d := by
  unfold normPathD
  simp only [show ¬(1 ≤ 11 ∧ 11 ≤ 10) by omega, if_false, if_true]
  congr 1
  rw [setTop_toNat, Nat.add_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 104 ≤ 112)),
    show c % 2 ^ 16 * 2 ^ 112 % 2 ^ 104 = 0 from
      Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by norm_num)) _), add_zero, Nat.mod_mod]

/-- T51: the zero-bit allocation (`b_h = 0,0,1,1,2,3,4,5,6,7,8`; #938 had `b_h = h`). -/
theorem normZeroBits_eq (j : Nat) (hj : j ≤ 11) : topZeroBits j = topZeroAlloc.getD j 0 := by
  rfl

/-- A path node that passes its zero test is fixed by the normal form (the top sibling up to its brute-forced
bits 109..127). -/
theorem normPathD_ok (j : Nat) (hj : j < 12) (d : Digest) (hz : 1 ≤ j → topZeroOk j d = true) :
    normPathD j d = if j = 11 then setTop d 0 else d := by
  unfold normPathD
  by_cases hj0 : j = 0
  · subst hj0
    simp
  by_cases h11 : j = 11
  · subst h11
    simp only [show ¬(1 ≤ 11 ∧ 11 ≤ 10) by omega, if_false, if_true]
    have h' : d.toNat / 2 ^ 104 % 2 ^ 8 = 0 := by
      have := hz (by omega)
      unfold topZeroOk at this
      simpa using this
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, setTop_toNat, show (2 : Nat) ^ 112 = 2 ^ 104 * 2 ^ 8 by norm_num, Nat.mod_mul, h']
    simp only [mul_zero, add_zero, Nat.zero_mod, zero_mul]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) d.isLt)
  · have h1 : 1 ≤ j ∧ j ≤ 10 := by omega
    simp only [if_pos h1, if_neg h11]
    have hz' := hz (by omega)
    unfold topZeroOk at hz'
    rw [if_neg h11, beq_iff_eq] at hz'
    have hdm := Nat.div_add_mod d.toNat (2 ^ (128 - topZeroBits j))
    rw [hz', mul_zero, zero_add] at hdm
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hdm]
    exact Nat.mod_eq_of_lt d.isLt

theorem normTop_rho (sig : Signature) : (normTop sig).rho = sig.rho := rfl
theorem normTop_forest (sig : Signature) : (normTop sig).forest = sig.forest := rfl

theorem normTop_layers_ne (sig : Signature) (lay : Layer) (h : lay ≠ 0) : (normTop sig).layers lay = sig.layers lay := by
  have h0 : lay.val ≠ 0 := fun hv => h (Fin.ext hv)
  unfold normTop normLayer
  simp only [h0, if_false]

theorem normTop_hints (sig : Signature) (h : sig.policyHints.toNat < 2 ^ 13) :
    (normTop sig).policyHints = sig.policyHints := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 16 (sig.policyHints.toNat % 2 ^ 13)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt sig.policyHints.isLt]

theorem normTop_normTop (sig : Signature) : normTop (normTop sig) = normTop sig := by
  unfold normTop
  congr 1
  · exact ofNat_mod_pow_idem 16 13 sig.policyHints.toNat (by omega)
  · funext lay
    unfold normLayer
    congr 1
    funext j
    by_cases h0 : lay.val = 0
    · simp only [h0, if_true, normPathD_idem]
    · simp only [h0, if_false]

theorem normTop_fill (sig : Signature) (c : Nat) : normTop (fillTopSignature sig c) = normTop sig := by
  unfold normTop fillTopSignature
  congr 1
  funext lay
  unfold normLayer fillLayer
  congr 1
  funext j
  by_cases h0 : lay.val = 0
  · by_cases h11 : j.val = 11
    · simp only [h0, h11, and_self, if_true, normPathD_setTop]
    · simp only [h0, h11, and_false, true_and, if_true, if_false]
  · simp only [h0, false_and, if_false]

/-- Honest signatures (top path zero tests passed, 13-bit hint) normalize to the old `fillTopSignature sig 0`. -/
theorem normTop_eq_fill (sig : Signature) (hh : sig.policyHints.toNat < 2 ^ 13) (hz : TopPathOK sig) :
    normTop sig = fillTopSignature sig 0 := by
  unfold normTop fillTopSignature
  congr 1
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt sig.policyHints.isLt]
  · funext lay
    unfold normLayer fillLayer
    congr 1
    funext j
    by_cases h0 : lay.val = 0
    · have hl : lay = 0 := Fin.ext h0
      subst hl
      have hj : j.val < 12 := j.isLt
      rw [normPathD_ok j.val hj _ (hz j)]
      by_cases h11 : j.val = 11
      · simp [h11]
      · simp [h11]
    · simp only [h0, false_and, if_false]

theorem expand_normTop (message : Message) (pk : Digest) (sig : Signature) :
    expand message pk (normTop sig) = expand message pk sig := by
  unfold expand
  rw [normTop_normTop]

theorem fillTopSignature_fill (sig : Signature) (a b : Nat) :
    fillTopSignature (fillTopSignature sig a) b = fillTopSignature sig b := by
  unfold fillTopSignature
  simp only [Signature.mk.injEq, true_and]
  funext lay
  exact fillLayer_fillLayer lay (sig.layers lay) a b

theorem expandFill_fill (message : Message) (pk : Digest) (sig : Signature) (c : Nat) :
    expandFill message pk (fillTopSignature sig c) = expandFill message pk sig := by
  simp only [expandFill, hints_retained, fillTopSignature_fill]

/-- On an honest signature (13-bit hint, top path zero tests passed) `expand` is the old kernel. -/
theorem expand_eq_expandFill (message : Message) (pk : Digest) (sig : Signature)
    (hh : sig.policyHints.toNat < 2 ^ 13) (htop : TopPathOK sig) :
    expand message pk sig = expandFill message pk sig := by
  unfold expand
  rw [normTop_eq_fill sig hh htop, expandFill_fill]


theorem canonical_fts_window : CanonicalPolicy.ftsSearchLimit = digestAttemptLimit := rfl

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

def aCorrection (low : Nat) : Nat := 2 - SharedPathPacking.saves low
def bCorrection (low : Nat) : Nat := 2 - SharedPathPacking.saves low

/-- C1 (stage 1): the correction `2 - skips′` of each low-field class (13 classes 0, 16 classes 1, 3 classes 2). -/
def correctionTable : List Nat :=
  [2,1,1,1,1,0,0,1,1,0,0,0,0,0,0,1,2,1,1,0,1,0,0,1,1,0,0,1,1,1,1,2]

set_option maxRecDepth 100000 in
theorem aCorrection_table : ∀ c : Fin 32, aCorrection c.val = correctionTable.getD c.val 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem bCorrection_table : ∀ c : Fin 32, bCorrection c.val = correctionTable.getD c.val 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Only five unshared selector bits influence a coordinate's accounting
cost. The shared pair-branch bit is absent from this formula. -/
theorem accountingCorrection_low (coord : Fin 9) (raw : Child) :
    accountingCorrection coord.val raw =
      if firstCoord coord.val then aCorrection (raw.val % 32)
      else bCorrection (raw.val / 2 % 32) := by
  fin_cases coord <;> fin_cases raw <;> decide +kernel

def costFieldBase (coord : Nat) : Nat := rawChildBase coord + (if firstCoord coord then 0 else 1)
def costField (output : HashOutput) (coord : Fin 9) : Fin 32 :=
  ⟨output.toNat / 2 ^ costFieldBase coord.val % 32, Nat.mod_lt _ (by decide)⟩

theorem accountingCorrection_field (output : HashOutput) (coord : Fin 9) :
    accountingCorrection coord.val (rawChildFromOutput output coord) =
      if firstCoord coord.val then aCorrection (costField output coord).val
      else bCorrection (costField output coord).val := by
  rw [accountingCorrection_low]
  unfold rawChildFromOutput costField costFieldBase
  split
  · rename_i h
    simp only [h, ↓reduceIte, Nat.add_zero]
    congr 1
    omega
  · rename_i h
    simp only [h, ↓reduceIte, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    congr 1
    omega

theorem costFieldBases : (List.range 9).map costFieldBase =
    [0, 7, 64, 71, 128, 135, 192, 199, 230] := by decide +kernel

/-- All nine5-bit cost fields, nine10-bit rank fields, the31-bit index,
and14-bit gate occupy disjoint ranges of the256-bit digest. -/
def countingFields : List (Nat × Nat) :=
  ((List.range 9).map fun k => (costFieldBase k, 5)) ++
  ((List.range 9).map fun k => (rankBase k, 10)) ++ [(33,31), (242,14)]

def countingFieldsOK : Bool :=
  countingFields.all (fun a => decide (a.1 + a.2 ≤ 256)) &&
    (countingFields.zipIdx).all (fun ai =>
      (countingFields.zipIdx).all (fun bj =>
        decide (ai.2 = bj.2 ∨ ai.1.1 + ai.1.2 ≤ bj.1.1 ∨ bj.1.1 + bj.1.2 ≤ ai.1.1)))

theorem countingFields_disjoint : countingFieldsOK = true := by decide +kernel
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness

def prefixRows (answers : Answers) (lay : Layer) (tree leaf : Nat) : List (List Digest) :=
  (List.range (chainCount lay)).map fun i =>
    evalWithAnswerFn answers (chainPrefixes lay tree leaf i 0 (maxDigit lay i)
      (wotsSeed answers lay tree leaf i))

theorem prefixRows_getD (answers : Answers) (lay : Layer) (tree leaf i j : Nat)
    (hi : i < chainCount lay) (hj : j ≤ maxDigit lay i) :
    ((prefixRows answers lay tree leaf).getD i []).getD j 0 =
      evalWithAnswerFn answers (chainW lay tree leaf i 0 j
        (wotsSeed answers lay tree leaf i)) := by
  unfold prefixRows
  rw [List.getD_eq_getElem _ [] (by simpa)]
  simp only [List.getElem_map, List.getElem_range]
  exact eval_chainPrefixes_getD answers lay tree leaf i 0 _ _ j hj

theorem buildLeafPrefixes_result (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree leaf : Nat) (carry : List Digest)
    (hcarry : leaf % famGrp lay ≠ 0 → carry = famCoefL answers lay tree (famOf lay leaf)) :
    evalWithAnswerFn answers (buildLeafPrefixes lay tree leaf carry) =
      ((wotsRoot answers lay tree leaf, prefixRows answers lay tree leaf),
       leafCarryOut answers lay tree leaf) := by
  simp only [buildLeafPrefixes, evalWithAnswerFn_bind,
    eval_lowerCoefs answers hlay tree leaf carry hcarry, evalWithAnswerFn_pure, eval_mapM,
    lowerFamilySeed_eq answers hlay]
  change ((evalWithAnswerFn answers (lowerLeafHash lay tree leaf
    ((List.range (chainCount lay)).map fun i =>
      ((prefixRows answers lay tree leaf).getD i []).getD (maxDigit lay i) 0)),
    prefixRows answers lay tree leaf), _) = _
  have he : (List.range (chainCount lay)).map (fun i =>
      ((prefixRows answers lay tree leaf).getD i []).getD (maxDigit lay i) 0) =
      (List.range (chainCount lay)).map (wotsEnd answers lay tree leaf) := by
    apply List.map_congr_left
    intro i hi
    exact prefixRows_getD answers lay tree leaf i _ (List.mem_range.mp hi) (by omega)
  rw [he]
  rfl

def prefixTreeRows (lay : Layer) (tree selected : Nat) :
    M (List Digest × List (List Digest) × List Digest) :=
  (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List (List Digest) × List Digest) leaf => do
      let ((root, prefixes), carry) ←
        if leaf = selected then buildLeafPrefixes lay tree leaf state.2.2
        else do
          let ((root, _), carry) ← buildLeafPF lay tree leaf [] state.2.2
          pure ((root, []), carry)
      pure (state.1 ++ [root], if leaf = selected then prefixes else state.2.1, carry))
    ([], [], [])

def PrefixTreeRows (answers : Answers) (lay : Layer) (tree selected done : Nat)
    (rows : List Digest × List (List Digest) × List Digest) : Prop :=
  rows.1.length = done ∧
    (∀ j, j < done → rows.1.getD j 0 = wotsRoot answers lay tree j) ∧
    rows.2.1 = (if selected < done then prefixRows answers lay tree selected else []) ∧
    rows.2.2 = treeCarry answers lay tree done

theorem eval_prefixTreeRows (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree selected : Nat) :
    PrefixTreeRows answers lay tree selected (2 ^ height lay)
      (evalWithAnswerFn answers (prefixTreeRows lay tree selected)) := by
  unfold prefixTreeRows
  refine eval_foldlM_range_inv answers (2 ^ height lay) _
    (PrefixTreeRows answers lay tree selected) ([], [], [])
    (by simp [PrefixTreeRows, treeCarry]) ?_
  intro done _ rows hrows
  rcases hrows with ⟨hlen, hroot, hvalues, hc⟩
  have hstep : evalWithAnswerFn answers (do
      let ((root, prefixes), carry) ←
        if done = selected then buildLeafPrefixes lay tree done rows.2.2
        else do
          let ((root, _), carry) ← buildLeafPF lay tree done [] rows.2.2
          pure ((root, []), carry)
      pure (rows.1 ++ [root], if done = selected then prefixes else rows.2.1, carry)) =
      (rows.1 ++ [wotsRoot answers lay tree done],
       if done = selected then prefixRows answers lay tree done else rows.2.1,
       leafCarryOut answers lay tree done) := by
    by_cases hs : done = selected
    · subst selected
      simp only [↓reduceIte, evalWithAnswerFn_bind, hc,
        buildLeafPrefixes_result answers hlay tree done _
          (carryOk_treeCarry answers lay tree done), evalWithAnswerFn_pure]
    · simp only [hs, ↓reduceIte, evalWithAnswerFn_bind, hc,
        buildLeafPF_result answers hlay tree done [] (Cost.validDigits_nil lay) _
          (carryOk_treeCarry answers lay tree done), evalWithAnswerFn_pure]
  rw [hstep]
  refine ⟨by simp [hlen], ?_, ?_, ?_⟩
  · intro j hj
    rw [ClaudeWCT.WCT9.getD_append_singleton, hlen]
    by_cases hjd : j < done
    · rw [if_pos hjd]; exact hroot j hjd
    · have he : j = done := by omega
      subst j
      simp
  · by_cases hs : done = selected
    · subst hs; simp
    · have hs' : selected < done + 1 ↔ selected < done := by omega
      simp only [if_neg hs, hvalues, hs']
  · show leafCarryOut answers lay tree done = treeCarry answers lay tree (done + 1)
    unfold treeCarry
    rw [if_neg (show done + 1 ≠ 0 by omega), Nat.add_sub_cancel]

theorem buildTreePrefixes_factor (lay : Layer) (tree selected : Nat) :
    buildTreePrefixes lay tree selected = (do
      let rows ← prefixTreeRows lay tree selected
      let levels ← buildLevelsBelow 3 lay.val tree (height lay) rows.1
      pure ⟨levels, rows.2.1⟩) := rfl

theorem eval_buildTreePrefixes_result (answers : Answers) {lay : Layer}
    (hlay : lay ≠ 0) (tree selected : Nat) (hsel : selected < 2 ^ height lay) :
    evalWithAnswerFn answers (buildTreePrefixes lay tree selected) =
      ⟨(wotsTree answers lay tree).take (height lay),
        prefixRows answers lay tree selected⟩ := by
  let rows := evalWithAnswerFn answers (prefixTreeRows lay tree selected)
  have hr : PrefixTreeRows answers lay tree selected (2 ^ height lay) rows :=
    eval_prefixTreeRows answers hlay tree selected
  rcases hr with ⟨hlen, hroot, hvalues, -⟩
  have hroots : rows.1 = (List.range (2 ^ height lay)).map (wotsRoot answers lay tree) :=
    list_eq_range_map _ _ _ hlen hroot
  rw [if_pos hsel] at hvalues
  rw [buildTreePrefixes_factor, evalWithAnswerFn_bind]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (⟨evalWithAnswerFn answers (buildLevelsBelow 3 lay.val tree (height lay) rows.1),
    rows.2.1⟩ : PreparedLower) = _
  rw [hroots, hvalues, eval_buildLevelsBelow answers 3 lay.val tree (height lay) _ (by simp)
    (by fin_cases lay <;> decide)]
  simp only [wotsTree, if_neg hlay]

theorem preparedPieces_result (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree selected : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (hsel : selected < 2 ^ height lay) :
    preparedPieces lay selected
      (evalWithAnswerFn answers (buildTreePrefixes lay tree selected)) digits =
      wotsPieces answers lay tree selected digits := by
  rw [eval_buildTreePrefixes_result answers hlay tree selected hsel]
  unfold preparedPieces wotsPieces
  apply Prod.ext
  · apply List.map_congr_left
    intro i hi
    exact prefixRows_getD answers lay tree selected i _ (List.mem_range.mp hi)
      (hvalid i (List.mem_range.mp hi))
  · exact map_range_take_path _ _ _

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem base22_unique {x y : Nat} (hx : x < 7744) (hy : y < 7744)
    (h1 : x / 484 % 22 = y / 484 % 22) (h2 : x / 22 % 22 = y / 22 % 22)
    (h3 : x % 22 = y % 22) : x = y := by
  omega

theorem hintFloor_unique {a b : BitVec 16} (ha : a.toNat < 7744) (hb : b.toNat < 7744)
    (h1 : hintFloor a 1 = hintFloor b 1)
    (h2 : hintFloor a 2 = hintFloor b 2)
    (h3 : hintFloor a 3 = hintFloor b 3) : a = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [hintFloor, show (1 : Layer) ≠ 0 by decide, show (2 : Layer) ≠ 0 by decide,
    show (3 : Layer) ≠ 0 by decide, if_false] at h1 h2 h3
  norm_num at h1 h2 h3
  exact base22_unique ha hb h1 h2 h3

theorem policyHintsValid_unique {a b : BitVec 16} {digits : List (List Nat)} {lows : List Bool}
    (ha : policyHintsValid a digits lows = true) (hb : policyHintsValid b digits lows = true) : a = b := by
  simp only [policyHintsValid, decide_eq_true_eq] at ha hb
  exact hintFloor_unique ha.1 hb.1 (ha.2.2.1.trans hb.2.2.1.symm)
    (ha.2.2.2.1.trans hb.2.2.2.1.symm) (ha.2.2.2.2.trans hb.2.2.2.2.symm)

theorem encodedHints_spec (a b c : Nat) (ha : a < 16) (hb : b < 22) (hc : c < 22) :
    let code := BitVec.ofNat 16 (484 * a + 22 * b + c)
    code.toNat < 7744 ∧ hintFloor code 1 = a ∧
      hintFloor code 2 = b ∧ hintFloor code 3 = c := by
  dsimp only
  simp only [hintFloor, show (1 : Layer) ≠ 0 by decide,
    show (2 : Layer) ≠ 0 by decide, show (3 : Layer) ≠ 0 by decide, if_false]
  norm_num [BitVec.toNat_ofNat]
  have hn : 484 * a + 22 * b + c < 65536 := by omega
  rw [Nat.mod_eq_of_lt hn]
  omega

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem firstThreshold_window : ∀ r : Fin 56,
    CanonicalPolicy.threshold 1 r.val < 16 ∧
      r.val - CanonicalPolicy.threshold 1 r.val ≤ 40 := by
  decide +kernel

theorem secondThreshold_window : ∀ r : Fin 41,
    CanonicalPolicy.threshold 2 r.val < 22 ∧
      r.val - CanonicalPolicy.threshold 2 r.val ≤ 21 := by
  decide +kernel

theorem thirdThreshold_window (r : Nat) (hr : r ≤ 21) :
    CanonicalPolicy.threshold 3 r = r := by
  simp [CanonicalPolicy.threshold, hr]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Cost ClaudeWCT.WCT9.Cost

theorem bound_chainPrefixes (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    CBound (fun xs => xs.length = count + 1) count
      (chainPrefixes lay tree leaf i start count value) := by
  induction count generalizing start value with
  | zero => exact .pure [value] 0 rfl
  | succ count ih =>
    unfold chainPrefixes
    have hs : CBound (fun _ => True) 1
        (halfHash (chainHigh lay i start)
          (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value)) := by
      apply bound_halfHash <;>
        simp [ClaudeWCT.WCT9.chainInputW_length, pad64_length]
    refine hs.bind' (l := count) (fun next _ => ?_) (by omega)
    refine (ih (start + 1) next).bind' (l := 0) (n := count)
      (fun tail ht => .pure (value :: tail) 0 (by simp [ht])) (by omega)

theorem sum_map_range_eq (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem bound_buildLeafPrefixes (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    CBound (fun result => result.1.2.length = chainCount lay) (leafCostP lay leaf)
      (buildLeafPrefixes lay tree leaf carry) := by
  unfold buildLeafPrefixes
  refine (bound_lowerCoefs lay tree leaf carry).bind' (l := digitTotal lay + leafHashCost lay)
    (fun res _ => ?_) (by unfold leafCostP; omega)
  refine (Bound.mapM_list (P := GoodQuery) (List.range (chainCount lay)) _
    (fun i => maxDigit lay i) (fun i _ =>
      (bound_chainPrefixes lay tree leaf i 0 (maxDigit lay i) (lowerFamilySeed res.1 lay leaf i)).mono
        (fun _ h => h) (fun _ _ => trivial))).bind' (l := leafHashCost lay)
    (fun prefixes hprefixes => ?_) ?_
  · refine (bound_lowerLeafHash lay tree leaf _ (by simp only [List.length_map, List.length_range])).bind' (l := 0) (n := leafHashCost lay)
      (fun root _ => .pure _ 0 (by simpa using hprefixes)) (by omega)
  · unfold digitTotal
    simp only [sum_map_range_eq]
    exact le_rfl

theorem bound_buildTreePrefixes (lay : Layer) (tree selected : Nat) :
    CBound (fun result => LevelShape (height lay) (height lay - 1) result.levels)
      (treeCostP lay) (buildTreePrefixes lay tree selected) := by
  unfold buildTreePrefixes
  refine Bound.bind' (l := 2 ^ height lay - 2) (Bound.foldlM_range (2 ^ height lay) _
    (fun i (state : List Digest × List (List Digest) × List Digest) => state.1.length = i)
    (leafCostP lay) ([], [], []) rfl (fun leaf _ state hstate => ?_))
    (fun state hstate => ?_) le_rfl
  · by_cases hs : leaf = selected
    · simp only [if_pos hs]
      refine (bound_buildLeafPrefixes lay tree leaf state.2.2).bind' (l := 0)
        (fun result _ => .pure _ 0 (by simp [hstate])) (by omega)
    · simp only [if_neg hs]
      refine (bound_buildLeafPF lay tree leaf [] (validDigits_nil lay) state.2.2).bind' (l := 0)
        (fun result _ => ?_) (by omega)
      exact .pure _ 0 (by simp [hstate])
  · refine (bound_buildLevelsBelow 3 lay.val tree (height lay) state.1 hstate
      (by fin_cases lay <;> decide)).bind' (l := 0)
      (fun levels hlevels => .pure (PreparedLower.mk levels state.2.1) 0 hlevels) (by omega)

theorem bound_prepareRoots (index : Nat) :
    CBound (fun _ => True) (treeCostP 1 + treeCostP 2 + treeCostP 3) (prepareRoots index) := by
  unfold prepareRoots
  refine (bound_buildTreePrefixes 1 (route index 1).2 (route index 1).1).bind'
    (l := treeCostP 2 + treeCostP 3) (fun one _ => ?_) (by omega)
  refine (bound_buildTreePrefixes 2 (route index 2).2 (route index 2).1).bind'
    (l := treeCostP 3) (fun two _ => ?_) (by omega)
  exact (bound_buildTreePrefixes 3 (route index 3).2 (route index 3).1).bind'
    (l := 0) (fun three _ => .pure (PreparedRoots.mk one two three) 0 trivial) (by omega)

/-- v6 lower families: 81146 − 325 (L1 349 + L2/L3 175 family pairs instead of 4 per leaf). -/
theorem prepared_roots_cost : treeCostP 1 + treeCostP 2 + treeCostP 3 = 80821 := by
  rw [treeCostP_one, treeCostP_two, treeCostP_three]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Cost ClaudeWCT.WCT9.Cost

theorem rawChild_lt (first : Bool) (physical : Nat) (h : physical < 128) :
    rawChild first physical < 128 := by
  cases first <;> simp only [rawChild, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem bound_highHash64 (input : HashInput) (hlen : input.length = 64) :
    CBound (fun _ => True) 1 (highHash input) := by
  apply bound_highHashP
  · simp only [GoodQuery, pad64_length, hlen]
    norm_num
  · simp only [pad64_length, hlen]
    norm_num

theorem bound_sharedOuterHash (coord index heap : Nat) (left right : Digest) :
    CBound (fun _ => True) 1 (sharedOuterHash coord index heap left right) := by
  unfold sharedOuterHash
  split
  · apply bound_shortHash <;> simp [wctTopInput_length, pad64_length]
  · exact bound_highHash64 _ (wctTopInput_length ..)

theorem bound_sharedNode (first : Bool) (coord index heap : Nat) (pads : Nat → PairRoot)
    (left right : Digest) :
    CBound (fun _ => True) 1 (sharedNode first coord index heap pads left right) := by
  unfold sharedNode
  split
  · exact bound_sharedOuterHash ..
  · split
    · split
      · exact bound_highHash64 _ (wctTopInput_length ..)
      · apply bound_shortHash <;> simp [wctTopInput_length, pad64_length]
    · rw [nodeHashH_eq, ftsHash_eq]
      split
      · exact bound_highHash64 _ (nodeInput_length ..)
      · apply bound_shortHash <;> simp [nodeInput_length, pad64_length]

theorem bound_sharedHeap (first : Bool) (index coord : Nat) (pads : Nat → PairRoot)
    (leaves : List Digest) :
    CBound (fun _ => True) (if first then 124 else 126) (sharedHeap first index coord pads leaves) := by
  unfold sharedHeap
  apply (Bound.foldlM_list (P := GoodQuery)
    (List.range' (if first then 4 else 2) (if first then 124 else 126)).reverse
    (fun (nodes : Array Digest) heap => do
      let value ← sharedNode first coord index heap pads
        (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
      pure (nodes.set! heap value)) (fun _ _ => True) (fun _ => 1) _
    trivial (fun i hi nodes _ =>
      (bound_sharedNode first coord index _ pads _ _).bind' (l := 0)
        (fun value _ => .pure (nodes.set! _ value) 0 trivial) (by omega))).mono_k
  simp

theorem bound_buildSharedCoordinate (first : Bool) (index coord : Nat)
    (hcoord : coord < 9) (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    CBound (fun _ => True) (if first then 3479 else 3481)
      (buildSharedCoordinate first index coord selected word pads) := by
  unfold buildSharedCoordinate
  refine (cbound_of_ftsBound (ftsBound_ftsCoefs index coord hcoord)).bind'
    (l := 3328 + if first then 124 else 126) (fun coefs _ => ?_) ?_
  · refine (Bound.foldlM_range_le 128 _ (fun _ _ => True) (fun _ => 26) ([], [])
      trivial (fun j hj state _ => ?_) (fun _ _ => trivial) (by simp)).bind'
      (l := if first then 124 else 126) (fun state _ => ?_) le_rfl
    · refine (bound_buildChildH (128 + j) index coord (rawChild first j) word coefs (pads (j / 64)).1
        hcoord (rawChild_lt first j hj)).bind' (l := 0)
        (fun child _ => .pure _ 0 trivial) (by simp [ClaudeWCT.WCT9.childCost])
    · exact (bound_sharedHeap first index coord pads state.1).bind' (l := 0)
        (fun nodes _ => .pure (nodes, state.2) 0 trivial) (by omega)
  · cases first <;> decide

theorem bound_buildPair (index pair : Nat) (hpair : pair < 4) (s : Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    CBound (fun _ => True) 6960 (buildPair index pair s aWord bWord prev) := by
  unfold buildPair
  refine (bound_buildSharedCoordinate true index (2 * pair) (by omega)
    (firstChild s) aWord (fun _ => prev)).bind' (l := 3481) (fun a _ => ?_) (by decide)
  exact (bound_buildSharedCoordinate false index (2 * pair + 1) (by omega)
    (secondChild s) bWord (nodesPair a.1)).bind' (l := 0)
    (fun b _ => .pure _ 0 trivial) (by decide)

theorem bound_buildSingleton (index : Nat) (selected : Child) (word : Rank) (prev : PairRoot) :
    CBound (fun _ => True) 3481 (buildSingleton index selected word prev) := by
  unfold buildSingleton
  exact (bound_buildSharedCoordinate false index 8 (by decide) selected word (fun _ => prev)).bind'
    (l := 0) (fun built _ => .pure _ 0 trivial) (by decide)

theorem bound_buildForest (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    CBound (fun _ => True) 31321 (buildForest index selected words) := by
  unfold buildForest
  refine (Bound.foldlM_list (P := GoodQuery) (List.finRange 4) _ (fun _ _ => True)
    (fun _ => 6960) ([], ftsStart) trivial (fun i hi state _ => ?_)).bind'
    (l := 3481) (fun state _ => ?_) (by simp)
  · exact (bound_buildPair index _ ((List.finRange 4)[i]'hi).isLt _ _ _ state.2).bind'
      (l := 0) (fun built _ => .pure _ 0 trivial) (by decide)
  · exact (bound_buildSingleton index selected.singleton words.singleton state.2).bind'
      (l := 0) (fun last _ => .pure _ 0 trivial) (by decide)

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem canonical_decode_valid {lay : Layer} {answer : Digest} {digits : List Nat}
    (h : CanonicalPolicy.decode lay answer = some digits) :
    Cost.ValidDigits lay digits := by
  have hv := Cost.validDigits_decode h
  fin_cases lay <;> simpa [CanonicalPolicy.normalLayer, Cost.ValidDigits, chainCount, maxDigit] using hv

theorem canonical_search_some (answers : Answers) (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) : ∀ fuel counter found digits low, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers
        (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) = some (found, digits, low) →
      counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧
        CanonicalPolicy.producerDecodeOut lay floor
          (evalWithAnswerFn answers (publicHash (layerEncodingInput lay tree leaf msg found))) =
            some (digits, low) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter found digits low _ he
      simp [CanonicalPolicy.layerCounterSearchAt] at he
  | succ fuel ih =>
      intro counter found digits low hlimit he
      simp only [CanonicalPolicy.layerCounterSearchAt, evalWithAnswerFn_bind] at he
      cases hd : CanonicalPolicy.producerDecodeOut lay floor (evalWithAnswerFn answers
        (publicHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)))) with
      | none =>
          simp only [hd] at he
          obtain ⟨hlo, hhi, hgood⟩ := ih (counter + 1) found digits low (by omega) he
          exact ⟨by omega, by omega, hgood⟩
      | some values =>
          simp only [hd, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          have hcount : (BitVec.ofNat 32 counter).toNat = counter := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact ⟨by rw [hcount], by rw [hcount]; omega, hd⟩

/-- `canonical_search_some` unpacked: the returned half is the canonical one and the producer accepted the
canonical word (`encodingHash`) with that half. -/
theorem canonical_search_some' (answers : Answers) (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (fuel counter : Nat) (found : BitVec 32) (digits : List Nat) (low : Bool)
    (hlimit : counter + fuel ≤ 2 ^ 32)
    (he : evalWithAnswerFn answers
        (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) = some (found, digits, low)) :
    counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧
      low = lowSelected lay (evalWithAnswerFn answers (publicHash (layerEncodingInput lay tree leaf msg found))) ∧
      CanonicalPolicy.producerDecodeAt lay floor low
        (evalWithAnswerFn answers (encodingHash lay (layerEncodingInput lay tree leaf msg found))) = some digits := by
  obtain ⟨h1, h2, h3⟩ := canonical_search_some answers lay floor tree leaf msg fuel counter found digits low hlimit he
  obtain ⟨hl, hd⟩ := CanonicalPolicy.producerDecodeOut_spec h3
  exact ⟨h1, h2, hl, hd⟩

theorem canonical_search_valid_credit (answers : Answers) (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (fuel counter : Nat) (found : BitVec 32) (digits : List Nat) (low : Bool)
    (hlimit : counter + fuel ≤ 2 ^ 32)
    (he : evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) = some (found, digits, low)) :
    Cost.ValidDigits lay digits ∧ floor ≤ CanonicalPolicy.credit lay low digits := by
  have hd := (canonical_search_some' answers lay floor tree leaf msg fuel counter found digits low hlimit he).2.2.2
  exact ⟨canonical_decode_valid (CanonicalPolicy.producerDecodeAt_spec hd).1,
    CanonicalPolicy.producerDecodeAt_credit hd⟩

theorem canonical_four_residual (d0 d1 d2 d3 : List Nat) (l0 l1 l2 l3 : Bool)
    (h0 : 14 ≤ CanonicalPolicy.credit 0 l0 d0)
    (h1 : CanonicalPolicy.threshold 1 (CanonicalPolicy.nextResidual 69 0 l0 d0) ≤
      CanonicalPolicy.credit 1 l1 d1)
    (h2 : CanonicalPolicy.threshold 2
      (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 69 0 l0 d0) 1 l1 d1) ≤
      CanonicalPolicy.credit 2 l2 d2)
    (h3 : CanonicalPolicy.threshold 3
      (CanonicalPolicy.nextResidual
        (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 69 0 l0 d0) 1 l1 d1) 2 l2 d2) ≤
      CanonicalPolicy.credit 3 l3 d3) :
    CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual
      (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 69 0 l0 d0) 1 l1 d1) 2 l2 d2) 3 l3 d3 = 0 := by
  let r1 := CanonicalPolicy.nextResidual 69 0 l0 d0
  have hr1 : r1 < 56 := by dsimp [r1, CanonicalPolicy.nextResidual]; omega
  have hw1 := firstThreshold_window ⟨r1, hr1⟩
  change CanonicalPolicy.threshold 1 r1 < 16 ∧ r1 - CanonicalPolicy.threshold 1 r1 ≤ 40 at hw1
  let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
  have hr2 : r2 < 41 := by
    change CanonicalPolicy.threshold 1 r1 ≤ CanonicalPolicy.credit 1 l1 d1 at h1
    dsimp [r2, CanonicalPolicy.nextResidual]; omega
  have hw2 := secondThreshold_window ⟨r2, hr2⟩
  change CanonicalPolicy.threshold 2 r2 < 22 ∧ r2 - CanonicalPolicy.threshold 2 r2 ≤ 21 at hw2
  let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
  have hr3 : r3 ≤ 21 := by
    change CanonicalPolicy.threshold 2 r2 ≤ CanonicalPolicy.credit 2 l2 d2 at h2
    dsimp [r3, CanonicalPolicy.nextResidual]; omega
  change CanonicalPolicy.threshold 3 r3 ≤ CanonicalPolicy.credit 3 l3 d3 at h3
  rw [thirdThreshold_window r3 hr3] at h3
  change r3 - CanonicalPolicy.credit 3 l3 d3 = 0
  omega

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9

def verifyDigestAccepted (output : HashOutput) : Bool :=
  decide (output.toNat / 2 ^ 242 % 16384 < 791) && ranksAccepted output

theorem digestAccepted_implies_verify {output : HashOutput} (h : digestAccepted output = true) :
    verifyDigestAccepted output = true := by
  simp only [digestAccepted, Bool.and_eq_true] at h
  simpa only [verifyDigestAccepted, Bool.and_eq_true] using h.1

/-- Broad normalized verification retains the machine's early abort ordering.
Canonical producer floors and hints are checked by the signer and expander. -/
def verifyLayers (w : Witness) (index : Nat) : Nat → LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← verificationHash lay w.topHigh (layerEncodingInput lay tree leaf msg counter)
      if n = 0 then verifyTopN (mainSignature w.signature) w.topNonces index answer
      else
        let some digits := CanonicalPolicy.decode lay answer | pure none
        let some pair ← recoverLayerPairGuard (mainSignature w.signature) index lay answer digits | pure none
        verifyLayers w index n (.pair pair.1 pair.2)

def verify (message : Message) (pk : Digest) (w : Witness) : M Bool := do
  if w.digestCounter.toNat ≥ digestVerifyWindow then return false
  let output ← digest w.signature.rho message w.digestCounter
  if !verifyDigestAccepted output then return false
  let index := digestIndex output
  let forest ← recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) w.signature.forest
  let some root ← verifyLayers w index 4 (.pair forest.1 forest.2) | pure false
  pure (root == pk)

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoverHintedLayers_verified (answers : Answers) (sig : Signature) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg result,
      evalWithAnswerFn answers (recoverHintedLayers sig index ((sig.layers 0).path topJ) n msg) = some result →
      result.counters.length = n ∧ result.digits.length = n ∧ result.lows.length = n ∧
        ∀ w : Witness, w.signature = sig →
          (∀ lay : Layer, lay.val < n → w.counters lay = result.counters.getD lay.val 0) →
          w.topHigh = !(result.lows.getD 0 true) → w.topNonces = result.nonces →
          evalWithAnswerFn answers (verifyLayers w index n msg) = some result.root := by
  intro n
  induction n with
  | zero =>
      intro _ msg result he
      simp [recoverHintedLayers] at he
  | succ n ih =>
      intro hn msg result he
      simp only [recoverHintedLayers, evalWithAnswerFn_bind] at he
      split at he
      ·
          rename_i counter digits low hs
          have hlim := searchLimit_le (Fin.ofNat 4 n)
          obtain ⟨_, hbound, hlow, hproducer⟩ := canonical_search_some' answers _ _ _ _ _
            _ 0 counter digits low (by unfold counterLimit at hlim; omega) hs
          have hdecode := (CanonicalPolicy.producerDecodeAt_spec hproducer).1
          have hnot : ¬counter.toNat ≥ verifyWindow := ctr_not_ge_verifyWindow counter
          have hlay := ofNat_layer_val n (by omega)
          by_cases hn0 : n = 0
          · subst n
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
            subst result
            refine ⟨rfl, rfl, rfl, fun w hw hc hh hnon => ?_⟩
            have hcounter : w.counters (Fin.ofNat 4 0) = counter := by
              rw [hc _ (by rw [hlay]; omega), hlay]; rfl
            have hdecode0 : SigGolfCandidate.T3.decode 0
                (evalWithAnswerFn answers (encodingHash 0
                  (layerEncodingInput 0 (route index 0).2 (route index 0).1 msg counter))) = some digits := hdecode
            have hv : evalWithAnswerFn answers (verificationHash 0 w.topHigh
                (layerEncodingInput 0 (route index 0).2 (route index 0).1 msg counter)) =
                evalWithAnswerFn answers (encodingHash 0
                  (layerEncodingInput 0 (route index 0).2 (route index 0).1 msg counter)) := by
              apply eval_verificationHash_honest
              rw [hh, encodingHigh_top]
              simp only [List.getD_cons_zero]
              exact congrArg (fun b => !b) hlow
            simp only [verifyLayers, hcounter, hnot, ite_false, evalWithAnswerFn_bind, if_true, hw]
            simp only [show (Fin.ofNat 4 0 : Layer) = 0 from rfl]
            rw [hv, hnon]
            exact eval_verifyTopN_topFoldN answers _ index hdecode0
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            split at he
            rotate_left
            · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
            ·
                rename_i previous hr
                simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
                subst result
                obtain ⟨hlen, hdlen, hllen, hverify⟩ := ih (by omega) _ _ hr
                refine ⟨by simp [hlen], by simp [hdlen], by simp [hllen], fun w hw hc hh => ?_⟩
                have hcounter : w.counters (Fin.ofNat 4 n) = counter := by
                  rw [hc _ (by rw [hlay]; omega), hlay,
                    List.getD_append_right previous.counters [counter] 0 n (by omega), hlen]
                  simp
                have hnonzero : (Fin.ofNat 4 n : Layer) ≠ 0 := by
                  intro h; have := congrArg Fin.val h; rw [hlay] at this; exact hn0 this
                have hgood : lowerRankGood (evalWithAnswerFn answers (encodingHash (Fin.ofNat 4 n)
                    (layerEncodingInput (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
                      (route index (Fin.ofNat 4 n)).1 msg counter))) :=
                  (CanonicalPolicy.producerDecodeAt_spec hproducer).2.2.2.resolve_left hnonzero
                simp only [verifyLayers, hcounter, hnot, ite_false, evalWithAnswerFn_bind,
                  verificationHash_lower (Fin.ofNat 4 n) hnonzero,
                  hdecode, hn0, hw, recoverLayerPairGuard_of_good _ _ _ _ _ hgood, evalWithAnswerFn_map]
                apply hverify w hw
                · intro lay hsmall
                  rw [hc lay (by omega), List.getD_append previous.counters [counter] 0 lay.val (by omega)]
                · rw [hh, List.getD_append previous.lows [low] true 0 (by omega)]
      · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

/-- The paired table selector is exactly the canonical A leaf position. -/
theorem physicalFromOutput_first (output : HashOutput) (pair : Fin 4) :
    physicalChildFromOutput output ⟨2 * pair.val, by have := pair.isLt; omega⟩ =
      firstChild ((forestSelectionFromOutput output).pairs pair) := by
  apply Fin.ext
  fin_cases pair <;>
    simp [physicalChildFromOutput, firstCoord, physicalChild, rawChildFromOutput, rawChildBase,
      forestSelectionFromOutput, selectionFromOutput, firstChild] <;> omega

/-- The rotated B selector shares A's branch and retains six independent path bits. -/
theorem physicalFromOutput_second (output : HashOutput) (pair : Fin 4) :
    physicalChildFromOutput output ⟨2 * pair.val + 1, by have := pair.isLt; omega⟩ =
      secondChild ((forestSelectionFromOutput output).pairs pair) := by
  apply Fin.ext
  fin_cases pair <;>
    simp [physicalChildFromOutput, firstCoord, physicalChild, rawChildFromOutput, rawChildBase,
      forestSelectionFromOutput, selectionFromOutput, secondChild] <;> omega

theorem physicalFromOutput_singleton (output : HashOutput) :
    physicalChildFromOutput output 8 = (forestSelectionFromOutput output).singleton := by
  rfl

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem mainSignature_fill (sig : Signature) (c : Nat) :
    mainSignature (fillTopSignature sig c) = fillTop (mainSignature sig) c := rfl

theorem topFold_fill_signature (sig : Signature) (index : Nat) (digits : List Nat) (c : Nat) :
    topFold (mainSignature (fillTopSignature sig c)) index digits =
      topFold (mainSignature sig) index digits := by
  rw [mainSignature_fill]
  have h := topFold_fill (mainSignature sig) index digits c
    ((topSib (mainSignature sig)).toNat / 2 ^ 112)
  rw [fillTop_self] at h
  exact h

theorem topFoldN_fill_signature (sig : Signature) (index : Nat) (digits : List Nat) (c : Nat) :
    topFoldN (mainSignature (fillTopSignature sig c)) index digits =
      topFoldN (mainSignature sig) index digits := by
  rw [mainSignature_fill]
  have h := topFoldN_fill (mainSignature sig) index digits c
    ((topSib (mainSignature sig)).toNat / 2 ^ 112)
  rw [fillTop_self] at h
  exact h

theorem recoverHintedLayers_fill (sig : Signature) (index : Nat) (other : Digest) (c : Nat) :
    ∀ n, n ≤ 4 → ∀ msg,
      recoverHintedLayers (fillTopSignature sig c) index other n msg =
        recoverHintedLayers sig index other n msg := by
  intro n
  induction n with
  | zero => intro _ msg; rfl
  | succ n ih =>
      intro hn msg
      simp only [recoverHintedLayers, hints_retained]
      apply bind_congr
      intro found
      cases found with
      | none => rfl
      | some found =>
          obtain ⟨counter, digits, low⟩ := found
          cases n with
          | zero =>
              simp only [if_true, topFoldN_fill_signature]
          | succ k =>
              have hne := fin_ofNat_succ_ne k (by omega)
              simp only [Nat.succ_ne_zero, if_false, mainSignature_fill,
                recoverLayerPair_fill _ _ _ _ _ hne]
              apply bind_congr
              intro pair
              rw [ih (by omega)]

theorem eval_recoverHintedLayers_other (answers : Answers) (sig : Signature)
    (index : Nat) (other other' : Digest) :
    ∀ n msg, evalWithAnswerFn answers (recoverHintedLayers sig index other' n msg) =
      (evalWithAnswerFn answers (recoverHintedLayers sig index other n msg)).map
        (fun result => {result with root := evalWithAnswerFn answers (topNode index result.foldedTop other')}) := by
  intro n
  induction n with
  | zero => intro msg; simp [recoverHintedLayers]
  | succ n ih =>
      intro msg
      simp only [recoverHintedLayers, evalWithAnswerFn_bind]
      split
      ·
          rename_i counter digits low _
          by_cases hn : n = 0
          · simp [hn]
          · simp only [hn, if_false, evalWithAnswerFn_bind, ih]
            cases evalWithAnswerFn answers (recoverHintedLayers sig index other n _) with
            | none => simp
            | some previous => simp
      · simp

theorem sharedDigestSearch_some (answers : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter found output, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers (sharedDigestSearch rho message counter fuel) = some (found, output) →
      counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧ digestAccepted output = true ∧
        evalWithAnswerFn answers (digest rho message found) = output := by
  intro fuel
  induction fuel with
  | zero => intro counter found output _ he; simp [sharedDigestSearch] at he
  | succ fuel ih =>
      intro counter found output hlimit he
      simp only [sharedDigestSearch, evalWithAnswerFn_bind] at he
      split_ifs at he with hg
      · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hc : (BitVec.ofNat 32 counter).toNat = counter := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact ⟨by rw [hc], by rw [hc]; omega, hg, rfl⟩
      · obtain ⟨hlo, hhi, hg, ho⟩ := ih (counter + 1) found output (by omega) he
        exact ⟨by omega, by omega, hg, ho⟩

theorem verify_from_recovered (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (counter : BitVec 32) (output : HashOutput) (result : RecoveredLayers)
    (ho : evalWithAnswerFn answers (digest sig.rho message counter) = output)
    (ha : verifyDigestAccepted output = true)
    (hr : evalWithAnswerFn answers (recoverHintedLayers sig (digestIndex output)
      ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
        (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) = some result)
    (hpk : result.root = pk) :
    evalWithAnswerFn answers (verify message pk
      ⟨sig, counter, fun lay => result.counters.getD lay.val 0, !(result.lows.getD 0 true), result.nonces⟩) = true := by
  have hc : ¬counter.toNat ≥ digestVerifyWindow := Nat.not_le.mpr counter.isLt
  have hv := (recoverHintedLayers_verified answers sig (digestIndex output) 4 le_rfl _ _ hr).2.2.2
    ⟨sig, counter, fun lay => result.counters.getD lay.val 0, !(result.lows.getD 0 true), result.nonces⟩ rfl (by intros; rfl) rfl
  simp only [verify, hc, if_false, evalWithAnswerFn_bind, ho, ha, Bool.not_true,
    Bool.false_eq_true, hv, evalWithAnswerFn_pure, hpk, beq_self_eq_true]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The forest commitment depends only on the signing index and oracle answers;
selector and rank choices determine its opening, but not its value. -/
def forestCommitment (answers : Answers) (index : Nat) : PairRoot :=
  let first := expectedPairRoot answers index 0 ftsStart
  let second := expectedPairRoot answers index 1 first
  let third := expectedPairRoot answers index 2 second
  let fourth := expectedPairRoot answers index 3 third
  let nodes := sharedNodes answers false index 8 (fun _ => fourth)
  (nodes.getD 2 0, nodes.getD 3 0)

attribute [local irreducible] sharedNodes

theorem buildForest_commitment (answers : Answers) (index : Nat)
    (selected : ForestSelection) (words : ForestWords) :
    (evalWithAnswerFn answers (buildForest index selected words)).2 = forestCommitment answers index := by
  have hfour : List.finRange 4 = [0, 1, 2, 3] := by decide
  simp only [buildForest, hfour, List.foldlM_cons, List.foldlM_nil,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, buildPair_result,
    buildSingleton, buildSharedCoordinate_result]
  rfl

theorem recoverForest_commitment (answers : Answers) (index : Nat)
    (selected : ForestSelection) (words : ForestWords) :
    evalWithAnswerFn answers (recoverForest index selected words
      (evalWithAnswerFn answers (buildForest index selected words)).1) = forestCommitment answers index :=
  (recoverForest_honest answers index selected words).trans (buildForest_commitment answers index selected words)

def fixedPrepared (answers : Answers) (index : Nat) (lay : Layer) : PreparedLower :=
  ⟨(wotsTree answers lay (route index lay).2).take (height lay),
    prefixRows answers lay (route index lay).2 (route index lay).1⟩

theorem prepareRoots_result (answers : Answers) (index : Nat) :
    evalWithAnswerFn answers (prepareRoots index) =
      ⟨fixedPrepared answers index 1, fixedPrepared answers index 2, fixedPrepared answers index 3⟩ := by
  simp only [prepareRoots, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [eval_buildTreePrefixes_result answers (by decide) _ _ (route_leaf_bound index 1),
    eval_buildTreePrefixes_result answers (by decide) _ _ (route_leaf_bound index 2),
    eval_buildTreePrefixes_result answers (by decide) _ _ (route_leaf_bound index 3)]
  rfl

theorem fixedPrepared_pair (answers : Answers) (index : Nat) (lay : Layer) :
    topPair lay (fixedPrepared answers index lay).levels = builtPair answers lay (route index lay).2 :=
  topPair_take lay _

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem topPath_fill_signature (sig : Signature) (c : Nat) :
    ((fillTopSignature sig c).layers 0).path topJ = setTop ((sig.layers 0).path topJ) c :=
  topSib_fillTop (mainSignature sig) c

theorem expandFill_verified (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (expandFill message pk sig) = some w) :
    evalWithAnswerFn answers (verify message pk w) = true := by
  unfold expandFill at he
  by_cases hh : sig.policyHints.toNat ≥ 7744
  · simp only [hh, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he
  simp only [hh, if_false, evalWithAnswerFn_bind] at he
  let sig0 := fillTopSignature sig 0
  cases hd : evalWithAnswerFn answers (sharedDigestSearch sig0.rho message 0 digestAttemptLimit) with
  | none =>
      dsimp only [sig0] at hd
      simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      have hdlim : 0 + digestAttemptLimit ≤ 2 ^ 32 := by simpa using digestAttemptLimit_le
      obtain ⟨_, _, haccept, houtput⟩ := sharedDigestSearch_some answers sig0.rho message
        digestAttemptLimit 0 counter output hdlim hd
      have ha := digestAccepted_implies_verify haccept
      dsimp only [sig0] at hd
      simp only [hd, evalWithAnswerFn_bind] at he
      let index := digestIndex output
      let forest := evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
        (forestWordsFromOutput output) sig0.forest)
      cases hr : evalWithAnswerFn answers (recoverHintedLayers sig0 index ((sig0.layers 0).path topJ)
        4 (.pair forest.1 forest.2)) with
      | none =>
          dsimp only [index, forest, sig0] at hr
          simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some result =>
          dsimp only [index, forest, sig0] at hr
          simp only [hr] at he
          cases hp : policyHintsValid sig0.policyHints result.digits result.lows with
          | false =>
              dsimp only [sig0] at hp
              simp only [hp, Bool.not_false, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he
          | true =>
              dsimp only [sig0] at hp
              simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at he
              by_cases hpk : result.root = pk
              · simp only [hpk, if_true, evalWithAnswerFn_pure, Option.some.injEq] at he
                subst w
                exact verify_from_recovered answers message pk sig0 counter output result houtput ha hr hpk
              · simp only [hpk, if_false, evalWithAnswerFn_bind] at he
                cases hs : evalWithAnswerFn answers
                  (searchTop index result.foldedTop ((sig0.layers 0).path topJ) pk searchFuel 1) with
                | none =>
                    dsimp only [index, sig0] at hs
                    simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
                | some c =>
                    dsimp only [index, sig0] at hs
                    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
                    subst w
                    have hc := (eval_searchTop answers index result.foldedTop ((sig0.layers 0).path topJ)
                      pk searchFuel 1 c hs).2.2
                    let completed : RecoveredLayers := {result with
                      root := evalWithAnswerFn answers
                        (topNode index result.foldedTop (((fillTopSignature sig0 c).layers 0).path topJ))}
                    have hcompleted : completed.root = pk := by
                      dsimp only [completed]
                      rw [topPath_fill_signature]
                      exact hc
                    have hr' : evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig0 c) index
                        (((fillTopSignature sig0 c).layers 0).path topJ) 4 (.pair forest.1 forest.2)) =
                        some completed := by
                      rw [recoverHintedLayers_fill _ _ _ _ _ le_rfl]
                      rw [eval_recoverHintedLayers_other answers sig0 index ((sig0.layers 0).path topJ)]
                      rw [hr]
                      rfl
                    exact verify_from_recovered answers message pk (fillTopSignature sig0 c)
                      counter output completed houtput ha hr' hcompleted

theorem expand_verified (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (expand message pk sig) = some w) :
    evalWithAnswerFn answers (verify message pk w) = true :=
  expandFill_verified answers message pk (normTop sig) w he

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def preparedResidual1 (result : CanonicalLayers) : Nat :=
  CanonicalPolicy.nextResidual (CanonicalPolicy.totalCredit) 0 (result.lows.getD 0 true) (result.digits.getD 0 [])

def preparedResidual2 (result : CanonicalLayers) : Nat :=
  CanonicalPolicy.nextResidual (preparedResidual1 result) 1 (result.lows.getD 1 true) (result.digits.getD 1 [])

def preparedResidual3 (result : CanonicalLayers) : Nat :=
  CanonicalPolicy.nextResidual (preparedResidual2 result) 2 (result.lows.getD 2 true) (result.digits.getD 2 [])

/-- The successful source program exposes exactly the four canonical searches,
with every lower threshold determined by its already selected ancestors. -/
structure PreparedSearchFacts (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) (result : CanonicalLayers) : Prop where
  pieces_length : result.pieces.length = 4
  counters_length : result.counters.length = 4
  digits_length : result.digits.length = 4
  lows_length : result.lows.length = 4
  search0 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 0
    (CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit) (route index 0).2 (route index 0).1
    (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2) 0 (searchLimit 0)) =
      some (result.counters.getD 0 0, result.digits.getD 0 [], result.lows.getD 0 true)
  search1 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 1
    (CanonicalPolicy.threshold 1 (preparedResidual1 result)) (route index 1).2 (route index 1).1
    (.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2) 0 (searchLimit 1)) =
      some (result.counters.getD 1 0, result.digits.getD 1 [], result.lows.getD 1 true)
  search2 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 2
    (CanonicalPolicy.threshold 2 (preparedResidual2 result)) (route index 2).2 (route index 2).1
    (.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2) 0 (searchLimit 2)) =
      some (result.counters.getD 2 0, result.digits.getD 2 [], result.lows.getD 2 true)
  search3 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 3
    (CanonicalPolicy.threshold 3 (preparedResidual3 result)) (route index 3).2 (route index 3).1
    (.pair (forest).1 (forest).2) 0 (searchLimit 3)) =
      some (result.counters.getD 3 0, result.digits.getD 3 [], result.lows.getD 3 true)
  floor1_lt : CanonicalPolicy.threshold 1 (preparedResidual1 result) < 16
  floor2_lt : CanonicalPolicy.threshold 2 (preparedResidual2 result) < 22
  floor3_lt : CanonicalPolicy.threshold 3 (preparedResidual3 result) < 22
  residual_eq : result.residual = CanonicalPolicy.nextResidual (preparedResidual3 result) 3
    (result.lows.getD 3 true) (result.digits.getD 3 [])
  hints_eq : result.policyHints = BitVec.ofNat 16
    (484 * CanonicalPolicy.threshold 1 (preparedResidual1 result) +
     22 * CanonicalPolicy.threshold 2 (preparedResidual2 result) +
     CanonicalPolicy.threshold 3 (preparedResidual3 result))
  pieces_eq : result.pieces = [
    evalWithAnswerFn answers (signTop cache (route index 0).1 (result.digits.getD 0 [])),
    preparedPieces 1 (route index 1).1 prepared.one (result.digits.getD 1 []),
    preparedPieces 2 (route index 2).1 prepared.two (result.digits.getD 2 []),
    preparedPieces 3 (route index 3).1 prepared.three (result.digits.getD 3 [])]

theorem searchPreparedLayers_some (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) (result : CanonicalLayers)
    (he : evalWithAnswerFn answers (searchPreparedLayers cache index prepared forest) = some result) :
    PreparedSearchFacts answers cache index prepared forest result := by
  unfold searchPreparedLayers at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs0 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 0
    (CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit) (route index 0).2 (route index 0).1
    (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2) 0 (searchLimit 0)) with
  | none => simp only [hs0, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found0 =>
      obtain ⟨c0, d0, l0⟩ := found0
      simp only [hs0, evalWithAnswerFn_bind] at he
      let r1 := CanonicalPolicy.nextResidual CanonicalPolicy.totalCredit 0 l0 d0
      let f1 := CanonicalPolicy.threshold 1 r1
      by_cases hf1 : f1 ≥ 16
      · dsimp only [r1, f1] at hf1
        simp only [hf1, if_true,
          evalWithAnswerFn_pure, reduceCtorEq] at he
      dsimp only [r1, f1] at hf1
      simp only [hf1, if_false,
        evalWithAnswerFn_bind] at he
      cases hs1 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 1
        f1 (route index 1).2 (route index 1).1
        (.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2) 0 (searchLimit 1)) with
      | none =>
          dsimp only [r1, f1] at hs1
          simp only [hs1, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some found1 =>
          obtain ⟨c1, d1, l1⟩ := found1
          dsimp only [r1, f1] at hs1
          simp only [hs1, evalWithAnswerFn_bind] at he
          let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
          let f2 := CanonicalPolicy.threshold 2 r2
          by_cases hf2 : f2 ≥ 22
          · dsimp only [r1, f1, r2, f2] at hf2
            simp only [hf2, if_true,
              evalWithAnswerFn_pure, reduceCtorEq] at he
          dsimp only [r1, f1, r2, f2] at hf2
          simp only [hf2, if_false,
            evalWithAnswerFn_bind] at he
          cases hs2 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 2
            f2 (route index 2).2 (route index 2).1
            (.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2) 0 (searchLimit 2)) with
          | none =>
              dsimp only [r1, f1, r2, f2] at hs2
              simp only [hs2, evalWithAnswerFn_pure, reduceCtorEq] at he
          | some found2 =>
              obtain ⟨c2, d2, l2⟩ := found2
              dsimp only [r1, f1, r2, f2] at hs2
              simp only [hs2, evalWithAnswerFn_bind] at he
              let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
              let f3 := CanonicalPolicy.threshold 3 r3
              by_cases hf3 : f3 ≥ 22
              · dsimp only [r1, f1, r2, f2, r3, f3] at hf3
                simp only [hf3, if_true,
                  evalWithAnswerFn_pure, reduceCtorEq] at he
              dsimp only [r1, f1, r2, f2, r3, f3] at hf3
              simp only [hf3, if_false,
                evalWithAnswerFn_bind] at he
              cases hs3 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 3
                f3 (route index 3).2 (route index 3).1
                (.pair (forest).1 (forest).2) 0 (searchLimit 3)) with
              | none =>
                  dsimp only [r1, f1, r2, f2, r3, f3] at hs3
                  simp only [hs3, evalWithAnswerFn_pure, reduceCtorEq] at he
              | some found3 =>
                  obtain ⟨c3, d3, l3⟩ := found3
                  dsimp only [r1, f1, r2, f2, r3, f3] at hs3
                  simp only [hs3, evalWithAnswerFn_bind] at he
                  simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
                  subst result
                  constructor
                  · rfl
                  · rfl
                  · rfl
                  · rfl
                  · exact hs0
                  · exact hs1
                  · exact hs2
                  · exact hs3
                  · exact Nat.lt_of_not_ge hf1
                  · exact Nat.lt_of_not_ge hf2
                  · exact Nat.lt_of_not_ge hf3
                  · rfl
                  · rfl
                  · rfl

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoverLayerPair_wotsPieces (answers : Answers) (sig : Signature) (index : Nat)
    (lay : Layer) (hl : lay ≠ 0) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (hpieces : sig.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 digits)) :
    evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index lay digits) =
      builtPair answers lay (route index lay).2 := by
  apply eval_recoverLayerPair_honest answers (mainSignature sig) index lay hl digits hvalid
  · intro i
    change (sig.layers lay).values i = _
    rw [hpieces]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, i.isLt]
  · intro j
    change (sig.layers lay).path j = _
    rw [hpieces]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, j.isLt]

theorem topNode_wotsPieces (answers : Answers) (sig : Signature) (index : Nat)
    (hindex : index < 2 ^ 31) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (hpieces : sig.layers 0 = piecesSignature 0
      (wotsPieces answers 0 (route index 0).2 (route index 0).1 digits)) :
    evalWithAnswerFn answers (topNode index
      (evalWithAnswerFn answers (topFoldN (mainSignature sig) index digits)).1
      ((sig.layers 0).path topJ)) = treeValue (builtTree answers 0 0) 12 0 := by
  have ht : (route index 0).2 = 0 := route_top_tree index hindex
  have hp : sig.layers 0 = piecesSignature 0 (honestPieces answers 0 0 (route index 0).1 digits) := by
    rw [hpieces, ht, wotsPieces_top]
  exact eval_topNode_topFoldN_honest answers (mainSignature sig) index hindex digits hvalid
    (fun i => by
      change (sig.layers 0).values i = _
      rw [hp]
      simp [piecesSignature, honestPieces, List.getD_eq_getElem, i.isLt])
    (fun j => by
      change (sig.layers 0).path j = _
      rw [hp]
      simp [piecesSignature, honestPieces, List.getD_eq_getElem, j.isLt])

theorem recoverHintedLayers_replay (answers : Answers) (sig : Signature) (index : Nat)
    (other : Digest) (forest : PairRoot)
    (counter : Layer → BitVec 32) (digits : Layer → List Nat) (lows : Layer → Bool)
    (hs : ∀ lay, evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay
      (hintFloor sig.policyHints lay) (route index lay).2 (route index lay).1
      (if lay = 3 then .pair forest.1 forest.2 else
        let lower : Layer := Fin.ofNat 4 (lay.val + 1)
        .pair (builtPair answers lower (route index lower).2).1
          (builtPair answers lower (route index lower).2).2)
      0 (searchLimit lay)) = some (counter lay, digits lay, lows lay))
    (hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (digits lay)) =
      builtPair answers lay (route index lay).2) :
    evalWithAnswerFn answers (recoverHintedLayers sig index other 4 (.pair forest.1 forest.2)) =
      some ⟨(evalWithAnswerFn answers (topFoldN (mainSignature sig) index (digits 0))).1,
        evalWithAnswerFn answers (topNode index
          (evalWithAnswerFn answers (topFoldN (mainSignature sig) index (digits 0))).1 other),
        [counter 0, counter 1, counter 2, counter 3],
        [digits 0, digits 1, digits 2, digits 3],
        [lows 0, lows 1, lows 2, lows 3],
        (evalWithAnswerFn answers (topFoldN (mainSignature sig) index (digits 0))).2⟩ := by
  have hs0 := hs 0
  have hs1 := hs 1
  have hs2 := hs 2
  have hs3 := hs 3
  have hp1 := hp 1 (by decide)
  have hp2 := hp 2 (by decide)
  have hp3 := hp 3 (by decide)
  simp only [show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
    show (2 : Layer) ≠ 3 by decide, if_false, if_true,
    show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
    show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
    show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl] at hs0 hs1 hs2 hs3
  simp only [recoverHintedLayers, evalWithAnswerFn_bind,
    show (Fin.ofNat 4 0 : Layer) = 0 from rfl,
    show (Fin.ofNat 4 1 : Layer) = 1 from rfl,
    show (Fin.ofNat 4 2 : Layer) = 2 from rfl,
    show (Fin.ofNat 4 3 : Layer) = 3 from rfl,
    hs0, hs1, hs2, hs3, hp1, hp2, hp3,
    Nat.reduceEqDiff, if_false, if_true, evalWithAnswerFn_pure]
  rfl

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem layer_four_cases (lay : Layer) : lay = 0 ∨ lay = 1 ∨ lay = 2 ∨ lay = 3 := by
  fin_cases lay <;> decide

@[simp] theorem layer_val_0 : (0 : Layer).val = 0 := rfl
@[simp] theorem layer_val_1 : (1 : Layer).val = 1 := rfl
@[simp] theorem layer_val_2 : (2 : Layer).val = 2 := rfl
@[simp] theorem layer_val_3 : (3 : Layer).val = 3 := rfl

theorem PreparedSearchFacts.validDigits {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result) (lay : Layer) :
    Cost.ValidDigits lay (result.digits.getD lay.val []) := by
  rcases layer_four_cases lay with rfl | rfl | rfl | rfl
  · exact (canonical_search_valid_credit answers 0 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (0 : Layer); unfold counterLimit at hb; omega) h.search0).1
  · exact (canonical_search_valid_credit answers 1 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (1 : Layer); unfold counterLimit at hb; omega) h.search1).1
  · exact (canonical_search_valid_credit answers 2 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (2 : Layer); unfold counterLimit at hb; omega) h.search2).1
  · exact (canonical_search_valid_credit answers 3 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (3 : Layer); unfold counterLimit at hb; omega) h.search3).1

theorem PreparedSearchFacts.hints_spec {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result) :
    result.policyHints.toNat < 7744 ∧
      hintFloor result.policyHints 1 = CanonicalPolicy.threshold 1 (preparedResidual1 result) ∧
      hintFloor result.policyHints 2 = CanonicalPolicy.threshold 2 (preparedResidual2 result) ∧
      hintFloor result.policyHints 3 = CanonicalPolicy.threshold 3 (preparedResidual3 result) := by
  rw [h.hints_eq]
  exact encodedHints_spec _ _ _ h.floor1_lt h.floor2_lt h.floor3_lt

theorem PreparedSearchFacts.hints_valid {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result) :
    policyHintsValid result.policyHints result.digits result.lows = true := by
  simp only [policyHintsValid, decide_eq_true_eq]
  exact ⟨h.hints_spec.1, h.digits_length, h.hints_spec.2⟩

theorem preparedPieces_fixed (answers : Answers) (index : Nat) {lay : Layer}
    (hlay : lay ≠ 0) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits) :
    preparedPieces lay (route index lay).1 (fixedPrepared answers index lay) digits =
      wotsPieces answers lay (route index lay).2 (route index lay).1 digits := by
  have h := preparedPieces_result answers hlay (route index lay).2 (route index lay).1
    digits hvalid (route_leaf_bound index lay)
  rw [eval_buildTreePrefixes_result answers hlay _ _ (route_leaf_bound index lay)] at h
  exact h

theorem PreparedSearchFacts.honest_pieces {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index (evalWithAnswerFn answers (prepareRoots index)) forest result)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (hindex : index < 2 ^ 31)
    (lay : Layer) :
    result.pieces.getD lay.val ([], []) =
      wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val []) := by
  have hv := h.validDigits lay
  rw [h.pieces_eq, prepareRoots_result]
  rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
    simp only [layer_val_0, layer_val_1, layer_val_2, layer_val_3] at hv ⊢
  · simp only [Fin.val_zero, List.getD_cons_zero]
    rw [eval_signTop_honest answers cache _ _ hcache (route_leaf_bound index 0) hv,
      route_top_tree index hindex, wotsPieces_top]
  · simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      preparedPieces_fixed answers index (lay := 1) (by decide) _ hv
  · simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      preparedPieces_fixed answers index (lay := 2) (by decide) _ hv
  · simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      preparedPieces_fixed answers index (lay := 3) (by decide) _ hv

theorem list_four_getD {α : Type} (xs : List α) (zero : α) (hlen : xs.length = 4) :
    [xs.getD 0 zero, xs.getD 1 zero, xs.getD 2 zero, xs.getD 3 zero] = xs := by
  apply List.ext_getElem (by simpa using hlen.symm)
  intro i hi hj
  have hi4 : i < 4 := by simpa using hi
  interval_cases i <;> simp_all [List.getD_eq_getElem]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem PreparedSearchFacts.recover_honest {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index (evalWithAnswerFn answers (prepareRoots index)) forest result)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (hindex : index < 2 ^ 31)
    (sig : Signature) (hhints : sig.policyHints = result.policyHints)
    (hpieces : ∀ lay, sig.layers lay = piecesSignature lay (result.pieces.getD lay.val ([], []))) :
    ∃ folded nonces, evalWithAnswerFn answers (recoverHintedLayers sig index ((sig.layers 0).path topJ)
      4 (.pair forest.1 forest.2)) = some ⟨folded,
        treeValue (builtTree answers 0 0) 12 0, result.counters, result.digits, result.lows, nonces⟩ := by
  have hpiece : ∀ lay, sig.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val [])) := by
    intro lay
    rw [hpieces lay, h.honest_pieces hcache hindex lay]
  have hs0 := h.search0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  simp only [prepareRoots_result, fixedPrepared_pair] at hs0 hs1 hs2
  have hs : ∀ lay, evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay
      (hintFloor sig.policyHints lay) (route index lay).2 (route index lay).1
      (if lay = 3 then .pair forest.1 forest.2 else
        let lower : Layer := Fin.ofNat 4 (lay.val + 1)
        .pair (builtPair answers lower (route index lower).2).1
          (builtPair answers lower (route index lower).2).2)
      0 (searchLimit lay)) = some (result.counters.getD lay.val 0, result.digits.getD lay.val [],
        result.lows.getD lay.val true) := by
    intro lay
    rw [hhints]
    rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
      simp only [layer_val_0, layer_val_1, layer_val_2, layer_val_3,
        show (Fin.ofNat 4 1 : Layer) = 1 from rfl,
        show (Fin.ofNat 4 2 : Layer) = 2 from rfl,
        show (Fin.ofNat 4 3 : Layer) = 3 from rfl, Nat.reduceAdd, show (0 : Layer) ≠ 3 by decide,
        show (1 : Layer) ≠ 3 by decide, show (2 : Layer) ≠ 3 by decide, if_false, if_true]
    · exact hs0
    · simpa only [h.hints_spec.2.1] using hs1
    · simpa only [h.hints_spec.2.2.1] using hs2
    · simpa only [h.hints_spec.2.2.2] using hs3
  have hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (result.digits.getD lay.val [])) =
      builtPair answers lay (route index lay).2 := by
    intro lay hl
    exact recoverLayerPair_wotsPieces answers sig index lay hl _ (h.validDigits lay) (hpiece lay)
  have hr := recoverHintedLayers_replay answers sig index ((sig.layers 0).path topJ) forest
    (fun lay => result.counters.getD lay.val 0) (fun lay => result.digits.getD lay.val [])
    (fun lay => result.lows.getD lay.val true) hs hp
  simp only [layer_val_0, layer_val_1, layer_val_2, layer_val_3] at hr
  have ht := topNode_wotsPieces answers sig index hindex _ (h.validDigits 0) (hpiece 0)
  simp only [layer_val_0] at ht
  rw [ht,
    list_four_getD result.counters 0 h.counters_length,
    list_four_getD result.digits [] h.digits_length,
    list_four_getD result.lows true h.lows_length] at hr
  exact ⟨_, _, hr⟩

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem expand_complete_of_recovered (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (counter : BitVec 32) (output : HashOutput) (result : RecoveredLayers)
    (hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) =
      some (counter, output))
    (hr : evalWithAnswerFn answers (recoverHintedLayers sig (digestIndex output)
      ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
        (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) = some result)
    (hh : policyHintsValid sig.policyHints result.digits result.lows = true) (hpk : result.root = pk)
    (htop : TopPathOK sig) :
    ∃ w, evalWithAnswerFn answers (expand message pk sig) = some w := by
  have hhbound' : sig.policyHints.toNat < 2 ^ 13 := by
    simp only [policyHintsValid, decide_eq_true_eq] at hh
    have := hh.1
    omega
  rw [expand_eq_expandFill message pk sig hhbound' htop]
  have hhbound : sig.policyHints.toNat < 7744 := by
    simp only [policyHintsValid, decide_eq_true_eq] at hh
    exact hh.1
  let index := digestIndex output
  let forest := evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) sig.forest)
  let sig0 := fillTopSignature sig 0
  let result0 : RecoveredLayers := {result with
    root := evalWithAnswerFn answers (topNode index result.foldedTop ((sig0.layers 0).path topJ))}
  have hr0 : evalWithAnswerFn answers (recoverHintedLayers sig0 index
      ((sig0.layers 0).path topJ) 4 (.pair forest.1 forest.2)) = some result0 := by
    dsimp only [sig0]
    rw [recoverHintedLayers_fill _ _ _ _ _ le_rfl,
      eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)]
    rw [hr]
    rfl
  have hroot : evalWithAnswerFn answers (topNode index result.foldedTop ((sig.layers 0).path topJ)) = pk := by
    have he := eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)
      ((sig.layers 0).path topJ) 4 (.pair forest.1 forest.2)
    rw [hr] at he
    simp only [Option.map_some, Option.some.injEq] at he
    have he' := congrArg RecoveredLayers.root he
    exact he'.symm.trans hpk
  unfold expandFill
  simp only [show ¬sig.policyHints.toNat ≥ 7744 by omega, if_false, evalWithAnswerFn_bind]
  simp only [nonce_retained, hd, evalWithAnswerFn_bind]
  dsimp only [sig0, index, forest] at hr0
  simp only [show (fillTopSignature sig 0).forest = sig.forest from rfl]
  rw [hr0]
  simp only [result0, sig0, hints_retained, hh, Bool.not_true, Bool.false_eq_true, if_false]
  by_cases hzero : result0.root = pk
  · dsimp only [result0, sig0] at hzero
    rw [if_pos hzero, evalWithAnswerFn_pure]
    exact ⟨_, rfl⟩
  · have hz : evalWithAnswerFn answers (topNode index result.foldedTop ((sig0.layers 0).path topJ)) ≠ pk := hzero
    have hcompletion : evalWithAnswerFn answers (topNode index result.foldedTop
        (setTop ((sig0.layers 0).path topJ) (((sig.layers 0).path topJ).toNat / 2 ^ 112))) = pk := by
      rw [topPath_fill_signature, setTop_setTop, setTop_self]
      exact hroot
    have hn : ((sig.layers 0).path topJ).toNat / 2 ^ 112 ≠ 0 := by
      intro he
      rw [he, topPath_fill_signature, setTop_setTop] at hcompletion
      exact hz hcompletion
    obtain ⟨c, hc⟩ := searchTop_complete answers index result.foldedTop ((sig0.layers 0).path topJ)
      pk searchFuel 1 (((sig.layers 0).path topJ).toNat / 2 ^ 112) (by omega)
      (by have ht := top_lt ((sig.layers 0).path topJ); unfold searchFuel; omega) hcompletion
    dsimp only [sig0] at hz
    dsimp only [sig0, index] at hc
    rw [if_neg hz, evalWithAnswerFn_bind, hc, evalWithAnswerFn_pure]
    exact ⟨_, rfl⟩

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_recovery (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    w.signature.rho = rho ∧ ∃ result : RecoveredLayers,
      evalWithAnswerFn answers (recoverHintedLayers w.signature (digestIndex output)
        ((w.signature.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1
          (evalWithAnswerFn answers (recoverForest (digestIndex output)
            (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2)) = some result ∧
      result.root = treeValue (builtTree answers 0 0) 12 0 ∧
      policyHintsValid w.signature.policyHints result.digits result.lows = true ∧
      w.topHigh = !(result.lows.getD 0 true) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (buildForest index
    (forestSelectionFromOutput output) (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots index)
  unfold signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache index prepared built.2) with
  | none =>
      dsimp only [index, prepared, built] at hs
      simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some layers =>
      have hf := searchPreparedLayers_some answers cache index prepared built.2 layers hs
      dsimp only [index, prepared, built] at hs
      simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
      subst w
      let sig : Signature := ⟨rho, layers.policyHints, built.1,
        fun lay => piecesSignature lay (layers.pieces.getD lay.val ([], []))⟩
      obtain ⟨folded, nonces, hr⟩ := hf.recover_honest hcache (digestIndex_lt output) sig rfl (by intro lay; rfl)
      refine ⟨rfl, ⟨folded, _, layers.counters, layers.digits, layers.lows, nonces⟩, ?_, rfl, hf.hints_valid, rfl⟩
      change evalWithAnswerFn answers (recoverHintedLayers sig index ((sig.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1)).1
          (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
            (forestWordsFromOutput output) built.1)).2)) = _
      have hforest : evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1) = built.2 :=
        recoverForest_honest answers index _ _
      rw [hforest]
      exact hr

/-- img-v6 completeness event: every node of the keygen top tree (heights 1..11) passes its zero test, i.e. no
top nonce search hit its cap (probability ≥ 1 − 2^−143). -/
def TopTreeOK (answers : Answers) : Prop :=
  ∀ j : Nat, 1 ≤ j → j ≤ 11 → ∀ i, i < 2 ^ (12 - j) →
    topZeroOk j (treeValue (builtTree answers 0 0) j i) = true

theorem route0_tree (index : Nat) (h : index < 2 ^ 31) : (route index 0).2 = 0 := by
  simp only [route]
  apply Nat.div_eq_of_lt
  simpa [height] using h

theorem route0_leaf_lt (index : Nat) : (route index 0).1 < 2 ^ 12 := by
  simp only [route]
  exact Nat.mod_lt _ (by simp [height])

theorem sibling_lt (leaf j : Nat) (hleaf : leaf < 2 ^ 12) (hj : j ≤ 11) : leaf / 2 ^ j ^^^ 1 < 2 ^ (12 - j) := by
  apply Nat.xor_lt_two_pow
  · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 12 - j + j = 12 by omega]
    exact hleaf
  · exact Nat.one_lt_two_pow (by omega)

/-- The signer's top path node at height `j` is the keygen's node next to the signed leaf's ancestor. -/
theorem signFromOutput_path (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) (j : Fin (height 0)) :
    (w.signature.layers 0).path j =
      treeValue (builtTree answers 0 0) j.val ((route (digestIndex output) 0).1 / 2 ^ j.val ^^^ 1) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (buildForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots index)
  unfold signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache index prepared built.2) with
  | none =>
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some layers =>
    have hf := searchPreparedLayers_some answers cache index prepared built.2 layers hs
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
    subst w
    have hp := hf.honest_pieces hcache (digestIndex_lt output) 0
    change (piecesSignature 0 (layers.pieces.getD (0 : Layer).val ([], []))).path j = _
    have hj : j.val < 12 := j.isLt
    rw [hp, route0_tree _ (digestIndex_lt output)]
    simp [piecesSignature, wotsPieces, wotsTree_top, height, index, hj]

theorem signFromOutput_topPathOK (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (htree : TopTreeOK answers) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    TopPathOK w.signature := by
  intro j hj
  have hj11 : j.val ≤ 11 := Nat.le_of_lt_succ j.isLt
  rw [signFromOutput_path answers cache hcache rho counter output w he j]
  exact htree j.val hj hj11 _ (sibling_lt _ _ (route0_leaf_lt _) hj11)

theorem signPayload_expands (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (htree : TopTreeOK answers)
    (message : Message) (sig : Signature)
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) :
    ∃ w, evalWithAnswerFn answers (expand message (treeValue (builtTree answers 0 0) 12 0) sig) = some w ∧
      evalWithAnswerFn answers (verify message (treeValue (builtTree answers 0 0) 12 0) w) = true := by
  unfold signPayload at he
  simp only [evalWithAnswerFn_bind] at he
  let rho := evalWithAnswerFn answers (privateNonce message)
  cases hd : evalWithAnswerFn answers (sharedDigestSearch rho message 0 digestAttemptLimit) with
  | none =>
      dsimp only [rho] at hd
      simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      dsimp only [rho] at hd
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (signFromOutput cache rho counter output) with
      | none =>
          dsimp only [rho] at hs
          simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some original =>
          have hh := signFromOutput_recovery answers cache hcache rho counter output original hs
          have htop := signFromOutput_topPathOK answers cache hcache htree rho counter output original hs
          dsimp only [rho] at hs
          simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
          subst sig
          obtain ⟨hrho, result, hr, hpk, hp, _⟩ := hh
          have hd' : evalWithAnswerFn answers
              (sharedDigestSearch original.signature.rho message 0 digestAttemptLimit) = some (counter, output) := by
            rw [hrho]
            exact hd
          obtain ⟨w, hw⟩ := expand_complete_of_recovered answers message _ original.signature
            counter output result hd' hr hp hpk htop
          exact ⟨w, hw, expand_verified answers message _ original.signature w hw⟩

theorem sign_expands (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (htree : TopTreeOK answers)
    (message : Message) (sig : Signature)
    (he : evalWithAnswerFn answers (sign cache message) = some sig) :
    ∃ w, evalWithAnswerFn answers (expand message (treeValue (builtTree answers 0 0) 12 0) sig) = some w ∧
      evalWithAnswerFn answers (verify message (treeValue (builtTree answers 0 0) 12 0) w) = true := by
  unfold sign at he
  simp only [evalWithAnswerFn_bind] at he
  split_ifs at he with htag
  · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
  · exact signPayload_expands answers cache hcache htree message sig he

end SigGolfCandidate.Research.SharedForest

/-! Exact relevant-bit product law for the shared forest producer. -/
namespace SigGolfCandidate.Research.SharedDigestFields

def fromBits (n : Nat) (f : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem fromBits_get (n : Nat) (f : Fin n → Bool) (i : Fin n) :
    (fromBits n f).getLsbD i.val = f i := by
  simp only [fromBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

def bitsEquiv (n : Nat) : BitVec n ≃ (Fin n → Bool) where
  toFun v i := v.getLsbD i.val
  invFun := fromBits n
  left_inv v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact fromBits_get n (fun j => v.getLsbD j.val) ⟨i, hi⟩
  right_inv f := by
    funext i
    exact fromBits_get n f i


set_option maxRecDepth 10000
set_option maxHeartbeats 0
def costBase (k : Nat) : Nat := [0, 7, 64, 71, 128, 135, 192, 199, 230].getD k 0
def rankBase (k : Nat) : Nat := [13, 77, 89, 101, 141, 153, 165, 205, 217].getD k 0
def spareBase (k : Nat) : Nat := [5, 6, 12, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 69, 70, 76, 87, 88, 99, 100, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 133, 134, 140, 151, 152, 163, 164, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 197, 198, 204, 215, 216, 227, 228, 229, 235, 236, 237, 238, 239, 240, 241].getD k 0
def position (i : Nat) : Nat :=
  if i < 45 then costBase (i / 5) + i % 5
  else if i < 135 then rankBase ((i-45)/10) + (i-45)%10
  else if i < 166 then 33 + (i-135)
  else if i < 180 then 242 + (i-166)
  else spareBase (i-180)
def inversePosition (i : Nat) : Nat := [0, 1, 2, 3, 4, 180, 181, 5, 6, 7, 8, 9, 182, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 10, 11, 12, 13, 14, 193, 194, 15, 16, 17, 18, 19, 195, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 196, 197, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 198, 199, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 20, 21, 22, 23, 24, 217, 218, 25, 26, 27, 28, 29, 219, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 220, 221, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 222, 223, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 30, 31, 32, 33, 34, 241, 242, 35, 36, 37, 38, 39, 243, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 244, 245, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 246, 247, 248, 40, 41, 42, 43, 44, 249, 250, 251, 252, 253, 254, 255, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179].getD i 0
theorem inversePosition_bound : ∀ i : Fin 256, inversePosition i.val < 256 := by decide +kernel
theorem inversePosition_correct : ∀ i : Fin 256, position (inversePosition i.val) = i.val := by decide +kernel
abbrev Fields := (Fin 9 → BitVec 5) × (Fin 9 → BitVec 10) × BitVec 31 × BitVec 14
def fields (a : BitVec 256) : Fields :=
  (fun k => a.extractLsb' (costBase k.val) 5,
   fun k => a.extractLsb' (rankBase k.val) 10,
   a.extractLsb' 33 31, a.extractLsb' 242 14)
def decompose (a : BitVec 256) : Fields × BitVec 76 :=
  (fields a, fromBits 76 (fun i => a.getLsbD (spareBase i.val)))
theorem decompose_injective : Function.Injective decompose := by
  intro a b h
  have hb : ∀ i : Fin 256, a.getLsbD (position i.val) = b.getLsbD (position i.val) := by
    intro i
    unfold position
    split_ifs with h0 h1 h2 h3
    · have hk : i.val / 5 < 9 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => (v.1.1 ⟨i.val / 5,hk⟩).getLsbD (i.val % 5)) h
      simpa only [decompose, fields, BitVec.getLsbD_extractLsb',
        Nat.mod_lt _ (by decide : 0 < 5), decide_true, Bool.true_and] using e
    · have hk : (i.val-45)/10 < 9 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => (v.1.2.1 ⟨(i.val-45)/10,hk⟩).getLsbD ((i.val-45)%10)) h
      simpa only [decompose, fields, BitVec.getLsbD_extractLsb',
        Nat.mod_lt _ (by decide : 0 < 10), decide_true, Bool.true_and] using e
    · have hk : i.val-135 < 31 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => v.1.2.2.1.getLsbD (i.val-135)) h
      simpa only [decompose, fields, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and] using e
    · have hk : i.val-166 < 14 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => v.1.2.2.2.getLsbD (i.val-166)) h
      simpa only [decompose, fields, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and] using e
    · have hk : i.val-180 < 76 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => v.2.getLsbD (i.val-180)) h
      simpa only [decompose, fromBits_get 76 _ ⟨i.val-180,hk⟩] using e
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have e := hb ⟨inversePosition k, inversePosition_bound ⟨k,hk⟩⟩
  simpa only [inversePosition_correct ⟨k,hk⟩] using e

theorem decompose_bijective : Function.Bijective decompose := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨decompose_injective, ?_⟩
  simp only [Fields, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec]
  norm_num
noncomputable def decomposeEquiv : BitVec 256 ≃ Fields × BitVec 76 :=
  Equiv.ofBijective decompose decompose_bijective
end SigGolfCandidate.Research.SharedDigestFields
namespace SigGolfCandidate.Research.SharedDigestFields
noncomputable def fiberEquiv (f : Fields) : {a : BitVec 256 // fields a = f} ≃ BitVec 76 where
  toFun a := (decompose a.val).2
  invFun spare := ⟨decomposeEquiv.symm (f, spare),
    congrArg Prod.fst (decomposeEquiv.apply_symm_apply (f,spare))⟩
  left_inv a := by
    apply Subtype.ext
    apply decomposeEquiv.injective
    change decomposeEquiv (decomposeEquiv.symm (f, (decompose a.val).2)) = decompose a.val
    rw [decomposeEquiv.apply_symm_apply]
    exact Prod.ext a.property.symm rfl
  right_inv spare := congrArg Prod.snd (decomposeEquiv.apply_symm_apply (f,spare))
theorem fiber_card (f : Fields) : Fintype.card {a : BitVec 256 // fields a = f} = 2^76 :=
  (Fintype.card_congr (fiberEquiv f)).trans (Fintype.card_bitVec 76)
end SigGolfCandidate.Research.SharedDigestFields
namespace SigGolfCandidate.Research.SharedDigestFields
open OracleComp OracleSpec ENNReal
 theorem fields_uniform :
    𝒮[fields <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      𝒮[($ᵗ Fields : ProbComp Fields)] := by
  have hm : fields <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256)) =
      Prod.fst <$> (decompose <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256))) := by
    simp only [Functor.map_map]
    rfl
  have hd : 𝒮[decompose <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      𝒮[($ᵗ (Fields × BitVec 76) : ProbComp (Fields × BitVec 76))] :=
    evalSPMF_map_bijective_uniform_cross (α := BitVec 256) (β := Fields × BitVec 76) decompose decompose_bijective
  rw [hm, evalSPMF_map, hd, ← evalSPMF_map]
  exact evalSPMF_map_fst_uniformSample_prod
end SigGolfCandidate.Research.SharedDigestFields
namespace SigGolfCandidate.Research.SharedDigestFields
open SigGolfCandidate.T3

theorem costBase_source (k : Fin 9) : costBase k.val = SharedForest.costFieldBase k.val := by
  fin_cases k <;> rfl

theorem rankBase_source (k : Nat) : rankBase k = SharedForest.rankBase k := rfl

theorem fields_cost (a : HashOutput) (k : Fin 9) :
    ((fields a).1 k).toNat = (SharedForest.costField a k).val := by
  simp only [fields, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, costBase_source]
  rfl

theorem fields_rank (a : HashOutput) (k : Fin 9) :
    ((fields a).2.1 k).toNat = SharedForest.rawForestRank a k.val := by
  simp only [fields, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, rankBase_source]
  rfl

theorem fields_index (a : HashOutput) : (fields a).2.2.1.toNat = ClaudeWCT.WCT9.digestIndex a := by
  simp only [fields, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rfl

theorem fields_gate (a : HashOutput) : (fields a).2.2.2.toNat = a.toNat / 2^242 % 16384 := by
  simp only [fields, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
end SigGolfCandidate.Research.SharedDigestFields

namespace SigGolfCandidate.Research.SharedDigestFields
open SigGolfCandidate.T3 ClaudeWCT.WCT9 OracleComp OracleSpec

def decodedRank (f : Fields) (k : Fin 9) : Fin 563 :=
  ⟨(f.2.1 k).toNat % 563, Nat.mod_lt _ (by decide)⟩
def coordinateCost (f : Fields) (k : Fin 9) : Nat :=
  routineCost (decodedRank f k) +
    (if SharedForest.firstCoord k.val then SharedForest.aCorrection (f.1 k).toNat
     else SharedForest.bCorrection (f.1 k).toNat)
def cost (f : Fields) : Nat := ((List.finRange 9).map (coordinateCost f)).sum
def accepted (f : Fields) : Bool :=
  decide (f.2.2.2.toNat < 791) &&
    (List.finRange 9).all (fun k => decide ((f.2.1 k).toNat < 563)) && decide (cost f ≤ 777)

theorem decodedRank_fields (a : HashOutput) (k : Fin 9) :
    decodedRank (fields a) k = SharedForest.forestRank a k.val := by
  apply Fin.ext
  simp only [decodedRank, fields_rank]
  rfl

theorem coordinateCost_fields (a : HashOutput) (k : Fin 9) :
    coordinateCost (fields a) k = SharedForest.coordinateAccountingCost a k := by
  simp only [coordinateCost, decodedRank_fields, fields_cost,
    SharedForest.coordinateAccountingCost, SharedForest.accountingCorrection_field]

theorem cost_fields (a : HashOutput) : cost (fields a) = SharedForest.jointAccountingCost a := by
  have hc : coordinateCost (fields a) = SharedForest.coordinateAccountingCost a :=
    funext (coordinateCost_fields a)
  simp only [cost, SharedForest.jointAccountingCost, hc]

theorem accepted_fields (a : HashOutput) : accepted (fields a) = SharedForest.digestAccepted a := by
  simp only [accepted, SharedForest.digestAccepted, SharedForest.ranksAccepted,
    fields_gate, fields_rank, cost_fields]

theorem accepted_uniform :
    𝒮[SharedForest.digestAccepted <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[accepted <$> ($ᵗ Fields : ProbComp Fields)] := by
  have h : SharedForest.digestAccepted = accepted ∘ fields := by
    funext a
    exact (accepted_fields a).symm
  have hm : SharedForest.digestAccepted <$> ($ᵗ HashOutput : ProbComp HashOutput) =
      accepted <$> (fields <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    rw [Functor.map_map]
    exact congrArg (fun f => f <$> ($ᵗ HashOutput : ProbComp HashOutput)) h
  rw [hm, evalSPMF_map, fields_uniform, ← evalSPMF_map]

noncomputable def predicateEquiv (p : Fields → Prop) :
    {a : HashOutput // p (fields a)} ≃ {f : Fields // p f} × BitVec 76 where
  toFun a := (⟨fields a.val, a.property⟩, (decompose a.val).2)
  invFun v := ⟨decomposeEquiv.symm (v.1.val, v.2), by
    have h := congrArg Prod.fst (decomposeEquiv.apply_symm_apply (v.1.val,v.2))
    change fields (decomposeEquiv.symm (v.1.val,v.2)) = v.1.val at h
    rw [h]
    exact v.1.property⟩
  left_inv a := by
    apply Subtype.ext
    exact decomposeEquiv.symm_apply_apply a.val
  right_inv v := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (decomposeEquiv.apply_symm_apply (v.1.val,v.2))
    · change (decompose (decomposeEquiv.symm (v.1.val,v.2))).2 = v.2
      exact congrArg Prod.snd (decomposeEquiv.apply_symm_apply (v.1.val,v.2))

theorem predicate_card (p : Fields → Prop) [DecidablePred p] :
    Fintype.card {a : HashOutput // p (fields a)} = Fintype.card {f : Fields // p f} * 2^76 := by
  rw [Fintype.card_congr (predicateEquiv p), Fintype.card_prod, Fintype.card_bitVec]
end SigGolfCandidate.Research.SharedDigestFields

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoverHintedLayers_credit (answers : Answers) (sig : Signature) (index : Nat) (other : Digest) :
    ∀ n, n ≤ 4 → ∀ msg result,
      evalWithAnswerFn answers (recoverHintedLayers sig index other n msg) = some result →
      result.digits.length = n ∧ result.lows.length = n ∧ ∀ lay : Layer, lay.val < n →
        hintFloor sig.policyHints lay ≤
          CanonicalPolicy.credit lay (result.lows.getD lay.val true) (result.digits.getD lay.val []) := by
  intro n
  induction n with
  | zero =>
      intro _ msg result he
      simp [recoverHintedLayers] at he
  | succ n ih =>
      intro hn msg result he
      simp only [recoverHintedLayers, evalWithAnswerFn_bind] at he
      split at he
      ·
          rename_i counter digits low hs
          have hlim := searchLimit_le (Fin.ofNat 4 n)
          have hd := (canonical_search_valid_credit answers _ _ _ _ _ _ 0 counter digits low
            (by unfold counterLimit at hlim; omega) hs).2
          have hlay := ofNat_layer_val n (by omega)
          by_cases hn0 : n = 0
          · subst n
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
            subst result
            refine ⟨rfl, rfl, fun lay hsmall => ?_⟩
            have heq : lay = 0 := Fin.ext (by omega)
            subst lay
            exact hd
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            split at he
            rotate_left
            · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
            ·
                rename_i previous hr
                simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
                subst result
                obtain ⟨hlen, hllen, hprevious⟩ := ih (by omega) _ _ hr
                refine ⟨by simp [hlen], by simp [hllen], fun lay hsmall => ?_⟩
                by_cases htop : lay.val = n
                · have heq : lay = Fin.ofNat 4 n := Fin.ext (htop.trans hlay.symm)
                  subst lay
                  simp only [hlay, List.getD_append_right previous.digits [digits] [] n (by omega), hlen,
                    List.getD_append_right previous.lows [low] true n (by omega), hllen,
                    Nat.sub_self, List.getD_cons_zero]
                  exact hd
                · rw [List.getD_append previous.digits [digits] [] lay.val (by omega),
                    List.getD_append previous.lows [low] true lay.val (by omega)]
                  exact hprevious lay (by omega)
      · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he

theorem policyHints_credit_sum (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool)
    (hh : policyHintsValid hints digits lows = true)
    (hc : ∀ lay : Layer, hintFloor hints lay ≤
      CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val [])) :
    69 ≤ ((List.finRange 4).map fun lay =>
      CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val [])).sum := by
  simp only [policyHintsValid, decide_eq_true_eq] at hh
  have h0 : 14 ≤ CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []) := by
    simpa [hintFloor, CanonicalPolicy.topFloor] using hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  rw [hh.2.2.1] at h1
  rw [hh.2.2.2.1] at h2
  rw [hh.2.2.2.2] at h3
  have hz := canonical_four_residual (digits.getD 0 []) (digits.getD 1 []) (digits.getD 2 [])
    (digits.getD 3 []) (lows.getD 0 true) (lows.getD 1 true) (lows.getD 2 true) (lows.getD 3 true) h0 h1 h2 h3
  simp only [CanonicalPolicy.nextResidual] at hz
  change 69 ≤ CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []) +
    (CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 []) +
      (CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 []) +
      (CanonicalPolicy.credit 3 (lows.getD 3 true) (digits.getD 3 []) + 0)))
  omega
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Cost
open ClaudeWCT.WCT9.Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem maxDigit_le_seven (lay : Layer) (i : Nat) : maxDigit lay i ≤ 7 := by
  unfold maxDigit
  split_ifs <;> omega

/-- Coarse unconditional main-tree recovery bound; no old local credit floor
or old layer-two/three target is used. -/
theorem bound_recoverLayerPair_coarse (sig : ClaudeWCT.WCT9.Signature) (index : Nat)
    (lay : Layer) (digits : List Nat) :
    CBound (fun _ => True) 404 (recoverLayerPair sig index lay digits) := by
  unfold recoverLayerPair
  dsimp only
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount lay)) _
    (fun _ => 7) (fun i _ => (bound_chainW _ _ _ _ _ _ _).mono_k
      (Nat.sub_le _ _ |>.trans (maxDigit_le_seven lay i.val)))).bind'
    (l := leafHashCost lay + (height lay - 1)) (fun ends hends => ?_) ?_
  · refine (bound_lowerLeafHash lay _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine ((Bound.foldlM_list (P := GoodQuery) (List.finRange (height lay - 1)) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).bind' (l := 0)
      (fun _ _ => .pure _ 0 trivial) (by simp))
    exact bound_lowerNodeHash _ _ _ _ _
  · fin_cases lay <;> decide

theorem bound_topFold_coarse (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (digits : List Nat) :
    CBound (fun _ => True) 403 (topFold sig index digits) := by
  unfold topFold topEnds
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount 0)) _
    (fun _ => 7) (fun i _ => (bound_layChain _ _ _ _ _ _ _).mono_k
      (Nat.sub_le _ _ |>.trans (maxDigit_le_seven 0 i.val)))).bind'
    (l := leafHashCost 0 + 11) (fun ends hends => ?_) ?_
  · refine (bound_leafHash 0 _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine (Bound.foldlM_list (P := GoodQuery) ((List.finRange (height 0)).take 11) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).mono_k
        (by rw [take_top_length]; simp)
    unfold topStep
    exact bound_nodeHash _ _ _ _ _ _
  · decide

/-- Top-bytes layer: the expander's nonce re-derivation costs at most `topNonceCap h = 104·2^h` per path node of
height `h = 1..11` (Σ = 425,776), on top of the 392 chain/leaf compressions. -/
def topFoldNCost : Nat := 392 + 425776
theorem bound_topFoldN_coarse (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (digits : List Nat) :
    CBound (fun _ => True) topFoldNCost (topFoldN sig index digits) := by
  unfold topFoldN topEnds topFoldNCost
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount 0)) _
    (fun _ => 7) (fun i _ => (bound_layChain _ _ _ _ _ _ _).mono_k
      (Nat.sub_le _ _ |>.trans (maxDigit_le_seven 0 i.val)))).bind'
    (l := leafHashCost 0 + 425776) (fun ends hends => ?_) ?_
  · refine (bound_leafHash 0 _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine (Bound.foldlM_list (P := GoodQuery) ((List.finRange (height 0)).take 11) _
      (fun _ _ => True) (fun i => topNonceCap (i + 1)) (root, []) trivial (fun i hi st _ => ?_)).mono_k
        (by decide +kernel)
    have hjv : (((List.finRange (height 0)).take 11)[i]'hi).val = i := by simp [List.getElem_take]
    unfold topStepN
    exact (Cost.bound_topNodeAt _ _ _ _).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by rw [hjv]; simp)
  · decide

theorem bound_recoverSharedInner (first : Bool) (index coord : Nat) (hc : coord<9)
    (selected : Child) (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    CBound (fun _ => True) 31 (recoverSharedInner first index coord selected word values path prev) := by
  unfold recoverSharedInner
  have hj := rawChild_lt first selected.val selected.isLt
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange 6) _ (fun _ => 4)
    (fun i _ => (cbound_of_ftsBound (ftsBound_chain index coord (rawChild first selected.val)
      i.val (4-wordDigit word i) (wordDigit word i) (values i) hc hj i.isLt
      (by have h := wordDigit_le_four word i; omega))).mono_k (wordDigit_le_four word i))).bind'
      (l := 7) (fun ends hends => ?_) (by decide)
  refine (cbound_of_ftsBound (ftsBound_leafHashH index (128 + selected.val) coord (rawChild first selected.val)
    prev.1 ends hc hj (by simpa using hends))).bind'
      (l := 5) (fun leaf _ => ?_) (by decide)
  exact (Bound.foldlM_list (P := GoodQuery) (List.range 5) _ (fun _ _ => True) (fun _ => 1)
    leaf trivial (fun i hi value _ => bound_sharedNode ..)).mono_k (by simp)

theorem bound_recoverPair (index pair : Nat) (hp : pair<4) (selected : Selection)
    (aWord bWord : Rank) (opened : PairOpening) (prev : PairRoot) :
    CBound (fun _ => True) 63 (recoverPair index pair selected aWord bWord opened prev) := by
  unfold recoverPair
  refine (bound_recoverSharedInner true index (2*pair) (by omega) _ _ _ _ _).bind'
    (l := 32) (fun a _ => ?_) (by decide)
  refine (bound_recoverSharedInner false index (2*pair+1) (by omega) _ _ _ _ _).bind'
    (l := 1) (fun b _ => ?_) (by decide)
  exact (bound_sharedOuterHash ..).bind' (l := 0) (fun outer _ => .pure _ 0 trivial) (by decide)

theorem bound_recoverSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) :
    CBound (fun _ => True) 32 (recoverSingleton index selected word opened prev) := by
  unfold recoverSingleton
  refine (bound_recoverSharedInner false index 8 (by decide) _ _ _ _ _).bind'
    (l := 1) (fun inner _ => ?_) (by decide)
  exact (bound_sharedOuterHash ..).bind' (l := 0) (fun outer _ => .pure _ 0 trivial) (by decide)

theorem bound_recoverForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) :
    CBound (fun _ => True) 284 (recoverForest index selected words opened) := by
  unfold recoverForest
  refine (Bound.foldlM_list (P := GoodQuery) (List.finRange 4) _ (fun _ _ => True) (fun _ => 63)
    ftsStart trivial (fun i hi prev _ => bound_recoverPair index ((List.finRange 4)[i]).val ((List.finRange 4)[i]).isLt _ _ _ _ _)).bind'
      (l := 32) (fun prev _ => bound_recoverSingleton ..) (by decide)

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def recoverySearch (answers : Answers) (sig : Signature) (index : Nat) (forest : PairRoot) (lay : Layer) :
    M (Option (BitVec 32 × List Nat × Bool)) :=
  CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
    (route index lay).2 (route index lay).1
    (if lay = 3 then .pair forest.1 forest.2 else
      let lower : Layer := Fin.ofNat 4 (lay.val + 1)
      .pair (builtPair answers lower (route index lower).2).1
        (builtPair answers lower (route index lower).2).2) 0 (searchLimit lay)

def recoverySearchCost (answers : Answers) (sig : Signature) (index : Nat) (forest : PairRoot) : Nat :=
  cost answers (recoverySearch answers sig index forest 0) +
  cost answers (recoverySearch answers sig index forest 1) +
  cost answers (recoverySearch answers sig index forest 2) +
  cost answers (recoverySearch answers sig index forest 3)

theorem recoverHintedLayers_cost_replay (answers : Answers) (sig : Signature) (index : Nat)
    (other : Digest) (forest : PairRoot) (counter : Layer → BitVec 32) (digits : Layer → List Nat)
    (lows : Layer → Bool)
    (hs : ∀ lay, evalWithAnswerFn answers (recoverySearch answers sig index forest lay) =
      some (counter lay, digits lay, lows lay))
    (hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (digits lay)) =
      builtPair answers lay (route index lay).2) :
    cost answers (recoverHintedLayers sig index other 4 (.pair forest.1 forest.2)) ≤
      recoverySearchCost answers sig index forest + (1616 + 425765) := by
  have hs0 := hs 0
  have hs1 := hs 1
  have hs2 := hs 2
  have hs3 := hs 3
  have hp1 := hp 1 (by decide)
  have hp2 := hp 2 (by decide)
  have hp3 := hp 3 (by decide)
  have hc1 := cost_bound answers (bound_recoverLayerPair_coarse (mainSignature sig) index 1 (digits 1))
  have hc2 := cost_bound answers (bound_recoverLayerPair_coarse (mainSignature sig) index 2 (digits 2))
  have hc3 := cost_bound answers (bound_recoverLayerPair_coarse (mainSignature sig) index 3 (digits 3))
  have hct := cost_bound answers (bound_topFoldN_coarse (mainSignature sig) index (digits 0))
  have hcn := cost_bound answers (ClaudeWCT.WCT9.Cost.bound_topNode index
    (evalWithAnswerFn answers (topFoldN (mainSignature sig) index (digits 0))).1 other)
  simp only [recoverySearch, show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
    show (2 : Layer) ≠ 3 by decide, if_false, if_true,
    show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
    show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
    show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl] at hs0 hs1 hs2 hs3 ⊢
  simp only [recoverySearchCost, recoverySearch,
    show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
    show (2 : Layer) ≠ 3 by decide, if_false, if_true,
    show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
    show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
    show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl]
  simp only [recoverHintedLayers, cost_bind, evalWithAnswerFn_bind,
    show (Fin.ofNat 4 0 : Layer) = 0 from rfl,
    show (Fin.ofNat 4 1 : Layer) = 1 from rfl,
    show (Fin.ofNat 4 2 : Layer) = 2 from rfl,
    show (Fin.ofNat 4 3 : Layer) = 3 from rfl,
    hs0, hs1, hs2, hs3, hp1, hp2, hp3,
    Nat.reduceEqDiff, if_false, if_true, evalWithAnswerFn_pure, cost_pure]
  simp only [topFoldNCost] at hct
  omega

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem PreparedSearchFacts.cost_eq {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result)
    (sig : Signature) (hh : sig.policyHints = result.policyHints)
    (hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2)
    (hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2)
    (hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2) :
    cost answers (searchPreparedLayers cache index prepared forest) =
      recoverySearchCost answers sig index forest +
        cost answers (signTop cache (route index 0).1 (result.digits.getD 0 [])) := by
  have hs0 := h.search0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  have hf1 := Nat.not_le.mpr h.floor1_lt
  have hf2 := Nat.not_le.mpr h.floor2_lt
  have hf3 := Nat.not_le.mpr h.floor3_lt
  dsimp only [preparedResidual1, preparedResidual2, preparedResidual3] at hs1 hs2 hs3 hf1 hf2 hf3
  simp only [searchPreparedLayers, cost_bind, hs0, hs1, hs2, hs3,
    hf1, hf2, hf3, if_false, cost_pure, Nat.add_zero]
  simp only [recoverySearchCost, recoverySearch, hh, h.hints_spec.2.1,
    h.hints_spec.2.2.1, h.hints_spec.2.2.2, hm0, hm1, hm2,
    show hintFloor result.policyHints 0 = CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit from rfl,
    show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
    show (2 : Layer) ≠ 3 by decide, if_false, if_true,
    show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
    show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
    show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl,
    preparedResidual1, preparedResidual2, preparedResidual3]
  omega

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem expand_fillTopSignature (message : Message) (pk : Digest) (sig : Signature) (c : Nat) :
    expand message pk (fillTopSignature sig c) = expand message pk sig := by
  rw [← expand_normTop message pk (fillTopSignature sig c), normTop_fill, expand_normTop]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem PreparedSearchFacts.recovery_cost_le {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result)
    (sig : Signature) (other : Digest) (hh : sig.policyHints = result.policyHints)
    (hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2)
    (hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2)
    (hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2)
    (hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (result.digits.getD lay.val [])) =
      builtPair answers lay (route index lay).2) :
    cost answers (recoverHintedLayers sig index other 4 (.pair forest.1 forest.2)) ≤
      cost answers (searchPreparedLayers cache index prepared forest) + (1616 + 425765) := by
  have hs0 := h.search0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  rw [hm0] at hs0
  rw [hm1] at hs1
  rw [hm2] at hs2
  have hs : ∀ lay, evalWithAnswerFn answers (recoverySearch answers sig index forest lay) =
      some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true) := by
    intro lay
    rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
      simp only [recoverySearch, hh, h.hints_spec.2.1, h.hints_spec.2.2.1, h.hints_spec.2.2.2,
        show hintFloor result.policyHints 0 = CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit from rfl,
        show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
        show (2 : Layer) ≠ 3 by decide, if_false, if_true,
        show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
        show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
        show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl]
    · exact hs0
    · exact hs1
    · exact hs2
    · exact hs3
  have hc := recoverHintedLayers_cost_replay answers sig index other forest
    (fun lay => result.counters.getD lay.val 0) (fun lay => result.digits.getD lay.val [])
    (fun lay => result.lows.getD lay.val true) hs hp
  have he := h.cost_eq sig hh hm0 hm1 hm2
  omega

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem policyHintsValid_congr_lows (hints : BitVec 16) (digits : List (List Nat)) {lowsA lowsB : List Bool}
    (h0 : lowsA.getD 0 true = lowsB.getD 0 true) (h1 : lowsA.getD 1 true = lowsB.getD 1 true)
    (h2 : lowsA.getD 2 true = lowsB.getD 2 true) :
    policyHintsValid hints digits lowsA = policyHintsValid hints digits lowsB := by
  simp only [policyHintsValid, h0, h1, h2]

theorem hintedSelections_unique (answers : Answers) (index : Nat) (messages : Layer → LayerMsg)
    (hintsA hintsB : BitVec 16) (countersA countersB : Layer → BitVec 32)
    (digitsA digitsB : List (List Nat)) (lowsA lowsB : List Bool)
    (hvalidA : policyHintsValid hintsA digitsA lowsA = true)
    (hvalidB : policyHintsValid hintsB digitsB lowsB = true)
    (hsearchA : ∀ lay, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor hintsA lay) (route index lay).2
        (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (countersA lay, digitsA.getD lay.val [], lowsA.getD lay.val true))
    (hsearchB : ∀ lay, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor hintsB lay) (route index lay).2
        (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (countersB lay, digitsB.getD lay.val [], lowsB.getD lay.val true)) :
    hintsA = hintsB ∧ countersA = countersB ∧ digitsA = digitsB ∧
      ∀ lay : Layer, lowsA.getD lay.val true = lowsB.getD lay.val true := by
  have hA := hvalidA
  have hB := hvalidB
  simp only [policyHintsValid, decide_eq_true_eq] at hA hB
  have same (lay : Layer) (hf : hintFloor hintsA lay = hintFloor hintsB lay) :
      (countersA lay, digitsA.getD lay.val [], lowsA.getD lay.val true) =
        (countersB lay, digitsB.getD lay.val [], lowsB.getD lay.val true) := by
    have ha := hsearchA lay
    rw [hf] at ha
    exact Option.some.inj (ha.symm.trans (hsearchB lay))
  have h0 := same 0 (by rfl)
  have hd0 : digitsA.getD 0 [] = digitsB.getD 0 [] := congrArg (fun x => x.2.1) h0
  have hl0 : lowsA.getD 0 true = lowsB.getD 0 true := congrArg (fun x => x.2.2) h0
  have h1 := same 1 (by rw [hA.2.2.1, hB.2.2.1, hd0, hl0])
  have hd1 : digitsA.getD 1 [] = digitsB.getD 1 [] := congrArg (fun x => x.2.1) h1
  have hl1 : lowsA.getD 1 true = lowsB.getD 1 true := congrArg (fun x => x.2.2) h1
  have h2 := same 2 (by rw [hA.2.2.2.1, hB.2.2.2.1, hd0, hd1, hl0, hl1])
  have hd2 : digitsA.getD 2 [] = digitsB.getD 2 [] := congrArg (fun x => x.2.1) h2
  have hl2 : lowsA.getD 2 true = lowsB.getD 2 true := congrArg (fun x => x.2.2) h2
  have h3 := same 3 (by rw [hA.2.2.2.2, hB.2.2.2.2, hd0, hd1, hd2, hl0, hl1, hl2])
  have hd3 : digitsA.getD 3 [] = digitsB.getD 3 [] := congrArg (fun x => x.2.1) h3
  have hl3 : lowsA.getD 3 true = lowsB.getD 3 true := congrArg (fun x => x.2.2) h3
  have hd : digitsA = digitsB := by
    apply List.ext_getElem (hA.2.1.trans hB.2.1.symm)
    intro i hi hj
    have hi4 : i < 4 := by omega
    have he : digitsA.getD i [] = digitsB.getD i [] := by
      interval_cases i <;> assumption
    simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using he
  have hvB : policyHintsValid hintsB digitsA lowsA = true := by
    rw [policyHintsValid_congr_lows hintsB digitsA hl0 hl1 hl2, hd]; exact hvalidB
  refine ⟨policyHintsValid_unique hvalidA hvB, ?_, hd, ?_⟩
  · funext lay
    fin_cases lay
    · exact congrArg Prod.fst h0
    · exact congrArg Prod.fst h1
    · exact congrArg Prod.fst h2
    · exact congrArg Prod.fst h3
  · intro lay
    fin_cases lay
    · exact hl0
    · exact hl1
    · exact hl2
    · exact hl3
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def recoveredMessage (answers : Answers) (sig : Signature) (index n : Nat)
    (message : LayerMsg) (digits : List (List Nat)) (lay : Layer) : LayerMsg :=
  if lay.val + 1 = n then message else
    let next : Layer := Fin.ofNat 4 (lay.val + 1)
    let pair := evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index next
      (digits.getD (lay.val + 1) []))
    .pair pair.1 pair.2

theorem recoverHintedLayers_selections (answers : Answers) (sig : Signature) (index : Nat)
    (other : Digest) : ∀ n, n ≤ 4 → ∀ message result,
    evalWithAnswerFn answers (recoverHintedLayers sig index other n message) = some result →
    result.counters.length = n ∧ result.digits.length = n ∧ result.lows.length = n ∧
      ∀ lay : Layer, lay.val < n → evalWithAnswerFn answers
        (CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
          (route index lay).2 (route index lay).1
          (recoveredMessage answers sig index n message result.digits lay) 0 (searchLimit lay)) =
            some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true) := by
  intro n
  induction n with
  | zero => intro _ message result he; simp [recoverHintedLayers] at he
  | succ n ih =>
      intro hn message result he
      have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
      simp only [recoverHintedLayers, evalWithAnswerFn_bind] at he
      split at he
      ·
          rename_i counter digits low hs
          by_cases hn0 : n = 0
          · subst n
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
            subst result
            refine ⟨rfl, rfl, rfl, ?_⟩
            intro lay hlay
            have hl : lay = 0 := Fin.ext (by omega)
            subst lay
            simp only [show (Fin.ofNat 4 0 : Layer) = 0 from rfl] at hs
            simpa only [recoveredMessage, Fin.val_zero, Nat.zero_add, if_true, List.getD_cons_zero] using hs
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            let pair := evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index
              (Fin.ofNat 4 n) digits)
            split at he
            rotate_left
            · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
            ·
                rename_i previous hr
                simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
                subst result
                obtain ⟨hcl, hdl, hll, hsel⟩ := ih (by omega) _ _ hr
                refine ⟨by simp [hcl], by simp [hdl], by simp [hll], ?_⟩
                intro lay hlay
                by_cases hlt : lay.val < n
                · have hcounter : (previous.counters ++ [counter]).getD lay.val 0 =
                      previous.counters.getD lay.val 0 := List.getD_append _ _ _ _ (by omega)
                  have hdigit : (previous.digits ++ [digits]).getD lay.val [] =
                      previous.digits.getD lay.val [] := List.getD_append _ _ _ _ (by omega)
                  have hlow : (previous.lows ++ [low]).getD lay.val true =
                      previous.lows.getD lay.val true := List.getD_append _ _ _ _ (by omega)
                  rw [hcounter, hdigit, hlow]
                  have hm : recoveredMessage answers sig index (n + 1) message
                        (previous.digits ++ [digits]) lay =
                      recoveredMessage answers sig index n (.pair pair.1 pair.2) previous.digits lay := by
                    unfold recoveredMessage
                    rw [if_neg (by omega)]
                    by_cases hnxt : lay.val + 1 = n
                    · rw [if_pos hnxt, hnxt, List.getD_append_right _ _ _ _ (by omega), hdl]
                      simp only [Nat.sub_self, List.getD_cons_zero]
                      rfl
                    · rw [if_neg hnxt, List.getD_append _ _ _ _ (by omega)]
                  rw [hm]
                  exact hsel lay hlt
                · have hl : lay = Fin.ofNat 4 n := Fin.ext (by rw [hv]; omega)
                  subst lay
                  simp only [recoveredMessage, hv, if_true]
                  rw [List.getD_append_right _ _ _ _ (by omega), hcl,
                    List.getD_append_right _ _ _ _ (by omega), hdl,
                    List.getD_append_right _ _ _ _ (by omega), hll]
                  simpa only [Nat.sub_self, List.getD_cons_zero] using hs
      · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
theorem fillTopSignature_fillTopSignature (sig : Signature) (a b : Nat) :
    fillTopSignature (fillTopSignature sig a) b = fillTopSignature sig b := by
  unfold fillTopSignature
  simp only [Signature.mk.injEq, true_and]
  funext lay
  exact fillLayer_fillLayer lay (sig.layers lay) a b
end SigGolfCandidate.Research.SharedForest


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoveredMessage_fill (answers : Answers) (sig : Signature) (index n : Nat)
    (hn : n ≤ 4) (message : LayerMsg) (digits : List (List Nat)) (lay : Layer)
    (hlay : lay.val < n) (c : Nat) :
    recoveredMessage answers (fillTopSignature sig c) index n message digits lay =
      recoveredMessage answers sig index n message digits lay := by
  unfold recoveredMessage
  split_ifs with htop
  · rfl
  · have hnext : (Fin.ofNat 4 (lay.val + 1) : Layer).val ≠ 0 := by
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hmain : mainSignature (fillTopSignature sig c) = fillTop (mainSignature sig) c := rfl
    dsimp only
    rw [hmain, recoverLayerPair_fill _ _ _ _ c hnext]

theorem recoveredPair_of_pieces (answers : Answers) (sig : Signature) (index : Nat)
    (lay : Layer) (hl : lay ≠ 0) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (hlayer : sig.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 digits)) :
    evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index lay digits) =
      builtPair answers lay (route index lay).2 := by
  apply eval_recoverLayerPair_honest answers (mainSignature sig) index lay hl digits hvalid
  · intro i
    change (sig.layers lay).values i = _
    rw [hlayer]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, i.isLt]
  · intro j
    change (sig.layers lay).path j = _
    rw [hlayer]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, j.isLt]

theorem recoveredSelections_canonical (answers : Answers) (sig : Signature) (index : Nat)
    (input : LayerMsg) (result : RecoveredLayers) (messages : Layer → LayerMsg)
    (hinput : input = messages 3)
    (hlower : ∀ n, n < 3 → messages (Fin.ofNat 4 n) =
      .pair (builtPair answers (Fin.ofNat 4 (n+1)) (route index (Fin.ofNat 4 (n+1))).2).1
        (builtPair answers (Fin.ofNat 4 (n+1)) (route index (Fin.ofNat 4 (n+1))).2).2)
    (hselections : ∀ lay : Layer, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
        (route index lay).2 (route index lay).1
        (recoveredMessage answers sig index 4 input result.digits lay) 0 (searchLimit lay)) =
          some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true))
    (hshape : ∀ lay : Layer, ∃ digits,
      CanonicalPolicy.decode lay (evalWithAnswerFn answers (encodingHash lay
        (layerEncodingInput lay (route index lay).2 (route index lay).1 (messages lay)
          (result.counters.getD lay.val 0)))) = some digits ∧
      sig.layers lay = piecesSignature lay
        (wotsPieces answers lay (route index lay).2 (route index lay).1 digits)) :
    ∀ lay : Layer,
      evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
        (route index lay).2 (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true) ∧
      sig.layers lay = piecesSignature lay
        (wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val [])) := by
  have step (lay : Layer)
      (hm : recoveredMessage answers sig index 4 input result.digits lay = messages lay) :
      evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
        (route index lay).2 (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true) ∧
      sig.layers lay = piecesSignature lay
        (wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val [])) ∧
      Cost.ValidDigits lay (result.digits.getD lay.val []) := by
    have hs := hselections lay
    rw [hm] at hs
    have hlim := searchLimit_le lay
    have hp := (canonical_search_some' answers lay (hintFloor sig.policyHints lay)
      (route index lay).2 (route index lay).1 (messages lay) (searchLimit lay) 0
      (result.counters.getD lay.val 0) (result.digits.getD lay.val []) (result.lows.getD lay.val true)
      (by unfold counterLimit at hlim; omega) hs).2.2.2
    have hd := (CanonicalPolicy.producerDecodeAt_spec hp).1
    obtain ⟨ds, hds, hfields⟩ := hshape lay
    have heq := Option.some.inj (hds.symm.trans hd)
    subst ds
    exact ⟨hs, hfields, canonical_decode_valid hd⟩
  have h3 := step 3 (by change input = messages 3; exact hinput)
  have h2 := step 2 (by
    change LayerMsg.pair
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 3 (result.digits.getD 3 []))).1
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 3 (result.digits.getD 3 []))).2 = messages 2
    have hp := recoveredPair_of_pieces answers sig index 3 (by decide) _ h3.2.2 h3.2.1
    change evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 3
      (result.digits.getD 3 [])) = builtPair answers 3 (route index 3).2 at hp
    rw [hp]
    exact (hlower 2 (by decide)).symm)
  have h1 := step 1 (by
    change LayerMsg.pair
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 2 (result.digits.getD 2 []))).1
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 2 (result.digits.getD 2 []))).2 = messages 1
    have hp := recoveredPair_of_pieces answers sig index 2 (by decide) _ h2.2.2 h2.2.1
    change evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 2
      (result.digits.getD 2 [])) = builtPair answers 2 (route index 2).2 at hp
    rw [hp]
    exact (hlower 1 (by decide)).symm)
  have h0 := step 0 (by
    change LayerMsg.pair
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 1 (result.digits.getD 1 []))).1
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 1 (result.digits.getD 1 []))).2 = messages 0
    have hp := recoveredPair_of_pieces answers sig index 1 (by decide) _ h1.2.2 h1.2.1
    change evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 1
      (result.digits.getD 1 [])) = builtPair answers 1 (route index 1).2 at hp
    rw [hp]
    exact (hlower 0 (by decide)).symm)
  intro lay
  fin_cases lay
  · exact ⟨h0.1,h0.2.1⟩
  · exact ⟨h1.1,h1.2.1⟩
  · exact ⟨h2.1,h2.2.1⟩
  · exact ⟨h3.1,h3.2.1⟩
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signature_unique_of_selections (answers : Answers) (index : Nat)
    (messages : Layer → LayerMsg) (a b : Signature)
    (ca cb : Layer → BitVec 32) (da db : List (List Nat)) (la lb : List Bool)
    (hrho : a.rho = b.rho) (hforest : a.forest = b.forest)
    (ha : policyHintsValid a.policyHints da la = true)
    (hb : policyHintsValid b.policyHints db lb = true)
    (hsa : ∀ lay, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor a.policyHints lay)
        (route index lay).2 (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (ca lay, da.getD lay.val [], la.getD lay.val true))
    (hsb : ∀ lay, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor b.policyHints lay)
        (route index lay).2 (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (cb lay, db.getD lay.val [], lb.getD lay.val true))
    (hla : ∀ lay, a.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 (da.getD lay.val [])))
    (hlb : ∀ lay, b.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 (db.getD lay.val []))) : a = b := by
  obtain ⟨hh, -, hd, -⟩ := hintedSelections_unique answers index messages a.policyHints b.policyHints
    ca cb da db la lb ha hb hsa hsb
  have hl : a.layers = b.layers := by
    funext lay
    rw [hla, hlb, hd]
  cases a
  cases b
  simp only [Signature.mk.injEq]
  exact ⟨hrho, hh, hforest, hl⟩
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_components (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    ∃ result : CanonicalLayers,
      evalWithAnswerFn answers (searchPreparedLayers cache (digestIndex output)
        (evalWithAnswerFn answers (prepareRoots (digestIndex output)))
        (evalWithAnswerFn answers (buildForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output))).2) = some result ∧
      w.signature.rho = rho ∧ w.signature.policyHints = result.policyHints ∧
      w.signature.forest = (evalWithAnswerFn answers (buildForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output))).1 ∧
      (∀ lay, w.signature.layers lay = piecesSignature lay (result.pieces.getD lay.val ([],[]))) ∧
      w.digestCounter = counter ∧ ∀ lay, w.counters lay = result.counters.getD lay.val 0 := by
  unfold signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache (digestIndex output)
    (evalWithAnswerFn answers (prepareRoots (digestIndex output)))
    (evalWithAnswerFn answers (buildForest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output))).2) with
  | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some result =>
      simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
      subst w
      exact ⟨result, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, fun _ => rfl⟩

theorem signPayload_components (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (sig : Signature)
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) :
    ∃ counter output w,
      evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
        message 0 digestAttemptLimit) = some (counter, output) ∧
      evalWithAnswerFn answers (signFromOutput cache (evalWithAnswerFn answers (privateNonce message))
        counter output) = some w ∧ w.signature = sig := by
  unfold signPayload at he
  simp only [evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
    message 0 digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (signFromOutput cache (evalWithAnswerFn answers (privateNonce message))
        counter output) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some w =>
          simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
          exact ⟨counter,output,w,rfl,hs,he⟩
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem PreparedSearchFacts.hinted_searches {answers : Answers} {cache : SigGolfCandidate.T3.Cache}
    {index : Nat} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index (evalWithAnswerFn answers (prepareRoots index)) forest result) :
    ∀ lay, evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay
      (hintFloor result.policyHints lay) (route index lay).2 (route index lay).1
      (if lay=3 then .pair forest.1 forest.2 else
        let lower : Layer := Fin.ofNat 4 (lay.val+1)
        .pair (builtPair answers lower (route index lower).2).1
          (builtPair answers lower (route index lower).2).2)
      0 (searchLimit lay)) = some (result.counters.getD lay.val 0,result.digits.getD lay.val [],result.lows.getD lay.val true) := by
  have hs0 := h.search0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  simp only [prepareRoots_result,fixedPrepared_pair] at hs0 hs1 hs2
  intro lay
  rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
    simp only [layer_val_0,layer_val_1,layer_val_2,layer_val_3,
      show (Fin.ofNat 4 1 : Layer)=1 from rfl,
      show (Fin.ofNat 4 2 : Layer)=2 from rfl,
      show (Fin.ofNat 4 3 : Layer)=3 from rfl, Nat.reduceAdd,
      show (0 : Layer)≠3 by decide,show (1 : Layer)≠3 by decide,
      show (2 : Layer)≠3 by decide,if_false,if_true]
  · exact hs0
  · simpa only [h.hints_spec.2.1] using hs1
  · simpa only [h.hints_spec.2.2.1] using hs2
  · simpa only [h.hints_spec.2.2.2] using hs3
end SigGolfCandidate.Research.SharedForest
