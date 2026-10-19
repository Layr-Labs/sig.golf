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

set_option Elab.async false
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

#print axioms selected_branch
#print axioms pair_saves_one_digest
#print axioms four_pairs_signature_size
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

#print axioms recoverPair_honest
#print axioms recoverSingleton_honest
#print axioms recoverForest_honest

end SigGolfCandidate.Research.SharedForest
