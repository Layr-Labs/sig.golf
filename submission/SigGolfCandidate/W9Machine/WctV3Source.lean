import SigGolfCandidate.W9Machine.WctLayout
import SigGolfCandidate.Research.V7Composed198Gate
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP

set_option autoImplicit false
namespace W9Machine.V3
open OracleComp SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE)
def chainPrefix (index coord child : Nat) : Nat :=
  (index <<< 27) ||| (coord <<< 16) ||| (child <<< 20)
def chainLow (index coord child chain step : Nat) : Nat :=
  0x80 ||| (chain <<< 2) ||| (step <<< 8) ||| chainPrefix index coord child
abbrev HeaderPad := BitVec 64
def chainInput (index coord child chain step : Nat) (a : Digest) (b : HeaderPad)
    (c value : Digest) : HashInput :=
  bytesLE 16 a ++ bytesLE 8 (chainLow index coord child chain step) ++ bytesLE 8 b ++
    bytesLE 16 c ++ bytesLE 16 value
def chainP (index coord child chain start count : Nat) (a : Digest) (b : HeaderPad)
    (c value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun v step => shortHash (chainInput index coord child chain step a b c v)) value
def regionOffset (coord : Nat) : Nat := 176 + 896 * (8 - coord)
def chainOffset (coord chain : Nat) : Nat := regionOffset coord + (640 - 64 * chain)
def leafSlot (chain : Nat) : Nat := if chain = 0 then 688 else 720 + 16 * chain
def chainPadA (w : WBytes) (coord chain : Nat) : Digest := wdig w (chainOffset coord chain)
def chainPadB (w : WBytes) (coord chain : Nat) : HeaderPad :=
  w.extractLsb' (8 * (chainOffset coord chain + 24)) 64
def chainPadC (w : WBytes) (coord chain : Nat) : Digest :=
  wdig w (chainOffset coord chain + 32)
def reveal (w : WBytes) (coord chain deficit : Nat) : Digest :=
  if deficit = 0 then wdig w (regionOffset coord + leafSlot chain)
  else wdig w (chainOffset coord chain + 48)
def chainProgram (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 666) : M (List Digest) :=
  (List.finRange 6).mapM fun t =>
    let d := ClaudeWCT.WCT9.digit rank t
    chainP index k.val j.val t.val (4 - d) d
      (chainPadA w k.val t.val) (chainPadB w k.val t.val)
      (chainPadC w k.val t.val) (reveal w k.val t.val d)
def leafLow (index coord child : Nat) : Nat := ClaudeWCT.WCT9.ftsLeafLow index coord child
def nodeLow (coord index : Nat) : Nat := ClaudeWCT.WCT9.ftsLeafLow index coord 0
/-- Node tweak as the verifier writes it: packed heaps (`8..127`) carry `nodeLow - heap` and a witness high
word `hp`; the other heaps carry `nodeLow` and the heap. -/
def nodeHdr (coord index heap : Nat) (hp : BitVec 64) : Digest :=
  if 8 ≤ heap ∧ heap < 128 then hp ++ BitVec.ofNat 64 (nodeLow coord index - heap)
  else BitVec.ofNat 64 heap ++ BitVec.ofNat 64 (nodeLow coord index)
def nodeInput (coord index heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (nodeHdr coord index heap hp) ++ bytesLE 16 pad ++ bytesLE 16 right
/-- Nested FTS (r1-1): fold block offset of child level `level` in a region. Levels 0..4 follow the child plan;
level 5 (heaps 2, 3) uses the fixed block at 832, `left | hdr | Z | right`. -/
def blkOff (child level : Nat) : Nat := if level < 5 then ClaudeWCT.W9.T3M.authBase child level else 832
def sibOff (child level : Nat) : Nat := blkOff child level + 48 * (1 - child / 2 ^ level % 2)
def padOff (child level : Nat) : Nat := blkOff child level + 32
def nodePad (w : WBytes) (coord child level : Nat) : Digest := wdig w (regionOffset coord + padOff child level)
/-- The 16-byte tweak slot of a child level in the witness (`blkOff + 16`). -/
def nodeTw (w : WBytes) (coord child level : Nat) : Digest :=
  wdig w (regionOffset coord + blkOff child level + 16)
/-- High tweak word of a packed node (levels `< 4`) whose computed child is the right input; elsewhere 0. -/
def nodeHPad (w : WBytes) (coord child level : Nat) : BitVec 64 :=
  if level < 4 ∧ child / 2 ^ level % 2 = 1 then (nodeTw w coord child level).extractLsb' 64 64 else 0
def sibling (w : WBytes) (coord child level : Nat) : Digest := wdig w (regionOffset coord + sibOff child level)
/-- FTS leaf pad slot (`regionOffset coord + 720`): tree `coord - 1`'s left top node in the nested FTS. -/
def leafPad (w : WBytes) (coord : Nat) : Digest := wdig w (regionOffset coord + 720)
/-- The high 16 bytes of a public hash: the value of a heap-2/3 node. -/
def hashHi (input : HashInput) : M Digest := do
  pure ((← publicHash input).extractLsb' 128 128)
/-- Witness slot of tree `coord`'s top sibling: the Z slot (`+864`) of the region below when the computed top
node is the left one, its leaf pad (`+720`) otherwise; below tree 8 this is the virtual region (offsets 144, 0). -/
def topOtherOff (coord child : Nat) : Nat :=
  if child / 64 % 2 = 0 then regionOffset coord - 32 else regionOffset coord - 176
def topOther (w : WBytes) (coord child : Nat) : Digest := wdig w (topOtherOff coord child)
/-- The eight 16-byte fields of the T8 leaf `end0 | header | pad | end1..end5`. -/
def leafFields (coord index child : Nat) (pad : Digest) (ends : List Digest) (slot : Nat) : Digest :=
  if slot = 0 then ends.getD 0 0
  else if slot = 1 then ClaudeWCT.WCT9.ftsLeafHeader index coord child
  else if slot = 2 then pad else ends.getD (slot - 2) 0
def leafInput (coord index child : Nat) (pad : Digest) (ends : List Digest) : HashInput :=
  (List.range 8).flatMap fun slot => bytesLE 16 (leafFields coord index child pad ends slot)
structure RootPair where
  left : Digest
  right : Digest
def orderPair (child : Nat) (computed other : Digest) : RootPair :=
  if child / 64 % 2 = 0 then ⟨computed, other⟩ else ⟨other, computed⟩
/-- One nested FTS tree with explicit nested pads: `padL` in the leaf pad slot and `padZ` in the level-5 (heap 2/3)
fold's pad slot. Levels 0..4 keep the low half; level 5 keeps the high half. Returns the computed top node. -/
def childN (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (ends : List Digest)
    (padL padZ : Digest) : M Digest := do
  let leaf ← shortHash (leafInput k.val index j.val padL ends)
  let v ← (List.range 5).foldlM (fun value level =>
    let other := sibling w k.val j.val level
    let left := if j.val / 2 ^ level % 2 = 0 then value else other
    let right := if j.val / 2 ^ level % 2 = 0 then other else value
    shortHash (nodeInput k.val index ((128 + j.val) / 2 ^ (level + 1))
      left (nodeHPad w k.val j.val level) (nodePad w k.val j.val level) right)) leaf
  let other := sibling w k.val j.val 5
  let left := if j.val / 2 ^ 5 % 2 = 0 then v else other
  let right := if j.val / 2 ^ 5 % 2 = 0 then other else v
  hashHi (nodeInput k.val index ((128 + j.val) / 2 ^ 6) left 0 padZ right)
/-- One nested FTS tree from the witness view `w`: the pads are read from `w` (the coordinate proof uses the view
of `w` with the previous tree's pair in the hand-off slots). -/
def childProgram (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) : M Digest :=
  childN w index k j ends (leafPad w k.val) (nodePad w k.val j.val 5)
end W9Machine.V3

/-! The arbitrary-witness source for the shared-path verifier. Chain addresses
retain raw child indices; only authentication paths use the rotated B placement. -/
namespace W9Machine.SharedV3
open OracleComp SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.Research
abbrev WBytes := ClaudeWCT.W9.T3M.WBytes
abbrev PairRoot := Digest × Digest

def first (coord : Nat) : Bool := decide (coord < 8 ∧ coord % 2 = 0)
def physical (coord raw : Nat) : Nat := SharedForest.physicalChild (first coord) raw
def lastLevel (coord : Nat) : Nat := if first coord then 4 else 5

def blkOff (child level : Nat) : Nat :=
  if level < 5 then SharedPathPacking.block child level else 832
def sibOff (child level : Nat) : Nat := blkOff child level + 48 * (1 - child / 2 ^ level % 2)
def nodePad (w : WBytes) (coord child level : Nat) : Digest :=
  wdig w (V3.regionOffset coord + blkOff child level + 32)
def nodeTw (w : WBytes) (coord child level : Nat) : Digest :=
  wdig w (V3.regionOffset coord + blkOff child level + 16)
def nodeHPad (w : WBytes) (coord child level : Nat) : BitVec 64 :=
  if level < 4 ∧ child / 2 ^ level % 2 = 1 then (nodeTw w coord child level).extractLsb' 64 64 else 0
def sibling (w : WBytes) (coord child level : Nat) : Digest :=
  wdig w (V3.regionOffset coord + sibOff child level)
def leafPad (w : WBytes) (coord : Nat) : Digest := V3.leafPad w coord
def handR (coord : Nat) : Nat := if coord = 9 then 768 else 144

def childInput (w : WBytes) (index coord physical : Nat) (padR value : Digest)
    (level : Nat) : HashInput :=
  let other := sibling w coord physical level
  let left := if physical / 2 ^ level % 2 = 0 then value else other
  let right := if physical / 2 ^ level % 2 = 0 then other else value
  V3.nodeInput coord index ((128 + physical) / 2 ^ (level + 1)) left
    (nodeHPad w coord physical level) (if level = 4 then padR else nodePad w coord physical level) right

def childN (w : WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128) (ends : List Digest)
    (padL padR : Digest) : M Digest := do
  let leaf ← shortHash (V3.leafInput k.val index raw.val padL ends)
  let j := physical k.val raw.val
  let n := lastLevel k.val
  let value ← (List.range n).foldlM
    (fun value level => shortHash (childInput w index k.val j padR value level)) leaf
  if k.val = 8 then shortHash (childInput w index k.val j padR value n)
  else V3.hashHi (childInput w index k.val j padR value n)

def childProgram (w : WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128)
    (ends : List Digest) : M Digest :=
  childN w index k raw ends (leafPad w k.val) (nodePad w k.val (physical k.val raw.val) 4)

def direction (coord child : Nat) : Nat := child / 2 ^ (lastLevel coord + 1) % 2

def topOtherOff (coord child : Nat) : Nat :=
  V3.regionOffset coord + (if direction coord child = 0 then handR (coord + 1) else 720) - 896

def topOther (w : WBytes) (coord child : Nat) : Digest := wdig w (topOtherOff coord child)

def orderPair (coord child : Nat) (computed other : Digest) : PairRoot :=
  if direction coord child = 0 then (computed, other) else (other, computed)

def initialPair (w : WBytes) : PairRoot :=
  (leafPad w 0, wdig w (V3.regionOffset 0 + 144))

def coordinate (w : WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128) (rank : Fin 666)
    (prev : PairRoot) : M PairRoot := do
  let ends ← V3.chainProgram w index k raw rank
  let computed ← childN w index k raw ends prev.1 prev.2
  pure (orderPair k.val (physical k.val raw.val) computed
    (topOther w k.val (physical k.val raw.val)))

def forest (w : WBytes) (index : Nat) (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 666) : M PairRoot :=
  (List.finRange 9).foldlM (fun prev k => coordinate w index k (raw k) (ranks k) prev) (initialPair w)

theorem physical_lt (coord raw : Nat) (h : raw < 128) : physical coord raw < 128 :=
  SharedForest.physicalChild_lt _ _ h

theorem lastLevel_cases (coord : Nat) : lastLevel coord = 4 ∨ lastLevel coord = 5 := by
  unfold lastLevel; split <;> simp

theorem pad4 (w : WBytes) (coord child : Nat) (h : child < 128) :
    nodePad w coord child 4 = wdig w (V3.regionOffset coord + 144) := by
  have hp := SharedPathPacking.planOK_all ⟨child, h⟩
  have hb : SharedPathPacking.block child 4 = 112 := by
    unfold SharedPathPacking.planOK at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.1.1
  simp only [nodePad, blkOff, show 4 < 5 by decide, ↓reduceIte, hb]
end W9Machine.SharedV3
