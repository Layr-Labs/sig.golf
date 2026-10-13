import SigGolfCandidate.W9Machine.WctLayout
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
/-- C1 fold windows of child levels `0..4` (by `child % 32`): five packed windows in `[0, 320)`. The spec's
`authBase` carries the same table (`W9Drv.blkOff_auth`). -/
def ftsPlan : List (List Nat) :=
  [[16,64,112,160,192], [0,64,112,160,192], [16,80,144,192,224], [0,80,144,192,224],
   [16,64,128,192,224], [0,64,128,192,224], [64,0,128,192,224], [0,80,160,224,256],
   [16,64,112,176,224], [0,64,112,176,224], [16,80,144,208,256], [0,80,144,208,256],
   [16,144,80,208,256], [0,64,128,208,256], [64,0,128,208,256], [0,128,80,208,256],
   [16,64,112,240,176], [0,64,112,240,176], [64,0,112,240,176], [256,0,64,192,128],
   [16,64,128,192,256], [0,64,128,192,256], [64,0,128,192,256], [0,256,80,144,208],
   [16,64,192,128,256], [0,64,192,128,256], [64,0,192,128,256], [0,80,144,256,208],
   [16,144,80,256,208], [0,64,128,256,208], [64,0,128,256,208], [0,80,256,208,160]]
/-- Nested FTS (r1-1): fold block offset of child level `level` in a region. Levels 0..4 follow the child plan;
level 5 (heaps 2, 3) uses the fixed block at 832, `left | hdr | Z | right`. -/
def blkOff (child level : Nat) : Nat := if level < 5 then (ftsPlan.getD (child % 32) []).getD level 0 else 832
def sibOff (child level : Nat) : Nat := blkOff child level + 48 * (1 - child / 2 ^ level % 2)
def padOff (child level : Nat) : Nat := blkOff child level + 32
def nodePad (w : WBytes) (coord child level : Nat) : Digest := wdig w (regionOffset coord + padOff child level)
/-- The 16-byte tweak slot of a child level in the witness (`blkOff + 16`). -/
def nodeTw (w : WBytes) (coord child level : Nat) : Digest :=
  wdig w (regionOffset coord + blkOff child level + 16)
/-- High tweak word of a packed node (levels `< 4`): witness memory (honest 0), the verifier writes only the low
tweak word there (C1: also when the computed child is the left input); elsewhere 0. -/
def nodeHPad (w : WBytes) (coord child level : Nat) : BitVec 64 :=
  if level < 4 then (nodeTw w coord child level).extractLsb' 64 64 else 0
def sibling (w : WBytes) (coord child level : Nat) : Digest := wdig w (regionOffset coord + sibOff child level)
/-- FTS leaf pad slot (`regionOffset coord + 720`): tree `coord - 1`'s left top node in the nested FTS. -/
def leafPad (w : WBytes) (coord : Nat) : Digest := wdig w (regionOffset coord + 720)
/-- The high 16 bytes of a public hash: the value of a heap-2/3 node. -/
def hashHi (input : HashInput) : M Digest := do
  pure ((← publicHash input).extractLsb' 128 128)
/-- C1 (FTS Merkle half-swap): the value computed at child level `m` (the leaf for `m = 0`, the output of fold level
`m - 1` otherwise) takes the high half of its hash output when it is a left input at a heap in `16..255`. -/
def hiOut (child m : Nat) : Bool := decide (m ≤ 3) && decide (child / 2 ^ m % 2 = 0)
/-- The 16-byte node value of a public hash: high half if `hi`, low half otherwise. -/
def hashSel (hi : Bool) (input : HashInput) : M Digest := if hi then hashHi input else shortHash input
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
fold's pad slot. The leaf and levels 0..4 keep the half chosen by `hiOut`; level 5 keeps the high half. Returns the
computed top node. -/
def childN (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (ends : List Digest)
    (padL padZ : Digest) : M Digest := do
  let leaf ← hashSel (hiOut j.val 0) (leafInput k.val index j.val padL ends)
  let v ← (List.range 5).foldlM (fun value level =>
    let other := sibling w k.val j.val level
    let left := if j.val / 2 ^ level % 2 = 0 then value else other
    let right := if j.val / 2 ^ level % 2 = 0 then other else value
    hashSel (hiOut j.val (level + 1)) (nodeInput k.val index ((128 + j.val) / 2 ^ (level + 1))
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
