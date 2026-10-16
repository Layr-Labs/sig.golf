import SigGolfCandidate.W9Machine.WctV3Source
import SigGolfCandidate.Research.V7Composed198Gate

set_option autoImplicit false
namespace W9Machine.Child
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
def heapReg : Nat → Reg
  | 2 => .x13 | 3 => .x19 | 4 => .x20 | 5 => .x21 | 6 => .x26 | 7 => .x30
  | _ => .x0
structure Pre (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) (u : MachineState) : Prop where
  indexBound : index < 2 ^ 31
  length : ends.length = 6
  pc : u.pc = pcOf (L.childWord j + 1)
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (coordinateBase k)
  hashMode : u.getReg .x5 = 0
  hashInput : u.getReg .x10 = BitVec.ofNat 64 (coordinateBase k + 688)
  hashLen : u.getReg .x11 = 128
  nodeWord : u.getReg .x15 = BitVec.ofNat 64 (V3.nodeLow k.val index)
  returnPC : u.getReg .x1 = pcOf (L.returnWord k)
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (heapReg h) = BitVec.ofNat 64 h
  leafAt : ∀ i, i < 8 → DigAt u (coordinateBase k + 688 + 16 * i)
    (V3.leafFields k.val index j.val (V3.leafPad w k.val) ends i)
  padAt : ∀ l, l < 6 → DigAt u (coordinateBase k + V3.padOff j.val l) (V3.nodePad w k.val j.val l)
  sibAt : ∀ l, l < 6 → DigAt u (coordinateBase k + V3.sibOff j.val l) (V3.sibling w k.val j.val l)
  twAt : ∀ l, l < 6 → DigAt u (coordinateBase k + V3.blkOff j.val l + 16) (V3.nodeTw w k.val j.val l)
/-- Nested FTS hand-off: the computed top node of tree `k` lands at this address (high half of the heap-2/3 fold
output), the next region's leaf pad (bit 6 = 0) or Z slot (bit 6 = 1). Witness trim: for `k = 8` the virtual
region's slots are `WIT + 0` (`- 80`) and the R9 slot `WIT + 64` (`- 16`). -/
def handAddr (k : Fin 9) (j : Fin 128) : Nat :=
  if k.val = 8 then (if j.val / 64 % 2 = 0 then coordinateBase k - 80 else coordinateBase k - 16)
  else if j.val / 64 % 2 = 0 then coordinateBase k - 176 else coordinateBase k - 32
def writes (k : Fin 9) (j : Fin 128) (A : Nat) : Prop :=
  (coordinateBase k ≤ A ∧ A < coordinateBase k + 912) ∨ (handAddr k j - 16 ≤ A ∧ A < handAddr k j + 16)
def clobbers : List Reg := [.x3, .x10, .x11, .x12, .x14]
structure Post (L : Layout) (k : Fin 9) (j : Fin 128) (u : MachineState)
    (computed : Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf (L.returnWord k + 74)
  hashLen : t.getReg .x11 = 64
  top : DigAt t (handAddr k j) computed
  a2 : t.getReg .x12 = BitVec.ofNat 64 (handAddr k j - 16)
  keep : ∀ r, r ∉ clobbers → t.getReg r = u.getReg r
  frame : Frame u t (writes k j)
def Good (L : Layout) (b : Budget) (j : Fin 128) (P : Hash → Prop := HashOk) : Prop :=
  ∀ (w : WBytes) (index : Nat) (k : Fin 9) (ends : List Digest) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Digest → OracleComp HashSpec Obs),
    Pre L w index k j ends u →
    (∀ computed t, Post L k j u computed t → GoodQFor (P := P) L.image t N C Q A (K computed)) →
    GoodQFor (P := P) L.image u (N + b.fuel) (C + b.allCycles) Q (A + b.acceptCycles)
      (ccM (V3.childProgram w index k j ends) K)
end W9Machine.Child

namespace W9Machine.SharedChild
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
structure Pre (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) (u : MachineState) : Prop where
  indexBound : index < 2 ^ 31
  length : ends.length = 6
  pc : u.pc = pcOf (L.childWord j + 1)
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (coordinateBase k)
  hashMode : u.getReg .x5 = 0
  hashInput : u.getReg .x10 = BitVec.ofNat 64 (coordinateBase k + 688)
  hashLen : u.getReg .x11 = 128
  nodeWord : u.getReg .x15 = BitVec.ofNat 64 (V3.nodeLow k.val index)
  returnPC : u.getReg .x1 = pcOf (L.returnWord k)
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (Child.heapReg h) = BitVec.ofNat 64 h
  leafAt : ∀ i, i < 8 → DigAt u (coordinateBase k + 688 + 16 * i)
    (V3.leafFields k.val index j.val (V3.leafPad w k.val) ends i)
  padAt : ∀ l, l < 6 → DigAt u (coordinateBase k + SharedV3.blkOff (SharedV3.physical k.val j.val) l + 32) (SharedV3.nodePad w k.val (SharedV3.physical k.val j.val) l)
  sibAt : ∀ l, l < 6 → DigAt u (coordinateBase k + SharedV3.sibOff (SharedV3.physical k.val j.val) l) (SharedV3.sibling w k.val (SharedV3.physical k.val j.val) l)
  twAt : ∀ l, l < 6 → DigAt u (coordinateBase k + SharedV3.blkOff (SharedV3.physical k.val j.val) l + 16) (SharedV3.nodeTw w k.val (SharedV3.physical k.val j.val) l)

/-- Where the computed top value lands: the next region's leaf pad (`- 176`, direction 0) or its R pad (`- 736` =
next region `+ 160`, direction 1); the final singleton (merged "Cm", stage 2) puts its left root on `WIT + 0`
(direction 0) and its right root on `WIT + 48` (direction 1); witness trim: `WIT = 1312 = coordinateBase 8 - 80`. -/
def handAddr (k : Fin 9) (raw : Fin 128) : Nat :=
  if SharedV3.direction k.val (SharedV3.physical k.val raw.val) = 0 then
    (if k.val = 8 then coordinateBase k - 80 else coordinateBase k - 176)
  else if k.val = 8 then coordinateBase k - 32 else coordinateBase k - 736

/-- Start of the 32-byte hash output carrying the computed top value: 16 bytes below the value for a high-half
value (every A/B child, and the singleton's left root, heap 2, stage 2 Cm: the junk low half lands on
`WIT - 16 .. WIT - 1`), at the value itself for the singleton's right root (heap 3, low half at `WIT + 48`). -/
def outputAddr (k : Fin 9) (raw : Fin 128) : Nat :=
  if k.val = 8 then
    (if SharedV3.direction k.val (SharedV3.physical k.val raw.val) = 0 then handAddr k raw - 16 else handAddr k raw)
  else handAddr k raw - 16

def writes (k : Fin 9) (raw : Fin 128) (A : Nat) : Prop :=
  (coordinateBase k ≤ A ∧ A < coordinateBase k + 912) ∨
    (outputAddr k raw ≤ A ∧ A < outputAddr k raw + 32)

structure Post (L : Layout) (k : Fin 9) (raw : Fin 128) (u : MachineState)
    (computed : Digest) (t : MachineState) : Prop where
  /-- A/B return with `jalr zero,296(ra)`; the singleton (Cm, stage 2) with `jalr zero,320(ra)`, i.e. to word 854 for
  `returnWord 8 = 774`, the L3 entry. -/
  pc : t.pc = pcOf (L.returnWord k + (if k.val = 8 then 80 else 74))
  hashLen : t.getReg .x11 = 64
  top : DigAt t (handAddr k raw) computed
  a2 : t.getReg .x12 = BitVec.ofNat 64 (outputAddr k raw)
  keep : ∀ r, r ∉ Child.clobbers → t.getReg r = u.getReg r
  frame : Frame u t (writes k raw)

/-- C1: every A routine fits its 32-word table slot, so no child takes the old spill jump. Kept (as 0) for the
interface of `cost`. -/
def spill (_k : Fin 9) (_raw : Fin 128) : Nat := 0

/-- C1 output offset (region-relative) of the hash computing the child-level-`m` value: `curO - 16` for a
high-half value (`SharedV3.hiOut`), `curO` otherwise. -/
def outOff (child m : Nat) : Nat :=
  SharedV3.blkOff child m + 48 * (child / 2 ^ m % 2) - (if SharedV3.hiOut child m then 16 else 0)

/-- C1 `skips′`: the elided `addi a2` words of a child routine (levels `0..3` whose output address equals the
previous one). The value depends only on `child % 32`; it is 0, 1 or 2 and sums to 42 over the 32 classes. -/
def skips (child : Nat) : Nat :=
  ((List.range 4).map fun l => if outOff child (l + 1) = outOff child l then 1 else 0).sum

/-- Exact cycles of a child routine: A `79 - skips′` (29 - skips′ instructions, seven hashed blocks), B and C
`91 - skips′` (34 - skips′ instructions, eight blocks). -/
def cost (k : Fin 9) (raw : Fin 128) : Nat :=
  (if SharedV3.first k.val then 79 else 91) - skips (SharedV3.physical k.val raw.val) + spill k raw

def Good (L : Layout) (k : Fin 9) (raw : Fin 128) (P : Hash → Prop := HashOk) : Prop :=
  ∀ (w : WBytes) (index : Nat) (ends : List Digest) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Digest → OracleComp HashSpec Obs),
    Pre L w index k raw ends u →
    (∀ computed t, Post L k raw u computed t → GoodQFor (P := P) L.image t N C Q A (K computed)) →
    GoodQFor (P := P) L.image u (N + 39) (C + 96) Q (A + cost k raw)
      (ccM (SharedV3.childProgram w index k raw ends) K)
end W9Machine.SharedChild
