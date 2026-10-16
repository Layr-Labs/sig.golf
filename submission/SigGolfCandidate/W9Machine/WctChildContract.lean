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
output), the next region's leaf pad (bit 6 = 0) or Z slot (bit 6 = 1). -/
def handAddr (k : Fin 9) (j : Fin 128) : Nat :=
  if j.val / 64 % 2 = 0 then coordinateBase k - 176 else coordinateBase k - 32
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

/-! A concrete instruction prototype for the proposed paired forest. It is not
installed in `Frozen.image` or in the current `Child.Good` proof. -/
namespace W9Machine.SharedPathPrototype
open SigGolfCandidate.Research.SharedPathPacking
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3 (Digest M)
open SigGolfCandidate.T3M.Verify

/-- A stops at heaps 4..7. B continues to heaps 2..3. -/
def levels (first : Bool) : Nat := if first then 5 else 6
def blockOff (j l : Nat) : Nat := if l < 5 then block j l else 832
def currentOff (j l : Nat) : Nat := blockOff j l + 48 * bitAt j l
def heap (j l : Nat) : Nat := 2 ^ (6 - l) + j / 2 ^ (l + 1)
def heapRegNumber (h : Nat) : Nat := [0,9,13,19,20,21,26,30].getD h 30

/-- Final hashes keep the high half. The receiving pair uses L at 720 and R at
144 in the next 896-byte region. A's pair direction is bit 5; B's is bit 6. -/
def handOffset (first : Bool) (j : Nat) : Nat :=
  if bitAt j (if first then 5 else 6) = 0 then 192 else 768
/-- All routines address the working region through x8. The final singleton
has a separate table with a shorter right-handoff offset. -/
def handBaseRegister (_first : Bool) (_j : Nat) : Nat := 8
def skipOutput (first : Bool) (j l : Nat) : Bool :=
  decide (l + 1 < levels first) && decide (currentOff j (l + 1) = currentOff j l)
def encI (rd rs imm : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (imm % 4096 * 2 ^ 20 + rs * 2 ^ 15 + rd * 2 ^ 7 + 0x13)
def encS (rs2 off rs1 : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (off / 32 * 2 ^ 25 + rs2 * 2 ^ 20 + rs1 * 2 ^ 15 +
    3 * 2 ^ 12 + off % 32 * 2 ^ 7 + 0x23)
def levelWords (first : Bool) (j l : Nat) : List (BitVec 32) :=
  [encI 10 8 (blockOff j l)] ++
    (if l < 4 then [encI 3 15 (4096 - heap j l), encS 3 16 10] ++
      (if bitAt j l = 0 then [encS 0 24 10] else [])
     else [encS 15 16 10, encS (heapRegNumber (heap j l)) 24 10]) ++
    (if skipOutput first j l then [] else
      [if l + 1 = levels first then
        encI 12 (handBaseRegister first j) (4096 - handOffset first j)
       else encI 12 8 (currentOff j (l + 1))]) ++ [0x00000073]
def coreWords (first : Bool) (j : Nat) : List (BitVec 32) :=
  [0, encI 12 8 (currentOff j 0), 0x00000073, encI 11 0 64] ++
    (List.range (levels first)).flatMap (levelWords first j) ++ [0x12808067]
def words (first : Bool) (j : Nat) : List (BitVec 32) :=
  coreWords first j ++ List.replicate (64 - (coreWords first j).length) 0x00000013
/-- Counts normal instructions, the two-block leaf HASH, and the one-block
node HASHes. The leading zero trap is not executed. -/
def cycles (first : Bool) (j : Nat) : Nat :=
  (coreWords first j).length - (levels first + 2) + 16 + 8 * levels first

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exact_costs : ∀ j : Fin 128,
    cycles true j.val = 83 - saves j.val ∧
    cycles false j.val = 95 - saves j.val ∧
    (words true j.val).length = 64 ∧ (words false j.val).length = 64 := by
  intro j
  fin_cases j <;> decide +kernel

/-- The eventual refinement contract: all five/six node inputs, including
the new R pad at level four, must match the selected source computation. -/
def Refines (im : Image) (first : Bool) (j : Fin 128)
    (pre : MachineState → Prop)
    (source : M Digest)
    (post : MachineState → Digest → MachineState → Prop) (P : Hash → Prop := HashOk) : Prop :=
  ∀ (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Digest → OracleComp HashSpec Obs), pre u →
    (∀ computed t, post u computed t → GoodQFor (P := P) im t N C Q A (K computed)) →
    GoodQFor (P := P) im u (N + 38) (C + cycles first j.val) Q
      (A + cycles first j.val) (SigGolfCandidate.T3M.Verify.ccM source K)
end W9Machine.SharedPathPrototype

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

def handAddr (k : Fin 9) (raw : Fin 128) : Nat :=
  if SharedV3.direction k.val (SharedV3.physical k.val raw.val) = 0 then coordinateBase k - 176
  else if k.val = 8 then coordinateBase k - 128 else coordinateBase k - 752

def outputAddr (k : Fin 9) (raw : Fin 128) : Nat :=
  if k.val = 8 then handAddr k raw else handAddr k raw - 16

def writes (k : Fin 9) (raw : Fin 128) (A : Nat) : Prop :=
  (coordinateBase k ≤ A ∧ A < coordinateBase k + 912) ∨
    (outputAddr k raw ≤ A ∧ A < outputAddr k raw + 32)

structure Post (L : Layout) (k : Fin 9) (raw : Fin 128) (u : MachineState)
    (computed : Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf (L.returnWord k + (if k.val = 8 then 79 else 74))
  hashLen : t.getReg .x11 = 64
  top : DigAt t (handAddr k raw) computed
  a2 : t.getReg .x12 = BitVec.ofNat 64 (outputAddr k raw)
  keep : ∀ r, r ∉ Child.clobbers → t.getReg r = u.getReg r
  frame : Frame u t (writes k raw)

def spill (k : Fin 9) (raw : Fin 128) : Nat :=
  if SharedV3.first k.val ∧ raw.val % 16 = 0 then 1 else 0

def cost (k : Fin 9) (raw : Fin 128) : Nat :=
  (if SharedV3.first k.val then 83 else 95) -
    SigGolfCandidate.Research.SharedPathPacking.saves (SharedV3.physical k.val raw.val) + spill k raw

def Good (L : Layout) (k : Fin 9) (raw : Fin 128) (P : Hash → Prop := HashOk) : Prop :=
  ∀ (w : WBytes) (index : Nat) (ends : List Digest) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Digest → OracleComp HashSpec Obs),
    Pre L w index k raw ends u →
    (∀ computed t, Post L k raw u computed t → GoodQFor (P := P) L.image t N C Q A (K computed)) →
    GoodQFor (P := P) L.image u (N + 39) (C + 96) Q (A + cost k raw)
      (ccM (SharedV3.childProgram w index k raw ends) K)
end W9Machine.SharedChild
