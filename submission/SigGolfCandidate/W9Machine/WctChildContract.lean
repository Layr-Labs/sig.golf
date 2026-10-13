import SigGolfCandidate.W9Machine.WctV3Source

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
  childIdx : u.getReg .x4 = BitVec.ofNat 64 j.val
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
def Good (L : Layout) (b : Budget) (j : Fin 128) : Prop :=
  ∀ (w : WBytes) (index : Nat) (k : Fin 9) (ends : List Digest) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Digest → OracleComp HashSpec Obs),
    Pre L w index k j ends u →
    (∀ computed t, Post L k j u computed t → GoodQFor L.image t N C Q A (K computed)) →
    GoodQFor L.image u (N + b.fuel) (C + b.allCycles) Q (A + b.acceptCycles)
      (ccM (V3.childProgram w index k j ends) K)
end W9Machine.Child
