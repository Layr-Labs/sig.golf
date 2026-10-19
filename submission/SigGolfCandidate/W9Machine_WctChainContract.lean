import SigGolfCandidate.W9Machine_WctChildContract
set_option Elab.async false

set_option autoImplicit false
namespace W9Machine.Chain
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
abbrev table := headerTable
abbrev program := V3.chainProgram
structure Pre (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 666) (u : MachineState) : Prop where
  indexBound : index < 2 ^ 31
  pc : u.pc = pcOf (L.chainWord rank)
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (base L k)
  leafWord : u.getReg .x31 = BitVec.ofNat 64 (V3.leafLow index k.val j.val)
  nodeWord : u.getReg .x15 = BitVec.ofNat 64 (V3.nodeLow k.val index)
  hashMode : u.getReg .x5 = 0
  stepOne : u.getReg .x7 = 1
  stepTwo : u.getReg .x13 = 2
  hashLen : u.getReg .x11 = 64
  childPC : u.getReg .x23 = pcOf (L.childWord j)
  returnPC : u.getReg .x1 = pcOf (L.returnWord k)
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (Child.heapReg h) = BitVec.ofNat 64 h
  witness : ∀ off, off < 848 → off % 8 = 0 →
    u.getMem (BitVec.ofNat 64 (base L k + off)) =
      w.extractLsb' (8 * (V3.regionOffset k.val + off)) 64
def writes (L : Layout) (k : Fin 9) (A : Nat) : Prop := base L k + 336 ≤ A ∧ A < base L k + 784
def clobbers : List Reg := [.x3, .x10, .x11, .x12, .x14, .x25]
structure Post (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (u : MachineState) (ends : List Digest) (t : MachineState) : Prop where
  length : ends.length = 6
  child : Child.Pre L w index k j ends t
  keep : ∀ r, r ∉ clobbers → t.getReg r = u.getReg r
  frame : Frame u t (writes L k)
def Good (L : Layout) (rank : Fin 666) (P : Hash → Prop := HashOk) : Prop :=
  ∀ (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : List Digest → OracleComp HashSpec Obs),
    Pre L w index k j rank u →
    (∀ ends t, Post L w index k j u ends t → GoodQFor (P := P) L.image t N C Q A (K ends)) →
    GoodQFor (P := P) L.image u (N + 89) (C + 89) Q (A + 89)
      (ccM (program w index k j rank) K)
def AllGood (L : Layout) (P : Hash → Prop := HashOk) : Prop := ∀ rank : Fin 666, Good L rank (P := P)
end W9Machine.Chain
