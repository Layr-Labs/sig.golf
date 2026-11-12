import SigGolfCandidate.OuterSignStubBlocks
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignInterface
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (M HashOutput)
open SigGolfCandidate.FtsGrind

def Writes (D X : Nat) : Prop := SignW D X ∨ X=1152 ∨ X=1160

structure Out (s : MachineState) (ret heap D b : Nat) (res : Nat×HashOutput) (t : MachineState) : Prop where
  pc : t.pc=pcOf ret
  regs : RegsExcept s t []
  ans : ∀ k<4,t.getMem (BitVec.ofNat 64 (D+8*k))=res.2.extractLsb' (64*k) 64
  sv0 : t.getMem 1104=0
  sv1 : t.getMem 1112=0
  sv4 : t.getMem 1136=0
  sv3 : 8≤heap ∧ heap<16→t.getMem 1128=0
  sv3p : ¬(8≤heap ∧ heap<16)→t.getMem 1128=s.getMem 1128
  frame : Frame s t (Writes D)

theorem Out.of_old {s t : MachineState} {ret heap D b : Nat} {res : Nat×HashOutput}
    (h : SignOut s ret heap D b res t) : Out s ret heap D b res t :=
  ⟨h.pc,h.regs,h.ans,h.sv0,h.sv1,h.sv4,h.sv3,h.sv3p,h.frame.mono (fun _ _ hw=>Or.inl hw)⟩

def program (b heap : Nat) (sel : Bool) (pre right : List UInt8) (plain : M (Nat×HashOutput)) : M (Nat×HashOutput) :=
  if 8≤heap ∧ heap<16 then groundFold b pre right else
  if G16 sel heap then groundFoldH (decide (heap%2=0)) 1 pre right else plain
#print axioms Out.of_old
end OuterSignInterface
