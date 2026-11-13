import SigGolfCandidate.OuterNodeHelper
import SigGolfCandidate.OuterNodeRawModel
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeSourceSim
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant OuterGroundCore

theorem map_sim {α β : Type} {im : Image} {sk : BitVec 256} {s : MachineState} {W : Nat}
    {p : M α} (f : α→β) {Q : β→MachineState→Prop}
    (h : TBSim im sk s W p (fun a t=>Q (f a) t)) : TBSim im sk s W (f <$> p) Q := by
  rw [map_eq_bind_pure_comp]
  have hh:=TBSim.bind h (fun a t ht=>TBSim.pure ht)
  simpa only [Nat.add_zero,Function.comp_def] using hh

def SourceOut (coord heap : Nat) (s : MachineState) (A D : Nat) (ret : Word)
    (res : Nat × Digest) (t : MachineState) : Prop :=
  ∃ raw,OuterNodeRawModel.keep coord heap raw=res ∧ OuterNodeSearchExit.Out s A D ret raw t

theorem runB {im : Image} {sk : BitVec 256} {b A D coord index heap : Nat} {left right : Digest}
    {s : MachineState} (hc8 : coord≠8)
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hc : CodeAt im (pcOf b) OuterNodeHelper.bCode) (hp : s.pc=pcOf b) :
    TBSim im sk s 61454 (nodeAt coord index heap left right)
      (SourceOut coord heap s A D (pcOf b-4#64)) := by
  rw [nodeAt,OuterNodeRawModel.source_eq]
  apply map_sim
  have hr:=OuterNodeHelper.runB (sk:=sk) F hc hp
  have hraw : OuterNodeRawModel.raw coord index heap left right (cap coord-1) 0=
      searchH true 5 (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) 4095 0 := by
    simp [OuterNodeRawModel.raw,OuterNodeRawModel.high,cap,OuterGroundCore.width,hc8]
  rw [hraw]
  exact hr.mono (by omega) (fun a t ht=>⟨a,rfl,ht⟩)

theorem runC {im : Image} {sk : BitVec 256} {b A D index heap : Nat} {left right : Digest}
    {s : MachineState} (hheap : heap=2 ∨ heap=3)
    (hmem : s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 heap)
    (F : Input A D (OuterNodeRawModel.pre 8 index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hc : CodeAt im (pcOf b) OuterNodeHelper.cCode) (hp : s.pc=pcOf b) :
    TBSim im sk s 77838 (nodeAt 8 index heap left right)
      (SourceOut 8 heap s A D (pcOf b-4#64)) := by
  rw [nodeAt,OuterNodeRawModel.source_eq]
  apply map_sim
  have hr:=OuterNodeHelper.runC (sk:=sk) F heap hheap hmem hc hp
  have hraw : OuterNodeRawModel.raw 8 index heap left right (cap 8-1) 0=
      searchH (OuterNodeSearchC.high heap) 4 (OuterNodeRawModel.pre 8 index heap left)
        (OuterNodeRawModel.rightBytes right) 4095 0 := by
    simp [OuterNodeRawModel.raw,OuterNodeRawModel.high,OuterNodeSearchC.high,cap,OuterGroundCore.width]
  rw [hraw]
  exact hr.mono (by omega) (fun a t ht=>⟨a,rfl,ht⟩)

#print axioms runB
#print axioms runC
end OuterNodeSourceSim
