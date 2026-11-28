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

/-- C47: the c8 grinder's exit: the record is the constant slot `0x7fb000` and the exit pc the jump target. -/
def SourceOutC (heap : Nat) (s : MachineState) (A D : Nat) (ret : Word) (res : Nat × Digest) (t : MachineState) : Prop :=
  ∃ raw,OuterNodeRawModel.keep 8 heap raw=res ∧ OuterNodeSearchExit.OutC s A D ret raw t

theorem runC {im : Image} {sk : BitVec 256} {b A D index heap : Nat} {left right : Digest}
    {s : MachineState} (hheap : heap=2 ∨ heap=3)
    (hmem : s.getMem (BitVec.ofNat 64 (A+24))=0#64 ↔ heap=2)
    (F : Input A D (OuterNodeRawModel.pre 8 index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hb : b+25<2^18) (hc : CodeAt im (pcOf b) (OuterNodeHelper.cCode b)) (hp : s.pc=pcOf b) :
    TBSim im sk s 77838 (nodeAt 8 index heap left right) (SourceOutC heap s A D (pcOf 46862)) := by
  rw [nodeAt,OuterNodeRawModel.source_eq]
  apply map_sim
  have hr:=OuterNodeHelper.runC (sk:=sk) F heap hheap hmem hb hc hp
  have hraw : OuterNodeRawModel.raw 8 index heap left right (cap 8-1) 0=
      searchH (OuterNodeSearchC.high heap) 4 (OuterNodeRawModel.pre 8 index heap left)
        (OuterNodeRawModel.rightBytes right) 4095 0 := by
    simp [OuterNodeRawModel.raw,OuterNodeRawModel.high,OuterNodeSearchC.high,cap,OuterGroundCore.width]
  rw [hraw]
  exact hr.mono (by omega) (fun a t ht=>⟨a,rfl,ht⟩)

/-- C47: the c8 grinder's nonce record (`0x7fb000 = 8323072 + (15 - 8 / 2) * 4096`). -/
theorem recordC {heap A D : Nat} {s t : MachineState} {ret : Word} {res : Nat × Digest}
    (hout : SourceOutC heap s A D ret res t) :
    t.getMem (BitVec.ofNat 64 (8323072+(15-8/2)*4096))=BitVec.ofNat 64 res.1 := by
  obtain ⟨raw,hkeep,ho⟩:=hout
  have hn : raw.1=res.1 := congrArg Prod.fst hkeep
  rw [← hn]
  exact ho.record

/-- C47: the c8 grinder's kept digest at `D + offset 8 heap / 8`. -/
theorem digestC {heap A D : Nat} {s t : MachineState} {ret : Word} {res : Nat × Digest}
    (hout : SourceOutC heap s A D ret res t) :
    DigAt t (D+offset 8 heap/8) res.2 := by
  obtain ⟨raw,hkeep,ho⟩:=hout
  have hv : value 8 heap raw.2=res.2 := congrArg Prod.snd hkeep
  rw [←hv]
  have h:=ho.answer
  by_cases hz : heap=3
  · simp only [value,offset,hz,and_self,if_true,Nat.zero_div,Nat.add_zero]
    constructor
    · rw [BitVec.extractLsb'_extractLsb'_of_le (by decide)]
      exact h.output 0 (by decide)
    · rw [BitVec.extractLsb'_extractLsb'_of_le (by decide)]
      exact h.output 1 (by decide)
  · simp only [value,offset,hz,and_false,if_false,show 128/8=16 from rfl]
    constructor
    · rw [h.output 2 (by decide)]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
      omega
    · rw [show D+16+8=D+8*3 by omega,h.output 3 (by decide),OuterNodeHashZero.high_word]

#print axioms runB
#print axioms runC
#print axioms recordC
#print axioms digestC
end OuterNodeSourceSim
