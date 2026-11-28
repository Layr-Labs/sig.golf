import SigGolfCandidate.OuterSignDispatch
import SigGolfCandidate.OuterSignImageLayout
import SigGolfCandidate.OuterSignSearchB
import SigGolfCandidate.OuterSignSearchC
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSignCanonical
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant OuterGroundCore

theorem run_raw {im : Image} {sk : BitVec 256} {A D coord index heap : Nat} {left right : Digest}
    {s : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hA : A=328448) (hc : 1≤coord) (hc9 : coord<9) (hi : index<2^31) (hh : heap=2 ∨ heap=3) (hco : coord%2=1 ∨ coord=8)
    (hcode : CodeAt im (pcOf 26156) OuterSignImageLayout.code) (hcls : OuterSignEntry.ClsAt im) (hp : s.pc=pcOf 26156) :
    TBSim im sk s 77858 (OuterNodeRawModel.raw coord index heap left right (cap coord-1) 0)
      (OuterSignExit.Out s A D) := by
  obtain ⟨c0,ca,cl,cfd,ce,cc,bs,bq,bc,bf,bj,cs,cq,cck,cf,cj,cp,cd⟩:=OuterSignImageLayout.slices hcode
  obtain ⟨u,hs,hu⟩:=OuterSignEntry.save_run (A:=A) (D:=D) c0 s hp
  have ck : CodeAt im (pcOf 26161) OuterSignBlocks.hookCode := codeAt_sub 5 hcode (by decide) (by rfl)
  obtain ⟨v,hr,hv⟩:=OuterSignDispatch.route F hA hc hc9 hi hh hco ca ck hcls hu
  have hrs:=OuterSignDispatch.routeSteps_le coord heap
  by_cases h8 : coord=8
  · subst coord
    have hrs8:=OuterSignDispatch.routeSteps_le8 heap
    simp only [if_pos rfl] at hv
    obtain ⟨w,hw,hwv⟩:=OuterSignEntry.start_run F cs hv
    have hwv' : Stage s A D (pcOf 26188) 0 w := by
      simpa only [show pcOf 26186+8#64=pcOf 26188 from by decide] using hwv
    have he:=OuterSignSearchC.loop (sk:=sk) F heap hh
      (OuterNodeInputHeader.input_hi8 F hh) cq cck cf cj cp cd 4095 0 w hwv' (by decide)
    have he' : TBSim im sk w 77834 (OuterNodeRawModel.raw 8 index heap left right (cap 8-1) 0)
        (OuterSignExit.Out s A D) := by
      simpa [OuterNodeRawModel.raw,OuterNodeRawModel.high,OuterNodeSearchC.high,cap,OuterGroundCore.width] using he
    exact (TBSim.steps (hs.trans (hr.trans hw)) he').mono (by omega) (by intros;assumption)
  · simp only [if_neg h8] at hv
    obtain ⟨w,hw,hwv⟩:=OuterSignEntry.start_run F bs hv
    have hwv' : Stage s A D (pcOf 26177) 0 w := by
      simpa only [show pcOf 26175+8#64=pcOf 26177 from by decide] using hwv
    have he:=OuterSignSearchB.loop (sk:=sk) F bq bc bf bj cp cd 4095 0 w hwv' (by decide)
    have he' : TBSim im sk w 61450 (OuterNodeRawModel.raw coord index heap left right (cap coord-1) 0)
        (OuterSignExit.Out s A D) := by
      simpa [OuterNodeRawModel.raw,OuterNodeRawModel.high,cap,OuterGroundCore.width,h8] using he
    exact (TBSim.steps (hs.trans (hr.trans hw)) he').mono (by omega) (by intros;assumption)

def Out (coord heap : Nat) (s : MachineState) (A D : Nat) (res : Nat × Digest) (t : MachineState) : Prop :=
  ∃ raw,OuterNodeRawModel.keep coord heap raw=res ∧ OuterSignExit.Out s A D raw t

theorem run {im : Image} {sk : BitVec 256} {A D coord index heap : Nat} {left right : Digest}
    {s : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hA : A=328448) (hc : 1≤coord) (hc9 : coord<9) (hi : index<2^31) (hh : heap=2 ∨ heap=3) (hco : coord%2=1 ∨ coord=8)
    (hcode : CodeAt im (pcOf 26156) OuterSignImageLayout.code) (hcls : OuterSignEntry.ClsAt im) (hp : s.pc=pcOf 26156) :
    TBSim im sk s 77858 (nodeAt coord index heap left right) (Out coord heap s A D) := by
  rw [nodeAt,OuterNodeRawModel.source_eq]
  apply OuterNodeSourceSim.map_sim
  exact (run_raw F hA hc hc9 hi hh hco hcode hcls hp).mono (by omega) (fun a t ht=>⟨a,rfl,ht⟩)

#print axioms run_raw
#print axioms run
end OuterSignCanonical
