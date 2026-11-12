import SigGolfCandidate.OuterNodeBufferInput
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterNodeHandC
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.FtsGrind W9Drv.SharedCProof
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

theorem setup {im : Image} (j : Fin 128) (coord : Fin 9) (index : Nat)
    (hc : CodeAt im (pcOf (W9Drv.SharedCProof.childBase j.val)) (OuterNodeBankLayout.cWords j.val))
    {leaf pads sibs tws : Nat→Digest} {u s : MachineState}
    (hu : ChildPre j.val (coordRegion coord.val) coord.val index leaf pads sibs tws u)
    (v : Digest) (hs : Mid j.val (coordRegion coord.val) coord.val index u 5 v s) :
    ∃ t,Steps im s 4 4 t ∧
      OuterNodeSearchInvariant.Input (coordRegion coord.val+blkO j.val 5) (coordRegion coord.val-handO j.val)
        (OuterNodeRawModel.pre coord.val index (heapOf 5 j.val) (if bitAt j.val 5=0 then v else sibs 5))
        (OuterNodeRawModel.rightBytes (if bitAt j.val 5=0 then sibs 5 else v)) t ∧
      t.pc=pcOf (W9Drv.SharedCProof.childBase j.val+OuterNodeBankLayout.cSite j.val) ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r) ∧
      Frame u t (fun A=>∃ off∈stagesW j.val 6,A=coordRegion coord.val+off) := by
  have hg:=OuterNodeControllerGeometry.c_geometry coord j.val
  have hlo : 768≤coordRegion coord.val := by
    have h:=OuterNodeControllerGeometry.actual_frame coord
    rw [h]
    unfold OuterNodeBufferGeometry.frameBase
    have := coord.isLt
    omega
  obtain ⟨t,hst,h5,hvalid,hin,hpc,h11,h10,h12,hkeep,hframe,hleft,hhdr,hright⟩:=
    OuterNodeBankSetupC.last_setup j.isLt hc hu hlo v s hs
  have hh : nodeHeader coord.val index (heapOf 5 j.val) (hpOf j.val tws 5)=wctNodeHeader coord.val index (heapOf 5 j.val) := by
    exact OuterNodeBufferInput.header coord index _
  rw [hh] at hhdr
  exact ⟨t,hst,OuterNodeBufferInput.of_points _ _ _ _ _ _ _ t h5 h10 h11 h12 hleft hhdr hright hg,hpc,hkeep,hframe⟩

#print axioms setup
end OuterNodeHandC
