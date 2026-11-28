import SigGolfCandidate.OuterNodeHandC
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterNodeHandRunC
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind W9Drv.SharedCProof OuterNodeSearchInvariant
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

/-- C47: the c8 grinder jumps straight to the expand continuation `pcOf 46862`; the nonce record is the constant slot
`8323072 + 11 * 4096` (= `8323072 + (15 - 8 / 2) * 4096`). -/
def Post (coord index j : Nat) (u : MachineState) (res : Nat×Digest) (t : MachineState) : Prop :=
  t.pc=pcOf 46862 ∧
  t.getReg .x11=64 ∧ t.getReg .x12=BitVec.ofNat 64 (coordRegion coord-handO j) ∧
  DigAt t (coordRegion coord-handO j+OuterGroundCore.offset coord (heapOf 5 j)/8) res.2 ∧
  t.getMem (BitVec.ofNat 64 (8323072+(15-coord/2)*4096))=BitVec.ofNat 64 res.1 ∧
  (∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r=u.getReg r) ∧
  Frame u t (fun X=>(∃ off∈stagesW j 6,X=coordRegion coord+off) ∨
    Work (coordRegion coord+blkO j 5) (coordRegion coord-handO j) X ∨ X=8323072+(15-coord/2)*4096)

theorem run {im : Image} {sk : BitVec 256} (j : Fin 128) (coord : Fin 9) (index : Nat)
    (hc1 : 1≤coord.val) (hc8 : coord.val=8) (hi : index<2^31)
    (hc : CodeAt im (pcOf (W9Drv.SharedCProof.childBase j.val)) (OuterNodeBankLayout.cWords j.val))
    {leaf pads sibs tws : Nat→Digest} {u s : MachineState}
    (hu : ChildPre j.val (coordRegion coord.val) coord.val index leaf pads sibs tws u)
    (v : Digest) (hs : Mid j.val (coordRegion coord.val) coord.val index u 5 v s) :
    TBSim im sk s 77843
      (OuterGroundCore.nodeAt coord.val index (heapOf 5 j.val)
        (if bitAt j.val 5=0 then v else sibs 5) (if bitAt j.val 5=0 then sibs 5 else v))
      (Post coord.val index j.val u) := by
  obtain ⟨mid,hst,F,hpc,hkeep,hframe⟩:=OuterNodeHandC.setup j coord index hc hu v hs
  have hh : heapOf 5 j.val=2 ∨ heapOf 5 j.val=3 := by
    unfold heapOf
    norm_num
    have := j.isLt
    omega
  have F' : Input (coordRegion coord.val+blkO j.val 5) (coordRegion coord.val-handO j.val)
      (OuterNodeRawModel.pre 8 index (heapOf 5 j.val) (if bitAt j.val 5=0 then v else sibs 5))
      (OuterNodeRawModel.rightBytes (if bitAt j.val 5=0 then sibs 5 else v)) mid := by
    simpa only [hc8] using F
  have he:=OuterNodeBankCall.runC (sk:=sk) j hh F' hc hpc
  have he' : TBSim im sk mid 77839
      (OuterGroundCore.nodeAt coord.val index (heapOf 5 j.val)
        (if bitAt j.val 5=0 then v else sibs 5) (if bitAt j.val 5=0 then sibs 5 else v))
      (OuterNodeSourceSim.SourceOutC (heapOf 5 j.val) mid (coordRegion coord.val+blkO j.val 5)
        (coordRegion coord.val-handO j.val) (pcOf 46862)) := by
    simpa only [hc8] using he
  refine (TBSim.steps hst he').mono (by omega) ?_
  intro res t ho
  have hd:=OuterNodeSourceSim.digestC ho
  have hn:=OuterNodeSourceSim.recordC ho
  obtain ⟨raw,hraw,hout⟩:=ho
  refine ⟨hout.at_pc,?_,?_,by simpa only [hc8] using hd,by rw [hc8];exact hn,?_,?_⟩
  · rw [hout.regs.get (by simp)];exact F.x11
  · rw [hout.regs.get (by simp)];exact F.x12
  · intro r h3 h10 h11 h12
    rw [hout.regs.get (by simp)]
    exact hkeep r h3 h10 h11 h12
  · refine (hframe.trans hout.frame).mono ?_
    intro X hX hw
    rcases hw with hw|(hw|hw)
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
    · apply Or.inr ∘ Or.inr
      rw [hc8];exact hw

#print axioms run
end OuterNodeHandRunC
