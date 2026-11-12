import SigGolfCandidate.OuterNodeHandB
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterNodeHandRunB
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind W9Drv.SharedBProof OuterNodeSearchInvariant
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

def Post (coord index j : Nat) (u : MachineState) (res : Nat×Digest) (t : MachineState) : Prop :=
  t.pc=pcOf (W9Drv.SharedBProof.childBase j+OuterNodeBankLayout.bSite j+2)-4#64 ∧
  t.getReg .x11=64 ∧ t.getReg .x12=BitVec.ofNat 64 (coordRegion coord-handO j) ∧
  DigAt t (coordRegion coord-handO j+16) res.2 ∧
  t.getMem (BitVec.ofNat 64 (8323072+(coord-1)*4096))=BitVec.ofNat 64 res.1 ∧
  (∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r=u.getReg r) ∧
  Frame u t (fun X=>(∃ off∈stagesW j 6,X=coordRegion coord+off) ∨
    Work (coordRegion coord+blkO j 5) (coordRegion coord-handO j) X ∨ X=8323072+(coord-1)*4096)

theorem run {im : Image} {sk : BitVec 256} (j : Fin 128) (coord : Fin 9) (index : Nat)
    (hc1 : 1≤coord.val) (hc8 : coord.val≠8) (hi : index<2^31)
    (hc : CodeAt im (pcOf (W9Drv.SharedBProof.childBase j.val)) (OuterNodeBankLayout.bWords j.val))
    {leaf pads sibs tws : Nat→Digest} {u s : MachineState}
    (hu : ChildPre j.val (coordRegion coord.val) coord.val index leaf pads sibs tws u)
    (v : Digest) (hs : Mid j.val (coordRegion coord.val) coord.val index u 5 v s) :
    TBSim im sk s 30739
      (OuterGroundCore.nodeAt coord.val index (heapOf 5 j.val)
        (if bitAt j.val 5=0 then v else sibs 5) (if bitAt j.val 5=0 then sibs 5 else v))
      (Post coord.val index j.val u) := by
  obtain ⟨mid,hst,F,hpc,hkeep,hframe⟩:=OuterNodeHandB.setup j coord index hc hu v hs
  have he:=OuterNodeBankCall.runB (sk:=sk) j hc8 F hc hpc
  refine (TBSim.steps hst he).mono (by omega) ?_
  intro res t ho
  have hd:=OuterNodeSourceFacts.digest ho
  have hoff : OuterGroundCore.offset coord.val (heapOf 5 j.val)=128 := by
    simp only [OuterGroundCore.offset,show ¬(coord.val=8 ∧ heapOf 5 j.val=3) from fun h=>hc8 h.1,if_false]
  rw [hoff] at hd
  have hh : heapOf 5 j.val=2 ∨ heapOf 5 j.val=3 := by
    unfold heapOf
    norm_num
    have := j.isLt
    omega
  have hn:=OuterNodeSourceFacts.record hc1 coord.isLt hi hh F ho
  obtain ⟨raw,hraw,hout⟩:=ho
  refine ⟨hout.at_pc,?_,?_,hd,hn,?_,?_⟩
  · rw [hout.regs.get (by simp)];exact F.x11
  · rw [hout.regs.get (by simp)];exact F.x12
  · intro r h3 h10 h11 h12
    rw [hout.regs.get (by simp)]
    exact hkeep r h3 h10 h11 h12
  · have hhdr:=OuterNodeInputHeader.input_header F coord.isLt hh
    have hr:=OuterNodeRecordHeader.record_address mid coord.val index hc1 coord.isLt hi (by
      rw [F.x10,ofNat_add_ofNat];exact hhdr.1)
    refine (hframe.trans hout.frame).mono ?_
    intro X hX hw
    rcases hw with hw|(hw|hw)
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
    · apply Or.inr ∘ Or.inr
      rw [hr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := coord.isLt;omega)] at hw
      exact hw

#print axioms run
end OuterNodeHandRunB
