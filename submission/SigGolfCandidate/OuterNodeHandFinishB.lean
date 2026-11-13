import SigGolfCandidate.OuterNodeHandRunB
import SigGolfCandidate.OuterNodeBankReturn
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterNodeHandFinishB
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind W9Drv.SharedBProof OuterNodeSearchInvariant
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

def Post (coord j : Nat) (u : MachineState) (res : Nat×Digest) (t : MachineState) : Prop :=
  t.pc=(u.getReg .x1+304#64) &&& ~~~1#64 ∧
  t.getReg .x11=64 ∧ t.getReg .x12=BitVec.ofNat 64 (coordRegion coord-handO j) ∧
  DigAt t (coordRegion coord-handO j+16) res.2 ∧
  t.getMem (BitVec.ofNat 64 (8323072+(coord-1)*4096))=BitVec.ofNat 64 res.1 ∧
  (∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r=u.getReg r) ∧
  Frame u t (fun X=>(∃ off∈stagesW j 6,X=coordRegion coord+off) ∨
    Work (coordRegion coord+blkO j 5) (coordRegion coord-handO j) X ∨ X=8323072+(coord-1)*4096)

theorem pc_return (base site : Nat) : pcOf (base+site+2)-4#64=pcOf (base+site+1) := by
  rw [OuterNodeHelper.pc_offset (base+site) 2,OuterNodeHelper.pc_offset (base+site) 1]
  change (pcOf (base+site)+8#64)-4#64=pcOf (base+site)+4#64
  simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rfl

theorem run {im : Image} {sk : BitVec 256} (j : Fin 128) (coord : Fin 9) (index : Nat)
    (hc1 : 1≤coord.val) (hc8 : coord.val≠8) (hi : index<2^31)
    (hc : CodeAt im (pcOf (W9Drv.SharedBProof.childBase j.val)) (OuterNodeBankLayout.bWords j.val))
    {leaf pads sibs tws : Nat→Digest} {u s : MachineState}
    (hu : ChildPre j.val (coordRegion coord.val) coord.val index leaf pads sibs tws u)
    (v : Digest) (hs : Mid j.val (coordRegion coord.val) coord.val index u 5 v s) :
    TBSim im sk s 61460
      (OuterGroundCore.nodeAt coord.val index (heapOf 5 j.val)
        (if bitAt j.val 5=0 then v else sibs 5) (if bitAt j.val 5=0 then sibs 5 else v))
      (Post coord.val j.val u) := by
  have h:=OuterNodeHandRunB.run (sk:=sk) j coord index hc1 hc8 hi hc hu v hs
  have ht : TBSim im sk s (61459+1)
      (OuterGroundCore.nodeAt coord.val index (heapOf 5 j.val)
        (if bitAt j.val 5=0 then v else sibs 5) (if bitAt j.val 5=0 then sibs 5 else v) >>= fun res=>pure res)
      (Post coord.val j.val u) := by
    refine TBSim.bind h ?_
    intro res t ho
    obtain ⟨hp,h11,h12,hd,hn,hkeep,hframe⟩:=ho
    rw [pc_return] at hp
    obtain ⟨z,hst,hpc,hg,hm⟩:=OuterNodeBankReturn.runB j hc t hp
    refine tb_pure_steps hst ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · rw [hpc,hkeep .x1 (by decide) (by decide) (by decide) (by decide)]
    · rw [hg];exact h11
    · rw [hg];exact h12
    · exact ⟨(hm _).trans hd.1,(hm _).trans hd.2⟩
    · rw [hm];exact hn
    · intro r h3 h10 h11 h12
      rw [hg];exact hkeep r h3 h10 h11 h12
    · intro X hX hne
      rw [hm];exact hframe X hX hne
  simpa only [bind_pure] using ht

#print axioms run
end OuterNodeHandFinishB
