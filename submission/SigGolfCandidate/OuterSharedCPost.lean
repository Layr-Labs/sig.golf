import SigGolfCandidate.OuterSharedCFrame
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterSharedCPost
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open W9Machine W9Drv.SharedCProof SigGolfCandidate.FtsGrind
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

theorem post_of {L : W9Machine.Layout} (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9)
    (raw : Fin 128) (ends : List Digest) (x : MachineState) (hf : SharedV3.first k.val=false) (hc : k.val=8)
    (hx : SharedChild.Pre L w index k raw ends x) (hbase : Chain.base L k=coordRegion k.val)
    (r : Nat×Nat×Nat×Digest) (t : MachineState)
    (ht : OuterCopyChildFlatC.Post k.val (SharedV3.physical k.val raw.val) (bankPc (SharedV3.physical k.val raw.val) x) r t) :
    OuterSharedPost.Post L k raw x (r.2.2.2,r.1,r.2.1,r.2.2.1) t := by
  have hk0 : k.val≠0 := by intro he;simp [SharedV3.first,he] at hf
  have hb : 768≤Chain.base L k := by unfold Chain.base coordinateBase Layout.shift;have := k.isLt;omega
  have hh0 : Chain.base L k-valO (SharedV3.physical k.val raw.val)=SharedChild.handAddr L k raw := by
    unfold SharedChild.handAddr SharedV3.direction SharedV3.lastLevel valO bitAt
    simp only [hf,if_pos hc,Bool.false_eq_true,↓reduceIte]
    split_ifs <;> omega
  have hh : Chain.base L k-handO (SharedV3.physical k.val raw.val)+
      OuterGroundCore.offset k.val (heapOf 5 (SharedV3.physical k.val raw.val))/8=SharedChild.handAddr L k raw := by
    rw [←hh0]
    simp only [hc]
    have hj:=SharedV3.physical_lt k.val raw.val raw.isLt
    rw [hc] at hj
    unfold handO valO bitAt OuterGroundCore.offset heapOf
    norm_num only [Nat.reducePow,Nat.reduceSub,Nat.reduceAdd,reduceCtorEq,and_self]
    split_ifs <;> simp_all only [true_and,Nat.reduceDiv] <;> omega
  have ho : Chain.base L k-handO (SharedV3.physical k.val raw.val)=SharedChild.outputAddr L k raw := by
    unfold SharedChild.outputAddr SharedChild.handAddr SharedV3.direction SharedV3.lastLevel handO bitAt
    simp only [hf,if_pos hc,Bool.false_eq_true,↓reduceIte]
    split_ifs <;> omega
  have hsel:=(OuterChildModel.widths k).2
  refine ⟨?_,ht.a1,?_,?_,?_,?_,?_,?_,?_,?_,ht.nle16,?_,fun _=>ht.outer,?_,ht.saves,ht.scr,?_,?_⟩
  · rw [ht.pc]
    change (x.getReg .x1+_) &&& _=_
    rw [hx.returnPC]
    simp only [if_pos hc,↓reduceIte]
    change (pcOf (L.returnWord k)+BitVec.ofNat 64 (4*79)) &&& ~~~1#64=_
    rw [W9Drv.SharedBank.pcOf_add_words,pcOf_and_not1]
  · rw [←hh,hbase];exact ht.top
  · rw [ht.a2,←hbase,ho]
  · intro reg hr
    simp only [Child.clobbers,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    exact ht.keep reg hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1
  · rw [hbase,ht.slot0]
    rfl
  · rw [hbase];exact ht.slot1
  · simpa only [(OuterChildModel.widths k).1] using ht.nle
  · intro hk
    rw [hbase,ht.rec0 (by rw [hsel];exact decide_eq_true hk)]
    rfl
  · intro hk
    rw [hbase]
    exact ht.rec1 (by rw [hsel];exact decide_eq_true hk)
  · intro hk
    exact ht.n0 (by rw [hsel];exact decide_eq_false (by omega))
  · intro he
    rw [hf] at he
    cases he
  · intro hk
    exact ht.scr16 (by rw [hsel];exact decide_eq_true hk)
  · intro addr ha hn
    apply ht.frame addr ha
    intro hw
    apply hn
    have hg:=OuterSharedCFrame.allowed k ⟨_,SharedV3.physical_lt _ _ raw.isLt⟩ addr hw
    rcases hg with hold|he
    · left
      rw [←hbase] at hold
      unfold OuterSharedCFrame.OldWrites at hold
      rcases hold with h|h|h|h|h|h
      · left;unfold SharedChild.writes;unfold prefixWrites at h;left;split <;> omega
      · left;unfold SharedChild.writes;right;rw [←ho];exact h
      · right;left;exact h
      · right;right;left;left;exact h
      · right;right;left;right;exact h
      · rcases h with h|h|h
        · right;right;right;left;exact h
        · right;right;left;left;exact h
        · right;right;right;right;exact h
    · right;exact he

#print axioms post_of
end OuterSharedCPost
