import SigGolfCandidate.OuterForestFrame
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterForestRecords
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
open ClaudeWCT.W9.Machine.Expand
open ClaudeWCT.W9.Machine.Expand.SharedForestRun (RecInv RecInv16)
open OuterForestFrame
theorem rec_next {image : Image} {w : W9Machine.WBytes} {index : Nat} {raw : Fin 9 → Fin 128}
    {u entry t : MachineState} {k : Fin 9} {ns : List Nat}
    {ends : List Digest} {res : Digest × Nat × Nat × Nat} (hr : RecInv raw k.val ns u)
    (hp : Chain.Post (SharedDispatch.layout image k) (SharedV3.viewWB 2904 w k.val u) index k (raw k)
      ((SharedDispatch.result k.val).toState u) ends entry)
    (ht : OuterSharedPost.Post (SharedDispatch.layout image k) k (raw k) entry res t) :
    RecInv raw (k.val+1) (ns++[res.2.1]) t := by
  have hk:=k.isLt
  have hf:=core_frame_dispatch hp ht
  have hb:Chain.base (SharedDispatch.layout image k) k=9768-848*k.val := by
    rw [SharedDispatch.layout_base]; unfold coordinateBase; omega
  have hlen:=hr.len
  have keep (m : Fin 9) (hm : m.val<k.val) (o : Nat) (ho : o<16) :
      t.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slotA (9768-848*m.val)+o))=
        u.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slotA (9768-848*m.val)+o)) := by
    apply hf _ (by unfold SigGolfCandidate.FtsGrind.slotA SigGolfCandidate.FtsGrind.SCR; omega)
    intro hw
    have hw : SharedForestRun.childW (SharedDispatch.layout image k) k (raw k) (SigGolfCandidate.FtsGrind.slotA (9768-848*m.val)+o) := by
      rcases hw with hw|hx
      · exact hw
      · rcases hx with hx|hx|hx <;> simp only [OuterSharedPost.record,SigGolfCandidate.FtsGrind.slotA,SigGolfCandidate.FtsGrind.SCR,SigGolfCandidate.FtsGrind.SCR16] at hx <;> omega
    rcases hw with hw|hw|hw
    · simp only [SharedChild.writes, SharedChild.outputAddr, SharedChild.handAddr, SharedDispatch.layout_base] at hw
      unfold coordinateBase SigGolfCandidate.FtsGrind.slotA SigGolfCandidate.FtsGrind.SCR at hw
      split_ifs at hw <;> omega
    · unfold SharedChild.recW SigGolfCandidate.FtsGrind.slotA at hw
      rw [hb] at hw
      have := m.isLt
      unfold SigGolfCandidate.FtsGrind.slotA at *
      omega
    · rcases hw with hw|hw
      · unfold SharedChild.scratchW SigGolfCandidate.FtsGrind.slotA SigGolfCandidate.FtsGrind.SCR at hw
        omega
      · unfold SharedChild.recW16 SigGolfCandidate.FtsGrind.slot16 SigGolfCandidate.FtsGrind.slotA
          SigGolfCandidate.FtsGrind.SCR16 SigGolfCandidate.FtsGrind.SCR at hw
        rw [hb] at hw
        omega
  have gd_old (m : Nat) (hm : m<k.val) : (ns++[res.2.1]).getD m 0=ns.getD m 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show m<ns.length by omega)]
  have gd_new : (ns++[res.2.1]).getD k.val 0=res.2.1 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (show ns.length≤k.val by omega), hlen,
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  refine ⟨by simp [hlen],?_,?_,?_,fun _=>ht.saves,fun _=>ht.scr⟩
  · intro m hm
    rcases Nat.lt_or_ge m.val k.val with h|h
    · have := keep m h 0 (by decide)
      rw [Nat.add_zero] at this
      rw [this]; exact hr.slot0 m h
    · obtain rfl : m=k := Fin.ext (by omega)
      have := ht.slot0
      rw [hb] at this
      exact this
  · intro m hm
    rcases Nat.lt_or_ge m.val k.val with h|h
    · rw [keep m h 8 (by decide), gd_old _ h]; exact hr.slot1 m h
    · obtain rfl : m=k := Fin.ext (by omega)
      have := ht.slot1
      rw [hb] at this
      rw [gd_new]; exact this
  · intro m hm
    rcases Nat.lt_or_ge m.val k.val with h|h
    · rw [gd_old _ h]; exact hr.nle m h
    · obtain rfl : m=k := Fin.ext (by omega)
      rw [gd_new]; exact ht.nle

theorem rec16_next {image : Image} {w : W9Machine.WBytes} {index : Nat} {raw : Fin 9 → Fin 128}
    {u entry t : MachineState} {k : Fin 9} {ns : List Nat}
    {ends : List Digest} {res : Digest × Nat × Nat × Nat} (hr : RecInv16 raw k.val ns u)
    (hp : Chain.Post (SharedDispatch.layout image k) (SharedV3.viewWB 2904 w k.val u) index k (raw k)
      ((SharedDispatch.result k.val).toState u) ends entry)
    (ht : OuterSharedPost.Post (SharedDispatch.layout image k) k (raw k) entry res t) :
    RecInv16 raw (k.val+1) (ns++[res.2.2.1]) t := by
  have hk:=k.isLt
  have hf:=core_frame_dispatch hp ht
  have hb:Chain.base (SharedDispatch.layout image k) k=9768-848*k.val := by
    rw [SharedDispatch.layout_base]; unfold coordinateBase; omega
  have hlen:=hr.len
  have keep (m : Fin 9) (hm : m.val<k.val) (o : Nat) (ho : o<16) :
      t.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot16 (9768-848*m.val)+o))=
        u.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot16 (9768-848*m.val)+o)) := by
    apply hf _ (by unfold SigGolfCandidate.FtsGrind.slot16 SigGolfCandidate.FtsGrind.SCR16; omega)
    intro hw
    have := m.isLt
    have hw : SharedForestRun.childW (SharedDispatch.layout image k) k (raw k) (SigGolfCandidate.FtsGrind.slot16 (9768-848*m.val)+o) := by
      rcases hw with hw|hx
      · exact hw
      · rcases hx with hx|hx|hx <;> simp only [OuterSharedPost.record,SigGolfCandidate.FtsGrind.slot16,SigGolfCandidate.FtsGrind.SCR,SigGolfCandidate.FtsGrind.SCR16] at hx <;> omega
    rcases hw with hw|hw|hw|hw
    · simp only [SharedChild.writes, SharedChild.outputAddr, SharedChild.handAddr, SharedDispatch.layout_base] at hw
      unfold coordinateBase SigGolfCandidate.FtsGrind.slot16 SigGolfCandidate.FtsGrind.SCR16 at hw
      split_ifs at hw <;> omega
    · unfold SharedChild.recW SigGolfCandidate.FtsGrind.slotA SigGolfCandidate.FtsGrind.SCR at hw
      unfold SigGolfCandidate.FtsGrind.slot16 SigGolfCandidate.FtsGrind.SCR16 at hw
      rw [hb] at hw
      omega
    · unfold SharedChild.scratchW SigGolfCandidate.FtsGrind.SCR at hw
      unfold SigGolfCandidate.FtsGrind.slot16 SigGolfCandidate.FtsGrind.SCR16 at hw
      omega
    · unfold SharedChild.recW16 SigGolfCandidate.FtsGrind.slot16 SigGolfCandidate.FtsGrind.SCR16 at hw
      rw [hb] at hw
      omega
  have gd_old (m : Nat) (hm : m<k.val) : (ns++[res.2.2.1]).getD m 0=ns.getD m 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show m<ns.length by omega)]
  have gd_new : (ns++[res.2.2.1]).getD k.val 0=res.2.2.1 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (show ns.length≤k.val by omega), hlen,
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  refine ⟨by simp [hlen],?_,?_,?_,?_⟩
  · intro m hm h4
    rcases Nat.lt_or_ge m.val k.val with h|h
    · have := keep m h 0 (by decide)
      rw [Nat.add_zero] at this
      rw [this]; exact hr.slot0 m h h4
    · obtain rfl : m=k := Fin.ext (by omega)
      have := ht.rec0 h4
      rw [hb] at this
      exact this
  · intro m hm h4
    rcases Nat.lt_or_ge m.val k.val with h|h
    · rw [keep m h 8 (by decide), gd_old _ h]; exact hr.slot1 m h h4
    · obtain rfl : m=k := Fin.ext (by omega)
      have := ht.rec1 h4
      rw [hb] at this
      rw [gd_new]; exact this
  · intro m hm
    rcases Nat.lt_or_ge m.val k.val with h|h
    · rw [gd_old _ h]; exact hr.nle m h
    · obtain rfl : m=k := Fin.ext (by omega)
      rw [gd_new]; exact ht.nle16
  · intro m hm h4
    rcases Nat.lt_or_ge m.val k.val with h|h
    · rw [gd_old _ h]; exact hr.n0 m h h4
    · obtain rfl : m=k := Fin.ext (by omega)
      rw [gd_new]; exact ht.n0 h4


#print axioms rec_next
#print axioms rec16_next
end OuterForestRecords
