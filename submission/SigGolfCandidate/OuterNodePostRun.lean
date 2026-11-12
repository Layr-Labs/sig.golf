import SigGolfCandidate.OuterNodePostSplit
import SigGolfCandidate.OuterNodeRecordBounds
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodePostRun
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachineBlocks OuterNodeMachinePost OuterNodePostSplit

theorem take_code {im : Image} {pc : Word} {code : List (BitVec 32)} (hc : CodeAt im pc code) (n : Nat) :
    CodeAt im pc (code.take n) := by
  have hl : (code.take n).length≤code.length := by simp only [List.length_take];exact Nat.min_le_right _ _
  refine ⟨hc.1,hc.2.1,by have h:=hc.2.2.1;omega,?_⟩
  obtain ⟨post,hpost⟩:=hc.2.2.2
  exact ⟨code.drop n++post,by rw [←List.append_assoc,List.take_append_drop,hpost]⟩

theorem body_obligs (s : MachineState) (input : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input)
    (hi : input < 2^20) (hl : 2048 ≤ input) (hm : input % 8 = 0) : body.res.obligs s := by
  have hb:=OuterNodeRecordBounds.bounds s
  have hp:=b_post_obligs s input (recordAddr s).toNat ha hi hl hm (by simp) hb.1 hb.2.1 hb.2.2
  simp only [Result.obligs,b_post.res,body.res,Oblig.all] at hp ⊢
  exact hp.2.2

theorem body_frame (s : MachineState) (a : Word) (ha : a≠recordAddr s) :
    (body.res.toState s).getMem a=s.getMem a := by
  rw [Result.toState_getMem]
  apply memEval_frame
  intro p hp
  simp only [body.res,List.mem_cons,List.not_mem_nil,or_false] at hp
  subst p
  simpa [recordAddr,Addr.eval,E.eval,BinOp.eval] using ha

theorem body_nonce (s : MachineState) : (body.res.toState s).getMem (recordAddr s)=s.getReg .x6 := by
  simp [Result.toState_getMem,body.res,memEval_cons,Addr.eval,E.eval,BinOp.eval,recordAddr]

theorem tailB_obligs (s : MachineState) : tailB.res.obligs s := by simp [tailB.res,Result.obligs,Oblig.all]


theorem record_ne_low (s : MachineState) (a : Word) (ha : a.toNat<2^22) : a≠recordAddr s := by
  intro he
  rw [he] at ha
  have hb:=OuterNodeRecordBounds.bounds s
  omega

theorem runB {im : Image} (pc : Word) (hc : CodeAt im pc b_postCode) (s : MachineState)
    (hs : s.pc=pc) (input : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input)
    (hi : input < 2^20) (hl : 2048 ≤ input) (hm : input % 8 = 0) :
    ∃ t,Steps im s 9 9 t ∧ t.pc=pc-56#64 ∧ RegsExcept s t [.x6,.x7] ∧
      t.getMem (recordAddr s)=s.getReg .x6 ∧ t.getReg .x6=s.getMem 1152 ∧ t.getReg .x7=s.getMem 1160 ∧
      (∀ a,a≠recordAddr s→t.getMem a=s.getMem a) := by
  let r0 : Result:={body.res with pc:=.c (pc+24#64)}
  let u:=r0.toState s
  let r1 : Result:={tailB.res with pc:=.c (pc+24#64-80#64)}
  let t:=r1.toState u
  have hbody:=symRun_sound (body_at pc) (take_code hc 6) s hs (body_obligs s input ha hi hl hm)
  have htc : CodeAt im (pc+24#64) (b_postCode.drop 6) := by
    have h:=hc.tail.tail.tail.tail.tail.tail
    simpa only [b_postCode,List.drop,BitVec.add_assoc,BitVec.reduceAdd] using h
  have htail:=symRun_sound (tailB_at (pc+24#64)) htc u (by rfl) (tailB_obligs u)
  refine ⟨t,hbody.trans htail,?_,?_,?_,?_,?_,?_⟩
  · change pc+24#64-80#64=pc-56#64
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · intro r hr;cases r <;> simp at hr <;> rfl
  · change (body.res.toState s).getMem (recordAddr s)=s.getReg .x6
    exact body_nonce s
  · change (body.res.toState s).getMem 1152=s.getMem 1152
    exact body_frame s _ (record_ne_low s _ (by decide))
  · change (body.res.toState s).getMem 1160=s.getMem 1160
    exact body_frame s _ (record_ne_low s _ (by decide))
  · intro a hne
    change (body.res.toState s).getMem a=s.getMem a
    exact body_frame s a hne

theorem tailC_obligs (s : MachineState) : tailC.res.obligs s := tailB_obligs s

theorem runC {im : Image} (pc : Word) (hc : CodeAt im pc c_postCode) (s : MachineState)
    (hs : s.pc=pc) (input : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input)
    (hi : input < 2^20) (hl : 2048 ≤ input) (hm : input % 8 = 0) :
    ∃ t,Steps im s 9 9 t ∧ t.pc=pc-72#64 ∧ RegsExcept s t [.x6,.x7] ∧
      t.getMem (recordAddr s)=s.getReg .x6 ∧ t.getReg .x6=s.getMem 1152 ∧ t.getReg .x7=s.getMem 1160 ∧
      (∀ a,a≠recordAddr s→t.getMem a=s.getMem a) := by
  let r0 : Result:={body.res with pc:=.c (pc+24#64)}
  let u:=r0.toState s
  let r1 : Result:={tailC.res with pc:=.c (pc+24#64-96#64)}
  let t:=r1.toState u
  have hbody:=symRun_sound (body_at pc) (take_code hc 6) s hs (body_obligs s input ha hi hl hm)
  have htc : CodeAt im (pc+24#64) (c_postCode.drop 6) := by
    have h:=hc.tail.tail.tail.tail.tail.tail
    simpa only [c_postCode,List.drop,BitVec.add_assoc,BitVec.reduceAdd] using h
  have htail:=symRun_sound (tailC_at (pc+24#64)) htc u (by rfl) (tailC_obligs u)
  refine ⟨t,hbody.trans htail,?_,?_,?_,?_,?_,?_⟩
  · change pc+24#64-96#64=pc-72#64
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · intro r hr;cases r <;> simp at hr <;> rfl
  · change (body.res.toState s).getMem (recordAddr s)=s.getReg .x6
    exact body_nonce s
  · change (body.res.toState s).getMem 1152=s.getMem 1152
    exact body_frame s _ (record_ne_low s _ (by decide))
  · change (body.res.toState s).getMem 1160=s.getMem 1160
    exact body_frame s _ (record_ne_low s _ (by decide))
  · intro a hne
    change (body.res.toState s).getMem a=s.getMem a
    exact body_frame s a hne

#print axioms runB
#print axioms runC
#print axioms take_code
#print axioms body_obligs
#print axioms body_frame
#print axioms body_nonce
end OuterNodePostRun
