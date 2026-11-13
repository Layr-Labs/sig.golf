import SigGolfCandidate.OuterSignExit
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSignSearchB
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant OuterSignBlocks

theorem check {im : Image} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {a : HashOutput} (F : Input A D pre right s)
    (hc : CodeAt im (pcOf 26179) b_checkCode) (hu : Stage s A D (pcOf 26179) n u)
    (hh : Answer A D n a u) :
    ∃ t,Steps im u 3 3 t ∧
      Stage s A D (if zeroOkH true 5 a then pcOf 26201 else pcOf 26182) n t ∧ Answer A D n a t := by
  have gx : u.getReg .x12=BitVec.ofNat 64 D := by rw [hu.regs.get (by decide)];exact F.x12
  have hob : b_check.res.obligs u := OuterNodeMachineCheck.b_check_obligs u D gx F.dhi F.dlo F.da
  let t:=b_check.res.toState u
  have hs:=symRun_sound b_check hc u hu.at_pc hob
  have hr : RegsExcept u t [.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hm : ∀ x,t.getMem x=u.getMem x := fun _=>rfl
  have ho : u.getMem (u.getReg .x12+24#64)=a.extractLsb' 192 64 := by
    rw [gx,ofNat_add_ofNat];exact hh.output 3 (by decide)
  have hp : t.pc=(if zeroOkH true 5 a then pcOf 26201 else pcOf 26182) := by
    change (b_check.res.toState u).pc=_
    simp only [Result.toState_pc,b_check.res,E.eval,RegFile.get,Addr.eval,BinOp.eval,CmpOp.eval,ho]
    norm_num only [BitVec.toNat_ofNat]
    simp only [beq_iff_eq]
    by_cases hz : zeroOkH true 5 a=true
    · have hb : (a.extractLsb' 192 64 >>> 59)=0#64 := (OuterNodeSearchB.ok a).mp hz
      simp only [if_pos hz,if_pos hb]
    · have hb : ¬(a.extractLsb' 192 64 >>> 59)=0#64 := fun h=>hz ((OuterNodeSearchB.ok a).mpr h)
      simp only [if_neg hz,if_neg hb]
  refine ⟨t,hs,hu.readOnly hp (hr.mono (by simp)) ?_ hm,hh.readOnly hm⟩
  rw [hr.get (by decide)];exact hu.nonce

theorem jump_exhaust {im : Image} (hc : CodeAt im (pcOf 26185) b_exhaustCode)
    (s : MachineState) (hp : s.pc=pcOf 26185) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 26201 ∧ RegsExcept s t [] ∧ (∀ a,t.getMem a=s.getMem a) := by
  refine ⟨b_exhaust.res.toState s,symRun_sound b_exhaust hc s hp (by simp [b_exhaust.res,Result.obligs,Oblig.all]),rfl,?_,?_⟩
  · intro r _;cases r <;> rfl
  · intro a;rfl

theorem retry {im : Image} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {a : HashOutput} (F : Input A D pre right s)
    (hc : CodeAt im (pcOf 26179) b_checkCode) (hf : CodeAt im (pcOf 26182) b_retryCode)
    (hu : Stage s A D (pcOf 26179) n u) (hh : Answer A D n a u)
    (hz : ¬zeroOkH true 5 a=true) (hn : n+1<4096) :
    ∃ t,Steps im u 6 6 t ∧ Stage s A D (pcOf 26177) (n+1) t := by
  obtain ⟨v,hs,hv,hav⟩:=check F hc hu hh
  simp only [if_neg hz] at hv
  obtain ⟨t,ht,hr,h6,hp,hm⟩:=OuterNodeCounterRun.runB (pcOf 26182) hf v hv.at_pc n (by omega) hv.nonce
  rw [if_pos hn] at hp
  exact ⟨t,hs.trans ht,hv.readOnly hp hr h6 hm⟩

theorem finish {im : Image} {sk : BitVec 256} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {a : HashOutput} (F : Input A D pre right s)
    (hc : CodeAt im (pcOf 26179) b_checkCode)
    (hp : CodeAt im (pcOf 26201) cleanupCode) (hd : CodeAt im (pcOf 26204) doneCode)
    (hu : Stage s A D (pcOf 26179) n u) (hh : Answer A D n a u)
    (hz : zeroOkH true 5 a=true) :
    TBSim im sk u 12 (pure (n,a)) (OuterSignExit.Out s A D) := by
  obtain ⟨v,hs,hv,hav⟩:=check F hc hu hh
  simp only [if_pos hz] at hv
  exact (TBSim.steps hs (OuterSignExit.run F hp hd hv hav)).mono (by omega) (by intros;assumption)

theorem exhaust {im : Image} {sk : BitVec 256} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {a : HashOutput} (F : Input A D pre right s)
    (hc : CodeAt im (pcOf 26179) b_checkCode) (hf : CodeAt im (pcOf 26182) b_retryCode)
    (hj : CodeAt im (pcOf 26185) b_exhaustCode)
    (hp : CodeAt im (pcOf 26201) cleanupCode) (hd : CodeAt im (pcOf 26204) doneCode)
    (hu : Stage s A D (pcOf 26179) n u) (hh : Answer A D n a u)
    (hz : ¬zeroOkH true 5 a=true) (hn : n+1=4096) :
    TBSim im sk u 16 (pure (n,a)) (OuterSignExit.Out s A D) := by
  obtain ⟨v,hs,hv,hav⟩:=check F hc hu hh
  simp only [if_neg hz] at hv
  obtain ⟨t,ht,hr,h6,hpt,hm⟩:=OuterNodeCounterRun.runB (pcOf 26182) hf v hv.at_pc n (by omega) hv.nonce
  have hpt' : t.pc=pcOf 26185 := by simpa only [show ¬n+1<4096 by omega,if_false,show pcOf 26182+12#64=pcOf 26185 from by decide] using hpt
  have htv:=hv.readOnly hpt' hr h6 hm
  have hat:=hav.readOnly hm
  obtain ⟨w,hw,hwp,hwr,hwm⟩:=jump_exhaust hj t hpt'
  have hwv:=htv.readOnly hwp (hwr.mono (by simp)) (by rw [hwr.get (by simp)];exact h6) hwm
  have haw:=hat.readOnly hwm
  exact (TBSim.steps (hs.trans (ht.trans hw)) (OuterSignExit.run F hp hd hwv haw)).mono (by omega) (by intros;assumption)

theorem loop {im : Image} {sk : BitVec 256} {A D : Nat} {pre right : List UInt8}
    {s : MachineState} (F : Input A D pre right s)
    (hq : CodeAt im (pcOf 26177) b_preCode) (hc : CodeAt im (pcOf 26179) b_checkCode)
    (hf : CodeAt im (pcOf 26182) b_retryCode) (hj : CodeAt im (pcOf 26185) b_exhaustCode)
    (hp : CodeAt im (pcOf 26201) cleanupCode) (hd : CodeAt im (pcOf 26204) doneCode) :
    ∀ fuel n u,Stage s A D (pcOf 26177) n u → n+fuel+1=4096 →
      TBSim im sk u (15*fuel+25) (searchH true 5 pre right fuel n) (OuterSignExit.Out s A D) := by
  refine OuterNodeLoopControl.loop_sim true 5 4096 3 pre right (Stage s A D (pcOf 26177))
    (fun n a u=>Stage s A D (pcOf 26179) n u ∧ Answer A D n a u)
    (OuterSignExit.Out s A D) ?_ ?_ ?_ ?_
  · intro β n u hu hn W f Q hk
    exact trial F hq hu (by omega) (fun a t ht ha=>hk a t ⟨ht,ha⟩)
  · intro n a u hu hn hz
    exact finish F hc hp hd hu.1 hu.2 hz
  · intro n a u hu hz hn
    exact retry F hc hf hu.1 hu.2 hz hn
  · intro n a u hu hz hn
    exact exhaust F hc hf hj hp hd hu.1 hu.2 hz hn

#print axioms finish
#print axioms exhaust
#print axioms loop

#print axioms check
#print axioms jump_exhaust
end OuterSignSearchB
