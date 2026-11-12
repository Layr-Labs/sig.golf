import SigGolfCandidate.OuterSignExit
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSignSearchC
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant OuterSignBlocks

theorem check {im : Image} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {a : HashOutput} (F : Input A D pre right s)
    (heap : Nat) (hheap : heap=2 ∨ heap=3)
    (hmem : s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 heap)
    (hc : CodeAt im (pcOf 26190) c_checkCode) (hu : Stage s A D (pcOf 26190) n u)
    (hh : Answer A D n a u) :
    ∃ t,Steps im u 7 7 t ∧
      Stage s A D (if zeroOkH (OuterNodeSearchC.high heap) 4 a then pcOf 26201 else pcOf 26197) n t ∧
      Answer A D n a t := by
  have h:=OuterNodeSearchC.check (pc:=pcOf 26188) F heap hheap hmem hc hu hh
  simpa only [show pcOf 26188+52#64=pcOf 26201 from by decide,
    show pcOf 26188+36#64=pcOf 26197 from by decide] using h

theorem jump_exhaust {im : Image} (hc : CodeAt im (pcOf 26200) c_exhaustCode)
    (s : MachineState) (hp : s.pc=pcOf 26200) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 26201 ∧ RegsExcept s t [] ∧ (∀ a,t.getMem a=s.getMem a) := by
  refine ⟨c_exhaust.res.toState s,symRun_sound c_exhaust hc s hp (by simp [c_exhaust.res,Result.obligs,Oblig.all]),rfl,?_,?_⟩
  · intro r _;cases r <;> rfl
  · intro a;rfl

theorem retry {im : Image} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {a : HashOutput} (F : Input A D pre right s) (heap : Nat) (hheap : heap=2 ∨ heap=3)
    (hmem : s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 heap)
    (hc : CodeAt im (pcOf 26190) c_checkCode) (hf : CodeAt im (pcOf 26197) c_retryCode)
    (hu : Stage s A D (pcOf 26190) n u) (hh : Answer A D n a u)
    (hz : ¬zeroOkH (OuterNodeSearchC.high heap) 4 a=true) (hn : n+1<4096) :
    ∃ t,Steps im u 10 10 t ∧ Stage s A D (pcOf 26188) (n+1) t := by
  obtain ⟨v,hs,hv,hav⟩:=check F heap hheap hmem hc hu hh
  simp only [if_neg hz] at hv
  obtain ⟨t,ht,hr,h6,hp,hm⟩:=OuterNodeCounterRun.runC (pcOf 26197) hf v hv.at_pc n (by omega) hv.nonce
  rw [if_pos hn] at hp
  exact ⟨t,hs.trans ht,hv.readOnly hp hr h6 hm⟩

theorem finish {im : Image} {sk : BitVec 256} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {a : HashOutput} (F : Input A D pre right s) (heap : Nat) (hheap : heap=2 ∨ heap=3)
    (hmem : s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 heap)
    (hc : CodeAt im (pcOf 26190) c_checkCode)
    (hp : CodeAt im (pcOf 26201) cleanupCode) (hd : CodeAt im (pcOf 26204) doneCode)
    (hu : Stage s A D (pcOf 26190) n u) (hh : Answer A D n a u)
    (hz : zeroOkH (OuterNodeSearchC.high heap) 4 a=true) :
    TBSim im sk u 16 (pure (n,a)) (OuterSignExit.Out s A D) := by
  obtain ⟨v,hs,hv,hav⟩:=check F heap hheap hmem hc hu hh
  simp only [if_pos hz] at hv
  exact (TBSim.steps hs (OuterSignExit.run F hp hd hv hav)).mono (by omega) (by intros;assumption)

theorem exhaust {im : Image} {sk : BitVec 256} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {a : HashOutput} (F : Input A D pre right s) (heap : Nat) (hheap : heap=2 ∨ heap=3)
    (hmem : s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 heap)
    (hc : CodeAt im (pcOf 26190) c_checkCode) (hf : CodeAt im (pcOf 26197) c_retryCode)
    (hj : CodeAt im (pcOf 26200) c_exhaustCode)
    (hp : CodeAt im (pcOf 26201) cleanupCode) (hd : CodeAt im (pcOf 26204) doneCode)
    (hu : Stage s A D (pcOf 26190) n u) (hh : Answer A D n a u)
    (hz : ¬zeroOkH (OuterNodeSearchC.high heap) 4 a=true) (hn : n+1=4096) :
    TBSim im sk u 20 (pure (n,a)) (OuterSignExit.Out s A D) := by
  obtain ⟨v,hs,hv,hav⟩:=check F heap hheap hmem hc hu hh
  simp only [if_neg hz] at hv
  obtain ⟨t,ht,hr,h6,hpt,hm⟩:=OuterNodeCounterRun.runC (pcOf 26197) hf v hv.at_pc n (by omega) hv.nonce
  have hpt' : t.pc=pcOf 26200 := by simpa only [show ¬n+1<4096 by omega,if_false,show pcOf 26197+12#64=pcOf 26200 from by decide] using hpt
  have htv:=hv.readOnly hpt' hr h6 hm
  have hat:=hav.readOnly hm
  obtain ⟨w,hw,hwp,hwr,hwm⟩:=jump_exhaust hj t hpt'
  have hwv:=htv.readOnly hwp (hwr.mono (by simp)) (by rw [hwr.get (by simp)];exact h6) hwm
  have haw:=hat.readOnly hwm
  exact (TBSim.steps (hs.trans (ht.trans hw)) (OuterSignExit.run F hp hd hwv haw)).mono (by omega) (by intros;assumption)

theorem loop {im : Image} {sk : BitVec 256} {A D : Nat} {pre right : List UInt8}
    {s : MachineState} (F : Input A D pre right s) (heap : Nat) (hheap : heap=2 ∨ heap=3)
    (hmem : s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 heap)
    (hq : CodeAt im (pcOf 26188) c_preCode) (hc : CodeAt im (pcOf 26190) c_checkCode)
    (hf : CodeAt im (pcOf 26197) c_retryCode) (hj : CodeAt im (pcOf 26200) c_exhaustCode)
    (hp : CodeAt im (pcOf 26201) cleanupCode) (hd : CodeAt im (pcOf 26204) doneCode) :
    ∀ fuel n u,Stage s A D (pcOf 26188) n u → n+fuel+1=4096 →
      TBSim im sk u (19*fuel+29) (searchH (OuterNodeSearchC.high heap) 4 pre right fuel n) (OuterSignExit.Out s A D) := by
  refine OuterNodeLoopControl.loop_sim (OuterNodeSearchC.high heap) 4 4096 7 pre right (Stage s A D (pcOf 26188))
    (fun n a u=>Stage s A D (pcOf 26190) n u ∧ Answer A D n a u)
    (OuterSignExit.Out s A D) ?_ ?_ ?_ ?_
  · intro β n u hu hn W f Q hk
    exact trial F hq hu (by omega) (fun a t ht ha=>hk a t ⟨ht,ha⟩)
  · intro n a u hu hn hz
    exact finish F heap hheap hmem hc hp hd hu.1 hu.2 hz
  · intro n a u hu hz hn
    exact retry F heap hheap hmem hc hf hu.1 hu.2 hz hn
  · intro n a u hu hz hn
    exact exhaust F heap hheap hmem hc hf hj hp hd hu.1 hu.2 hz hn

#print axioms finish
#print axioms exhaust
#print axioms loop

#print axioms check
#print axioms jump_exhaust
end OuterSignSearchC
