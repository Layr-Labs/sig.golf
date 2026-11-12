import SigGolfCandidate.OuterSignBlocks
import SigGolfCandidate.OuterNodeSearchInvariant
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSignExit
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant OuterSignBlocks

structure Out (s : MachineState) (A D : Nat) (res : Nat × HashOutput) (t : MachineState) : Prop where
  at_pc : t.pc=pcOf 25339
  regs : RegsExcept s t []
  output : ∀ k<4,t.getMem (BitVec.ofNat 64 (D+8*k))=res.2.extractLsb' (64*k) 64
  pad32 : t.getMem (BitVec.ofNat 64 (A+32))=0
  pad40 : t.getMem (BitVec.ofNat 64 (A+40))=0
  frame : Frame s t (Work A D)

theorem cleanup_obligs (s : MachineState) (A : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 A)
    (hi : A<2^20) (hlo : 2048≤A) (hm : A%8=0) : cleanup.res.obligs s := by
  simp [cleanup.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
    memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
  omega

theorem cleanup_value (s : MachineState) (A : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 A) :
    (cleanup.res.toState s).getMem (BitVec.ofNat 64 (A+32))=0 := by
  simp [Result.toState_getMem,cleanup.res,memEval_cons,Addr.eval,E.eval,ha,ofNat_add_ofNat]

theorem cleanup_frame (s : MachineState) (A : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 A)
    (a : Word) (hne : a≠BitVec.ofNat 64 (A+32)) : (cleanup.res.toState s).getMem a=s.getMem a := by
  rw [Result.toState_getMem]
  apply memEval_frame
  intro p hp
  simp only [cleanup.res,List.mem_cons,List.not_mem_nil,or_false] at hp
  subst p
  simpa [Addr.eval,E.eval,ha,ofNat_add_ofNat] using hne

theorem run {im : Image} {sk : BitVec 256} {A D n m : Nat} {pre right : List UInt8}
    {s u : MachineState} {a : HashOutput} (F : Input A D pre right s)
    (hc : CodeAt im (pcOf 26201) cleanupCode) (hd : CodeAt im (pcOf 26204) doneCode)
    (hu : Stage s A D (pcOf 26201) m u) (hh : Answer A D n a u) :
    TBSim im sk u 5 (pure (n,a)) (Out s A D) := by
  have gx : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  have ha:=F.ahi;have hlo:=F.alo;have hdo:=F.dlo;have hdi:=F.dhi;have hsep:=F.disjoint
  let v:=cleanup.res.toState u
  have hv:=symRun_sound cleanup hc u hu.at_pc (cleanup_obligs u A gx ha hlo F.aa)
  have hdone : done.res.obligs v := by simp [done.res,Result.obligs,Oblig.all]
  let t:=done.res.toState v
  have ht:=symRun_sound done hd v (by rfl) hdone
  have hm : ∀ X,X<2^64 → X≠A+32 → v.getMem (BitVec.ofNat 64 X)=u.getMem (BitVec.ofNat 64 X) := by
    intro X hX hne
    apply cleanup_frame u A gx
    exact fun h=>hne ((ofNat_inj hX (by omega)).mp h)
  have tm : ∀ x,t.getMem x=v.getMem x := fun _=>rfl
  refine tb_pure_steps (hv.trans ht) ⟨rfl,?_,?_,?_,?_,?_⟩
  · intro reg _
    by_cases hr : reg∈[Reg.x6,Reg.x7]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · change v.getMem 1152=s.getReg .x6
        change v.getMem 1152#64=_
        rw [hm _ (by decide) (by omega)];exact hu.saved6
      · change v.getMem 1160=s.getReg .x7
        change v.getMem 1160#64=_
        rw [hm _ (by decide) (by omega)];exact hu.saved7
    · have hdreg : RegsExcept v t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
      have hvreg : RegsExcept u v [] := by intro r _;cases r <;> rfl
      rw [hdreg.get hr,hvreg.get (by simp),hu.regs.get hr]
  · intro k hk;rw [tm,hm _ (by omega) (by omega)];exact hh.output k hk
  · rw [tm];exact cleanup_value u A gx
  · rw [tm,hm _ (by omega) (by omega)];exact hu.pad40
  · intro X hX hne
    rw [tm,hm _ hX (by intro he;exact hne (Or.inl he))]
    exact hu.frame X hX hne

#print axioms run
end OuterSignExit
