import SigGolfCandidate.OuterSignBlocks
import SigGolfCandidate.OuterNodeSearchInvariant
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSignEntry
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open OuterNodeSearchInvariant OuterSignBlocks

structure Ready (s : MachineState) (A D : Nat) (pc : Word) (t : MachineState) : Prop where
  at_pc : t.pc=pc
  regs : RegsExcept s t [.x6,.x7]
  saved6 : t.getMem 1152=s.getReg .x6
  saved7 : t.getMem 1160=s.getReg .x7
  frame : Frame s t (Work A D)
  savedFrame : Frame s t (fun X=>X=1152 ∨ X=1160)

theorem Ready.readOnly {s u t : MachineState} {A D : Nat} {pc pc' : Word}
    (hu : Ready s A D pc u) (hp : t.pc=pc') (hr : RegsExcept u t [.x6,.x7])
    (hm : ∀ a,t.getMem a=u.getMem a) : Ready s A D pc' t := by
  refine ⟨hp,(fun r hr'=>by rw [hr.get hr',hu.regs.get hr']),?_,?_,?_,?_⟩
  · rw [hm];exact hu.saved6
  · rw [hm];exact hu.saved7
  · intro X hX hn;rw [hm];exact hu.frame X hX hn
  · intro X hX hn;rw [hm];exact hu.savedFrame X hX hn

theorem save_obligs (s : MachineState) : save.res.obligs s := by
  simp [save.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]

theorem save_run {im : Image} {A D : Nat} (hc : CodeAt im (pcOf 26156) saveCode)
    (s : MachineState) (hp : s.pc=pcOf 26156) :
    ∃ t,Steps im s 2 2 t ∧ Ready s A D (pcOf 26158) t := by
  refine ⟨save.res.toState s,symRun_sound save hc s hp (save_obligs s),rfl,?_,?_,?_,?_,?_⟩
  · intro reg hr;cases reg <;> simp at hr <;> rfl
  · simp [Result.toState_getMem,save.res,memEval_cons,memEval_nil,Addr.eval,E.eval]
  · simp [Result.toState_getMem,save.res,memEval_cons,memEval_nil,Addr.eval,E.eval]
  · intro X hX hn
    rw [Result.toState_getMem]
    apply memEval_frame
    intro p hp
    simp only [save.res,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · simp only [Addr.eval,E.eval]
      intro he;exact hn (Or.inr (Or.inr (Or.inr (Or.inr ((ofNat_inj hX (by decide)).mp he)))))
    · simp only [Addr.eval,E.eval]
      intro he;exact hn (Or.inr (Or.inr (Or.inr (Or.inl ((ofNat_inj hX (by decide)).mp he)))))
  · intro X hX hn
    rw [Result.toState_getMem]
    apply memEval_frame
    intro p hp
    simp only [save.res,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · simp only [Addr.eval]
      intro he;exact hn (Or.inr ((ofNat_inj hX (by decide)).mp he))
    · simp only [Addr.eval]
      intro he;exact hn (Or.inl ((ofNat_inj hX (by decide)).mp he))

theorem start_at (pc : Word) : symRun {noAlias:=true} b_startCode pc 40=
    some {b_start.res with pc:=.c (pc+8#64)} := by
  change some {b_start.res with pc:=.c (pc+4#64+4#64)}=_
  simp only [BitVec.add_assoc]
  rfl

theorem start_obligs (s : MachineState) (A : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 A)
    (hi : A<2^20) (hlo : 2048≤A) (hm : A%8=0) : b_start.res.obligs s := by
  simp [b_start.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
    memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
  omega

theorem start_run {im : Image} {A D : Nat} {pre right : List UInt8} {s u : MachineState}
    {pc : Word} (F : Input A D pre right s) (hc : CodeAt im pc b_startCode)
    (hu : Ready s A D pc u) : ∃ t,Steps im u 2 2 t ∧ Stage s A D (pc+8#64) 0 t := by
  let r : Result:={b_start.res with pc:=.c (pc+8#64)}
  have gx : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  have ha:=F.ahi;have hlo:=F.alo
  have hm : ∀ X,X<2^64 → X≠A+40 → (r.toState u).getMem (BitVec.ofNat 64 X)=u.getMem (BitVec.ofNat 64 X) := by
    intro X hX hn
    change (b_start.res.toState u).getMem (BitVec.ofNat 64 X)=_
    rw [Result.toState_getMem]
    apply memEval_frame
    intro p hp
    simp only [b_start.res,List.mem_cons,List.not_mem_nil,or_false] at hp
    subst p
    simp only [Addr.eval,E.eval,gx,ofNat_add_ofNat]
    intro he;exact hn ((ofNat_inj hX (by omega)).mp he)
  refine ⟨r.toState u,symRun_sound (start_at pc) hc u hu.at_pc (start_obligs u A gx ha hlo F.aa),rfl,?_,?_,?_,?_,?_,?_⟩
  · have hr : RegsExcept u (r.toState u) [.x6] := by
      intro reg hreg;cases reg <;> simp at hreg <;> rfl
    intro reg hreg
    rw [(hr.mono (by simp)).get hreg,hu.regs.get hreg]
  · rfl
  · change (r.toState u).getMem 1152#64=_
    rw [hm _ (by decide) (by omega)];exact hu.saved6
  · change (r.toState u).getMem 1160#64=_
    rw [hm _ (by decide) (by omega)];exact hu.saved7
  · change (b_start.res.toState u).getMem (BitVec.ofNat 64 (A+40))=0
    simp [Result.toState_getMem,b_start.res,memEval_cons,Addr.eval,E.eval,gx,ofNat_add_ofNat]
  · intro X hX hn
    rw [hm _ hX (by intro he;exact hn (Or.inr (Or.inl he)))]
    exact hu.frame X hX hn

#print axioms save_run
#print axioms start_run
end OuterSignEntry
