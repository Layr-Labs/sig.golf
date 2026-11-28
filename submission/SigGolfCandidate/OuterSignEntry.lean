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

/-! C46: the outer-root classifier (sign words 26654..26671), entered through the hook word 26161. Each block only
reads the input buffer and writes `t1`/`t2`. -/

theorem hook_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26161) hookCode) (hu : Ready s A D (pcOf 26161) u) :
    ∃ t,Steps im u 1 1 t ∧ Ready s A D (pcOf 26654) t := by
  let t:=hook.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26654 := by simp [t,Result.toState_pc,hook.res,E.eval]
  refine ⟨t,symRun_sound hook hc u hu.at_pc (by simp [hook.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

/-- C46: `w - 3 = 0` exactly for the heap-3 label. -/
theorem label3 (w : BitVec 64) : w+18446744073709551613#64=0#64 ↔ w=3#64 := by
  constructor
  · intro h
    calc w=w+18446744073709551613#64+3#64 := by
          rw [BitVec.add_assoc,show (18446744073709551613#64+3#64 : BitVec 64)=0#64 by decide,BitVec.add_zero]
      _=3#64 := by rw [h,BitVec.zero_add]
  · intro h;subst h;decide

/-- C46: `w - 3 = 0xf1aff` exactly for the heap-2 label `0xf1b02`. -/
theorem label2 (w : BitVec 64) : w+18446744073709551613#64=989951#64 ↔ w=989954#64 := by
  constructor
  · intro h
    calc w=w+18446744073709551613#64+3#64 := by
          rw [BitVec.add_assoc,show (18446744073709551613#64+3#64 : BitVec 64)=0#64 by decide,BitVec.add_zero]
      _=989954#64 := by rw [h];decide
  · intro h;subst h;decide

theorem clsA_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26654) clsACode) (hu : Ready s A D (pcOf 26654) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 3 3 t ∧
      Ready s A D (if u.getMem (u.getReg .x10+24#64)=3#64 then pcOf 26660 else pcOf 26657) t ∧
      t.getReg .x6=u.getMem (u.getReg .x10+24#64)+18446744073709551613#64 := by
  let t:=clsA.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : clsA.res.obligs u := by
    simp [clsA.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if u.getMem (u.getReg .x10+24#64)=3#64 then pcOf 26660 else pcOf 26657) := by
    simp only [t,Result.toState_pc,clsA.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,RegFile.get]
    by_cases h3 : u.getMem (u.getReg .x10+24#64)=3#64
    · have h0 := (label3 _).mpr h3
      simp [h3,h0]
    · have h0 : ¬ u.getMem (u.getReg .x10+24#64)+18446744073709551613#64=0#64 := fun h=>h3 ((label3 _).mp h)
      simp [h3,h0]
  have h6 : t.getReg .x6=u.getMem (u.getReg .x10+24#64)+18446744073709551613#64 := by
    simp [t,Result.toState_getReg,clsA.res,RegFile.get,E.eval,Addr.eval,BinOp.eval]
  refine ⟨t,symRun_sound clsA hc u hu.at_pc ho,hu.readOnly hp hr ?_,h6⟩
  intro a;rfl

theorem clsB_step {im : Image} {A D : Nat} {s u : MachineState} {w : BitVec 64}
    (hc : CodeAt im (pcOf 26657) clsBCode) (hu : Ready s A D (pcOf 26657) u)
    (h6 : u.getReg .x6=w+18446744073709551613#64) :
    ∃ t,Steps im u 3 3 t ∧ Ready s A D (if w=989954#64 then pcOf 26660 else pcOf 26670) t := by
  let t:=clsB.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=(if w=989954#64 then pcOf 26660 else pcOf 26670) := by
    simp only [t,Result.toState_pc,clsB.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,RegFile.get,h6]
    by_cases h2 : w=989954#64
    · have h0 := (label2 _).mpr h2
      simp [h2,h0]
    · have h0 : ¬ w+18446744073709551613#64=989951#64 := fun h=>h2 ((label2 _).mp h)
      simp [h2,h0]
  refine ⟨t,symRun_sound clsB hc u hu.at_pc (by simp [clsB.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem clsC_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26660) clsCCode) (hu : Ready s A D (pcOf 26660) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 3 3 t ∧ Ready s A D
      (if u.getMem (u.getReg .x10+16#64) <<< 53=0#64 then pcOf 26663 else pcOf 26670) t := by
  let t:=clsC.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : clsC.res.obligs u := by
    simp [clsC.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if u.getMem (u.getReg .x10+16#64) <<< 53=0#64 then pcOf 26663 else pcOf 26670) := by
    simp [t,Result.toState_pc,clsC.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval]
  refine ⟨t,symRun_sound clsC hc u hu.at_pc ho,hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem clsD_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26663) clsDCode) (hu : Ready s A D (pcOf 26663) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 5 5 t ∧ Ready s A D
      (if ((u.getMem (u.getReg .x10+16#64) <<< 48) >>> 59).toNat<27 then pcOf 26670 else pcOf 26668) t ∧
      t.getReg .x7=(u.getMem (u.getReg .x10+16#64) <<< 48) >>> 59 ∧ t.getReg .x6=27#64 := by
  let t:=clsD.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : clsD.res.obligs u := by
    simp [clsD.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if ((u.getMem (u.getReg .x10+16#64) <<< 48) >>> 59).toNat<27 then pcOf 26670 else pcOf 26668) := by
    simp [t,Result.toState_pc,clsD.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,BitVec.ult]
  have h7 : t.getReg .x7=(u.getMem (u.getReg .x10+16#64) <<< 48) >>> 59 := by
    simp [t,Result.toState_getReg,clsD.res,RegFile.get,E.eval,Addr.eval,BinOp.eval]
  have h6 : t.getReg .x6=27#64 := by
    simp [t,Result.toState_getReg,clsD.res,RegFile.get,E.eval]
  refine ⟨t,symRun_sound clsD hc u hu.at_pc ho,hu.readOnly hp hr ?_,h7,h6⟩
  intro a;rfl

theorem clsE_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26668) clsECode) (hu : Ready s A D (pcOf 26668) u) :
    ∃ t,Steps im u 1 1 t ∧ Ready s A D (if u.getReg .x7=u.getReg .x6 then pcOf 26671 else pcOf 26669) t := by
  let t:=clsE.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=(if u.getReg .x7=u.getReg .x6 then pcOf 26671 else pcOf 26669) := by
    simp [t,Result.toState_pc,clsE.res,E.eval,RegFile.get,CmpOp.eval]
  refine ⟨t,symRun_sound clsE hc u hu.at_pc (by simp [clsE.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem clsBJ_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26669) clsBJCode) (hu : Ready s A D (pcOf 26669) u) :
    ∃ t,Steps im u 1 1 t ∧ Ready s A D (pcOf 26175) t := by
  let t:=clsBJ.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26175 := by simp [t,Result.toState_pc,clsBJ.res,E.eval]
  refine ⟨t,symRun_sound clsBJ hc u hu.at_pc (by simp [clsBJ.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem clsRJ_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26670) clsRJCode) (hu : Ready s A D (pcOf 26670) u) :
    ∃ t,Steps im u 1 1 t ∧ Ready s A D (pcOf 26203) t := by
  let t:=clsRJ.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26203 := by simp [t,Result.toState_pc,clsRJ.res,E.eval]
  refine ⟨t,symRun_sound clsRJ hc u hu.at_pc (by simp [clsRJ.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem clsCJ_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26671) clsCJCode) (hu : Ready s A D (pcOf 26671) u) :
    ∃ t,Steps im u 1 1 t ∧ Ready s A D (pcOf 26186) t := by
  let t:=clsCJ.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26186 := by simp [t,Result.toState_pc,clsCJ.res,E.eval]
  refine ⟨t,symRun_sound clsCJ hc u hu.at_pc (by simp [clsCJ.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

/-- C46: the classifier's slices. -/
structure ClsAt (im : Image) : Prop where
  a : CodeAt im (pcOf 26654) clsACode
  b : CodeAt im (pcOf 26657) clsBCode
  c : CodeAt im (pcOf 26660) clsCCode
  d : CodeAt im (pcOf 26663) clsDCode
  e : CodeAt im (pcOf 26668) clsECode
  bj : CodeAt im (pcOf 26669) clsBJCode
  rj : CodeAt im (pcOf 26670) clsRJCode
  cj : CodeAt im (pcOf 26671) clsCJCode

theorem cls_slices {im : Image} (hc : CodeAt im (pcOf 26654) clsCode) : ClsAt im :=
  ⟨SigGolfCandidate.FtsGrind.codeAt_sub 0 hc (by decide) (by rfl),SigGolfCandidate.FtsGrind.codeAt_sub 3 hc (by decide) (by rfl),SigGolfCandidate.FtsGrind.codeAt_sub 6 hc (by decide) (by rfl),
    SigGolfCandidate.FtsGrind.codeAt_sub 9 hc (by decide) (by rfl),SigGolfCandidate.FtsGrind.codeAt_sub 14 hc (by decide) (by rfl),SigGolfCandidate.FtsGrind.codeAt_sub 15 hc (by decide) (by rfl),
    SigGolfCandidate.FtsGrind.codeAt_sub 16 hc (by decide) (by rfl),SigGolfCandidate.FtsGrind.codeAt_sub 17 hc (by decide) (by rfl)⟩

#print axioms save_run
#print axioms start_run
#print axioms clsA_step
end OuterSignEntry
