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

/-! C47: the outer-root classifier (sign words 26752..26781), entered through the hook word 26161. Each block only
reads the input buffer and writes `t1`/`t2`. -/

theorem hook_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26161) hookCode) (hu : Ready s A D (pcOf 26161) u) :
    ∃ t,Steps im u 1 1 t ∧ Ready s A D (pcOf 26752) t := by
  let t:=hook.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26752 := by simp [t,Result.toState_pc,hook.res,E.eval]
  refine ⟨t,symRun_sound hook hc u hu.at_pc (by simp [hook.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

/-- C47: `ld t1,24(a0); bne t1,zero`: a zero high word goes to 26754, a nonzero one to 26758. -/
theorem clsA_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26752) clsACode) (hu : Ready s A D (pcOf 26752) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 2 2 t ∧
      Ready s A D (if u.getMem (u.getReg .x10+24#64)=0#64 then pcOf 26754 else pcOf 26758) t := by
  let t:=clsA.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : clsA.res.obligs u := by
    simp [clsA.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if u.getMem (u.getReg .x10+24#64)=0#64 then pcOf 26754 else pcOf 26758) := by
    by_cases h0 : u.getMem (u.getReg .x10+24#64)=0#64 <;>
      simp [t,Result.toState_pc,clsA.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,h0]
  refine ⟨t,symRun_sound clsA hc u hu.at_pc ho,hu.readOnly hp hr ?_⟩
  intro a;rfl

/-- C47: high word zero: `ld t2,16(a0); slli 53; beq t2,zero`: zero low 11 bits take the `c` search (26780). -/
theorem clsZ_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26754) clsZCode) (hu : Ready s A D (pcOf 26754) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 3 3 t ∧ Ready s A D
      (if u.getMem (u.getReg .x10+16#64) <<< 53=0#64 then pcOf 26780 else pcOf 26757) t := by
  let t:=clsZ.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : clsZ.res.obligs u := by
    simp [clsZ.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if u.getMem (u.getReg .x10+16#64) <<< 53=0#64 then pcOf 26780 else pcOf 26757) := by
    by_cases h0 : u.getMem (u.getReg .x10+16#64) <<< 53=0#64 <;>
      simp [t,Result.toState_pc,clsZ.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,h0]
  refine ⟨t,symRun_sound clsZ hc u hu.at_pc ho,hu.readOnly hp hr ?_⟩
  intro a;rfl

/-- C47: high word nonzero: `ld t2,16(a0); t1 := 929 << 50; beq t2,t1`: the c8 heap-3 label takes the `c` search. -/
theorem clsT_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26758) clsTCode) (hu : Ready s A D (pcOf 26758) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 4 4 t ∧ Ready s A D
      (if u.getMem (u.getReg .x10+16#64)=1045961013456797696#64 then pcOf 26780 else pcOf 26762) t := by
  let t:=clsT.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : clsT.res.obligs u := by
    simp [clsT.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if u.getMem (u.getReg .x10+16#64)=1045961013456797696#64 then pcOf 26780 else pcOf 26762) := by
    by_cases h0 : u.getMem (u.getReg .x10+16#64)=1045961013456797696#64 <;>
      simp [t,Result.toState_pc,clsT.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,h0]
  refine ⟨t,symRun_sound clsT hc u hu.at_pc ho,hu.readOnly hp hr ?_⟩
  intro a;rfl

/-- C47: `ld t1,24(a0); t2 := 0xf1b02; beq t1,t2` (odd heap 2 to the field tests 26771, else the `K` test). -/
theorem clsH_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26762) clsHCode) (hu : Ready s A D (pcOf 26762) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 4 4 t ∧
      Ready s A D (if u.getMem (u.getReg .x10+24#64)=989954#64 then pcOf 26771 else pcOf 26766) t ∧
      t.getReg .x6=u.getMem (u.getReg .x10+24#64) := by
  let t:=clsH.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : clsH.res.obligs u := by
    simp [clsH.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if u.getMem (u.getReg .x10+24#64)=989954#64 then pcOf 26771 else pcOf 26766) := by
    by_cases h0 : u.getMem (u.getReg .x10+24#64)=989954#64 <;>
      simp [t,Result.toState_pc,clsH.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,h0]
  have h6 : t.getReg .x6=u.getMem (u.getReg .x10+24#64) := by
    simp [t,Result.toState_getReg,clsH.res,RegFile.get,E.eval,Addr.eval,BinOp.eval]
  refine ⟨t,symRun_sound clsH hc u hu.at_pc ho,hu.readOnly hp hr ?_,h6⟩
  intro a;rfl

/-- C47: `t2 := K = 0xe7404003; bne t1,t2` (odd heap 3 to the field tests 26771, else reject). -/
theorem clsK_step {im : Image} {A D : Nat} {s u : MachineState} {w : BitVec 64}
    (hc : CodeAt im (pcOf 26766) clsKCode) (hu : Ready s A D (pcOf 26766) u) (h6 : u.getReg .x6=w) :
    ∃ t,Steps im u 5 5 t ∧ Ready s A D (if w=3879747587#64 then pcOf 26771 else pcOf 26781) t := by
  let t:=clsK.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=(if w=3879747587#64 then pcOf 26771 else pcOf 26781) := by
    by_cases h0 : w=3879747587#64 <;>
      simp [t,Result.toState_pc,clsK.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,RegFile.get,h6,h0]
  refine ⟨t,symRun_sound clsK hc u hu.at_pc (by simp [clsK.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem clsC_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26771) clsCCode) (hu : Ready s A D (pcOf 26771) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 3 3 t ∧ Ready s A D
      (if u.getMem (u.getReg .x10+16#64) <<< 53=0#64 then pcOf 26774 else pcOf 26781) t := by
  let t:=clsC.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : clsC.res.obligs u := by
    simp [clsC.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if u.getMem (u.getReg .x10+16#64) <<< 53=0#64 then pcOf 26774 else pcOf 26781) := by
    by_cases h0 : u.getMem (u.getReg .x10+16#64) <<< 53=0#64 <;>
      simp [t,Result.toState_pc,clsC.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,h0]
  refine ⟨t,symRun_sound clsC hc u hu.at_pc ho,hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem clsD_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26774) clsDCode) (hu : Ready s A D (pcOf 26774) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 5 5 t ∧ Ready s A D
      (if ((u.getMem (u.getReg .x10+16#64) <<< 48) >>> 59).toNat<28 then pcOf 26781 else pcOf 26779) t := by
  let t:=clsD.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : clsD.res.obligs u := by
    simp [clsD.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if ((u.getMem (u.getReg .x10+16#64) <<< 48) >>> 59).toNat<28 then pcOf 26781 else pcOf 26779) := by
    simp [t,Result.toState_pc,clsD.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,BitVec.ult]
  refine ⟨t,symRun_sound clsD hc u hu.at_pc ho,hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem clsZR_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26757) clsZRCode) (hu : Ready s A D (pcOf 26757) u) :
    ∃ t,Steps im u 1 1 t ∧ Ready s A D (pcOf 26203) t := by
  let t:=clsZR.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26203 := by simp [t,Result.toState_pc,clsZR.res,E.eval]
  refine ⟨t,symRun_sound clsZR hc u hu.at_pc (by simp [clsZR.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem clsBJ_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26779) clsBJCode) (hu : Ready s A D (pcOf 26779) u) :
    ∃ t,Steps im u 1 1 t ∧ Ready s A D (pcOf 26175) t := by
  let t:=clsBJ.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26175 := by simp [t,Result.toState_pc,clsBJ.res,E.eval]
  refine ⟨t,symRun_sound clsBJ hc u hu.at_pc (by simp [clsBJ.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem clsRJ_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26781) clsRJCode) (hu : Ready s A D (pcOf 26781) u) :
    ∃ t,Steps im u 1 1 t ∧ Ready s A D (pcOf 26203) t := by
  let t:=clsRJ.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26203 := by simp [t,Result.toState_pc,clsRJ.res,E.eval]
  refine ⟨t,symRun_sound clsRJ hc u hu.at_pc (by simp [clsRJ.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem clsCJ_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26780) clsCJCode) (hu : Ready s A D (pcOf 26780) u) :
    ∃ t,Steps im u 1 1 t ∧ Ready s A D (pcOf 26186) t := by
  let t:=clsCJ.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26186 := by simp [t,Result.toState_pc,clsCJ.res,E.eval]
  refine ⟨t,symRun_sound clsCJ hc u hu.at_pc (by simp [clsCJ.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

/-- C47: the classifier's slices. -/
structure ClsAt (im : Image) : Prop where
  a : CodeAt im (pcOf 26752) clsACode
  z : CodeAt im (pcOf 26754) clsZCode
  zr : CodeAt im (pcOf 26757) clsZRCode
  t : CodeAt im (pcOf 26758) clsTCode
  h : CodeAt im (pcOf 26762) clsHCode
  k : CodeAt im (pcOf 26766) clsKCode
  c : CodeAt im (pcOf 26771) clsCCode
  d : CodeAt im (pcOf 26774) clsDCode
  bj : CodeAt im (pcOf 26779) clsBJCode
  cj : CodeAt im (pcOf 26780) clsCJCode
  rj : CodeAt im (pcOf 26781) clsRJCode

theorem cls_slices {im : Image} (hc : CodeAt im (pcOf 26752) clsCode) : ClsAt im :=
  ⟨SigGolfCandidate.FtsGrind.codeAt_sub 0 hc (by decide) (by rfl),SigGolfCandidate.FtsGrind.codeAt_sub 2 hc (by decide) (by rfl),
    SigGolfCandidate.FtsGrind.codeAt_sub 5 hc (by decide) (by rfl),SigGolfCandidate.FtsGrind.codeAt_sub 6 hc (by decide) (by rfl),
    SigGolfCandidate.FtsGrind.codeAt_sub 10 hc (by decide) (by rfl),SigGolfCandidate.FtsGrind.codeAt_sub 14 hc (by decide) (by rfl),
    SigGolfCandidate.FtsGrind.codeAt_sub 19 hc (by decide) (by rfl),SigGolfCandidate.FtsGrind.codeAt_sub 22 hc (by decide) (by rfl),
    SigGolfCandidate.FtsGrind.codeAt_sub 27 hc (by decide) (by rfl),SigGolfCandidate.FtsGrind.codeAt_sub 28 hc (by decide) (by rfl),
    SigGolfCandidate.FtsGrind.codeAt_sub 29 hc (by decide) (by rfl)⟩

#print axioms save_run
#print axioms start_run
#print axioms clsA_step
end OuterSignEntry
