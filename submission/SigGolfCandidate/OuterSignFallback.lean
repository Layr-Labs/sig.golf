import SigGolfCandidate.OuterSignPlain
import SigGolfCandidate.OuterSignImageLayout
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSignFallback
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterSignBlocks OuterSignEntry

theorem addr_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26158) addrCode) (hu : Ready s A D (pcOf 26158) u) :
    ∃ t,Steps im u 3 3 t ∧ Ready s A D (if u.getReg .x10=328448#64 then pcOf 26161 else pcOf 26203) t := by
  let t:=addr.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=(if u.getReg .x10=328448#64 then pcOf 26161 else pcOf 26203) := by
    simp [t,Result.toState_pc,addr.res,E.eval,CmpOp.eval]
  refine ⟨t,symRun_sound addr hc u hu.at_pc (by simp [addr.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

/-- C46: the classifier falls back to the plain hash unless the call is the node-buffer call, the heap label is `3`
or `0xf1b02`, the header word has zero low 11 bits and a coordinate field `≥ 27`. -/
def Bad (A : Nat) (s : MachineState) : Prop :=
  A≠328448 ∨ (s.getMem (BitVec.ofNat 64 (A+24))≠3#64 ∧ s.getMem (BitVec.ofNat 64 (A+24))≠989954#64) ∨
    s.getMem (BitVec.ofNat 64 (A+16)) <<< 53≠0#64 ∨
    ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 59).toNat<27

theorem read_header {A D : Nat} {input : List UInt8} {s u : MachineState} {pc : Word}
    (F : OuterSignPlain.Input A D input s) (hu : Ready s A D pc u) (off : Nat) (hoff : off=16 ∨ off=24) :
    u.getMem (u.getReg .x10+BitVec.ofNat 64 off)=s.getMem (BitVec.ofNat 64 (A+off)) := by
  have ha:=F.ahi;have hlo:=F.alo
  rw [hu.regs.get (by decide),F.x10,ofNat_add_ofNat]
  exact hu.savedFrame.get (by rcases hoff with rfl|rfl <;> omega) (by rcases hoff with rfl|rfl <;> omega)

/-- C46: a classifier reject (26670) jumps to the plain hash. -/
theorem reject {im : Image} {sk : BitVec 256} {A D : Nat} {input : List UInt8} {s u : MachineState}
    (F : OuterSignPlain.Input A D input s) (cplain : CodeAt im (pcOf 26203) [0x73])
    (cd : CodeAt im (pcOf 26204) doneCode) (cls : ClsAt im) (hu : Ready s A D (pcOf 26670) u) :
    TBSim im sk u 12 (publicHash input) (OuterSignPlain.Out s D) := by
  obtain ⟨t,ht,htr⟩:=clsRJ_step cls.rj hu
  exact TBSim.steps ht (OuterSignPlain.run F cplain cd htr)

/-- C46: past the label test, a bad low word or coordinate field rejects. -/
theorem tail_reject {im : Image} {sk : BitVec 256} {A D : Nat} {input : List UInt8} {s u : MachineState}
    (F : OuterSignPlain.Input A D input s) (cplain : CodeAt im (pcOf 26203) [0x73])
    (cd : CodeAt im (pcOf 26204) doneCode) (cls : ClsAt im) (hu : Ready s A D (pcOf 26660) u)
    (hbad : s.getMem (BitVec.ofNat 64 (A+16)) <<< 53≠0#64 ∨
      ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 59).toNat<27) :
    TBSim im sk u 20 (publicHash input) (OuterSignPlain.Out s D) := by
  have ua : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  obtain ⟨y,hy,hyr⟩:=clsC_step cls.c hu ua F.ahi F.alo F.aa
  rw [read_header F hu 16 (Or.inl rfl)] at hyr
  by_cases hlo : s.getMem (BitVec.ofNat 64 (A+16)) <<< 53=0#64
  · rw [if_pos hlo] at hyr
    have ya : y.getReg .x10=BitVec.ofNat 64 A := by rw [hyr.regs.get (by decide)];exact F.x10
    obtain ⟨z,hz,hzr,-,-⟩:=clsD_step cls.d hyr ya F.ahi F.alo F.aa
    rw [read_header F hyr 16 (Or.inl rfl)] at hzr
    have hfld : ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 59).toNat<27 := by
      rcases hbad with hb|hb
      · exact (hb hlo).elim
      · exact hb
    rw [if_pos hfld] at hzr
    exact TBSim.steps (hy.trans hz) (reject F cplain cd cls hzr)
  · rw [if_neg hlo] at hyr
    exact (TBSim.steps hy (reject F cplain cd cls hyr)).mono (by omega) (by intros;assumption)

theorem run {im : Image} {sk : BitVec 256} {A D : Nat} {input : List UInt8} {s : MachineState}
    (F : OuterSignPlain.Input A D input s) (hbad : Bad A s)
    (hc : CodeAt im (pcOf 26156) OuterSignImageLayout.code) (cls : ClsAt im) (hp : s.pc=pcOf 26156) :
    TBSim im sk s 32 (publicHash input) (OuterSignPlain.Out s D) := by
  obtain ⟨c0,ca,cl,cf,ce,cc,bs,bq,bc,bf,bj,cs,cq,cck,cfx,cj,cp,cd⟩:=OuterSignImageLayout.slices hc
  have ck : CodeAt im (pcOf 26161) hookCode := codeAt_sub 5 hc (by decide) (by rfl)
  have cplain : CodeAt im (pcOf 26203) [0x73] := codeAt_sub 47 hc (by decide) (by rfl)
  obtain ⟨u,hs,hu⟩:=save_run (A:=A) (D:=D) c0 s hp
  have ga : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  have haddr : u.getReg .x10=328448#64 ↔ A=328448 := by
    rw [ga];exact ofNat_inj (by have:=F.ahi;omega) (by decide)
  obtain ⟨v,hv,hvr⟩:=addr_step ca hu
  simp only [haddr] at hvr
  by_cases hA : A=328448
  · simp only [if_pos hA] at hvr
    obtain ⟨w,hw,hwr⟩:=hook_step ck hvr
    have wa : w.getReg .x10=BitVec.ofNat 64 A := by rw [hwr.regs.get (by decide)];exact F.x10
    obtain ⟨x,hx,hxr,hx6⟩:=clsA_step cls.a hwr wa F.ahi F.alo F.aa
    rw [read_header F hwr 24 (Or.inr rfl)] at hxr hx6
    by_cases h3 : s.getMem (BitVec.ofNat 64 (A+24))=3#64
    · rw [if_pos h3] at hxr
      have hb : s.getMem (BitVec.ofNat 64 (A+16)) <<< 53≠0#64 ∨
          ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 59).toNat<27 := by
        rcases hbad with hb|hb|hb|hb
        · exact (hb hA).elim
        · exact (hb.1 h3).elim
        · exact Or.inl hb
        · exact Or.inr hb
      exact (TBSim.steps (hs.trans (hv.trans (hw.trans hx))) (tail_reject F cplain cd cls hxr hb)).mono (by omega)
        (by intros;assumption)
    · rw [if_neg h3] at hxr
      obtain ⟨y,hy,hyr⟩:=clsB_step cls.b hxr hx6
      by_cases h2 : s.getMem (BitVec.ofNat 64 (A+24))=989954#64
      · rw [if_pos h2] at hyr
        have hb : s.getMem (BitVec.ofNat 64 (A+16)) <<< 53≠0#64 ∨
            ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 59).toNat<27 := by
          rcases hbad with hb|hb|hb|hb
          · exact (hb hA).elim
          · exact (hb.2 h2).elim
          · exact Or.inl hb
          · exact Or.inr hb
        exact TBSim.steps (hs.trans (hv.trans (hw.trans (hx.trans hy)))) (tail_reject F cplain cd cls hyr hb)
      · rw [if_neg h2] at hyr
        exact (TBSim.steps (hs.trans (hv.trans (hw.trans (hx.trans hy)))) (reject F cplain cd cls hyr)).mono
          (by omega) (by intros;assumption)
  · simp only [if_neg hA] at hvr
    exact (TBSim.steps (hs.trans hv) (OuterSignPlain.run F cplain cd hvr)).mono (by omega) (by intros;assumption)

#print axioms run

#print axioms addr_step
#print axioms tail_reject
end OuterSignFallback
