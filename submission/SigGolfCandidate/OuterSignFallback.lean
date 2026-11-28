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

/-- C47: the classifier falls back to the plain hash unless the call is the node-buffer call and either (high word
`0`, zero low 11 bits), or (high word nonzero, low word `929 * 2^50`), or (high word `0xf1b02` or `K = 0xe7404003`,
zero low 11 bits, pair field `≥ 28`). -/
def Bad (A : Nat) (s : MachineState) : Prop :=
  A≠328448 ∨
    (s.getMem (BitVec.ofNat 64 (A+24))=0#64 ∧ s.getMem (BitVec.ofNat 64 (A+16)) <<< 53≠0#64) ∨
    (s.getMem (BitVec.ofNat 64 (A+24))≠0#64 ∧ s.getMem (BitVec.ofNat 64 (A+16))≠1045961013456797696#64 ∧
      ((s.getMem (BitVec.ofNat 64 (A+24))≠989954#64 ∧ s.getMem (BitVec.ofNat 64 (A+24))≠3879747587#64) ∨
        s.getMem (BitVec.ofNat 64 (A+16)) <<< 53≠0#64 ∨
        ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 59).toNat<28))

theorem read_header {A D : Nat} {input : List UInt8} {s u : MachineState} {pc : Word}
    (F : OuterSignPlain.Input A D input s) (hu : Ready s A D pc u) (off : Nat) (hoff : off=16 ∨ off=24) :
    u.getMem (u.getReg .x10+BitVec.ofNat 64 off)=s.getMem (BitVec.ofNat 64 (A+off)) := by
  have ha:=F.ahi;have hlo:=F.alo
  rw [hu.regs.get (by decide),F.x10,ofNat_add_ofNat]
  exact hu.savedFrame.get (by rcases hoff with rfl|rfl <;> omega) (by rcases hoff with rfl|rfl <;> omega)

/-- C46: a classifier reject jumps to the plain hash. -/
theorem reject {im : Image} {sk : BitVec 256} {A D : Nat} {input : List UInt8} {s u : MachineState}
    (F : OuterSignPlain.Input A D input s) (cplain : CodeAt im (pcOf 26203) [0x73])
    (cd : CodeAt im (pcOf 26204) doneCode) (cls : ClsAt im) (hu : Ready s A D (pcOf 26781) u) :
    TBSim im sk u 12 (publicHash input) (OuterSignPlain.Out s D) := by
  obtain ⟨t,ht,htr⟩:=clsRJ_step cls.rj hu
  exact TBSim.steps ht (OuterSignPlain.run F cplain cd htr)

/-- C47: past the label tests, a bad low word or pair field rejects. -/
theorem tail_reject {im : Image} {sk : BitVec 256} {A D : Nat} {input : List UInt8} {s u : MachineState}
    (F : OuterSignPlain.Input A D input s) (cplain : CodeAt im (pcOf 26203) [0x73])
    (cd : CodeAt im (pcOf 26204) doneCode) (cls : ClsAt im) (hu : Ready s A D (pcOf 26771) u)
    (hbad : s.getMem (BitVec.ofNat 64 (A+16)) <<< 53≠0#64 ∨
      ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 59).toNat<28) :
    TBSim im sk u 20 (publicHash input) (OuterSignPlain.Out s D) := by
  have ua : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  obtain ⟨y,hy,hyr⟩:=clsC_step cls.c hu ua F.ahi F.alo F.aa
  rw [read_header F hu 16 (Or.inl rfl)] at hyr
  by_cases hlo : s.getMem (BitVec.ofNat 64 (A+16)) <<< 53=0#64
  · rw [if_pos hlo] at hyr
    have ya : y.getReg .x10=BitVec.ofNat 64 A := by rw [hyr.regs.get (by decide)];exact F.x10
    obtain ⟨z,hz,hzr⟩:=clsD_step cls.d hyr ya F.ahi F.alo F.aa
    rw [read_header F hyr 16 (Or.inl rfl)] at hzr
    have hfld : ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 59).toNat<28 := by
      rcases hbad with hb|hb
      · exact (hb hlo).elim
      · exact hb
    rw [if_pos hfld] at hzr
    exact TBSim.steps (hy.trans hz) (reject F cplain cd cls hzr)
  · rw [if_neg hlo] at hyr
    exact (TBSim.steps hy (reject F cplain cd cls hyr)).mono (by omega) (by intros;assumption)

/-- C47: at most `2 + 3 + 1 + 2 + 4 + 4 + 5 + 20` steps to the plain hash. -/
theorem run {im : Image} {sk : BitVec 256} {A D : Nat} {input : List UInt8} {s : MachineState}
    (F : OuterSignPlain.Input A D input s) (hbad : Bad A s)
    (hc : CodeAt im (pcOf 26156) OuterSignImageLayout.code) (cls : ClsAt im) (hp : s.pc=pcOf 26156) :
    TBSim im sk s 41 (publicHash input) (OuterSignPlain.Out s D) := by
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
    obtain ⟨x,hx,hxr⟩:=clsA_step cls.a hwr wa F.ahi F.alo F.aa
    rw [read_header F hwr 24 (Or.inr rfl)] at hxr
    have xa : x.getReg .x10=BitVec.ofNat 64 A := by rw [hxr.regs.get (by decide)];exact F.x10
    by_cases h0 : s.getMem (BitVec.ofNat 64 (A+24))=0#64
    · rw [if_pos h0] at hxr
      have hl : s.getMem (BitVec.ofNat 64 (A+16)) <<< 53≠0#64 := by
        rcases hbad with hb|hb|hb
        · exact (hb hA).elim
        · exact hb.2
        · exact (hb.1 h0).elim
      obtain ⟨y,hy,hyr⟩:=clsZ_step cls.z hxr xa F.ahi F.alo F.aa
      rw [read_header F hxr 16 (Or.inl rfl),if_neg hl] at hyr
      obtain ⟨z,hz,hzr⟩:=clsZR_step cls.zr hyr
      exact (TBSim.steps (hs.trans (hv.trans (hw.trans (hx.trans (hy.trans hz)))))
        (OuterSignPlain.run F cplain cd hzr)).mono (by omega) (by intros;assumption)
    · rw [if_neg h0] at hxr
      obtain ⟨hT,hrest⟩ : s.getMem (BitVec.ofNat 64 (A+16))≠1045961013456797696#64 ∧
          ((s.getMem (BitVec.ofNat 64 (A+24))≠989954#64 ∧ s.getMem (BitVec.ofNat 64 (A+24))≠3879747587#64) ∨
            s.getMem (BitVec.ofNat 64 (A+16)) <<< 53≠0#64 ∨
            ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 59).toNat<28) := by
        rcases hbad with hb|hb|hb
        · exact (hb hA).elim
        · exact (h0 hb.1).elim
        · exact hb.2
      obtain ⟨y,hy,hyr⟩:=clsT_step cls.t hxr xa F.ahi F.alo F.aa
      rw [read_header F hxr 16 (Or.inl rfl),if_neg hT] at hyr
      have ya : y.getReg .x10=BitVec.ofNat 64 A := by rw [hyr.regs.get (by decide)];exact F.x10
      obtain ⟨z,hz,hzr,hz6⟩:=clsH_step cls.h hyr ya F.ahi F.alo F.aa
      rw [read_header F hyr 24 (Or.inr rfl)] at hzr hz6
      by_cases h2 : s.getMem (BitVec.ofNat 64 (A+24))=989954#64
      · rw [if_pos h2] at hzr
        have hb : s.getMem (BitVec.ofNat 64 (A+16)) <<< 53≠0#64 ∨
            ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 59).toNat<28 := by
          rcases hrest with hb|hb
          · exact (hb.1 h2).elim
          · exact hb
        exact (TBSim.steps (hs.trans (hv.trans (hw.trans (hx.trans (hy.trans hz))))) (tail_reject F cplain cd cls hzr hb)).mono
          (by omega) (by intros;assumption)
      · rw [if_neg h2] at hzr
        obtain ⟨k,hk,hkr⟩:=clsK_step cls.k hzr hz6
        by_cases hK : s.getMem (BitVec.ofNat 64 (A+24))=3879747587#64
        · rw [if_pos hK] at hkr
          have hb : s.getMem (BitVec.ofNat 64 (A+16)) <<< 53≠0#64 ∨
              ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 59).toNat<28 := by
            rcases hrest with hb|hb
            · exact (hb.2 hK).elim
            · exact hb
          exact TBSim.steps (hs.trans (hv.trans (hw.trans (hx.trans (hy.trans (hz.trans hk))))))
            (tail_reject F cplain cd cls hkr hb)
        · rw [if_neg hK] at hkr
          exact (TBSim.steps (hs.trans (hv.trans (hw.trans (hx.trans (hy.trans (hz.trans hk))))))
            (reject F cplain cd cls hkr)).mono (by omega) (by intros;assumption)
  · simp only [if_neg hA] at hvr
    exact (TBSim.steps (hs.trans hv) (OuterSignPlain.run F cplain cd hvr)).mono (by omega) (by intros;assumption)

#print axioms run

#print axioms addr_step
#print axioms tail_reject
end OuterSignFallback
