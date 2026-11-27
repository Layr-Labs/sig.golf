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

theorem low_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26161) lowCode) (hu : Ready s A D (pcOf 26161) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 3 3 t ∧ Ready s A D
      (if u.getMem (u.getReg .x10+16#64) <<< 53=0#64 then pcOf 26164 else pcOf 26203) t := by
  let t:=low.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : low.res.obligs u := by
    simp [low.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if u.getMem (u.getReg .x10+16#64) <<< 53=0#64 then pcOf 26164 else pcOf 26203) := by
    simp [t,Result.toState_pc,low.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval]
  refine ⟨t,symRun_sound low hc u hu.at_pc ho,hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem field_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26164) fieldCode) (hu : Ready s A D (pcOf 26164) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 5 5 t ∧ Ready s A D
      (if ((u.getMem (u.getReg .x10+16#64) <<< 48) >>> 59).toNat<23 then pcOf 26203 else pcOf 26169) t := by
  let t:=field.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : field.res.obligs u := by
    simp [field.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if ((u.getMem (u.getReg .x10+16#64) <<< 48) >>> 59).toNat<23 then pcOf 26203 else pcOf 26169) := by
    simp [t,Result.toState_pc,field.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,BitVec.ult]
  refine ⟨t,symRun_sound field hc u hu.at_pc ho,hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem heap_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26169) heapCode) (hu : Ready s A D (pcOf 26169) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 3 3 t ∧ Ready s A D
      (if (u.getMem (u.getReg .x10+24#64)).toNat<4 then pcOf 26172 else pcOf 26203) t := by
  let t:=heap.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : heap.res.obligs u := by
    simp [heap.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if (u.getMem (u.getReg .x10+24#64)).toNat<4 then pcOf 26172 else pcOf 26203) := by
    simp [t,Result.toState_pc,heap.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,BitVec.ult]
    split_ifs <;> first | rfl | omega | simp_all
  refine ⟨t,symRun_sound heap hc u hu.at_pc ho,hu.readOnly hp hr ?_⟩
  intro a;rfl

/-- C31: the hook falls back to the plain hash unless the call is the node-buffer call, the header word has zero low
11 bits and a coordinate field `≥ 23`, and the heap label is below 4. -/
def Bad (A : Nat) (s : MachineState) : Prop :=
  A≠328448 ∨ s.getMem (BitVec.ofNat 64 (A+16)) <<< 53≠0#64 ∨
    ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 59).toNat<23 ∨
    4≤(s.getMem (BitVec.ofNat 64 (A+24))).toNat

theorem read_header {A D : Nat} {input : List UInt8} {s u : MachineState} {pc : Word}
    (F : OuterSignPlain.Input A D input s) (hu : Ready s A D pc u) (off : Nat) (hoff : off=16 ∨ off=24) :
    u.getMem (u.getReg .x10+BitVec.ofNat 64 off)=s.getMem (BitVec.ofNat 64 (A+off)) := by
  have ha:=F.ahi;have hlo:=F.alo
  rw [hu.regs.get (by decide),F.x10,ofNat_add_ofNat]
  exact hu.savedFrame.get (by rcases hoff with rfl|rfl <;> omega) (by rcases hoff with rfl|rfl <;> omega)

theorem run {im : Image} {sk : BitVec 256} {A D : Nat} {input : List UInt8} {s : MachineState}
    (F : OuterSignPlain.Input A D input s) (hbad : Bad A s)
    (hc : CodeAt im (pcOf 26156) OuterSignImageLayout.code) (hp : s.pc=pcOf 26156) :
    TBSim im sk s 27 (publicHash input) (OuterSignPlain.Out s D) := by
  obtain ⟨c0,ca,cl,cf,ce,cc,bs,bq,bc,bf,bj,cs,cq,cck,cfx,cj,cp,cd⟩:=OuterSignImageLayout.slices hc
  have cplain : CodeAt im (pcOf 26203) [0x73] := codeAt_sub 47 hc (by decide) (by rfl)
  obtain ⟨u,hs,hu⟩:=save_run (A:=A) (D:=D) c0 s hp
  have ga : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  have haddr : u.getReg .x10=328448#64 ↔ A=328448 := by
    rw [ga];exact ofNat_inj (by have:=F.ahi;omega) (by decide)
  obtain ⟨v,hv,hvr⟩:=addr_step ca hu
  simp only [haddr] at hvr
  by_cases hA : A=328448
  · simp only [if_pos hA] at hvr
    have va : v.getReg .x10=BitVec.ofNat 64 A := by rw [hvr.regs.get (by decide)];exact F.x10
    obtain ⟨w,hw,hwr⟩:=low_step cl hvr va F.ahi F.alo F.aa
    rw [read_header F hvr 16 (Or.inl rfl)] at hwr
    by_cases hlo : s.getMem (BitVec.ofNat 64 (A+16)) <<< 53=0#64
    · simp only [if_pos hlo] at hwr
      have wa : w.getReg .x10=BitVec.ofNat 64 A := by rw [hwr.regs.get (by decide)];exact F.x10
      obtain ⟨y,hy,hyr⟩:=field_step cf hwr wa F.ahi F.alo F.aa
      rw [read_header F hwr 16 (Or.inl rfl)] at hyr
      by_cases hfld : ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 59).toNat<23
      · simp only [if_pos hfld] at hyr
        exact (TBSim.steps (hs.trans (hv.trans (hw.trans hy))) (OuterSignPlain.run F cplain cd hyr)).mono (by omega) (by intros;assumption)
      · simp only [if_neg hfld] at hyr
        have ya : y.getReg .x10=BitVec.ofNat 64 A := by rw [hyr.regs.get (by decide)];exact F.x10
        obtain ⟨x,hx,hxr⟩:=heap_step ce hyr ya F.ahi F.alo F.aa
        rw [read_header F hyr 24 (Or.inr rfl)] at hxr
        have hheap : ¬(s.getMem (BitVec.ofNat 64 (A+24))).toNat<4 := by
          rcases hbad with hb|hb|hb|hb
          · exact (hb hA).elim
          · exact (hb hlo).elim
          · exact (hfld hb).elim
          · omega
        simp only [if_neg hheap] at hxr
        exact TBSim.steps (hs.trans (hv.trans (hw.trans (hy.trans hx)))) (OuterSignPlain.run F cplain cd hxr)
    · simp only [if_neg hlo] at hwr
      exact (TBSim.steps (hs.trans (hv.trans hw)) (OuterSignPlain.run F cplain cd hwr)).mono (by omega) (by intros;assumption)
  · simp only [if_neg hA] at hvr
    exact (TBSim.steps (hs.trans hv) (OuterSignPlain.run F cplain cd hvr)).mono (by omega) (by intros;assumption)

#print axioms run

#print axioms addr_step
#print axioms low_step
#print axioms field_step
#print axioms heap_step
end OuterSignFallback
