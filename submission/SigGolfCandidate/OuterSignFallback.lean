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

theorem header_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26161) headerCode) (hu : Ready s A D (pcOf 26161) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 6 6 t ∧ Ready s A D
      (if ((u.getMem (u.getReg .x10+16#64) <<< 48) >>> 48)=63488#64 then pcOf 26167 else pcOf 26203) t := by
  let t:=header.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : header.res.obligs u := by
    simp [header.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if ((u.getMem (u.getReg .x10+16#64) <<< 48) >>> 48)=63488#64 then pcOf 26167 else pcOf 26203) := by
    simp [t,Result.toState_pc,header.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval]
  refine ⟨t,symRun_sound header hc u hu.at_pc ho,hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem heap_step {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26167) heapCode) (hu : Ready s A D (pcOf 26167) u)
    (ha : u.getReg .x10=BitVec.ofNat 64 A) (hi : A<2^20) (hlo : 2048≤A) (hma : A%8=0) :
    ∃ t,Steps im u 3 3 t ∧ Ready s A D
      (if (u.getMem (u.getReg .x10+24#64)).toNat<4 then pcOf 26170 else pcOf 26203) t := by
  let t:=heap.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have ho : heap.res.obligs u := by
    simp [heap.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
      memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
    omega
  have hp : t.pc=(if (u.getMem (u.getReg .x10+24#64)).toNat<4 then pcOf 26170 else pcOf 26203) := by
    simp [t,Result.toState_pc,heap.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,BitVec.ult]
    split_ifs <;> first | rfl | omega
  refine ⟨t,symRun_sound heap hc u hu.at_pc ho,hu.readOnly hp hr ?_⟩
  intro a;rfl

def Bad (A : Nat) (s : MachineState) : Prop :=
  A≠328448 ∨ ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 48)≠63488#64 ∨
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
    TBSim im sk s 25 (publicHash input) (OuterSignPlain.Out s D) := by
  obtain ⟨c0,ca,ch,ce,cc,bs,bq,bc,bf,bj,cs,cq,cck,cf,cj,cp,cd⟩:=OuterSignImageLayout.slices hc
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
    obtain ⟨w,hw,hwr⟩:=header_step ch hvr va F.ahi F.alo F.aa
    have hhead := read_header F hvr 16 (Or.inl rfl)
    rw [hhead] at hwr
    by_cases htag : ((s.getMem (BitVec.ofNat 64 (A+16)) <<< 48) >>> 48)=63488#64
    · simp only [if_pos htag] at hwr
      have wa : w.getReg .x10=BitVec.ofNat 64 A := by rw [hwr.regs.get (by decide)];exact F.x10
      obtain ⟨x,hx,hxr⟩:=heap_step ce hwr wa F.ahi F.alo F.aa
      rw [read_header F hwr 24 (Or.inr rfl)] at hxr
      have hheap : ¬(s.getMem (BitVec.ofNat 64 (A+24))).toNat<4 := by
        rcases hbad with hb|hb|hb
        · exact (hb hA).elim
        · exact (hb htag).elim
        · omega
      simp only [if_neg hheap] at hxr
      exact TBSim.steps (hs.trans (hv.trans (hw.trans hx))) (OuterSignPlain.run F cplain cd hxr)
    · simp only [if_neg htag] at hwr
      exact (TBSim.steps (hs.trans (hv.trans hw)) (OuterSignPlain.run F cplain cd hwr)).mono (by omega) (by intros;assumption)
  · simp only [if_neg hA] at hvr
    exact (TBSim.steps (hs.trans hv) (OuterSignPlain.run F cplain cd hvr)).mono (by omega) (by intros;assumption)

#print axioms run

#print axioms addr_step
#print axioms header_step
#print axioms heap_step
end OuterSignFallback
