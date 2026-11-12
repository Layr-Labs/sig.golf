import SigGolfCandidate.OuterSignEntry
import SigGolfCandidate.OuterSignFields
import SigGolfCandidate.OuterNodeInputHeader
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSignDispatch
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open OuterNodeSearchInvariant OuterSignBlocks OuterSignEntry
open SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem addr_run {im : Image} {A D : Nat} {s u : MachineState}
    (hc : CodeAt im (pcOf 26158) addrCode) (hu : Ready s A D (pcOf 26158) u)
    (ha : u.getReg .x10=328448#64) :
    ∃ t,Steps im u 3 3 t ∧ Ready s A D (pcOf 26161) t := by
  let t:=addr.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26161 := by
    simp [t,Result.toState_pc,addr.res,E.eval,CmpOp.eval,ha]
  refine ⟨t,symRun_sound addr hc u hu.at_pc (by simp [addr.res,Result.obligs,Oblig.all]),hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem header_obligs (s : MachineState) (A : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 A)
    (hi : A<2^20) (hlo : 2048≤A) (hm : A%8=0) : header.res.obligs s := by
  simp [header.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
    memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
  omega

theorem header_run {im : Image} {A D : Nat} {s u : MachineState} {pre right : List UInt8}
    (F : Input A D pre right s) (hc : CodeAt im (pcOf 26161) headerCode)
    (hu : Ready s A D (pcOf 26161) u)
    (hw : ((u.getMem (u.getReg .x10+16#64) <<< 48) >>> 48)=63488#64) :
    ∃ t,Steps im u 6 6 t ∧ Ready s A D (pcOf 26167) t := by
  have gx : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  let t:=header.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26167 := by
    simp [t,Result.toState_pc,header.res,E.eval,RegFile.get,Addr.eval,BinOp.eval,CmpOp.eval,hw]
  refine ⟨t,symRun_sound header hc u hu.at_pc (header_obligs u A gx F.ahi F.alo F.aa),hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem heap_obligs (s : MachineState) (A : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 A)
    (hi : A<2^20) (hlo : 2048≤A) (hm : A%8=0) : heap.res.obligs s := by
  simp [heap.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
    memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
  omega

theorem heap_run {im : Image} {A D h : Nat} {s u : MachineState} {pre right : List UInt8}
    (F : Input A D pre right s) (hc : CodeAt im (pcOf 26167) heapCode)
    (hu : Ready s A D (pcOf 26167) u) (hh : h=2 ∨ h=3)
    (hw : u.getMem (u.getReg .x10+24#64)=BitVec.ofNat 64 h) :
    ∃ t,Steps im u 3 3 t ∧ Ready s A D (pcOf 26170) t := by
  have gx : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  let t:=heap.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26170 := by
    rcases hh with rfl|rfl <;>
      simp [t,Result.toState_pc,heap.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,hw]
  refine ⟨t,symRun_sound heap hc u hu.at_pc (heap_obligs u A gx F.ahi F.alo F.aa),hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem coord_run {im : Image} {A D coord index : Nat} {s u : MachineState} {pre right : List UInt8}
    (F : Input A D pre right s) (hc : CodeAt im (pcOf 26170) coordCode)
    (hu : Ready s A D (pcOf 26170) u) (hcoord : 1≤coord) (hcoord9 : coord<9) (hi : index<2^31)
    (hw : u.getMem (u.getReg .x10+16#64)=ftsNodeWord coord index) :
    ∃ t,Steps im u 5 5 t ∧ Ready s A D (if coord=8 then pcOf 26186 else pcOf 26175) t := by
  have gx : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  let t:=OuterSignBlocks.coord.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hob : OuterSignBlocks.coord.res.obligs u := header_obligs u A gx F.ahi F.alo F.aa
  have hp : t.pc=(if coord=8 then pcOf 26186 else pcOf 26175) := by
    change (OuterSignBlocks.coord.res.toState u).pc=_
    simp only [Result.toState_pc,OuterSignBlocks.coord.res,E.eval,RegFile.get,Addr.eval,BinOp.eval,CmpOp.eval,hw]
    norm_num only [BitVec.toNat_ofNat]
    simp only [beq_iff_eq]
    by_cases h8 : coord=8
    · have hb : ((ftsNodeWord coord index >>> 16) &&& 15#64)=7#64 :=
        (OuterSignFields.coordinate coord index hcoord hcoord9 hi).mpr h8
      simp only [if_pos h8,if_pos hb]
    · have hb : ¬((ftsNodeWord coord index >>> 16) &&& 15#64)=7#64 :=
        fun h=>h8 ((OuterSignFields.coordinate coord index hcoord hcoord9 hi).mp h)
      simp only [if_neg h8,if_neg hb]
  refine ⟨t,symRun_sound OuterSignBlocks.coord hc u hu.at_pc hob,hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem header_words {A D coord index heap : Nat} {left right : Digest} {s u : MachineState} {pc : Word}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hu : Ready s A D pc u) (hc : coord<9) (hh : heap=2 ∨ heap=3) :
    u.getMem (u.getReg .x10+16#64)=ftsNodeWord coord index ∧
    u.getMem (u.getReg .x10+24#64)=BitVec.ofNat 64 heap := by
  have hw:=OuterNodeInputHeader.input_header F hc hh
  have gx : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  have ha:=F.ahi;have hlo:=F.alo;have hsep:=F.disjoint
  constructor
  · rw [gx,ofNat_add_ofNat,hu.frame.get (by omega) (by unfold Work;omega)];exact hw.1
  · rw [gx,ofNat_add_ofNat,hu.frame.get (by omega) (by unfold Work;omega)];exact hw.2

theorem route {im : Image} {A D coord index heap : Nat} {left right : Digest} {s u : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hA : A=328448) (hc : 1≤coord) (hc9 : coord<9) (hi : index<2^31) (hh : heap=2 ∨ heap=3)
    (ca : CodeAt im (pcOf 26158) addrCode) (ch : CodeAt im (pcOf 26161) headerCode)
    (ce : CodeAt im (pcOf 26167) heapCode) (cc : CodeAt im (pcOf 26170) coordCode)
    (hu : Ready s A D (pcOf 26158) u) :
    ∃ t,Steps im u 17 17 t ∧ Ready s A D (if coord=8 then pcOf 26186 else pcOf 26175) t := by
  have ga : u.getReg .x10=328448#64 := by
    rw [hu.regs.get (by decide),F.x10,hA]
  obtain ⟨v,hs,hv⟩:=addr_run ca hu ga
  have hwh:=(header_words F hv hc9 hh).1
  have tag : ((v.getMem (v.getReg .x10+16#64) <<< 48) >>> 48)=63488#64 := by
    rw [hwh];exact OuterSignFields.fts_tag coord index hc hc9 hi
  obtain ⟨w,hw,hwv⟩:=header_run F ch hv tag
  obtain ⟨x,hx,hxv⟩:=heap_run F ce hwv hh (header_words F hwv hc9 hh).2
  obtain ⟨t,ht,htv⟩:=coord_run F cc hxv hc hc9 hi (header_words F hxv hc9 hh).1
  exact ⟨t,hs.trans (hw.trans (hx.trans ht)),htv⟩

#print axioms route

#print axioms coord_run

#print axioms addr_run
#print axioms header_run
#print axioms heap_run
end OuterSignDispatch
