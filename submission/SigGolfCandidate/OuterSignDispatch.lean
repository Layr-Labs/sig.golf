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

theorem low_obligs (s : MachineState) (A : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 A)
    (hi : A<2^20) (hlo : 2048≤A) (hm : A%8=0) : low.res.obligs s := by
  simp [low.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
    memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
  omega

theorem low_run {im : Image} {A D : Nat} {s u : MachineState} {pre right : List UInt8}
    (F : Input A D pre right s) (hc : CodeAt im (pcOf 26161) lowCode)
    (hu : Ready s A D (pcOf 26161) u)
    (hw : u.getMem (u.getReg .x10+16#64) <<< 53=0#64) :
    ∃ t,Steps im u 3 3 t ∧ Ready s A D (pcOf 26164) t := by
  have gx : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  let t:=low.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26164 := by
    simp [t,Result.toState_pc,low.res,E.eval,RegFile.get,Addr.eval,BinOp.eval,CmpOp.eval,hw]
  refine ⟨t,symRun_sound low hc u hu.at_pc (low_obligs u A gx F.ahi F.alo F.aa),hu.readOnly hp hr ?_⟩
  intro a;rfl

theorem field_obligs (s : MachineState) (A : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 A)
    (hi : A<2^20) (hlo : 2048≤A) (hm : A%8=0) : field.res.obligs s := by
  simp [field.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
    memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
  omega

theorem field_run {im : Image} {A D f : Nat} {s u : MachineState} {pre right : List UInt8}
    (F : Input A D pre right s) (hc : CodeAt im (pcOf 26164) fieldCode)
    (hu : Ready s A D (pcOf 26164) u) (hf : 23≤f) (hf32 : f<32)
    (hw : (u.getMem (u.getReg .x10+16#64) <<< 48) >>> 59=BitVec.ofNat 64 f) :
    ∃ t,Steps im u 5 5 t ∧ Ready s A D (pcOf 26169) t ∧ t.getReg .x7=BitVec.ofNat 64 f := by
  have gx : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  let t:=field.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hlt : ¬ BitVec.ult (BitVec.ofNat 64 f) 23#64 := by
    simp [BitVec.ult,Nat.mod_eq_of_lt (show f<2^64 by omega)] <;> omega
  have hp : t.pc=pcOf 26169 := by
    simp [t,Result.toState_pc,field.res,E.eval,RegFile.get,Addr.eval,BinOp.eval,CmpOp.eval,hw]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show f<2^64 by omega)] at hlt ⊢
    simp [hlt]
  have h7 : t.getReg .x7=BitVec.ofNat 64 f := by
    simp [t,Result.toState_getReg,field.res,E.eval,RegFile.get,Addr.eval,BinOp.eval,hw]
  refine ⟨t,symRun_sound field hc u hu.at_pc (field_obligs u A gx F.ahi F.alo F.aa),hu.readOnly hp hr ?_,h7⟩
  intro a;rfl

theorem heap_obligs (s : MachineState) (A : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 A)
    (hi : A<2^20) (hlo : 2048≤A) (hm : A%8=0) : heap.res.obligs s := by
  simp [heap.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
    memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
  omega

theorem heap_run {im : Image} {A D h : Nat} {s u : MachineState} {pre right : List UInt8}
    (F : Input A D pre right s) (hc : CodeAt im (pcOf 26169) heapCode)
    (hu : Ready s A D (pcOf 26169) u) (hh : h=2 ∨ h=3)
    (hw : u.getMem (u.getReg .x10+24#64)=BitVec.ofNat 64 h) :
    ∃ t,Steps im u 3 3 t ∧ Ready s A D (pcOf 26172) t ∧ t.getReg .x7=u.getReg .x7 := by
  have gx : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  let t:=heap.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hp : t.pc=pcOf 26172 := by
    rcases hh with rfl|rfl <;>
      simp [t,Result.toState_pc,heap.res,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,hw]
  have h7 : t.getReg .x7=u.getReg .x7 := by
    simp [t,Result.toState_getReg,heap.res,RegFile.get,E.eval]
  refine ⟨t,symRun_sound heap hc u hu.at_pc (heap_obligs u A gx F.ahi F.alo F.aa),hu.readOnly hp hr ?_,h7⟩
  intro a;rfl

theorem coord_run {im : Image} {A D coord : Nat} {s u : MachineState} {pre right : List UInt8}
    (F : Input A D pre right s) (hc : CodeAt im (pcOf 26172) coordCode)
    (hu : Ready s A D (pcOf 26172) u) (hcoord9 : coord<9)
    (h7 : u.getReg .x7=BitVec.ofNat 64 (31-coord)) :
    ∃ t,Steps im u 3 3 t ∧ Ready s A D (if coord=8 then pcOf 26186 else pcOf 26175) t := by
  let t:=OuterSignBlocks.coord.res.toState u
  have hr : RegsExcept u t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
  have hob : OuterSignBlocks.coord.res.obligs u := by
    simp [OuterSignBlocks.coord.res,Result.obligs,Oblig.all]
  have hp : t.pc=(if coord=8 then pcOf 26186 else pcOf 26175) := by
    change (OuterSignBlocks.coord.res.toState u).pc=_
    simp only [Result.toState_pc,OuterSignBlocks.coord.res,E.eval,RegFile.get,Addr.eval,BinOp.eval,CmpOp.eval,h7]
    by_cases h8 : coord=8
    · have hb : BitVec.ofNat 64 (31-coord)=23#64 := (OuterSignFields.coordinate coord hcoord9).mpr h8
      simp [if_pos h8,hb]
    · have hb : ¬BitVec.ofNat 64 (31-coord)=23#64 := fun h=>h8 ((OuterSignFields.coordinate coord hcoord9).mp h)
      simp [if_neg h8,hb]
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
    (ca : CodeAt im (pcOf 26158) addrCode) (cl : CodeAt im (pcOf 26161) lowCode)
    (cf : CodeAt im (pcOf 26164) fieldCode)
    (ce : CodeAt im (pcOf 26169) heapCode) (cc : CodeAt im (pcOf 26172) coordCode)
    (hu : Ready s A D (pcOf 26158) u) :
    ∃ t,Steps im u 17 17 t ∧ Ready s A D (if coord=8 then pcOf 26186 else pcOf 26175) t := by
  have ga : u.getReg .x10=328448#64 := by
    rw [hu.regs.get (by decide),F.x10,hA]
  obtain ⟨v,hs,hv⟩:=addr_run ca hu ga
  have hwh:=(header_words F hv hc9 hh).1
  have lo : v.getMem (v.getReg .x10+16#64) <<< 53=0#64 := by
    rw [hwh];exact OuterSignFields.fts_low11 coord index hc9
  obtain ⟨w,hw,hwv⟩:=low_run F cl hv lo
  have fld : (w.getMem (w.getReg .x10+16#64) <<< 48) >>> 59=BitVec.ofNat 64 (31-coord) := by
    rw [(header_words F hwv hc9 hh).1];exact OuterSignFields.fts_field coord index hc9
  obtain ⟨y,hy,hyv,hy7⟩:=field_run F cf hwv (by omega) (by omega) fld
  obtain ⟨x,hx,hxv,hx7⟩:=heap_run F ce hyv hh (header_words F hyv hc9 hh).2
  obtain ⟨t,ht,htv⟩:=coord_run F cc hxv hc9 (hx7.trans hy7)
  exact ⟨t,hs.trans (hw.trans (hy.trans (hx.trans ht))),htv⟩

#print axioms route

#print axioms coord_run

#print axioms addr_run
#print axioms low_run
#print axioms field_run
#print axioms heap_run
end OuterSignDispatch
