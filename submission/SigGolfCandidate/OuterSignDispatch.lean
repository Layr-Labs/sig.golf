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

theorem header_words {A D coord index heap : Nat} {left right : Digest} {s u : MachineState} {pc : Word}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hu : Ready s A D pc u) (hc : coord<9) (hh : heap=2 ∨ heap=3) :
    u.getMem (u.getReg .x10+16#64)=ftsNodeWord coord index ∧
    u.getMem (u.getReg .x10+24#64)=BitVec.ofNat 64 (ftsHeapLabelC coord heap) := by
  have hw:=OuterNodeInputHeader.input_header F hc hh
  have gx : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  have ha:=F.ahi;have hlo:=F.alo;have hsep:=F.disjoint
  constructor
  · rw [gx,ofNat_add_ofNat,hu.frame.get (by omega) (by unfold Work;omega)];exact hw.1
  · rw [gx,ofNat_add_ofNat,hu.frame.get (by omega) (by unfold Work;omega)];exact hw.2

/-- C46: the label test: heap 3 (`3`) passes the first compare, heap 2 (`0xf1b02`) the second. -/
theorem label_run {im : Image} {A D coord index heap : Nat} {left right : Digest} {s u : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hc9 : coord<9) (hh : heap=2 ∨ heap=3) (hco : coord%2=1 ∨ coord=8) (cls : ClsAt im)
    (hu : Ready s A D (pcOf 26654) u) :
    ∃ t,Steps im u (if heap=2 then 6 else 3) (if heap=2 then 6 else 3) t ∧ Ready s A D (pcOf 26660) t := by
  have ua : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  have hw:=(header_words F hu hc9 hh).2
  rw [OuterNodeInputHeader.label_outer hco hh] at hw
  obtain ⟨v,hs,hv,h6⟩:=clsA_step cls.a hu ua F.ahi F.alo F.aa
  rcases hh with rfl|rfl
  · have hn : ¬ u.getMem (u.getReg .x10+24#64)=3#64 := by rw [hw];decide
    rw [if_neg hn] at hv
    obtain ⟨t,ht,htv⟩:=clsB_step cls.b hv h6
    have hy : u.getMem (u.getReg .x10+24#64)=989954#64 := by rw [hw];decide
    rw [if_pos hy] at htv
    exact ⟨t,hs.trans ht,htv⟩
  · have hy : u.getMem (u.getReg .x10+24#64)=3#64 := by rw [hw];decide
    rw [if_pos hy] at hv
    exact ⟨v,hs,hv⟩

/-- C46: steps of the outer-root route (heap 2 also runs the compare against `0xf1b02`). -/
def routeSteps (heap : Nat) : Nat := if heap=2 then 20 else 17

theorem routeSteps_le (heap : Nat) : routeSteps heap≤20 := by unfold routeSteps;split_ifs <;> omega

theorem route {im : Image} {A D coord index heap : Nat} {left right : Digest} {s u : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hA : A=328448) (hc : 1≤coord) (hc9 : coord<9) (hi : index<2^31) (hh : heap=2 ∨ heap=3)
    (hco : coord%2=1 ∨ coord=8) (ca : CodeAt im (pcOf 26158) addrCode) (ck : CodeAt im (pcOf 26161) hookCode) (cls : ClsAt im)
    (hu : Ready s A D (pcOf 26158) u) :
    ∃ t,Steps im u (routeSteps heap) (routeSteps heap) t ∧
      Ready s A D (if coord=8 then pcOf 26186 else pcOf 26175) t := by
  have ga : u.getReg .x10=328448#64 := by
    rw [hu.regs.get (by decide),F.x10,hA]
  obtain ⟨v,hs,hv⟩:=addr_run ca hu ga
  obtain ⟨w,hw,hwv⟩:=hook_step ck hv
  obtain ⟨x,hx,hxv⟩:=label_run F hc9 hh hco cls hwv
  have xa : x.getReg .x10=BitVec.ofNat 64 A := by rw [hxv.regs.get (by decide)];exact F.x10
  obtain ⟨y,hy,hyv⟩:=clsC_step cls.c hxv xa F.ahi F.alo F.aa
  have lo : x.getMem (x.getReg .x10+16#64) <<< 53=0#64 := by
    rw [(header_words F hxv hc9 hh).1];exact OuterSignFields.fts_low11 coord index hc9
  rw [if_pos lo] at hyv
  have ya : y.getReg .x10=BitVec.ofNat 64 A := by rw [hyv.regs.get (by decide)];exact F.x10
  obtain ⟨z,hz,hzv,hz7,hz6⟩:=clsD_step cls.d hyv ya F.ahi F.alo F.aa
  have fld : (y.getMem (y.getReg .x10+16#64) <<< 48) >>> 59=BitVec.ofNat 64 (31-coord/2) := by
    rw [(header_words F hyv hc9 hh).1];exact OuterSignFields.fts_field coord index hc9
  have hge : ¬ ((y.getMem (y.getReg .x10+16#64) <<< 48) >>> 59).toNat<27 := by
    rw [fld,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];omega
  rw [if_neg hge] at hzv
  obtain ⟨e,he,hev⟩:=clsE_step cls.e hzv
  have hcmp : z.getReg .x7=z.getReg .x6 ↔ coord=8 := by
    rw [hz7,hz6,fld];exact OuterSignFields.coordinate coord hc9
  have hst : routeSteps heap=3+(1+((if heap=2 then 6 else 3)+(3+(5+(1+1))))) := by
    unfold routeSteps;split_ifs <;> rfl
  by_cases h8 : coord=8
  · rw [if_pos (hcmp.mpr h8)] at hev
    obtain ⟨t,ht,htv⟩:=clsCJ_step cls.cj hev
    rw [if_pos h8]
    exact ⟨t,by rw [hst];exact hs.trans (hw.trans (hx.trans (hy.trans (hz.trans (he.trans ht))))),htv⟩
  · rw [if_neg (fun h=>h8 (hcmp.mp h))] at hev
    obtain ⟨t,ht,htv⟩:=clsBJ_step cls.bj hev
    rw [if_neg h8]
    exact ⟨t,by rw [hst];exact hs.trans (hw.trans (hx.trans (hy.trans (hz.trans (he.trans ht))))),htv⟩

#print axioms route

#print axioms addr_run
#print axioms label_run
end OuterSignDispatch
