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

theorem read_word {A D : Nat} {pre right : List UInt8} {s u : MachineState} {pc : Word}
    (F : Input A D pre right s) (hu : Ready s A D pc u) (off : Nat) (hoff : off=16 ∨ off=24) :
    u.getMem (u.getReg .x10+BitVec.ofNat 64 off)=s.getMem (BitVec.ofNat 64 (A+off)) := by
  have gx : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  have ha:=F.ahi;have hlo:=F.alo;have hsep:=F.disjoint
  rw [gx,ofNat_add_ofNat,hu.frame.get (by rcases hoff with rfl|rfl <;> omega)
    (by unfold Work;rcases hoff with rfl|rfl <;> omega)]

/-- C47: steps of the outer-root route (address test, hook, classifier): coordinate 8 heap 2 / 3 `10` / `11`, odd
coordinates heap 2 / 3 `23` / `28`. -/
def routeSteps (coord heap : Nat) : Nat :=
  if coord=8 then (if heap=2 then 10 else 11) else (if heap=2 then 23 else 28)

theorem routeSteps_le (coord heap : Nat) : routeSteps coord heap≤28 := by unfold routeSteps;split_ifs <;> omega
theorem routeSteps_le8 (heap : Nat) : routeSteps 8 heap≤11 := by unfold routeSteps;split_ifs <;> omega

theorem route {im : Image} {A D coord index heap : Nat} {left right : Digest} {s u : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hA : A=328448) (hc : 1≤coord) (hc9 : coord<9) (hi : index<2^31) (hh : heap=2 ∨ heap=3)
    (hco : coord%2=1 ∨ coord=8) (ca : CodeAt im (pcOf 26158) addrCode) (ck : CodeAt im (pcOf 26161) hookCode) (cls : ClsAt im)
    (hu : Ready s A D (pcOf 26158) u) :
    ∃ t,Steps im u (routeSteps coord heap) (routeSteps coord heap) t ∧
      Ready s A D (if coord=8 then pcOf 26186 else pcOf 26175) t := by
  have ga : u.getReg .x10=328448#64 := by
    rw [hu.regs.get (by decide),F.x10,hA]
  obtain ⟨v,hs,hv⟩:=addr_run ca hu ga
  obtain ⟨w,hw,hwv⟩:=hook_step ck hv
  have wa : w.getReg .x10=BitVec.ofNat 64 A := by rw [hwv.regs.get (by decide)];exact F.x10
  obtain ⟨x,hx,hxv⟩:=clsA_step cls.a hwv wa F.ahi F.alo F.aa
  rw [read_word F hwv 24 (Or.inr rfl)] at hxv
  have xa : x.getReg .x10=BitVec.ofNat 64 A := by rw [hxv.regs.get (by decide)];exact F.x10
  by_cases h8 : coord=8
  · subst coord
    obtain ⟨hlo,hhi⟩:=OuterNodeInputHeader.input_eight F hh
    rw [if_pos rfl]
    rcases hh with rfl|rfl
    · simp only [↓reduceIte] at hlo hhi
      rw [hhi,if_pos rfl] at hxv
      obtain ⟨y,hy,hyv⟩:=clsZ_step cls.z hxv xa F.ahi F.alo F.aa
      rw [read_word F hxv 16 (Or.inl rfl),hlo,if_pos (OuterSignFields.fts_low11 8 index (by decide))] at hyv
      obtain ⟨t,ht,htv⟩:=clsCJ_step cls.cj hyv
      refine ⟨t,?_,htv⟩
      rw [show routeSteps 8 2=3+(1+(2+(3+1))) from rfl]
      exact hs.trans (hw.trans (hx.trans (hy.trans ht)))
    · have hne : ¬ ftsNodeWord 8 index=0#64 := fun he=>ftsNodeWord_ne_zero 8 index (by rw [he];rfl)
      simp only [show ¬ (3:Nat)=2 by decide,if_false] at hlo hhi
      rw [hhi,if_neg hne] at hxv
      obtain ⟨y,hy,hyv⟩:=clsT_step cls.t hxv xa F.ahi F.alo F.aa
      rw [read_word F hxv 16 (Or.inl rfl),hlo,if_pos rfl] at hyv
      obtain ⟨t,ht,htv⟩:=clsCJ_step cls.cj hyv
      refine ⟨t,?_,htv⟩
      rw [show routeSteps 8 3=3+(1+(2+(4+1))) from rfl]
      exact hs.trans (hw.trans (hx.trans (hy.trans ht)))
  · have ho : coord%2=1 := by omega
    rw [if_neg h8]
    -- the field tests from 26771
    have tail : ∀ v : MachineState,Ready s A D (pcOf 26771) v →
        ∃ t,Steps im v 9 9 t ∧ Ready s A D (pcOf 26175) t := by
      intro v hv
      have hlo:=(OuterNodeInputHeader.input_odd F hc9 hh ho).1
      have va : v.getReg .x10=BitVec.ofNat 64 A := by rw [hv.regs.get (by decide)];exact F.x10
      obtain ⟨p,hp,hpv⟩:=clsC_step cls.c hv va F.ahi F.alo F.aa
      rw [read_word F hv 16 (Or.inl rfl),hlo,if_pos (OuterSignFields.fts_low11 coord index hc9)] at hpv
      have pa : p.getReg .x10=BitVec.ofNat 64 A := by rw [hpv.regs.get (by decide)];exact F.x10
      obtain ⟨q,hq,hqv⟩:=clsD_step cls.d hpv pa F.ahi F.alo F.aa
      rw [read_word F hpv 16 (Or.inl rfl),hlo,if_neg (OuterSignFields.field_ge coord index hc9)] at hqv
      obtain ⟨t,ht,htv⟩:=clsBJ_step cls.bj hqv
      exact ⟨t,hp.trans (hq.trans ht),htv⟩
    -- the label tests from 26758 (`hi` the high word: `0xf1b02` on heap 2, `K` on heap 3)
    have front : ∀ hi : BitVec 64, s.getMem (BitVec.ofNat 64 (A+24))=hi → hi≠0#64 →
        ∃ z,Steps im u 14 14 z ∧ Ready s A D (if hi=989954#64 then pcOf 26771 else pcOf 26766) z ∧
          z.getReg .x6=hi := by
      intro hi hhi hnz
      have hlo:=(OuterNodeInputHeader.input_odd F hc9 hh ho).1
      rw [hhi,if_neg hnz] at hxv
      obtain ⟨y,hy,hyv⟩:=clsT_step cls.t hxv xa F.ahi F.alo F.aa
      rw [read_word F hxv 16 (Or.inl rfl),hlo,if_neg (OuterSignFields.ne_T4 coord index hc9)] at hyv
      have ya : y.getReg .x10=BitVec.ofNat 64 A := by rw [hyv.regs.get (by decide)];exact F.x10
      obtain ⟨z,hz,hzv,hz6⟩:=clsH_step cls.h hyv ya F.ahi F.alo F.aa
      rw [read_word F hyv 24 (Or.inr rfl),hhi] at hzv hz6
      exact ⟨z,hs.trans (hw.trans (hx.trans (hy.trans hz))),hzv,hz6⟩
    have hhi:=(OuterNodeInputHeader.input_odd F hc9 hh ho).2
    rcases hh with rfl|rfl
    · simp only [↓reduceIte] at hhi
      obtain ⟨z,hz,hzv,-⟩:=front 989954#64 hhi (by decide)
      rw [if_pos rfl] at hzv
      obtain ⟨t,ht,htv⟩:=tail z hzv
      refine ⟨t,?_,htv⟩
      have e : routeSteps coord 2=14+9 := by unfold routeSteps;rw [if_neg h8,if_pos rfl]
      rw [e];exact hz.trans ht
    · simp only [show ¬ (3:Nat)=2 by decide,if_false] at hhi
      obtain ⟨z,hz,hzv,hz6⟩:=front 3879747587#64 hhi (by decide)
      rw [if_neg (by decide)] at hzv
      obtain ⟨k,hk,hkv⟩:=clsK_step cls.k hzv hz6
      rw [if_pos rfl] at hkv
      obtain ⟨t,ht,htv⟩:=tail k hkv
      refine ⟨t,?_,htv⟩
      have e : routeSteps coord 3=14+(5+9) := by unfold routeSteps;rw [if_neg h8,if_neg (by decide)]
      rw [e];exact hz.trans (hk.trans ht)

#print axioms route

#print axioms addr_run
end OuterSignDispatch
