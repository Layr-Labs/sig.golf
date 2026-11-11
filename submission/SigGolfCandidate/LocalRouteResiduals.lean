import SigGolfCandidate.Merge055
import SigGolfCandidate.LocalRouteMachineHelpers
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
set_option linter.all false
namespace LocalRouteResiduals
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.WCT9.CanonicalPolicy
def pre0Code : List (BitVec 32) := [0x66e37,0xe0e13,0x2942806f]
sym_block pre0 := symRun {noAlias:=true} pre0Code (pcOf 46933) 10
def test0Code : List (BitVec 32) := [0x1536663]
sym_block test0 := symRun {noAlias:=true} test0Code (pcOf 46936) 10
def zero0Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero0 := symRun {noAlias:=true} zero0Code (pcOf 46937) 10
def sub0Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub0 := symRun {noAlias:=true} sub0Code (pcOf 46939) 10
structure Code0 (im : Image) : Prop where
  pre : CodeAt im (pcOf 46933) pre0Code
  helper : CodeAt im (pcOf 88060) LocalRouteMachineHelpers.expand1Code
  test : CodeAt im (pcOf 46936) test0Code
  zero : CodeAt im (pcOf 46937) zero0Code
  sub : CodeAt im (pcOf 46939) sub0Code

theorem first0_steps {im : Image} (hc : Code0 im)
    (s : MachineState) (hp : s.pc=pcOf 46933) (index R C : Nat)
    (hi : index<2^64) (hR : R≤74) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417856#64=BitVec.ofNat 64 C)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 16 16 t ∧
      t.pc=(if guardedCredit R C (lowerPathSave 1 (index/2^12))<R then pcOf 46939 else pcOf 46937) ∧
      t.getReg .x6=BitVec.ofNat 64 (guardedCredit R C (lowerPathSave 1 (index/2^12))) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let u := pre0.res.toState s
  have su : Steps im s 3 3 u := symRun_sound pre0 hc.pre s hp (by simp [pre0.res,rv_simp])
  have pu : u.pc=pcOf 88060 := rfl
  have u28 : u.getReg .x28=0x66000#64 := rfl
  have u21 : u.getReg .x21=BitVec.ofNat 64 R := by simpa [u,pre0.res,rv_simp] using h21
  have um : u.getMem 417856#64=BitVec.ofNat 64 C := by simpa [u,pre0.res,rv_simp] using hm
  have ui : u.getMem 0x20550#64=BitVec.ofNat 64 index := by simpa [u,pre0.res,rv_simp] using hindex
  have ru : RegsExcept s u [.x28] := by intro r hr;cases r <;> simp at hr <;> rfl
  have fu : Frame s u (fun _=>False) := by intro A ha hn;rfl
  obtain ⟨v,sv,pv,v6,rv,fv⟩ := LocalRouteMachineHelpers.expand1_steps hc.helper u pu index C R
    hi hC (by omega) u28 u21 um ui
  let t := test0.res.toState v
  have st : Steps im v 1 1 t := symRun_sound test0 hc.test v pv (by simp [test0.res,rv_simp])
  have rt : RegsExcept v t [] := by intro r hr;cases r <;> rfl
  have ft : Frame v t (fun _=>False) := by intro A ha hn;rfl
  have ht6 : t.getReg .x6=BitVec.ofNat 64 (guardedCredit R C (lowerPathSave 1 (index/2^12))) := by
    rw [rt .x6 (by decide)];exact v6
  refine ⟨t,(su.trans sv).trans st,?_,ht6,((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
  have v21 : v.getReg .x21=BitVec.ofNat 64 R := (rv .x21 (by decide)).trans u21
  have hcG : guardedCredit R C (lowerPathSave 1 (index/2^12))<2^64 :=
    guardedCredit_lt R C _ _ (by omega) hC (lowerPathSave_le_one _ _)
  simp only [t,Result.toState_pc,test0.res,rv_simp,v21,v6]
  simp only [BitVec.ult_eq_decide,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hcG,
    Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
  all_goals split_ifs <;> rfl
#print axioms first0_steps
def pre1Code : List (BitVec 32) := [0x66e37,0xe0e13,0x2842806f]
sym_block pre1 := symRun {noAlias:=true} pre1Code (pcOf 46949) 10
def test1Code : List (BitVec 32) := [0x1536663]
sym_block test1 := symRun {noAlias:=true} test1Code (pcOf 46952) 10
def zero1Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero1 := symRun {noAlias:=true} zero1Code (pcOf 46953) 10
def sub1Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub1 := symRun {noAlias:=true} sub1Code (pcOf 46955) 10
structure Code1 (im : Image) : Prop where
  pre : CodeAt im (pcOf 46949) pre1Code
  helper : CodeAt im (pcOf 88072) LocalRouteMachineHelpers.expand2Code
  test : CodeAt im (pcOf 46952) test1Code
  zero : CodeAt im (pcOf 46953) zero1Code
  sub : CodeAt im (pcOf 46955) sub1Code

theorem first1_steps {im : Image} (hc : Code1 im)
    (s : MachineState) (hp : s.pc=pcOf 46949) (index R C : Nat)
    (hi : index<2^64) (hR : R≤74) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417864#64=BitVec.ofNat 64 C)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 16 16 t ∧
      t.pc=(if guardedCredit R C (lowerPathSave 2 (index/2^6))<R then pcOf 46955 else pcOf 46953) ∧
      t.getReg .x6=BitVec.ofNat 64 (guardedCredit R C (lowerPathSave 2 (index/2^6))) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let u := pre1.res.toState s
  have su : Steps im s 3 3 u := symRun_sound pre1 hc.pre s hp (by simp [pre1.res,rv_simp])
  have pu : u.pc=pcOf 88072 := rfl
  have u28 : u.getReg .x28=0x66000#64 := rfl
  have u21 : u.getReg .x21=BitVec.ofNat 64 R := by simpa [u,pre1.res,rv_simp] using h21
  have um : u.getMem 417864#64=BitVec.ofNat 64 C := by simpa [u,pre1.res,rv_simp] using hm
  have ui : u.getMem 0x20550#64=BitVec.ofNat 64 index := by simpa [u,pre1.res,rv_simp] using hindex
  have ru : RegsExcept s u [.x28] := by intro r hr;cases r <;> simp at hr <;> rfl
  have fu : Frame s u (fun _=>False) := by intro A ha hn;rfl
  obtain ⟨v,sv,pv,v6,rv,fv⟩ := LocalRouteMachineHelpers.expand2_steps hc.helper u pu index C R
    hi hC (by omega) u28 u21 um ui
  let t := test1.res.toState v
  have st : Steps im v 1 1 t := symRun_sound test1 hc.test v pv (by simp [test1.res,rv_simp])
  have rt : RegsExcept v t [] := by intro r hr;cases r <;> rfl
  have ft : Frame v t (fun _=>False) := by intro A ha hn;rfl
  have ht6 : t.getReg .x6=BitVec.ofNat 64 (guardedCredit R C (lowerPathSave 2 (index/2^6))) := by
    rw [rt .x6 (by decide)];exact v6
  refine ⟨t,(su.trans sv).trans st,?_,ht6,((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
  have v21 : v.getReg .x21=BitVec.ofNat 64 R := (rv .x21 (by decide)).trans u21
  have hcG : guardedCredit R C (lowerPathSave 2 (index/2^6))<2^64 :=
    guardedCredit_lt R C _ _ (by omega) hC (lowerPathSave_le_one _ _)
  simp only [t,Result.toState_pc,test1.res,rv_simp,v21,v6]
  simp only [BitVec.ult_eq_decide,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hcG,
    Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
  all_goals split_ifs <;> rfl
#print axioms first1_steps
def pre2Code : List (BitVec 32) := [0x66e37,0xe0e13,0x2702806f]
sym_block pre2 := symRun {noAlias:=true} pre2Code (pcOf 46966) 10
def test2Code : List (BitVec 32) := [0x1536663]
sym_block test2 := symRun {noAlias:=true} test2Code (pcOf 46969) 10
def zero2Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero2 := symRun {noAlias:=true} zero2Code (pcOf 46970) 10
def sub2Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub2 := symRun {noAlias:=true} sub2Code (pcOf 46972) 10
structure Code2 (im : Image) : Prop where
  pre : CodeAt im (pcOf 46966) pre2Code
  helper : CodeAt im (pcOf 88084) LocalRouteMachineHelpers.expand3Code
  test : CodeAt im (pcOf 46969) test2Code
  zero : CodeAt im (pcOf 46970) zero2Code
  sub : CodeAt im (pcOf 46972) sub2Code

theorem first2_steps {im : Image} (hc : Code2 im)
    (s : MachineState) (hp : s.pc=pcOf 46966) (index R C : Nat)
    (hi : index<2^64) (hR : R≤74) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417872#64=BitVec.ofNat 64 C)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 15 15 t ∧
      t.pc=(if guardedCredit R C (lowerPathSave 3 (index/2^0))<R then pcOf 46972 else pcOf 46970) ∧
      t.getReg .x6=BitVec.ofNat 64 (guardedCredit R C (lowerPathSave 3 (index/2^0))) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let u := pre2.res.toState s
  have su : Steps im s 3 3 u := symRun_sound pre2 hc.pre s hp (by simp [pre2.res,rv_simp])
  have pu : u.pc=pcOf 88084 := rfl
  have u28 : u.getReg .x28=0x66000#64 := rfl
  have u21 : u.getReg .x21=BitVec.ofNat 64 R := by simpa [u,pre2.res,rv_simp] using h21
  have um : u.getMem 417872#64=BitVec.ofNat 64 C := by simpa [u,pre2.res,rv_simp] using hm
  have ui : u.getMem 0x20550#64=BitVec.ofNat 64 index := by simpa [u,pre2.res,rv_simp] using hindex
  have ru : RegsExcept s u [.x28] := by intro r hr;cases r <;> simp at hr <;> rfl
  have fu : Frame s u (fun _=>False) := by intro A ha hn;rfl
  obtain ⟨v,sv,pv,v6,rv,fv⟩ := LocalRouteMachineHelpers.expand3_steps hc.helper u pu index C R
    hi hC (by omega) u28 u21 um ui
  let t := test2.res.toState v
  have st : Steps im v 1 1 t := symRun_sound test2 hc.test v pv (by simp [test2.res,rv_simp])
  have rt : RegsExcept v t [] := by intro r hr;cases r <;> rfl
  have ft : Frame v t (fun _=>False) := by intro A ha hn;rfl
  have ht6 : t.getReg .x6=BitVec.ofNat 64 (guardedCredit R C (lowerPathSave 3 (index/2^0))) := by
    rw [rt .x6 (by decide)];exact v6
  refine ⟨t,(su.trans sv).trans st,?_,ht6,((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
  have v21 : v.getReg .x21=BitVec.ofNat 64 R := (rv .x21 (by decide)).trans u21
  have hcG : guardedCredit R C (lowerPathSave 3 (index/2^0))<2^64 :=
    guardedCredit_lt R C _ _ (by omega) hC (lowerPathSave_le_one _ _)
  simp only [t,Result.toState_pc,test2.res,rv_simp,v21,v6]
  simp only [BitVec.ult_eq_decide,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hcG,
    Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
  all_goals split_ifs <;> rfl
#print axioms first2_steps
theorem residual0_steps {im : Image} (hc : Code0 im)
    (s : MachineState) (hp : s.pc=pcOf 46933) (index R C : Nat)
    (hi : index<2^64) (hR : R≤74) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417856#64=BitVec.ofNat 64 C)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t n, n≤18 ∧ Steps im s n n t ∧ t.pc=pcOf 46940 ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C-lowerPathSave 1 (index/2^12)) ∧
      RegsExcept s t [.x6,.x7,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  let G := guardedCredit R C (lowerPathSave 1 (index/2^12))
  obtain ⟨u,su,pu,u6,ru,fu⟩ := first0_steps hc s hp index R C hi hR hC h21 hm hindex
  have u21 : u.getReg .x21=BitVec.ofNat 64 R := (ru .x21 (by decide)).trans h21
  have hg : R-G=R-C-lowerPathSave 1 (index/2^12) := residual_guardedCredit _ _ _
  change u.pc=(if G<R then pcOf 46939 else pcOf 46937) at pu
  by_cases h : G<R
  · rw [if_pos h] at pu
    let t := sub0.res.toState u
    have st : Steps im u 1 1 t := symRun_sound sub0 hc.sub u pu (by simp [sub0.res,rv_simp])
    have t21 : t.getReg .x21=BitVec.ofNat 64 (R-G) := by
      simp only [t,sub0.res,rv_simp,u21,u6]
      exact BitVec.ofNat_sub_ofNat_of_le R G (by omega) (by omega)
    have rt : RegsExcept u t [.x21] := by intro r hr;cases r <;> simp at hr <;> rfl
    have ft : Frame u t (fun _=>False) := by intro A ha hn;rfl
    refine ⟨t,16+1,by omega,su.trans st,rfl,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    simpa only [hg] using t21
  · rw [if_neg h] at pu
    let t := zero0.res.toState u
    have st : Steps im u 2 2 t := symRun_sound zero0 hc.zero u pu (by simp [zero0.res,rv_simp])
    have rt : RegsExcept u t [.x21] := by intro r hr;cases r <;> simp at hr <;> rfl
    have ft : Frame u t (fun _=>False) := by intro A ha hn;rfl
    refine ⟨t,16+2,by omega,su.trans st,rfl,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    have hz : R-G=0 := by omega
    rw [←hg,hz]
    rfl
#print axioms residual0_steps
theorem residual1_steps {im : Image} (hc : Code1 im)
    (s : MachineState) (hp : s.pc=pcOf 46949) (index R C : Nat)
    (hi : index<2^64) (hR : R≤74) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417864#64=BitVec.ofNat 64 C)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t n, n≤18 ∧ Steps im s n n t ∧ t.pc=pcOf 46956 ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C-lowerPathSave 2 (index/2^6)) ∧
      RegsExcept s t [.x6,.x7,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  let G := guardedCredit R C (lowerPathSave 2 (index/2^6))
  obtain ⟨u,su,pu,u6,ru,fu⟩ := first1_steps hc s hp index R C hi hR hC h21 hm hindex
  have u21 : u.getReg .x21=BitVec.ofNat 64 R := (ru .x21 (by decide)).trans h21
  have hg : R-G=R-C-lowerPathSave 2 (index/2^6) := residual_guardedCredit _ _ _
  change u.pc=(if G<R then pcOf 46955 else pcOf 46953) at pu
  by_cases h : G<R
  · rw [if_pos h] at pu
    let t := sub1.res.toState u
    have st : Steps im u 1 1 t := symRun_sound sub1 hc.sub u pu (by simp [sub1.res,rv_simp])
    have t21 : t.getReg .x21=BitVec.ofNat 64 (R-G) := by
      simp only [t,sub1.res,rv_simp,u21,u6]
      exact BitVec.ofNat_sub_ofNat_of_le R G (by omega) (by omega)
    have rt : RegsExcept u t [.x21] := by intro r hr;cases r <;> simp at hr <;> rfl
    have ft : Frame u t (fun _=>False) := by intro A ha hn;rfl
    refine ⟨t,16+1,by omega,su.trans st,rfl,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    simpa only [hg] using t21
  · rw [if_neg h] at pu
    let t := zero1.res.toState u
    have st : Steps im u 2 2 t := symRun_sound zero1 hc.zero u pu (by simp [zero1.res,rv_simp])
    have rt : RegsExcept u t [.x21] := by intro r hr;cases r <;> simp at hr <;> rfl
    have ft : Frame u t (fun _=>False) := by intro A ha hn;rfl
    refine ⟨t,16+2,by omega,su.trans st,rfl,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    have hz : R-G=0 := by omega
    rw [←hg,hz]
    rfl
#print axioms residual1_steps
theorem residual2_steps {im : Image} (hc : Code2 im)
    (s : MachineState) (hp : s.pc=pcOf 46966) (index R C : Nat)
    (hi : index<2^64) (hR : R≤74) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417872#64=BitVec.ofNat 64 C)
    (hindex : s.getMem 0x20550#64=BitVec.ofNat 64 index) :
    ∃ t n, n≤17 ∧ Steps im s n n t ∧ t.pc=pcOf 46973 ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C-lowerPathSave 3 (index/2^0)) ∧
      RegsExcept s t [.x6,.x7,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  let G := guardedCredit R C (lowerPathSave 3 (index/2^0))
  obtain ⟨u,su,pu,u6,ru,fu⟩ := first2_steps hc s hp index R C hi hR hC h21 hm hindex
  have u21 : u.getReg .x21=BitVec.ofNat 64 R := (ru .x21 (by decide)).trans h21
  have hg : R-G=R-C-lowerPathSave 3 (index/2^0) := residual_guardedCredit _ _ _
  change u.pc=(if G<R then pcOf 46972 else pcOf 46970) at pu
  by_cases h : G<R
  · rw [if_pos h] at pu
    let t := sub2.res.toState u
    have st : Steps im u 1 1 t := symRun_sound sub2 hc.sub u pu (by simp [sub2.res,rv_simp])
    have t21 : t.getReg .x21=BitVec.ofNat 64 (R-G) := by
      simp only [t,sub2.res,rv_simp,u21,u6]
      exact BitVec.ofNat_sub_ofNat_of_le R G (by omega) (by omega)
    have rt : RegsExcept u t [.x21] := by intro r hr;cases r <;> simp at hr <;> rfl
    have ft : Frame u t (fun _=>False) := by intro A ha hn;rfl
    refine ⟨t,15+1,by omega,su.trans st,rfl,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    simpa only [hg] using t21
  · rw [if_neg h] at pu
    let t := zero2.res.toState u
    have st : Steps im u 2 2 t := symRun_sound zero2 hc.zero u pu (by simp [zero2.res,rv_simp])
    have rt : RegsExcept u t [.x21] := by intro r hr;cases r <;> simp at hr <;> rfl
    have ft : Frame u t (fun _=>False) := by intro A ha hn;rfl
    refine ⟨t,15+2,by omega,su.trans st,rfl,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    have hz : R-G=0 := by omega
    rw [←hg,hz]
    rfl
#print axioms residual2_steps
end LocalRouteResiduals
