import SigGolfCandidate.Merge055
import SigGolfCandidate.LocalRouteMachineHelpers
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.all false
namespace LocalSignResidual
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.WCT9.CanonicalPolicy
def topPreCode : List (BitVec 32) := [0x66e37,0xe0e13,0x8e3303,0x3290306f]
sym_block topPre := symRun {noAlias:=true} topPreCode (pcOf 22230) 10
def topTestCode : List (BitVec 32) := [0x63e663]
sym_block topTest := symRun {noAlias:=true} topTestCode (pcOf 22234) 10
structure TopCode (im : Image) : Prop where
  pre : CodeAt im (pcOf 22230) topPreCode
  helper : CodeAt im (pcOf 26019) LocalRouteMachineHelpers.signTopCode
  test : CodeAt im (pcOf 22234) topTestCode

theorem readTop_steps {im : Image} (hc : TopCode im)
    (s : MachineState) (hp : s.pc=pcOf 22230) (index r c : Nat)
    (hi : index<2^64) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c)
    (hmidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 18 18 t ∧
      t.pc=(if guardedCredit r c (lowerPathSave 1 (index/4096))<r then pcOf 22237 else pcOf 22235) ∧
      t.getReg .x6=BitVec.ofNat 64 r ∧
      t.getReg .x7=BitVec.ofNat 64 (guardedCredit r c (lowerPathSave 1 (index/4096))) ∧
      t.getReg .x28=0x66000#64 ∧ RegsExcept s t [.x3,.x6,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let u := topPre.res.toState s
  have su : Steps im s 4 4 u := symRun_sound topPre hc.pre s hp (by simp [topPre.res,rv_simp])
  have pu : u.pc=pcOf 26019 := rfl
  have u6 : u.getReg .x6=BitVec.ofNat 64 r := by simpa [u,topPre.res,rv_simp] using hrm
  have u28 : u.getReg .x28=0x66000#64 := rfl
  have um : u.getMem (0x66018#64)=BitVec.ofNat 64 c := by simpa [u,topPre.res,rv_simp] using hcm
  have ui : u.getMem (0x20550#64)=BitVec.ofNat 64 index := by simpa [u,topPre.res,rv_simp] using hmidx
  have ru : RegsExcept s u [.x6,.x28] := by intro q hq;cases q <;> simp at hq <;> rfl
  have fu : Frame s u (fun _=>False) := by intro A ha hn;rfl
  obtain ⟨v,sv,pv,v7,v28,rv,fv⟩:=LocalRouteMachineHelpers.signTop_steps hc.helper u pu index c r hi (by omega) (by omega) u6 u28 um ui
  simp only [Nat.reducePow] at v7
  have v6 : v.getReg .x6=BitVec.ofNat 64 r := (rv.get (by decide)).trans u6
  let t:=topTest.res.toState v
  have st : Steps im v 1 1 t:=symRun_sound topTest hc.test v pv (by simp [topTest.res,rv_simp])
  have rt : RegsExcept v t [] := by intro q hq;cases q <;> rfl
  have ft : Frame v t (fun _=>False) := by intro A ha hn;rfl
  refine ⟨t,(su.trans sv).trans st,?_,(rt.get (by decide)).trans v6,(rt.get (by decide)).trans v7,
    (rt.get (by decide)).trans v28,((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
  have hg : guardedCredit r c (lowerPathSave 1 (index/4096))<2^64 :=
    guardedCredit_lt r c _ _ (by omega) (by omega) (lowerPathSave_le_one _ _)
  simp only [t,Result.toState_pc,topTest.res,rv_simp,v6,v7]
  simp only [BitVec.ult_eq_decide,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hg,
    Nat.mod_eq_of_lt (show r<2^64 by omega),decide_eq_true_eq]
  all_goals split_ifs <;> rfl
#print axioms readTop_steps

structure LowerHelpers (im : Image) : Prop where
  one : CodeAt im (pcOf 26032) LocalRouteMachineHelpers.dispatchOneCode
  two : CodeAt im (pcOf 26035) LocalRouteMachineHelpers.dispatchTwoCode
  last : CodeAt im (pcOf 26037) LocalRouteMachineHelpers.dispatchDefaultCode
  credit2 : CodeAt im (pcOf 26038) LocalRouteMachineHelpers.signTwoCode
  credit3 : CodeAt im (pcOf 26050) LocalRouteMachineHelpers.signThreeCode
theorem lowerCredit1_steps {im : Image} (hc : LowerHelpers im)
    (s : MachineState) (hp : s.pc=pcOf 26032) (index r c : Nat)
    (hi : index<2^64) (hr : r<2^64) (hc' : c<2^64)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h8 : s.getReg .x8=1)
    (h28 : s.getReg .x28=0x66000#64) (hm : s.getMem (0x66018#64)=BitVec.ofNat 64 c)
    (hindex : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 15 15 t ∧ t.pc=pcOf 22452 ∧
      t.getReg .x7=BitVec.ofNat 64 (guardedCredit r c (lowerPathSave 2 (index/64))) ∧
      t.getReg .x28=0x66000#64 ∧ RegsExcept s t [.x3,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u7,ru,fu⟩:=LocalRouteMachineHelpers.dispatchOne_steps hc.one s hp 1 c (by decide) h8 h28 hm
  have u6 : u.getReg .x6=BitVec.ofNat 64 r := (ru.get (by decide)).trans h6
  have ui : u.getMem (0x20550#64)=BitVec.ofNat 64 index := (fu.get (by decide) (by simp)).trans hindex
  obtain ⟨t,ut,pt,t7,t28,rt,ft⟩:=LocalRouteMachineHelpers.signTwo_steps hc.credit2 u (by simpa using pu) index c r hi hc' hr u6 u7 ui
  simp only [Nat.reducePow] at t7
  exact ⟨t,su.trans ut,pt,t7,t28,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
#print axioms lowerCredit1_steps
theorem lowerCredit2_steps {im : Image} (hc : LowerHelpers im)
    (s : MachineState) (hp : s.pc=pcOf 26032) (index r c : Nat)
    (hi : index<2^64) (hr : r<2^64) (hc' : c<2^64)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h8 : s.getReg .x8=2)
    (h28 : s.getReg .x28=0x66000#64) (hm : s.getMem (0x66018#64)=BitVec.ofNat 64 c)
    (hindex : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 16 16 t ∧ t.pc=pcOf 22452 ∧
      t.getReg .x7=BitVec.ofNat 64 (guardedCredit r c (lowerPathSave 3 index)) ∧
      t.getReg .x28=0x66000#64 ∧ RegsExcept s t [.x3,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u7,ru,fu⟩:=LocalRouteMachineHelpers.dispatchOne_steps hc.one s hp 2 c (by decide) h8 h28 hm
  have u6 : u.getReg .x6=BitVec.ofNat 64 r := (ru.get (by decide)).trans h6
  have ui : u.getMem (0x20550#64)=BitVec.ofNat 64 index := (fu.get (by decide) (by simp)).trans hindex
  have u8 : u.getReg .x8=2 := (ru.get (by decide)).trans h8
  obtain ⟨v,uv,pv,rv,fv⟩:=LocalRouteMachineHelpers.dispatchTwo_steps hc.two u (by simpa using pu) 2 (by decide) u8
  have v6 : v.getReg .x6=BitVec.ofNat 64 r := (rv.get (by decide)).trans u6
  have v7 : v.getReg .x7=BitVec.ofNat 64 c := (rv.get (by decide)).trans u7
  obtain ⟨t,vt,pt,t7,t28,rt,ft⟩:=LocalRouteMachineHelpers.signThree_steps hc.credit3 v (by simpa using pv) index c r hi hc' hr v6 v7
    ((fv.get (by decide) (by simp)).trans ui)
  simp only [Nat.reducePow,Nat.div_one] at t7
  exact ⟨t,(su.trans uv).trans vt,pt,t7,t28,((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
#print axioms lowerCredit2_steps
theorem lowerCredit3_steps {im : Image} (hc : LowerHelpers im)
    (s : MachineState) (hp : s.pc=pcOf 26032) (index r c : Nat)
    (hi : index<2^64) (hr : r<2^64) (hc' : c<2^64)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h8 : s.getReg .x8=3)
    (h28 : s.getReg .x28=0x66000#64) (hm : s.getMem (0x66018#64)=BitVec.ofNat 64 c)
    (hindex : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf 22452 ∧
      t.getReg .x7=BitVec.ofNat 64 (guardedCredit r c (0)) ∧
      t.getReg .x28=0x66000#64 ∧ RegsExcept s t [.x3,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u7,ru,fu⟩:=LocalRouteMachineHelpers.dispatchOne_steps hc.one s hp 3 c (by decide) h8 h28 hm
  have u6 : u.getReg .x6=BitVec.ofNat 64 r := (ru.get (by decide)).trans h6
  have ui : u.getMem (0x20550#64)=BitVec.ofNat 64 index := (fu.get (by decide) (by simp)).trans hindex
  have u8 : u.getReg .x8=3 := (ru.get (by decide)).trans h8
  obtain ⟨v,uv,pv,rv,fv⟩:=LocalRouteMachineHelpers.dispatchTwo_steps hc.two u (by simpa using pu) 3 (by decide) u8
  have v6 : v.getReg .x6=BitVec.ofNat 64 r := (rv.get (by decide)).trans u6
  have v7 : v.getReg .x7=BitVec.ofNat 64 c := (rv.get (by decide)).trans u7
  obtain ⟨t,vt,pt,rt,ft⟩:=LocalRouteMachineHelpers.dispatchDefault_steps hc.last v (by simpa using pv)
  refine ⟨t,(su.trans uv).trans vt,pt,?_,?_,((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
  · simpa [guardedCredit] using (rt.get (by decide)).trans v7
  · exact ((rt.get (by decide)).trans (rv.get (by decide))).trans ((ru.get (by decide)).trans h28)
#print axioms lowerCredit3_steps

def zero22230Code : List (BitVec 32) := bv_list% 32 [0x313,0x80006f]
sym_block zero22230 := symRun { noAlias := true } zero22230Code (pcOf 22235) 100
def sub22230Code : List (BitVec 32) := bv_list% 32 [0x40730333]
sym_block sub22230 := symRun { noAlias := true } sub22230Code (pcOf 22237) 100
def store22230Code : List (BitVec 32) := bv_list% 32 [0x6e3423]
sym_block store22230 := symRun { noAlias := true } store22230Code (pcOf 22238) 100
theorem zero22230_steps {im : Image} (hc : CodeAt im (pcOf 22235) zero22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22235) :
    ∃ t, Steps im s 2 2 t ∧ t.pc=pcOf 22238 ∧ t.getReg .x6=0 ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound zero22230 hc s hp (by simp [zero22230.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [zero22230.res,rv_simp]
  · simp [zero22230.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [zero22230.res,rv_simp]

theorem sub22230_steps {im : Image} (hc : CodeAt im (pcOf 22237) sub22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22237) (r c : Nat) (hr : r<2^32) (hc' : c≤r)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h7 : s.getReg .x7=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22238 ∧ t.getReg .x6=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound sub22230 hc s hp (by simp [sub22230.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [sub22230.res,rv_simp]
  · simp only [Result.toState_getReg,sub22230.res]; t3n [h6,h7]
    exact BitVec.ofNat_sub_ofNat_of_le r c (by omega) hc'
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [sub22230.res,rv_simp]

theorem store22230_steps {im : Image} (hc : CodeAt im (pcOf 22238) store22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22238) (v : BitVec 64)
    (h6 : s.getReg .x6=v) (h28 : s.getReg .x28=BitVec.ofNat 64 0x66000) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22239 ∧ t.getMem (0x66008#64)=v ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A=0x66008) := by
  refine ⟨_,symRun_sound store22230 hc s hp (by simp [store22230.res,rv_simp,h28]; decide),?_,?_,?_,?_⟩
  · simp [store22230.res,rv_simp]
  · simp [store22230.res,rv_simp,h6,h28]
  · intro q hq; cases q <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,store22230.res]; t3n [h28]
    rw [if_neg (by omega)]

structure TopFullCode (im : Image)  : Prop extends TopCode im where
  zero : CodeAt im (pcOf 22235) zero22230Code
  sub : CodeAt im (pcOf 22237) sub22230Code
  store : CodeAt im (pcOf 22238) store22230Code

theorem residualTop_steps {im : Image} (hc : TopFullCode im)
    (s : MachineState) (hp : s.pc=pcOf 22230) (index r c : Nat)
    (hi : index<2^64) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c)
    (hmidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t k, Steps im s k k t ∧ k≤21 ∧ t.pc=pcOf 22239 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c-lowerPathSave 1 (index/4096)) ∧
      RegsExcept s t [.x3,.x6,.x7,.x28] ∧ Frame s t (fun A=>A=0x66008) := by
  let G:=guardedCredit r c (lowerPathSave 1 (index/4096))
  obtain ⟨a,sa,ap,a6,a7,a28,ar,af⟩:=readTop_steps hc.toTopCode s hp index r c hi hr hc' hrm hcm hmidx
  by_cases hcr : G<r
  · obtain ⟨b,ab,bp,b6,br,bf⟩:=sub22230_steps hc.sub a (by simpa [G,hcr] using ap) r G hr (by omega) a6 a7
    obtain ⟨t,bt,tp,tv,tr,tf⟩:=store22230_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    refine ⟨t,20,sa.trans (ab.trans bt),by decide,tp,?_,((ar.trans br).trans tr).mono (by simp),((af.trans bf).trans tf).mono (by tauto)⟩
    simpa only [G,residual_guardedCredit] using tv
  · obtain ⟨b,ab,bp,b6,br,bf⟩:=zero22230_steps hc.zero a (by simpa [G,hcr] using ap)
    obtain ⟨t,bt,tp,tv,tr,tf⟩:=store22230_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    have hz : r-c-lowerPathSave 1 (index/4096)=0 := by
      rw [←residual_guardedCredit]; exact Nat.sub_eq_zero_of_le (by omega)
    exact ⟨t,21,sa.trans (ab.trans bt),by decide,tp,by simpa [hz] using tv,
      ((ar.trans br).trans tr).mono (by simp),((af.trans bf).trans tf).mono (by tauto)⟩
#print axioms residualTop_steps

def lowerSaved (index lay : Nat) := lowerPathSave (lay+1) (index/2^(if lay=1 then 6 else 0))
theorem lowerCredit_steps {im : Image} (hc : LowerHelpers im)
    (s : MachineState) (hp : s.pc=pcOf 26032) (index lay r c : Nat)
    (hi : index<2^64) (hl : 1≤lay ∧ lay≤3) (hr : r<2^64) (hc' : c<2^64)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (h28 : s.getReg .x28=0x66000#64) (hm : s.getMem (0x66018#64)=BitVec.ofNat 64 c)
    (hindex : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t n, n≤16 ∧ Steps im s n n t ∧ t.pc=pcOf 22452 ∧
      t.getReg .x7=BitVec.ofNat 64 (guardedCredit r c (lowerSaved index lay)) ∧
      t.getReg .x28=0x66000#64 ∧ RegsExcept s t [.x3,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  rcases hl with ⟨hlo,hhi⟩
  interval_cases lay
  · obtain ⟨t,st,pt,t7,t28,rt,ft⟩:=lowerCredit1_steps hc s hp index r c hi hr hc' h6 h8 h28 hm hindex
    refine ⟨t,15,by decide,st,pt,?_,t28,rt,ft⟩
    simpa [lowerSaved,lowerPathSave] using t7
  · obtain ⟨t,st,pt,t7,t28,rt,ft⟩:=lowerCredit2_steps hc s hp index r c hi hr hc' h6 h8 h28 hm hindex
    refine ⟨t,16,by decide,st,pt,?_,t28,rt,ft⟩
    simpa [lowerSaved,lowerPathSave] using t7
  · obtain ⟨t,st,pt,t7,t28,rt,ft⟩:=lowerCredit3_steps hc s hp index r c hi hr hc' h6 h8 h28 hm hindex
    refine ⟨t,6,by decide,st,pt,?_,t28,rt,ft⟩
    simpa [lowerSaved,lowerPathSave] using t7
def lowerPreCode : List (BitVec 32) := [0x66e37,0xe0e13,0x8e3303,0x7f40306f]
sym_block lowerPre := symRun {noAlias:=true} lowerPreCode (pcOf 22448) 10
def lowerTestCode : List (BitVec 32) := [0x63e663]
sym_block lowerTest := symRun {noAlias:=true} lowerTestCode (pcOf 22452) 10
structure LowerCode (im : Image) : Prop where
  pre : CodeAt im (pcOf 22448) lowerPreCode
  helpers : LowerHelpers im
  test : CodeAt im (pcOf 22452) lowerTestCode

theorem readLower_steps {im : Image} (hc : LowerCode im)
    (s : MachineState) (hp : s.pc=pcOf 22448) (index lay r c : Nat)
    (hi : index<2^64) (hl : 1≤lay ∧ lay≤3) (hr : r<2^32) (hc' : c<2^32)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c)
    (hmidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t n, n≤21 ∧ Steps im s n n t ∧
      t.pc=(if guardedCredit r c (lowerSaved index lay)<r then pcOf 22455 else pcOf 22453) ∧
      t.getReg .x6=BitVec.ofNat 64 r ∧
      t.getReg .x7=BitVec.ofNat 64 (guardedCredit r c (lowerSaved index lay)) ∧
      t.getReg .x28=0x66000#64 ∧ RegsExcept s t [.x3,.x6,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  let u:=lowerPre.res.toState s
  have su : Steps im s 4 4 u:=symRun_sound lowerPre hc.pre s hp (by simp [lowerPre.res,rv_simp])
  have pu : u.pc=pcOf 26032:=rfl
  have u6 : u.getReg .x6=BitVec.ofNat 64 r:=by simpa [u,lowerPre.res,rv_simp] using hrm
  have u8 : u.getReg .x8=BitVec.ofNat 64 lay:=by simpa [u,lowerPre.res,rv_simp] using h8
  have u28 : u.getReg .x28=0x66000#64:=rfl
  have um : u.getMem (0x66018#64)=BitVec.ofNat 64 c:=by simpa [u,lowerPre.res,rv_simp] using hcm
  have ui : u.getMem (0x20550#64)=BitVec.ofNat 64 index:=by simpa [u,lowerPre.res,rv_simp] using hmidx
  have ru : RegsExcept s u [.x6,.x28]:=by intro q hq;cases q <;> simp at hq <;> rfl
  have fu : Frame s u (fun _=>False):=by intro A ha hn;rfl
  obtain ⟨v,n,hn,sv,pv,v7,v28,rv,fv⟩:=lowerCredit_steps hc.helpers u pu index lay r c hi hl (by omega) (by omega) u6 u8 u28 um ui
  have v6 : v.getReg .x6=BitVec.ofNat 64 r:=(rv.get (by decide)).trans u6
  let t:=lowerTest.res.toState v
  have st : Steps im v 1 1 t:=symRun_sound lowerTest hc.test v pv (by simp [lowerTest.res,rv_simp])
  have rt : RegsExcept v t []:=by intro q hq;cases q <;> rfl
  have ft : Frame v t (fun _=>False):=by intro A ha hn;rfl
  refine ⟨t,4+n+1,by omega,(su.trans sv).trans st,?_,(rt.get (by decide)).trans v6,(rt.get (by decide)).trans v7,
    (rt.get (by decide)).trans v28,((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
  have hg : guardedCredit r c (lowerSaved index lay)<2^64:=
    guardedCredit_lt r c _ _ (by omega) (by omega) (lowerPathSave_le_one _ _)
  simp only [t,Result.toState_pc,lowerTest.res,rv_simp,v6,v7]
  simp only [BitVec.ult_eq_decide,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hg,
    Nat.mod_eq_of_lt (show r<2^64 by omega),decide_eq_true_eq]
  all_goals split_ifs <;> rfl
#print axioms readLower_steps
def zero22448Code : List (BitVec 32) := bv_list% 32 [0x313,0x80006f]
sym_block zero22448 := symRun { noAlias := true } zero22448Code (pcOf 22453) 100
def sub22448Code : List (BitVec 32) := bv_list% 32 [0x40730333]
sym_block sub22448 := symRun { noAlias := true } sub22448Code (pcOf 22455) 100
def store22448Code : List (BitVec 32) := bv_list% 32 [0x6e3423]
sym_block store22448 := symRun { noAlias := true } store22448Code (pcOf 22456) 100
theorem zero22448_steps {im : Image} (hc : CodeAt im (pcOf 22453) zero22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22453) :
    ∃ t, Steps im s 2 2 t ∧ t.pc=pcOf 22456 ∧ t.getReg .x6=0 ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound zero22448 hc s hp (by simp [zero22448.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [zero22448.res,rv_simp]
  · simp [zero22448.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [zero22448.res,rv_simp]

theorem sub22448_steps {im : Image} (hc : CodeAt im (pcOf 22455) sub22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22455) (r c : Nat) (hr : r<2^32) (hc' : c≤r)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h7 : s.getReg .x7=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22456 ∧ t.getReg .x6=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound sub22448 hc s hp (by simp [sub22448.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [sub22448.res,rv_simp]
  · simp only [Result.toState_getReg,sub22448.res]; t3n [h6,h7]
    exact BitVec.ofNat_sub_ofNat_of_le r c (by omega) hc'
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [sub22448.res,rv_simp]

theorem store22448_steps {im : Image} (hc : CodeAt im (pcOf 22456) store22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22456) (v : BitVec 64)
    (h6 : s.getReg .x6=v) (h28 : s.getReg .x28=BitVec.ofNat 64 0x66000) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22457 ∧ t.getMem (0x66008#64)=v ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A=0x66008) := by
  refine ⟨_,symRun_sound store22448 hc s hp (by simp [store22448.res,rv_simp,h28]; decide),?_,?_,?_,?_⟩
  · simp [store22448.res,rv_simp]
  · simp [store22448.res,rv_simp,h6,h28]
  · intro q hq; cases q <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,store22448.res]; t3n [h28]
    rw [if_neg (by omega)]

structure LowerFullCode (im : Image)  : Prop extends LowerCode im where
  zero : CodeAt im (pcOf 22453) zero22448Code
  sub : CodeAt im (pcOf 22455) sub22448Code
  store : CodeAt im (pcOf 22456) store22448Code

theorem residualLower_steps {im : Image} (hc : LowerFullCode im)
    (s : MachineState) (hp : s.pc=pcOf 22448) (index lay r c : Nat)
    (hi : index<2^64) (hl : 1≤lay ∧ lay≤3) (hr : r<2^32) (hc' : c<2^32)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c)
    (hmidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t k, Steps im s k k t ∧ k≤24 ∧ t.pc=pcOf 22457 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c-lowerSaved index lay) ∧
      RegsExcept s t [.x3,.x6,.x7,.x28] ∧ Frame s t (fun A=>A=0x66008) := by
  let G:=guardedCredit r c (lowerSaved index lay)
  obtain ⟨a,n,hn,sa,ap,a6,a7,a28,ar,af⟩:=readLower_steps hc.toLowerCode s hp index lay r c hi hl hr hc' h8 hrm hcm hmidx
  by_cases hcr : G<r
  · obtain ⟨b,ab,bp,b6,br,bf⟩:=sub22448_steps hc.sub a (by simpa [G,hcr] using ap) r G hr (by omega) a6 a7
    obtain ⟨t,bt,tp,tv,tr,tf⟩:=store22448_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    refine ⟨t,n+2,sa.trans (ab.trans bt),by omega,tp,?_,((ar.trans br).trans tr).mono (by simp),((af.trans bf).trans tf).mono (by tauto)⟩
    simpa only [G,residual_guardedCredit] using tv
  · obtain ⟨b,ab,bp,b6,br,bf⟩:=zero22448_steps hc.zero a (by simpa [G,hcr] using ap)
    obtain ⟨t,bt,tp,tv,tr,tf⟩:=store22448_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    have hz : r-c-lowerSaved index lay=0 := by
      rw [←residual_guardedCredit]; exact Nat.sub_eq_zero_of_le (by omega)
    exact ⟨t,n+3,sa.trans (ab.trans bt),by omega,tp,by simpa [hz] using tv,
      ((ar.trans br).trans tr).mono (by simp),((af.trans bf).trans tf).mono (by tauto)⟩

#print axioms residualLower_steps
end LocalSignResidual
