import SigGolfCandidate.OuterInstalledPool
import SigGolfCandidate.OuterPolicyCondition
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterValidate
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.WCT9 SigGolfCandidate.Research
open ClaudeWCT.W9.Machine.Expand.SharedValidateV6

theorem init_steps {im : Image} (hc : CodeAt im (pcOf 46929) initCode)
    (hg : CodeAt im (pcOf 54324) OuterRoutePool.expandIndexCode)
    (s : MachineState) (hp : s.pc=pcOf 46929) (index H : Nat) (hi : index<2^31)
    (hmidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 H) :
    ∃t,Steps im s 15 15 t ∧ t.pc=pcOf 46933 ∧ t.getReg .x20=BitVec.ofNat 64 H ∧
      t.getReg .x21=BitVec.ofNat 64 (OuterSigning.requiredCredit index) ∧
      RegsExcept s t [.x20,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,ru,fu⟩ := SigGolfCandidate.T3M.Search.T51.jump_hook (k:=46929) (t:=54324)
    (off:=29580) (fun _=>rfl) hc (by norm_num [pcOf]) (by norm_num [pcOf])
    (by norm_num [pcOf]) s hp
  obtain ⟨t,ut,pt,tpool,tH,rt,ft⟩ := OuterRoutePool.expandIndex_steps hg u pu index H hi
    ((fu.get (by decide) (by simp)).trans hmidx) ((fu.get (by decide) (by simp)).trans hm)
  refine ⟨t,su.trans ut,pt,tH,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
  have hr : (SigGolfCandidate.T3.route index 0).1=index/2^19 := by
    change index/2^19%2^12=index/2^19
    apply Nat.mod_eq_of_lt
    omega
  have he : OuterSigning.requiredCredit index =
      OuterSigning.rootPool (index/2^19) := by
    unfold OuterSigning.requiredCredit
    rw [hr]
  rw [he]
  exact tpool
structure Code (im : Image) : Prop where
  init : CodeAt im (pcOf 46929) initCode
  poolHelper : CodeAt im (pcOf 54324) OuterRoutePool.expandIndexCode
  r0 : LocalRouteResiduals.Code0 im
  r1 : LocalRouteResiduals.Code1 im
  r2 : LocalRouteResiduals.Code2 im
  range1 : CodeAt im (pcOf 46940) range1Code
  range2 : CodeAt im (pcOf 46956) range2Code
  range3 : CodeAt im (pcOf 46973) range3Code
  lookup1Pre : CodeAt im (pcOf 46942) lookup1PreCode
  lookup1Load : CodeAt im (pcOf 46945) lookup1LoadCode
  lookup1Post : CodeAt im (pcOf 46946) lookup1PostCode
  lookup2Pre : CodeAt im (pcOf 46958) lookup2PreCode
  lookup2Load : CodeAt im (pcOf 46961) lookup2LoadCode
  lookup2Post : CodeAt im (pcOf 46962) lookup2PostCode
  last : CodeAt im (pcOf 46975) lastCode
  l3e : CodeAt im (pcOf 87800) l3eCode
  l3Helper : CodeAt im (pcOf 88160) l3HelperCode
  l3Ok : CodeAt im (pcOf 87812) l3OkCode
  l3Bad : CodeAt im (pcOf 87813) l3BadCode
  good : CodeAt im (pcOf 46978) goodCode
  bad : CodeAt im (pcOf 46979) badCode

def regs : List Reg := [.x6,.x7,.x21,.x28,.x29]
theorem phase1_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46933) (index R C H : Nat) (hi : index<2^64) (hR : R≤75) (hC : C<2^64) (hH : H<12288)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hindex : s.getMem (0x20550#64)=BitVec.ofNat 64 index)
    (hm : s.getMem (417856#64)=BitVec.ofNat 64 C)
    (T : Nat→Nat) (hT : ∀ r,r<58 → T r<24)
    (hbytes : ∀ r,r<58 → s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (T r)) :
    ∃t n c,n≤27 ∧ c≤30 ∧ Steps im s n c t ∧
      t.pc=(if (R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1)<58 ∧ H/576=T ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1)) then pcOf 46949 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1)) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=LocalRouteResiduals.residual0_steps hc.r0 s hp index R C hi hR hC h21 hm hindex
  simp only [Nat.reducePow,Nat.div_one] at u21
  rw [← SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave_one_div] at u21
  obtain ⟨v,sv,pv,rv,fv⟩:=range1_steps hc.range1 u pu ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1)) (by omega) u21
  by_cases hlt : (R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1)<58
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=lookup1_steps hc.lookup1Pre hc.lookup1Load hc.lookup1Post v pv
      ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1)) H (T ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1))) hlt hH (hT _ hlt)
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
      (by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hbytes _ hlt)
    refine ⟨t,n+2+7,n+2+10,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt,eq_comm] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
theorem phase2_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46949) (index R C H : Nat) (hi : index<2^64) (hR : R≤75) (hC : C<2^64) (hH : H<12288)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hindex : s.getMem (0x20550#64)=BitVec.ofNat 64 index)
    (hm : s.getMem (417864#64)=BitVec.ofNat 64 C)
    (T : Nat→Nat) (hT : ∀ r,r<42 → T r<24)
    (hbytes : ∀ r,r<42 → s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (T r)) :
    ∃t n c,n≤28 ∧ c≤34 ∧ Steps im s n c t ∧
      t.pc=(if (R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2)<42 ∧ H/24%24=T ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2)) then pcOf 46966 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2)) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=LocalRouteResiduals.residual1_steps hc.r1 s hp index R C hi hR hC h21 hm hindex
  simp only [Nat.reducePow,Nat.div_one] at u21
  rw [← SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave_two_div] at u21
  obtain ⟨v,sv,pv,rv,fv⟩:=range2_steps hc.range2 u pu ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2)) (by omega) u21
  by_cases hlt : (R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2)<42
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=lookup2_steps hc.lookup2Pre hc.lookup2Load hc.lookup2Post v pv
      ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2)) H (T ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2))) hlt hH (hT _ hlt)
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
      (by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hbytes _ hlt)
    refine ⟨t,n+2+8,n+2+14,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt,eq_comm] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
theorem phase3_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46966) (index R C H : Nat) (hi : index<2^64) (hR : R≤75) (hC : C<2^64) (hH : H<12288)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hindex : s.getMem (0x20550#64)=BitVec.ofNat 64 index)
    (hm : s.getMem (417872#64)=BitVec.ofNat 64 C) :
    ∃t n c,n≤38 ∧ c≤54 ∧ Steps im s n c t ∧
      t.pc=(if (R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 3)<24 ∧ H%24=ClaudeWCT.WCT9.Policy75Safe23.lowerThreeFloor ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 3)) then pcOf 42795 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 3)) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=LocalRouteResiduals.residual2_steps hc.r2 s hp index R C hi hR hC h21 hm hindex
  simp only [Nat.reducePow,Nat.div_one] at u21
  rw [← SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave_three_div] at u21
  obtain ⟨v,sv,pv,rv,fv⟩:=range3_steps hc.range3 u pu ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 3)) (by omega) u21
  by_cases hlt : (R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 3)<24
  · rw [if_pos hlt] at pv
    obtain ⟨t,n3,c3,hn3,hc3,st,pt,rt,ft⟩:=last_steps hc.last hc.l3e hc.l3Helper hc.l3Ok hc.l3Bad v pv ((R-C-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 3)) H (by omega) hH
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
    refine ⟨t,n+2+n3,n+2+c3,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
abbrev Condition (index H C0 C1 C2 : Nat) (T1 T2 : Nat→Nat) : Prop :=
  let R1:=(OuterSigning.requiredCredit index)-C0-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1
  let R2:=R1-C1-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2
  let R3:=R2-C2-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 3
  R1<58 ∧ R2<42 ∧ R3<24 ∧ H/576=T1 R1 ∧ H/24%24=T2 R2 ∧ H%24=ClaudeWCT.WCT9.Policy75Safe23.lowerThreeFloor R3

theorem validate_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46929) (index : Nat) (hi : index<2^31)
    (hmidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) (H C0 C1 C2 : Nat)
    (hH : H<12288) (hC0 : C0<2^64) (hC1 : C1<2^64) (hC2 : C2<2^64)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 H)
    (hm0 : s.getMem (417856#64)=BitVec.ofNat 64 C0)
    (hm1 : s.getMem (417864#64)=BitVec.ofNat 64 C1)
    (hm2 : s.getMem (417872#64)=BitVec.ofNat 64 C2)
    (T1 T2 : Nat→Nat) (ht1 : ∀r,r<58→T1 r<24) (ht2 : ∀r,r<42→T2 r<24)
    (hb1 : ∀r,r<58→s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (T1 r))
    (hb2 : ∀r,r<42→s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (T2 r)) :
    ∃t n c,n≤109 ∧ c≤134 ∧ Steps im s n c t ∧
      t.pc=(if Condition index H C0 C1 C2 T1 T2 then pcOf 42795 else pcOf 354) ∧
      RegsExcept s t [.x6,.x7,.x20,.x21,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u20,u21,ru,fu⟩:=init_steps hc.init hc.poolHelper s hp index H hi hmidx hm
  have hpool := OuterSigning.requiredCredit_bounds index
  obtain ⟨v,n1,c1,hn1,hc1,sv,pv,v21,rv,fv⟩:=phase1_steps hc u pu index (OuterSigning.requiredCredit index) C0 H (by omega) (by omega) hC0 hH u21 u20
    (by rw [fu.get (by decide) (by simp)];exact hmidx)
    (by rw [fu.get (by decide) (by simp)];exact hm0) T1 ht1
    (fun r hr=>by rw [fu.getByte (by omega) (by simp)];exact hb1 r hr)
  by_cases h1 : (OuterSigning.requiredCredit index)-C0-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1<58 ∧ H/576=T1 ((OuterSigning.requiredCredit index)-C0-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1)
  · rw [if_pos h1] at pv
    obtain ⟨w,n2,c2,hn2,hc2,sw,pw,w21,rw_,fw⟩:=phase2_steps hc v pv index ((OuterSigning.requiredCredit index)-C0-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1) C1 H (by omega) (by omega) hC1 hH v21
      (by rw [rv.get (by decide)];exact u20)
      (by rw [fv.get (by decide) (by simp),fu.get (by decide) (by simp)];exact hmidx)
      (by rw [fv.get (by decide) (by simp),fu.get (by decide) (by simp)];exact hm1) T2 ht2
      (fun r hr=>by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hb2 r hr)
    by_cases h2 : (OuterSigning.requiredCredit index)-C0-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1-C1-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2<42 ∧ H/24%24=T2 ((OuterSigning.requiredCredit index)-C0-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1-C1-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2)
    · rw [if_pos h2] at pw
      obtain ⟨x,n3,c3,hn3,hc3,sx,px,x21,rx,fx⟩:=phase3_steps hc w pw index ((OuterSigning.requiredCredit index)-C0-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1-C1-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2) C2 H (by omega) (by omega) hC2 hH w21
        (by rw [rw_.get (by decide),rv.get (by decide)];exact u20)
        (by rw [fw.get (by decide) (by simp),fv.get (by decide) (by simp),fu.get (by decide) (by simp)];exact hmidx)
        (by rw [fw.get (by decide) (by simp),fv.get (by decide) (by simp),fu.get (by decide) (by simp)];exact hm2)
      by_cases h3 : (OuterSigning.requiredCredit index)-C0-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1-C1-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2-C2-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 3<24 ∧ H%24=ClaudeWCT.WCT9.Policy75Safe23.lowerThreeFloor ((OuterSigning.requiredCredit index)-C0-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1-C1-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2-C2-SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 3)
      · rw [if_pos h3] at px
        -- Y5: the L3 check at 87812 jumps to 42795 directly (word 46978 is not visited on success).
        refine ⟨x,15+n1+n2+n3,15+c1+c2+c3,by omega,by omega,((su.trans sv).trans sw).trans sx,?_,?_,?_⟩
        · have hcond : Condition index H C0 C1 C2 T1 T2 := by exact ⟨h1.1,h2.1,h3.1,h1.2,h2.2,h3.2⟩
          simpa only [if_pos hcond] using px
        · exact (((ru.trans rv).trans rw_).trans rx).mono (by decide)
        · exact (((fu.trans fv).trans fw).trans fx).mono (by simp)
      · rw [if_neg h3] at px
        obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad x px
        refine ⟨t,15+n1+n2+n3+1,15+c1+c2+c3+1,by omega,by omega,(((su.trans sv).trans sw).trans sx).trans st,?_,?_,?_⟩
        · have hcond : ¬Condition index H C0 C1 C2 T1 T2 := by intro h;exact h3 ⟨h.2.2.1,h.2.2.2.2.2⟩
          simpa [hcond] using pt
        · exact ((((ru.trans rv).trans rw_).trans rx).trans rt).mono (by decide)
        · exact ((((fu.trans fv).trans fw).trans fx).trans ft).mono (by simp)
    · rw [if_neg h2] at pw
      obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad w pw
      refine ⟨t,15+n1+n2+1,15+c1+c2+1,by omega,by omega,((su.trans sv).trans sw).trans st,?_,?_,?_⟩
      · have hcond : ¬Condition index H C0 C1 C2 T1 T2 := by intro h;exact h2 ⟨h.2.1,h.2.2.2.2.1⟩
        simpa [hcond] using pt
      · exact (((ru.trans rv).trans rw_).trans rt).mono (by decide)
      · exact (((fu.trans fv).trans fw).trans ft).mono (by simp)
  · rw [if_neg h1] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad v pv
    refine ⟨t,15+n1+1,15+c1+1,by omega,by omega,(su.trans sv).trans st,?_,?_,?_⟩
    · have hcond : ¬Condition index H C0 C1 C2 T1 T2 := by intro h;exact h1 ⟨h.1,h.2.2.2.1⟩
      simpa [hcond] using pt
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
theorem validate_source_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46929) (index : Nat) (hi : index<2^31)
    (hmidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool)
    (hH : hints.toNat<12288) (hlen : digits.length=4)
    (hfloor : ∀lay:SigGolfCandidate.T3.Layer, OuterSigning.hintFloor index hints lay≤
      CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val []))
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat)
    (hcredits : ∀lay:SigGolfCandidate.T3.Layer,s.getMem (BitVec.ofNat 64 (417856+8*lay.val))=
      BitVec.ofNat 64 (CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val [])))
    (ht1 : ∀r,r<58→ClaudeWCT.WCT9.Policy75Safe23.threshold 1 r<24)
    (ht2 : ∀r,r<42→ClaudeWCT.WCT9.Policy75Safe23.threshold 2 r<24)
    (hb1 : ∀r,r<58→s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (ClaudeWCT.WCT9.Policy75Safe23.threshold 1 r))
    (hb2 : ∀r,r<42→s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (ClaudeWCT.WCT9.Policy75Safe23.threshold 2 r)) :
    ∃t n c,n≤109 ∧ c≤134 ∧ Steps im s n c t ∧
      t.pc=(if OuterSigning.policyHintsValid index hints digits lows then pcOf 42795 else pcOf 354) ∧
      RegsExcept s t [.x6,.x7,.x20,.x21,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨t,n,c,hn,hc',st,pt,rt,ft⟩:=validate_steps hc s hp index hi hmidx hints.toNat
    (CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []))
    (CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 []))
    (CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 [])) hH (credit_lt _ _ _) (credit_lt _ _ _)
    (credit_lt _ _ _) hm
    (hcredits 0) (hcredits 1) (hcredits 2)
    (ClaudeWCT.WCT9.Policy75Safe23.threshold 1) (ClaudeWCT.WCT9.Policy75Safe23.threshold 2) ht1 ht2 hb1 hb2
  refine ⟨t,n,c,hn,hc',st,?_,rt,ft⟩
  have hh:=OuterPolicyCondition.policyCondition_iff index hints digits lows hH hlen (by simpa [OuterSigning.hintFloor,CanonicalPolicy.topFloor] using hfloor 0)
    (hfloor 1) (hfloor 2)
  change (Condition index hints.toNat (CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []))
    (CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 []))
    (CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 []))
    (ClaudeWCT.WCT9.Policy75Safe23.threshold 1) (ClaudeWCT.WCT9.Policy75Safe23.threshold 2) ↔ OuterSigning.policyHintsValid index hints digits lows=true) at hh
  simpa only [hh] using pt

#print axioms validate_source_steps
end OuterValidate
