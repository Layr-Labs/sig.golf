import SigGolfCandidate.OuterSignTrip
import SigGolfCandidate.OuterSignCanonical
import SigGolfCandidate.OuterSignPlain
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignPlainFinish
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.FtsGrind OuterSignStubBlocks OuterSignInterface

theorem canonical_call {s t : MachineState} {A D : Nat} {r : Nat×HashOutput}
    (h : OuterSignExit.Out s A D r t)
    (hz32 : s.getMem (BitVec.ofNat 64 (A+32))=0) (hz40 : s.getMem (BitVec.ofNat 64 (A+40))=0) :
    OuterSignPlain.Out s D r.2 t := by
  refine ⟨h.at_pc,h.regs,h.output,?_⟩
  intro X hX hn
  by_cases h32 : X=A+32
  · subst X;exact h.pad32.trans hz32.symm
  by_cases h40 : X=A+40
  · subst X;exact h.pad40.trans hz40.symm
  exact h.frame.get hX (by unfold OuterNodeSearchInvariant.Work;omega)

theorem finish {sk : BitVec 256} {tb ret heap A D : Nat} {pre mid right : List UInt8} {s u v : MachineState}
    {r : Nat×HashOutput} (hT : CodeAt OuterImages.signImage (pcOf tb) (trampWords tb SIGN_S16 ret))
    (F : SignIn tb ret heap A D pre mid right s) (hD : 2048≤D)
    (hng : ¬(8≤heap ∧ heap<16)) (ho : OuterSignPlain.Out u D r.2 v)
    (hr : RegsExcept s u [.x16,.x17]) (h16 : u.getReg .x16=pcOf (tb+2))
    (sv0 : u.getMem (BitVec.ofNat 64 1104)=s.getReg .x14)
    (sv1 : u.getMem (BitVec.ofNat 64 1112)=s.getReg .x17)
    (sv4 : u.getMem (BitVec.ofNat 64 1136)=s.getReg .x16)
    (hf : Frame s u (fun X=>X=1104 ∨ X=1112 ∨ X=1136)) :
    TBSim OuterImages.signImage sk v 9 (pure r) (OuterSignInterface.Out s ret heap D (2-signR tb)) := by
  have hb:=F.hb;have hret:=F.hret;have hD2:=F.hD2
  have g : ∀ x,x≠.x16→x≠.x17→u.getReg x=s.getReg x := fun x h1 h2=>hr.get (by simp [h1,h2])
  obtain ⟨w1,s1,p1,r1,f1⟩:=q_spec v ho.at_pc
  obtain ⟨w2,s2,p2,x14,x17,r2,m04,m12,f2⟩:=r_spec w1 p1 (tb+2)
    (by rw [r1.get (by simp),ho.regs.get (by simp)];exact h16)
  obtain ⟨w3,s3,p3,x16,r3,m36,f3⟩:=tramp_tail hT hb hret w2 p2
  have mm : ∀ X,X<2^64→X≠1104→X≠1112→X≠1136→w3.getMem (BitVec.ofNat 64 X)=v.getMem (BitVec.ofNat 64 X) := by
    intro X hX a1 a2 a3
    rw [f3.get hX a3,f2.get hX (by rintro (h|h) <;> contradiction),f1.get hX (fun h=>h)]
  have w1m : ∀ X,X<2^64→w1.getMem (BitVec.ofNat 64 X)=v.getMem (BitVec.ofNat 64 X) := fun X hX=>f1.get hX (fun h=>h)
  refine tb_pure_steps (s1.trans (s2.trans s3)) ⟨p3,?_,?_,?_,?_,m36,fun h=>absurd h hng,fun _=>?_,?_⟩
  · intro x _
    by_cases hx16 : x=.x16
    · subst x
      rw [x16,f2.get (by decide) (by omega),w1m _ (by decide),ho.frame.get (by decide) (by omega),sv4]
    rw [r3.get (by simpa using hx16)]
    by_cases hx14 : x=.x14
    · subst x;rw [x14,w1m _ (by decide),ho.frame.get (by decide) (by omega),sv0]
    by_cases hx17 : x=.x17
    · subst x;rw [x17,w1m _ (by decide),ho.frame.get (by decide) (by omega),sv1]
    rw [r2.get (by simp [hx14,hx17]),r1.get (by simp),ho.regs.get (by simp),g _ hx16 hx17]
  · intro k hk
    rw [mm _ (by omega) (by omega) (by omega) (by omega),ho.output k hk]
  · change w3.getMem (BitVec.ofNat 64 1104)=0
    rw [f3.get (by decide) (by decide)];exact m04
  · change w3.getMem (BitVec.ofNat 64 1112)=0
    rw [f3.get (by decide) (by decide)];exact m12
  · change w3.getMem (BitVec.ofNat 64 1128)=s.getMem (BitVec.ofNat 64 1128)
    rw [mm _ (by decide) (by decide) (by decide) (by decide),ho.frame.get (by decide) (by omega),hf.get (by decide) (by decide)]
  · exact ((((hf.trans ho.frame).trans f1).trans f2).trans f3).mono (by
      intro X hX hw
      simp only [Writes,SignW] at hw ⊢
      tauto)
#print axioms canonical_call
#print axioms finish
end OuterSignPlainFinish
