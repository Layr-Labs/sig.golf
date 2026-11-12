import SigGolfCandidate.OuterSignForestSource
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignForestGood
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify SigGolfCandidate.Research
open ClaudeWCT ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedCoordinate
variable {sk : BitVec 256}
def ForestPost (sk a : BitVec 256) (s0 : MachineState)
    (rv : SharedForest.ForestOpening × SharedForest.PairRoot) (t : MachineState) : Prop :=
  ∃ rows, rv=forestAssembly (SharedForest.forestSelectionFromOutput a) rows ∧ OuterSignForest.ForestInv sk a s0 9 rows t

theorem forest_good (hf:SharedReuse.Fetch OuterImages.signImage) (hcode:∀c,c < 9 → OuterSignCoordinateCode.Code c)
    (a : BitVec 256) (hranks:∀c,c < 9 → rank c a < 563)
    (s : MachineState) (hpc:s.pc=pcOf (cbase 0)) (hs:Ready sk a s) :
    TBSim OuterImages.signImage sk s (9*OuterSignForest.forestStepBound)
      (OuterForestMoment.forest (WCT9.digestIndex a) (SharedForest.forestSelectionFromOutput a)
        (SharedForest.forestWordsFromOutput a)) (ForestPost sk a s) := by
  rw [←OuterSignForestSource.forestProgram_output a,map_eq_bind_pure_comp]
  exact (TBSim.bind (W₂:=0)
    (OuterSignForest.forest_loop hf hcode a (SharedForest.forestRank a) (fun c hc=>forestRank_val a c (hranks c hc)) s hpc hs)
    (fun rows t ht=>TBSim.pure ⟨rows,rfl,ht⟩)).mono (by omega) (fun _ _ h=>h)

theorem ForestPost.roots {a : BitVec 256} {s0 t : MachineState}
    {rv : SharedForest.ForestOpening × SharedForest.PairRoot} (h:ForestPost sk a s0 rv t) :
    t.pc=pcOf 20715 ∧ Ready sk a t ∧
    DigAt t (FORW+forOff 8) rv.2.1 ∧ DigAt t (FORW+forOff 8+16) rv.2.2 := by
  obtain ⟨rows,rfl,h⟩:=h
  have hp:=h.prior (by decide)
  exact ⟨h.pc,h.ready,hp 0 (by decide),hp 1 (by decide)⟩

theorem ForestPost.values {sk a : BitVec 256} {s0 t : MachineState}
    {rv : SharedForest.ForestOpening × SharedForest.PairRoot} (h:ForestPost sk a s0 rv t)
    (c : Fin 9) (i : Fin 6) : DigAt t (slotV c.val i.val) (openingValues rv.1 c i) := by
  obtain ⟨rows,rfl,h⟩:=h
  rw [assembly_values]
  exact (h.signatures c.val c.isLt).values.2 i.val i.isLt

theorem ForestPost.path {sk a : BitVec 256} {s0 t : MachineState}
    {rv : SharedForest.ForestOpening × SharedForest.PairRoot} (h:ForestPost sk a s0 rv t)
    (c : Fin 9) (level : Nat) (hl:level < SharedPath.levels c.val) :
    DigAt t (SharedPath.target c.val level) (openingPath rv.1 c level) := by
  obtain ⟨rows,rfl,h⟩:=h
  rw [assembly_path _ _ c level hl,childFamily_output a c.val c.isLt]
  have h7:level < 7:=lt_of_lt_of_le hl (SharedPath.levels_bound c.val)
  unfold SharedForest.authAt
  rw [Nat.add_comm 128, pathIdx_eq _ (chosen_lt c.val a) level h7]
  exact (h.signatures c.val c.isLt).paths level hl

theorem ForestPost.dummy {sk a : BitVec 256} {s0 t : MachineState}
    {rv : SharedForest.ForestOpening × SharedForest.PairRoot} (h:ForestPost sk a s0 rv t)
    (c : Fin 9) (hc:SharedEnd.first c.val=true) : DigAt t (SharedEnd.target c.val) 0 := by
  obtain ⟨rows,rfl,h⟩:=h
  exact (h.signatures c.val c.isLt).dummy hc

structure ClosedPost (sk a : BitVec 256) (s0 : MachineState)
    (rv : SharedForest.ForestOpening×SharedForest.PairRoot) (t : MachineState) : Prop where
  pc : t.pc=pcOf 370
  x5 : t.getReg .x5=0
  rootLeft : DigAt t FOUT rv.2.1
  rootRight : DigAt t 0x20290 rv.2.2
  values : ∀c : Fin 9,∀i : Fin 6,DigAt t (slotV c.val i.val) (openingValues rv.1 c i)
  paths : ∀c : Fin 9,∀l,l<SharedPath.levels c.val → DigAt t (SharedPath.target c.val l) (openingPath rv.1 c l)
  dummy : ∀c : Fin 9,SharedEnd.first c.val=true → DigAt t (SharedEnd.target c.val) 0
  frame : Frame s0 t (fun A=>A=PRIVW+40 ∨ A=PRIVW+32 ∨ A=PRIVW+8 ∨ A=PRIVW ∨ OuterSignForest.forestW A ∨ FinalW A)

theorem forest_boundary_good {sk a : BitVec 256}
    (hf:SharedReuse.Fetch OuterImages.signImage) (hcode:∀c,c<9 → OuterSignCoordinateCode.Code c)
    (hfor:LookOK OuterImages.signImage SharedBoundary.forLook) (hranks:∀c,c<9 → rank c a<563)
    (s : MachineState) (hp:Entry sk a s) :
    TBSim OuterImages.signImage sk s (9*OuterSignForest.forestStepBound+23)
      (OuterForestMoment.forest (WCT9.digestIndex a) (SharedForest.forestSelectionFromOutput a)
        (SharedForest.forestWordsFromOutput a)) (ClosedPost sk a s) := by
  obtain ⟨u,su,pu,k1,k2,ru,fu⟩:=SharedBoundary.step_SK hf.head s hp.pc
  have gm : ∀A,A<2^64 → A≠PRIVW+40 → A≠PRIVW+32 → A≠PRIVW+8 → A≠PRIVW →
      u.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4;exact fu.get hA (by simp [h1,h2,h3,h4])
  have hu : Ready sk a u := by
    refine ⟨(ru.get (by decide)).trans hp.x5,(ru.get (by decide)).trans hp.x22,?_,?_,?_,?_,?_,?_,?_⟩
    · intro k hk;rw [gm _ (by ao) (by ao) (by ao) (by ao) (by ao)];exact hp.nbuf k hk
    · intro k hk;rw [gm _ (by ao) (by ao) (by ao) (by ao) (by ao)];exact hp.table k hk
    · simpa only [Nat.mul_zero,Nat.add_zero] using (k1 0 (by decide)).trans (hp.secret 0 (by decide))
    · simpa only [Nat.mul_one] using (k1 1 (by decide)).trans (hp.secret 1 (by decide))
    · simpa only [Nat.mul_zero,Nat.add_zero] using (k2 0 (by decide)).trans (hp.secret 2 (by decide))
    · exact (k2 1 (by decide)).trans (hp.secret 3 (by decide))
    · intro A hA
      rw [gm _ (by unfold ZeroCell ScrZero at hA;aoh) (by unfold ZeroCell ScrZero at hA;aoh)
        (by unfold ZeroCell ScrZero at hA;aoh) (by unfold ZeroCell ScrZero at hA;aoh) (by unfold ZeroCell ScrZero at hA;aoh)]
      exact hp.zero A hA
  rw [←bind_pure (OuterForestMoment.forest (WCT9.digestIndex a) (SharedForest.forestSelectionFromOutput a)
        (SharedForest.forestWordsFromOutput a))]
  refine (TBSim.steps su (TBSim.bind (W₂:=12) (forest_good hf hcode a hranks u pu hu) (fun rv v hv=>?_))).mono (by omega) (fun _ _ h=>h)
  obtain ⟨pv,ready,l,r⟩:=hv.roots
  obtain ⟨t,vt,pt,m0,m8,m16,m24,rt,ft⟩:=SharedBoundary.step_For hfor v pv
  have hslot : ∀A,28672≤A → A<32000 → ¬FinalW A := by simp only [FinalW,FOUT];omega
  refine TBSim.pure_steps' vt ⟨pt,(rt.get (by decide)).trans ready.x5,⟨m0.trans l.1,m8.trans l.2⟩,
    ⟨m16.trans r.1,by simpa [Nat.add_assoc] using m24.trans r.2⟩,?_,?_,?_,?_⟩
  · intro c i
    have hc:=c.isLt;have hi:=i.isLt
    exact (hv.values c i).frame ft (by unfold slotV SIG;omega)
      (hslot _ (by unfold slotV SIG;omega) (by unfold slotV SIG;omega))
      (hslot _ (by unfold slotV SIG;omega) (by unfold slotV SIG;omega))
  · intro c l hl
    have hc:=c.isLt;have hb:=SharedPath.levels_bound c.val
    exact (hv.path c l hl).frame ft (by unfold SharedPath.target slotV SIG;omega)
      (hslot _ (by unfold SharedPath.target slotV SIG;omega) (by unfold SharedPath.target slotV SIG;omega))
      (hslot _ (by unfold SharedPath.target slotV SIG;omega) (by unfold SharedPath.target slotV SIG;omega))
  · intro c hc
    have hcb:=c.isLt
    exact (hv.dummy c hc).frame ft (by unfold SharedEnd.target slotP SIG;omega)
      (hslot _ (by unfold SharedEnd.target slotP SIG;omega) (by unfold SharedEnd.target slotP SIG;omega))
      (hslot _ (by unfold SharedEnd.target slotP SIG;omega) (by unfold SharedEnd.target slotP SIG;omega))
  · obtain ⟨rows,he,hv⟩:=hv
    exact ((fu.trans hv.frame).trans ft).mono (by intro A hA h;rcases h with ((h|h)|h)|h <;> tauto)
#print axioms forest_good
#print axioms forest_boundary_good
end OuterSignForestGood
