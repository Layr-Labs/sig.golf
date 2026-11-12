import SigGolfCandidate.OuterSignE8Ground
import SigGolfCandidate.OuterSignInterface
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignE8
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.FtsGrind OuterSignStubBlocks OuterSignInterface
variable {sk : BitVec 256} {tb ret heap A D : Nat} {pre mid right : List UInt8} {s : MachineState}
  (hT : CodeAt OuterImages.signImage (pcOf tb) (trampWords tb SIGN_S16 ret))
  (F : SignIn tb ret heap A D pre mid right s)
  (P : M (Nat×HashOutput)) (W : Nat)
  (hplain : ∀ u,¬(8≤heap ∧ heap<16)→u.pc=pcOf 25338→
    RegsExcept s u [.x16,.x17]→u.getReg .x16=pcOf (tb+2)→
    u.getMem (BitVec.ofNat 64 1104)=s.getReg .x14→u.getMem (BitVec.ofNat 64 1112)=s.getReg .x17→u.getMem (BitVec.ofNat 64 1136)=s.getReg .x16→
    Frame s u (fun X=>X=1104 ∨ X=1112 ∨ X=1136)→
    TBSim OuterImages.signImage sk u W P (OuterSignInterface.Out s ret heap D (2-signR tb)))
include hT F P W hplain
theorem e8_run {v : MachineState} (hng16 : ¬ G16 (signSel tb) heap) (hpc : v.pc = pcOf 25310)
    (r01 : RegsExcept s v [.x16, .x17]) (x16' : v.getReg .x16 = pcOf (tb + 2))
    (sv0' : v.getMem (BitVec.ofNat 64 1104) = s.getReg .x14) (sv1' : v.getMem (BitVec.ofNat 64 1112) = s.getReg .x17)
    (sv4' : v.getMem (BitVec.ofNat 64 1136) = s.getReg .x16)
    (f01 : Frame s v (fun X => X = 1104 ∨ X = 1112 ∨ X = 1136)) :
    TBSim OuterImages.signImage sk v (if 8 ≤ heap ∧ heap < 16 then 18 * FUEL (2 - signR tb) + 36+W else 21+W)
      (program (2 - signR tb) heap (signSel tb) pre right P) (OuterSignInterface.Out s ret heap D (2 - signR tb)) := by
  have hA1 := F.hA1
  have h18 : v.getReg .x18 = BitVec.ofNat 64 heap := by rw [r01.get (by decide)]; exact F.x18
  obtain ⟨u1, s1, p1, r1, f1⟩ := e1_spec v hpc heap h18 F.hheap
  have fm1 : ∀ X, X < 2 ^ 64 → u1.getMem (BitVec.ofNat 64 X) = v.getMem (BitVec.ofNat 64 X) :=
    fun X hX => f1.get hX (fun h => h)
  have r01b : RegsExcept s u1 [.x16, .x17] := (r01.trans r1).mono (by decide)
  have f01b : Frame s u1 (fun X => X = 1104 ∨ X = 1112 ∨ X = 1136) :=
    (f01.trans f1).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
  have x16b : u1.getReg .x16 = pcOf (tb + 2) := by rw [r1.get (by decide)]; exact x16'
  have sv0b : u1.getMem (BitVec.ofNat 64 1104) = s.getReg .x14 := by rw [fm1 _ (by decide)]; exact sv0'
  have sv1b : u1.getMem (BitVec.ofNat 64 1112) = s.getReg .x17 := by rw [fm1 _ (by decide)]; exact sv1'
  have sv4b : u1.getMem (BitVec.ofNat 64 1136) = s.getReg .x16 := by rw [fm1 _ (by decide)]; exact sv4'
  by_cases h8 : heap < 8
  · rw [if_pos h8] at p1
    have hng : ¬ (8 ≤ heap ∧ heap < 16) := by omega
    unfold program; rw [if_neg hng, if_neg hng16, if_neg hng]
    exact (TBSim.steps s1 (hplain _ hng p1 r01b x16b sv0b sv1b sv4b f01b)).mono
      (by omega) (fun _ _ h => h)
  rw [if_neg h8] at p1
  have h18b : u1.getReg .x18 = BitVec.ofNat 64 heap := by rw [r01b.get (by decide)]; exact F.x18
  obtain ⟨u2, s2, p2, r2, f2⟩ := e2_spec u1 p1 heap h18b F.hheap
  have r02 : RegsExcept s u2 [.x16, .x17] := (r01b.trans r2).mono (by decide)
  have fm : ∀ X, X < 2 ^ 64 → u2.getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) :=
    fun X hX => f2.get hX (fun h => h)
  by_cases h16 : 16 ≤ heap
  · rw [if_pos h16] at p2
    have hng : ¬ (8 ≤ heap ∧ heap < 16) := by omega
    unfold program; rw [if_neg hng, if_neg hng16, if_neg hng]
    refine (TBSim.steps s1 (TBSim.steps s2 (hplain _ hng p2 r02
      (by rw [r2.get (by decide)]; exact x16b) (by rw [fm _ (by decide)]; exact sv0b)
      (by rw [fm _ (by decide)]; exact sv1b) (by rw [fm _ (by decide)]; exact sv4b)
      ((f01b.trans f2).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))))).mono
      (by omega) (fun _ _ h => h)
  rw [if_neg h16] at p2
  have hg : 8 ≤ heap ∧ heap < 16 := by omega
  obtain ⟨u3, s3, p3, x31, x17, r3, m28, f3⟩ := g_spec u2 p2 tb (by rw [r2.get (by decide)]; exact x16b)
    (by have := F.hb; omega)
  have fm3 : ∀ X, X < 2 ^ 64 → X ≠ 1128 → u3.getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) :=
    fun X hX h => (f3.get hX h).trans (fm X hX)
  have hu3 : AtG s tb A D 25319 0 u3 :=
    { pc := p3
      regs := (r02.trans r3).mono (by decide)
      x16 := by rw [r3.get (by decide), r2.get (by decide)]; exact x16b
      x17 := x17
      x31 := x31
      sv0 := by rw [fm3 _ (by decide) (by decide)]; exact sv0b
      sv1 := by rw [fm3 _ (by decide) (by decide)]; exact sv1b
      sv3 := by rw [m28, r02.get (by decide)]
      sv4 := by rw [fm3 _ (by decide) (by decide)]; exact sv4b
      frame := ((f01b.trans f2).trans f3).mono (fun X _ h => by
        unfold GW SignW
        rcases h with (h | h) | h
        · rcases h with h | h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
        · exact h.elim
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      hn := Nat.zero_le _ }
  unfold program groundFold; rw [if_pos hg, if_pos hg]
  exact (TBSim.steps s1 (TBSim.steps s2 (TBSim.steps s3
    ((OuterSignE8Ground.gloop hT F hg (FUEL (2 - signR tb)) 0 u3 hu3 (by omega)).mono le_rfl (fun _ _ h=>OuterSignInterface.Out.of_old h))))).mono (by omega) (fun _ _ h => h)

#print axioms e8_run
end OuterSignE8
