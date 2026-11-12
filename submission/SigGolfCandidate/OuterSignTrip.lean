import SigGolfCandidate.OuterSignE8
import SigGolfCandidate.OuterSignInterface
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignTrip
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.FtsGrind OuterSignStubBlocks OuterSignInterface
variable {sk : BitVec 256} {tb ret heap A D : Nat} {pre mid right : List UInt8} {s : MachineState}
  (hT : CodeAt OuterImages.signImage (pcOf tb) (trampWords tb SIGN_S16 ret))
  (hS16 : CodeAt OuterImages.signImage (pcOf SIGN_S16) signS16Words)
  (F : SignIn tb ret heap A D pre mid right s)
  (P : M (Nat×HashOutput)) (W : Nat)
  (hplain : ∀ u,¬(8≤heap ∧ heap<16)→u.pc=pcOf 25338→
    RegsExcept s u [.x16,.x17]→u.getReg .x16=pcOf (tb+2)→
    u.getMem (BitVec.ofNat 64 1104)=s.getReg .x14→u.getMem (BitVec.ofNat 64 1112)=s.getReg .x17→u.getMem (BitVec.ofNat 64 1136)=s.getReg .x16→
    Frame s u (fun X=>X=1104 ∨ X=1112 ∨ X=1136)→
    TBSim OuterImages.signImage sk u W P (OuterSignInterface.Out s ret heap D (2-signR tb)))
include hT hS16 F P W hplain
theorem sign_tramp_node :
    TBSim OuterImages.signImage sk s (signW (2 - signR tb) heap (signSel tb)+W) (program (2 - signR tb) heap (signSel tb) pre right P)
      (OuterSignInterface.Out s ret heap D (2 - signR tb)) := by
  have hA1 := F.hA1
  obtain ⟨u0, s0, p0, x16, r0, m0, f0⟩ := tramp_head hT F.hb (by decide) s F.pc
  have g0 : ∀ x, x ≠ .x16 → u0.getReg x = s.getReg x := fun x h => r0.get (by simp [h])
  obtain ⟨u1, s1, p1, r1, sv0, sv1, f1⟩ := q16_h0 hS16 u0 p0 heap (by rw [g0 _ (by decide)]; exact F.x18) F.hheap
  have f01 : Frame s u1 (fun X => X = 1104 ∨ X = 1112 ∨ X = 1136) := (f0.trans f1).mono (fun X _ h => by
    rcases h with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have r01 : RegsExcept s u1 [.x16, .x17] := (r0.trans r1).mono (by decide)
  have x16a : u1.getReg .x16 = pcOf (tb + 2) := by rw [r1.get (by decide)]; exact x16
  have sv0a : u1.getMem (BitVec.ofNat 64 1104) = s.getReg .x14 := by rw [sv0, g0 _ (by decide)]
  have sv1a : u1.getMem (BitVec.ofNat 64 1112) = s.getReg .x17 := by rw [sv1, g0 _ (by decide)]
  have sv4a : u1.getMem (BitVec.ofNat 64 1136) = s.getReg .x16 := by
    rw [f1.get (by decide) (by omega)]; exact m0
  by_cases h16 : heap < 16
  · rw [if_pos h16] at p1
    have hng16 : ¬ G16 (signSel tb) heap := by unfold G16; omega
    exact (TBSim.steps s0 (TBSim.steps s1 (OuterSignE8.e8_run hT F P W hplain hng16 p1 r01 x16a sv0a sv1a sv4a f01))).mono
      (by unfold signW; rw [if_neg hng16]; split_ifs <;> omega) (fun _ _ h => h)
  rw [if_neg h16] at p1
  have h18 : u1.getReg .x18 = BitVec.ofNat 64 heap := by rw [r01.get (by decide)]; exact F.x18
  obtain ⟨u2, s2, p2, r2, f2⟩ := q16_h1 hS16 u1 p1 heap h18 F.hheap
  have r02 : RegsExcept s u2 [.x16, .x17] := (r01.trans r2).mono (by decide)
  have fm2 : ∀ X, X < 2 ^ 64 → u2.getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) :=
    fun X hX => f2.get hX (fun h => h)
  have f02 : Frame s u2 (fun X => X = 1104 ∨ X = 1112 ∨ X = 1136) :=
    (f01.trans f2).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
  have x16b : u2.getReg .x16 = pcOf (tb + 2) := by rw [r2.get (by decide)]; exact x16a
  by_cases h32 : 32 ≤ heap
  · rw [if_pos h32] at p2
    have hng16 : ¬ G16 (signSel tb) heap := by unfold G16; omega
    exact (TBSim.steps s0 (TBSim.steps s1 (TBSim.steps s2 (OuterSignE8.e8_run hT F P W hplain hng16 p2 r02 x16b
      (by rw [fm2 _ (by decide)]; exact sv0a) (by rw [fm2 _ (by decide)]; exact sv1a)
      (by rw [fm2 _ (by decide)]; exact sv4a) f02)))).mono (by unfold signW; rw [if_neg hng16]; split_ifs <;> omega) (fun _ _ h => h)
  rw [if_neg h32] at p2
  obtain ⟨u3, s3, p3, r3, f3⟩ := q16_h2 hS16 u2 p2 tb x16b (by have := F.hb; omega)
  have r03 : RegsExcept s u3 [.x16, .x17] := (r02.trans r3).mono (by decide)
  have fm3 : ∀ X, X < 2 ^ 64 → u3.getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) :=
    fun X hX => (f3.get hX (fun h => h)).trans (fm2 X hX)
  have f03 : Frame s u3 (fun X => X = 1104 ∨ X = 1112 ∨ X = 1136) :=
    (f02.trans f3).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
  have x16c : u3.getReg .x16 = pcOf (tb + 2) := by rw [r3.get (by decide)]; exact x16b
  by_cases hsel : signSel tb = true
  · rw [if_pos hsel] at p3
    have hg : G16 (signSel tb) heap := ⟨hsel, by omega, by omega⟩
    obtain ⟨u4, s4, p4, x17, r4, f4⟩ := q16_l0 hS16 u3 p3
    have fm4 : ∀ X, X < 2 ^ 64 → u4.getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) :=
      fun X hX => (f4.get hX (fun h => h)).trans (fm3 X hX)
    have r04 : RegsExcept s u4 [.x16, .x17] := (r03.trans r4).mono (by decide)
    have hu4 : AtH s tb A D 25911 0 u4 :=
      { pc := p4
        regs := r04.mono (by decide)
        x16 := by rw [r4.get (by decide)]; exact x16c
        x17 := x17
        x31 := r04.get (by decide)
        sv0 := by rw [fm4 _ (by decide)]; exact sv0a
        sv1 := by rw [fm4 _ (by decide)]; exact sv1a
        sv3 := by rw [fm4 _ (by decide), f01.get (by decide) (by omega)]
        sv4 := by rw [fm4 _ (by decide)]; exact sv4a
        frame := ((f03.trans f4).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)).mono
          (fun X _ h => by
            unfold GW SignW
            rcases h with h | h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
        hn := Nat.zero_le _ }
    have hng : ¬ (8 ≤ heap ∧ heap < 16) := by omega
    unfold program signW groundFoldH; rw [if_neg hng, if_pos hg, if_neg hng, if_pos hg]
    exact (TBSim.steps s0 (TBSim.steps s1 (TBSim.steps s2 (TBSim.steps s3 (TBSim.steps s4
      ((gloop16 hS16 hT F hg (FUEL 1) 0 u4 hu4 (by decide)).mono le_rfl (fun _ _ h=>OuterSignInterface.Out.of_old h))))))).mono (by unfold FUEL; omega) (fun _ _ h => h)
  · rw [if_neg hsel] at p3
    have hng16 : ¬ G16 (signSel tb) heap := fun h => hsel h.1
    exact (TBSim.steps s0 (TBSim.steps s1 (TBSim.steps s2 (TBSim.steps s3 (OuterSignE8.e8_run hT F P W hplain hng16 p3 r03 x16c
      (by rw [fm3 _ (by decide)]; exact sv0a) (by rw [fm3 _ (by decide)]; exact sv1a)
      (by rw [fm3 _ (by decide)]; exact sv4a) f03))))).mono (by unfold signW; rw [if_neg hng16]; split_ifs <;> omega) (fun _ _ h => h)

#print axioms sign_tramp_node
end OuterSignTrip
