import SigGolfCandidate.OuterSignTransfers
import SigGolfCandidate.Merge096
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignStubBlocks
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind
attribute [local rv_simp] Result.toState_getReg Result.toState_getMem Result.toState_pc
  Result.toState_code SymState.toState_getReg SymState.toState_getMem SymState.toState_pc
  RegFile.get E.eval BinOp.eval UnOp.eval CmpOp.eval LoadKind.fromWord StoreKind.merge
  Addr.eval memEval_cons memEval_nil BitVec.add_zero Oblig.all Oblig.holds Result.obligs
  Result.toState_getMem Result.pc Result.st Result.steps Result.cycles Result.stop

theorem code_gw (a b : Nat) (ha : SIGN_STUB≤a) (hb : b≤SIGN_STUB+32) (hab : a≤b)
    (hex : b≤25338 ∨ 25339≤a := by omega) : CodeAt OuterImages.signImage (pcOf a) (gw a b) := by
  apply OuterSignTransfers.code
  · have hlen : (gw a b).length≤b-a := List.length_take_le _ _
    unfold OuterSignTransfers.Clean
    simp only [SIGN_STUB] at ha hb
    omega
  · exact SigGolfCandidate.FtsGrind.code_gw ClaudeWCT.W9.Machine.Sign.SharedNode.installed_grind.stub a b ha hb hab

variable (s : MachineState)
theorem e1_spec (hpc : s.pc = pcOf 25310) (heap : Nat) (h18 : s.getReg .x18 = BitVec.ofNat 64 heap)
    (hh : heap < 2 ^ 64) :
    ∃ t, Steps OuterImages.signImage s 2 2 t ∧ t.pc = (if heap < 8 then pcOf 25338 else pcOf 25312) ∧ RegsExcept s t [.x17] ∧
      Frame s t (fun _ => False) := by
  have hc := code_gw 25310 25312 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sE1 hc s hpc (by simp [sE1.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sE1.res, rv_simp, h18]
    rw [show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ult_ofNat' _ _ hh (by decide)]
    by_cases h : heap < 8 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [sE1.res, rv_simp] <;> rfl
  · intro A _ _; simp [sE1.res, rv_simp]

theorem e2_spec (hpc : s.pc = pcOf 25312) (heap : Nat) (h18 : s.getReg .x18 = BitVec.ofNat 64 heap)
    (hh : heap < 2 ^ 64) :
    ∃ t, Steps OuterImages.signImage s 2 2 t ∧ t.pc = (if 16 ≤ heap then pcOf 25338 else pcOf 25314) ∧ RegsExcept s t [.x17] ∧
      Frame s t (fun _ => False) := by
  have hc := code_gw 25312 25314 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sE2 hc s hpc (by simp [sE2.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sE2.res, rv_simp, h18]
    rw [show (16#64 : Word) = BitVec.ofNat 64 16 from rfl, ult_ofNat' _ _ hh (by decide)]
    by_cases h : 16 ≤ heap
    · simp [h]
    · simp [show heap < 16 by omega, h]
  · intro r hr; simp at hr; cases r <;> simp_all [sE2.res, rv_simp] <;> rfl
  · intro A _ _; simp [sE2.res, rv_simp]

theorem g_spec (hpc : s.pc = pcOf 25314) (tb : Nat) (h16 : s.getReg .x16 = pcOf (tb + 2)) (htb : tb < 2 ^ 18) :
    ∃ t, Steps OuterImages.signImage s 5 5 t ∧ t.pc = pcOf 25319 ∧ t.getReg .x31 = BitVec.ofNat 64 (signR tb) ∧
      t.getReg .x17 = 0 ∧ RegsExcept s t [.x17, .x31] ∧ t.getMem (BitVec.ofNat 64 1128) = s.getReg .x31 ∧
      Frame s t (fun X => X = 1128) := by
  have hc := code_gw 25314 25319 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sG hc s hpc (by simp [sG.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sG.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, sG.res, rv_simp, h16]
    rw [show (105488#64 : Word) = BitVec.ofNat 64 105488 from rfl, ult_ofNat' _ _ (by omega) (by decide)]
    unfold signR SIGN_TRAMP
    by_cases h : tb + 2 < 25340 + 8
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  · simp only [Result.toState_getReg, sG.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [sG.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, sG.res]; t3n []
  · intro A hA hn; simp only [Result.toState_getMem, sG.res]; t3n []; rw [if_neg (by omega)]

theorem sg_sl_spec (hpc : s.pc = pcOf 25319) (A : Nat) (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A + 64 ≤ 2 ^ 24) :
    ∃ t, Steps OuterImages.signImage s 1 1 t ∧ t.pc = pcOf 25320 ∧ RegsExcept s t [] ∧
      t.getMem (BitVec.ofNat 64 (A + 32)) = s.getReg .x17 ∧ Frame s t (fun X => X = A + 32) ∧
      fetch OuterImages.signImage t = some (.base .ECALL) := by
  have hc := code_gw 25319 25321 (by decide) (by decide) (by decide)
  have hob : sL.res.obligs s := by simp only [sL.res]; t3n [h10]; omega
  refine ⟨_, symRun_sound sL hc s hpc hob, ?_, ?_, ?_, ?_, symRun_ecall sL hc s hob rfl⟩
  · simp [sL.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp [sL.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, sL.res]; t3n [h10]
  · intro X hX hn; simp only [Result.toState_getMem, sL.res]; t3n [h10]; rw [if_neg (by omega)]

theorem sc_spec (hpc : s.pc = pcOf 25321) (D : Nat) (h12 : s.getReg .x12 = BitVec.ofNat 64 D) (hD : D % 8 = 0)
    (hD' : D + 32 ≤ 2 ^ 24) (r : Nat) (h31 : s.getReg .x31 = BitVec.ofNat 64 r) (hr : r < 2) :
    ∃ t, Steps OuterImages.signImage s 4 4 t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 (D + 8))).toNat < 2 ^ (62 + r) then pcOf 25330 else pcOf 25325) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw 25321 25325 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sC hc s hpc (by simp only [sC.res]; t3n [h12]; omega), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sC.res, rv_simp, h12, ofNat_add_ofNat, beq_iff_eq]
    have e62 : ((62#64 : Word).toNat % 64) = 62 := rfl
    simp only [e62, h31]
    have hiff := shr_shr_eq_zero (s.getMem (BitVec.ofNat 64 (D + 8))) r (by omega)
    by_cases h1 : s.getMem (BitVec.ofNat 64 (D + 8)) >>> 62 >>> ((BitVec.ofNat 64 r).toNat % 64) = 0#64
    · rw [if_pos h1]; exact (if_pos (hiff.mp h1)).symm
    · rw [if_neg h1]; exact (if_neg (fun h => h1 (hiff.mpr h))).symm
  · intro r hr; simp at hr; cases r <;> simp_all [sC.res, rv_simp] <;> rfl
  · intro A _ _; simp [sC.res, rv_simp]

theorem sg_sn_spec (hpc : s.pc = pcOf 25325) (r : Nat) (h31 : s.getReg .x31 = BitVec.ofNat 64 r) (hr : r < 2) :
    ∃ t, Steps OuterImages.signImage s 3 3 t ∧
      t.pc = (if s.getReg .x17 = BitVec.ofNat 64 (511 / 2 ^ r) then pcOf 25330 else pcOf 25328) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw 25325 25328 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sN hc s hpc (by simp [sN.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sN.res, rv_simp, h31, beq_iff_eq]
    rw [show (511#64 : Word) = BitVec.ofNat 64 511 from rfl, ofNat_shr' 511 r]
    rw [show r % 2 ^ 64 % 64 = r by omega, show 511 % 2 ^ 64 = 511 from rfl]
  · intro r hr; simp at hr; cases r <;> simp_all [sN.res, rv_simp] <;> rfl
  · intro A _ _; simp [sN.res, rv_simp]

theorem sg_sj_spec (hpc : s.pc = pcOf 25328) :
    ∃ t, Steps OuterImages.signImage s 2 2 t ∧ t.pc = pcOf 25319 ∧ t.getReg .x17 = s.getReg .x17 + 1#64 ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw 25328 25330 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sJ hc s hpc (by simp [sJ.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [sJ.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, sJ.res]; simp [rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [sJ.res, rv_simp] <;> rfl
  · intro A _ _; simp [sJ.res, rv_simp]

/-- 25330..25337: clear the pad, restore `t6 a4 a7`, clear their saves, return through `a6`. -/
theorem d_spec (hpc : s.pc = pcOf 25330) (A R : Nat) (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA1 : 1144 ≤ A) (hA' : A + 64 ≤ 2 ^ 24) (h16 : s.getReg .x16 = pcOf R) :
    ∃ t, Steps OuterImages.signImage s 8 8 t ∧ t.pc = pcOf R ∧ t.getReg .x14 = s.getMem (BitVec.ofNat 64 1104) ∧
      t.getReg .x17 = s.getMem (BitVec.ofNat 64 1112) ∧ t.getReg .x31 = s.getMem (BitVec.ofNat 64 1128) ∧
      RegsExcept s t [.x14, .x17, .x31] ∧ t.getMem (BitVec.ofNat 64 (A + 32)) = 0 ∧
      t.getMem (BitVec.ofNat 64 1104) = 0 ∧ t.getMem (BitVec.ofNat 64 1112) = 0 ∧
      t.getMem (BitVec.ofNat 64 1128) = 0 ∧
      Frame s t (fun X => X = A + 32 ∨ X = 1104 ∨ X = 1112 ∨ X = 1128) := by
  have hc := code_gw 25330 25338 (by decide) (by decide) (by decide)
  have hob : sD.res.obligs s := by simp only [sD.res]; t3n [h10]; omega
  refine ⟨_, symRun_sound sD hc s hpc hob, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sD.res]; t3n [h16, pcOf_and_max]
  · simp only [Result.toState_getReg, sD.res]; t3n []
  · simp only [Result.toState_getReg, sD.res]; t3n []
  · simp only [Result.toState_getReg, sD.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [sD.res, rv_simp] <;> rfl
  all_goals try (simp only [Result.toState_getMem, sD.res]; t3n [h10]
                 try simp (disch := first | decide | omega) only [if_pos, if_neg, if_true, if_false]
                 done)
  · intro X hX hn; simp only [Result.toState_getMem, sD.res]; t3n [h10]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]

/-- 25339: `jal zero, 25333`. -/
theorem q_spec (hpc : s.pc = pcOf 25339) :
    ∃ t, Steps OuterImages.signImage s 1 1 t ∧ t.pc = pcOf 25333 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hc := code_gw 25339 25340 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sQ hc s hpc (by simp [sQ.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [sQ.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp [sQ.res, rv_simp] <;> rfl
  · intro A _ _; simp [sQ.res, rv_simp]

/-- 25333..25337: restore `a4 a7`, clear their saves, return through `a6`. -/
theorem r_spec (hpc : s.pc = pcOf 25333) (R : Nat) (h16 : s.getReg .x16 = pcOf R) :
    ∃ t, Steps OuterImages.signImage s 5 5 t ∧ t.pc = pcOf R ∧ t.getReg .x14 = s.getMem (BitVec.ofNat 64 1104) ∧
      t.getReg .x17 = s.getMem (BitVec.ofNat 64 1112) ∧ RegsExcept s t [.x14, .x17] ∧
      t.getMem (BitVec.ofNat 64 1104) = 0 ∧ t.getMem (BitVec.ofNat 64 1112) = 0 ∧
      Frame s t (fun X => X = 1104 ∨ X = 1112) := by
  have hc := code_gw 25333 25338 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound sR hc s hpc (by simp [sR.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sR.res]; t3n [h16, pcOf_and_max]
  · simp only [Result.toState_getReg, sR.res]; t3n []
  · simp only [Result.toState_getReg, sR.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [sR.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, sR.res]; t3n []
  · simp only [Result.toState_getMem, sR.res]; t3n []
  · intro X hX hn; simp only [Result.toState_getMem, sR.res]; t3n []; rw [if_neg (by omega), if_neg (by omega)]

#print axioms code_gw
#print axioms e1_spec
#print axioms d_spec
#print axioms q_spec
end OuterSignStubBlocks
