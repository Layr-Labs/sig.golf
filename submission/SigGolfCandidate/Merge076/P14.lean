import SigGolfCandidate.ExpandLabel
import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge059
import SigGolfCandidate.Merge060
import SigGolfCandidate.Merge070
import SigGolfCandidate.Merge075
import SigGolfCandidate.Merge076.P1
import SigGolfCandidate.Merge076.P2
import SigGolfCandidate.Merge076.P4
import SigGolfCandidate.Merge076.P5
import SigGolfCandidate.Merge076.P6
import SigGolfCandidate.Merge076.P7
import SigGolfCandidate.Merge076.P9
import SigGolfCandidate.Merge076.P10
import SigGolfCandidate.Merge076.P11
import SigGolfCandidate.Merge076.P12
import SigGolfCandidate.Merge076.P13

set_option debug.skipKernelTC false
set_option linter.all false

-- ==== merged from T3M_Expand_LayerBlocks ====
section

section
namespace SigGolfCandidate.T3M.Expand.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
end SigGolfCandidate.T3M.Expand.BCBlocks
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
section blocks
variable (s : MachineState)
end blocks
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand.BCBlocks
class Code (im : Image) : Prop where
  hookCode_at : CodeAt im (pcOf 1117) hookCode
  testCode_at : CodeAt im (pcOf 40875) testCode
  branch1Code_at : CodeAt im (pcOf 40877) branch1Code
  branch2Code_at : CodeAt im (pcOf 40878) branch2Code
  pairCode_at : CodeAt im (pcOf 40879) pairCode
  backCode_at : CodeAt im (pcOf 40892) backCode
  selectCode_at : CodeAt im (pcOf 40875) selectCode
variable {im : Image} [Code im]
theorem pair_spec (s : MachineState) (hpc : s.pc = pcOf 40879) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 NODE) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (NODE + 8)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (NODE + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (NODE + 56)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  have hobl : Oblig.all s pairCodeBlock.res.st.obl := by
    simp [pairCodeBlock.res, rv_simp]
  refine ⟨_, symRun_sound pairCodeBlock (Code.pairCode_at (im := im)) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pairCodeBlock.res, rv_simp, h1, pcOf_and_max]
  · simp only [Result.toState_getMem, pairCodeBlock.res, ENC, NODE]
    t3n []
  · simp only [Result.toState_getMem, pairCodeBlock.res, ENC, NODE]
    t3n []
  · simp only [Result.toState_getMem, pairCodeBlock.res, ENC, NODE]
    t3n []
  · simp only [Result.toState_getMem, pairCodeBlock.res, ENC, NODE]
    t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pairCodeBlock.res, rv_simp]; rfl
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, pairCodeBlock.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem select_spec (s : MachineState) (hpc : s.pc = pcOf 40875) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if remaining s = 0 then pcOf 40878 else pcOf 40892) ∧
      t.getReg .x28 = remaining s ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound selectBlock (Code.selectCode_at (im := im)) s hpc (by simp [selectBlock.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, selectBlock.res, rv_simp, remaining, sub_eq_add_neg]
  · simp [Result.toState_getReg, selectBlock.res, rv_simp, remaining, sub_eq_add_neg]
  · intro r hr; simp at hr; cases r <;> simp_all [selectBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, selectBlock.res, rv_simp]

theorem layer_spec (s : MachineState) (hpc : s.pc = pcOf 40878) :
    ∃ t, Steps im s 1 1 t ∧
      t.pc = (if s.getReg .x8 = 0 then pcOf 40892 else pcOf 40879) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound layerBranch (Code.branch2Code_at (im := im)) s hpc (by simp [layerBranch.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, layerBranch.res, rv_simp]
  · intro r hr; cases r <;> simp [layerBranch.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, layerBranch.res, rv_simp]

theorem hook_spec (s : MachineState) (hpc : s.pc = pcOf 1117) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 40875 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hookCodeBlock (Code.hookCode_at (im := im)) s hpc (by simp [hookCodeBlock.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, hookCodeBlock.res, rv_simp, pcOf]
  · intro r hr; cases r <;> simp [hookCodeBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, hookCodeBlock.res, rv_simp]

theorem back_spec (s : MachineState) (hpc : s.pc = pcOf 40892) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1119 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound backCodeBlock (Code.backCode_at (im := im)) s hpc (by simp [backCodeBlock.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, backCodeBlock.res, rv_simp, pcOf]
  · intro r hr; cases r <;> simp [backCodeBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, backCodeBlock.res, rv_simp]

theorem continue_spec (s : MachineState) (hpc : s.pc = pcOf 1117)
    (hc : remaining s ≠ 0 ∨ s.getReg .x8 = 0) :
    ∃ t k, Steps im s k k t ∧ k ≤ 6 ∧ t.pc = pcOf 1119 ∧
      t.getReg .x28 = remaining s ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨u, su, up, ur, uf⟩ := hook_spec (im := im) s hpc
  have he : remaining u = remaining s := by
    unfold remaining
    rw [ur.get (by simp), ur.get (by simp)]
  obtain ⟨v, uv, vp, v28, vr, vf⟩ := select_spec (im := im) u up
  rw [he] at vp v28
  by_cases hz : remaining s = 0
  · rw [if_pos hz] at vp
    have h8 : v.getReg .x8 = 0 := by
      rw [vr.get (by simp), ur.get (by simp)]
      exact hc.resolve_left (not_not_intro hz)
    obtain ⟨w, vw, wp, wr, wf⟩ := layer_spec (im := im) v vp
    rw [if_pos h8] at wp
    obtain ⟨t, wt, tp, tr, tf⟩ := back_spec (im := im) w wp
    refine ⟨t, 6, ((su.trans uv).trans vw).trans wt, by omega, tp, ?_, ?_, ?_⟩
    · rw [tr.get (by simp), wr.get (by simp), v28]
    · exact (((ur.trans vr).trans wr).trans tr).mono (by decide)
    · exact (((uf.trans vf).trans wf).trans tf).mono (by intro A hA h; simpa using h)
  · rw [if_neg hz] at vp
    obtain ⟨t, vt, tp, tr, tf⟩ := back_spec (im := im) v vp
    refine ⟨t, 5, (su.trans uv).trans vt, by omega, tp, ?_, ?_, ?_⟩
    · rw [tr.get (by simp), v28]
    · exact ((ur.trans vr).trans tr).mono (by decide)
    · exact ((uf.trans vf).trans tf).mono (by intro A hA h; simpa using h)

theorem finish_spec (s : MachineState) (hpc : s.pc = pcOf 1117) (ret : Nat)
    (hz : remaining s = 0) (hl : s.getReg .x8 ≠ 0) (hra : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 18 18 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 NODE) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (NODE + 8)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (NODE + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (NODE + 56)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  obtain ⟨u, su, up, ur, uf⟩ := hook_spec (im := im) s hpc
  have he : remaining u = 0 := by unfold remaining; rw [ur.get (by simp), ur.get (by simp)]; exact hz
  obtain ⟨v, uv, vp, v28, vr, vf⟩ := select_spec (im := im) u up
  rw [if_pos he] at vp
  have h8 : v.getReg .x8 ≠ 0 := by rw [vr.get (by simp), ur.get (by simp)]; exact hl
  obtain ⟨w, vw, wp, wr, wf⟩ := layer_spec (im := im) v vp
  rw [if_neg h8] at wp
  obtain ⟨t, wt, tp, m0, m8, m48, m56, tr, tf⟩ := pair_spec (im := im) w wp ret
    (by rw [wr.get (by simp), vr.get (by simp), ur.get (by simp)]; exact hra)
  have fsw : Frame s w (fun _ => False) := ((uf.trans vf).trans wf).mono (by intro A hA h; simpa using h)
  refine ⟨t, ((su.trans uv).trans vw).trans wt, tp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m0, fsw.get (by decide) (by simp)]
  · rw [m8, fsw.get (by decide) (by simp)]
  · rw [m48, fsw.get (by decide) (by simp)]
  · rw [m56, fsw.get (by decide) (by simp)]
  · exact (((ur.trans vr).trans wr).trans tr).mono (by decide)
  · exact (fsw.trans tf).mono (by intro A hA h; simpa using h)

end SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
/-! img-v6 top-node nonce routine (words 43195 .. 43249, hooked at 1139 `jal 43195`; topfold-v6, NOTES V49). -/
variable {im : Image} [Code im]
variable [BCBlocks.Code im] [PackedBlocks.Code im]
variable (s : MachineState)
theorem rl997_spec (hpc : s.pc = pcOf 997) (lay : T3.Layer) (tree leaf : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ T3.hyperW lay.val)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h15 : s.getReg .x15 = BitVec.ofNat 64 (T3.height lay)) :
    ∃ t, Steps im s (hpK lay) (hpK lay) t ∧ t.pc = pcOf 1010 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧
      (lay = 0 → t.getMem (BitVec.ofNat 64 LEAFPK) = 0 ∧ t.getMem (BitVec.ofNat 64 (LEAFPK + 8)) = 0) ∧
      RegsExcept s t [.x6, .x7, .x19, .x28, .x30] ∧
      Frame s t (fun A => A = LEAFPK ∨ A = LEAFPK + 8 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
  have hl := lay.isLt
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42741 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_997 (Code.codeAt_997 (im := im)) s hpc (by simp [eblk_997.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_997.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [r1.get (by decide), h8]
  have g9 : t1.getReg .x9 = BitVec.ofNat 64 tree := by rw [r1.get (by decide), h9]
  have g18 : t1.getReg .x18 = BitVec.ofNat 64 leaf := by rw [r1.get (by decide), h18]
  have g15 : t1.getReg .x15 = BitVec.ofNat 64 (T3.height lay) := by rw [r1.get (by decide), h15]
  obtain ⟨t2, s2, p2, m16, m24, x28, r2, f2⟩ : ∃ t, Steps im t1 21 21 t ∧
      t.pc = (if lay = 0 then pcOf 42755 else pcOf 42757) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧ t.getReg .x28 = BitVec.ofNat 64 LEAFPK ∧
      RegsExcept t1 t [.x6, .x28, .x30] ∧ Frame t1 t (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
    refine ⟨_, LH.chain3_sound eb_hpA0 (Code.e_hpA_at (im := im)) p1 (by rfl) eb_hpT (Code.e_hpT_at (im := im))
      (by rfl) eb_hpA (Code.e_hpA2_at (im := im))
      (by simp [eb_hpA.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_hpA.res, LH.y6E_fold, LH.restE_fold]
      simp only [E.eval, CmpOp.eval, LH.restE_eval t1 lay.val lay.isLt g8, g8, bne]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq lay.val 0 (by omega) (by norm_num)]
      by_cases h0 : lay = 0
      · subst h0; simp
      · have : lay.val ≠ 0 := fun h => h0 (Fin.ext h)
        simp [h0, this]
    · simp only [Result.toState_getMem, eb_hpA.res]
      t3n [g9, g18, g15, LEAFPK]
      have hh : T3.height lay < 64 := by fin_cases lay <;> decide
      rw [Nat.mod_eq_of_lt (by omega : T3.height lay < 18446744073709551616), Nat.mod_eq_of_lt hh,
        LH.mark_bv lay.val lay.isLt _ g8]
      exact LH.label_or0 lay.val _ lay.isLt hr
    · simp only [Result.toState_getMem, eb_hpA.res]
      t3n [LEAFPK]
    · simp [eb_hpA.res, rv_simp]
    · intro r hr
      by_cases h8r : r = .x8
      · subst h8r; simp only [Result.toState_getReg, eb_hpA.res, LH.y6E_fold, LH.restE_fold]
        exact LH.restE_eval t1 lay.val lay.isLt g8
      · simp at hr; cases r <;> simp_all [eb_hpA.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, eb_hpA.res]
      t3n []
      simp only [LEAFPK] at hn
      rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨t3, s3, p3, z0, r3, f3⟩ : ∃ t, Steps im t2 (if lay = 0 then 3 else 1) (if lay = 0 then 3 else 1) t ∧
      t.pc = pcOf 1009 ∧
      (lay = 0 → t.getMem (BitVec.ofNat 64 LEAFPK) = 0 ∧ t.getMem (BitVec.ofNat 64 (LEAFPK + 8)) = 0) ∧
      RegsExcept t2 t [] ∧ Frame t2 t (fun A => A = LEAFPK ∨ A = LEAFPK + 8) := by
    by_cases h0 : lay = 0
    · rw [if_pos h0] at p2
      refine ⟨_, (symRun_sound eb_hpZ (Code.e_hpZ_at (im := im)) t2 p2
        (by simp [eb_hpZ.res, rv_simp, x28, accessValid_iff, MEMORY_BYTES, LEAFPK])).of_eq (by simp [h0, eb_hpZ.res])
        (by simp [h0, eb_hpZ.res]),
        ?_, fun _ => ⟨?_, ?_⟩, ?_, ?_⟩
      · simp [Result.toState_pc, eb_hpZ.res, E.eval]
      · simp only [Result.toState_getMem, eb_hpZ.res]
        t3n [x28, LEAFPK]
      · simp only [Result.toState_getMem, eb_hpZ.res]
        t3n [x28, LEAFPK]
      · intro r hr; cases r <;> rfl
      · intro A hA hn
        simp only [Result.toState_getMem, eb_hpZ.res]
        t3n [x28]
        simp only [LEAFPK] at hn ⊢
        rw [if_neg (by omega), if_neg (by omega)]
    · rw [if_neg h0] at p2
      refine ⟨_, (symRun_sound eb_hpJ (Code.e_hpJ_at (im := im)) t2 p2 (by simp [eb_hpJ.res, rv_simp])).of_eq (by simp [h0, eb_hpJ.res])
        (by simp [h0, eb_hpJ.res]), ?_, fun h => absurd h h0, ?_, ?_⟩
      · simp [Result.toState_pc, eb_hpJ.res, E.eval]
      · intro r hr; cases r <;> rfl
      · intro A hA hn; rfl
  obtain ⟨t4, s4, p4, x19, r4, f4⟩ : ∃ t, Steps im t3 1 1 t ∧ t.pc = pcOf 1010 ∧
      t.getReg .x19 = BitVec.ofNat 64 0 ∧ RegsExcept t3 t [.x19] ∧ Frame t3 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_w1009 (Code.e_w1009_at (im := im)) t3 p3 (by simp [eb_w1009.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_w1009.res, E.eval]
    · simp [eb_w1009.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [eb_w1009.res, rv_simp] <;> rfl
    · intro A _ _; simp [eb_w1009.res, rv_simp]
  refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by unfold hpK; split_ifs <;> simp_all)
    (by unfold hpK; split_ifs <;> simp_all), p4, x19, ?_, ?_, fun h => ?_,
    (((r1.trans r2).trans r3).trans r4).mono (by decide),
    (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by
      rcases h with ((h | h) | h) | h <;> simp only [LEAFPK] at h ⊢ <;> omega)⟩
  · rw [f4.get (by simp only [LEAFPK]; omega) (by simp), f3.get (by simp only [LEAFPK]; omega)
      (by simp only [LEAFPK]; omega), m16]
  · rw [f4.get (by simp only [LEAFPK]; omega) (by simp), f3.get (by simp only [LEAFPK]; omega)
      (by simp only [LEAFPK]; omega), m24]
  · obtain ⟨a, b⟩ := z0 h
    exact ⟨by rw [f4.get (by simp only [LEAFPK]; omega) (by simp), a],
      by rw [f4.get (by simp only [LEAFPK]; omega) (by simp), b]⟩

theorem rl1010_spec (hpc : s.pc = pcOf 1010) (i n : Nat) (hi : i < 2 ^ 63) (hn : n < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = (if n ≤ i then pcOf 1063 else pcOf 1011) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1010 (Code.codeAt_1010 (im := im)) s hpc (by simp [eblk_1010.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1010.res, E.eval, CmpOp.eval, h19, h26]
    rw [ex_slt i n hi hn]
    by_cases hc : n ≤ i
    · simp [hc, show ¬ i < n by omega]
    · simp [hc, show i < n by omega]
  · ex_regs eblk_1010.res
  · intro A _ _; simp [eblk_1010.res, rv_simp]

theorem rl1011_spec (hpc : s.pc = pcOf 1011) (i P W : Nat) (hP : 0x7000 ≤ P) (hPi : P + 16 * i + 16 ≤ 0x7000 + 5616)
    (hP8 : P % 8 = 0) (hW8 : W % 8 = 0) (hW : 64 ≤ W) (hW' : W + 64 ≤ 0x7000)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h16 : s.getReg .x16 = BitVec.ofNat 64 P)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 W) :
    ∃ t, Steps im s 16 16 t ∧ t.pc = pcOf 1027 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 48)) = s.getMem (BitVec.ofNat 64 (P + 16 * i)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 56)) = s.getMem (BitVec.ofNat 64 (P + 16 * i + 8)) ∧
      t.getMem (BitVec.ofNat 64 (W + 48)) = s.getMem (BitVec.ofNat 64 (P + 16 * i)) ∧
      t.getMem (BitVec.ofNat 64 (W + 56)) = s.getMem (BitVec.ofNat 64 (P + 16 * i + 8)) ∧
      t.getReg .x23 = BitVec.ofNat 64 (W - 64) ∧ t.getReg .x28 = BitVec.ofNat 64 (i + DIGITS) ∧
      RegsExcept s t [.x6, .x7, .x23, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) := by
  have ea : ∀ k, BitVec.ofNat 64 i <<< ((4#64 : Word).toNat % 64) + BitVec.ofNat 64 P + BitVec.ofNat 64 k =
      BitVec.ofNat 64 (P + 16 * i + k) := fun k => by
    rw [show ((4#64 : Word).toNat % 64) = 4 from rfl, ofNat_shl, ofNat_add_ofNat, ofNat_add_ofNat]
    congr 1; ring
  have hne : ∀ x y : Nat, x < 2 ^ 64 → y < 2 ^ 64 → x ≠ y → BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y :=
    fun x y hx hy h he => h ((ofNat_inj hx hy).mp he)
  have hv : ∀ x : Nat, x % 8 = 0 → x + 8 ≤ 2 ^ 24 → accessValid (BitVec.ofNat 64 x) 8 = true := fun x h1 h2 => by
    rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
  refine ⟨_, symRun_sound eblk_1011 (Code.codeAt_1011 (im := im)) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_1011.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, h19, h16, h23,
      ea, ofNat_add_ofNat, show (56#64 : Word) = BitVec.ofNat 64 56 from rfl,
      show (48#64 : Word) = BitVec.ofNat 64 48 from rfl, show (131536#64 : Word) = BitVec.ofNat 64 131536 from rfl,
      show (131544#64 : Word) = BitVec.ofNat 64 131544 from rfl]
    refine ⟨hv _ (by omega) (by omega), hv _ (by omega) (by omega), hne _ _ (by omega) (by omega) (by omega),
      hne _ _ (by omega) (by omega) (by omega), hne _ _ (by omega) (by omega) (by omega),
      hne _ _ (by omega) (by omega) (by omega), hv _ (by omega) (by omega), hv _ (by omega) (by omega)⟩
  · simp [Result.toState_pc, eblk_1011.res, E.eval]
  iterate 4
    · simp only [Result.toState_getMem, eblk_1011.res, CHAIN]
      t3n [h19, h16, h23]
      (try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl
  · simp only [Result.toState_getReg, eblk_1011.res, rv_simp, h23]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, toNat_ofNat_lt (show W < 2 ^ 64 by omega), toNat_ofNat_lt (show W - 64 < 2 ^ 64 by omega)]
    rw [show (64#64 : Word).toNat = 64 from rfl]; omega
  · simp only [Result.toState_getReg, eblk_1011.res, rv_simp, h19, ofNat_add_ofNat]
  · ex_regs eblk_1011.res
  · intro A hA hn
    simp only [CHAIN] at hn
    simp only [Result.toState_getMem, eblk_1011.res, rv_simp, h23, ofNat_add_ofNat]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem rl1027_spec (hpc : s.pc = pcOf 1027) (i d : Nat) (hi : i < 64) (hd : d < 256)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (i + DIGITS))
    (hb : s.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1028 ∧ t.getReg .x20 = BitVec.ofNat 64 d ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have ea : s.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (DIGITS + i) := by
    rw [h28, show signExtend12 (0 : BitVec 12) = 0 from rfl, add_zero, Nat.add_comm]
  have hv : accessValid (s.getReg .x28 + signExtend12 0) 1 = true := by
    rw [ea, accessValid_iff, toNat_ofNat_lt (by simp only [DIGITS]; omega)]; simp only [MEMORY_BYTES, DIGITS]; omega
  refine ⟨_, steps_lbu (Code.codeAt_1027 (im := im)) hpc lbu_word1027 hv, ?_, ?_, ?_, ?_⟩
  · show s.pc + 4 = _; rw [hpc, pcOf_add4]
  · have e2 : ∀ (u : MachineState) (v pc : Word), ((u.setReg .x20 v).setPC pc).getReg .x20 = v :=
      fun u v pc => rfl
    rw [e2, ea, hb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth]
    omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show ((s.setReg .x20 _).setPC _).getReg r = _
    cases r <;> simp_all [MachineState.getReg, MachineState.setReg, MachineState.setPC]
  · intro A _ _; rfl

theorem rl1028_spec (hpc : s.pc = pcOf 1028) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if lay = 0 then pcOf 1030 else pcOf 1031) ∧
      t.getReg .x21 = BitVec.ofNat 64 7 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hz : (BitVec.ofNat 64 lay = 0#64) ↔ lay = 0 := by
    constructor
    · intro e
      have q := congrArg BitVec.toNat e
      simpa [toNat_ofNat_lt hlay] using q
    · intro e; subst lay; rfl
  refine ⟨_, symRun_sound eblk_1028 (Code.codeAt_1028 (im := im)) s hpc (by simp [eblk_1028.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1028.res, E.eval, CmpOp.eval, h8, hz]
  · simp [eblk_1028.res, rv_simp]
  · ex_regs eblk_1028.res
  · intro A _ _; simp [eblk_1028.res, rv_simp]

theorem rl1030_spec (hpc : s.pc = pcOf 1030) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1158 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1030 (Code.codeAt_1030 (im := im)) s hpc (by simp [eblk_1030.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1030.res, E.eval]
  · ex_regs eblk_1030.res
  · intro A _ _; simp [eblk_1030.res, rv_simp]

theorem rl1158_spec (hpc : s.pc = pcOf 1158) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s (kmaxSteps i) (kmaxSteps i) t ∧ t.pc = pcOf 1031 ∧
      t.getReg .x21 = BitVec.ofNat 64 (SigGolfCandidate.T3.maxDigit 0 i) ∧ RegsExcept s t [.x21, .x28] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 54532 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_1158 (Code.codeAt_1158 (im := im)) s hpc (by simp [eblk_1158.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_1158.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A _ _; rfl
  have g19 : t0.getReg .x19 = BitVec.ofNat 64 i := by rw [r0.get (by decide), h19]
  have j4 : ∀ u : MachineState, u.pc = pcOf 54542 → ∃ v, Steps im u 1 1 v ∧ v.pc = pcOf 1031 ∧
      RegsExcept u v [] ∧ Frame u v (fun _ => False) := fun u hu => by
    refine ⟨_, symRun_sound eb_kmax4 (Code.e_kmax4_at (im := im)) u hu (by simp [eb_kmax4.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_kmax4.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A _ _; rfl
  have hmd : SigGolfCandidate.T3.maxDigit 0 i =
      (if i < 27 then 5 else if i < 48 then 4 else if i < 50 then 6 else 5) := by
    simp [SigGolfCandidate.T3.maxDigit]
  obtain ⟨t1, s1, p1, x1, r1, f1⟩ : ∃ t, Steps im t0 3 3 t ∧
      t.pc = (if i < 27 then pcOf 54542 else pcOf 54535) ∧ t.getReg .x21 = BitVec.ofNat 64 5 ∧
      RegsExcept t0 t [.x21, .x28] ∧ Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_kmax0 (Code.e_kmax0_at (im := im)) t0 p0 (by simp [eb_kmax0.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_kmax0.res, E.eval, CmpOp.eval, RegFile.get, g19]
      rw [show (27#64 : Word) = BitVec.ofNat 64 27 from rfl, ex_slt i 27 hi (by norm_num)]
      by_cases hi' : i < 27 <;> simp [hi']
    · simp [eb_kmax0.res, rv_simp]
    · ex_regs eb_kmax0.res
    · intro A _ _; simp [eb_kmax0.res, rv_simp]
  by_cases h27 : i < 27
  · rw [if_pos h27] at p1
    obtain ⟨t2, s2, p2, r2, f2⟩ := j4 t1 p1
    refine ⟨t2, ((s0.trans s1).trans s2).of_eq (by unfold kmaxSteps; split_ifs <;> omega)
      (by unfold kmaxSteps; split_ifs <;> omega), p2, by rw [r2.get (by decide), x1, hmd, if_pos h27],
      ((r0.trans r1).trans r2).mono (by decide), ((f0.trans f1).trans f2).mono (fun A _ h => by simp_all)⟩
  rw [if_neg h27] at p1
  have g19a : t1.getReg .x19 = BitVec.ofNat 64 i := by rw [r1.get (by decide), g19]
  obtain ⟨t2, s2, p2, x2, r2, f2⟩ : ∃ t, Steps im t1 3 3 t ∧
      t.pc = (if i < 48 then pcOf 54542 else pcOf 54538) ∧ t.getReg .x21 = BitVec.ofNat 64 4 ∧
      RegsExcept t1 t [.x21, .x28] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_kmax1 (Code.e_kmax1_at (im := im)) t1 p1 (by simp [eb_kmax1.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_kmax1.res, E.eval, CmpOp.eval, RegFile.get, g19a]
      rw [show (48#64 : Word) = BitVec.ofNat 64 48 from rfl, ex_slt i 48 hi (by norm_num)]
      by_cases hi' : i < 48 <;> simp [hi']
    · simp [eb_kmax1.res, rv_simp]
    · ex_regs eb_kmax1.res
    · intro A _ _; simp [eb_kmax1.res, rv_simp]
  by_cases h48 : i < 48
  · rw [if_pos h48] at p2
    obtain ⟨t3, s3, p3, r3, f3⟩ := j4 t2 p2
    refine ⟨t3, (((s0.trans s1).trans s2).trans s3).of_eq (by unfold kmaxSteps; split_ifs <;> omega)
      (by unfold kmaxSteps; split_ifs <;> omega), p3, by rw [r3.get (by decide), x2, hmd, if_neg h27, if_pos h48],
      (((r0.trans r1).trans r2).trans r3).mono (by decide),
      (((f0.trans f1).trans f2).trans f3).mono (fun A _ h => by simp_all)⟩
  rw [if_neg h48] at p2
  have g19b : t2.getReg .x19 = BitVec.ofNat 64 i := by rw [r2.get (by decide), g19a]
  obtain ⟨t3, s3, p3, x3, r3, f3⟩ : ∃ t, Steps im t2 3 3 t ∧
      t.pc = (if i < 50 then pcOf 54542 else pcOf 54541) ∧ t.getReg .x21 = BitVec.ofNat 64 6 ∧
      RegsExcept t2 t [.x21, .x28] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_kmax2 (Code.e_kmax2_at (im := im)) t2 p2 (by simp [eb_kmax2.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_kmax2.res, E.eval, CmpOp.eval, RegFile.get, g19b]
      rw [show (50#64 : Word) = BitVec.ofNat 64 50 from rfl, ex_slt i 50 hi (by norm_num)]
      by_cases hi' : i < 50 <;> simp [hi']
    · simp [eb_kmax2.res, rv_simp]
    · ex_regs eb_kmax2.res
    · intro A _ _; simp [eb_kmax2.res, rv_simp]
  by_cases h50 : i < 50
  · rw [if_pos h50] at p3
    obtain ⟨t4, s4, p4, r4, f4⟩ := j4 t3 p3
    refine ⟨t4, ((((s0.trans s1).trans s2).trans s3).trans s4).of_eq (by unfold kmaxSteps; split_ifs <;> omega)
      (by unfold kmaxSteps; split_ifs <;> omega), p4,
      by rw [r4.get (by decide), x3, hmd, if_neg h27, if_neg h48, if_pos h50],
      ((((r0.trans r1).trans r2).trans r3).trans r4).mono (by decide),
      ((((f0.trans f1).trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩
  rw [if_neg h50] at p3
  obtain ⟨t4, s4, p4, x4, r4, f4⟩ : ∃ t, Steps im t3 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x21 = BitVec.ofNat 64 5 ∧
      RegsExcept t3 t [.x21] ∧ Frame t3 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_kmax3 (Code.e_kmax3_at (im := im)) t3 p3 (by simp [eb_kmax3.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_kmax3.res, E.eval]
    · simp [eb_kmax3.res, rv_simp]
    · ex_regs eb_kmax3.res
    · intro A _ _; simp [eb_kmax3.res, rv_simp]
  refine ⟨t4, ((((s0.trans s1).trans s2).trans s3).trans s4).of_eq (by unfold kmaxSteps; split_ifs <;> omega)
    (by unfold kmaxSteps; split_ifs <;> omega), p4,
    by rw [x4, hmd, if_neg h27, if_neg h48, if_neg h50],
    ((((r0.trans r1).trans r2).trans r3).trans r4).mono (by decide),
    ((((f0.trans f1).trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩

theorem rl1031_spec (hpc : s.pc = pcOf 1031) (st e : Nat) (hs : st < 2 ^ 63) (he : e < 2 ^ 63)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 st) (h21 : s.getReg .x21 = BitVec.ofNat 64 e) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = (if e ≤ st then pcOf 1049 else pcOf 1032) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1031 (Code.codeAt_1031 (im := im)) s hpc (by simp [eblk_1031.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1031.res, E.eval, CmpOp.eval, h20, h21]
    rw [ex_slt st e hs he]
    by_cases hc : e ≤ st
    · simp [hc, show ¬ st < e by omega]
    · simp [hc, show st < e by omega]
  · ex_regs eblk_1031.res
  · intro A _ _; simp [eblk_1031.res, rv_simp]

theorem rl1032_spec (hpc : s.pc = pcOf 1032) (lay : T3.Layer) (tree leaf i st : Nat)
    (hrH : tree * 2 ^ T3.height lay + leaf < 2 ^ T3.hyperW lay.val) (hf : leaf < 2 ^ T3.height lay)
    (hi : i < 64) (hs : st < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 st) :
    ∃ t, Steps im s (expHdrK lay) (expHdrK lay) t ∧ t.pc = pcOf 1041 ∧
      t.getReg .x28 = BitVec.ofNat 64 CHAIN ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 16)) = (T3.chainHeader lay tree leaf i st).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 24)) = (T3.chainHeader lay tree leaf i st).extractLsb' 64 64 ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun A => A = CHAIN + 16 ∨ A = CHAIN + 24) := by
  have hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31 :=
    lt_of_lt_of_le hrH (Nat.pow_le_pow_right (by norm_num) (T3.hyperW_le _))
  have run : ∃ t, Steps im s (expHdrK lay) (expHdrK lay) t ∧
      t.pc = pcOf 1041 ∧ PackedBlocks.ExpHeaderPost s t (T3.height lay) := by
    fin_cases lay
    · exact PackedBlocks.expand_header_0 (im := im) s hpc h8
    · exact PackedBlocks.expand_header_1 (im := im) s hpc h8
    · exact PackedBlocks.expand_header_2 (im := im) s hpc h8
    · exact PackedBlocks.expand_header_3 (im := im) s hpc h8
  obtain ⟨t, steps, pc, post⟩ := run
  refine ⟨t, steps, pc, post.x28,
    post.low.trans (Keygen.PackedBlocks.packedAt_source s lay tree leaf i st hrH hf hi hs h8 h9 h18 h19 h20),
    ?_, post.regs, post.frame⟩
  exact (post.high.trans (Keygen.PackedBlocks.routedAt_high_zero s lay tree leaf hr h9 h18)).trans
    (Keygen.PackedBlocks.source_high_actual lay tree leaf i st hrH hf hi hs).symm

/-- The F path's C3 tail `jal 43451` (at 49337) and its trampoline (an F chain: `isG = false`). -/
theorem rl1047_spec (hpc : s.pc = pcOf 49337) (lay : T3.Layer) (i m : Nat) (hi : i < 2 ^ 64) (hm : m < 2 ^ 63)
    (hG : ClaudeWCT.WCT9.isG lay i = false)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (lo hv : T3.Digest) (hlo : DigAt s (CHAIN + 48) lo)
    (hhv : DigAt s (CHAIN + 64) hv) :
    ∃ t, Steps im s (2 + trXE lay.val i m) (2 + trXE lay.val i m) t ∧ t.pc = pcOf 1031 ∧
      t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
      DigAt t (CHAIN + 48) (if ClaudeWCT.WCT9.chainHigh lay i m then hv else lo) ∧
      RegsExcept s t [.x6, .x7, .x20, .x28] ∧ Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  have hlay : lay.val < 2 ^ 64 := by have := lay.isLt; omega
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 43451 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_49337 (Code.codeAt_49337 (im := im)) s hpc (by simp [eblk_49337.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [eblk_49337.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have last : ∀ u : MachineState, u.pc = pcOf 43460 → u.getReg .x20 = BitVec.ofNat 64 m →
      ∃ t, Steps im u 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
        RegsExcept u t [.x20] ∧ Frame u t (fun _ => False) := by
    intro u hu hu20
    refine ⟨_, symRun_sound eb_ct4 (Code.e_ct4_at (im := im)) u hu (by simp [eb_ct4.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [eb_ct4.res, E.eval]
    · simp only [Result.toState_getReg, eb_ct4.res, rv_simp, hu20]
      rw [ofNat_add_ofNat]
    · intro r hr; simp at hr; cases r <;> simp_all [eb_ct4.res, rv_simp] <;> rfl
    · intro A _ _; simp [eb_ct4.res, rv_simp]
  have ne_of {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
      (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = decide (x ≠ y) := by
    by_cases hxy : x = y
    · subst hxy; simp
    · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
      simp [hxy, this]
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps im t0 1 1 t ∧ t.pc = (if i ≠ 0 then pcOf 43460 else pcOf 43452) ∧
      RegsExcept t0 t [] ∧ Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_ct0 (Code.e_ct0_at (im := im)) t0 p0 (by simp [eb_ct0.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_ct0.res, E.eval, CmpOp.eval, r0.get (by simp), h19]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ne_of hi (by norm_num)]
      by_cases hi0 : i = 0 <;> simp [hi0]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g1 : ∀ r, r ∉ ([] : List Reg) → t1.getReg r = s.getReg r := fun r hr => (r0.trans r1).get hr
  by_cases hi0 : i ≠ 0
  · rw [if_pos hi0] at p1
    obtain ⟨t2, s2, p2, x2, r2, f2⟩ := last t1 p1 (by rw [g1 _ (by simp)]; exact h20)
    have hs : ClaudeWCT.WCT9.chainHigh lay i m = false := ClaudeWCT.WCT9.chainHigh_eq_false_F hG (Or.inl hi0)
    refine ⟨t2, ((s0.trans s1).trans s2).of_eq (by simp [trXE, hi0]) (by simp [trXE, hi0]), p2, x2, ?_,
      ((r0.trans r1).trans r2).mono (by simp), ((f0.trans f1).trans f2).mono (fun A _ hA => by simp_all)⟩
    rw [hs]
    exact hlo.frame ((f0.trans f1).trans f2) (by decide) (by simp) (by simp)
  have hi0' : i = 0 := by omega
  rw [if_neg hi0] at p1
  obtain ⟨t2, s2, p2, r2, f2⟩ : ∃ t, Steps im t1 1 1 t ∧
      t.pc = (if lay.val = 0 then pcOf 43460 else pcOf 43453) ∧
      RegsExcept t1 t [] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_ct1 (Code.e_ct1_at (im := im)) t1 p1 (by simp [eb_ct1.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_ct1.res, E.eval, CmpOp.eval, g1 _ (by simp), h8]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq _ _ hlay (by norm_num)]
      by_cases hl0 : lay.val = 0 <;> simp [hl0]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g2 : ∀ r, r ∉ ([] : List Reg) → t2.getReg r = s.getReg r := fun r hr => ((r0.trans r1).trans r2).get hr
  have f02 : Frame s t2 (fun _ => False) := ((f0.trans f1).trans f2).mono (fun A _ hA => by simp_all)
  by_cases hl0 : lay.val = 0
  · rw [if_pos hl0] at p2
    obtain ⟨t3, s3, p3, x3, r3, f3⟩ := last t2 p2 (by rw [g2 _ (by simp)]; exact h20)
    have hs : ClaudeWCT.WCT9.chainHigh lay i m = false := by
      exfalso
      have hl : lay = 0 := Fin.ext hl0
      subst hl hi0'
      simp [ClaudeWCT.WCT9.isG, SigGolfCandidate.T3.topIsG] at hG
    refine ⟨t3, (((s0.trans s1).trans s2).trans s3).of_eq (by simp [trXE, hi0', hl0]) (by simp [trXE, hi0', hl0]),
      p3, x3, ?_, (((r0.trans r1).trans r2).trans r3).mono (by simp),
      (f02.trans f3).mono (fun A _ hA => by simp_all)⟩
    rw [hs]
    exact hlo.frame (f02.trans f3) (by decide) (by simp) (by simp)
  rw [if_neg hl0] at p2
  obtain ⟨t3, s3, p3, r3, f3⟩ : ∃ t, Steps im t2 2 2 t ∧ t.pc = (if m ≠ 6 then pcOf 43460 else pcOf 43455) ∧
      RegsExcept t2 t [.x6] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_ct2 (Code.e_ct2_at (im := im)) t2 p2 (by simp [eb_ct2.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_ct2.res, E.eval, CmpOp.eval, g2 _ (by simp), h20]
      rw [show (6#64 : Word) = BitVec.ofNat 64 6 from rfl, ne_of (by omega) (by norm_num)]
      by_cases hm6 : m = 6 <;> simp [hm6]
    · intro r hr; simp at hr; cases r <;> simp_all [eb_ct2.res, rv_simp] <;> rfl
    · intro A hA hn; simp [eb_ct2.res, rv_simp]
  have f03 : Frame s t3 (fun _ => False) := (f02.trans f3).mono (fun A _ hA => by simp_all)
  have g3 : ∀ r, r ∉ [.x6] → t3.getReg r = s.getReg r := fun r hr => ((((r0.trans r1).trans r2).trans r3)).get
    (by simpa using hr)
  by_cases hm6 : m ≠ 6
  · rw [if_pos hm6] at p3
    obtain ⟨t4, s4, p4, x4, r4, f4⟩ := last t3 p3 (by rw [g3 _ (by simp)]; exact h20)
    have hs : ClaudeWCT.WCT9.chainHigh lay i m = false :=
      ClaudeWCT.WCT9.chainHigh_eq_false_F hG (Or.inr hm6)
    refine ⟨t4, ((((s0.trans s1).trans s2).trans s3).trans s4).of_eq (by simp [trXE, hi0', hl0, hm6])
      (by simp [trXE, hi0', hl0, hm6]), p4, x4, ?_, ((((r0.trans r1).trans r2).trans r3).trans r4).mono (by simp),
      (f03.trans f4).mono (fun A _ hA => by simp_all)⟩
    rw [hs]
    exact hlo.frame (f03.trans f4) (by decide) (by simp) (by simp)
  have hm6' : m = 6 := by omega
  rw [if_neg hm6] at p3
  have hs : ClaudeWCT.WCT9.chainHigh lay i m = true :=
    ClaudeWCT.WCT9.chainHigh_eq_true.mpr (Or.inl ⟨fun h => hl0 (by rw [h]; rfl), Or.inl ⟨hi0', hm6'⟩⟩)
  have hobl : Oblig.all t3 eb_ct3.res.st.obl := by simp [eb_ct3.res, rv_simp]
  refine ⟨_, ((((s0.trans s1).trans s2).trans s3).trans (symRun_sound eb_ct3 (Code.e_ct3_at (im := im)) t3 p3 hobl)).of_eq
    (by simp [trXE, hi0', hl0, hm6', eb_ct3.res]) (by simp [trXE, hi0', hl0, hm6', eb_ct3.res]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [eb_ct3.res, E.eval]
  · simp only [Result.toState_getReg, eb_ct3.res, rv_simp]
    rw [g3 .x20 (by simp), h20, hm6']; rfl
  · rw [hs, if_pos rfl]
    have hv3 := hhv.frame f03 (by decide) (by simp) (by simp)
    constructor
    · simp only [Result.toState_getMem, eb_ct3.res]
      t3n []
      exact hv3.1
    · simp only [Result.toState_getMem, eb_ct3.res]
      t3n []
      exact hv3.2
  · exact ((((r0.trans r1).trans r2).trans r3).trans (eb_ct3_regs t3)).mono (by simp)
  · have f4 : Frame t3 (eb_ct3.res.toState t3) (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
      intro A hA hn
      simp only [Result.toState_getMem, eb_ct3.res]
      t3n []
      have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
      rw [hA', if_neg (by simp only [CHAIN] at hn; omega), if_neg (by simp only [CHAIN] at hn; omega)]
    exact (f03.trans f4).mono (fun A _ hA => by simp_all)

/-! ### Witness stack: the chain step block 49300..49337 (lower G, top G with the top rule, F) -/
/-- 1041 `jal 49300`, 49300 `beq s0,zero,49306`. -/
theorem sel_spec (hpc : s.pc = pcOf 1041) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if lay = 0 then pcOf 49306 else pcOf 49301) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 49300 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_1041 (Code.codeAt_1041 (im := im)) s hpc (by simp [eblk_1041.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [eblk_1041.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  refine ⟨_, s0.trans (symRun_sound eblk_49300 (Code.codeAt_49300 (im := im)) t0 p0
    (by simp [eblk_49300.res, rv_simp])), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_49300.res, E.eval, CmpOp.eval, r0.get (by simp), h8]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_eq hlay (by norm_num)]
    by_cases h0 : lay = 0 <;> simp [h0]
  · have r1 : RegsExcept t0 (eblk_49300.res.toState t0) [] := by
      intro r hr; cases r <;> rfl
    exact (r0.trans r1).mono (by simp)
  · have f1 : Frame t0 (eblk_49300.res.toState t0) (fun _ => False) := by
      intro A _ _; rfl
    exact (f0.trans f1).mono (fun A _ h => by simp_all)

/-- Lower layer: 49301 `andi t1,s3,1`, 49302 `beq t1,zero,49331`. -/
theorem lsel_spec (hpc : s.pc = pcOf 49301) (i : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if i % 2 = 0 then pcOf 49331 else pcOf 49303) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49301 (Code.codeAt_49301 (im := im)) s hpc (by simp [eblk_49301.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_49301.res, E.eval, CmpOp.eval, BinOp.eval, rv_simp, h19, pe_and1]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_eq (by omega) (by norm_num)]
    by_cases h0 : i % 2 = 0 <;> simp [h0]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49301.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49301.res, rv_simp]

/-- Lower G: 49303 `addi t1,zero,6`, 49304 `addi t2,zero,0`, 49305 `jal 49316`. -/
theorem lg_spec (hpc : s.pc = pcOf 49303) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 49316 ∧ t.getReg .x6 = BitVec.ofNat 64 6 ∧
      t.getReg .x7 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49303 (Code.codeAt_49303 (im := im)) s hpc (by simp [eblk_49303.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [eblk_49303.res, E.eval]
  · simp [eblk_49303.res, rv_simp]
  · simp [eblk_49303.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49303.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49303.res, rv_simp]

/-- Top: 49306 `andi t1,s3,1`, 49307 `addi t2,zero,0`, 49308 `bne t1,t2,49331`. -/
theorem tsel_spec (hpc : s.pc = pcOf 49306) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if i % 2 = 0 then pcOf 49309 else pcOf 49331) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49306 (Code.codeAt_49306 (im := im)) s hpc (by simp [eblk_49306.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_49306.res, E.eval, CmpOp.eval, BinOp.eval, rv_simp, h19, pe_and1]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_ne (by omega) (by norm_num)]
    by_cases h0 : i % 2 = 0 <;> simp [h0]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49306.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49306.res, rv_simp]

/-- Top: 49309 `addi t2,zero,52`, 49310 `blt t2,s3,49331`. -/
theorem tle_spec (hpc : s.pc = pcOf 49309) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if 52 < i then pcOf 49331 else pcOf 49311) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49309 (Code.codeAt_49309 (im := im)) s hpc (by simp [eblk_49309.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_49309.res, E.eval, CmpOp.eval, rv_simp, h19]
    rw [show (BitVec.ofNat 64 52 : Word) = BitVec.ofNat 64 52 from rfl, ofNat_slt 52 i (by norm_num) hi]
    by_cases h : 52 < i <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49309.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49309.res, rv_simp]

theorem tcap_spec (hpc : s.pc = pcOf 49311) (i : Nat) (hi : i ≤ 52) (hev : i % 2 = 0)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s (gtK i) (gtK i) t ∧ t.pc = pcOf 49316 ∧
      t.getReg .x6 = BitVec.ofNat 64 (gTerm i) ∧
      t.getReg .x7 = s.getMem (BitVec.ofNat 64 (CHAIN + 24)) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 54543 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_49311 (Code.codeAt_49311 (im := im)) s hpc (by simp [eblk_49311.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_49311.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A _ _; rfl
  have g19 : t0.getReg .x19 = BitVec.ofNat 64 i := by rw [r0.get (by decide), h19]
  obtain ⟨t1, s1, p1, x1, r1, f1⟩ : ∃ t, Steps im t0 8 8 t ∧
      t.pc = (if i = 0 then pcOf 54551 else pcOf 54552) ∧
      t.getReg .x6 = BitVec.ofNat 64 (SigGolfCandidate.T3.maxDigit 0 i - 1) ∧
      RegsExcept t0 t [.x6, .x7] ∧ Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_gt0 (Code.e_gt0_at (im := im)) t0 p0 (by simp [eb_gt0.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_gt0.res, E.eval, CmpOp.eval, g19]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_ne (by omega) (by norm_num)]
      by_cases h0 : i = 0 <;> simp [h0]
    · simp only [Result.toState_getReg, eb_gt0.res, rv_simp, g19]
      interval_cases i <;> first | decide | (exfalso; omega)
    · ex_regs eb_gt0.res
    · intro A _ _; simp [eb_gt0.res, rv_simp]
  obtain ⟨t2, k2, s2, hk2, p2, x2, r2, f2⟩ : ∃ t k, Steps im t1 k k t ∧ k = (if i = 0 then 2 else 1) ∧
      t.pc = pcOf 49315 ∧ t.getReg .x6 = BitVec.ofNat 64 (gTerm i) ∧
      RegsExcept t1 t [.x6] ∧ Frame t1 t (fun _ => False) := by
    by_cases h0 : i = 0
    · rw [if_pos h0] at p1
      refine ⟨_, 2, symRun_sound eb_gt1 (Code.e_gt1_at (im := im)) t1 p1 (by simp [eb_gt1.res, rv_simp]),
        by rw [if_pos h0], ?_, ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_gt1.res, E.eval]
      · simp [eb_gt1.res, rv_simp, gTerm, h0]
      · ex_regs eb_gt1.res
      · intro A _ _; simp [eb_gt1.res, rv_simp]
    · rw [if_neg h0] at p1
      refine ⟨_, 1, symRun_sound eb_gt2 (Code.e_gt2_at (im := im)) t1 p1 (by simp [eb_gt2.res, rv_simp]),
        by rw [if_neg h0], ?_, ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_gt2.res, E.eval]
      · simp only [Result.toState_getReg, eb_gt2.res, rv_simp, x1, gTerm, if_neg h0]
      · intro r hr; cases r <;> rfl
      · intro A _ _; rfl
  have r02 : RegsExcept s t2 [.x6, .x7] := ((r0.trans r1).trans r2).mono (by decide)
  have v28 : t2.getReg .x28 = BitVec.ofNat 64 CHAIN := by rw [r02.get (by simp)]; exact h28
  have hobl : Oblig.all t2 eblk_49315.res.st.obl := by
    simp only [eblk_49315.res]
    t3n [v28, CHAIN]
    try norm_num
  have sw := symRun_sound eblk_49315 (Code.codeAt_49315 (im := im)) t2 p2 hobl
  have f02 : Frame s t2 (fun _ => False) := ((f0.trans f1).trans f2).mono (fun A _ h => by simp_all)
  refine ⟨_, (((s0.trans s1).trans s2).trans sw).of_eq (by unfold gtK; rw [hk2]; split_ifs <;> simp [eblk_49315.res])
    (by unfold gtK; rw [hk2]; split_ifs <;> simp [eblk_49315.res]), by simp [eblk_49315.res, E.eval], ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_getReg, eblk_49315.res, rv_simp]; exact x2
  · rw [← f02.get (A := CHAIN + 24) (by decide) (by simp)]
    simp only [Result.toState_getReg, eblk_49315.res, rv_simp]
    t3n [v28, CHAIN]
  · have rw' : RegsExcept t2 (eblk_49315.res.toState t2) [.x7] := by
      intro r hr; simp at hr; cases r <;> simp_all [eblk_49315.res, rv_simp] <;> rfl
    exact (r02.trans rw').mono (by simp)
  · intro A hA _
    rw [show (eblk_49315.res.toState t2).getMem (BitVec.ofNat 64 A) = t2.getMem (BitVec.ofNat 64 A) by
      simp [eblk_49315.res, rv_simp]]
    exact (f02.get hA (by simp))

/-- The G body 49316..49326 (and 49327 on the terminal step `m = T`): `CHAIN+64 := CHAIN+16`, `CHAIN+72 := t2`,
pads, HASH arguments. -/
theorem g_spec (hpc : s.pc = pcOf 49316) (m T : Nat) (Y : Word)
    (hm : m < 2 ^ 63) (hT : T < 2 ^ 63) (h6 : s.getReg .x6 = BitVec.ofNat 64 T) (h7 : s.getReg .x7 = Y)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s (11 + (if m = T then 1 else 0)) (11 + (if m = T then 1 else 0)) t ∧ t.pc = pcOf 49328 ∧
      t.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (if m = T then CHAIN + 48 else CHAIN + 32) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 72)) = Y ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12, .x30] ∧ Frame s t (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
  have hobl : Oblig.all s eblk_49316.res.st.obl := by
    simp only [eblk_49316.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  have st := symRun_sound eblk_49316 (Code.codeAt_49316 (im := im)) s hpc hobl
  set u := eblk_49316.res.toState s with hu
  have upc : u.pc = (if m = T then pcOf 49327 else pcOf 49328) := by
    simp only [hu, Result.toState_pc, eblk_49316.res, E.eval, CmpOp.eval, h20, h6]
    rw [pe_ne (by omega) (by omega)]
    by_cases hm6 : m = T <;> simp [hm6]
  have ur : RegsExcept s u [.x10, .x11, .x12, .x30] := by
    intro r hr; simp at hr; cases r <;> simp_all [hu, eblk_49316.res, rv_simp] <;> rfl
  have uf : Frame s u (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
    intro A hA hn
    simp only [hu, Result.toState_getMem, eblk_49316.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
    have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
    simp only [CHAIN] at hn
    rw [hA']
    simp only [show ¬ A = 131560 by omega, show ¬ A = 131568 by omega, show ¬ A = 131576 by omega,
      show ¬ A = 131584 by omega, show ¬ A = 131592 by omega, show ¬ A = 131552 by omega, if_false]
  have u10 : u.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) := by
    simp only [hu, Result.toState_getReg, eblk_49316.res, rv_simp, h28] <;> rfl
  have u11 : u.getReg .x11 = BitVec.ofNat 64 64 := by
    simp only [hu, Result.toState_getReg, eblk_49316.res, rv_simp] <;> rfl
  have u12 : u.getReg .x12 = BitVec.ofNat 64 (CHAIN + 32) := by
    simp only [hu, Result.toState_getReg, eblk_49316.res, rv_simp, h28] <;> rfl
  have umem : u.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 72)) = Y ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [hu, Result.toState_getMem, eblk_49316.res]
      t3n [h28, h7, CHAIN, Nat.reduceLeDiff, and_true]
  by_cases hm6 : m = T
  · rw [if_pos hm6] at upc
    have hobl6 : Oblig.all u eblk_49327.res.st.obl := by simp [eblk_49327.res, rv_simp]
    have st6 := symRun_sound eblk_49327 (Code.codeAt_49327 (im := im)) u upc hobl6
    refine ⟨_, (st.trans st6).of_eq (by simp [hm6, eblk_49316.res, eblk_49327.res])
      (by simp [hm6, eblk_49316.res, eblk_49327.res]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [eblk_49327.res, E.eval]
    · simp only [Result.toState_getReg, eblk_49327.res, rv_simp]; exact u10
    · simp only [Result.toState_getReg, eblk_49327.res, rv_simp]; exact u11
    · simp only [Result.toState_getReg, eblk_49327.res, rv_simp, if_pos hm6, ur.get (show Reg.x28 ∉ _ by simp), h28]
      rfl
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.2.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.2.2.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.2.2.2.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.2.2.2.2
    · intro r hr
      rw [show (eblk_49327.res.toState u).getReg r = u.getReg r by
        cases r <;> simp_all [eblk_49327.res, rv_simp] <;> rfl]
      exact ur r hr
    · intro A hA hn
      rw [show (eblk_49327.res.toState u).getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) by
        simp [eblk_49327.res, rv_simp]]
      exact uf A hA hn
  · rw [if_neg hm6] at upc
    refine ⟨u, st.of_eq (by simp [hm6, eblk_49316.res]) (by simp [hm6, eblk_49316.res]), upc, u10, u11, ?_, umem.1,
      umem.2.1, umem.2.2.1, umem.2.2.2.1, umem.2.2.2.2.1, umem.2.2.2.2.2, ur, uf⟩
    rw [if_neg hm6]; exact u12

/-- The F body 49331..49335: zero the pad `CHAIN+32 .. CHAIN+48`, HASH arguments. -/
theorem f_spec (hpc : s.pc = pcOf 49331) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 49336 ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAIN ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAIN + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) := by
  have hobl : Oblig.all s eblk_49331.res.st.obl := by
    simp only [eblk_49331.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  refine ⟨_, symRun_sound eblk_49331 (Code.codeAt_49331 (im := im)) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eblk_49331.res, E.eval]
  · simp only [Result.toState_getReg, eblk_49331.res, rv_simp, h28] <;> rfl
  · simp only [Result.toState_getReg, eblk_49331.res, rv_simp] <;> rfl
  · simp only [Result.toState_getReg, eblk_49331.res, rv_simp, h28] <;> rfl
  · simp only [Result.toState_getMem, eblk_49331.res]; t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  · simp only [Result.toState_getMem, eblk_49331.res]; t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49331.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_49331.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
    have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
    simp only [CHAIN] at hn
    rw [hA']
    simp only [show ¬ A = 131520 by omega, show ¬ A = 131528 by omega, if_false]

/-- 49329 `addi s4,s4,1`, 49330 `jal 1031`. -/
theorem gtail_spec (hpc : s.pc = pcOf 49329) (m : Nat) (h20 : s.getReg .x20 = BitVec.ofNat 64 m) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49329 (Code.codeAt_49329 (im := im)) s hpc (by simp [eblk_49329.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [eblk_49329.res, E.eval]
  · simp only [Result.toState_getReg, eblk_49329.res, rv_simp, h20]
    rw [ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49329.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49329.res, rv_simp]

theorem rl1049_spec (hpc : s.pc = pcOf 1049) (lay : T3.Layer) (i : Nat) (hi : i < 2 ^ 59)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s (slK lay i) (slK lay i) t ∧ t.pc = pcOf 1052 ∧
      t.getReg .x28 = BitVec.ofNat 64 (slotOff lay i) ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42758 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_1049 (Code.codeAt_1049 (im := im)) s hpc (by simp [eblk_1049.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_1049.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g19 : t1.getReg .x19 = BitVec.ofNat 64 i := by rw [r1.get (by decide), h19]
  obtain ⟨t2, s2, p2, x28, r2, f2⟩ : ∃ t, Steps im t1 2 2 t ∧
      t.pc = pcOf 42760 ∧ t.getReg .x28 = BitVec.ofNat 64 (16 * i) ∧
      RegsExcept t1 t [.x28] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_slA (Code.e_slA_at (im := im)) t1 p1 (by simp [eb_slA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_slA.res, E.eval]
    · simp only [Result.toState_getReg, eb_slA.res, rv_simp, g19]
      t3n []; congr 1; ring
    · ex_regs eb_slA.res
    · intro A _ _; simp [eb_slA.res, rv_simp]
  have g19' : t2.getReg .x19 = BitVec.ofNat 64 i := by rw [r2.get (by decide), g19]
  obtain ⟨t3, s3, p3, r3, f3⟩ : ∃ t, Steps im t2 1 1 t ∧
      t.pc = (if i = 0 then pcOf 42764 else pcOf 42761) ∧ RegsExcept t2 t [] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_slB (Code.e_slB_at (im := im)) t2 p2 (by simp [eb_slB.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_slB.res, E.eval, CmpOp.eval, g19']
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq i 0 (by omega) (by norm_num)]
      by_cases hc : i = 0 <;> simp [hc]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  by_cases hi0 : i = 0
  · rw [if_pos hi0] at p3
    obtain ⟨t4, s4, p4, r4, f4⟩ : ∃ t, Steps im t3 1 1 t ∧ t.pc = pcOf 1052 ∧ RegsExcept t3 t [] ∧
        Frame t3 t (fun _ => False) := by
      refine ⟨_, symRun_sound eb_slZ (Code.e_slZ_at (im := im)) t3 p3 (by simp [eb_slZ.res, rv_simp]), ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_slZ.res, E.eval]
      · intro r hr; cases r <;> rfl
      · intro A hA hn; rfl
    refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by simp [slK, hi0]) (by simp [slK, hi0]), p4,
      by rw [r4.get (by decide), r3.get (by decide), x28, slotOff, if_pos hi0, hi0],
      (((r1.trans r2).trans r3).trans r4).mono (by decide),
      (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩
  · rw [if_neg hi0] at p3
    have y28 : t3.getReg .x28 = BitVec.ofNat 64 (16 * i) := by rw [r3.get (by decide), x28]
    obtain ⟨t4, s4, p4, z28, r4, f4⟩ : ∃ t, Steps im t3 2 2 t ∧ t.pc = pcOf 1052 ∧
        t.getReg .x28 = BitVec.ofNat 64 (16 * i + 16) ∧ RegsExcept t3 t [.x28] ∧ Frame t3 t (fun _ => False) := by
      refine ⟨_, symRun_sound eb_slN (Code.e_slN_at (im := im)) t3 p3 (by simp [eb_slN.res, rv_simp]), ?_, ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_slN.res, E.eval]
      · simp only [Result.toState_getReg, eb_slN.res, rv_simp, y28, ofNat_add_ofNat]
      · ex_regs eb_slN.res
      · intro A _ _; simp [eb_slN.res, rv_simp]
    refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by simp [slK, hi0]) (by simp [slK, hi0]), p4,
      by rw [z28, slotOff, if_neg hi0], (((r1.trans r2).trans r3).trans r4).mono (by decide),
      (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩

theorem rl1052_spec (hpc : s.pc = pcOf 1052) (i x : Nat) (hx8 : x % 8 = 0) (hx : LEAFPK + x + 16 ≤ 2 ^ 24)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 x) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf 1010 ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + x)) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + x + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x19, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFPK + x ∨ A = LEAFPK + x + 8) := by
  refine ⟨_, symRun_sound eblk_1052 (Code.codeAt_1052 (im := im)) s hpc (by
      simp only [eblk_1052.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, h28, ofNat_add_ofNat,
        show (132616#64 : Word) = BitVec.ofNat 64 132616 from rfl,
        show (132608#64 : Word) = BitVec.ofNat 64 132608 from rfl, accessValid_iff, MEMORY_BYTES,
        toNat_ofNat_lt (show x + 132616 < 2 ^ 64 by simp only [LEAFPK] at hx; omega),
        toNat_ofNat_lt (show x + 132608 < 2 ^ 64 by simp only [LEAFPK] at hx; omega)]
      simp only [LEAFPK] at hx; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1052.res, E.eval]
  · simp only [Result.toState_getReg, eblk_1052.res, rv_simp, h19, ofNat_add_ofNat]
  · simp only [Result.toState_getMem, eblk_1052.res, LEAFPK, CHAIN]
    t3n [h28]
    (try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl
  · simp only [Result.toState_getMem, eblk_1052.res, LEAFPK, CHAIN]
    t3n [h28]
    (try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl
  · ex_regs eblk_1052.res
  · intro A hA hn
    simp only [LEAFPK] at hn
    simp only [Result.toState_getMem, eblk_1052.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]

theorem rl1063_spec (hpc : s.pc = pcOf 1063) (n : Nat) (hn : n < 2 ^ 32)
    (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps im s 9 9 t ∧ t.pc = pcOf 1072 ∧ t.getReg .x10 = BitVec.ofNat 64 LEAFPK ∧
      t.getReg .x11 = BitVec.ofNat 64 ((16 * (n + 1) + 63) / 64 * 64) ∧ t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x6, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1063 (Code.codeAt_1063 (im := im)) s hpc (by simp [eblk_1063.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1063.res, E.eval]
  · simp [eblk_1063.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_1063.res, rv_simp, h26]
    have e1 : (BitVec.ofNat 64 n + 1#64) <<< ((4#64 : Word).toNat % 64) + 63#64 =
        BitVec.ofNat 64 (16 * (n + 1) + 63) := by
      rw [show ((4#64 : Word).toNat % 64) = 4 from rfl, show (1#64 : Word) = BitVec.ofNat 64 1 from rfl,
        show (63#64 : Word) = BitVec.ofNat 64 63 from rfl, ofNat_add_ofNat, ofNat_shl, ofNat_add_ofNat]
      congr 1; ring
    rw [e1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, toNat_ofNat_lt (show 16 * (n + 1) + 63 < 2 ^ 64 by omega),
      toNat_ofNat_lt (show (16 * (n + 1) + 63) / 64 * 64 < 2 ^ 64 by omega),
      show (18446744073709551552#64 : Word).toNat = (2 ^ 58 - 1) * 2 ^ 6 from rfl]
    have key : ∀ x : Nat, x < 2 ^ 64 → x &&& ((2 ^ 58 - 1) * 2 ^ 6) = x / 64 * 64 := by
      intro x hx
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.testBit_mul_two_pow, show (64 : Nat) = 2 ^ 6 from rfl, Nat.testBit_mul_two_pow,
        Nat.testBit_two_pow_sub_one]
      by_cases hk : 6 ≤ k
      · simp only [hk, decide_true, Bool.true_and, Nat.testBit_div_two_pow]
        by_cases hk2 : k - 6 < 58
        · simp [hk2, show k - 6 + 6 = k by omega]
        · simp only [hk2, decide_false, Bool.and_false]
          rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      · simp [hk]
    exact key _ (by omega)
  · simp [eblk_1063.res, rv_simp]
  · ex_regs eblk_1063.res
  · intro A _ _; simp [eblk_1063.res, rv_simp]

theorem rl1073_spec (hpc : s.pc = pcOf 1073) (P n : Nat) (hP : P + 16 * n < 2 ^ 64)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 P) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 1076 ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      t.getReg .x22 = BitVec.ofNat 64 (P + 16 * n) ∧ RegsExcept s t [.x20, .x22, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1073 (Code.codeAt_1073 (im := im)) s hpc (by simp [eblk_1073.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1073.res, E.eval]
  · simp [eblk_1073.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_1073.res, rv_simp, h16, h26]
    t3n []; congr 1; ring
  · ex_regs eblk_1073.res
  · intro A _ _; simp [eblk_1073.res, rv_simp]

theorem rl1076_spec (hpc : s.pc = pcOf 1076) (j hh : Nat) (hj : j < 2 ^ 63) (hh' : hh < 2 ^ 63)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = (if hh ≤ j then pcOf 1143 else pcOf 1077) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1076 (Code.codeAt_1076 (im := im)) s hpc (by simp [eblk_1076.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1076.res, E.eval, CmpOp.eval, h20, h15]
    rw [ex_slt j hh hj hh']
    by_cases hc : hh ≤ j
    · simp [hc, show ¬ j < hh by omega]
    · simp [hc, show j < hh by omega]
  · ex_regs eblk_1076.res
  · intro A _ _; simp [eblk_1076.res, rv_simp]

theorem rl1077_spec (hpc : s.pc = pcOf 1077) (leaf j : Nat) (hl : leaf < 2 ^ 64) (hj : j < 64)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if leaf / 2 ^ j % 2 = 0 then pcOf 1099 else pcOf 1080) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1077 (Code.codeAt_1077 (im := im)) s hpc (by simp [eblk_1077.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1077.res, E.eval, CmpOp.eval, BinOp.eval, h18, h20]
    rw [toNat_ofNat_lt (show j < 2 ^ 64 by omega), Nat.mod_eq_of_lt hj, ofNat_shr _ _ hl, ofNat_and1,
      show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq _ 0 (by omega) (by norm_num)]
    by_cases hc : leaf / 2 ^ j % 2 = 0
    · simp [hc]
    · simp [hc]
  · ex_regs eblk_1077.res
  · intro A _ _; simp [eblk_1077.res, rv_simp]

theorem rl1080_spec (hpc : s.pc = pcOf 1080) (P M : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P) (hP' : P + 16 ≤ 0x7000 + 5616)
    (hM8 : M % 8 = 0) (hM : 0x800 ≤ M) (hM' : M + 64 ≤ 0x7000)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M) :
    ∃ t, Steps im s 19 19 t ∧ t.pc = pcOf 1117 ∧
      t.getMem (BitVec.ofNat 64 M) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (M + 8)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = M ∨ A = M + 8 ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56) := by
  refine ⟨_, symRun_sound eblk_1080 (Code.codeAt_1080 (im := im)) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_1080.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h22, h24, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
        | (simp only [show (131584 : Nat) = NODE from rfl, show (131592 : Nat) = NODE + 8 from rfl]; exact ex_ne _ _ (by omega) (by omega) (by omega))
        | skip
  · simp [Result.toState_pc, eblk_1080.res, E.eval]
  iterate 6
    · simp only [Result.toState_getMem, eblk_1080.res, NODE, NOUT]
      t3n [h22, h24]
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl)
  · ex_regs eblk_1080.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eblk_1080.res]
    t3n [h24]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]

theorem rl1105_spec (hpc : s.pc = pcOf 1105) (X P : Nat) (hX : X = NOUT ∨ X = NOUT + 16) (hP8 : P % 8 = 0)
    (hP : 0x7000 ≤ P) (hP' : P + 16 ≤ 0x7000 + 5616)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 X) (h22 : s.getReg .x22 = BitVec.ofNat 64 P) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf 1117 ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 X) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (X + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      RegsExcept s t [.x6, .x7, .x30] ∧
      Frame s t (fun A => A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56) := by
  have hX' : 131648 ≤ X ∧ X ≤ 131664 ∧ X % 8 = 0 := by rcases hX with h | h <;> rw [h] <;> decide
  refine ⟨_, symRun_sound eb_lcD (Code.e_lcD_at (im := im)) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eb_lcD.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h22, h29, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    repeat' apply And.intro
    all_goals first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
        | skip
  · simp [Result.toState_pc, eb_lcD.res, E.eval]
  iterate 4
    · simp only [Result.toState_getMem, eb_lcD.res, NODE, NOUT]
      t3n [h22, h29]
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl)
  · ex_regs eb_lcD.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eb_lcD.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
/-- C2 (FULL): the bit-0 branch (current value = left input). Lower layers read the high half of the node output
(`NOUT + 16`, trampoline at 43462), the top layer the low half. -/
theorem rl1099_spec (hpc : s.pc = pcOf 1099) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (P M : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P)
    (hP' : P + 16 ≤ 0x7000 + 5616) (hM8 : M % 8 = 0) (hM : 0x800 ≤ M) (hM' : M + 64 ≤ 0x7000)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M) :
    ∃ t, Steps im s 22 22 t ∧ t.pc = pcOf 1117 ∧
      t.getMem (BitVec.ofNat 64 (M + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (M + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (NOUT + hiOff lay)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + hiOff lay + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = M + 48 ∨ A = M + 56 ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56) := by
  obtain ⟨t1, s1, p1, m48, m56, r1, f1⟩ : ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 43462 ∧
      t.getMem (BitVec.ofNat 64 (M + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (M + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun A => A = M + 48 ∨ A = M + 56) := by
    refine ⟨_, symRun_sound eblk_1099 (Code.codeAt_1099 (im := im)) s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [eblk_1099.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
        h22, h24, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
      repeat' apply And.intro
      all_goals first
          | exact ex_valid _ (by omega) (by omega)
          | exact ex_ne _ _ (by omega) (by omega) (by omega)
          | skip
    · simp [Result.toState_pc, eblk_1099.res, E.eval]
    iterate 2
      · simp only [Result.toState_getMem, eblk_1099.res]
        t3n [h22, h24]
        all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl)
    · ex_regs eblk_1099.res
    · intro A hA hn
      simp only [Result.toState_getMem, eblk_1099.res]
      t3n [h24]
      rw [if_neg (by omega), if_neg (by omega)]
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay := by rw [r1.get (by decide), h8]
  obtain ⟨t2, s2, p2, x29, r2, f2⟩ : ∃ t, Steps im t1 3 3 t ∧
      t.pc = pcOf 43465 ∧ t.getReg .x29 = BitVec.ofNat 64 NOUT ∧
      RegsExcept t1 t [.x29] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_lcA (Code.e_lcA_at (im := im)) t1 p1 (by simp [eb_lcA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_lcA.res, E.eval]
    · simp [eb_lcA.res, rv_simp]
    · ex_regs eb_lcA.res
    · intro A _ _; simp [eb_lcA.res, rv_simp]
  obtain ⟨t3, s3, p3, y29, r3, f3⟩ : ∃ t, Steps im t2 2 2 t ∧
      t.pc = pcOf 1105 ∧ t.getReg .x29 = BitVec.ofNat 64 (NOUT + hiOff lay) ∧
      RegsExcept t2 t [.x29] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_lcB (Code.e_lcB_at (im := im)) t2 p2 (by simp [eb_lcB.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_lcB.res, E.eval]
    · simp only [Result.toState_getReg, eb_lcB.res, rv_simp, x29, hiOff, ofNat_add_ofNat]
    · ex_regs eb_lcB.res
    · intro A _ _; simp [eb_lcB.res, rv_simp]
  have g22 : t3.getReg .x22 = BitVec.ofNat 64 P := by
    rw [r3.get (by decide), r2.get (by decide), r1.get (by decide), h22]
  obtain ⟨t4, s4, p4, n0, n8, n48, n56, r4, f4⟩ := rl1105_spec (im := im) t3 p3 (NOUT + hiOff lay) P
    (by unfold hiOff; simp) hP8 hP hP' y29 g22
  have f13 : Frame s t3 (fun A => A = M + 48 ∨ A = M + 56) :=
    ((f1.trans f2).trans f3).mono (fun A _ h => by rcases h with (h | h) | h; exact h; exact h.elim; exact h.elim)
  have hoff : hiOff lay ≤ 16 := by unfold hiOff; omega
  refine ⟨t4, ((s1.trans s2).trans s3).trans s4 |>.of_eq rfl rfl, p4,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f4.get (by omega) (by simp only [NODE]; omega), f3.get (by omega) (by simp), f2.get (by omega) (by simp), m48]
  · rw [f4.get (by omega) (by simp only [NODE]; omega), f3.get (by omega) (by simp), f2.get (by omega) (by simp), m56]
  · rw [n0, f13.get (by simp only [NOUT]; omega) (by simp only [NOUT]; omega)]
  · rw [n8, f13.get (by simp only [NOUT]; omega) (by simp only [NOUT]; omega)]
  · rw [n48, f13.get (by omega) (by omega)]
  · rw [n56, f13.get (by omega) (by omega)]
  · exact (((r1.trans r2).trans r3).trans r4).mono (by decide)
  · exact (f13.trans f4).mono (fun A _ h => by rcases h with (h | h) | h <;> simp_all)
set_option maxHeartbeats 1000000 in
theorem rl1119_spec (hpc : s.pc = pcOf 1119) (lay tree leaf hh j : Nat) (hlay : lay < 4) (htree : tree < 2 ^ 32)
    (htrH : lay ≠ 0 → tree < 2 ^ T3.hyperW (lay - 1))
    (hl : leaf < 2 ^ 32) (hj : j < hh) (hh' : hh ≤ 12) (htopl : lay = 0 → leaf < 2 ^ hh)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h15 : s.getReg .x15 = BitVec.ofNat 64 hh)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (hh - j - 1)) :
    ∃ t, Steps im s (hdrK lay) (hdrK lay) t ∧ t.pc = pcOf 1138 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) =
        (ClaudeWCT.WCT9.merkleTweak lay tree (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1))).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) =
        (ClaudeWCT.WCT9.merkleTweak lay tree (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1))).extractLsb' 64 64 ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x3, .x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30] ∧
      Frame s t (fun A => A = NODE + 16 ∨ A = NODE + 24) := by
  set heap := 2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1) with hheap
  have hheap' : heap < 2 ^ 64 := by
    have : 2 ^ (hh - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : leaf / 2 ^ (j + 1) ≤ leaf := Nat.div_le_self _ _
    omega
  obtain ⟨t1, s1, p1, x13, r1, f1⟩ : ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 42765 ∧
      t.getReg .x13 = BitVec.ofNat 64 heap ∧
      RegsExcept s t [.x13, .x28] ∧ Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_hdrA (Code.e_hdrA_at (im := im)) s hpc (by simp [eb_hdrA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_hdrA.res, E.eval]
    · simp only [Result.toState_getReg, eb_hdrA.res]
      t3n [h9, h15, h20, h18, h28]
      have e1 : (BitVec.ofNat 64 (hh - j - 1)).toNat % 64 = hh - j - 1 := by
        rw [toNat_ofNat_lt (show hh - j - 1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [BitVec.toNat_ofNat] at e1
      have e2 : (j + 1) % 18446744073709551616 % 64 = j + 1 := by omega
      have hp : 2 ^ (hh - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hq : leaf / 2 ^ (j + 1) < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) hl
      rw [e1, e2, ofNat_shr _ _ (by omega), Nat.one_mul, ofNat_add_ofNat]
    · ex_regs eb_hdrA.res
    · intro A _ _; simp [eb_hdrA.res, rv_simp]
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay := by rw [r1.get (by decide), h8]
  have g9 : t1.getReg .x9 = BitVec.ofNat 64 tree := by rw [r1.get (by decide), h9]
  obtain ⟨t2, s2, p2, x7, x6, r2, f2⟩ : ∃ t, Steps im t1 3 3 t ∧
      t.pc = (if lay = 0 then pcOf 42776 else pcOf 42768) ∧
      t.getReg .x7 = 0 ∧
      t.getReg .x6 = BitVec.ofNat 64 heap ∧ RegsExcept t1 t [.x6, .x7] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_hdrB (Code.e_hdrB_at (im := im)) t1 p1 (by simp [eb_hdrB.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_hdrB.res, E.eval, CmpOp.eval, g8]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq lay 0 (by omega) (by norm_num)]
      by_cases h0 : lay = 0 <;> simp [h0]
    · simp [eb_hdrB.res, rv_simp]
    · simp only [Result.toState_getReg, eb_hdrB.res, rv_simp, x13]
    · ex_regs eb_hdrB.res
    · intro A _ _; simp [eb_hdrB.res, rv_simp]
  have g13 : t2.getReg .x13 = BitVec.ofNat 64 heap := by rw [r2.get (by decide), x13]
  obtain ⟨t3, s3, p3, y6, y7, r3, f3⟩ : ∃ t, Steps im t2 (if lay = 0 then 13 else 20) (if lay = 0 then 13 else 20) t ∧
      t.pc = pcOf 1129 ∧ t.getReg .x6 = (ClaudeWCT.WCT9.merkleTweak lay tree heap).extractLsb' 0 64 ∧
      t.getReg .x7 = (ClaudeWCT.WCT9.merkleTweak lay tree heap).extractLsb' 64 64 ∧
      RegsExcept t2 t [.x3, .x6, .x7, .x30] ∧ Frame t2 t (fun _ => False) := by
    by_cases h0 : lay = 0
    · subst h0
      rw [if_pos rfl] at p2
      have hlf := htopl rfl
      have hheap1 : 1 ≤ heap := by
        rw [hheap]; exact le_trans Nat.one_le_two_pow (Nat.le_add_right _ _)
      have hheap2 : heap < 4096 := by
        have e : 2 ^ hh = 2 ^ (j + 1) * 2 ^ (hh - j - 1) := by rw [← Nat.pow_add]; congr 1; omega
        have hq : leaf / 2 ^ (j + 1) < 2 ^ (hh - j - 1) := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← e]; exact hlf
        have hp : 2 ^ (hh - j - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h11 : (2 : Nat) ^ 11 = 2048 := by norm_num
        rw [hheap]
        rw [h11] at hp
        generalize 2 ^ (hh - j - 1) = X at hq hp ⊢
        generalize leaf / 2 ^ (j + 1) = Y at hq ⊢
        omega
      obtain ⟨wlo, whi⟩ := merkleTweak_words_top tree heap hheap1 hheap2
      let nz : Bool := decide (t2.getReg .x6 ≠ 7#64)
      have hbr : (t2.getReg .x6 ≠ 7#64) ↔ nz = true := by simp [nz]
      have hwin : ExpandLabel.window <+: im.code.drop 1125 := by
        have h := (Code.e_hdrWindow_at (im := im)).2.2.2
        change ExpandLabel.window <+: im.code.drop 1125 at h
        exact h
      have hjump : [ExpandLabel.jump] <+: im.code.drop 42776 := by
        have h := (Code.e_hdrD_at (im := im)).2.2.2
        change [ExpandLabel.jump] <+: im.code.drop 42776 at h
        exact h
      have hpad : ExpandLabel.remapCode <+: im.code.drop 231593 := by
        exact (Code.e_hdrRemap_at (im := im)).2.2.2
      have ho : ∀ o ∈ (ExpandLabel.result nz).st.obl, o.holds t2 := by
        cases nz <;> simp [ExpandLabel.result, ExpandLabel.frozenEq.res, ExpandLabel.frozenNe.res]
      refine ⟨_, (ExpandLabel.steps (ExpandLabel.look_ok hwin hjump hpad) nz t2 p2 ho hbr).of_eq
        (by simp) (by simp), ExpandLabel.post_pc nz t2, ?_, ?_, ?_, ?_⟩
      · rw [wlo]
        exact ExpandLabel.post_word_ofNat t2 heap hheap' x6
      · rw [whi, ExpandLabel.post_seven]
        rfl
      · exact (ExpandLabel.post_regs nz t2).mono (by decide)
      · exact ExpandLabel.post_frame nz t2
    · rw [if_neg h0] at p2
      have g8' : t2.getReg .x8 = BitVec.ofNat 64 lay := by rw [r2.get (by decide), g8]
      have g9' : t2.getReg .x9 = BitVec.ofNat 64 tree := by rw [r2.get (by decide), g9]
      obtain ⟨u, su, pu, uor, u13, ru, fu⟩ : ∃ u, Steps im t2 15 15 u ∧ u.pc = pcOf 43467 ∧
          (u.getReg .x6 ||| u.getReg .x30) = BitVec.ofNat 64 (Keygen.nodeLo lay tree) ∧
          u.getReg .x13 = BitVec.ofNat 64 heap ∧ RegsExcept t2 u [.x6, .x30] ∧ Frame t2 u (fun _ => False) := by
        refine ⟨_, LH.chain2_sound eb_hdrC0 (Code.e_hdrC_at (im := im)) p2 (by rfl) eb_hdrC (Code.e_ndT_at (im := im))
          (by simp [eb_hdrC.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
        · simp [Result.toState_pc, eb_hdrC.res, E.eval]
        · simp only [Result.toState_getReg, eb_hdrC.res]
          t3n [g9']
          have hm := LH.markN_bv (lay - 1) (by omega) (t2.getReg .x8) (by rw [g8']; congr 1; omega)
          rw [Keygen.nodeLo_honest h0 (SigGolfCandidate.T3.hyperHonest_of (by omega) (htrH h0)), hm, BitVec.or_assoc,
            BitVec.or_self]
          exact LH.label_or (lay - 1) tree (by omega) (htrH h0)
        · simp only [Result.toState_getReg, eb_hdrC.res, rv_simp, g13]
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          by_cases h8r : r = .x8
          · subst h8r; simp only [Result.toState_getReg, eb_hdrC.res, LH.y6E_fold, LH.restNE_fold]
            exact LH.restNE_eval t2 (lay - 1) (by omega) (by rw [g8']; congr 1; omega)
          · cases r <;> simp_all [rv_simp, eb_hdrC.res] <;> rfl
        · intro A _ _; simp [eb_hdrC.res, rv_simp]
      refine ⟨_, (su.trans (symRun_sound eb_hdrT (Code.e_hdrT_at (im := im)) u pu (by simp [eb_hdrT.res, rv_simp]))).of_eq
        (by simp [h0, eb_hdrT.res]) (by simp [h0, eb_hdrT.res]), ?_, ?_, ?_, ?_, ?_⟩
      · exact eb_hdrT_pc u
      · rw [ClaudeWCT.WCT9.merkleTweak_lower h0, ClaudeWCT.WCT9.lowerTweak_low, eb_hdrT_x6, uor, u13]
        rewrite [← ClaudeWCT.WCT9.lowerNodeWord, Keygen.lowerNodeWord_nodeLo h0]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, ClaudeWCT.WCT9.lowerK]
        omega
      · rw [ClaudeWCT.WCT9.merkleTweak_lower h0, ClaudeWCT.WCT9.lowerTweak_high, eb_hdrT_x7]
      · exact (ru.trans (eb_hdrT_regs u)).mono (by decide)
      · exact (fu.trans (eb_hdrT_frame u)).mono (fun A _ h => by simp_all)
  obtain ⟨t4, s4, p4, m16, m24, x10, x11, x12, r4, f4⟩ : ∃ t, Steps im t3 9 9 t ∧ t.pc = pcOf 1138 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = (ClaudeWCT.WCT9.merkleTweak lay tree heap).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = (ClaudeWCT.WCT9.merkleTweak lay tree heap).extractLsb' 64 64 ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept t3 t [.x10, .x11, .x12, .x28] ∧ Frame t3 t (fun A => A = NODE + 16 ∨ A = NODE + 24) := by
    refine ⟨_, symRun_sound eb_hdrE (Code.e_hdrE_at (im := im)) t3 p3 (by simp [eb_hdrE.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_hdrE.res, E.eval]
    · simp only [Result.toState_getMem, eb_hdrE.res, NODE]
      t3n [y6]
    · simp only [Result.toState_getMem, eb_hdrE.res, NODE]
      t3n [y7]
    · simp [eb_hdrE.res, rv_simp]
    · simp [eb_hdrE.res, rv_simp]
    · simp [eb_hdrE.res, rv_simp]
    · exact eb_hdrE_regs t3
    · intro A hA hn
      simp only [NODE] at hn
      simp only [Result.toState_getMem, eb_hdrE.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
  refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by unfold hdrK; split_ifs <;> simp_all)
    (by unfold hdrK; split_ifs <;> simp_all), p4, m16, m24, x10, x11, x12,
    (((r1.trans r2).trans r3).trans r4).mono (by decide),
    (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩

theorem rl1143_spec (hpc : s.pc = pcOf 1143) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 9 9 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧ Frame s t (fun A => A = ENC ∨ A = ENC + 8) := by
  refine ⟨_, symRun_sound eblk_1143 (Code.codeAt_1143 (im := im)) s hpc (by simp [eblk_1143.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1143.res, rv_simp, h1, pcOf_and_max]
  · simp only [Result.toState_getMem, eblk_1143.res, ENC, NOUT]
    t3n []
  · simp only [Result.toState_getMem, eblk_1143.res, ENC, NOUT]
    t3n []
  · ex_regs eblk_1143.res
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, eblk_1143.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
variable {im : Image} [Code im] (s : MachineState)
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_bc : BCBlocks.Code Images.expandImage := by
  constructor <;> apply codeAt_expand_current_chunk <;> decide +kernel
namespace Grind
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (NODE NOUT)
open SigGolfCandidate.T3 (Digest nonceBytes pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.WCT9 (lowerZeroBits lowerNonceCap lowerZeroOk lowerNodeInputN lowerNodeHashN lowerNonceSearch
  lowerNodeAt)
section blocks
variable {im : Image} [Code im] (s : MachineState)

end blocks

/-! U16b grind stub: tweak-word arithmetic. -/

theorem lowTw_rec (lay tree heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3) (ht : tree < 2 ^ T3.hyperW (lay - 1))
    (hh : heap < 128) : decW (BitVec.ofNat 64 (lowTw lay tree heap)) <<< 5 = BitVec.ofNat 64 (32 * (lay - 1)) := by
  rw [lowTw_dec lay tree heap h1 h3 ht hh]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show lay - 1 < 2 ^ 64 by omega),
    Nat.shiftLeft_eq]
  omega
section cls
variable {im : Image} [Code im]

/-- After the trial-0 hash: classification of a lower node (54806 -> 54875 for heaps `≥ 32`, else 54838 with
`t4 = lowerZeroBits`), with the fold-0 heap record. -/
theorem cls_spec (u : MachineState) (hpc : u.pc = pcOf 54806) (lay tree heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3)
    (ht : tree < 2 ^ T3.hyperW (lay - 1)) (hh2 : 2 ≤ heap) (hh : heap < 128) (h10 : u.getReg .x10 = BitVec.ofNat 64 NODE)
    (hT : u.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 (lowTw lay tree heap)) :
    ∃ v k, Steps im u k k v ∧ k ≤ 47 ∧ v.pc = (if 32 ≤ heap then pcOf 54875 else pcOf 54838) ∧
      v.getReg .x7 = BitVec.ofNat 64 heap ∧ v.getReg .x31 = BitVec.ofNat 64 (lowTw lay tree heap) ∧
      (heap < 32 → v.getReg .x29 = BitVec.ofNat 64 (ClaudeWCT.WCT9.lowerZeroBits lay heap)) ∧
      RegsExcept u v [.x7, .x28, .x29, .x30, .x31] ∧
      (recThr lay ≤ heap → v.getMem (BitVec.ofNat 64 (recB lay + 24)) = BitVec.ofNat 64 heap) ∧
      Frame u v (fun A => recThr lay ≤ heap ∧ A = recB lay + 24) := by
  have hl := lowTw_lt lay tree heap h1 h3 ht hh
  obtain ⟨v1, s1, p1, x31, r1, f1⟩ := b1_spec (im := im) u hpc h10
  rw [hT, lowTw_byte1 lay tree heap h1 h3 ht hh] at p1
  rw [hT] at x31
  obtain ⟨v2, s2, p2, r2, f2⟩ := b2_spec (im := im) v1 p1
  rw [x31, if_neg (by rw [lowTw_hi lay tree heap h1 h3 ht hh]; exact not_false)] at p2
  obtain ⟨v3, s3, p3, x7, x28, x29, x30, r3, f3⟩ := b3_spec (im := im) v2 p2
  have g31 : v2.getReg .x31 = BitVec.ofNat 64 (lowTw lay tree heap) := by rw [r2.get (by decide)]; exact x31
  rw [g31, lowTw_rec lay tree heap h1 h3 ht hh] at p3 x28 x30
  rw [g31, lowTw_heap lay tree heap h1 h3 ht hh] at x7
  -- 54823 / 54824: compare with the fold-0 threshold
  obtain ⟨v4, k4, s4, hk4, p4, x7', r4, f4⟩ : ∃ v4 k4, Steps im v3 k4 k4 v4 ∧ k4 ≤ 2 ∧
      v4.pc = (if heap < recThr lay then pcOf 54826 else pcOf 54825) ∧ v4.getReg .x7 = BitVec.ofNat 64 heap ∧
      RegsExcept v3 v4 [.x29] ∧ Frame v3 v4 (fun _ => False) := by
    by_cases hl1 : lay = 1
    · subst hl1
      rw [if_neg (by simp)] at p3
      obtain ⟨v4, s4, p4, -, r4, f4⟩ := b3a_spec (im := im) v3 p3
      rw [x7, ult_ofNat heap 64 (by omega) (by omega)] at p4
      refine ⟨v4, 2, s4, le_rfl, ?_, by rw [r4.get (by decide)]; exact x7, r4, f4⟩
      rw [p4]; simp [recThr]
    · have hne : BitVec.ofNat 64 (32 * (lay - 1)) ≠ 0#64 := by
        rw [Ne, show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ofNat_inj (by omega) (by omega)]; omega
      rw [if_pos (by simpa using hne)] at p3
      obtain ⟨v4, s4, p4, r4, f4⟩ := b3b_spec (im := im) v3 p3
      rw [x7, x29, show (32#64 : Word) = BitVec.ofNat 64 32 from rfl, ult_ofNat heap 32 (by omega) (by omega)] at p4
      refine ⟨v4, 1, s4, by omega, ?_, by rw [r4.get (by decide)]; exact x7, r4.mono (by simp), f4⟩
      rw [p4]; simp [recThr, hl1]
  have g30 : v4.getReg .x30 = BitVec.ofNat 64 (recB lay) := by
    rw [r4.get (by decide), x30, ofNat_add_ofNat]; unfold recB; congr 1; omega
  obtain ⟨v5, k5, s5, hk5, hk5', p5, r5, rec5, f5⟩ : ∃ v5 k5, Steps im v4 k5 k5 v5 ∧ k5 ≤ 2 ∧ (heap < recThr lay → k5 ≤ 1) ∧
      v5.pc = pcOf 60108 ∧ RegsExcept v4 v5 [] ∧
      (recThr lay ≤ heap → v5.getMem (BitVec.ofNat 64 (recB lay + 24)) = BitVec.ofNat 64 heap) ∧
      Frame v4 v5 (fun A => recThr lay ≤ heap ∧ A = recB lay + 24) := by
    by_cases hr : heap < recThr lay
    · rw [if_pos hr] at p4
      obtain ⟨v5, s5, p5, r5, f5⟩ := b4b_spec (im := im) v4 p4
      exact ⟨v5, 1, s5, by omega, fun _ => le_rfl, p5, r5, fun h => absurd h (by omega), f5.mono (fun _ _ h => h.elim)⟩
    · rw [if_neg hr] at p4
      obtain ⟨v5, s5, p5, m5, r5, f5⟩ := b4a_spec (im := im) v4 p4 (recB lay) g30 (by unfold recB; omega)
        (by unfold recB; omega)
      exact ⟨v5, 2, s5, le_rfl, fun h => absurd h hr, p5, r5, fun _ => by rw [m5, x7'], f5.mono (fun _ _ h => ⟨by omega, h⟩)⟩
  have g31' : v5.getReg .x31 = BitVec.ofNat 64 (lowTw lay tree heap) := by
    rw [r5.get (by decide), r4.get (by decide), r3.get (by decide)]; exact g31
  obtain ⟨v6, k6, s6, hk6, p6, x7v, x29v, r6, f6⟩ := tiers_spec (im := im) v5 p5 lay tree heap h1 h3 ht hh2 hh g31'
  have hrec6 : recThr lay ≤ heap → v6.getMem (BitVec.ofNat 64 (recB lay + 24)) = BitVec.ofNat 64 heap := fun h => by
    rw [f6.get (by unfold recB; omega) (fun h => h)]; exact rec5 h
  have hk : 5 + 3 + 16 + k4 + k5 + k6 ≤ 47 := by
    rcases hk6 with hk6 | ⟨hl, hh4, hk6⟩
    · omega
    · have hr1 : recThr 1 = 64 := rfl
      have := hk5' (by rw [hl, hr1]; omega)
      omega
  refine ⟨v6, 5 + 3 + 16 + k4 + k5 + k6, ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6, hk, p6,
    x7v, ?_, x29v, ?_, hrec6, ?_⟩
  · rw [r6.get (by decide)]; exact g31'
  · exact (((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).mono (by decide)
  · exact (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).mono (fun A _ h => by
      rcases h with ((((h | h) | h) | h) | h) | h
      all_goals first | exact h.elim | exact h)
end cls

/-! U16b grind stub: loop setup and the zero test. -/

section setup
variable {im : Image} [Code im]

end setup

/-! U16b grind stub: node input, zero test, trial invariant. -/

section sim
variable {im : Image} {sk : BitVec 256}
end sim

section found
variable {im : Image} [Code im]

/-- E11: the post-grind slot code (60128..60141) from `t5 = recB lay`: `t5 = recA lay heap`, then 54872. -/
theorem pg_spec (u : MachineState) (hpc : u.pc = pcOf 60128) (lay tree heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3)
    (ht : tree < 2 ^ T3.hyperW (lay - 1)) (hh2 : 2 ≤ heap) (hh : heap < 32)
    (h31 : u.getReg .x31 = BitVec.ofNat 64 (lowTw lay tree heap)) (h30 : u.getReg .x30 = BitVec.ofNat 64 (recB lay)) :
    ∃ v k, Steps im u k k v ∧ k ≤ 14 ∧ v.pc = pcOf 54872 ∧ v.getReg .x30 = BitVec.ofNat 64 (recA lay heap) ∧
      RegsExcept u v [.x7, .x28, .x29, .x30] ∧ Frame u v (fun _ => False) := by
  obtain ⟨v1, s1, p1, x7, x29a, r1, f1⟩ := pA_spec (im := im) u hpc
  rw [h31, lowTw_heap lay tree heap h1 h3 ht (by omega), ult_ofNat heap 16 (by omega) (by omega)] at p1
  rw [h31, lowTw_heap lay tree heap h1 h3 ht (by omega)] at x7
  have g30 : v1.getReg .x30 = BitVec.ofNat 64 (recB lay) := by rw [r1.get (by decide)]; exact h30
  have hR := recA_cases lay heap h1 h3
  by_cases h16 : 16 ≤ heap
  · rw [if_neg (by simp; omega)] at p1
    obtain ⟨v2, s2, p2, x30, r2, f2⟩ := pE_spec (im := im) v1 p1
    refine ⟨v2, 7, s1.trans s2, by omega, p2, ?_, (r1.trans r2).mono (by decide),
      (f1.trans f2).mono (fun _ _ h => by rcases h with h | h <;> exact h)⟩
    rw [x30, g30, x29a, show (256#64 : Word) = BitVec.ofNat 64 256 from rfl, ofNat_add_ofNat]
    unfold recA; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [if_pos (by simp; omega)] at p1
  obtain ⟨v2, s2, p2, x29b, r2, f2⟩ := pB_spec (im := im) v1 p1
  rw [x7, ult_ofNat heap 4 (by omega) (by omega)] at p2
  have g30' : v2.getReg .x30 = BitVec.ofNat 64 (recB lay) := by rw [r2.get (by decide)]; exact g30
  have g7 : v2.getReg .x7 = BitVec.ofNat 64 heap := by rw [r2.get (by decide)]; exact x7
  by_cases h4 : heap < 4
  · rw [if_pos (by simp; omega)] at p2
    obtain ⟨v3, s3, p3, x30, r3, f3⟩ := pE_spec (im := im) v2 p2
    refine ⟨v3, 10, (s1.trans s2).trans s3, by omega, p3, ?_, ((r1.trans r2).trans r3).mono (by decide),
      ((f1.trans f2).trans f3).mono (fun _ _ h => by rcases h with (h | h) | h <;> exact h)⟩
    rw [x30, g30', x29b, show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ofNat_add_ofNat]
    unfold recA; rw [if_pos h4]
  rw [if_neg (by simp; omega)] at p2
  obtain ⟨v3, s3, p3, x29c, r3, f3⟩ := pC_spec (im := im) v2 p2
  rw [g7, ult_ofNat heap 8 (by omega) (by omega)] at p3
  have g30'' : v3.getReg .x30 = BitVec.ofNat 64 (recB lay) := by rw [r3.get (by decide)]; exact g30'
  by_cases h8 : heap < 8
  · rw [if_pos (by simp; omega)] at p3
    obtain ⟨v4, s4, p4, x30, r4, f4⟩ := pE_spec (im := im) v3 p3
    refine ⟨v4, 13, ((s1.trans s2).trans s3).trans s4, by omega, p4, ?_, (((r1.trans r2).trans r3).trans r4).mono
      (by decide), (((f1.trans f2).trans f3).trans f4).mono (fun _ _ h => by rcases h with ((h | h) | h) | h <;> exact h)⟩
    rw [x30, g30'', x29c, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]
    unfold recA; rw [if_neg h4, if_pos h8]
  rw [if_neg (by simp; omega)] at p3
  obtain ⟨v4, s4, p4, x30, r4, f4⟩ := pD_spec (im := im) v3 p3
  refine ⟨v4, 14, ((s1.trans s2).trans s3).trans s4, le_rfl, p4, ?_, (((r1.trans r2).trans r3).trans r4).mono
    (by decide), (((f1.trans f2).trans f3).trans f4).mono (fun _ _ h => by rcases h with ((h | h) | h) | h <;> exact h)⟩
  rw [x30, g30'', show (16#64 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
  unfold recA; rw [if_neg h4, if_neg h8, if_pos (by omega)]

/-- The found exit 54856 .. 1139: record the nonce `n` (the pad), clear the pad, restore and clear `SAVE`. -/
theorem found_spec {t u : MachineState} {lay tree heap n : Nat} {l r : Digest} (F : StubIn t lay tree heap l r)
    (hg : lowerZeroBits lay heap ≠ 0) (hpc : u.pc = pcOf 54856) (hr : RegsExcept t u [.x7, .x28, .x29, .x30, .x31])
    (hpad : u.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n)
    (s0 : u.getMem (BitVec.ofNat 64 1000) = t.getReg .x7) (s1 : u.getMem (BitVec.ofNat 64 1008) = t.getReg .x28)
    (s2 : u.getMem (BitVec.ofNat 64 1016) = t.getReg .x29) (s3 : u.getMem (BitVec.ofNat 64 1024) = t.getReg .x30)
    (s4 : u.getMem (BitVec.ofNat 64 1032) = t.getReg .x31)
    (hf : Frame t u (fun A => A = NODE + 32 ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨ SaveW A)) {v : Digest}
    (hv : DigAt u (NOUT + if ClaudeWCT.WCT9.lowerHigh lay heap then 16 else 0) v) :
    ∃ w k, Steps im u k k w ∧ k ≤ 42 ∧ StubOut t lay heap (n, v) w := by
  have h1 := F.h1; have h3 := F.h3; have hh := F.hh; have hh2 := F.hh2; have ht := F.ht
  have h32 : heap < 32 := by
    by_contra hc; apply hg; unfold ClaudeWCT.WCT9.lowerZeroBits; rw [if_pos (by omega)]
  have g10 : u.getReg .x10 = BitVec.ofNat 64 NODE := by rw [hr.get (by decide)]; exact F.x10
  have g16 : u.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 (lowTw lay tree heap) := by
    rw [hf.get (by decide) (by unfold SaveW; simp only [NODE, NOUT]; omega)]; exact F.w16
  obtain ⟨u1, su1, pu1, x31, x30, r1, f1⟩ := f1_spec (im := im) u hpc g10
  rw [g16] at x31
  rw [g16, lowTw_rec lay tree heap h1 h3 ht hh, ofNat_add_ofNat] at x30
  have e30 : u1.getReg .x30 = BitVec.ofNat 64 (recB lay) := by rw [x30]; unfold recB; congr 1; omega
  obtain ⟨u2, k2, su2, hk2, pu2, x30', r2, f2⟩ := pg_spec (im := im) u1 pu1 lay tree heap h1 h3 ht hh2 h32 x31 e30
  have hrc := recA_cases lay heap h1 h3
  have f12 : Frame u u2 (fun _ => False) := (f1.trans f2).mono (fun _ _ h => by rcases h with h | h <;> exact h)
  obtain ⟨w, sw, pw, mrec, mpad, x7w, x28w, x29w, x30w, x31w, msave, rw, fw⟩ :=
    f3b_spec (im := im) u2 pu2 (by rw [r2.get (by decide), r1.get (by decide)]; exact g10) (recA lay heap)
      x30' hrc.1 hrc.2.1 hrc.2.2.1
  have fu : ∀ A, A < 2 ^ 64 → A ≠ recA lay heap → A ≠ NODE + 32 → ¬ SaveW A →
      w.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := fun A hA a b c =>
    (fw.get hA (by rintro (h | h | h) <;> contradiction)).trans (f12.get hA (fun h => h))
  refine ⟨w, 14 + k2 + 14, (su1.trans su2).trans sw, by omega, ⟨pw, ?_, ?_, mpad, msave, fun _ => ?_, ?_, ?_⟩⟩
  · intro x _
    by_cases hx : x ∈ [Reg.x7, .x28, .x29, .x30, .x31]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · rw [x7w, f12.get (by decide) (fun h => h), s0]
      · rw [x28w, f12.get (by decide) (fun h => h), s1]
      · rw [x29w, f12.get (by decide) (fun h => h), s2]
      · rw [x30w, f12.get (by decide) (fun h => h), s3]
      · rw [x31w, f12.get (by decide) (fun h => h), s4]
    · rw [rw.get hx, r2.get (fun h => hx ((by decide : ∀ y ∈ [Reg.x7, .x28, .x29, .x30], y ∈ [Reg.x7, .x28, .x29, .x30, .x31]) x h)),
        r1.get (fun h => hx ((by decide : ∀ y ∈ [Reg.x28, .x30, .x31], y ∈ [Reg.x7, .x28, .x29, .x30, .x31]) x h)),
        hr.get hx]
  · have hoff : (NOUT + if ClaudeWCT.WCT9.lowerHigh lay heap then 16 else 0) + 16 ≤ NOUT + 32 := by split_ifs <;> omega
    exact ⟨(fu _ (by split_ifs <;> decide) (by unfold recA recB NOUT; split_ifs <;> omega)
      (by simp only [NODE, NOUT]; split_ifs <;> omega) (by unfold SaveW NOUT; split_ifs <;> omega)).trans hv.1,
      (fu _ (by split_ifs <;> decide) (by unfold recA recB NOUT; split_ifs <;> omega)
      (by simp only [NODE, NOUT]; split_ifs <;> omega) (by unfold SaveW NOUT; split_ifs <;> omega)).trans hv.2⟩
  · rw [mrec, f12.get (by decide) (fun h => h), hpad]
  · intro hth; exfalso; unfold recThr at hth; split_ifs at hth <;> omega
  · intro A hA hn
    simp only [not_or] at hn
    by_cases hp : A = NODE + 32
    · subst hp; rw [mpad, F.w32]
    · rw [fu A hA (fun e => hn.2.2.1 ⟨hg, e⟩) hp hn.2.1, hf.get hA (by
        rintro (h | h | h); exact hp h; exact hn.1 h; exact hn.2.1 h)]
end found

/-! U16b grind stub: the search loop and the whole stub (word 1138 -> 1139). -/

section loop
variable {im : Image} [Code im] (sk : BitVec 256)

theorem g_check {t u : MachineState} {lay tree heap n : Nat} {l r : Digest} {a : BitVec 256}
    (F : StubIn t lay tree heap l r) (hg : lowerZeroBits lay heap ≠ 0) (hu : GTrial t lay heap n a u) :
    ∃ u1, Steps im u 3 3 u1 ∧
      u1.pc = (if lowerZeroOk lay heap (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.lowerHigh lay heap) a) = true
        then pcOf 54856 else pcOf 54850) ∧ RegsExcept u u1 [.x28] ∧ Frame u u1 (fun _ => False) := by
  have hb := zb_range lay heap hg
  have he := high_eq lay heap F.h3
  set off := (if ClaudeWCT.WCT9.lowerHigh lay heap then 16 else 0) with hoff
  have hoff' : off = 0 ∨ off = 16 := by rw [hoff]; split_ifs <;> simp
  have h12 : u.getReg .x12 = BitVec.ofNat 64 NOUT := by rw [hu.regs.get (by decide)]; exact F.x12
  obtain ⟨u1, s1, p1, r1, f1⟩ := lc_spec (im := im) u hu.pc (off + 15) (by omega) NOUT h12 (by decide) (by decide)
    (by rw [hu.x30, ← he]; congr 1)
  refine ⟨u1, s1, ?_, r1, f1⟩
  rw [p1, show NOUT + (off + 15) - 7 = NOUT + off + 8 by omega, hu.out.2, hu.x29]
  unfold ClaudeWCT.WCT9.lowerZeroOk
  by_cases hz : (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.lowerHigh lay heap) a).toNat / 2 ^ (128 - lowerZeroBits lay heap) = 0
  · rw [if_pos ((zero_test _ _ hb.1 hb.2).mpr hz), if_pos (by simp [hz])]
  · rw [if_neg (fun h => hz ((zero_test _ _ hb.1 hb.2).mp h)), if_neg (by simp [hz])]

theorem g_loop {t : MachineState} {lay tree heap : Nat} {l r : Digest} (F : StubIn t lay tree heap l r)
    (hg : lowerZeroBits lay heap ≠ 0) : ∀ fuel n (a : BitVec 256) u, GTrial t lay heap n a u →
      n + fuel + 1 = lowerNonceCap lay heap →
      TBSim im sk u (16 * fuel + 48)
        (gTail lay tree heap l r fuel n (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.lowerHigh lay heap) a))
        (StubOut t lay heap) := by
  have hb := zb_range lay heap hg
  have hcap := cap_le lay heap
  have h3 := F.h3
  -- the found exit from 54856 with the pad `n`
  have exitF : ∀ n (a : BitVec 256) u u1 k1, GTrial t lay heap n a u → Steps im u k1 k1 u1 → k1 ≤ 6 →
      u1.pc = pcOf 54856 → RegsExcept u u1 [.x7, .x28] → Frame u u1 (fun _ => False) →
      TBSim im sk u 48 (pure (n, ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.lowerHigh lay heap) a)) (StubOut t lay heap) := by
    intro n a u u1 k1 hu s1 hk1 p1 r1 f1
    obtain ⟨w, k, sw, hk, hw⟩ := found_spec (im := im) F hg p1 ((hu.regs.trans r1).mono (by decide))
      (by rw [f1.get (by decide) (fun h => h)]; exact hu.pad)
      (by rw [f1.get (by decide) (fun h => h)]; exact hu.s0) (by rw [f1.get (by decide) (fun h => h)]; exact hu.s1)
      (by rw [f1.get (by decide) (fun h => h)]; exact hu.s2) (by rw [f1.get (by decide) (fun h => h)]; exact hu.s3)
      (by rw [f1.get (by decide) (fun h => h)]; exact hu.s4)
      ((hu.frame.trans f1).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim))
      (hu.out.frame f1 (by split_ifs <;> decide) (fun h => h) (fun h => h))
    exact (tb_pure_steps (sk := sk) (s1.trans sw) hw).mono
      (by omega) (fun _ _ h => h)
  intro fuel
  induction fuel with
  | zero =>
    intro n a u hu hn
    obtain ⟨u1, s1, p1, r1, f1⟩ := g_check (im := im) F hg hu
    by_cases hz : lowerZeroOk lay heap (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.lowerHigh lay heap) a) = true
    · rw [if_pos hz] at p1
      exact exitF n a u u1 3 hu s1 (by omega) p1 (r1.mono (by decide)) f1
    · rw [if_neg hz] at p1
      obtain ⟨u2, s2, p2, -, r2, f2⟩ := l2_spec (im := im) u1 p1 (by rw [r1.get (by decide), hu.regs.get (by decide)]; exact F.x10)
        n (lowerNonceCap lay heap) (by omega) (by omega) (by rw [f1.get (by decide) (fun h => h)]; exact hu.pad)
        (by rw [r1.get (by decide)]; exact hu.x31)
      rw [if_pos (by omega)] at p2
      exact exitF n a u u2 6 hu (s1.trans s2) le_rfl p2 ((r1.trans r2).mono (by decide))
        ((f1.trans f2).mono (fun _ _ h => by rcases h with h | h <;> exact h))
  | succ fuel ih =>
    intro n a u hu hn
    obtain ⟨u1, s1, p1, r1, f1⟩ := g_check (im := im) F hg hu
    by_cases hz : lowerZeroOk lay heap (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.lowerHigh lay heap) a) = true
    · rw [if_pos hz] at p1
      have e : gTail lay tree heap l r (fuel + 1) n (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.lowerHigh lay heap) a) =
          pure (n, ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.lowerHigh lay heap) a) := by simp only [gTail, hz, if_true]
      rw [e]
      exact (exitF n a u u1 3 hu s1 (by omega) p1 (r1.mono (by decide)) f1).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at p1
      have g10 : u1.getReg .x10 = BitVec.ofNat 64 NODE := by rw [r1.get (by decide), hu.regs.get (by decide)]; exact F.x10
      obtain ⟨u2, s2, p2, x7, r2, f2⟩ := l2_spec (im := im) u1 p1 g10
        n (lowerNonceCap lay heap) (by omega) (by omega) (by rw [f1.get (by decide) (fun h => h)]; exact hu.pad)
        (by rw [r1.get (by decide)]; exact hu.x31)
      rw [if_neg (by omega)] at p2
      obtain ⟨u3, s3, p3, m32, r3, f3, fe3⟩ := l3_spec (im := im) u2 p2 (by rw [r2.get (by decide)]; exact g10)
      rw [x7] at m32
      have r03 : RegsExcept t u3 ([.x7, .x28, .x29, .x30, .x31] ++ [.x28] ++ [.x7] ++ []) :=
        ((hu.regs.trans r1).trans r2).trans r3
      have g3 : ∀ x, x ∉ [Reg.x7, .x28, .x29, .x30, .x31] → u3.getReg x = t.getReg x := fun x hx => r03.get
        (fun h => hx ((by decide : ∀ y ∈ ([Reg.x7, .x28, .x29, .x30, .x31] ++ [.x28] ++ [.x7] ++ []),
          y ∈ [Reg.x7, .x28, .x29, .x30, .x31]) x h))
      have f03 : Frame t u3 (fun A => A = NODE + 32 ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨ SaveW A) :=
        (((hu.frame.trans f1).trans f2).trans f3).mono (fun A _ h => by
          rcases h with ((h | h) | h) | h
          · exact h
          · exact h.elim
          · exact h.elim
          · exact Or.inl h)
      have fu3 : Frame u u3 (fun A => A = NODE + 32) := ((f1.trans f2).trans f3).mono (fun A _ h => by
          rcases h with ((h | h) | h) <;> first | exact h.elim | exact h)
      have hq := hashInput_N F f03 (fun X h1 h2 h3 hw => by
          rcases hw with hw | hw | hw
          · exact h3 hw
          · simp only [NODE, NOUT] at h2 hw; omega
          · unfold SaveW at hw; simp only [NODE] at h1; omega)
        (n + 1) (by omega) (by rw [g3 _ (by decide)]; exact F.x10) (by rw [g3 _ (by decide)]; exact F.x11) m32
      have h12 : u3.getReg .x12 = BitVec.ofNat 64 NOUT := by rw [g3 _ (by decide)]; exact F.x12
      have hv : hashArgumentsValid u3 = true := hashArgs_const u3 NODE 64 NOUT (by rw [g3 _ (by decide)]; exact F.x10)
        (by rw [g3 _ (by decide)]; exact F.x11) h12 (by decide) (by decide) (by decide) (by decide) (by decide)
      have h5 : u3.getReg .x5 = 0 := by rw [g3 _ (by decide)]; exact F.x5
      have e : gTail lay tree heap l r (fuel + 1) n (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.lowerHigh lay heap) a) =
          ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.lowerHigh lay heap) (lowerNodeInputN lay tree heap (n + 1) l r) >>=
            gTail lay tree heap l r fuel (n + 1) := by
        rw [gTail.eq_2, if_neg hz, search_eq]
      rw [e]
      refine (TBSim.steps (s1.trans (s2.trans s3)) (tb_half (im := im) (sk := sk) _ fe3 h5 hv hq
        (W := 1 + (16 * fuel + 48)) (fun a' => ?_))).mono (by rw [inputN_blocks]; omega) (fun _ _ h => h)
      have hwf := Frame.writeHash u3 a' NOUT h12 (by decide)
      obtain ⟨w, s4, p4, r4, f4⟩ := l4_spec (im := im) (writeHash u3 a') (by rw [pc_writeHash, p3, pcOf_add4])
      have rw0 : RegsExcept u3 (writeHash u3 a') [] := fun x _ => getReg_writeHash u3 a' x
      have fw : Frame u3 w (fun A => NOUT ≤ A ∧ A < NOUT + 32) := (hwf.trans f4).mono (fun A _ h => by
        rcases h with h | h; exact h; exact h.elim)
      have fwS : ∀ A, A < 2 ^ 64 → ¬ (NOUT ≤ A ∧ A < NOUT + 32) → A ≠ NODE + 32 →
          w.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := fun A hA h1 h2 =>
        (fw.get hA h1).trans (fu3.get hA h2)
      refine TBSim.steps s4 (ih (n + 1) a' w ⟨p4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (by omega))
      · exact (r03.trans (rw0.trans r4)).mono (by decide)
      · rw [r4.get (by decide), getReg_writeHash, r3.get (by decide), r2.get (by decide), r1.get (by decide)]; exact hu.x29
      · rw [r4.get (by decide), getReg_writeHash, r3.get (by decide), r2.get (by decide), r1.get (by decide)]; exact hu.x30
      · rw [r4.get (by decide), getReg_writeHash, r3.get (by decide), r2.get (by decide), r1.get (by decide)]; exact hu.x31
      · rw [fw.get (by decide) (by simp only [NODE, NOUT]; omega), m32]
      · rw [fwS _ (by decide) (by simp only [NOUT]; omega) (by simp only [NODE]; omega)]; exact hu.s0
      · rw [fwS _ (by decide) (by simp only [NOUT]; omega) (by simp only [NODE]; omega)]; exact hu.s1
      · rw [fwS _ (by decide) (by simp only [NOUT]; omega) (by simp only [NODE]; omega)]; exact hu.s2
      · rw [fwS _ (by decide) (by simp only [NOUT]; omega) (by simp only [NODE]; omega)]; exact hu.s3
      · rw [fwS _ (by decide) (by simp only [NOUT]; omega) (by simp only [NODE]; omega)]; exact hu.s4
      · exact (f03.trans fw).mono (fun A _ h => by rcases h with h | h; exact h; exact Or.inr (Or.inl h))
      · exact (dig_half u3 a' NOUT h12 (by decide) _).frame f4 (by split_ifs <;> decide) (fun h => h) (fun h => h)

/-- The U16b fold hash of a lower node (word 1138 -> the stub -> 1139) refines `lowerNodeAt`. -/
theorem stub_lower {t : MachineState} {lay tree heap : Nat} {l r : Digest} (F : StubIn t lay tree heap l r) :
    TBSim im sk t (stubW lay heap) (lowerNodeAt lay tree heap l r) (StubOut t lay heap) := by
  have h1 := F.h1; have h3 := F.h3; have hh := F.hh; have hh2 := F.hh2; have ht := F.ht
  obtain ⟨t1, s1, p1, r1, f1⟩ := j1138_spec (im := im) t F.pc
  obtain ⟨t2, s2, p2, r2, sv0, sv1, sv2, sv3, sv4, f2, fe2⟩ := hd_spec (im := im) t1 p1
  have r02 : RegsExcept t t2 [] := (r1.trans r2).mono (by decide)
  have f02 : Frame t t2 SaveW := (f1.trans f2).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
  have g2 : ∀ x, t2.getReg x = t.getReg x := fun x => r02.get (by simp)
  have hq := hashInput_N F f02 (fun X h1 h2 _ hw => by unfold SaveW at hw; simp only [NODE] at h1; omega) 0
    (by norm_num) (by rw [g2]; exact F.x10) (by rw [g2]; exact F.x11)
    (by rw [f02.get (by decide) (by unfold SaveW; simp only [NODE]; omega)]; exact F.w32)
  have h12 : t2.getReg .x12 = BitVec.ofNat 64 NOUT := by rw [g2]; exact F.x12
  have hv : hashArgumentsValid t2 = true := hashArgs_const t2 NODE 64 NOUT (by rw [g2]; exact F.x10)
    (by rw [g2]; exact F.x11) h12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 : t2.getReg .x5 = 0 := by rw [g2]; exact F.x5
  have hT : ∀ a : BitVec 256, (writeHash t2 a).getMem (BitVec.ofNat 64 (NODE + 16)) =
      BitVec.ofNat 64 (lowTw lay tree heap) := fun a => by
    rw [(Frame.writeHash t2 a NOUT h12 (by decide)).get (by decide) (by simp only [NODE, NOUT]; omega),
      f02.get (by decide) (by unfold SaveW; simp only [NODE]; omega)]; exact F.w16
  have hthr : 32 ≤ recThr lay := by unfold recThr; split_ifs <;> omega
  have hpc2 : ∀ a : BitVec 256, (writeHash t2 a).pc = pcOf 54806 := fun a => by rw [pc_writeHash, p2, pcOf_add4]
  by_cases hg : lowerZeroBits lay heap = 0
  · -- off the ground: one hash, classification, restore
    have h16 : 32 ≤ heap := by
      by_contra hc
      have := hg
      unfold ClaudeWCT.WCT9.lowerZeroBits at this
      split_ifs at this <;> omega
    have e : lowerNodeAt lay tree heap l r = ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.lowerHigh lay heap)
        (lowerNodeInputN lay tree heap 0 l r) >>= fun v => pure (0, v) := by
      unfold ClaudeWCT.WCT9.lowerNodeAt
      rw [if_pos hg, ClaudeWCT.WCT9.lowerNodeInputN_zero, map_eq_bind_pure_comp]
      rfl
    rw [e, show stubW lay heap = 1 + 5 + (8 * (toQ (pad64 (lowerNodeInputN lay tree heap 0 l r))).blocks + 58) by
      rw [inputN_blocks]; unfold stubW; rw [if_pos hg]]
    refine TBSim.steps (s1.trans s2) (tb_half (im := im) (sk := sk) _ fe2 h5 hv hq (fun a => ?_))
    obtain ⟨v, k, sv, hk, pv, x7v, x31v, -, rv, recv, fv⟩ := cls_spec (im := im) (writeHash t2 a) (hpc2 a) lay tree heap
      h1 h3 ht hh2 hh (by rw [getReg_writeHash, g2]; exact F.x10) (hT a)
    rw [if_pos h16] at pv
    obtain ⟨w, sw, pw, x7w, x28w, x29w, x30w, x31w, msave, rw, fw⟩ := dn_spec (im := im) v pv
    have hwf := Frame.writeHash t2 a NOUT h12 (by decide)
    have fS : ∀ A, A < 2 ^ 64 → ¬ SaveW A → ¬ (NOUT ≤ A ∧ A < NOUT + 32) → ¬ (recThr lay ≤ heap ∧ A = recB lay + 24) →
        w.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A hA a1 a2 a3 =>
      (((fw.get hA a1).trans (fv.get hA a3)).trans (hwf.get hA a2)).trans (f02.get hA a1)
    have gS : ∀ A x, A < 2 ^ 64 → SaveW A → t2.getMem (BitVec.ofNat 64 A) = x →
        v.getMem (BitVec.ofNat 64 A) = x := fun A x hA hs h => by
      rw [fv.get hA (by unfold SaveW at hs; unfold recB; omega), hwf.get hA (by unfold SaveW at hs; simp only [NOUT]; omega), h]
    refine (TBSim.steps (sv.trans sw) (TBSim.pure ⟨pw, ?_, ?_, ?_, msave, fun h => absurd hg h, ?_, ?_⟩)).mono
      (by omega) (fun _ _ h => h)
    · intro x _
      by_cases hx : x ∈ [Reg.x7, .x28, .x29, .x30, .x31]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · rw [x7w, gS _ _ (by decide) (by unfold SaveW; omega) sv0, r1.get (by simp)]
        · rw [x28w, gS _ _ (by decide) (by unfold SaveW; omega) sv1, r1.get (by simp)]
        · rw [x29w, gS _ _ (by decide) (by unfold SaveW; omega) sv2, r1.get (by simp)]
        · rw [x30w, gS _ _ (by decide) (by unfold SaveW; omega) sv3, r1.get (by simp)]
        · rw [x31w, gS _ _ (by decide) (by unfold SaveW; omega) sv4, r1.get (by simp)]
      · rw [rw.get hx, rv.get hx, getReg_writeHash, g2]
    · have hd := dig_half t2 a NOUT h12 (by decide) (ClaudeWCT.WCT9.lowerHigh lay heap)
      exact (hd.frame fv (by split_ifs <;> decide) (by unfold recB NOUT; split_ifs <;> omega)
        (by unfold recB NOUT; split_ifs <;> omega)).frame fw (by split_ifs <;> decide)
        (by unfold SaveW NOUT; split_ifs <;> omega) (by unfold SaveW NOUT; split_ifs <;> omega)
    · rw [fS _ (by decide) (by unfold SaveW; simp only [NODE]; omega) (by simp only [NODE, NOUT]; omega)
        (by unfold recB; simp only [NODE]; omega)]; exact F.w32
    · intro hr; rw [fw.get (by unfold recB; omega) (by unfold SaveW recB; omega)]; exact recv hr
    · intro A hA hn; simp only [not_or] at hn
      exact fS A hA hn.2.1 hn.1 hn.2.2.2
  · -- ground: trial 0, classification, setup, the search loop
    have hb := zb_range lay heap hg
    have h16 : heap < 32 := by
      by_contra hc; apply hg; unfold ClaudeWCT.WCT9.lowerZeroBits; rw [if_pos (by omega)]
    have hcap := cap_le lay heap
    have hcap1 : 1 ≤ lowerNonceCap lay heap := by
      unfold ClaudeWCT.WCT9.lowerNonceCap; have := Nat.one_le_two_pow (n := lowerZeroBits lay heap); omega
    have e : lowerNodeAt lay tree heap l r = ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.lowerHigh lay heap)
        (lowerNodeInputN lay tree heap 0 l r) >>= gTail lay tree heap l r (lowerNonceCap lay heap - 1) 0 := by
      unfold ClaudeWCT.WCT9.lowerNodeAt; rw [if_neg hg, search_eq]
    rw [e, show stubW lay heap = 1 + 5 + (8 * (toQ (pad64 (lowerNodeInputN lay tree heap 0 l r))).blocks +
      (56 + (16 * (lowerNonceCap lay heap - 1) + 48))) by rw [inputN_blocks]; unfold stubW; rw [if_neg hg]; omega]
    refine TBSim.steps (s1.trans s2) (tb_half (im := im) (sk := sk) _ fe2 h5 hv hq (fun a => ?_))
    obtain ⟨v, k, sv, hk, pv, x7v, x31v, x29v, rv, -, fv⟩ := cls_spec (im := im) (writeHash t2 a) (hpc2 a) lay tree heap
      h1 h3 ht hh2 hh (by rw [getReg_writeHash, g2]; exact F.x10) (hT a)
    rw [if_neg (by omega)] at pv
    obtain ⟨u, k', su, hk', pu, x29u, x30u, x31u, ru, fu⟩ := setup_spec (im := im) v pv lay heap hh2 h16 h1
      x7v (x29v h16) (by rw [rv.get (by decide), getReg_writeHash, g2]; exact F.x12)
    have hwf := Frame.writeHash t2 a NOUT h12 (by decide)
    have fvu : Frame (writeHash t2 a) u (fun _ => False) := (fv.trans fu).mono (fun A _ h => by
      rcases h with h | h
      · exact absurd h.1 (by omega)
      · exact h.elim)
    have gS : ∀ A x, A < 2 ^ 64 → SaveW A → t2.getMem (BitVec.ofNat 64 A) = x →
        u.getMem (BitVec.ofNat 64 A) = x := fun A x hA hs h => by
      rw [fvu.get hA (fun h => h), hwf.get hA (by unfold SaveW at hs; simp only [NOUT]; omega), h]
    have hst : GTrial t lay heap 0 a u := by
      refine ⟨pu, ?_, x29u, x30u, x31u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have rw0 : RegsExcept t2 (writeHash t2 a) [] := fun x _ => getReg_writeHash t2 a x
        exact ((r02.trans rw0).trans (rv.trans ru)).mono (by decide)
      · rw [fvu.get (by decide) (fun h => h), hwf.get (by decide) (by simp only [NODE, NOUT]; omega),
          f02.get (by decide) (by unfold SaveW; simp only [NODE]; omega), F.w32]; rfl
      · rw [gS _ _ (by decide) (by unfold SaveW; omega) sv0, r1.get (by simp)]
      · rw [gS _ _ (by decide) (by unfold SaveW; omega) sv1, r1.get (by simp)]
      · rw [gS _ _ (by decide) (by unfold SaveW; omega) sv2, r1.get (by simp)]
      · rw [gS _ _ (by decide) (by unfold SaveW; omega) sv3, r1.get (by simp)]
      · rw [gS _ _ (by decide) (by unfold SaveW; omega) sv4, r1.get (by simp)]
      · exact ((f02.trans hwf).trans fvu).mono (fun A _ h => by
          rcases h with (h | h) | h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)
          · exact h.elim)
      · exact (dig_half t2 a NOUT h12 (by decide) _).frame fvu (by split_ifs <;> decide) (fun h => h) (fun h => h)
    exact (TBSim.steps (sv.trans su) (g_loop (im := im) sk F hg (lowerNonceCap lay heap - 1) 0 a u hst
      (by omega))).mono (by omega) (fun _ _ h => h)
end loop

/-! U16b grind stub: the pass-through of a non-lower node (top tree). -/

section pass
variable {im : Image} [Code im] {sk : BitVec 256}

end pass

end Grind


end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_Basic ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
section tb
variable {image : Image} {sk : BitVec 256}
end tb
end SigGolfCandidate.T3M.Expand
end
-- ==== merged from T3M_Expand_LayerChain ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chain chainInput shortHash pad64 zero16 header)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS)
set_option autoImplicit false
section chain
variable {sk : BitVec 256}
end chain
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [Code im] [BCBlocks.Code im] [PackedBlocks.Code im] {sk : BitVec 256}
theorem tb_halfHash_bind' {β : Type} {s : MachineState} {input : List UInt8} {W : Nat} (high : Bool)
    {f : Digest → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash s a) W (f (ClaudeWCT.WCT9.halfOf high a)) Q) :
    TBSim im sk s (8 * (toQ (pad64 input)).blocks + W) (ClaudeWCT.WCT9.halfHash high input >>= f) Q := by
  rw [ClaudeWCT.WCT9.halfHash_eq, bind_assoc]
  simp only [pure_bind]
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
/-- Witness stack: one chain step (loop head 1031, header 1032..1040, the step block 49300..49337 and, on the F
path, the C3 tail) computes `halfHash (chainHigh) (chainInputW)`; at most 60 instructions + HASH. -/
theorem chain_step (lay : Layer) (tree leaf i st e : Nat)
    (hrH : tree * 2 ^ T3.height lay + leaf < 2 ^ T3.hyperW lay.val) (hf : leaf < 2 ^ T3.height lay) (hst : st < e) (he : e ≤ 7)
    (hcap : e ≤ SigGolfCandidate.T3.maxDigit lay i)
    (hi : i < 64) (hiT : lay = 0 → i ≤ 50) (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1031)
    (hc : ChainCtx lay.val tree leaf i t) (h20 : t.getReg .x20 = BitVec.ofNat 64 st)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 e) (hv : DigAt t (CHAIN + 48) v) :
    TBSim im sk t (stepW lay) (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i st)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v))
      (fun v' u => u.pc = pcOf 1031 ∧ u.getReg .x20 = BitVec.ofNat 64 (st + 1) ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
        ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) v' ∧ RegsExcept t u stepRegs ∧ Frame t u StepW) := by
  have hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31 :=
    lt_of_lt_of_le hrH (Nat.pow_le_pow_right (by norm_num) (T3.hyperW_le _))
  have hlay := lay.isLt
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1031_spec (im := im) t hpc st e (by omega) (by omega) h20 h21
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, a28, m16, m24, r2, f2⟩ := rl1032_spec (im := im) t1 p1 lay tree leaf i st hrH hf hi (by omega)
    (by rw [r1.get (by simp)]; exact hc.x8) (by rw [r1.get (by simp)]; exact hc.x19)
    (by rw [r1.get (by simp)]; exact hc.x9) (by rw [r1.get (by simp)]; exact hc.x18)
    (by rw [r1.get (by simp)]; exact h20)
  have f12 : Frame t t2 (fun A => A = CHAIN + 16 ∨ A = CHAIN + 24) := (f1.trans f2).mono (fun A _ h => by
    rcases h with h | h; exact h.elim; exact h)
  have r12 : RegsExcept t t2 [.x6, .x7, .x10, .x11, .x12, .x28, .x30] := (r1.trans r2).mono (by simp)
  have g2 : ∀ r, r ∉ stepRegs → t2.getReg r = t.getReg r := fun r hr =>
    r12.get (not_mem_of_sub (by simp [stepRegs]) hr)
  obtain ⟨u0, s0, p0, r0, f0⟩ := sel_spec (im := im) t2 p2 lay.val (by omega)
    (by rw [g2 _ (by simp [stepRegs])]; exact hc.x8)
  have g19 : u0.getReg .x19 = BitVec.ofNat 64 i := by
    rw [r0.get (by simp), g2 _ (by simp [stepRegs])]; exact hc.x19
  have hK := expHdrK_le lay
  have fin_frame : ∀ {w : MachineState}, Frame t2 w (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) →
      Frame t w StepW := fun hw => (f12.trans hw).mono (fun A _ h => by
        unfold StepW; rcases h with h | h
        · exact Or.inl h
        · exact Or.inr h)
  rw [show ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i st) (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v) =
    (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i st) (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v)
      >>= pure) by rw [bind_pure]]
  by_cases hGb : ClaudeWCT.WCT9.isG lay i = true
  · -- G path: `value | header | 0 | 0` at CHAIN+48
    obtain ⟨u, k1, su, hk1, upc, u6, u7, ur, uf⟩ : ∃ u k1, Steps im t2 k1 k1 u ∧ expHdrK lay + k1 + 23 ≤ stepW lay ∧
        u.pc = pcOf 49316 ∧ u.getReg .x6 = BitVec.ofNat 64 (gTermL lay i) ∧
        u.getReg .x7 = (T3.chainHeader lay tree leaf i st).extractLsb' 64 64 ∧
        RegsExcept t2 u [.x6, .x7] ∧ Frame t2 u (fun _ => False) := by
      rcases ClaudeWCT.WCT9.isG_eq_true.mp hGb with ⟨hl, hi2⟩ | ⟨hl, hi2, hi52⟩
      · have hl' : lay.val ≠ 0 := fun h => hl (Fin.ext h)
        rw [if_neg hl'] at p0
        obtain ⟨u1, q1, p1', r1', f1'⟩ := lsel_spec (im := im) u0 p0 i g19
        rw [if_neg (by omega)] at p1'
        obtain ⟨u2, q2, p2', x6', x7', r2', f2'⟩ := lg_spec (im := im) u1 p1'
        refine ⟨u2, 7, s0.trans (q1.trans q2), by unfold stepW; rw [if_neg hl]; have := expHdrK_le lay; unfold expHdrK at this ⊢; split_ifs at this ⊢ <;> omega, p2', ?_, ?_, ?_, ?_⟩
        · rw [x6']; simp [gTermL, SigGolfCandidate.T3.maxDigit, hl]
        · rw [x7', Keygen.PackedBlocks.source_high_actual lay tree leaf i st hrH hf hi (by omega)]
        · exact ((r0.trans r1').trans r2').mono (by simp)
        · exact ((f0.trans f1').trans f2').mono (fun A _ h => by simp_all)
      · have hl' : lay.val = 0 := by rw [hl]; rfl
        rw [if_pos hl'] at p0
        obtain ⟨u1, q1, p1', r1', f1'⟩ := tsel_spec (im := im) u0 p0 i (by omega) g19
        rw [if_pos hi2] at p1'
        obtain ⟨u2, q2, p2', r2', f2'⟩ := tle_spec (im := im) u1 p1' i (by omega)
          (by rw [r1'.get (by simp)]; exact g19)
        rw [if_neg (by omega)] at p2'
        obtain ⟨u3, q3, p3', x6', x7', r3', f3'⟩ := tcap_spec (im := im) u2 p2' i (by omega) hi2
          (by rw [r2'.get (by simp), r1'.get (by simp)]; exact g19)
          (by rw [r2'.get (by simp), r1'.get (by simp), r0.get (by simp)]; exact a28)
        have hK0 : expHdrK lay = 32 := by unfold expHdrK; rw [if_pos hl']
        refine ⟨u3, _, ((s0.trans q1).trans q2).trans q3, by rw [hK0]; unfold stepW gtK; rw [if_pos hl]; split_ifs <;> omega,
          p3', ?_, ?_, ?_, ?_⟩
        · rw [x6', hl]; simp [gTermL]
        · have f02 : Frame t2 u2 (fun _ => False) :=
            ((f0.trans f1').trans f2').mono (fun A _ h => by simp_all)
          rw [x7', f02.get (by decide) (by simp), m24]
        · exact (((r0.trans r1').trans r2').trans r3').mono (by simp)
        · exact (((f0.trans f1').trans f2').trans f3').mono (fun A _ h => by simp_all)
    have g1 : ∀ r, r ∉ [Reg.x6, .x7] → u.getReg r = t2.getReg r := fun r hr => ur.get hr
    have hT : gTermL lay i < 2 ^ 63 := by
      unfold gTermL SharedRecover.gTerm SigGolfCandidate.T3.maxDigit; split_ifs <;> omega
    obtain ⟨u2, su2, u2pc, u210, u211, u212, u264, u272, u280, u288, u296, u2104, u2r, u2f⟩ :=
      g_spec (im := im) u upc st (gTermL lay i) _ (by omega) hT u6 u7
        (by rw [g1 _ (by simp), r12.get (by simp)]; exact h20) (by rw [g1 _ (by simp)]; exact a28)
    have f02 : Frame t2 u2 (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) :=
      (uf.trans u2f).mono (fun A _ h => by rcases h with h | h <;> simp_all)
    have r02 : RegsExcept t2 u2 [.x6, .x7, .x10, .x11, .x12, .x30] := (ur.trans u2r).mono (by simp)
    have v2 := (hv.frame f12 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)).frame f02
      (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
    have hq : hashInput u2 = toQ (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v)) := by
      have hl := ClaudeWCT.WCT9.chainInputW_length lay tree leaf i st v
      rw [pad64_of_aligned _ (by rw [hl])]
      refine hashInput_toQ u2 _ 0 (CHAIN + 48) hl u210 (by decide) (by decide) u211 (by decide) ?_
      rw [wordsOf_chainInputW_G hGb, readWords_eight]
      rw [show CHAIN + 48 + 8 = CHAIN + 56 from rfl, show CHAIN + 48 + 16 = CHAIN + 64 from rfl,
        show CHAIN + 48 + 24 = CHAIN + 72 from rfl, show CHAIN + 48 + 32 = CHAIN + 80 from rfl,
        show CHAIN + 48 + 40 = CHAIN + 88 from rfl, show CHAIN + 48 + 48 = CHAIN + 96 from rfl,
        show CHAIN + 48 + 56 = CHAIN + 104 from rfl]
      rw [v2.1, v2.2, u264, u272, u280, u288, u296, u2104, uf.get (A := CHAIN + 16) (by decide) (by simp), m16]
    have hvalid : hashArgumentsValid u2 = true := by
      by_cases hm6 : st = gTermL lay i
      · rw [if_pos hm6] at u212
        exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 48) u210 u211 u212 (by decide) (by decide) (by decide)
          (by decide) (by decide)
      · rw [if_neg hm6] at u212
        exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 32) u210 u211 u212 (by decide) (by decide) (by decide)
          (by decide) (by decide)
    have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp), g2 _ (by simp [stepRegs])]; exact hc.x5
    refine (TBSim.steps (((s1.trans s2).trans su).trans su2)
      (tb_halfHash_bind' (im := im) (W := 2) _ (fetch_49328 (im := im) u2 u2pc) h5' hvalid hq (fun a => ?_))).mono
      (by rw [chainInputW_blocks]; split_ifs <;> omega) (fun _ _ h => h)
    have hw20 : (writeHash u2 a).getReg .x20 = BitVec.ofNat 64 st := by
      rw [getReg_writeHash, r02.get (by simp), r12.get (by simp)]
      exact h20
    obtain ⟨w, sw, wpc, w20, wr, wf⟩ := gtail_spec (im := im) (writeHash u2 a)
      (by rw [pc_writeHash, u2pc, pcOf_add4]) st hw20
    have hB : ∀ B, u2.getReg .x12 = BitVec.ofNat 64 B → B = CHAIN + 32 ∨ B = CHAIN + 48 →
        Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := fun B h12 hB =>
      (Frame.writeHash u2 a B h12 (by rcases hB with rfl | rfl <;> decide)).mono
        (fun A _ h => by simp only [CHAIN] at hB ⊢; omega)
    have hwf : Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := by
      by_cases hm6 : st = gTermL lay i
      · rw [if_pos hm6] at u212; exact hB _ u212 (Or.inr rfl)
      · rw [if_neg hm6] at u212; exact hB _ u212 (Or.inl rfl)
    have hval : DigAt (writeHash u2 a) (CHAIN + 48)
        (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.chainHigh lay i st) a) := by
      rw [gHigh_eq hGb (by omega)]
      by_cases hm6 : st = gTermL lay i
      · rw [if_pos hm6] at u212
        rw [decide_eq_false (fun h => h hm6)]
        exact DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by decide)
      · rw [if_neg hm6] at u212
        rw [decide_eq_true hm6]
        exact DigAt.writeHash_hi u2 a (CHAIN + 32) u212 (by decide)
    have fall : Frame t w StepW := fin_frame (((f02.trans hwf).trans wf).mono (fun A _ h => by
      simp only [CHAIN] at h ⊢; rcases h with (h | h) | h <;> first | omega | exact h.elim))
    have rall : RegsExcept t w stepRegs := fun r hr => by
      have rr : RegsExcept u2 (writeHash u2 a) [] := fun r _ => getReg_writeHash u2 a r
      rw [((r02.trans rr).trans wr).get (by simp [stepRegs] at hr ⊢; tauto), g2 r hr]
    refine TBSim.steps (W := 0) sw (TBSim.pure ⟨wpc, w20, ?_, ?_, hval.frame wf (by decide) (by simp) (by simp),
      rall, fall⟩)
    · rw [rall.get (by simp [stepRegs])]; exact h21
    · exact hc.frame (l := stepRegs) (by simp [stepRegs]) rall fall
  · -- F path: `T3.chainInput` at CHAIN
    have hGf : ClaudeWCT.WCT9.isG lay i = false := by simpa using hGb
    rw [ClaudeWCT.WCT9.chainInputW_F hGf]
    obtain ⟨u1, k1, su1, hk1, u1pc, u1r, u1f⟩ : ∃ u1 k1, Steps im t2 k1 k1 u1 ∧
        expHdrK lay + k1 + trXE lay.val i st ≤ 50 ∧ u1.pc = pcOf 49331 ∧ RegsExcept t2 u1 [.x6, .x7] ∧
        Frame t2 u1 (fun _ => False) := by
      by_cases hl0 : lay.val = 0
      · rw [if_pos hl0] at p0
        have hl : lay = 0 := Fin.ext hl0
        have hK0 : expHdrK lay = 32 := by unfold expHdrK; rw [if_pos hl0]
        obtain ⟨u1, q1, p1', r1', f1'⟩ := tsel_spec (im := im) u0 p0 i (by omega) g19
        by_cases hi2 : i % 2 = 0
        · rw [if_pos hi2] at p1'
          obtain ⟨u2, q2, p2', r2', f2'⟩ := tle_spec (im := im) u1 p1' i (by omega)
            (by rw [r1'.get (by simp)]; exact g19)
          exact absurd (ClaudeWCT.WCT9.isG_eq_true.mpr (Or.inr ⟨hl, hi2, hiT hl⟩)) hGb
        · rw [if_neg hi2] at p1'
          have hX : trXE lay.val i st = 2 := by unfold trXE; rw [if_pos (by omega)]
          exact ⟨u1, 5, s0.trans q1, by omega, p1', (r0.trans r1').mono (by simp),
            (f0.trans f1').mono (fun A _ h => by simp_all)⟩
      · rw [if_neg hl0] at p0
        obtain ⟨u1, q1, p1', r1', f1'⟩ := lsel_spec (im := im) u0 p0 i g19
        have hi2 : i % 2 = 0 := by
          by_contra h
          exact hGb (ClaudeWCT.WCT9.isG_eq_true.mpr (Or.inl ⟨fun h' => hl0 (by rw [h']; rfl), by omega⟩))
        rw [if_pos hi2] at p1'
        have := trXE_le lay.val i st
        exact ⟨u1, 4, s0.trans q1, by omega, p1', (r0.trans r1').mono (by simp),
          (f0.trans f1').mono (fun A _ h => by simp_all)⟩
    obtain ⟨u2, su2, u2pc, u210, u211, u212, u232, u240, u2r, u2f⟩ :=
      f_spec (im := im) u1 u1pc (by rw [u1r.get (by simp)]; exact a28)
    have f02 : Frame t2 u2 (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) :=
      (u1f.trans u2f).mono (fun A _ h => by rcases h with h | h <;> simp_all)
    have r02 : RegsExcept t2 u2 [.x6, .x7, .x10, .x11, .x12] := (u1r.trans u2r).mono (by simp)
    have v2 := (hv.frame f12 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)).frame f02
      (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
    have z0 : u2.getMem (BitVec.ofNat 64 CHAIN) = 0 := by
      rw [f02.get (by decide) (by simp only [CHAIN]; omega), f12.get (by decide) (by simp only [CHAIN]; omega)]
      exact hc.z0
    have z8 : u2.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0 := by
      rw [f02.get (by decide) (by simp only [CHAIN]; omega), f12.get (by decide) (by simp only [CHAIN]; omega)]
      exact hc.z8
    have hq : hashInput u2 = toQ (pad64 (chainInput lay tree leaf i st v)) := by
      refine hashInput_toQ u2 _ 0 CHAIN (by rw [pad64_of_aligned _ (by rw [chainInput_length']), chainInput_length'])
        u210 (by simp only [CHAIN]) (by simp only [CHAIN]; omega) u211 (by norm_num) ?_
      rw [readWords_eight, wordsOf_chainInput', z0, z8,
        f02.get (A := CHAIN + 16) (by decide) (by simp only [CHAIN]; omega),
        f02.get (A := CHAIN + 24) (by decide) (by simp only [CHAIN]; omega), m16, m24, u232, u240, v2.1,
        show CHAIN + 48 + 8 = CHAIN + 56 from rfl, v2.2]
    have hvalid : hashArgumentsValid u2 = true :=
      hashArgs_const u2 CHAIN 64 (CHAIN + 48) u210 u211 u212 (by simp only [CHAIN]) (by norm_num)
        (by simp only [CHAIN]; omega) (by simp only [CHAIN]) (by simp only [CHAIN]; omega)
    have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp), g2 _ (by simp [stepRegs])]; exact hc.x5
    refine (TBSim.steps (((s1.trans s2).trans su1).trans su2)
      (tb_halfHash_bind' (im := im) (W := 2 + trXE lay.val i st) _ (fetch_49336 (im := im) u2 u2pc) h5' hvalid hq
        (fun a => ?_))).mono
      (by rw [blocks_chainInput']; unfold stepW; split_ifs <;> omega) (fun _ _ h => h)
    have gw : ∀ r, r ∉ stepRegs → (writeHash u2 a).getReg r = t.getReg r := fun r hr => by
      rw [getReg_writeHash, r02.get (by simp [stepRegs] at hr ⊢; tauto), g2 r hr]
    have p3 : (writeHash u2 a).pc = pcOf 49337 := by rw [pc_writeHash, u2pc, pcOf_add4]
    have hlo := DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by simp only [CHAIN]; omega)
    have hhi : DigAt (writeHash u2 a) (CHAIN + 64) (a.extractLsb' 128 128) :=
      DigAt.writeHash_hi u2 a (CHAIN + 48) u212 (by simp only [CHAIN]; omega)
    obtain ⟨w, s4, p4, w20, hd, r4, f4⟩ := rl1047_spec (im := im) (writeHash u2 a) p3 lay i st (by omega) (by omega)
      hGf (by rw [gw _ (by simp [stepRegs])]; exact hc.x8) (by rw [gw _ (by simp [stepRegs])]; exact hc.x19)
      (by rw [getReg_writeHash, r02.get (by simp), r12.get (by simp)]; exact h20) _ _ hlo hhi
    have fw := Frame.writeHash u2 a (CHAIN + 48) u212 (by simp only [CHAIN]; omega)
    have fall : Frame t w StepW := fin_frame (((f02.trans fw).trans f4).mono (fun A _ h => by
      simp only [CHAIN] at h ⊢; omega))
    have rall : RegsExcept t w stepRegs := fun r hr => by
      rw [r4.get (not_mem_of_sub (by simp [stepRegs]) hr), gw r hr]
    refine TBSim.steps (W := 0) s4 (TBSim.pure ⟨p4, w20, ?_, ?_, ?_, rall, fall⟩)
    · rw [rall.get (by simp [stepRegs])]; exact h21
    · exact hc.frame (l := stepRegs) (by simp [stepRegs]) rall fall
    · unfold ClaudeWCT.WCT9.halfOf; exact hd

theorem chain_loop (lay : Layer) (tree leaf i d e : Nat)
    (hrH : tree * 2 ^ T3.height lay + leaf < 2 ^ T3.hyperW lay.val) (hf : leaf < 2 ^ T3.height lay) (hd : d ≤ e) (he : e ≤ 7)
    (hcap : e ≤ SigGolfCandidate.T3.maxDigit lay i)
    (hi : i < 64) (hiT : lay = 0 → i ≤ 50) (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1031)
    (hc : ChainCtx lay.val tree leaf i t) (h20 : t.getReg .x20 = BitVec.ofNat 64 d)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 e) (hv : DigAt t (CHAIN + 48) v) :
    TBSim im sk t ((e - d) * stepW lay + 1) (ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v)
      (fun v' u => u.pc = pcOf 1049 ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
        ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) v' ∧ RegsExcept t u stepRegs ∧ Frame t u StepW) := by
  have hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31 :=
    lt_of_lt_of_le hrH (Nat.pow_le_pow_right (by norm_num) (T3.hyperW_le _))
  let Inv : Nat → Digest → MachineState → Prop := fun j w u =>
    u.pc = pcOf 1031 ∧ u.getReg .x20 = BitVec.ofNat 64 (d + j) ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
      ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) w ∧ RegsExcept t u stepRegs ∧ Frame t u StepW
  have hloop := TBSim.foldlM_range' (image := im) (sk := sk) d (e - d)
    (fun value step => ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i step) (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) v Inv (stepW lay)
    (fun j hj w u hu => by
      obtain ⟨p, x20, x21, cc, dv, rr, ff⟩ := hu
      refine (chain_step (im := im) lay tree leaf i (d + j) e hrH hf (by omega) he hcap hi hiT w u p cc x20 x21 dv).mono le_rfl ?_
      rintro w' u' ⟨p', y20, y21, cc', dv', rr', ff'⟩
      refine ⟨p', by rw [y20]; congr 1, y21, cc', dv', ?_, ?_⟩
      · exact (rr.trans rr').mono (fun r hr => by
          rcases List.mem_append.mp hr with h | h <;> exact h)
      · exact (ff.trans ff').mono (fun A _ h => by rcases h with h | h <;> exact h))
    (s := t) ⟨hpc, by simpa using h20, h21, hc, hv, RegsExcept.refl _ _, Frame.refl _ _⟩
  have hprog : ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v = ((List.range' d (e - d)).foldlM
      (fun value step => ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i step) (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) v >>= pure) := by
    rw [bind_pure]; rfl
  rw [hprog]
  refine (TBSim.bind (W₂ := 1) hloop (fun w u hu => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p, x20, x21, cc, dv, rr, ff⟩ := hu
  obtain ⟨u1, s1, p1, r1, f1⟩ := rl1031_spec (im := im) u p (d + (e - d)) e (by omega) (by omega) x20 x21
  rw [if_pos (by omega)] at p1
  exact (TBSim.steps s1 (TBSim.pure ⟨p1, by rw [r1.get (by simp)]; exact x21, cc.frame (l := []) (by simp) r1
      (f1.mono (fun _ _ h => h.elim)), dv.frame f1 (by simp only [CHAIN]; omega) (by simp) (by simp),
    (rr.trans r1).mono (by simp), (ff.trans f1).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)⟩)).mono
    (by omega) (fun _ _ h => h)

theorem rl_one (lay : Layer) (tree leaf i d P W n n4 : Nat)
    (hrH : tree * 2 ^ T3.height lay + leaf < 2 ^ T3.hyperW lay.val) (hf : leaf < 2 ^ T3.height lay) (hi : i < n) (hn : n ≤ 58)
    (hiT : lay = 0 → i ≤ 50)
    (hn4 : n4 ≤ n) (hP : 0x7000 ≤ P) (hPi : P + 16 * i + 16 ≤ 0x7000 + 5616) (hP8 : P % 8 = 0)
    (hW8 : W % 8 = 0) (hW : 64 ≤ W) (hW' : W + 64 ≤ 0x7000) (hd : d ≤ (endpoint lay i n4))
    (hcap : endpoint lay i n4 ≤ SigGolfCandidate.T3.maxDigit lay i)
    (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1010)
    (hc : ChainCtx lay.val tree leaf i t) (h26 : t.getReg .x26 = BitVec.ofNat 64 n)
    (h27 : t.getReg .x27 = BitVec.ofNat 64 n4) (h16 : t.getReg .x16 = BitVec.ofNat 64 P)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 W) (hv : DigAt t (P + 16 * i) v)
    (hdig : t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d) :
    TBSim im sk t 507 (ClaudeWCT.WCT9.chainW lay tree leaf i d ((endpoint lay i n4) - d) v)
      (fun v' u => u.pc = pcOf 1010 ∧ u.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
        u.getReg .x23 = BitVec.ofNat 64 (W - 64) ∧ ChainCtx lay.val tree leaf (i + 1) u ∧
        DigAt u (LEAFPK + slotOff lay i) v' ∧ DigAt u (W + 48) v ∧ RegsExcept t u oneRegs ∧ Frame t u (OneW lay i W)) := by
  have hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31 :=
    lt_of_lt_of_le hrH (Nat.pow_le_pow_right (by norm_num) (T3.hyperW_le _))
  have hlay := lay.isLt
  set e := (endpoint lay i n4) with he
  have he7 : e ≤ 7 := by rw [he]; unfold endpoint; split_ifs <;> omega
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1010_spec (im := im) t hpc i n (by omega) (by omega) hc.x19 h26
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, c48, c56, w48, w56, x23, x28, r2, f2⟩ := rl1011_spec (im := im) t1 p1 i P W hP hPi hP8 hW8 hW hW'
    (by rw [r1.get (by simp)]; exact hc.x19) (by rw [r1.get (by simp)]; exact h16)
    (by rw [r1.get (by simp)]; exact h23)
  have f12 : Frame t t2 (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) :=
    (f1.trans f2).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
  have hb2 : t2.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d := by
    rw [Frame.getByte f12 (by simp only [DIGITS]; omega) (by simp only [DIGITS, CHAIN]; omega), hdig]
  obtain ⟨t3, s3, p3, x20, r3, f3⟩ := rl1027_spec (im := im) t2 p2 i d (by omega) (by omega) x28 hb2
  obtain ⟨t4, s4, p4, x21, r4, f4⟩ := rl1028_spec (im := im) t3 p3 lay.val (by omega)
    (by rw [r3.get (by simp), r2.get (by simp), r1.get (by simp)]; exact hc.x8)
  obtain ⟨t5, s5, p5, x21', r5, f5⟩ : ∃ t5, Steps im t4 (endpointExtra lay i n4) (endpointExtra lay i n4) t5 ∧
      t5.pc = pcOf 1031 ∧ t5.getReg .x21 = BitVec.ofNat 64 e ∧ RegsExcept t4 t5 [.x21, .x28] ∧
      Frame t4 t5 (fun _ => False) := by
    have hl0 : lay.val = 0 ↔ lay = 0 := by simp
    by_cases hl : lay = 0
    · rw [if_pos (hl0.mpr hl)] at p4
      obtain ⟨ta, qa, pa, ra, fa⟩ := rl1030_spec (im := im) t4 p4
      have rr := (((r1.trans r2).trans r3).trans r4).trans ra
      obtain ⟨tb, qb, pb, xb, rb, fb⟩ := rl1158_spec (im := im) ta pa i (by omega)
        (by rw [rr.get (by simp)]; exact hc.x19)
      refine ⟨tb, ?_, pb, ?_, ?_, ?_⟩
      · simpa only [endpointExtra, if_pos hl] using qa.trans qb
      · rw [xb, he, hl, ← endpoint_top i n4]
      · exact (ra.trans rb).mono (by simp)
      · exact (fa.trans fb).mono (by simp)
    · rw [if_neg (fun hv => hl (hl0.mp hv))] at p4
      exact ⟨t4, by simpa [endpointExtra, hl] using Steps.refl t4, p4,
        by simpa [he, endpoint, hl] using x21, RegsExcept.refl _ _, Frame.refl _ _⟩
  have f15 : Frame t t5 (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) :=
    (((f12.trans f3).trans f4).trans f5).mono (fun A _ h => by
      rcases h with ((h | h) | h) | h
      · exact h
      · exact h.elim
      · exact h.elim
      · exact h.elim)
  have r15 : RegsExcept t t5 ([] ++ [.x6, .x7, .x23, .x28, .x29, .x30] ++ [.x20] ++ [.x21] ++ [.x21, .x28]) :=
    (((r1.trans r2).trans r3).trans r4).trans r5
  have g5 : ∀ r, r ∉ [Reg.x6, .x7, .x20, .x21, .x23, .x28, .x29, .x30] → t5.getReg r = t.getReg r :=
    fun r hr => r15.get (fun hm => hr (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; tauto))
  have hc5 : ChainCtx lay.val tree leaf i t5 :=
    { x5 := by rw [g5 _ (by simp)]; exact hc.x5
      x8 := by rw [g5 _ (by simp)]; exact hc.x8
      x9 := by rw [g5 _ (by simp)]; exact hc.x9
      x18 := by rw [g5 _ (by simp)]; exact hc.x18
      x19 := by rw [g5 _ (by simp)]; exact hc.x19
      z0 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z0
      z8 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z8 }
  have hv5 : DigAt t5 (CHAIN + 48) v := by
    constructor
    · rw [f5.get (by simp only [CHAIN]; omega) (by simp), f4.get (by simp only [CHAIN]; omega) (by simp),
        f3.get (by simp only [CHAIN]; omega) (by simp), c48, f1.get (by omega) (by simp)]; exact hv.1
    · rw [f5.get (by simp only [CHAIN]; omega) (by simp), f4.get (by simp only [CHAIN]; omega) (by simp),
        f3.get (by simp only [CHAIN]; omega) (by simp), c56, f1.get (by omega) (by simp)]; exact hv.2
  have x20' : t5.getReg .x20 = BitVec.ofNat 64 d := by rw [r5.get (by simp), r4.get (by simp)]; exact x20
  have hloop := chain_loop (im := im) (sk := sk) lay tree leaf i d e hrH hf hd he7 hcap (by omega) hiT v t5 p5 hc5 x20' x21' hv5
  have hprog : ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v =
      (ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v >>= pure) := by rw [bind_pure]
  rw [hprog]
  have total_cost : (1 + 16 + 1 + 2 + endpointExtra lay i n4) + ((e - d) * stepW lay + 1 + 17) ≤ 507 := by
    rw [he]; unfold endpointExtra endpoint stepW SharedRecover.kmaxSteps
    split_ifs <;> omega
  refine (TBSim.steps (((((s1.trans s2).trans s3).trans s4).trans s5)) (TBSim.bind (W₂ := 17) hloop
    (fun v' u hu => ?_))).mono (by
      simpa only [Nat.add_assoc] using total_cost) (fun _ _ h => h)
  obtain ⟨pu, u21, cu, du, ru, fu⟩ := hu
  obtain ⟨u2, q2, pu2, z28, ry2, fy2⟩ := rl1049_spec (im := im) u pu lay i (by omega) cu.x8 cu.x19
  have hslot8 : slotOff lay i % 8 = 0 := by unfold slotOff; split_ifs <;> omega
  have hslot : LEAFPK + slotOff lay i + 16 ≤ 2 ^ 24 := by unfold slotOff; simp only [LEAFPK]; split_ifs <;> omega
  obtain ⟨u3, q3, pu3, w19, m0, m8, ry3, fy3⟩ := rl1052_spec (im := im) u2 pu2 i (slotOff lay i) hslot8 hslot z28
    (by rw [ry2.get (by simp)]; exact cu.x19)
  have fy12 : Frame u u2 (fun _ => False) := fy2
  have hslotC : ∀ A, (A = LEAFPK + slotOff lay i ∨ A = LEAFPK + slotOff lay i + 8) → ¬ StepW A := by
    intro A hA hS; unfold StepW at hS; unfold slotOff at hA; simp only [LEAFPK, CHAIN] at hA hS; split_ifs at hA <;> omega
  refine (TBSim.steps (q2.trans q3) (TBSim.pure ⟨pu3, w19, ?_, ?_, ?_, ?_, ?_, ?_⟩)).mono
    (by unfold slK; split_ifs <;> omega) (fun _ _ h => h)
  · rw [ry3.get (by simp), ry2.get (by simp), ru.get (by simp [stepRegs]),
      r5.get (by simp), r4.get (by simp), r3.get (by simp)]; exact x23
  · refine
      { x5 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x5
        x8 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x8
        x9 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x9
        x18 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x18
        x19 := w19
        z0 := ?_, z8 := ?_ } <;>
    · rw [fy3.get (by simp only [CHAIN]; omega) (by unfold slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega),
        fy12.get (by simp only [CHAIN]; omega) (by simp)]
      first | exact cu.z0 | exact cu.z8
  · constructor
    · rw [m0, fy12.get (by simp only [CHAIN]; omega) (by simp)]; exact du.1
    · rw [m8, fy12.get (by simp only [CHAIN]; omega) (by simp)]; exact du.2
  · have hW : ∀ A, (A = W + 48 ∨ A = W + 56) → A < 2 ^ 64 ∧ ¬ StepW A ∧ ¬ (A = LEAFPK + slotOff lay i ∨ A = LEAFPK + slotOff lay i + 8) := by
      intro A hA; unfold StepW slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega
    constructor
    · obtain ⟨h1, h2, h3⟩ := hW (W + 48) (Or.inl rfl)
      rw [fy3.get h1 h3, fy12.get h1 (by simp), fu.get h1 h2, f5.get h1 (by simp), f4.get h1 (by simp),
        f3.get h1 (by simp), w48, f1.get (by omega) (by simp)]; exact hv.1
    · obtain ⟨h1, h2, h3⟩ := hW (W + 56) (Or.inr rfl)
      rw [fy3.get h1 h3, fy12.get h1 (by simp), fu.get h1 h2, f5.get h1 (by simp), f4.get h1 (by simp),
        f3.get h1 (by simp), w56, f1.get (by omega) (by simp)]; exact hv.2
  · intro r hr
    have hr' : r ∉ [Reg.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x23, .x28, .x29, .x30] := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [ry3.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ry2.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ru.get (by simp only [stepRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      g5 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto)]
  · intro A hA hn
    unfold OneW at hn
    simp only [not_or] at hn
    rw [fy3.get hA (by tauto), fy12.get hA (by simp), fu.get hA hn.1,
      f15.get hA (by simp only [CHAIN] at hn ⊢; unfold StepW at hn; simp only [CHAIN] at hn; omega)]

end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_LayersBlocks ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
set_option autoImplicit false
set_option maxRecDepth 8192
section blocks
variable (s : MachineState)
-- [h2 lane] removed c342_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
open SigGolfCandidate.T3M.Expand
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [EntryCode im]
section
variable (s : MachineState)
end
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
end SigGolfCandidate.T3M.Expand.SharedRecover

/-! ## T51 KCOPY (54522..54531, from 331 `jal ra, 54522`): copy the 1,896-byte shared kernel table window
`0xFF9E00 .. 0xFFA568` (237 doublewords; the 1,892-byte block + 4 bytes) to RAM `0xA0000`, then `j 457`. -/
namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

end SigGolfCandidate.T3M.Expand.KCopy
end
-- ==== merged from T3M_Search_DigestSearch ====
section

section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
section blocks
variable {image : Image} {b : Nat}
end blocks
section sort
variable {image : Image} {b : Nat}
end sort
section loop
variable {image : Image} {b : Nat}
end loop
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer HashOutput)
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
section blocks
variable {image : Image} {d b : Nat}
end blocks
section loop
variable {image : Image} {d b : Nat} {sk : BitVec 256}
end loop
end SigGolfCandidate.T3M.Search
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Defs ====
section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC FailedAt KernAt)
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ExpSearch ====
section

section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Search (DIG NBUF)
open SigGolfCandidate.T3M.Expand (IDXV)
open ClaudeWCT.W9.Machine.Sign (run)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE)
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand.ESearch
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign (run memEval_cons_ofNat)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE costByte costChk
  costChk_getD costByte_lt piece regs_rfs shl0_shr33 sll_eval srl_eval fieldE_eval psum psum_succ psum_le fieldN_lt
  psum_nine digestInput_length' pad64_digestInput' wordsOf_digestInput' blocks_digestInput' childN childN_lt childE_eval)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
section pieces
variable {im : Image}
end pieces
section loop
variable {im : Image} {sk : BitVec 256}
end loop
end ClaudeWCT.W9.Machine.Expand.ESearch
end
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Base ====
section

section
namespace ClaudeWCT.W9.Machine.Expand
open Lean Meta Elab Tactic
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_DrvBits ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIG NBUF ENC)
set_option autoImplicit false
set_option maxRecDepth 8192
section blocks
variable (s : MachineState)
-- [h2 lane] removed s0_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Expand (IDXV)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.Driver
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 16384
end ClaudeWCT.W9.Machine.Expand.Driver
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Merkle_ChildDefs ====
section

namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE)
end ClaudeWCT.W9.Machine.Merkle
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Region ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput readDigest readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (chainBytes leafBytes)
set_option linter.unusedSimpArgs false
section windows
variable (c : Nat) (op : WCT9.Opening)
end windows
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_LayoutCode ====
section

/-! Pairing stage 1: code tables of the leaf / digest layout block 48100 .. 49225 (proofs in `LayoutBlock`). -/
namespace ClaudeWCT.W9.Machine.Expand.Layout
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
/-! Generated by pair1-expand (from sol-pair1/img-candidate/expand.code, words 48119 .. 49224).
T51 (VERA2, round 2; regenerated from the T51 expand image t51/sign/img/t51e, words 48119 .. 49225): the top group
keeps the 51 items of values 0..50 (item 129, value 0: `sd t1,-32(a1)`, so `xK 129 = 2^64 - 32` and its slot is
`(dK + xK) % 2^64 = 25200`; item 129 + i: `X = 16 (i - 1)`). #938's items 180..182 (values 51..53) lost their
stores (`nop`): with the return word they form the straight tail `cRet` (49207 .. 49225, 19 words). -/
end ClaudeWCT.W9.Machine.Expand.Layout
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactCode ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib

namespace PairCopy
/-! Pairing stage 1: the lower-chain pair copy block at 48000 (outside the compact lookup scope). -/
end PairCopy
structure CompactCodeAt (im : Image) : Prop where
  look : LookOK im compactLook
  /-- Pairing stage 1: the pair copy block 48000 .. 48017. -/
  pair : PairCopy.Code im
  /-- Pairing stage 1: the leaf / digest layout block 48100 .. 49225. -/
  layout : Layout.Code im

theorem CompactCodeAt.ofNew {im : Image} (h : NewCodeAt im) (hp : PairCopy.Code im) (hl : Layout.Code im) :
    CompactCodeAt im := by
  refine ⟨?_, hp, hl⟩
  intro n w hw
  unfold compactLook at hw
  split at hw
  · exact expLook_ok h n w hw
  · cases hw

theorem codeAt_of_compact_window {im : Image} (hc : CompactCodeAt im) {n : Nat} {ws : List (BitVec 32)}
    (hn : 0x1000+4*n+4*ws.length<2^64) (h : compactWindowOK n ws=true) : CodeAt im (pcOf n) ws := by
  refine codeAt_of_look hc.look n ws hn (fun i hi=>?_)
  unfold compactWindowOK at h
  have:=List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa using this
end ClaudeWCT.W9.Machine.Expand

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
section code
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem code_cStart : CodeAt im (pcOf 41108) cStart := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRegs : CodeAt im (pcOf 41115) cRegs := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cFinal : CodeAt im (pcOf 42120) cFinal := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cHalt : CodeAt im (pcOf 42127) cHalt := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCopy : CodeAt im (pcOf 42130) cCopy := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cZero : CodeAt im (pcOf 42137) cZero := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_copyRet : CodeAt im (pcOf 42136) [0x8067] := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_zeroRet : CodeAt im (pcOf 42141) [0x8067] := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cHead (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k)) (cHead k) := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cMid (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 6)) (cMid k) := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRow (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 10)) cRow := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cStep (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 109)) cStep := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
/-- Nested FTS (r1-1): levels 0..5 run in place (level 5 now writes to the fixed staging block at +832); level 6
jumps to a per-coordinate trampoline (`sib6_spec`). -/
theorem code_cSib (k l : Nat) (hk : k < 9) (hl : l < 6) : CodeAt im (pcOf (sibAt k l)) (cSib k l) := by
  interval_cases k <;> interval_cases l <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
end code
end ClaudeWCT.W9.Machine.Expand.Compact

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
theorem compactCode_of_chunks {im : Image}
    (hc : ∀c,compactChunkAllowed c → CodeAt im (pcOf (256*c+compactChunkLo c))
      (((expChunks.getD (c-4) []).take (compactChunkLen c)).drop (compactChunkLo c)))
    (hpair : PairCopy.Code im) (hlay : Layout.Code im) :
    CompactCodeAt im := by
  refine ⟨?_, hpair, hlay⟩
  intro n w hw
  unfold compactLook at hw
  split at hw
  · rename_i hs
    have hn := of_decide_eq_true hs
    have ha : compactChunkAllowed (n/256) := by unfold compactChunkAllowed; omega
    have hlo : compactChunkLo (n/256) ≤ n%256 := by unfold compactChunkLo; split <;> omega
    have hlo' : compactChunkLo (n/256) < 256 := by unfold compactChunkLo; split <;> omega
    have hl : n%256<compactChunkLen (n/256) := by unfold compactChunkLen; split_ifs <;> omega
    have hp : 1024≤n := by omega
    unfold expLook at hw
    rw [if_pos hp] at hw
    have ht : (((expChunks.getD (n/256-4) []).take (compactChunkLen (n/256))).drop
        (compactChunkLo (n/256)))[n%256-compactChunkLo (n/256)]?=some w := by
      rw [List.getElem?_drop,show compactChunkLo (n/256)+(n%256-compactChunkLo (n/256))=n%256 by omega,
        List.getElem?_take,if_pos hl]
      exact hw
    have hb : (pcOf (256*(n/256)+compactChunkLo (n/256))).toNat=0x1000+4*(256*(n/256)+compactChunkLo (n/256)) := by
      rw [pcOf,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]; omega
    obtain ⟨_,_,_,hpre⟩ := hc (n/256) ha
    rw [hb] at hpre
    obtain ⟨rest,hrest⟩ := hpre
    have hh := congrArg (·[n%256-compactChunkLo (n/256)]?) hrest
    simp only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1,ht,List.getElem?_drop] at hh
    rw [show (0x1000+4*(256*(n/256)+compactChunkLo (n/256))-0x1000)/4+(n%256-compactChunkLo (n/256))=n by omega] at hh
    exact hh.symm
  · cases hw
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Lv ====
section

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
section code
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
theorem code_cSnap : CodeAt im (pcOf 42142) cSnap := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cZero2 : CodeAt im (pcOf 42149) cZero2 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cHdr : CodeAt im (pcOf 42154) cHdr := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cTop : CodeAt im (pcOf 42224) cTop := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCtr : CodeAt im (pcOf 33117) cCtr := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cPEnd : CodeAt im (pcOf 33284) cPEnd := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cPReg (c : Nat) (hc9 : c < 9) : CodeAt im (pcOf (pregAt c)) (cPReg c) := by
  interval_cases c <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cHold (c : Nat) (hc9 : c < 9) : CodeAt im (pcOf (holdPc c)) (cHold c) := by
  interval_cases c <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cIdx : CodeAt im (pcOf 42231) cIdx := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCh1 : CodeAt im (pcOf 42235) cCh1 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRow1 : CodeAt im (pcOf 42242) cRow1 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCh2 : CodeAt im (pcOf 42408) cCh2 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRow2 : CodeAt im (pcOf 42415) cRow2 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCh3 : CodeAt im (pcOf 42557) cCh3 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRow3 : CodeAt im (pcOf 42564) cRow3 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cTail : CodeAt im (pcOf 42705) cTail := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cLv (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj : j < (if lay = 1 then 7 else 6)) :
    CodeAt im (pcOf (lvAt lay j)) (cLv lay j) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> simp only [if_true, if_false, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide] at hj <;>
    interval_cases j <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cLvA (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) : CodeAt im (pcOf (lvAt lay (rootJ lay))) (cLvA lay) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cLvB (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    CodeAt im (pcOf (lvAt lay (rootJ lay) + 11)) (cLvB lay) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRT (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) : CodeAt im (pcOf (rtAt lay)) (cRT lay) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
end code
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
section eval
variable {s : MachineState} {r : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 r) (hr : r < 2 ^ 7)
include h19 hr
end eval
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem lv_spec (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj' : j + 1 < lvH lay) (s : MachineState)
    (hpc : s.pc = pcOf (lvAt lay j)) (r : Nat) (hr : r < 2 ^ lvH lay) (h19 : s.getReg .x19 = BitVec.ofNat 64 r)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow lay r)) (hp : LPlanAt s) :
    ∃ t, Steps im s 23 23 t ∧ t.pc = pcOf (lvAt lay j + 23) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2) + 8 then
          s.getMem (BitVec.ofNat 64 (lvSrc lay j + 48 * (1 - r / 2 ^ j % 2) + 8))
        else if A = lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2) then
          s.getMem (BitVec.ofNat 64 (lvSrc lay j + 48 * (1 - r / 2 ^ j % 2)))
        else if A = lvDst lay + 16 * plan lay r j + 40 then s.getMem (BitVec.ofNat 64 (lvSrc lay j + 40))
        else if A = lvDst lay + 16 * plan lay r j + 32 then s.getMem (BitVec.ofNat 64 (lvSrc lay j + 32))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  have hj : j < lvH lay := by omega
  have hH := lvH_le lay
  have hr7 : r < 2 ^ 7 := lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hH)
  have hj7 : j < 7 := by omega
  have ht6 := t6E_eval h19 hr7 j hj7
  have hpb := pbE_eval hl hr h20 hp j hj
  have hpl := (plan_ok lay r j hl hr hj).2
  have hpl23 : plan lay r j ≤ 23 := by split_ifs at hpl <;> omega
  have hb : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  obtain ⟨h1, h4⟩ := hl
  have hD : lvDst lay + 16 * 23 ≤ 0x800 + 20912 ∧ 0x800 + 11648 ≤ lvDst lay := by
    unfold lvDst; split_ifs <;> omega
  have hDp : lvDst lay + 16 * plan lay r j + 64 ≤ 0x800 + 20912 := by
    unfold lvDst at *; split_ifs at * <;> omega
  have hS : 0x310000 + 8136 + 64 * 66 ≤ lvSrc lay j ∧ lvSrc lay j + 64 ≤ 0x310000 + 21832 := by
    unfold lvSrc; unfold lvH at hj; split_ifs at * <;> omega
  have hS16 : lvSrc lay j % 16 = 8 := by unfold lvSrc; split_ifs <;> omega
  have hDm : lvDst lay % 8 = 0 := by unfold lvDst; split_ifs <;> omega
  have hrun := run_lv lay j ⟨h1, h4⟩ (by omega)
  rw [rLv_eq lay j ⟨h1, h4⟩ (by omega)] at hrun
  have hslot : (slotE j).eval s = BitVec.ofNat 64 (16 * plan lay r j) := by
    simp only [slotE, E.eval, BinOp.eval, hpb]
    rw [show (4#64 : Word).toNat % 64 = 4 from rfl, ofNat_shl]; congr 1; ring
  have ha0 : ∀ S, (a0E j S).eval s = BitVec.ofNat 64 (48 * (1 - r / 2 ^ j % 2) + S) := fun S => by
    simp only [a0E, E.eval, BinOp.eval, ht6, ofNat_add_ofNat]
  have ha1 : (a1E j (lvDst lay)).eval s =
      BitVec.ofNat 64 (lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2)) := by
    simp only [a1E, E.eval, BinOp.eval, hslot, ht6, ofNat_add_ofNat]; congr 1; ring
  have hobl : Oblig.all s (lvObl j (lvSrc lay j) (lvDst lay)) := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [lvObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, ha1, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, ha1, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, ht6, hslot, ofNat_add_ofNat]
      intro h; have := (ofNat_inj (by omega) (by omega)).mp h; omega
    · simp only [Oblig.holds, Addr.eval, ht6, hslot, ofNat_add_ofNat]
      intro h; have := (ofNat_inj (by omega) (by omega)).mp h; omega
    · simp only [Oblig.holds, Addr.eval, ht6, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, ht6, hslot, ofNat_add_ofNat]
      intro h; have := (ofNat_inj (by omega) (by omega)).mp h; omega
    · simp only [Oblig.holds, Addr.eval, ht6, hslot, ofNat_add_ofNat]
      intro h; have := (ofNat_inj (by omega) (by omega)).mp h; omega
    · simp only [Oblig.holds, Addr.eval, ht6, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, hslot, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, hslot, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, E.eval, h20, BitVec.toNat_ofNat]; unfold LPLAN; omega
    · simp only [Oblig.holds, Addr.eval, E.eval, h20, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      unfold LPLAN lvRow at *; split_ifs <;> omega
  refine ⟨_, symRun_sound hrun (Compact2.code_cLv hc lay j ⟨h1, h4⟩ hj) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h6, h7, h10, h11, h29, h30⟩ := hx
    rw [Result.toState_getReg]
    cases x <;> first | rfl | (exfalso; simp_all)
  · intro A hA
    simp only [Result.toState_getMem, lvMem, memEval_cons, memEval_nil, Addr.eval, E.eval, ha0, ha1, hslot,
      ofNat_add_ofNat, BitVec.add_zero]
    have e1 : 48 * (1 - r / 2 ^ j % 2) + (lvSrc lay j + 8) = lvSrc lay j + 48 * (1 - r / 2 ^ j % 2) + 8 := by ring
    have e2 : 48 * (1 - r / 2 ^ j % 2) + lvSrc lay j = lvSrc lay j + 48 * (1 - r / 2 ^ j % 2) := by ring
    have e3 : 16 * plan lay r j + (lvDst lay + 40) = lvDst lay + 16 * plan lay r j + 40 := by ring
    have e4 : 16 * plan lay r j + (lvDst lay + 32) = lvDst lay + 16 * plan lay r j + 32 := by ring
    rw [e1, e2, e3, e4]
    by_cases q1 : A = lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2) + 8
    · subst q1; simp
    · rw [if_neg (fun h => q1 ((ofNat_inj hA (by omega)).mp h)), if_neg q1]
      by_cases q2 : A = lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2)
      · subst q2; simp
      · rw [if_neg (fun h => q2 ((ofNat_inj hA (by omega)).mp h)), if_neg q2]
        by_cases q3 : A = lvDst lay + 16 * plan lay r j + 40
        · subst q3; simp
        · rw [if_neg (fun h => q3 ((ofNat_inj hA (by omega)).mp h)), if_neg q3]
          by_cases q4 : A = lvDst lay + 16 * plan lay r j + 32
          · subst q4; simp
          · rw [if_neg (fun h => q4 ((ofNat_inj hA (by omega)).mp h)), if_neg q4]
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section
namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
/-! C3 (FULL, E6): the root level of each lower layer runs in three pieces: `cLvA` (Z low word copy, then
`jal rtAt`), the trampoline `cRT` (Z high word copy, LE64(1) at window + 24, `jal` back) and `cLvB` (sibling copy). -/
def rLvA (lay : Nat) : Result := [RLvA1.res, RLvA2.res, RLvA3.res].getD (lay - 1) RLvA1.res
theorem rLvA_eq (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    rLvA lay = ⟨⟨lvARegs (rootJ lay) (lvSrc lay (rootJ lay)) (lvDst lay),
      lvAMem (rootJ lay) (lvSrc lay (rootJ lay)) (lvDst lay), lvAObl (rootJ lay) (lvDst lay)⟩,
      .c (pcOf (rtAt lay)), .jump, 11, 11⟩ := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem run_lvA (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    symRun cfgC (cLvA lay) (pcOf (lvAt lay (rootJ lay))) 40 = some (rLvA lay) := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- C3 (FULL, E6): the root level (`j = rootJ lay`) copies like any other level and also writes LE64(1) at
window + 24, the encoding row tweak's high word (27 steps: the trampoline adds 4). -/
theorem lvRoot_spec (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (s : MachineState)
    (hpc : s.pc = pcOf (lvAt lay (rootJ lay))) (r : Nat) (hr : r < 2 ^ lvH lay)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 r)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow lay r)) (hp : LPlanAt s) :
    ∃ t, Steps im s 27 27 t ∧ t.pc = pcOf (lvAt lay (rootJ lay) + 23) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = lvDst lay + 16 * plan lay r (rootJ lay) + 24 then 1#64
        else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2) + 8 then
          s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2) + 8))
        else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2) then
          s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2)))
        else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 40 then
          s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 40))
        else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 32 then
          s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 32))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  have hjl : rootJ lay < lvH lay := by obtain ⟨h1, h4⟩ := hl; unfold rootJ lvH; split_ifs <;> omega
  have hH := lvH_le lay
  have hr7 : r < 2 ^ 7 := lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hH)
  have hj7 : rootJ lay < 7 := by omega
  have hpb := pbE_eval hl hr h20 hp (rootJ lay) hjl
  have hpl := (plan_ok lay r (rootJ lay) hl hr hjl).2
  have hb : r / 2 ^ rootJ lay % 2 < 2 := Nat.mod_lt _ (by norm_num)
  obtain ⟨h1, h4⟩ := hl
  have hDp : lvDst lay + 16 * plan lay r (rootJ lay) + 64 ≤ 0x800 + 20912 ∧ 0x800 + 11648 ≤ lvDst lay := by
    unfold lvDst at *; split_ifs at * <;> omega
  have hS : 0x310000 + 8136 + 64 * 66 ≤ lvSrc lay (rootJ lay) ∧ lvSrc lay (rootJ lay) + 64 ≤ 0x310000 + 21832 := by
    unfold lvSrc; unfold lvH at hjl; split_ifs at * <;> omega
  have hS16 : lvSrc lay (rootJ lay) % 16 = 8 := by unfold lvSrc; split_ifs <;> omega
  have hDm : lvDst lay % 8 = 0 := by unfold lvDst; split_ifs <;> omega
  -- abbreviations
  have hslot : (slotE (rootJ lay)).eval s = BitVec.ofNat 64 (16 * plan lay r (rootJ lay)) := by
    simp only [slotE, E.eval, BinOp.eval, hpb]
    rw [show (4#64 : Word).toNat % 64 = 4 from rfl, ofNat_shl]; congr 1; ring
  -- piece A: Z low word, then `jal` to the trampoline
  have hrunA := run_lvA lay ⟨h1, h4⟩
  rw [rLvA_eq lay ⟨h1, h4⟩] at hrunA
  have hoblA : Oblig.all s (lvAObl (rootJ lay) (lvDst lay)) := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [lvAObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hslot, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, E.eval, h20, BitVec.toNat_ofNat]; unfold LPLAN; omega
    · simp only [Oblig.holds, Addr.eval, E.eval, h20, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      unfold LPLAN lvRow at *; split_ifs <;> omega
  have sA := symRun_sound hrunA (code_cLvA hc lay ⟨h1, h4⟩) s hpc hoblA
  generalize ht1 : Result.toState _ s = t1 at sA
  have p1 : t1.pc = pcOf (rtAt lay) := by rw [← ht1]; simp [Result.toState_pc, E.eval]
  have ga : ∀ x : Reg, t1.getReg x = ((lvARegs (rootJ lay) (lvSrc lay (rootJ lay)) (lvDst lay)).get x).eval s := by
    intro x; rw [← ht1, Result.toState_getReg]
  have a11 : t1.getReg .x11 = BitVec.ofNat 64 (lvDst lay + 16 * plan lay r (rootJ lay)) := by
    rw [ga]; simp only [lvARegs, RegFile.set, RegFile.get, E.eval, BinOp.eval, hslot, ofNat_add_ofNat]
    congr 1; ring
  have a10 : t1.getReg .x10 = BitVec.ofNat 64 (lvSrc lay (rootJ lay)) := by
    rw [ga]; simp only [lvARegs, RegFile.set, RegFile.get, E.eval]
  have a30 : t1.getReg .x30 = s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 40)) := by
    rw [ga]; simp only [lvARegs, RegFile.set, RegFile.get, E.eval]
  have aR : RegsExcept s t1 [.x6, .x10, .x11, .x29, .x30] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h6, h10, h11, h29, h30⟩ := hx
    rw [ga]
    cases x <;> first | rfl | (exfalso; simp_all)
  have am : ∀ A < 2 ^ 64, t1.getMem (BitVec.ofNat 64 A) =
      if A = lvDst lay + 16 * plan lay r (rootJ lay) + 32 then s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 32))
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [← ht1]
    simp only [Result.toState_getMem, lvAMem, memEval_cons, memEval_nil, Addr.eval, E.eval, hslot, ofNat_add_ofNat]
    by_cases q : A = lvDst lay + 16 * plan lay r (rootJ lay) + 32
    · subst q; rw [if_pos (by congr 1; ring), if_pos rfl]
    · rw [if_neg (fun h => q (by have := (ofNat_inj hA (by omega)).mp h; omega)), if_neg q]
  -- piece B: the trampoline
  have hrunR := run_rt lay ⟨h1, h4⟩
  rw [rRT_eq lay ⟨h1, h4⟩] at hrunR
  have hoblR : Oblig.all t1 rtObl := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [rtObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · simp only [Oblig.holds, Addr.eval, E.eval, a11, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, E.eval, a11, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
  have sR := symRun_sound hrunR (code_cRT hc lay ⟨h1, h4⟩) t1 p1 hoblR
  generalize ht2 : Result.toState _ t1 = t2 at sR
  have p2 : t2.pc = pcOf (lvAt lay (rootJ lay) + 11) := by rw [← ht2]; simp [Result.toState_pc, E.eval]
  have bR : RegsExcept t1 t2 [.x29] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [← ht2, Result.toState_getReg]
    cases x <;> first | rfl | (exfalso; simp_all)
  have bm : ∀ A < 2 ^ 64, t2.getMem (BitVec.ofNat 64 A) =
      if A = lvDst lay + 16 * plan lay r (rootJ lay) + 24 then 1#64
      else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 40 then s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 40))
      else t1.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [← ht2]
    simp only [Result.toState_getMem, rtMem, memEval_cons, memEval_nil, Addr.eval, E.eval, a11, a30,
      ofNat_add_ofNat]
    by_cases q : A = lvDst lay + 16 * plan lay r (rootJ lay) + 24
    · subst q; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => q ((ofNat_inj hA (by omega)).mp h)), if_neg q]
      by_cases q' : A = lvDst lay + 16 * plan lay r (rootJ lay) + 40
      · subst q'; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg (fun h => q' ((ofNat_inj hA (by omega)).mp h)), if_neg q']
  -- piece C: the sibling copy
  have hrunB := run_lvB lay ⟨h1, h4⟩
  rw [rLvB_eq lay ⟨h1, h4⟩] at hrunB
  have h19' : t2.getReg .x19 = BitVec.ofNat 64 r := by
    rw [bR.get (by decide), aR.get (by decide), h19]
  have ht6 := t6E_eval h19' hr7 (rootJ lay) hj7
  have b10 : t2.getReg .x10 = BitVec.ofNat 64 (lvSrc lay (rootJ lay)) := by rw [bR.get (by decide), a10]
  have b11 : t2.getReg .x11 = BitVec.ofNat 64 (lvDst lay + 16 * plan lay r (rootJ lay)) := by
    rw [bR.get (by decide), a11]
  have haB : (aBE (rootJ lay)).eval t2 =
      BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2)) := by
    simp only [aBE, E.eval, BinOp.eval, b10, ht6, ofNat_add_ofNat]
  have hdB : (dBE (rootJ lay)).eval t2 =
      BitVec.ofNat 64 (lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2)) := by
    simp only [dBE, E.eval, BinOp.eval, b11, ht6, ofNat_add_ofNat]
  have hoblB : Oblig.all t2 (lvBObl (rootJ lay)) := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [lvBObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hdB, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, hdB, ofNat_add_ofNat, BitVec.add_zero]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, haB, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, haB, ofNat_add_ofNat, BitVec.add_zero]; exact valid8 _ (by omega) (by omega)
  have sB := symRun_sound hrunB (code_cLvB hc lay ⟨h1, h4⟩) t2 p2 hoblB
  generalize ht3 : Result.toState _ t2 = t3 at sB
  refine ⟨t3, ((sA.trans sR).trans sB).of_eq (by norm_num) (by norm_num), ?_, ?_, ?_⟩
  · rw [← ht3]; simp [Result.toState_pc, E.eval]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h6, h7, h10, h11, h29, h30⟩ := hx
    have e2 : t2.getReg x = s.getReg x := by
      rw [bR.get (by simp [h29]), aR.get (by simp [h6, h10, h11, h29, h30])]
    rw [← ht3, Result.toState_getReg, ← e2]
    cases x <;> first | rfl | (exfalso; simp_all)
  · intro A hA
    rw [← ht3]
    simp only [Result.toState_getMem, lvBMem, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, haB, hdB,
      ofNat_add_ofNat, BitVec.add_zero]
    have hsrc : ∀ X, lvSrc lay (rootJ lay) ≤ X → X < lvSrc lay (rootJ lay) + 64 →
        t2.getMem (BitVec.ofNat 64 X) = s.getMem (BitVec.ofNat 64 X) := by
      intro X hX1 hX2
      rw [bm X (by omega), if_neg (by omega), if_neg (by omega), am X (by omega), if_neg (by omega)]
    rw [hsrc _ (by omega) (by omega), hsrc _ (by omega) (by omega)]
    by_cases q1 : A = lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2) + 8
    · subst q1
      rw [if_pos rfl, if_neg (by omega), if_pos rfl]
    · rw [if_neg (fun h => q1 ((ofNat_inj hA (by omega)).mp h))]
      by_cases q2 : A = lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2)
      · subst q2
        rw [if_pos rfl, if_neg (by omega), if_neg q1, if_pos rfl]
      · rw [if_neg (fun h => q2 ((ofNat_inj hA (by omega)).mp h)), bm A hA, am A hA]
        by_cases q3 : A = lvDst lay + 16 * plan lay r (rootJ lay) + 24
        · rw [if_pos q3, if_pos q3]
        · rw [if_neg q3, if_neg q3, if_neg q1, if_neg q2]
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end
end
