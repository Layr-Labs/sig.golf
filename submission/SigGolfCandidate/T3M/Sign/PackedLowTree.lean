import SigGolfCandidate.T3M.Keygen.Tree
import SigGolfCandidate.T3M.Sign.SeedChain
import SigGolfCandidate.T3M.Sign.TopBlocks
import SigGolfCandidate.T3M.Sign.BaseInv
import SigGolfCandidate.T3M.Sign.TopLeaf
import SigGolfCandidate.T3M.Witness.Dfs

section


namespace SigGolfCandidate.T3M.Sign.Seed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open Keygen
open SeedIndependent (SeedIndependentAt)
open SigGolfCandidate.T3 (Digest buildLevels buildLevel nodeHash shortHash header pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
theorem sub113_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 113)) (hh : Nat) (h1 : 1 ≤ hh) (h2 : hh ≤ 32)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 116) ∧ t.getReg .x20 = BitVec.ofNat 64 (2 ^ (hh - 1)) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_113 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_113 h) s hpc (by simp [st_113, blk117_113.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_113, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, st_113, blk117_113.res, rv_simp, h15]
    apply BitVec.eq_of_toNat_eq
    have e : (BitVec.ofNat 64 hh - 1#64).toNat = hh - 1 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    rw [BitVec.toNat_shiftLeft, e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show hh - 1 < 64 by omega)]
    have : 2 ^ (hh - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    simp only [Nat.one_mod, Nat.one_mul, Nat.mod_eq_of_lt this]
  · intro r hr; simp at hr; cases r <;> simp_all [st_113, blk117_113.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_113, blk117_113.res, rv_simp]
theorem sub116_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 116)) (lo : Nat) (hlo : lo < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if lo = 0 then pcOf (b + 159) else pcOf (b + 117)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_116 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_116 h) s hpc (by simp [st_116, blk117_116.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_116, rebase, blk117_116.res, E.eval, CmpOp.eval, h20]
    by_cases h0 : lo = 0
    · subst h0; simp
    · have : BitVec.ofNat 64 lo ≠ 0#64 := fun he => h0 (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt hlo] at this)
      simp [h0, this]
  · intro r hr; cases r <;> simp_all [st_116, blk117_116.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_116, blk117_116.res, rv_simp]
theorem sub117_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 117)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 118) ∧ t.getReg .x24 = s.getReg .x20 ∧
      RegsExcept s t [.x24] ∧ Frame s t (fun _ => False) := by
  have hrun := run_117 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_117 h) s hpc (by simp [st_117, blk117_117.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_117, Result.toState_pc, E.eval]
  · simp [st_117, blk117_117.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_117, blk117_117.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_117, blk117_117.res, rv_simp]
theorem sub118_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 118)) (lo k : Nat) (hlo : lo < 2 ^ 40) (hk : k < 2 ^ 40)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if k < 2 * lo then pcOf (b + 120) else pcOf (b + 157)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hrun := run_118 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_118 h) s hpc (by simp [st_118, blk117_118.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_118, rebase, blk117_118.res, rv_simp, h20, h24]
    rw [ofNat_shl, show (1#64 : Word).toNat % 64 = 1 from rfl, ofNat_slt k (lo * 2 ^ 1) (by omega) (by omega)]
    by_cases hkl : k < 2 * lo
    · simp [hkl, show k < lo * 2 by omega]
    · simp [hkl, show ¬ k < lo * 2 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_118, blk117_118.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_118, blk117_118.res, rv_simp]
theorem sub120_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (arena k tree h0 : Nat) (ha8 : arena % 8 = 0)
    (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h21 : s.getReg .x21 = BitVec.ofNat 64 h0) :
    ∃ t, Steps image s 20 20 t ∧
      t.pc = (if 2048 ≤ h0 % 4096 then pcOf (b + 1004) else pcOf (b + 140)) ∧
      t.getReg .x7 = BitVec.ofNat 64 k ∧ t.getReg .x30 = BitVec.ofNat 64 (NODE + 48) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = s.getReg .x21 ||| (BitVec.ofNat 64 tree <<< 32) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x30] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 48 ∨ X = NODE + 56) := by
  have hrun := run_120 h.2.1
  have hobl : Oblig.all s st_120.obl := by
    simp only [st_120, blk117_120.res]
    t3n [h2, h24]
    simp only [NODE] at hdis
    omega
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_120 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_120, rebase, blk117_120.res, E.eval, CmpOp.eval, BinOp.eval, h21]
    simp only [slt_shl52, slt_shl52', slt_shl52n, slt_shl52n']
    by_cases hc : 2048 ≤ h0 % 4096 <;> simp [hc]
  · simp [st_120, blk117_120.res, rv_simp, h24]
  · simp [st_120, blk117_120.res, rv_simp]
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h9]
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_120, blk117_120.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, st_120, blk117_120.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem sub214_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1004)) (k : Nat) (hk : k < 2 ^ 12) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 28 28 t ∧ t.pc = pcOf (b + 140) ∧
      t.getReg .x7 = BitVec.ofNat 64 (T3.Rev.revBits 64 k) ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun _ => False) := by
  have hrun := run_rev h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_rev h) s hpc (by simp [st_rev, blk117_rev.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_rev, Result.toState_pc, E.eval]
  · rw [Result.toState_getReg, ← RevNet.revNetBV_eq k hk, ← h24]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [st_rev, blk117_rev.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_rev, blk117_rev.res, rv_simp]
theorem sub140_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 140)) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = s.getReg .x7 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun X => X = NODE + 24) := by
  have hrun := run_140 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_140 h) s hpc (sub140_obl s h30), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_140, Result.toState_pc, E.eval]
  · simp [st_140, blk117_140.res, rv_simp]
  · simp [st_140, blk117_140.res, rv_simp]
  · simp [st_140, blk117_140.res, rv_simp]
  · rw [Result.toState_getMem]; exact sub140_m24 s h30
  · intro r hr; simp at hr; cases r <;> simp_all [st_140, blk117_140.res, rv_simp] <;> rfl
  · intro X hX hn
    rw [Result.toState_getMem]
    exact sub140_frame s h30 X hX (by simp only [NODE] at hn; omega)
theorem sub120_full {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (tag lay arena k tree : Nat) (htag : tag = 3 ∨ tag = 10)
    (ha8 : arena % 8 = 0) (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (hk' : k < 2 ^ 12) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 (hdr0 tag lay tree 0)) :
    ∃ t, Steps image s (26 + revX tag) (26 + revX tag) t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = s.getReg .x21 ||| (BitVec.ofNat 64 tree <<< 32) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = BitVec.ofNat 64 (T3.nodeWord tag 0 k) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56) := by
  obtain ⟨t1, st1, t1pc, t1x7, t1x30, m0, m8, m16, m48, m56, t1r, t1f⟩ :=
    sub120_spec h s hpc arena k tree (hdr0 tag lay tree 0) ha8 hk htree hdis h2 h24 h9 h21
  have hmod : hdr0 tag lay tree 0 % 4096 = 1 + 256 * (tag % 16) := by
    unfold hdr0; omega
  have mid : ∃ u, Steps image t1 (revX tag) (revX tag) u ∧ u.pc = pcOf (b + 140) ∧
      u.getReg .x7 = BitVec.ofNat 64 (T3.nodeWord tag 0 k) ∧ RegsExcept t1 u [.x6, .x7, .x28] ∧
      Frame t1 u (fun _ => False) := by
    rcases htag with rfl | rfl
    · rw [hmod, if_neg (by norm_num)] at t1pc
      refine ⟨t1, (Steps.refl _).of_eq (by decide) (by decide), t1pc, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
      rw [t1x7, nodeWord_3, hdr1_eq k 0 (by omega) (by norm_num)]; simp
    · rw [hmod, if_pos (by norm_num)] at t1pc
      obtain ⟨u, stu, upc, ux7, ur, uf⟩ := sub214_spec h t1 t1pc k hk'
        (by rw [t1r.get (by simp)]; exact h24)
      refine ⟨u, stu.of_eq (by decide) (by decide), upc, ?_, ur, uf⟩
      rw [ux7, nodeWord_10, hdr1_eq k 0 (by omega) (by norm_num)]; simp
  obtain ⟨u, stu, upc, ux7, ur, uf⟩ := mid
  obtain ⟨t, stt, tpc, tx10, tx11, tx12, tm24, tr, tf⟩ := sub140_spec h u upc
    (by rw [ur.get (by simp)]; exact t1x30)
  have g : ∀ X, X < 2 ^ 64 → X ≠ NODE + 24 → t.getMem (BitVec.ofNat 64 X) = t1.getMem (BitVec.ofNat 64 X) :=
    fun X hX hn => (tf.get hX hn).trans (uf.get hX (fun h => h))
  refine ⟨t, (st1.trans (stu.trans stt)).of_eq (by omega) (by omega),
    tpc, tx10, tx11, tx12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g NODE (by decide) (by decide), m0]
  · rw [g (NODE + 8) (by decide) (by decide), m8]
  · rw [g (NODE + 16) (by decide) (by decide), m16]
  · rw [tm24, ux7]
  · rw [g (NODE + 48) (by decide) (by decide), m48]
  · rw [g (NODE + 56) (by decide) (by decide), m56]
  · exact ((t1r.trans ur).trans tr).mono (by decide)
  · refine ((t1f.trans uf).trans tf).mono (fun X _ hX => ?_)
    rcases hX with (hX | hX) | hX
    · rcases hX with hX | hX | hX | hX | hX <;> simp [hX]
    · exact hX.elim
    · simp [hX]
theorem fetch_sub146 {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 146)) : fetch image s = some (.base .ECALL) :=
  ((SeedIndependent.codeAt_sub_146 h).fetch s hpc).trans rfl
theorem sub147_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 147)) (arena k : Nat) (ha8 : arena % 8 = 0) (hk : arena + 16 * k + 16 ≤ 2 ^ 24)
    (hdis : NOUT + 16 ≤ arena + 16 * k ∨ arena + 16 * k + 16 ≤ NOUT)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf (b + 118) ∧ t.getReg .x24 = BitVec.ofNat 64 (k + 1) ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x24, .x28, .x29] ∧
      Frame s t (fun X => X = arena + 16 * k ∨ X = arena + 16 * k + 8) := by
  have hrun := run_147 h.2.1
  have hobl : Oblig.all s st_147.obl := by
    simp only [st_147, blk117_147.res]
    t3n [h2, h24]
    omega
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_147 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_147, Result.toState_pc, E.eval]
  · t3n [st_147, blk117_147.res, h24]
  · simp only [Result.toState_getMem, st_147, blk117_147.res]
    t3n [h2, h24]
    simp only [NOUT] at hdis ⊢
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, st_147, blk117_147.res]
    t3n [h2, h24]
    simp only [NOUT] at hdis ⊢
    rw [if_pos (by omega)]
  · intro r hr; simp at hr; cases r <;> simp_all [st_147, blk117_147.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [Result.toState_getMem, st_147, blk117_147.res]
    t3n [h2, h24]
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub157_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 157)) (lo : Nat) (hlo : lo < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 116) ∧ t.getReg .x20 = BitVec.ofNat 64 (lo / 2) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_157 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_157 h) s hpc (by simp [st_157, blk117_157.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_157, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, st_157, blk117_157.res, rv_simp, h20]
    rw [ofNat_shr _ _ hlo]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [st_157, blk117_157.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_157, blk117_157.res, rv_simp]
theorem sub159_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 159)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_159 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_159 h) s hpc (by simp [st_159, blk117_159.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_159, blk117_159.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_159, blk117_159.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_159, blk117_159.res, rv_simp]
section lev
variable {image : Image} {b : Nat} (hsub : SeedIndependentAt image b) (sk : BitVec 256) {s0 : MachineState}
  {B : LevArgs} {leaves : List Digest} (hpre : LevPre s0 B leaves)
include hsub hpre
theorem lev_node {ℓ : Nat} (hl : ℓ < B.h) {levels : List (List Digest)} {pre : List Digest}
    (hi : pre.length < 2 ^ (B.h - ℓ - 1)) {t : MachineState} (ht : NodeInv s0 B ℓ levels pre t)
    (hpc : t.pc = pcOf (b + 118)) :
    TSim image sk t (39 + revX B.tag) (46 + revX B.tag) 1 1
      (nodeHash B.tag B.lay B.tree (2 ^ (B.h - (ℓ + 1)) + pre.length)
        ((levels.getD ℓ []).getD (2 * pre.length) 0) ((levels.getD ℓ []).getD (2 * pre.length + 1) 0))
      (fun v u => u.pc = pcOf (b + 118) ∧ NodeInv s0 B ℓ levels (pre ++ [v]) u) := by
  have hh := hpre.hh
  have ha := hpre.ha
  have has := hpre.has
  have ha8 := hpre.ha8
  set lo := 2 ^ (B.h - ℓ - 1) with hlo_def
  set i := pre.length with hi_def
  have hY : 2 ^ (B.h - ℓ) = 2 * lo := two_pow_split hl
  have hYZ : 2 ^ (B.h - ℓ) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hW : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
  have hZ : 2 ^ B.h ≤ 4096 := by
    calc 2 ^ B.h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have hk' : 2 ^ (B.h - (ℓ + 1)) = lo := by rw [hlo_def]; congr 1
  have g : ∀ r, r ∉ levRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r2 : t.getReg .x2 = BitVec.ofNat 64 B.arena := by rw [g _ (by simp [levRegs]), hpre.x2]
  have r9 : t.getReg .x9 = BitVec.ofNat 64 B.tree := by rw [g _ (by simp [levRegs]), hpre.x9]
  have r5 : t.getReg .x5 = 0 := by rw [g _ (by simp [levRegs]), hpre.x5]
  have r21 : t.getReg .x21 = BitVec.ofNat 64 (hdr0 B.tag B.lay B.tree 0) := by
    rw [g _ (by simp [levRegs]), hpre.x21]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub118_spec hsub t hpc lo (lo + i) (by omega) (by omega) ht.x20 ht.x24
  rw [if_pos (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x10, t2x11, t2x12, t2n0, t2n8, t2n16, t2n24, t2n48, t2n56, t2r, t2f⟩ :=
    sub120_full hsub t1 t1pc B.tag B.lay B.arena (lo + i) B.tree hpre.tag3 ha8 (by omega) (by omega) hpre.htree
      (by simp only [NODE, NOUT] at has ⊢; omega) (by rw [t1r.get (by simp)]; exact r2)
      (by rw [t1r.get (by simp)]; exact ht.x24) (by rw [t1r.get (by simp)]; exact r9)
      (by rw [t1r.get (by simp)]; exact r21)
  obtain ⟨hlen, hlev⟩ := ht.heap
  obtain ⟨hll, hlv⟩ := hlev ℓ le_rfl
  have hL : DigAt t (B.arena + 32 * (lo + i)) ((levels.getD ℓ []).getD (2 * i) 0) := by
    have := hlv.get (i := 2 * i) (by rw [hll, hY]; omega)
    rwa [hY, show B.arena + 16 * (2 * lo) + 16 * (2 * i) = B.arena + 32 * (lo + i) by ring] at this
  have hR : DigAt t (B.arena + 32 * (lo + i) + 16) ((levels.getD ℓ []).getD (2 * i + 1) 0) := by
    have := hlv.get (i := 2 * i + 1) (by rw [hll, hY]; omega)
    rwa [hY, show B.arena + 16 * (2 * lo) + 16 * (2 * i + 1) = B.arena + 32 * (lo + i) + 16 by ring] at this
  have hL1 := hL.frame t1f (by omega) (by simp) (by simp)
  have hR1 := hR.frame t1f (by omega) (by simp) (by simp)
  have fr : ∀ X, (X = NODE + 32 ∨ X = NODE + 40) → t2.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := by
    intro X hX
    have hX' : X < 2 ^ 64 := by rcases hX with h | h <;> (rw [h]; decide)
    rw [t2f.get hX' (by simp only [NODE] at hX ⊢; omega), t1f.get hX' (by simp),
      ht.frame.get hX' (by unfold LevW; simp only [NODE, NOUT] at hX has ⊢; omega)]
  have hq : hashInput t2 = toQ (pad64 (bytesLE 16 ((levels.getD ℓ []).getD (2 * i) 0) ++
      bytesLE 16 (header B.tag B.lay B.tree 0 (lo + i)) ++ zero16 ++
      bytesLE 16 ((levels.getD ℓ []).getD (2 * i + 1) 0))) := by
    rw [pad64_of_aligned _ (by rw [nodeInput_length])]
    refine hashInput_toQ t2 _ 0 NODE (nodeInput_length _ _ _ _ _ _) t2x10 (by decide) (by decide) t2x11
      (by decide) ?_
    rw [wordsOf_nodeInput _ _ _ _ _ _ (by rcases hpre.tag3 with h | h <;> rw [h] <;> decide), readWords_eight, t2n0, t2n8, t2n16, t2n24, fr (NODE + 32) (by simp),
      fr (NODE + 40) (by simp), t2n48, t2n56, hpre.z32, hpre.z40, hL1.1, hL1.2, hR1.1, hR1.2,
      t1r.get (by simp), r21, hdr0_or_tree B.tag B.lay B.tree hpre.htree]
  have hv : hashArgumentsValid t2 = true :=
    hashArgs_const t2 NODE 64 NOUT t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h5 : t2.getReg .x5 = 0 := by rw [t2r.get (by simp), t1r.get (by simp), r5]
  have hblk : (toQ (pad64 (bytesLE 16 ((levels.getD ℓ []).getD (2 * i) 0) ++
      bytesLE 16 (header B.tag B.lay B.tree 0 (lo + i)) ++ zero16 ++
      bytesLE 16 ((levels.getD ℓ []).getD (2 * i + 1) 0)))).blocks = 1 := by
    rw [pad64_of_aligned _ (by rw [nodeInput_length]),
      blocks_toQ ⟨by rw [nodeInput_length]; omega, by rw [nodeInput_length]⟩, nodeInput_length]
  unfold nodeHash
  rw [hk']
  refine (TSim.steps (st1.trans st2)
    ((TSim.shortHash_bind (k := 10) (c := 10) (n := 0) (b := 0) (f := Pure.pure)
      (fetch_sub146 hsub t2 t2pc) h5 hv hq (fun a => ?_)).of_eq (bind_pure _) rfl rfl rfl rfl)).of_eq
    rfl ?_ ?_ ?_ ?_
  · have hwf := Frame.writeHash t2 a NOUT t2x12 (by decide)
    obtain ⟨u, st3, upc, ux24, um0, um8, ur, uf⟩ := sub147_spec hsub (writeHash t2 a)
      (by rw [pc_writeHash, t2pc, pcOf_add4]) B.arena (lo + i) ha8 (by omega)
      (by sc_omega)
      (by rw [getReg_writeHash, t2r.get (by simp), t1r.get (by simp)]; exact r2)
      (by rw [getReg_writeHash, t2r.get (by simp), t1r.get (by simp)]; exact ht.x24)
    have hlo := DigAt.writeHash_lo t2 a NOUT t2x12 (by decide)
    have hnew : DigAt u (B.arena + 16 * (lo + i)) (a.extractLsb' 0 128) := ⟨um0.trans hlo.1, by
      rw [um8]; exact hlo.2⟩
    have fall : Frame t u (fun X => (X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨
        X = NODE + 48 ∨ X = NODE + 56) ∨ (NOUT ≤ X ∧ X < NOUT + 32) ∨
        (X = B.arena + 16 * (lo + i) ∨ X = B.arena + 16 * (lo + i) + 8)) :=
      ((t1f.trans t2f).trans (hwf.trans uf)).mono (fun X _ h => by
        rcases h with (h | h) | (h | h)
        · exact h.elim
        · left; exact h
        · right; left; exact h
        · right; right; exact h)
    refine TSim.pure_steps st3 ⟨upc, ⟨?_, ?_, ?_, ?_, ⟨hlen, fun l hl' => ?_⟩, ?_⟩⟩
    · rw [ur.get (by simp), getReg_writeHash, t2r.get (by simp), t1r.get (by simp)]; exact ht.x20
    · rw [ux24, List.length_append, List.length_singleton]; congr 1
    · have hw0 : RegsExcept t2 (writeHash t2 a) [] := fun r _ => getReg_writeHash t2 a r
      exact (ht.regs.trans (((t1r.trans t2r).trans hw0).trans ur)).mono (by decide)
    · refine (ht.frame.trans fall).mono (fun X _ h => ?_)
      unfold LevW at *
      rcases h with h | (h | h | h)
      · exact h
      · rcases h with h | h | h | h | h | h <;> simp_all
      · right; right; right; right; right; right; left; exact h
      · right; right; right; right; right; right; right; simp only [NODE, NOUT] at has; omega
    · obtain ⟨hl1, hl2⟩ := hlev l hl'
      have hYl : 2 * lo ≤ 2 ^ (B.h - l) := by
        rw [← hY]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hYlZ : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine ⟨hl1, hl2.frame fall (by rw [hl1]; omega) (fun X h1 h2 h => ?_)⟩
      rw [hl1] at h2
      simp only [NODE, NOUT] at h has
      omega
    · refine (ht.cur.frame fall (by omega) (fun X h1 h2 h => ?_)).snoc ?_
      · simp only [NODE, NOUT] at h has
        omega
      · rw [show B.arena + 16 * lo + 16 * i = B.arena + 16 * (lo + i) by ring]; exact hnew
  all_goals (try rw [hblk])
  all_goals (first | rfl | omega)
theorem lev_level {ℓ : Nat} (hl : ℓ < B.h) {levels : List (List Digest)} {t : MachineState}
    (ht : LevInv s0 B ℓ levels t) (hpc : t.pc = pcOf (b + 116)) :
    TSim image sk t (6 + (39 + revX B.tag) * 2 ^ (B.h - 1 - ℓ)) (6 + (46 + revX B.tag) * 2 ^ (B.h - 1 - ℓ))
      (2 ^ (B.h - 1 - ℓ))
      (2 ^ (B.h - 1 - ℓ))
      (do let nodes ← buildLevel B.tag B.lay B.tree B.h (1 + ℓ) (levels.getD (1 + ℓ - 1) [])
          pure (levels ++ [nodes]))
      (fun levels' u => u.pc = pcOf (b + 116) ∧ LevInv s0 B (ℓ + 1) levels' u) := by
  have hh := hpre.hh
  set lo := 2 ^ (B.h - ℓ - 1) with hlo_def
  have hY : 2 ^ (B.h - ℓ) = 2 * lo := two_pow_split hl
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have hloZ : lo ≤ 2048 := by
    calc lo ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2048 := by norm_num
  have hx20 : 2 ^ B.h / 2 ^ (ℓ + 1) = lo := by
    rw [hlo_def, show B.h = (ℓ + 1) + (B.h - ℓ - 1) by omega, Nat.pow_add, Nat.mul_div_cancel_left _
      (by positivity)]
    congr 1; omega
  have hx20' : 2 ^ B.h / 2 ^ (ℓ + 1 + 1) = lo / 2 := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hx20]
  have hl1 : 2 ^ (B.h - 1 - ℓ) = lo := by rw [hlo_def]; congr 1; omega
  have r20 : t.getReg .x20 = BitVec.ofNat 64 lo := by rw [ht.x20, hx20]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub116_spec hsub t hpc lo (by omega) r20
  rw [if_neg (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x24, t2r, t2f⟩ := sub117_spec hsub t1 t1pc
  have f02 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  have h0 : NodeInv s0 B ℓ levels [] t2 := by
    refine ⟨?_, ?_, ?_, (ht.frame.trans f02).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim),
      ⟨ht.heap.1, fun l hl' => ⟨(ht.heap.2 l hl').1, (ht.heap.2 l hl').2.frame f02 (by
        rw [(ht.heap.2 l hl').1]
        have := hpre.ha
        have : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
        omega) (fun X _ _ h => h.elim)⟩⟩, DigsAt.nil _ _⟩
    · rw [t2r.get (by simp), t1r.get (by simp), r20]
    · rw [t2x24, t1r.get (by simp), r20, List.length_nil, Nat.add_zero]
    · exact (ht.regs.trans (t1r.trans t2r)).mono (by decide)
  have hnodes : (levels.getD (1 + ℓ - 1) []).length / 2 = lo := by
    rw [show 1 + ℓ - 1 = ℓ by omega, (ht.heap.2 ℓ le_rfl).1, hY]; omega
  unfold buildLevel
  rw [hnodes]
  refine (TSim.steps (st1.trans st2) (TSim.bind (k₂ := 4) (c₂ := 4) (n₂ := 0) (b₂ := 0)
    (TSim.mapM_range lo _ (fun _ => 39 + revX B.tag) (fun _ => 46 + revX B.tag) (fun _ => 1) (fun _ => 1)
      (fun pre w => w.pc = pcOf (b + 118) ∧ NodeInv s0 B ℓ levels pre w)
      (fun pre w hpre' hw => ?_) ⟨t2pc, h0⟩) (fun nodes w hw => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · rw [show 1 + ℓ - 1 = ℓ by omega, show 1 + ℓ = ℓ + 1 by omega]
    exact lev_node hsub sk hpre hl hpre' hw.2 hw.1
  · obtain ⟨hlen, wpc, hw⟩ := hw
    obtain ⟨w1, st3, w1pc, w1r, w1f⟩ := sub118_spec hsub w wpc lo (lo + nodes.length) (by omega) (by omega)
      hw.x20 (by rw [hw.x24])
    rw [if_neg (by omega)] at w1pc
    obtain ⟨w2, st4, w2pc, w2x20, w2r, w2f⟩ := sub157_spec hsub w1 w1pc lo (by omega)
      (by rw [w1r.get (by simp)]; exact hw.x20)
    have f12 : Frame w w2 (fun _ => False) := (w1f.trans w2f).mono (fun X _ h => by simp_all)
    refine TSim.pure_steps (st3.trans st4) ⟨w2pc, ?_, ?_, ?_, ?_⟩
    · rw [w2x20, hx20']
    · exact (hw.regs.trans (w1r.trans w2r)).mono (by decide)
    · exact (hw.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
    · obtain ⟨hlen0, hlev⟩ := hw.heap
      refine ⟨by simp [hlen0], fun l hl' => ?_⟩
      have hZ : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
      have := hpre.ha
      by_cases hle : l ≤ ℓ
      · have hg : (levels ++ [nodes]).getD l [] = levels.getD l [] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show l < levels.length by omega)]
        rw [hg]
        obtain ⟨h1, h2⟩ := hlev l hle
        have : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact ⟨h1, h2.frame f12 (by rw [h1]; omega) (fun X _ _ h => h.elim)⟩
      · have hl2 : l = ℓ + 1 := by omega
        subst hl2
        have hg : (levels ++ [nodes]).getD (ℓ + 1) [] = nodes := by
          simp [List.getD_eq_getElem?_getD, hlen0]
        rw [hg, show B.h - (ℓ + 1) = B.h - ℓ - 1 by omega]
        have : lo ≤ 2 ^ B.h := by
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show B.h - ℓ - 1 ≤ B.h by omega)
          omega
        exact ⟨hlen, hw.cur.frame f12 (by rw [hlen]; omega) (fun X _ _ h => h.elim)⟩
  all_goals simp only [sumTo_const, hl1]
  all_goals (first | omega | ring)
theorem buildLevels_tsim (hpc : s0.pc = pcOf (b + 113)) :
    TSim image sk s0 B.levK B.levC B.levN B.levN (buildLevels B.tag B.lay B.tree B.h leaves)
      (fun levels t => t.pc = pcOf B.ret ∧ HeapAt t B B.h levels ∧ RegsExcept s0 t levRegs ∧
        Frame s0 t (LevW B)) := by
  have hh := hpre.hh
  have hh1 := hpre.hh1
  have ha := hpre.ha
  have hZ : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
  obtain ⟨t1, st1, t1pc, t1x20, t1r, t1f⟩ := sub113_spec hsub s0 hpc B.h hh1 (by omega) hpre.x15
  have h0 : LevInv s0 B 0 [leaves] t1 := by
    refine ⟨?_, t1r.mono (by decide), t1f.mono (fun X _ h => h.elim), ⟨rfl, fun l hl => ?_⟩⟩
    · rw [t1x20]; congr 1
      rw [show B.h = 1 + (B.h - 1) by omega, Nat.pow_add, Nat.mul_div_cancel_left _ (by norm_num)]
      congr 1; omega
    · have hl0 : l = 0 := by omega
      subst hl0
      simp only [List.getD_cons_zero, Nat.sub_zero]
      exact ⟨hpre.hlen, hpre.hleaves.frame t1f (by rw [hpre.hlen]; omega) (fun X _ _ h => h.elim)⟩
  unfold buildLevels
  refine (TSim.steps st1 (TSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0) (f := Pure.pure)
    (TSim.foldlM_range' 1 B.h _ [leaves]
      (fun j levels t => t.pc = pcOf (b + 116) ∧ LevInv s0 B j levels t)
      (fun j => 6 + (39 + revX B.tag) * 2 ^ (B.h - 1 - j)) (fun j => 6 + (46 + revX B.tag) * 2 ^ (B.h - 1 - j))
      (fun j => 2 ^ (B.h - 1 - j)) (fun j => 2 ^ (B.h - 1 - j))
      (fun j hj levels t ht => lev_level hsub sk hpre hj ht.2 ht.1) ⟨t1pc, h0⟩)
    (fun levels t ht => ?_))).of_eq (bind_pure _) ?_ ?_ ?_ ?_
  · obtain ⟨tpc, hinv⟩ := ht
    have hx : 2 ^ B.h / 2 ^ (B.h + 1) = 0 := Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
    obtain ⟨u1, st2, u1pc, u1r, u1f⟩ := sub116_spec hsub t tpc 0 (by omega) (by rw [hinv.x20, hx])
    rw [if_pos rfl] at u1pc
    obtain ⟨u2, st3, u2pc, u2r, u2f⟩ := sub159_spec hsub u1 u1pc B.ret
      (by rw [u1r.get (by simp), hinv.regs.get (by simp [levRegs]), hpre.x1])
    have f12 : Frame t u2 (fun _ => False) := (u1f.trans u2f).mono (fun X _ h => by simp_all)
    refine TSim.pure_steps (st2.trans st3) ⟨u2pc, ⟨hinv.heap.1, fun l hl => ?_⟩,
      (hinv.regs.trans (u1r.trans u2r)).mono (by decide),
      (hinv.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)⟩
    obtain ⟨h1, h2⟩ := hinv.heap.2 l hl
    have : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact ⟨h1, h2.frame f12 (by rw [h1]; omega) (fun X _ _ h => h.elim)⟩
  all_goals simp only [LevArgs.levK, LevArgs.levC, LevArgs.levN]
  all_goals omega
end lev
end SigGolfCandidate.T3M.Sign.Seed
end

section





section
namespace SigGolfCandidate.T3M.Sign.Packed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
macro "packed_sgo" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, MOUT, ZDIG, DUMMY, TOP, MACBLK,
    REGION, MSG, SK, SIG, CACHE, NONCE, RHOOUT, DIG, NBUF, ENC, EOUT, FLEAF, LFOUT, FOREST, FOUT, MACOUT, TAG,
    DIGITS, SEL, IDXV, LOW, FTS, SEC, false_or, or_false] at *) <;> omega))
theorem ofNat_xor1 (v : Nat) (hv : v < 2 ^ 64) : BitVec.ofNat 64 v ^^^ 1#64 = BitVec.ofNat 64 (v ^^^ 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, toNat_ofNat_lt hv, toNat_ofNat_lt (Nat.xor_lt_two_pow hv (by norm_num))]
  rfl
theorem toNat_mod64 (l : Nat) (hl : l < 64) : (BitVec.ofNat 64 l).toNat % 64 = l := by
  rw [toNat_ofNat_lt (by omega)]; omega
theorem blk1173_spec (s : MachineState) (hpc : s.pc = pcOf 1173) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1175 ∧ t.getReg .x4 = s.getReg .x1 ∧
      t.getReg .x13 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x4, .x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1173 codeAt_1173 s hpc (by simp [blk_1173.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1173.res, E.eval]
  · simp [blk_1173.res, rv_simp]
  · simp [blk_1173.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1173.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1173.res, rv_simp]
theorem blk1175_spec (s : MachineState) (hpc : s.pc = pcOf 1175) (l h : Nat) (hl : l < 2 ^ 63) (hh : h ≤ 12)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h15 : s.getReg .x15 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if l < 2 ^ h then pcOf 1178 else pcOf 1193) ∧
      t.getReg .x6 = BitVec.ofNat 64 (2 ^ h) ∧ RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hp : 2 ^ h ≤ 4096 := by
    calc 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  have e : (1#64 : Word) <<< ((BitVec.ofNat 64 h).toNat % 64) = BitVec.ofNat 64 (2 ^ h) := by
    rw [toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega), show (1#64 : Word) = BitVec.ofNat 64 1 from rfl,
      ofNat_shl, Nat.one_mul]
  refine ⟨_, symRun_sound blk_1175 codeAt_1175 s hpc (by simp [blk_1175.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1175.res, E.eval, CmpOp.eval, BinOp.eval, h13, h15, e,
      ofNat_slt l (2 ^ h) hl (by omega)]
    by_cases hc : l < 2 ^ h <;> simp [hc]
  · simp only [Result.toState_getReg, blk_1175.res, rv_simp, BinOp.eval, h15, e]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1175.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1175.res, rv_simp]
theorem blk1178_spec (s : MachineState) (hpc : s.pc = pcOf 1178) (l sel : Nat) (hl : l < 2 ^ 64)
    (hsel : sel < 2 ^ 64) (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h14 : s.getReg .x14 = BitVec.ofNat 64 sel) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = (if l = sel then pcOf 1184 else pcOf 1187) ∧
      t.getReg .x18 = BitVec.ofNat 64 l ∧ t.getReg .x22 = BitVec.ofNat 64 ZDIG ∧
      t.getReg .x23 = BitVec.ofNat 64 DUMMY ∧ RegsExcept s t [.x18, .x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1178 codeAt_1178 s hpc (by simp [blk_1178.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1178.res, E.eval, CmpOp.eval, h13, h14]
    by_cases hc : l = sel
    · subst hc; simp
    · rw [if_neg hc]
      have : BitVec.ofNat 64 l ≠ BitVec.ofNat 64 sel := fun he => hc ((ofNat_inj hl hsel).mp he)
      simp [this]
  · simp only [Result.toState_getReg, blk_1178.res]; t3n [h13]
  · simp [blk_1178.res, rv_simp]
  · simp [blk_1178.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1178.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1178.res, rv_simp]
theorem blk1184_spec (s : MachineState) (hpc : s.pc = pcOf 1184) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 1187 ∧ t.getReg .x22 = BitVec.ofNat 64 DIGITS ∧
      t.getReg .x23 = s.getReg .x16 ∧ RegsExcept s t [.x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1184 codeAt_1184 s hpc (by simp [blk_1184.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1184.res, E.eval]
  · simp [blk_1184.res, rv_simp]
  · simp [blk_1184.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1184.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1184.res, rv_simp]
theorem blk1187_spec (s : MachineState) (hpc : s.pc = pcOf 1187) (l h ar : Nat) (hl : l < 2 ^ h)
    (hh : h ≤ 12) (har : ar + 16 * 8192 < 2 ^ 64)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h6 : s.getReg .x6 = BitVec.ofNat 64 (2 ^ h))
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (1013 + 27) ∧ t.getReg .x1 = pcOf 1191 ∧
      t.getReg .x25 = BitVec.ofNat 64 (ar + 16 * (2 ^ h + l)) ∧
      RegsExcept s t [.x1, .x7, .x25] ∧ Frame s t (fun _ => False) := by
  have hp : 2 ^ h ≤ 4096 := by
    calc 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  refine ⟨_, symRun_sound blk_1187 codeAt_1187 s hpc (by simp [blk_1187.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1187.res, E.eval]
  · simp [blk_1187.res, rv_simp]
  · simp only [Result.toState_getReg, blk_1187.res]; t3n [h13, h6, h2]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1187.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1187.res, rv_simp]
theorem blk1191_spec (s : MachineState) (hpc : s.pc = pcOf 1191) (l : Nat)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1175 ∧ t.getReg .x13 = BitVec.ofNat 64 (l + 1) ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1191 codeAt_1191 s hpc (by simp [blk_1191.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_1191.res, E.eval]
  · simp only [Result.toState_getReg, blk_1191.res]; t3n [h13]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1191.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1191.res, rv_simp]
theorem blk1193_spec (s : MachineState) (hpc : s.pc = pcOf 1193) (lay : Nat) (hlay : lay < 256)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (1013 + 113) ∧ t.getReg .x1 = pcOf 1196 ∧
      t.getReg .x21 = BitVec.ofNat 64 (769 + 65536 * lay) ∧
      RegsExcept s t [.x1, .x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1193 codeAt_1193 s hpc (by simp [blk_1193.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1193.res, E.eval]
  · simp [blk_1193.res, rv_simp]
  · simp only [Result.toState_getReg, blk_1193.res]
    t3n [h8]
    rw [show (769#64 : Word) = BitVec.ofNat 64 769 from rfl,
      ofNat_or_disjoint 769 (lay * 65536) 16 (by norm_num) (by omega)]
    congr 1; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1193.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1193.res, rv_simp]
theorem blk1196_spec (s : MachineState) (hpc : s.pc = pcOf 1196) (h sel sb n : Nat) (hh : h ≤ 12)
    (hsel : sel < 4096) (hsb : sb + 16 * n < 2 ^ 64)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 h) (h14 : s.getReg .x14 = BitVec.ofNat 64 sel)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 sb) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf 1202 ∧ t.getReg .x13 = BitVec.ofNat 64 0 ∧
      t.getReg .x19 = BitVec.ofNat 64 (2 ^ h + sel) ∧ t.getReg .x24 = BitVec.ofNat 64 (sb + 16 * n) ∧
      RegsExcept s t [.x6, .x7, .x13, .x19, .x24] ∧ Frame s t (fun _ => False) := by
  have hp : 2 ^ h ≤ 4096 := by
    calc 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  have e : (1#64 : Word) <<< ((BitVec.ofNat 64 h).toNat % 64) = BitVec.ofNat 64 (2 ^ h) := by
    rw [toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega), show (1#64 : Word) = BitVec.ofNat 64 1 from rfl,
      ofNat_shl, Nat.one_mul]
  refine ⟨_, symRun_sound blk_1196 codeAt_1196 s hpc (by simp [blk_1196.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1196.res, E.eval]
  · simp [blk_1196.res, rv_simp]
  · simp only [Result.toState_getReg, blk_1196.res, rv_simp, BinOp.eval, h15, h14, e, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, blk_1196.res]; t3n [h16, h26]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1196.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1196.res, rv_simp]
theorem blk1202_spec (s : MachineState) (hpc : s.pc = pcOf 1202) (l h : Nat) (hl : l < 2 ^ 63) (hh : h < 2 ^ 63)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h15 : s.getReg .x15 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if l < h then pcOf 1203 else pcOf 1214) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1202 codeAt_1202 s hpc (by simp [blk_1202.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1202.res, E.eval, CmpOp.eval, h13, h15, ofNat_slt l h hl hh]
    by_cases hc : l < h <;> simp [hc]
  · intro r hr; cases r <;> simp_all [blk_1202.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1202.res, rv_simp]
theorem blk1203_spec (s : MachineState) (hpc : s.pc = pcOf 1203) (l hi ar ep : Nat) (hl : l < 64)
    (hhi : hi < 8192) (har : ar + 16 * 8192 ≤ 2 ^ 24) (har8 : ar % 8 = 0) (hep : ep + 16 ≤ 2 ^ 24)
    (hep8 : ep % 8 = 0)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h19 : s.getReg .x19 = BitVec.ofNat 64 hi)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) (h24 : s.getReg .x24 = BitVec.ofNat 64 ep) :
    ∃ t, Steps image s 11 11 t ∧ t.pc = pcOf 1202 ∧ t.getReg .x13 = BitVec.ofNat 64 (l + 1) ∧
      t.getReg .x24 = BitVec.ofNat 64 (ep + 16) ∧
      t.getMem (BitVec.ofNat 64 ep) = s.getMem (BitVec.ofNat 64 (ar + 16 * (hi / 2 ^ l ^^^ 1))) ∧
      t.getMem (BitVec.ofNat 64 (ep + 8)) = s.getMem (BitVec.ofNat 64 (ar + 16 * (hi / 2 ^ l ^^^ 1) + 8)) ∧
      RegsExcept s t [.x6, .x7, .x13, .x24, .x28] ∧ Frame s t (fun A => A = ep ∨ A = ep + 8) := by
  have hd : hi / 2 ^ l < 8192 := lt_of_le_of_lt (Nat.div_le_self _ _) hhi
  have hx : hi / 2 ^ l ^^^ 1 < 8192 := Nat.xor_lt_two_pow (n := 13) hd (by norm_num)
  have e1 : BitVec.ofNat 64 hi >>> ((BitVec.ofNat 64 l).toNat % 64) ^^^ 1#64 =
      BitVec.ofNat 64 (hi / 2 ^ l ^^^ 1) := by
    rw [toNat_mod64 l hl, ofNat_shr hi l (by omega), ofNat_xor1 _ (by omega)]
  have hobl : Oblig.all s blk_1203.res.st.obl := by
    simp only [blk_1203.res]
    simp only [rv_simp, h13, h19, h2, h24, e1]
    t3n []
    omega
  refine ⟨_, symRun_sound blk_1203 codeAt_1203 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1203.res, E.eval]
  · simp only [Result.toState_getReg, blk_1203.res]; t3n [h13]
  · simp only [Result.toState_getReg, blk_1203.res]; t3n [h24]
  · simp only [Result.toState_getMem, blk_1203.res]
    simp only [rv_simp, h13, h19, h2, h24, e1]
    t3n []
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
    congr 2; omega
  · simp only [Result.toState_getMem, blk_1203.res]
    simp only [rv_simp, h13, h19, h2, h24, e1]
    t3n []
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1203.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, blk_1203.res]
    t3n [h24]
    rw [if_neg (by omega), if_neg (by omega)]
end SigGolfCandidate.T3M.Sign.Packed
end
section
namespace SigGolfCandidate.T3M.Sign.Packed.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def entryCode : List (BitVec 32) := [134967,638521107,0xc90906f]
def pairCode : List (BitVec 32) := [33633027,42021763,7286819,8336419,50410243,58798979,40843299,41892899,131175]
theorem entry_at : CodeAt image (pcOf 1214) entryCode :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem pair_at : CodeAt image (pcOf 10994) pairCode :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
sym_block entryBlock := symRun { noAlias := true } entryCode (pcOf 1214) 20
sym_block pairBlock := symRun { noAlias := true } pairCode (pcOf 10994) 20
theorem pair_spec (s : MachineState) (hpc : s.pc = pcOf 10994) (ar ret : Nat)
    (har : ar + 64 ≤ 2 ^ 24) (har8 : ar % 8 = 0)
    (hsep : ENC + 64 ≤ ar ∨ ar + 64 ≤ ENC)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) (h4 : s.getReg .x4 = pcOf ret)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 ENC) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 (ar + 32)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (ar + 40)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (ar + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (ar + 56)) ∧
      RegsExcept s t [.x6, .x7] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  have hobl : Oblig.all s pairBlock.res.st.obl := by
    simp only [pairBlock.res]
    t3n [h2, h30, ENC]
    simp only [ENC] at hsep
    simp only [and_true]
    omega
  refine ⟨_, symRun_sound pairBlock pair_at s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pairBlock.res, rv_simp, h4, pcOf_and_max]
  · simp only [Result.toState_getMem, pairBlock.res, ENC]
    t3n [h2, h30, ENC]
  · simp only [Result.toState_getMem, pairBlock.res, ENC]
    t3n [h2, h30, ENC]
  · simp only [Result.toState_getMem, pairBlock.res, ENC]
    t3n [h2, h30, ENC]
  · simp only [Result.toState_getMem, pairBlock.res, ENC]
    t3n [h2, h30, ENC]
  · intro r hr; simp at hr; cases r <;> simp_all [pairBlock.res, rv_simp]; rfl
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, pairBlock.res]
    t3n [h30, ENC]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem entry_spec (s : MachineState) (hpc : s.pc = pcOf 1214) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 10994 ∧
      t.getReg .x30 = BitVec.ofNat 64 ENC ∧ RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound entryBlock entry_at s hpc (by simp [entryBlock.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, entryBlock.res, rv_simp, pcOf]
  · simp [Result.toState_getReg, entryBlock.res, rv_simp, ENC]
  · intro r hr; simp at hr; cases r <;> simp_all [entryBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, entryBlock.res, rv_simp]
theorem blk1214_pair_spec (s : MachineState) (hpc : s.pc = pcOf 1214) (ar ret : Nat)
    (har : ar + 64 ≤ 2 ^ 24) (har8 : ar % 8 = 0)
    (hsep : ENC + 64 ≤ ar ∨ ar + 64 ≤ ENC)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) (h4 : s.getReg .x4 = pcOf ret) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 (ar + 32)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (ar + 40)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (ar + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (ar + 56)) ∧
      RegsExcept s t [.x6, .x7, .x30] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  obtain ⟨u, su, upc, u30, ur, uf⟩ := entry_spec s hpc
  obtain ⟨t, ut, tpc, m0, m8, m48, m56, tr, tf⟩ := pair_spec u upc ar ret har har8 hsep
    (by rw [ur.get (by simp), h2]) (by rw [ur.get (by simp), h4]) u30
  refine ⟨t, su.trans ut, tpc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m0, uf.get (by omega) (by simp)]
  · rw [m8, uf.get (by omega) (by simp)]
  · rw [m48, uf.get (by omega) (by simp)]
  · rw [m56, uf.get (by omega) (by simp)]
  · exact (ur.trans tr).mono (by decide)
  · exact (uf.trans tf).mono (by intro A hA h; simpa using h)
#print axioms blk1214_pair_spec
end SigGolfCandidate.T3M.Sign.Packed.BCBlocks
end
section
namespace SigGolfCandidate.T3M.Sign.Packed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest buildLeaf buildLevels buildTree height chainCount width)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION
  LeafArgs LeafPre LeafW leafRegs LevArgs LevPre HeapAt LevW levRegs n4 buildLeaf_tsim buildLevels_tsim)
def memDig (t : MachineState) (A : Nat) : Digest := t.getMem (BitVec.ofNat 64 (A + 8)) ++ t.getMem (BitVec.ofNat 64 A)
theorem memDig_toNat (t : MachineState) (A : Nat) :
    (memDig t A).toNat = (t.getMem (BitVec.ofNat 64 (A + 8))).toNat * 2 ^ 64 + (t.getMem (BitVec.ofNat 64 A)).toNat := by
  rw [memDig, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (t.getMem (BitVec.ofNat 64 A)).isLt,
    Nat.shiftLeft_eq]
theorem memDig_digAt (t : MachineState) (A : Nat) : DigAt t A (memDig t A) := by
  have h1 := (t.getMem (BitVec.ofNat 64 A)).isLt
  have h2 := (t.getMem (BitVec.ofNat 64 (A + 8))).isLt
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, memDig_toNat, Nat.shiftRight_zero]
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, memDig_toNat, Nat.shiftRight_eq_div_pow]
    omega
theorem memDig_eq {t : MachineState} {A : Nat} {d : Digest} (h : DigAt t A d) : memDig t A = d := by
  apply BitVec.eq_of_toNat_eq
  rw [memDig_toNat, h.1, h.2, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.shiftRight_eq_div_pow]
  have := d.isLt
  omega
abbrev LeafFn := Layer → Nat → Nat → List Nat → Digest → T3.M ((Digest × List Digest) × Digest)
def topPair (lay : Layer) (levels : List (List Digest)) : Digest × Digest :=
  ((levels.getD (height lay - 1) []).getD 0 0, (levels.getD (height lay - 1) []).getD 1 0)
def PackedLeafSpec (leafFn : LeafFn) : Prop :=
  ∀ (sk : SecretKey) (A : LeafArgs) (s : MachineState) (carry : Digest),
    A.lay ≠ 0 → A.so = false → LeafPreS sk s A → s.pc = pcOf (1013 + 27) →
    (A.leaf % 2 = 1 → DigAt s (SEEDS + 16) carry) →
    TBSim image sk s (if A.lay = 1 then 16387 else 16688)
      (leafFn A.lay A.tree A.leaf A.digits carry)
      (fun r t => t.pc = pcOf A.ret ∧
        (A.so = false → DigAt t A.dest r.1.1) ∧ DigsAt t A.valp r.1.2 ∧
        r.1.2.length = A.n ∧ DigAt t (SEEDS + 16) r.2 ∧
        RegsExcept s t leafRegs ∧ Frame s t (LeafW A))
def btLeaf (lay : Layer) (tree sel : Nat) (ds : List Nat) (sb l : Nat) : LeafArgs :=
  ⟨lay, tree, l, if l = sel then ds else [], false, if l = sel then DIGITS else ZDIG,
    if l = sel then sb else DUMMY, LOW + 16 * (2 ^ height lay + l), 1191⟩
theorem btLeaf_costs (lay : Layer) (hlay : lay ≠ 0) (tree sel : Nat) (ds : List Nat) (sb l : Nat) :
    (btLeaf lay tree sel ds sb l).leafK = (if lay = 1 then 13800 else 14101) ∧
    (btLeaf lay tree sel ds sb l).leafC = (if lay = 1 then 16148 else 16449) ∧
    (btLeaf lay tree sel ds sb l).leafN = 324 ∧ (btLeaf lay tree sel ds sb l).leafB = 334 := by
  have e : (btLeaf lay tree sel ds sb l).leafK = (btLeaf lay 0 0 [] 0 1).leafK ∧
      (btLeaf lay tree sel ds sb l).leafC = (btLeaf lay 0 0 [] 0 1).leafC ∧
      (btLeaf lay tree sel ds sb l).leafN = (btLeaf lay 0 0 [] 0 1).leafN ∧
      (btLeaf lay tree sel ds sb l).leafB = (btLeaf lay 0 0 [] 0 1).leafB := ⟨rfl, rfl, rfl, rfl⟩
  rw [e.1, e.2.1, e.2.2.1, e.2.2.2]
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
theorem chainCount_low {lay : Layer} (h : lay ≠ 0) : chainCount lay = 43 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals rfl
theorem n4_low {lay : Layer} (h : lay ≠ 0) : n4 lay = 0 := by simp [n4, h]
theorem height_low {lay : Layer} (h : lay ≠ 0) : height lay = 6 ∨ height lay = 7 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals simp [height]
structure BtPre (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (tree sel : Nat) (ds : List Nat)
    (sb : Nat) (s : MachineState) : Prop where
  x2 : s.getReg .x2 = BitVec.ofNat 64 LOW
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 tree
  x14 : s.getReg .x14 = BitVec.ofNat 64 sel
  x15 : s.getReg .x15 = BitVec.ofNat 64 (height lay)
  x16 : s.getReg .x16 = BitVec.ofNat 64 sb
  x26 : s.getReg .x26 = BitVec.ofNat 64 43
  x27 : s.getReg .x27 = BitVec.ofNat 64 0
  x31 : s.getReg .x31 = BitVec.ofNat 64 0
  base : Base sk cache s
  hlay : lay ≠ 0
  htree : tree < 2 ^ 32
  hroute : ∀ l < 2 ^ height lay, tree * 2 ^ height lay + l < 2 ^ 31
  hsel : sel < 2 ^ height lay
  hdb : ∀ i < 43, ds.getD i 0 ≤ 7
  digits : ∀ i < 43, s.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (ds.getD i 0)
  hsb : SIG ≤ sb ∧ sb + 16 * (43 + height lay) ≤ SIG + 5616
  hsb8 : sb % 8 = 0
def BtW (sb H : Nat) (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨ X = CHAIN + 24 ∨
    (CHAIN + 48 ≤ X ∧ X < CHAIN + 80) ∨ (LEAFPK ≤ X ∧ X < LEAFPK + 16 * 44) ∨ (LOUT ≤ X ∧ X < LOUT + 32) ∨
    (DUMMY ≤ X ∧ X < DUMMY + 16 * 43) ∨ (sb ≤ X ∧ X < sb + 16 * 43) ∨
    (LOW + 16 * 2 ^ H ≤ X ∧ X < LOW + 16 * 2 ^ (H + 1))
def btRegs : List Reg := leafRegs ++ [.x6, .x13, .x18, .x22, .x23, .x25]
structure BtInv (s1 : MachineState) (sb sel H l : Nat) (st : List Digest × List Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf 1175
  x13 : t.getReg .x13 = BitVec.ofNat 64 l
  regs : RegsExcept s1 t btRegs
  frame : Frame s1 t (BtW sb H)
  len : st.1.length = l
  roots : DigsAt t (LOW + 16 * 2 ^ H) st.1
  vals : sel < l → st.2.length = 43 ∧ DigsAt t sb st.2
theorem extractByte_zero' (k : Nat) : extractByte (0 : Word) k = 0 := by
  simp [extractByte]
structure BtInvP (s1 : MachineState) (sb sel H l : Nat)
    (st : List Digest × List Digest × Digest) (t : MachineState) : Prop where
  old : BtInv s1 sb sel H l (st.1, st.2.1) t
  carry : l % 2 = 1 → DigAt t (SEEDS + 16) st.2.2
def btBodyP (leafFn : LeafFn) (lay : Layer) (tree sel : Nat) (ds : List Nat)
    (state : List Digest × List Digest × Digest) (leaf : Nat) : T3.M (List Digest × List Digest × Digest) := do
  let ((root, values), carry) ← leafFn lay tree leaf (if leaf = sel then ds else []) state.2.2
  pure (state.1 ++ [root], (if leaf = sel then values else state.2.1), carry)
def buildTreeP (leafFn : LeafFn) (lay : Layer) (tree sel : Nat) (ds : List Nat) :
    T3.M (List (List Digest) × List Digest) := do
  let state ← (List.range (2 ^ height lay)).foldlM (btBodyP leafFn lay tree sel ds) ([], [], 0)
  let levels ← buildLevels 3 lay.val tree (height lay) state.1
  pure (levels, state.2.1)
section loop
variable {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat} {sb : Nat}
  {s1 : MachineState} (hs : BtPre sk cache lay tree sel ds sb s1)
include hs
theorem bt_leafPre {l : Nat} (hl : l < 2 ^ height lay) {t : MachineState}
    (hr : RegsExcept s1 t (btRegs ++ [.x1, .x4, .x6, .x7, .x18, .x22, .x23, .x25])) (hf : Frame s1 t (BtW sb (height lay)))
    (h1 : t.getReg .x1 = pcOf 1191) (h18 : t.getReg .x18 = BitVec.ofNat 64 l)
    (h22 : t.getReg .x22 = BitVec.ofNat 64 (if l = sel then DIGITS else ZDIG))
    (h23 : t.getReg .x23 = BitVec.ofNat 64 (if l = sel then sb else DUMMY))
    (h25 : t.getReg .x25 = BitVec.ofNat 64 (LOW + 16 * (2 ^ height lay + l))) :
    LeafPreS sk t (btLeaf lay tree sel ds sb l) := by
  have hlay := hs.hlay
  have hn : (btLeaf lay tree sel ds sb l).n = 43 := chainCount_low hlay
  have hH := height_low hlay
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsb := hs.hsb
  have g : ∀ r, r ∉ btRegs ++ [.x1, .x4, .x6, .x7, .x18, .x22, .x23, .x25] → t.getReg r = s1.getReg r :=
    fun r hr' => hr.get hr'
  have m : ∀ X, X < 2 ^ 64 → ¬ BtW sb (height lay) X → t.getMem (BitVec.ofNat 64 X) = s1.getMem (BitVec.ofNat 64 X) :=
    fun X hX hn' => hf.get hX hn'
  have hz : ∀ X, X < 2 ^ 64 → NeverW X → t.getMem (BitVec.ofNat 64 X) = 0 := fun X hX hnw =>
    (m X hX (by unfold NeverW at hnw; unfold BtW; rcases hH with h | h <;> rw [h] <;> packed_sgo)).trans
      (hs.base.zero X hX hnw)
  refine
    { x1 := h1
      x5 := by rw [g _ (by decide), hs.base.x5]
      x8 := by rw [g _ (by decide), hs.x8]; rfl
      x9 := by rw [g _ (by decide), hs.x9]; rfl
      x18 := h18
      x22 := h22
      x23 := h23
      x25 := h25
      x26 := by rw [g _ (by decide), hs.x26, hn]
      x27 := by rw [g _ (by decide), hs.x27]; show _ = BitVec.ofNat 64 (n4 lay); rw [n4_low hlay]
      x31 := by rw [g _ (by decide), hs.x31]; rfl
      htree := hs.htree
      hleaf := by show l < 2 ^ 32; omega
      hroute := hs.hroute l hl
      hleafHeight := hl
      hsteps := fun i _ => by change T3.maxDigit lay i ≤ 8; simp [T3.maxDigit, hlay]
      p0 := by rw [m _ (by decide) (by unfold BtW; packed_sgo), hs.base.p0]
      p8 := by rw [m _ (by decide) (by unfold BtW; packed_sgo), hs.base.p8]
      p32 := by rw [m _ (by decide) (by unfold BtW; packed_sgo), hs.base.p32]
      p40 := by rw [m _ (by decide) (by unfold BtW; packed_sgo), hs.base.p40]
      p48 := by rw [m _ (by decide) (by unfold BtW; packed_sgo), hs.base.p48]
      p56 := by rw [m _ (by decide) (by unfold BtW; packed_sgo), hs.base.p56]
      z0 := hz _ (by decide) (by unfold NeverW; simp)
      z8 := hz _ (by decide) (by unfold NeverW; simp)
      z32 := hz _ (by decide) (by unfold NeverW; simp)
      z40 := hz _ (by decide) (by unfold NeverW; simp)
      ztail := fun h => by rw [hn] at h; exact absurd h (by norm_num)
      hdig := fun i hi => by
        rw [hn] at hi
        show t.getByte (BitVec.ofNat 64 ((if l = sel then DIGITS else ZDIG) + i)) =
          BitVec.ofNat 8 ((if l = sel then ds else []).getD i 0)
        by_cases hls : l = sel
        · simp only [hls, if_true]
          rw [hf.getByte (by packed_sgo) (by unfold BtW; rcases hH with h | h <;> rw [h] <;> packed_sgo)]
          exact hs.digits i hi
        · simp only [hls, if_false, List.getD_nil]
          rw [hf.getByte (by packed_sgo) (by unfold BtW; rcases hH with h | h <;> rw [h] <;> packed_sgo),
            getByte_eq_word s1 _ (by packed_sgo), hs.base.zero _ (by packed_sgo) (by unfold NeverW; packed_sgo), extractByte_zero']
          rfl
      hdigb := fun i hi => by
        rw [hn] at hi
        show (if l = sel then ds else []).getD i 0 < 256 ∧
          (false = false → (if l = sel then ds else []).getD i 0 ≤ T3.maxDigit lay i)
        have hw : T3.maxDigit lay i = 7 := by simp [T3.maxDigit, hlay]
        rw [hw]
        by_cases hls : l = sel
        · simp only [hls, if_true]; have := hs.hdb i hi; omega
        · simp [hls]
      hdigp := by show (if l = sel then DIGITS else ZDIG) + (btLeaf lay tree sel ds sb l).n ≤ 2 ^ 24
                  rw [hn]; split_ifs <;> packed_sgo
      hdigW := fun i hi => by
        rw [hn] at hi
        show ¬ LeafW (btLeaf lay tree sel ds sb l) (((if l = sel then DIGITS else ZDIG) + i) / 8 * 8)
        unfold LeafW
        show ¬ (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ (LEAFPK ≤ _ ∧ _ < LEAFPK + 16 * ((btLeaf lay tree sel ds sb l).n + 1)) ∨ _ ∨
          ((if l = sel then sb else DUMMY) ≤ _ ∧ _ < (if l = sel then sb else DUMMY) + 16 * (btLeaf lay tree sel ds sb l).n) ∨
          (LOW + 16 * (2 ^ height lay + l) ≤ _ ∧ _ < LOW + 16 * (2 ^ height lay + l) + 16))
        rw [hn]
        split_ifs <;> packed_sgo
      hv8 := by show (if l = sel then sb else DUMMY) % 8 = 0; split_ifs; exact hs.hsb8; decide
      hv := by
        show (if l = sel then sb else DUMMY) + 16 * (btLeaf lay tree sel ds sb l).n ≤ 2 ^ 24
        rw [hn]; split_ifs <;> packed_sgo
      hvs := by
        show (if l = sel then sb else DUMMY) + 16 * (btLeaf lay tree sel ds sb l).n ≤ PRIV ∨
          LEAFPK + 960 ≤ (if l = sel then sb else DUMMY)
        rw [hn]; split_ifs
        · left; packed_sgo
        · right; decide
      hd8 := fun _ => by show (LOW + 16 * (2 ^ height lay + l)) % 8 = 0; packed_sgo
      hd := by show LOW + 16 * (2 ^ height lay + l) + 16 ≤ 2 ^ 24; packed_sgo
      hds := Or.inr (Or.inl (by show LEAFPK + 960 ≤ LOW + 16 * (2 ^ height lay + l); packed_sgo))
      hdv := by
        show LOW + 16 * (2 ^ height lay + l) + 16 ≤ (if l = sel then sb else DUMMY) ∨
          (if l = sel then sb else DUMMY) + 16 * (btLeaf lay tree sel ds sb l).n ≤ LOW + 16 * (2 ^ height lay + l)
        rw [hn]; right; split_ifs <;> packed_sgo }
theorem bt_bodyP (leafFn : LeafFn) (hleafSpec : PackedLeafSpec leafFn)
    {l : Nat} (hl : l < 2 ^ height lay) {st : List Digest × List Digest × Digest} {t : MachineState}
    (htp : BtInvP s1 sb sel (height lay) l st t) :
    TBSim image sk t (if lay = 1 then 16405 else 16706)
      (btBodyP leafFn lay tree sel ds st l) (BtInvP s1 sb sel (height lay) (l + 1)) := by
  have ht := htp.old
  have hlay := hs.hlay
  have hH := height_low hlay
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsb := hs.hsb
  have g : ∀ r, r ∉ btRegs → t.getReg r = s1.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1x6, t1r, t1f⟩ := blk1175_spec t ht.pc l (height lay) (by omega)
    (by rcases hH with h | h <;> omega) ht.x13 (by rw [g _ (by decide), hs.x15])
  rw [if_pos hl] at t1pc
  obtain ⟨t2, st2, t2pc, t2x18, t2x22, t2x23, t2r, t2f⟩ := blk1178_spec t1 t1pc l sel (by omega)
    (by have := hs.hsel; omega) (by rw [t1r.get (by simp)]; exact ht.x13)
    (by rw [t1r.get (by simp), g _ (by decide), hs.x14])
  obtain ⟨t3, k3, st3, hk3, t3pc, t3x22, t3x23, t3r, t3f⟩ : ∃ t3 k3, Steps image t2 k3 k3 t3 ∧
      k3 = (if l = sel then 3 else 0) ∧ t3.pc = pcOf 1187 ∧
      t3.getReg .x22 = BitVec.ofNat 64 (if l = sel then DIGITS else ZDIG) ∧
      t3.getReg .x23 = BitVec.ofNat 64 (if l = sel then sb else DUMMY) ∧
      RegsExcept t2 t3 [.x22, .x23] ∧ Frame t2 t3 (fun _ => False) := by
    by_cases hls : l = sel
    · rw [if_pos hls] at t2pc
      obtain ⟨u, stu, upc, u22, u23, ur, uf⟩ := blk1184_spec t2 t2pc
      refine ⟨u, 3, stu, by simp [hls], upc, by simp [hls, u22], ?_, ur, uf⟩
      rw [u23, t2r.get (by simp), t1r.get (by simp), g _ (by decide), hs.x16]; simp [hls]
    · rw [if_neg hls] at t2pc
      exact ⟨t2, 0, Steps.refl _, by simp [hls], t2pc, by simp [hls, t2x22], by simp [hls, t2x23],
        RegsExcept.refl _ _, Frame.refl _ _⟩
  obtain ⟨t4, st4, t4pc, t4x1, t4x25, t4r, t4f⟩ := blk1187_spec t3 t3pc l (height lay) LOW hl
    (by rcases hH with h | h <;> omega) (by packed_sgo)
    (by rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp)]; exact ht.x13)
    (by rw [t3r.get (by simp), t2r.get (by simp)]; exact t1x6)
    (by rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp), g _ (by decide), hs.x2])
  have r14 : RegsExcept t t4 ([.x6] ++ [.x18, .x22, .x23] ++ [.x22, .x23] ++ [.x1, .x7, .x25]) :=
    ((t1r.trans t2r).trans t3r).trans t4r
  have f14 : Frame t t4 (fun _ => False) :=
    (((t1f.trans t2f).trans t3f).trans t4f).mono (fun _ _ h => by simp_all)
  have hpre : LeafPreS sk t4 (btLeaf lay tree sel ds sb l) :=
    bt_leafPre hs hl ((ht.regs.trans r14).mono (by decide)) ((ht.frame.trans f14).mono
      (fun X _ h => by rcases h with h | h; exact h; exact h.elim)) t4x1
      (by rw [t4r.get (by simp), t3r.get (by simp)]; exact t2x18)
      (by rw [t4r.get (by simp)]; exact t3x22) (by rw [t4r.get (by simp)]; exact t3x23) t4x25
  have hcarry : l % 2 = 1 → DigAt t4 (SEEDS + 16) st.2.2 := by
    intro hp
    exact (htp.carry hp).frame f14 (by decide) (by simp) (by simp)
  have hleaf := hleafSpec sk (btLeaf lay tree sel ds sb l) t4 st.2.2 hlay rfl hpre t4pc hcarry
  unfold btBodyP
  refine TBSim.mono (TBSim.steps (st1.trans (st2.trans (st3.trans st4)))
    (TBSim.bind (W₂ := 2) hleaf (fun r u hu => ?_))) ?_ (fun _ _ h => h)
  rotate_left
  · simp only [btLeaf] at *
    rw [hk3]
    by_cases h : lay = 1 <;> simp only [h, ite_true, ite_false]
    all_goals split_ifs <;> omega
  obtain ⟨upc, uroot, uvals, ulen, ucarry, ur, uf⟩ := hu
  obtain ⟨⟨root, values⟩, carry⟩ := r
  obtain ⟨t5, st5, t5pc, t5x13, t5r, t5f⟩ := blk1191_spec u upc l
    (by rw [ur.get (by decide), r14.get (by simp)]; exact ht.x13)
  have hLW : ∀ X, LeafW (btLeaf lay tree sel ds sb l) X → BtW sb (height lay) X := by
    intro X h
    unfold LeafW at h
    rw [show (btLeaf lay tree sel ds sb l).n = 43 from chainCount_low hlay] at h
    change X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨ X = CHAIN + 24 ∨
      (CHAIN + 48 ≤ X ∧ X < CHAIN + 80) ∨ (LEAFPK ≤ X ∧ X < LEAFPK + 16 * (43 + 1)) ∨ (LOUT ≤ X ∧ X < LOUT + 32) ∨
      ((if l = sel then sb else DUMMY) ≤ X ∧ X < (if l = sel then sb else DUMMY) + 16 * 43) ∨
      (LOW + 16 * (2 ^ height lay + l) ≤ X ∧ X < LOW + 16 * (2 ^ height lay + l) + 16) at h
    unfold BtW
    rw [show 2 ^ (height lay + 1) = 2 * 2 ^ height lay by rw [pow_succ]; ring]
    split_ifs at h <;> packed_sgo
  have fU : Frame t t5 (BtW sb (height lay)) := ((f14.trans uf).trans t5f).mono (fun X _ h => by
    rcases h with (h | h) | h
    · exact h.elim
    · exact hLW X h
    · exact h.elim)
  have hc : DigAt t5 (SEEDS + 16) carry :=
    ucarry.frame t5f (by decide) (by simp) (by simp)
  refine TBSim.pure_steps st5 ⟨⟨t5pc, t5x13, ?_, ?_, by simp [ht.len], ?_, ?_⟩, fun _ => hc⟩
  · exact (((ht.regs.trans r14).trans ur).trans t5r).mono (by decide)
  · exact (ht.frame.trans fU).mono (fun X _ h => by rcases h with h | h <;> exact h)
  ·
    have hd : DigAt u (LOW + 16 * 2 ^ height lay + 16 * st.1.length) root := by
      rw [ht.len, show LOW + 16 * 2 ^ height lay + 16 * l = LOW + 16 * (2 ^ height lay + l) by ring]
      exact uroot rfl
    have hold : DigsAt u (LOW + 16 * 2 ^ height lay) st.1 := by
      refine ht.roots.frame ((f14.trans uf).mono (fun X _ h => h)) (by rw [ht.len]; packed_sgo) ?_
      intro B h1 h2 h
      rw [ht.len] at h2
      rcases h with h | h
      · exact h
      · unfold LeafW at h
        rw [show (btLeaf lay tree sel ds sb l).n = 43 from chainCount_low hlay] at h
        change B = PRIV + 16 ∨ B = PRIV + 24 ∨ (SEEDS ≤ B ∧ B < SEEDS + 32) ∨ B = CHAIN + 16 ∨ B = CHAIN + 24 ∨
          (CHAIN + 48 ≤ B ∧ B < CHAIN + 80) ∨ (LEAFPK ≤ B ∧ B < LEAFPK + 16 * (43 + 1)) ∨ (LOUT ≤ B ∧ B < LOUT + 32) ∨
          ((if l = sel then sb else DUMMY) ≤ B ∧ B < (if l = sel then sb else DUMMY) + 16 * 43) ∨
          (LOW + 16 * (2 ^ height lay + l) ≤ B ∧ B < LOW + 16 * (2 ^ height lay + l) + 16) at h
        split_ifs at h <;> packed_sgo
    exact (hold.snoc hd).frame t5f (by simp only [List.length_append, List.length_singleton, ht.len]; packed_sgo)
      (fun _ _ _ h => h)
  ·
    intro hsl
    by_cases hls : l = sel
    · subst hls
      simp only [if_true]
      refine ⟨by rw [ulen]; exact chainCount_low hlay, ?_⟩
      have := uvals
      simp only [btLeaf, if_true] at this
      exact this.frame t5f (by rw [ulen, show (btLeaf lay tree l ds sb l).n = 43 from chainCount_low hlay]; packed_sgo)
        (fun _ _ _ h => h)
    · simp only [hls, if_false]
      obtain ⟨hl2, hv⟩ := ht.vals (by omega)
      refine ⟨hl2, hv.frame ((f14.trans uf).trans t5f) (by rw [hl2]; packed_sgo) (fun B h1 h2 h => ?_)⟩
      rw [hl2] at h2
      rcases h with (h | h) | h
      · exact h
      · unfold LeafW at h
        rw [show (btLeaf lay tree sel ds sb l).n = 43 from chainCount_low hlay] at h
        change B = PRIV + 16 ∨ B = PRIV + 24 ∨ (SEEDS ≤ B ∧ B < SEEDS + 32) ∨ B = CHAIN + 16 ∨ B = CHAIN + 24 ∨
          (CHAIN + 48 ≤ B ∧ B < CHAIN + 80) ∨ (LEAFPK ≤ B ∧ B < LEAFPK + 16 * (43 + 1)) ∨ (LOUT ≤ B ∧ B < LOUT + 32) ∨
          ((if l = sel then sb else DUMMY) ≤ B ∧ B < (if l = sel then sb else DUMMY) + 16 * 43) ∨
          (LOW + 16 * (2 ^ height lay + l) ≤ B ∧ B < LOW + 16 * (2 ^ height lay + l) + 16) at h
        rw [if_neg hls] at h
        packed_sgo
      · exact h
end loop
theorem bt_path_loop (t0 : MachineState) (H hi : Nat) (hH : H ≤ 7) (hhi : hi < 2 ^ (H + 1)) :
    ∀ (n j : Nat), j + n = H → ∀ (t : MachineState) (ep : Nat), t.pc = pcOf 1202 →
      t.getReg .x13 = BitVec.ofNat 64 j → t.getReg .x15 = BitVec.ofNat 64 H →
      t.getReg .x19 = BitVec.ofNat 64 hi → t.getReg .x2 = BitVec.ofNat 64 LOW →
      t.getReg .x24 = BitVec.ofNat 64 ep → ep % 8 = 0 → ep + 16 * n ≤ LOW →
      (∀ A, LOW ≤ A → A < LOW + 4096 → t.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A)) →
      ∃ u k, Steps image t k k u ∧ k ≤ 12 * n + 1 ∧ u.pc = pcOf 1214 ∧
        (∀ i < n, DigAt u (ep + 16 * i) (memDig t0 (LOW + 16 * (hi / 2 ^ (j + i) ^^^ 1)))) ∧
        RegsExcept t u [.x6, .x7, .x13, .x24, .x28] ∧ Frame t u (fun A => ep ≤ A ∧ A < ep + 16 * n)
  | 0, j, hjn, t, ep, hpc, h13, h15, _, _, _, _, _, _ => by
    obtain ⟨u, st, upc, ur, uf⟩ := blk1202_spec t hpc j H (by omega) (by omega) h13 h15
    rw [if_neg (by omega)] at upc
    exact ⟨u, 1, st, by omega, upc, fun i hi => absurd hi (by omega), ur.mono (by simp),
      uf.mono (fun _ _ h => h.elim)⟩
  | n + 1, j, hjn, t, ep, hpc, h13, h15, h19, h2, h24, hep8, hepl, hheap => by
    obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk1202_spec t hpc j H (by omega) (by omega) h13 h15
    rw [if_pos (by omega)] at t1pc
    have hhi' : hi < 8192 := lt_of_lt_of_le hhi (by
      calc 2 ^ (H + 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 8192 := by norm_num)
    obtain ⟨t2, st2, t2pc, t2x13, t2x24, m0, m8, t2r, t2f⟩ := blk1203_spec t1 t1pc j hi LOW ep (by omega)
      hhi' (by packed_sgo) (by packed_sgo) (by packed_sgo) hep8 (by rw [t1r.get (by simp)]; exact h13)
      (by rw [t1r.get (by simp)]; exact h19) (by rw [t1r.get (by simp)]; exact h2)
      (by rw [t1r.get (by simp)]; exact h24)
    have hx : hi / 2 ^ j ^^^ 1 < 8192 :=
      Nat.xor_lt_two_pow (n := 13) (lt_of_le_of_lt (Nat.div_le_self _ _) hhi') (by norm_num)
    have hx' : hi / 2 ^ j ^^^ 1 < 256 := by
      have h1 : hi / 2 ^ j < 2 ^ 8 := lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le hhi
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
      exact Nat.xor_lt_two_pow h1 (by norm_num)
    have f12 : Frame t t2 (fun A => A = ep ∨ A = ep + 8) := (t1f.trans t2f).mono (fun _ _ h => by
      rcases h with h | h; exact h.elim; exact h)
    obtain ⟨u, k, st, hk, upc, uem, ur, uf⟩ := bt_path_loop t0 H hi hH hhi n (j + 1) (by omega) t2 (ep + 16) t2pc
      t2x13 (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h15)
      (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h19) (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h2)
      t2x24 (by omega) (by omega) (fun A h1 h2' => (f12.get (by packed_sgo) (by packed_sgo)).trans (hheap A h1 h2'))
    refine ⟨u, 1 + (11 + k), st1.trans (st2.trans st), by omega, upc, fun i hi' => ?_,
      ((t1r.trans t2r).trans ur).mono (by simp), (f12.trans uf).mono (fun A _ h => by rcases h with h | h <;> omega)⟩
    rcases i with _ | i
    · simp only [Nat.mul_zero, Nat.add_zero]
      refine ⟨?_, ?_⟩
      · rw [uf.get (by packed_sgo) (by omega), m0, t1f.get (by packed_sgo) (fun h => h), hheap _ (by packed_sgo) (by packed_sgo)]
        exact (memDig_digAt t0 (LOW + 16 * (hi / 2 ^ j ^^^ 1))).1
      · rw [uf.get (by packed_sgo) (by omega), m8, t1f.get (by packed_sgo) (fun h => h), hheap _ (by packed_sgo) (by packed_sgo)]
        exact (memDig_digAt t0 (LOW + 16 * (hi / 2 ^ j ^^^ 1))).2
    · have := uem i (by omega)
      rw [show ep + 16 + 16 * i = ep + 16 * (i + 1) by ring, show j + 1 + i = j + (i + 1) by ring] at this
      exact this
def btLev (lay : Layer) (tree : Nat) : LevArgs := ⟨3, lay.val, tree, height lay, LOW, 1196⟩
def btAllRegs : List Reg :=
  [.x4, .x13] ++ btRegs ++ [.x6] ++ [.x1, .x21] ++ levRegs ++ [.x6, .x7, .x13, .x19, .x24] ++
    [.x6, .x7, .x13, .x24, .x28] ++ [.x6, .x7, .x30]
def BtAllW (lay : Layer) (tree sb : Nat) (A : Nat) : Prop :=
  BtW sb (height lay) A ∨ LevW (btLev lay tree) A ∨ (sb + 16 * 43 ≤ A ∧ A < sb + 16 * (43 + height lay)) ∨
    A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56
structure BtPost (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (tree sel sb ret : Nat) (s : MachineState)
    (r : List (List Digest) × List Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf ret
  vlen : r.2.length = 43
  vals : DigsAt u sb r.2
  path : DigsAt u (sb + 16 * 43) ((List.range (height lay)).map fun j => (r.1.getD j []).getD (sel / 2 ^ j ^^^ 1) 0)
  left : DigAt u ENC (topPair lay r.1).1
  right : DigAt u (ENC + 48) (topPair lay r.1).2
  base : Base sk cache u
  regs : RegsExcept s u btAllRegs
  frame : Frame s u (BtAllW lay tree sb)
def btCost : Nat := 2127776
theorem sumTo_le_mul (f : Nat → Nat) (b : Nat) : ∀ n, (∀ j < n, f j ≤ b) → sumTo f n ≤ n * b
  | 0, _ => by simp [sumTo]
  | n + 1, h => by
    have := sumTo_le_mul f b n (fun j hj => h j (by omega))
    have := h n (by omega)
    simp only [sumTo]; rw [Nat.succ_mul]; omega
theorem sumTo_le_sumTo (f g : Nat → Nat) : ∀ n, (∀ j < n, f j ≤ g j) → sumTo f n ≤ sumTo g n
  | 0, _ => le_rfl
  | n + 1, h => by
    have := sumTo_le_sumTo f g n (fun j hj => h j (by omega))
    have := h n (by omega)
    simp only [sumTo]; omega
theorem heapH_sib {H sel i : Nat} (hi : i < H) :
    (2 ^ H + sel) / 2 ^ i ^^^ 1 = 2 ^ (H - i) + (sel / 2 ^ i ^^^ 1) := by
  have h2 : 2 ^ H = 2 ^ (H - i) * 2 ^ i := by rw [← pow_add, Nat.sub_add_cancel hi.le]
  rw [h2, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i), Nat.add_comm,
    two_pow_add_xor_one (by omega)]
theorem btLev_costs (lay : Layer) (hlay : lay ≠ 0) (tree : Nat) :
    (btLev lay tree).levK ≤ (btLev lay tree).levC ∧ (btLev lay tree).levC ≤ 5889 := by
  rcases height_low hlay with h | h <;> simp only [LevArgs.levK, LevArgs.levC, btLev, h] <;> decide
theorem bt_tail {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat}
    {sb ret : Nat} {s s1 t : MachineState} (hs : BtPre sk cache lay tree sel ds sb s1)
    (h4 : s1.getReg .x4 = pcOf ret) (hr0 : RegsExcept s s1 [.x4, .x13]) (hf0 : Frame s s1 (fun _ => False))
    {st : List Digest × List Digest} (ht : BtInv s1 sb sel (height lay) (2 ^ height lay) st t) :
    TBSim image sk t 19000 (do
      let levels ← buildLevels 3 lay.val tree (height lay) st.1
      pure (levels, st.2)) (BtPost sk cache lay tree sel sb ret s) := by
  have hlay := hs.hlay
  have hH := height_low hlay
  have hH7 : height lay ≤ 7 := by rcases hH with h | h <;> omega
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsel := hs.hsel
  have hsb := hs.hsb
  have hsb8 := hs.hsb8
  have g : ∀ r, r ∉ btRegs → t.getReg r = s1.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, -, t1r, t1f⟩ := blk1175_spec t ht.pc (2 ^ height lay) (height lay) (by omega)
    (by omega) ht.x13 (by rw [g _ (by decide), hs.x15])
  rw [if_neg (lt_irrefl _)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x1, t2x21, t2r, t2f⟩ := blk1193_spec t1 t1pc lay.val (by have := lay.isLt; omega)
    (by rw [t1r.get (by simp), g _ (by decide), hs.x8])
  have g2 : ∀ r, r ∉ btRegs ++ [.x6] ++ [.x1, .x21] → t2.getReg r = s1.getReg r := fun r hr =>
    ((ht.regs.trans t1r).trans t2r).get hr
  have f2 : Frame s1 t2 (BtW sb (height lay)) := (ht.frame.trans (t1f.trans t2f)).mono (fun X _ h => by
    rcases h with h | h | h
    · exact h
    · exact h.elim
    · exact h.elim)
  have hlp : LevPre t2 (btLev lay tree) st.1 :=
    { x1 := t2x1
      x2 := by rw [g2 _ (by decide), hs.x2]; rfl
      x5 := by rw [g2 _ (by decide), hs.base.x5]
      x9 := by rw [g2 _ (by decide), hs.x9]; rfl
      x15 := by rw [g2 _ (by decide), hs.x15]; rfl
      x21 := by
        rw [t2x21]
        show BitVec.ofNat 64 (769 + 65536 * lay.val) = BitVec.ofNat 64 (hdr0 3 lay.val tree 0)
        congr 1
        unfold hdr0
        rw [Nat.div_eq_of_lt hs.htree]
        have := lay.isLt
        omega
      tag3 := Or.inl rfl
      htree := hs.htree
      hh1 := by show 1 ≤ height lay; omega
      hh := by show height lay ≤ 12; omega
      ha8 := by show LOW % 8 = 0; decide
      ha := by
        show LOW + 16 * 2 ^ (height lay + 1) ≤ 2 ^ 24
        rcases hH with h | h <;> rw [h] <;> norm_num
      has := Or.inl (by show NOUT + 32 ≤ LOW; decide)
      z32 := by
        rw [f2.get (by packed_sgo) (by unfold BtW; packed_sgo)]
        exact hs.base.zero _ (by packed_sgo) (by unfold NeverW; simp)
      z40 := by
        rw [f2.get (by packed_sgo) (by unfold BtW; packed_sgo)]
        exact hs.base.zero _ (by packed_sgo) (by unfold NeverW; simp)
      hlen := ht.len
      hleaves := by
        show DigsAt t2 (LOW + 16 * 2 ^ height lay) st.1
        exact ht.roots.frame (t1f.trans t2f) (by rw [ht.len]; packed_sgo) (fun _ _ _ h => by
          rcases h with h | h <;> exact h) }
  have hlev := Seed.buildLevels_tsim SeedIndependent.seedIndependentAt_sign sk hlp t2pc
  obtain ⟨hlk, hlc⟩ := btLev_costs lay hlay tree
  refine TBSim.mono (TBSim.steps (st1.trans st2) (TBSim.bind (W₂ := 120) (TSim.toTBSim hlev hlk)
    (fun levels u hu => ?_))) (by omega) (fun _ _ h => h)
  obtain ⟨upc, uheap, ur, uf⟩ := hu
  have gu : ∀ r, r ∉ btRegs ++ [.x6] ++ [.x1, .x21] ++ levRegs → u.getReg r = s1.getReg r := fun r hr =>
    (((ht.regs.trans t1r).trans t2r).trans ur).get hr
  obtain ⟨v, stv, vpc, vx13, vx19, vx24, vr, vf⟩ := blk1196_spec u upc (height lay) sel sb 43 (by omega)
    (by omega) (by packed_sgo) (by rw [gu _ (by decide), hs.x15]) (by rw [gu _ (by decide), hs.x14])
    (by rw [gu _ (by decide), hs.x16]) (by rw [gu _ (by decide), hs.x26])
  have gv : ∀ r, r ∉ btRegs ++ [.x6] ++ [.x1, .x21] ++ levRegs ++ [.x6, .x7, .x13, .x19, .x24] →
      v.getReg r = s1.getReg r := fun r hr => ((((ht.regs.trans t1r).trans t2r).trans ur).trans vr).get hr
  obtain ⟨w, k, stw, hk, wpc, wem, wr, wf⟩ := bt_path_loop u (height lay) (2 ^ height lay + sel) hH7
    (by rw [pow_succ]; omega) (height lay) 0 (by omega) v (sb + 16 * 43) vpc vx13
    (by rw [gv _ (by decide), hs.x15]) vx19 (by rw [gv _ (by decide), hs.x2]) vx24 (by omega) (by packed_sgo)
    (fun A h1 h2 => vf.get (by packed_sgo) (fun h => h))
  obtain ⟨x, stx, xpc, xm0, xm8, xm48, xm56, xr, xf⟩ := BCBlocks.blk1214_pair_spec w wpc LOW ret (by decide) (by decide) (by decide)
    (by rw [wr.get (by simp), gv _ (by decide), hs.x2])
    (by rw [wr.get (by simp), gv _ (by decide), h4])
  refine TBSim.mono (TBSim.pure_steps (stv.trans (stw.trans stx)) ?_) (by omega) (fun _ _ h => h)
  have fux : Frame u x (fun A => (sb + 16 * 43 ≤ A ∧ A < sb + 16 * 43 + 16 * height lay) ∨ A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) :=
    ((vf.trans wf).trans xf).mono (fun A _ h => by
      rcases h with (h | h) | h
      · exact h.elim
      · exact Or.inl h
      · exact Or.inr h)
  have f1x : Frame s1 x (BtAllW lay tree sb) := (f2.trans (uf.trans fux)).mono (fun A _ h => by
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr h)))
  have hW : ∀ A, A < 2 ^ 64 → BaseA A → ¬ BtAllW lay tree sb A := by
    intro A _ hb hw
    unfold BaseA NeverW Search.TOP_DATA at hb
    unfold BtAllW BtW LevW at hw
    simp only [btLev] at hw
    rcases hH with h | h <;> rw [h] at hw <;> packed_sgo
  have r1x : RegsExcept s1 x (btRegs ++ [.x6] ++ [.x1, .x21] ++ levRegs ++ [.x6, .x7, .x13, .x19, .x24] ++
      [.x6, .x7, .x13, .x24, .x28] ++ [.x6, .x7, .x30]) :=
    (((((ht.regs.trans t1r).trans t2r).trans ur).trans vr).trans wr).trans xr
  obtain ⟨-, hlv⟩ := uheap
  refine ⟨xpc, (ht.vals hsel).1, ?_, ?_, ?_, ?_, hs.base.frame f1x r1x (by decide) hW, ?_, ?_⟩
  ·
    obtain ⟨hl2, hv⟩ := ht.vals hsel
    have ftx : Frame t x (fun A => LevW (btLev lay tree) A ∨
        (sb + 16 * 43 ≤ A ∧ A < sb + 16 * 43 + 16 * height lay) ∨ A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) :=
      ((t1f.trans t2f).trans (uf.trans fux)).mono (fun A _ h => by
        rcases h with (h | h) | h
        · exact h.elim
        · exact h.elim
        · exact h)
    refine hv.frame ftx (by rw [hl2]; packed_sgo) (fun B h1 h2 h => ?_)
    rw [hl2] at h2
    unfold LevW at h
    simp only [btLev] at h
    packed_sgo
  ·
    intro i hi
    rw [List.length_map, List.length_range] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    have he := wem i hi
    rw [Nat.zero_add, heapH_sib hi] at he
    obtain ⟨hlen, hd⟩ := hlv i (by show i ≤ height lay; omega)
    have hq : sel / 2 ^ i < 2 ^ (height lay - i) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos i), ← pow_add, Nat.sub_add_cancel hi.le]; exact hsel
    have h2i : 2 ^ 1 ≤ 2 ^ (height lay - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hkq : sel / 2 ^ i ^^^ 1 < 2 ^ (height lay - i) := Nat.xor_lt_two_pow hq (by omega)
    have hdi := hd _ (by rw [hlen]; exact hkq)
    simp only [btLev] at hdi
    rw [show LOW + 16 * (2 ^ (height lay - i) + (sel / 2 ^ i ^^^ 1)) =
      LOW + 16 * 2 ^ (height lay - i) + 16 * (sel / 2 ^ i ^^^ 1) by ring, memDig_eq hdi] at he
    exact he.frame xf (by packed_sgo) (by packed_sgo) (by packed_sgo)
  ·
    obtain ⟨hl0, hd⟩ := hlv (height lay - 1) (by change height lay - 1 ≤ height lay; omega)
    have he : height lay - (height lay - 1) = 1 := by rcases hH with h | h <;> omega
    have hd0 := hd 0 (by rw [hl0]; simp only [btLev, he]; norm_num)
    simp only [btLev, he, pow_one, Nat.mul_zero, Nat.add_zero] at hd0
    change DigAt x ENC ((levels.getD (height lay - 1) []).getD 0 0)
    refine ⟨?_, ?_⟩
    · rw [xm0, wf.get (by packed_sgo) (by packed_sgo), vf.get (by packed_sgo) (fun h => h)]; exact hd0.1
    · rw [xm8, wf.get (by packed_sgo) (by packed_sgo), vf.get (by packed_sgo) (fun h => h)]; exact hd0.2
  ·
    obtain ⟨hl0, hd⟩ := hlv (height lay - 1) (by change height lay - 1 ≤ height lay; omega)
    have he : height lay - (height lay - 1) = 1 := by rcases hH with h | h <;> omega
    have hd1 := hd 1 (by rw [hl0]; simp only [btLev, he]; norm_num)
    simp only [btLev, he, pow_one, Nat.mul_one] at hd1
    change DigAt x (ENC + 48) ((levels.getD (height lay - 1) []).getD 1 0)
    refine ⟨?_, ?_⟩
    · rw [xm48, wf.get (by packed_sgo) (by packed_sgo), vf.get (by packed_sgo) (fun h => h)]; exact hd1.1
    · rw [xm56, wf.get (by packed_sgo) (by packed_sgo), vf.get (by packed_sgo) (fun h => h)]; exact hd1.2
  · exact (hr0.trans r1x).mono (by decide)
  · exact (hf0.trans f1x).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
theorem buildTreeP_tbsim (leafFn : LeafFn) (hleafSpec : PackedLeafSpec leafFn) {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat}
    {sb ret : Nat} {s : MachineState} (hs : BtPre sk cache lay tree sel ds sb s) (hpc : s.pc = pcOf 1173)
    (h1 : s.getReg .x1 = pcOf ret) :
    TBSim image sk s btCost (buildTreeP leafFn lay tree sel ds) (BtPost sk cache lay tree sel sb ret s) := by
  have hlay := hs.hlay
  have hH := height_low hlay
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsel := hs.hsel
  have hsb := hs.hsb
  obtain ⟨s1, st1, s1pc, s1x4, s1x13, s1r, s1f⟩ := blk1173_spec s hpc
  have g1 : ∀ r, r ∉ [.x4, .x13] → s1.getReg r = s.getReg r := fun r hr => s1r.get hr
  have hs1 : BtPre sk cache lay tree sel ds sb s1 :=
    { x2 := by rw [g1 _ (by decide), hs.x2]
      x8 := by rw [g1 _ (by decide), hs.x8]
      x9 := by rw [g1 _ (by decide), hs.x9]
      x14 := by rw [g1 _ (by decide), hs.x14]
      x15 := by rw [g1 _ (by decide), hs.x15]
      x16 := by rw [g1 _ (by decide), hs.x16]
      x26 := by rw [g1 _ (by decide), hs.x26]
      x27 := by rw [g1 _ (by decide), hs.x27]
      x31 := by rw [g1 _ (by decide), hs.x31]
      base := hs.base.frame s1f s1r (by decide) (fun _ _ _ h => h)
      hlay := hlay
      htree := hs.htree
      hsel := hsel
      hroute := hs.hroute
      hdb := hs.hdb
      digits := fun i hi => by rw [s1f.getByte (by packed_sgo) (fun h => h)]; exact hs.digits i hi
      hsb := hsb
      hsb8 := hs.hsb8 }
  have h0 : BtInvP s1 sb sel (height lay) 0 ([], [], 0) s1 :=
    ⟨⟨s1pc, s1x13, RegsExcept.refl _ _, Frame.refl _ _, rfl, DigsAt.nil _ _,
      fun h => absurd h (by omega)⟩, fun h => absurd h (by decide)⟩
  have hloop := TBSim.foldlM_range' (image := image) (sk := sk) 0 (2 ^ height lay)
    (btBodyP leafFn lay tree sel ds) ([], [], 0) (BtInvP s1 sb sel (height lay))
    (if lay = 1 then 16405 else 16706)
    (fun l hl st t ht => by simpa using bt_bodyP hs1 leafFn hleafSpec hl ht) h0
  have hcost : 2 + (2 ^ height lay * (if lay = 1 then 16405 else 16706) + 19000) ≤ btCost := by
    fin_cases lay
    · exact absurd rfl hlay
    all_goals decide
  unfold buildTreeP
  have heq : List.range' 0 (2 ^ height lay) = List.range (2 ^ height lay) := List.range_eq_range'.symm
  rw [heq] at hloop
  exact TBSim.mono (TBSim.steps st1 (TBSim.bind (W₂ := 19000) hloop
    (fun st t ht => bt_tail hs1 (by rw [s1x4, h1]) s1r s1f ht.old))) hcost (fun _ _ h => h)
end SigGolfCandidate.T3M.Sign.Packed
end
end
