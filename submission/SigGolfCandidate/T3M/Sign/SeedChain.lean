import SigGolfCandidate.T3M.Sign.SeedIndependent
namespace SigGolfCandidate.T3M.Sign.Seed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open Keygen Keygen.PackedBlocks
open SeedIndependent (SeedIndependentAt)
open SigGolfCandidate.T3 (Layer Digest chainInput chain shortHash header pad64 zero16 height chainHeader)
open SphincsSecurity (bytesLE bytesLE_length)
set_option backward.isDefEq.respectTransparency false
/-! ### C3 (FULL): the chain tail trampoline at 1667 -/
def ctr0 : List (BitVec 32) := [34181731]
def ctr1 : List (BitVec 32) := [33816675]
def ctr2 : List (BitVec 32) := [6292243,6954083]
def ctr3 : List (BitVec 32) := [134711,504247043,512635779,476985379,478034979,1706515,3662671983]
def ctr4 : List (BitVec 32) := [1706515,3662671983]
sym_block blkC0 := symRun { noAlias := true } ctr0 (pcOf 1667) 100
sym_block blkC1 := symRun { noAlias := true } ctr1 (pcOf 1668) 100
sym_block blkC2 := symRun { noAlias := true } ctr2 (pcOf 1669) 100
sym_block blkC3 := symRun { noAlias := true } ctr3 (pcOf 1671) 100
sym_block blkC4 := symRun { noAlias := true } ctr4 (pcOf 1676) 100
theorem codeAt_ctr0 {image : Image} {b : Nat} (h : SeedIndependentAt image b) : CodeAt image (pcOf 1667) ctr0 := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_ctr1 {image : Image} {b : Nat} (h : SeedIndependentAt image b) : CodeAt image (pcOf 1668) ctr1 := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_ctr2 {image : Image} {b : Nat} (h : SeedIndependentAt image b) : CodeAt image (pcOf 1669) ctr2 := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_ctr3 {image : Image} {b : Nat} (h : SeedIndependentAt image b) : CodeAt image (pcOf 1671) ctr3 := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_ctr4 {image : Image} {b : Nat} (h : SeedIndependentAt image b) : CodeAt image (pcOf 1676) ctr4 := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem blkC3_regs (t : MachineState) : RegsExcept t (blkC3.res.toState t) [.x6, .x7, .x20, .x28] := by
  intro r hr; simp at hr; cases r <;> simp_all [blkC3.res, rv_simp] <;> rfl
/-- C3 (FULL): does the chain tail take the high half (chain 0 of a lower layer, after step 6)? -/
def hiSel (lay i m : Nat) : Prop := lay ≠ 0 ∧ i = 0 ∧ m = 6
instance (lay i m : Nat) : Decidable (hiSel lay i m) := by unfold hiSel; infer_instance
/-- C3 (FULL): extra steps of the chain tail trampoline over the old `addi s4; jal` (2 steps). -/
def trX (lay i m : Nat) : Nat := if i ≠ 0 then 2 else if lay = 0 then 3 else if m = 6 then 10 else 5
theorem tramp_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 24)) (lay i m : Nat) (hlay : lay < 2 ^ 64) (hi : i < 2 ^ 64) (hm : m < 2 ^ 63)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (lo hv : Digest) (hlo : DigAt s (CHAIN + 48) lo)
    (hhv : DigAt s (CHAIN + 64) hv) :
    ∃ t, Steps image s (2 + trX lay i m) (2 + trX lay i m) t ∧ t.pc = pcOf (b + 1) ∧
      t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧ DigAt t (CHAIN + 48) (if hiSel lay i m then hv else lo) ∧
      RegsExcept s t [.x6, .x7, .x20, .x28] ∧ Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  obtain rfl := SeedIndependent.b_eq h
  -- 1037: jal 1667
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1667 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_24 (SeedIndependent.codeAt_sub24S h) s hpc
      (by simp [SeedIndependent.blkS_24.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_24.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  -- the final `addi s4,s4,1; jal 1014` at 1676
  have last : ∀ u : MachineState, u.pc = pcOf 1676 → u.getReg .x20 = BitVec.ofNat 64 m →
      ∃ t, Steps image u 2 2 t ∧ t.pc = pcOf (1013 + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
        RegsExcept u t [.x20] ∧ Frame u t (fun _ => False) := by
    intro u hu hu20
    refine ⟨_, symRun_sound blkC4 (codeAt_ctr4 h) u hu (by simp [blkC4.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [blkC4.res, E.eval]
    · simp only [Result.toState_getReg, blkC4.res, rv_simp, hu20]
      rw [ofNat_add_ofNat]
    · intro r hr; simp at hr; cases r <;> simp_all [blkC4.res, rv_simp] <;> rfl
    · intro A _ _; simp [blkC4.res, rv_simp]
  have ne_of {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = decide (x ≠ y) := by
    by_cases hxy : x = y
    · subst hxy; simp
    · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
      simp [hxy, this]
  have eq_of {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
    by_cases hxy : x = y
    · subst hxy; simp
    · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
      simp [hxy, this]
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps image t0 1 1 t ∧ t.pc = (if i ≠ 0 then pcOf 1676 else pcOf 1668) ∧
      RegsExcept t0 t [] ∧ Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound blkC0 (codeAt_ctr0 h) t0 p0 (by simp [blkC0.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, blkC0.res, E.eval, CmpOp.eval, r0.get (by simp), h19]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ne_of hi (by norm_num)]
      by_cases hi0 : i = 0 <;> simp [hi0]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g1 : ∀ r, r ∉ ([] : List Reg) → t1.getReg r = s.getReg r := fun r hr => (r0.trans r1).get hr
  by_cases hi0 : i ≠ 0
  · rw [if_pos hi0] at p1
    obtain ⟨t2, s2, p2, x2, r2, f2⟩ := last t1 p1 (by rw [g1 _ (by simp)]; exact h20)
    have hs : ¬ hiSel lay i m := fun hh => hi0 hh.2.1
    refine ⟨t2, ((s0.trans s1).trans s2).of_eq (by simp [trX, hi0]) (by simp [trX, hi0]), p2, x2, ?_,
      ((r0.trans r1).trans r2).mono (by simp), ((f0.trans f1).trans f2).mono (fun A _ hA => by simp_all)⟩
    rw [if_neg hs]
    exact hlo.frame ((f0.trans f1).trans f2) (by decide) (by simp) (by simp)
  have hi0' : i = 0 := by omega
  rw [if_neg hi0] at p1
  obtain ⟨t2, s2, p2, r2, f2⟩ : ∃ t, Steps image t1 1 1 t ∧ t.pc = (if lay = 0 then pcOf 1676 else pcOf 1669) ∧
      RegsExcept t1 t [] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound blkC1 (codeAt_ctr1 h) t1 p1 (by simp [blkC1.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, blkC1.res, E.eval, CmpOp.eval, g1 _ (by simp), h8]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, eq_of hlay (by norm_num)]
      by_cases hl0 : lay = 0 <;> simp [hl0]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g2 : ∀ r, r ∉ ([] : List Reg) → t2.getReg r = s.getReg r := fun r hr => ((r0.trans r1).trans r2).get hr
  have f02 : Frame s t2 (fun _ => False) := ((f0.trans f1).trans f2).mono (fun A _ hA => by simp_all)
  by_cases hl0 : lay = 0
  · rw [if_pos hl0] at p2
    obtain ⟨t3, s3, p3, x3, r3, f3⟩ := last t2 p2 (by rw [g2 _ (by simp)]; exact h20)
    have hs : ¬ hiSel lay i m := fun hh => hh.1 hl0
    refine ⟨t3, (((s0.trans s1).trans s2).trans s3).of_eq (by simp [trX, hi0', hl0]) (by simp [trX, hi0', hl0]),
      p3, x3, ?_, (((r0.trans r1).trans r2).trans r3).mono (by simp),
      (f02.trans f3).mono (fun A _ hA => by simp_all)⟩
    rw [if_neg hs]
    exact hlo.frame (f02.trans f3) (by decide) (by simp) (by simp)
  rw [if_neg hl0] at p2
  obtain ⟨t3, s3, p3, r3, f3⟩ : ∃ t, Steps image t2 2 2 t ∧ t.pc = (if m ≠ 6 then pcOf 1676 else pcOf 1671) ∧
      RegsExcept t2 t [.x6] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound blkC2 (codeAt_ctr2 h) t2 p2 (by simp [blkC2.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, blkC2.res, E.eval, CmpOp.eval, g2 _ (by simp), h20]
      rw [show (6#64 : Word) = BitVec.ofNat 64 6 from rfl, ne_of (by omega) (by norm_num)]
      by_cases hm6 : m = 6 <;> simp [hm6]
    · intro r hr; simp at hr; cases r <;> simp_all [blkC2.res, rv_simp] <;> rfl
    · intro A hA hn; simp [blkC2.res, rv_simp]
  have f03 : Frame s t3 (fun _ => False) := (f02.trans f3).mono (fun A _ hA => by simp_all)
  have g3 : ∀ r, r ∉ [.x6] → t3.getReg r = s.getReg r := fun r hr => ((((r0.trans r1).trans r2).trans r3)).get
    (by simpa using hr)
  by_cases hm6 : m ≠ 6
  · rw [if_pos hm6] at p3
    obtain ⟨t4, s4, p4, x4, r4, f4⟩ := last t3 p3 (by rw [g3 _ (by simp)]; exact h20)
    have hs : ¬ hiSel lay i m := fun hh => hm6 hh.2.2
    refine ⟨t4, ((((s0.trans s1).trans s2).trans s3).trans s4).of_eq (by simp [trX, hi0', hl0, hm6])
      (by simp [trX, hi0', hl0, hm6]), p4, x4, ?_, ((((r0.trans r1).trans r2).trans r3).trans r4).mono (by simp),
      (f03.trans f4).mono (fun A _ hA => by simp_all)⟩
    rw [if_neg hs]
    exact hlo.frame (f03.trans f4) (by decide) (by simp) (by simp)
  have hm6' : m = 6 := by omega
  rw [if_neg hm6] at p3
  have hs : hiSel lay i m := ⟨hl0, hi0', hm6'⟩
  have hobl : Oblig.all t3 blkC3.res.st.obl := by simp [blkC3.res, rv_simp]
  refine ⟨_, ((((s0.trans s1).trans s2).trans s3).trans (symRun_sound blkC3 (codeAt_ctr3 h) t3 p3 hobl)).of_eq
    (by simp [trX, hi0', hl0, hm6', blkC3.res]) (by simp [trX, hi0', hl0, hm6', blkC3.res]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blkC3.res, E.eval]
  · simp only [Result.toState_getReg, blkC3.res, rv_simp]
    rw [g3 .x20 (by simp), h20, hm6']; rfl
  · rw [if_pos hs]
    have hv3 := hhv.frame f03 (by decide) (by simp) (by simp)
    constructor
    · simp only [Result.toState_getMem, blkC3.res]
      t3n []
      exact hv3.1
    · simp only [Result.toState_getMem, blkC3.res]
      t3n []
      exact hv3.2
  · exact ((((r0.trans r1).trans r2).trans r3).trans (blkC3_regs t3)).mono (by simp)
  · have f4 : Frame t3 (blkC3.res.toState t3) (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
      intro A hA hn
      simp only [Result.toState_getMem, blkC3.res]
      t3n []
      have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
      rw [hA', if_neg (by simp only [CHAIN] at hn; omega), if_neg (by simp only [CHAIN] at hn; omega)]
    exact (f03.trans f4).mono (fun A _ hA => by simp_all)
theorem shared_header {image : Image} {b : Nat} (h : SeedIndependentAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (b + 9)) (lay : Layer)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) :
    ∃ t, Steps image s (headerK lay) (headerK lay) t ∧ t.pc = pcOf (b + 23) ∧
      HeaderPost s t (height lay) := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  fin_cases lay
  · exact sign_header_0 s hpc h8
  · exact sign_header_1 s hpc h8
  · exact sign_header_2 s hpc h8
  · exact sign_header_3 s hpc h8
theorem shared_header_source {image : Image} {b : Nat} (h : SeedIndependentAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (b + 9)) (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ height lay)
    (hi : i < 64) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    ∃ t, Steps image s (headerK lay) (headerK lay) t ∧ t.pc = pcOf (b + 23) ∧
      t.getReg .x10 = BitVec.ofNat 64 0x201A0 ∧ t.getReg .x11 = 64#64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (0x201A0 + 48) ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 16)) = (chainHeader lay tree leaf i step).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = (chainHeader lay tree leaf i step).extractLsb' 64 64 ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun A => A = 0x201A0 + 16 ∨ A = 0x201A0 + 24) := by
  obtain ⟨t, st, pc, post⟩ := shared_header h s hpc lay h8
  refine ⟨t, st, pc, post.arg0, post.arg1, post.arg2,
    post.low.trans (packedAt_source s lay tree leaf i step hr hf hi hs h8 h9 h18 h19 h20),
    ?_, post.regs, post.frame⟩
  exact (post.high.trans (routedAt_high_zero s lay tree leaf hr h9 h18)).trans
    (source_high_actual lay tree leaf i step hr hf hi hs).symm
theorem sub0_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_0 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_0 h) s hpc (by simp [st_0, blk117_0.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_0, Result.toState_pc, E.eval]
  · simp [st_0, blk117_0.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_0, blk117_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_0, blk117_0.res, rv_simp]
theorem sub1_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1)) (m cap : Nat) (hm : m < 2 ^ 64) (hcap : cap < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h17 : s.getReg .x17 = BitVec.ofNat 64 cap) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if m = cap then pcOf (b + 2) else pcOf (b + 8)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_1 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_1 h) s hpc (by simp [st_1, blk117_1.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_1, rebase, blk117_1.res, E.eval, CmpOp.eval, h20, h17]
    by_cases hmc : m = cap
    · subst hmc; simp
    · rw [if_neg hmc]
      have : BitVec.ofNat 64 m ≠ BitVec.ofNat 64 cap := fun he => hmc ((ofNat_inj hm hcap).mp he)
      simp [this]
  · intro r hr; cases r <;> simp_all [st_1, blk117_1.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_1, blk117_1.res, rv_simp]
theorem sub2_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 2)) (valp : Nat) (h23 : s.getReg .x23 = BitVec.ofNat 64 valp)
    (hv8 : valp % 8 = 0) (hv : valp + 16 ≤ 2 ^ 24) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 8) ∧
      t.getMem (BitVec.ofNat 64 valp) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (valp + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x29] ∧ Frame s t (fun A => A = valp ∨ A = valp + 8) := by
  have hrun := run_2 h.2.1
  have hobl : Oblig.all s st_2.obl := by
    simp only [st_2, blk117_2.res]
    t3n [h23]
    omega
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_2 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_2, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
  · intro r hr; simp at hr; cases r <;> simp_all [st_2, blk117_2.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub8_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 8)) (m e : Nat) (hm : m < 2 ^ 64) (he : e < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h21 : s.getReg .x21 = BitVec.ofNat 64 e) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if m = e then pcOf (b + 26) else pcOf (b + 9)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_8 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_8 h) s hpc (by simp [st_8, blk117_8.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_8, rebase, blk117_8.res, E.eval, CmpOp.eval, h20, h21]
    by_cases hme : m = e
    · subst hme; simp
    · rw [if_neg hme]
      have : BitVec.ofNat 64 m ≠ BitVec.ofNat 64 e := fun he' => hme ((ofNat_inj hm he).mp he')
      simp [this]
  · intro r hr; cases r <;> simp_all [st_8, blk117_8.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_8, blk117_8.res, rv_simp]
abbrev sub9_spec {image : Image} {b : Nat} := @shared_header_source image b
theorem sub26_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 26)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_26 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_26 h) s hpc (by simp [st_26, blk117_26.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_26, blk117_26.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_26, blk117_26.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_26, blk117_26.res, rv_simp]
theorem fetch_sub23 {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 23)) : fetch image s = some (.base .ECALL) :=
  ((SeedIndependent.codeAt_sub_23 h).fetch s hpc).trans rfl
theorem sumTo_split (F : Nat → Nat) (a : Nat) : ∀ n, sumTo F (a + 1 + n) = sumTo F a + F a + sumTo (fun j => F (a + 1 + j)) n
  | 0 => by simp [sumTo]
  | n + 1 => by
    rw [show a + 1 + (n + 1) = (a + 1 + n) + 1 by omega, sumTo, sumTo_split F a n, sumTo]; omega
/-- C3 (FULL): steps of one chain run of `e` hashes (entry 1, per step `rungK + trX`, exit 9). -/
def chainK (lay : Layer) (i e : Nat) : Nat := sumTo (fun m => rungK lay + trX lay.val i m) e + 10
/-- C3 (FULL): cycles of one chain run of `e` hashes. -/
def chainCy (lay : Layer) (i e : Nat) : Nat := sumTo (fun m => rungC lay + trX lay.val i m) e + 10
theorem halfOf_chainHigh (lay : Layer) (i m : Nat) (a : BitVec 256) :
    ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.chainHigh lay i m) a =
      if hiSel lay.val i m then a.extractLsb' 128 128 else a.extractLsb' 0 128 := by
  have hl : (lay ≠ 0) ↔ lay.val ≠ 0 := ⟨fun h h' => h (Fin.ext h'), fun h h' => h (by rw [h']; rfl)⟩
  unfold ClaudeWCT.WCT9.halfOf ClaudeWCT.WCT9.chainHigh hiSel
  by_cases h1 : lay.val ≠ 0 <;> by_cases h2 : i = 0 <;> by_cases h3 : m = 6 <;> simp_all
/-- C2: the half of a lower leaf / node hash output kept by the machine (`16` = the HIGH half, for even indices). -/
def hiO (x : Nat) : Nat := if x % 2 = 0 then 16 else 0
theorem and1_ofNat (x : Nat) : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (1 : Nat) % 2 ^ 64 = 1 by norm_num, Nat.and_one_is_mod]
  omega
theorem halfSel_eval (x : Nat) :
    BinOp.eval .sll (BinOp.eval .xor (BinOp.eval .and (BitVec.ofNat 64 x) 1#64) 1#64) 4#64 =
      BitVec.ofNat 64 (hiO x) := by
  show BinOp.eval .sll (BinOp.eval .xor (BitVec.ofNat 64 x &&& 1#64) 1#64) 4#64 = _
  rw [and1_ofNat]; unfold hiO
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> simp [h] <;> decide
theorem DigAt.writeHash_lowerHalf (t : MachineState) (a : BitVec 256) (B lay x : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 B) (hB : B + 32 < 2 ^ 64) (hl : 1 ≤ lay ∧ lay < 4) :
    DigAt (writeHash t a) (B + hiO x) (ClaudeWCT.WCT9.lowerHalf lay x a) := by
  unfold hiO ClaudeWCT.WCT9.lowerHalf ClaudeWCT.WCT9.halfOf ClaudeWCT.WCT9.lowerHigh
  by_cases hx : x % 2 = 0
  · simp only [hx, hl, if_true, decide_true, Bool.and_self]; exact DigAt.writeHash_hi t a B h12 hB
  · simp only [hx, hl, if_false, decide_true, decide_false, Bool.and_false, Bool.false_eq_true, Nat.add_zero]
    exact DigAt.writeHash_lo t a B h12 hB
section loop
variable {image : Image} {b : Nat} (hsub : SeedIndependentAt image b) (sk : BitVec 256) {s0 : MachineState}
  {lay : Layer} {tree leaf i cap e valp ret : Nat} (hpre : ChainPre s0 lay tree leaf i cap e valp ret)
include hsub hpre
omit hpre in
theorem chain_entry (hpc : s0.pc = pcOf b) (seed : Digest) (hseed : DigAt s0 (CHAIN + 48) seed) :
    ∃ t, Steps image s0 1 1 t ∧ ChainHead b s0 valp 0 seed t := by
  obtain ⟨t, st, tpc, t20, tr, tf⟩ := sub0_spec hsub s0 (by simpa using hpc)
  exact ⟨t, st, ⟨tpc, t20, tr.mono (by simp [chainRegs]), tf.mono (fun _ _ h => h.elim),
    hseed.frame tf (by decide) (by simp) (by simp)⟩⟩
theorem chain_tail {m : Nat} {u : MachineState} (hupc : u.pc = pcOf (b + 23))
    (h20 : u.getReg .x20 = BitVec.ofNat 64 m) (hm : m < 8) (h12 : u.getReg .x12 = BitVec.ofNat 64 (CHAIN + 48))
    (hregs : RegsExcept s0 u chainRegs) (hfr : Frame s0 u (ChainW valp)) (a : BitVec 256) :
    ∃ w, Steps image (writeHash u a) (2 + trX lay.val i m) (2 + trX lay.val i m) w ∧
      ChainHead b s0 valp (m + 1) (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.chainHigh lay i m) a) w ∧
      Frame u w (fun A => CHAIN + 48 ≤ A ∧ A < CHAIN + 80) := by
  have hwf := Frame.writeHash u a (CHAIN + 48) h12 (by decide)
  have g : ∀ r, r ∉ chainRegs → u.getReg r = s0.getReg r := fun r hr => hregs.get hr
  have hi := hpre.hi
  obtain ⟨w, st, wpc, w20, wv, wr, wf⟩ := tramp_spec hsub (writeHash u a)
    (by rw [pc_writeHash, hupc, pcOf_add4]) lay.val i m (by have := lay.isLt; omega) (by omega) (by omega)
    (by rw [getReg_writeHash, g _ (by simp [chainRegs]), hpre.x8])
    (by rw [getReg_writeHash, g _ (by simp [chainRegs]), hpre.x19])
    (by rw [getReg_writeHash, h20]) _ _ (DigAt.writeHash_lo u a (CHAIN + 48) h12 (by decide))
    (DigAt.writeHash_hi u a (CHAIN + 48) h12 (by decide))
  have hfw : Frame u w (fun A => CHAIN + 48 ≤ A ∧ A < CHAIN + 80) := (hwf.trans wf).mono (fun A _ h => by
    rcases h with h | h
    · exact h
    · simp only [CHAIN] at h ⊢; omega)
  refine ⟨w, st, ⟨wpc, w20, ?_, ?_, ?_⟩, hfw⟩
  · have h1 : RegsExcept u (writeHash u a) [] := fun r _ => getReg_writeHash u a r
    refine ((hregs.trans h1).trans wr).mono ?_
    intro r hr
    simp only [chainRegs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    tauto
  · refine (hfr.trans (hwf.trans wf)).mono ?_
    intro A _ h; unfold ChainW; rcases h with h | h | h
    · exact h
    · exact Or.inr (Or.inl h)
    · right; left; simp only [CHAIN] at h ⊢; omega
  · rw [halfOf_chainHigh]; exact wv
theorem chain_step {m : Nat} (hm : m < e) (hmc : m ≠ cap) {v : Digest} {t : MachineState}
    (ht : ChainHead b s0 valp m v t) :
    TSim image sk t (rungK lay + trX lay.val i m) (rungC lay + trX lay.val i m) 1 1
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m) (chainInput lay tree leaf i m v))
      (fun v' u => ChainHead b s0 valp (m + 1) v' u ∧
        Frame t u (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 48 ≤ A ∧ A < CHAIN + 80))) := by
  have hcap := hpre.hcap
  have he := hpre.he
  have hi := hpre.hi
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have h17 : t.getReg .x17 = BitVec.ofNat 64 cap := by rw [g _ (by simp [chainRegs]), hpre.x17]
  have h21 : t.getReg .x21 = BitVec.ofNat 64 e := by rw [g _ (by simp [chainRegs]), hpre.x21]
  have h19 : t.getReg .x19 = BitVec.ofNat 64 i := by rw [g _ (by simp [chainRegs]), hpre.x19]
  have h8 : t.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [g _ (by simp [chainRegs]), hpre.x8]
  have h5 : t.getReg .x5 = 0 := by rw [g _ (by simp [chainRegs]), hpre.x5]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc m cap (by omega) (by omega) ht.x20 h17
  rw [if_neg hmc] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub8_spec hsub t1 t1pc m e (by omega) (by omega)
    (by rw [t1r.get (by simp)]; exact ht.x20) (by rw [t1r.get (by simp)]; exact h21)
  rw [if_neg (by omega)] at t2pc
  have e12 : RegsExcept t t2 [] := (t1r.trans t2r).mono (by simp)
  obtain ⟨t3, st3, t3pc, t3x10, t3x11, t3x12, t3w, t3w24, t3r, t3f⟩ :=
    sub9_spec hsub t2 t2pc lay tree leaf i m hpre.hroute hpre.hleaf hi (by omega)
    (by rw [e12.get (by simp)]; exact h8)
    (by rw [e12.get (by simp), g _ (by simp [chainRegs]), hpre.x9])
    (by rw [e12.get (by simp), g _ (by simp [chainRegs]), hpre.x18])
    (by rw [e12.get (by simp)]; exact h19)
    (by rw [e12.get (by simp)]; exact ht.x20)
  have f13 : Frame t t3 (fun A => A = CHAIN + 16 ∨ A = CHAIN + 24) :=
    ((t1f.trans t2f).trans t3f).mono (fun A _ h => by rcases h with (h | h) | h <;> simp_all)
  have r13 : RegsExcept t t3 [.x6, .x7, .x10, .x11, .x12, .x28, .x30] := (e12.trans t3r).mono (by simp)
  have hq := chain_hash hpre hm ht (f13.mono (fun A _ h => Or.inl h)) t3x10 t3x11 t3w t3w24
  have hv : hashArgumentsValid t3 = true :=
    hashArgs_const t3 CHAIN 64 (CHAIN + 48) t3x10 t3x11 t3x12 (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have h5' : t3.getReg .x5 = 0 := by rw [r13.get (by simp), h5]
  have h20' : t3.getReg .x20 = BitVec.ofNat 64 m := by rw [r13.get (by simp), ht.x20]
  have hr3 : RegsExcept s0 t3 chainRegs := (ht.regs.trans r13).mono (by simp [chainRegs])
  have hf3 : Frame s0 t3 (ChainW valp) :=
    (ht.frame.trans f13).mono (fun A _ h => by unfold ChainW at *; rcases h with h | h <;> simp_all)
  rw [ClaudeWCT.WCT9.halfHash_eq]
  refine (TSim.steps (st1.trans (st2.trans st3)) (TSim.publicHash_bind (k := 2 + trX lay.val i m)
    (c := 2 + trX lay.val i m) (n := 0) (b := 0)
    (fetch_sub23 hsub t3 t3pc) h5' hv hq (fun a => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · obtain ⟨w, stw, hw, wf⟩ := chain_tail hsub hpre t3pc h20' (by omega) t3x12 hr3 hf3 a
    exact TSim.pure_steps stw ⟨hw, (f13.trans wf).mono (fun A _ h => by rcases h with h | h <;> simp_all)⟩
  all_goals simp [toQ_chainInput_blocks, rungK, rungC] <;> omega
theorem chain_step_cap {m : Nat} (hm : m < e) (hmc : m = cap) {v : Digest} {t : MachineState}
    (ht : ChainHead b s0 valp m v t) :
    TSim image sk t (rungK lay + 6 + trX lay.val i m) (rungC lay + 6 + trX lay.val i m) 1 1
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m) (chainInput lay tree leaf i m v))
      (fun v' u => ChainHead b s0 valp (m + 1) v' u ∧ DigAt u valp v ∧ Frame t u (ChainW valp)) := by
  have hcap := hpre.hcap
  have he := hpre.he
  have hi := hpre.hi
  have hvc := hpre.hvc
  have hvb := hpre.hv
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have h17 : t.getReg .x17 = BitVec.ofNat 64 cap := by rw [g _ (by simp [chainRegs]), hpre.x17]
  have h21 : t.getReg .x21 = BitVec.ofNat 64 e := by rw [g _ (by simp [chainRegs]), hpre.x21]
  have h19 : t.getReg .x19 = BitVec.ofNat 64 i := by rw [g _ (by simp [chainRegs]), hpre.x19]
  have h8 : t.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [g _ (by simp [chainRegs]), hpre.x8]
  have h5 : t.getReg .x5 = 0 := by rw [g _ (by simp [chainRegs]), hpre.x5]
  have h23 : t.getReg .x23 = BitVec.ofNat 64 valp := by rw [g _ (by simp [chainRegs]), hpre.x23]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc m cap (by omega) (by omega) ht.x20 h17
  rw [if_pos hmc] at t1pc
  obtain ⟨t2, st2, t2pc, t2v0, t2v8, t2r, t2f⟩ := sub2_spec hsub t1 t1pc valp
    (by rw [t1r.get (by simp)]; exact h23) hpre.hv8 hpre.hv
  have hvt1 := ht.val.frame t1f (by decide) (by simp) (by simp)
  have hvv : DigAt t2 valp v := ⟨t2v0.trans hvt1.1, t2v8.trans hvt1.2⟩
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub8_spec hsub t2 t2pc m e (by omega) (by omega)
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact ht.x20)
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h21)
  rw [if_neg (by omega)] at t3pc
  have e13 : RegsExcept t t3 [.x6, .x7, .x29] := ((t1r.trans t2r).trans t3r).mono (by simp)
  obtain ⟨t4, st4, t4pc, t4x10, t4x11, t4x12, t4w, t4w24, t4r, t4f⟩ :=
    sub9_spec hsub t3 t3pc lay tree leaf i m hpre.hroute hpre.hleaf hi (by omega)
    (by rw [e13.get (by simp)]; exact h8)
    (by rw [e13.get (by simp), g _ (by simp [chainRegs]), hpre.x9])
    (by rw [e13.get (by simp), g _ (by simp [chainRegs]), hpre.x18])
    (by rw [e13.get (by simp)]; exact h19)
    (by rw [e13.get (by simp)]; exact ht.x20)
  have f14 : Frame t t4 (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (valp ≤ A ∧ A < valp + 16)) :=
    (((t1f.trans t2f).trans t3f).trans t4f).mono (fun A _ h => by
      rcases h with ((h | h | h) | h) | h <;> first | exact h.elim | (right; omega) | (left; exact h))
  have r14 : RegsExcept t t4 [.x6, .x7, .x10, .x11, .x12, .x28, .x29, .x30] :=
    (e13.trans t4r).mono (by simp)
  have hq := chain_hash hpre hm ht f14 t4x10 t4x11 t4w t4w24
  have hv : hashArgumentsValid t4 = true :=
    hashArgs_const t4 CHAIN 64 (CHAIN + 48) t4x10 t4x11 t4x12 (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have h5' : t4.getReg .x5 = 0 := by rw [r14.get (by simp), h5]
  have h20' : t4.getReg .x20 = BitVec.ofNat 64 m := by rw [r14.get (by simp), ht.x20]
  have hr4 : RegsExcept s0 t4 chainRegs := (ht.regs.trans r14).mono (by simp [chainRegs])
  have hf4 : Frame s0 t4 (ChainW valp) :=
    (ht.frame.trans f14).mono (fun A _ h => by unfold ChainW at *; rcases h with h | h | h <;> simp_all)
  have hvv4 : DigAt t4 valp v := hvv.frame (t3f.trans t4f) (by omega)
    (by simp; sc_omega) (by simp; sc_omega)
  rw [ClaudeWCT.WCT9.halfHash_eq]
  refine (TSim.steps (st1.trans (st2.trans (st3.trans st4))) (TSim.publicHash_bind (k := 2 + trX lay.val i m)
    (c := 2 + trX lay.val i m) (n := 0) (b := 0)
    (fetch_sub23 hsub t4 t4pc) h5' hv hq (fun a => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · obtain ⟨w, stw, hw, wf⟩ := chain_tail hsub hpre t4pc h20' (by omega) t4x12 hr4 hf4 a
    refine TSim.pure_steps stw ⟨hw, hvv4.frame wf (by omega) (by simp; omega) (by simp; omega), ?_⟩
    refine (f14.trans wf).mono (fun A _ h => ?_)
    unfold ChainW; rcases h with (h | h) | h <;> simp_all
  all_goals simp [toQ_chainInput_blocks, rungK, rungC] <;> omega
theorem chain_exit {v : Digest} {t : MachineState} (ht : ChainHead b s0 valp e v t) (hec : e ≠ cap) :
    ∃ u, Steps image t 3 3 u ∧ u.pc = pcOf ret ∧ RegsExcept t u [] ∧ Frame t u (fun _ => False) := by
  have he := hpre.he
  have hcap := hpre.hcap
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc e cap (by omega) (by omega) ht.x20
    (by rw [g _ (by simp [chainRegs]), hpre.x17])
  rw [if_neg hec] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub8_spec hsub t1 t1pc e e (by omega) (by omega)
    (by rw [t1r.get (by simp)]; exact ht.x20)
    (by rw [t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x21])
  rw [if_pos rfl] at t2pc
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub26_spec hsub t2 t2pc ret
    (by rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x1])
  exact ⟨t3, st1.trans (st2.trans st3), t3pc, ((t1r.trans t2r).trans t3r).mono (by simp),
    ((t1f.trans t2f).trans t3f).mono (fun A _ h => by simp_all)⟩
theorem chain_exit_cap {v : Digest} {t : MachineState} (ht : ChainHead b s0 valp e v t) (hec : e = cap) :
    ∃ u, Steps image t 9 9 u ∧ u.pc = pcOf ret ∧ DigAt u valp v ∧ RegsExcept t u [.x6, .x7, .x29] ∧
      Frame t u (fun A => valp ≤ A ∧ A < valp + 16) := by
  have he := hpre.he
  have hcap := hpre.hcap
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc e cap (by omega) (by omega) ht.x20
    (by rw [g _ (by simp [chainRegs]), hpre.x17])
  rw [if_pos hec] at t1pc
  obtain ⟨t2, st2, t2pc, t2v0, t2v8, t2r, t2f⟩ := sub2_spec hsub t1 t1pc valp
    (by rw [t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x23]) hpre.hv8 hpre.hv
  have hvt1 := ht.val.frame t1f (by decide) (by simp) (by simp)
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub8_spec hsub t2 t2pc e e (by omega) (by omega)
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact ht.x20)
    (by rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x21])
  rw [if_pos rfl] at t3pc
  obtain ⟨t4, st4, t4pc, t4r, t4f⟩ := sub26_spec hsub t3 t3pc ret
    (by rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x1])
  refine ⟨t4, st1.trans (st2.trans (st3.trans st4)), t4pc, ?_, (((t1r.trans t2r).trans t3r).trans t4r).mono
    (by simp), (((t1f.trans t2f).trans t3f).trans t4f).mono (fun A _ h => by
      rcases h with ((h | h | h) | h) | h <;> first | exact h.elim | omega)⟩
  have hvv : DigAt t2 valp v := ⟨t2v0.trans hvt1.1, t2v8.trans hvt1.2⟩
  exact hvv.frame (t3f.trans t4f) (by have := hpre.hv; omega) (by simp) (by simp)
theorem chainRun_tsim (hpc : s0.pc = pcOf b) (seed : Digest) (hseed : DigAt s0 (CHAIN + 48) seed) :
    TSim image sk s0 (chainK lay i e) (chainCy lay i e) e e
      (do let v ← ClaudeWCT.WCT9.chainW lay tree leaf i 0 cap seed
          let last ← ClaudeWCT.WCT9.chainW lay tree leaf i cap (e - cap) v
          pure (v, last))
      (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
        RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainW valp)) := by
  have hcap := hpre.hcap
  have hvc := hpre.hvc
  have hvb := hpre.hv
  obtain ⟨t0, st0, h0⟩ := chain_entry hsub hpc seed hseed
  have p1 : TSim image sk t0 (sumTo (fun j => rungK lay + trX lay.val i (0 + j)) cap)
      (sumTo (fun j => rungC lay + trX lay.val i (0 + j)) cap)
      (sumTo (fun _ => 1) cap) (sumTo (fun _ => 1) cap)
      (ClaudeWCT.WCT9.chainW lay tree leaf i 0 cap seed) (fun v t => ChainHead b s0 valp cap v t) := by
    unfold ClaudeWCT.WCT9.chainW
    exact TSim.foldlM_range' 0 cap _ seed (fun j v t => ChainHead b s0 valp j v t) _ _ _ _
      (fun j hj v t ht => (chain_step hsub sk hpre (m := 0 + j) (by omega) (by omega)
        (by simpa using ht)).mono (fun v' u hu => by simpa using hu.1)) h0
  rcases Nat.lt_or_ge cap e with hlt | hge
  ·
    have hsplit : ClaudeWCT.WCT9.chainW lay tree leaf i cap (e - cap) = fun v =>
        ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i cap) (chainInput lay tree leaf i cap v) >>= fun v1 =>
          (List.range' (cap + 1) (e - cap - 1)).foldlM
            (fun value step => ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i step)
              (chainInput lay tree leaf i step value)) v1 := by
      funext v
      unfold ClaudeWCT.WCT9.chainW
      rw [show e - cap = e - cap - 1 + 1 by omega, List.range'_succ, List.foldlM_cons]
      rfl
    have rest : ∀ v t, ChainHead b s0 valp cap v t →
        TSim image sk t (rungK lay + 6 + trX lay.val i cap +
            (sumTo (fun j => rungK lay + trX lay.val i (cap + 1 + j)) (e - cap - 1) + 3))
          (rungC lay + 6 + trX lay.val i cap +
            (sumTo (fun j => rungC lay + trX lay.val i (cap + 1 + j)) (e - cap - 1) + 3))
          (1 + (sumTo (fun _ => 1) (e - cap - 1) + 0))
          (1 + (sumTo (fun _ => 1) (e - cap - 1) + 0))
          (do let last ← ClaudeWCT.WCT9.chainW lay tree leaf i cap (e - cap) v; pure (v, last))
          (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
            RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainW valp)) := by
      intro v t ht
      rw [hsplit, bind_assoc]
      refine TSim.bind (chain_step_cap hsub sk hpre hlt rfl ht) (fun v1 u hu => ?_)
      have p2 := TSim.foldlM_range' (image := image) (sk := sk) (cap + 1) (e - cap - 1)
        (fun value step => ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i step)
          (chainInput lay tree leaf i step value)) v1
        (fun j v' w => ChainHead b s0 valp (cap + 1 + j) v' w ∧ DigAt w valp v)
        (fun j => rungK lay + trX lay.val i (cap + 1 + j)) (fun j => rungC lay + trX lay.val i (cap + 1 + j))
        (fun _ => 1) (fun _ => 1)
        (fun j hj v' w hw => (chain_step hsub sk hpre (m := cap + 1 + j) (by omega) (by omega)
          hw.1).mono (fun v'' w' hw' => ⟨by simpa [Nat.add_assoc] using hw'.1,
            hw.2.frame hw'.2 (by omega) (by simp; omega) (by simp; omega)⟩))
        ⟨by simpa using hu.1, hu.2.1⟩
      refine TSim.bind p2 (fun last w hw => ?_)
      have hw1 : ChainHead b s0 valp e last w := by
        have := hw.1; rwa [show cap + 1 + (e - cap - 1) = e by omega] at this
      obtain ⟨x, stx, xpc, xr, xf⟩ := chain_exit hsub hpre hw1 (by omega)
      exact TSim.pure_steps stx ⟨xpc, hw.2.frame xf (by omega) (by simp) (by simp),
        hw1.val.frame xf (by decide) (by simp) (by simp), (hw1.regs.trans xr).mono (by simp),
        (hw1.frame.trans xf).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)⟩
    refine (TSim.steps st0 (TSim.bind p1 rest)).of_eq rfl ?_ ?_ ?_ ?_
    · unfold chainK
      rw [show e = cap + 1 + (e - cap - 1) by omega, sumTo_split]
      simp only [Nat.zero_add, show cap + 1 + (e - cap - 1) - cap - 1 = e - cap - 1 by omega]
      omega
    · unfold chainCy
      rw [show e = cap + 1 + (e - cap - 1) by omega, sumTo_split]
      simp only [Nat.zero_add, show cap + 1 + (e - cap - 1) - cap - 1 = e - cap - 1 by omega]
      omega
    all_goals simp only [sumTo_const]
    all_goals omega
  ·
    have he : cap = e := by omega
    have hz : ClaudeWCT.WCT9.chainW lay tree leaf i cap (e - cap) = fun v => pure v := by
      funext v; rw [show e - cap = 0 by omega]; rfl
    have rest : ∀ v t, ChainHead b s0 valp cap v t →
        TSim image sk t 9 9 0 0
          (do let last ← ClaudeWCT.WCT9.chainW lay tree leaf i cap (e - cap) v; pure (v, last))
          (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
            RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainW valp)) := by
      intro v t ht
      rw [hz]
      simp only [pure_bind]
      have ht' : ChainHead b s0 valp e v t := he ▸ ht
      obtain ⟨x, stx, xpc, xv, xr, xf⟩ := chain_exit_cap hsub hpre ht' he.symm
      exact TSim.pure_steps stx ⟨xpc, xv, ht'.val.frame xf (by decide) (by simp; omega)
        (by simp; omega), (ht'.regs.trans xr).mono (by simp [chainRegs]),
        (ht'.frame.trans xf).mono (fun A _ h => by
          unfold ChainW at *; rcases h with h | h; exact h; exact Or.inr (Or.inr h))⟩
    refine (TSim.steps st0 (TSim.bind p1 rest)).of_eq rfl ?_ ?_ ?_ ?_
    · unfold chainK; subst he; simp only [Nat.zero_add]; omega
    · unfold chainCy; subst he; simp only [Nat.zero_add]; omega
    all_goals simp only [sumTo_const]
    all_goals subst he; omega
end loop
end SigGolfCandidate.T3M.Sign.Seed
