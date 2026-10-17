import SigGolfCandidate.Research.V7Composed198Gate
import SigGolfCandidate.T3M.Sign.PairStep

namespace SigGolfCandidate.T3M.Sign.Seed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open Keygen Keygen.PackedBlocks
open SeedIndependent (SeedIndependentAt)
open SigGolfCandidate.T3 (Layer Digest chainInput chain shortHash header pad64 zero16 height chainHeader)
open SphincsSecurity (bytesLE bytesLE_length)
set_option backward.isDefEq.respectTransparency false
/-- Pairing stage 1: the header ends at `b + 18` (`jal 1732`) with `t3 = CHAIN`. -/
theorem shared_header {image : Image} {b : Nat} (h : SeedIndependentAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (b + 9)) (lay : Layer)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) :
    ∃ t, Steps image s (headerK lay - 5) (headerK lay - 5) t ∧ t.pc = pcOf (b + 18) ∧
      SignHeaderPost s t (height lay) := by
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
    ∃ t, Steps image s (headerK lay - 5) (headerK lay - 5) t ∧ t.pc = pcOf (b + 18) ∧
      t.getReg .x28 = BitVec.ofNat 64 0x201A0 ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 16)) = (chainHeader lay tree leaf i step).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = (chainHeader lay tree leaf i step).extractLsb' 64 64 ∧
      RegsExcept s t [.x6, .x7, .x28, .x30] ∧
      Frame s t (fun A => A = 0x201A0 + 16 ∨ A = 0x201A0 + 24) := by
  obtain ⟨t, st, pc, post⟩ := shared_header h s hpc lay h8
  refine ⟨t, st, pc, post.x28,
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
theorem sumTo_split (F : Nat → Nat) (a : Nat) : ∀ n, sumTo F (a + 1 + n) = sumTo F a + F a + sumTo (fun j => F (a + 1 + j)) n
  | 0 => by simp [sumTo]
  | n + 1 => by
    rw [show a + 1 + (n + 1) = (a + 1 + n) + 1 by omega, sumTo, sumTo_split F a n, sumTo]; omega
/-- C3 (FULL): steps of one chain run of `e` hashes (entry 1, per step `rungK + trX`, exit 9). -/
def chainK (lay : Layer) (i e : Nat) : Nat := sumTo (fun m => rungK lay + trX lay.val i m) e + 10
/-- C3 (FULL): cycles of one chain run of `e` hashes. -/
def chainCy (lay : Layer) (i e : Nat) : Nat := sumTo (fun m => rungC lay + trX lay.val i m) e + 10
/-- C2: the half of a lower leaf / node hash output kept by the machine (`16` = the HIGH half, for even indices). -/
def hiO (x : Nat) : Nat := if x % 2 = 0 then 16 else 0
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
  {lay : Layer} {tree leaf i cap e valp ret : Nat} (hpre : ChainPreS s0 lay tree leaf i cap e valp ret)
include hsub hpre
omit hpre in
theorem chain_entry (hpc : s0.pc = pcOf b) (seed : Digest) (hseed : DigAt s0 (CHAIN + 48) seed) :
    ∃ t, Steps image s0 1 1 t ∧ ChainHeadS b s0 valp 0 seed t := by
  obtain ⟨t, st, tpc, t20, tr, tf⟩ := sub0_spec hsub s0 (by simpa using hpc)
  exact ⟨t, st, ⟨tpc, t20, tr.mono (by simp [chainRegs]), tf.mono (fun _ _ h => h.elim),
    hseed.frame tf (by decide) (by simp) (by simp)⟩⟩
omit hpre in
theorem stepCode_of : StepCode image := by
  obtain ⟨rfl, rfl⟩ := hsub.2.2.2.2
  exact stepCode_reference
/-- Pairing stage 1: the header from `b + 9` and the step block (`pair_rung`), from a state `t3` that agrees with the
chain head `t` outside the header words and `valp`. -/
theorem chain_rung {m : Nat} (hm : m < e) {v : Digest} {t t2 : MachineState}
    (ht : ChainHeadS b s0 valp m v t) (ht2 : t2.pc = pcOf (b + 9))
    (hr2 : RegsExcept t t2 [.x6, .x7, .x29]) (hf2 : Frame t t2 (fun A => valp ≤ A ∧ A < valp + 16)) :
    TSim image sk t2 (headerK lay - 5 + (8 + trX lay.val i m)) (headerK lay - 5 + (15 + trX lay.val i m)) 1 1
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m) (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v))
      (fun v' u => ChainHeadS b s0 valp (m + 1) v' u ∧
        Frame t2 u (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112))) := by
  have he := hpre.he
  have hi := hpre.hi
  have hvc := hpre.hvc
  obtain rfl := SeedIndependent.b_eq hsub
  have g : ∀ r, r ∉ chainRegs → r ∉ [.x6, .x7, .x29] → t2.getReg r = s0.getReg r := fun r hr hr' =>
    (hr2.get hr').trans (ht.regs.get hr)
  obtain ⟨t3, st3, t3pc, t3x28, t3w, t3w24, t3r, t3f⟩ :=
    sub9_spec hsub t2 ht2 lay tree leaf i m hpre.hroute hpre.hleaf hi (by omega)
    (by rw [g _ (by simp [chainRegs]) (by simp)]; exact hpre.x8)
    (by rw [g _ (by simp [chainRegs]) (by simp)]; exact hpre.x9)
    (by rw [g _ (by simp [chainRegs]) (by simp)]; exact hpre.x18)
    (by rw [g _ (by simp [chainRegs]) (by simp)]; exact hpre.x19)
    (by rw [hr2.get (by simp)]; exact ht.x20)
  have g3 : ∀ r, r ∉ chainRegs → t3.getReg r = s0.getReg r := fun r hr =>
    (t3r.get (fun h => hr (by simp [chainRegs] at h ⊢; rcases h with h | h | h | h <;> simp [h]))).trans
      (g r hr (fun h => hr (by simp [chainRegs] at h ⊢; rcases h with h | h | h <;> simp [h])))
  have f03 : Frame s0 t3 (fun A => ChainWS valp A) := ((ht.frame.trans hf2).trans t3f).mono (fun A _ h => by
    unfold ChainWS at *; rcases h with (h | h) | h
    · exact h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h)
  have hv3 : DigAt t3 (CHAIN + 48) v := (ht.val.frame hf2 (by decide) (by omega) (by omega)).frame t3f
    (by decide) (by simp) (by simp)
  have run := pair_rung (stepCode_of hsub) sk t3 (by rw [t3pc]) lay tree leaf i m v hi (by omega)
    (fun hl => by have := hpre.hlow hl; omega)
    ((g3 _ (by simp [chainRegs])).trans hpre.x5)
    ((g3 _ (by simp [chainRegs])).trans hpre.x8)
    ((g3 _ (by simp [chainRegs])).trans hpre.x19)
    (by rw [t3r.get (by simp), hr2.get (by simp)]; exact ht.x20)
    t3x28
    (by rw [f03.get (by decide) (by unfold ChainWS; simp only [CHAIN] at *; omega)]; exact hpre.z0)
    (by rw [f03.get (by decide) (by unfold ChainWS; simp only [CHAIN] at *; omega)]; exact hpre.z8)
    t3w t3w24 (source_high_actual lay tree leaf i m hpre.hroute hpre.hleaf hi (by omega)) hv3
  refine (TSim.steps st3 run).mono ?_
  intro v' u hu
  refine ⟨⟨hu.1, hu.2.1, ?_, ?_, hu.2.2.1⟩, ?_⟩
  · exact (((ht.regs.trans hr2).trans t3r).trans hu.2.2.2.1).mono (by simp [chainRegs])
  · exact (f03.trans hu.2.2.2.2.1).mono (fun A _ h => by
      unfold ChainWS at *; rcases h with h | h
      · exact h
      · exact Or.inr (Or.inl h))
  · exact (t3f.trans hu.2.2.2.2.1).mono (fun A _ h => by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h)
theorem chain_step {m : Nat} (hm : m < e) (hmc : m ≠ cap) {v : Digest} {t : MachineState}
    (ht : ChainHeadS b s0 valp m v t) :
    TSim image sk t (rungK lay + trX lay.val i m) (rungC lay + trX lay.val i m) 1 1
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m) (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v))
      (fun v' u => ChainHeadS b s0 valp (m + 1) v' u ∧
        Frame t u (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112))) := by
  have hcap := hpre.hcap
  have he := hpre.he
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have h17 : t.getReg .x17 = BitVec.ofNat 64 cap := by rw [g _ (by simp [chainRegs]), hpre.x17]
  have h21 : t.getReg .x21 = BitVec.ofNat 64 e := by rw [g _ (by simp [chainRegs]), hpre.x21]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc m cap (by omega) (by omega) ht.x20 h17
  rw [if_neg hmc] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub8_spec hsub t1 t1pc m e (by omega) (by omega)
    (by rw [t1r.get (by simp)]; exact ht.x20) (by rw [t1r.get (by simp)]; exact h21)
  rw [if_neg (by omega)] at t2pc
  have run := chain_rung hsub sk hpre hm ht t2pc ((t1r.trans t2r).mono (by simp))
    ((t1f.trans t2f).mono (fun A _ h => by simp_all))
  refine ((TSim.steps (st1.trans st2) run).of_eq rfl ?_ ?_ rfl rfl).mono ?_
  · unfold rungK headerK; split_ifs <;> omega
  · unfold rungC headerK; split_ifs <;> omega
  · intro v' u hu
    exact ⟨hu.1, ((t1f.trans t2f).trans hu.2).mono (fun A _ h => by rcases h with (h | h) | h <;> simp_all)⟩
theorem chain_step_cap {m : Nat} (hm : m < e) (hmc : m = cap) {v : Digest} {t : MachineState}
    (ht : ChainHeadS b s0 valp m v t) :
    TSim image sk t (rungK lay + 6 + trX lay.val i m) (rungC lay + 6 + trX lay.val i m) 1 1
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m) (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v))
      (fun v' u => ChainHeadS b s0 valp (m + 1) v' u ∧ DigAt u valp v ∧ Frame t u (ChainWS valp)) := by
  have hcap := hpre.hcap
  have he := hpre.he
  have hvc := hpre.hvc
  have hvb := hpre.hv
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have h17 : t.getReg .x17 = BitVec.ofNat 64 cap := by rw [g _ (by simp [chainRegs]), hpre.x17]
  have h21 : t.getReg .x21 = BitVec.ofNat 64 e := by rw [g _ (by simp [chainRegs]), hpre.x21]
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
  have f13 : Frame t t3 (fun A => valp ≤ A ∧ A < valp + 16) :=
    ((t1f.trans t2f).trans t3f).mono (fun A _ h => by
      rcases h with (h | h | h) | h <;> first | exact h.elim | omega)
  have run := chain_rung hsub sk hpre hm ht t3pc (((t1r.trans t2r).trans t3r).mono (by simp)) f13
  have hvv3 : DigAt t3 valp v := hvv.frame t3f (by omega) (by simp) (by simp)
  refine ((TSim.steps (st1.trans (st2.trans st3)) run).of_eq rfl ?_ ?_ rfl rfl).mono ?_
  · unfold rungK headerK; split_ifs <;> omega
  · unfold rungC headerK; split_ifs <;> omega
  · intro v' u hu
    refine ⟨hu.1, hvv3.frame hu.2 (by omega) (by simp only [CHAIN] at *; omega)
      (by simp only [CHAIN] at *; omega), ?_⟩
    exact (f13.trans hu.2).mono (fun A _ h => by
      unfold ChainWS; rcases h with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
theorem chain_exit {v : Digest} {t : MachineState} (ht : ChainHeadS b s0 valp e v t) (hec : e ≠ cap) :
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
theorem chain_exit_cap {v : Digest} {t : MachineState} (ht : ChainHeadS b s0 valp e v t) (hec : e = cap) :
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
        RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainWS valp)) := by
  have hcap := hpre.hcap
  have hvc := hpre.hvc
  have hvb := hpre.hv
  obtain ⟨t0, st0, h0⟩ := chain_entry hsub hpc seed hseed
  have p1 : TSim image sk t0 (sumTo (fun j => rungK lay + trX lay.val i (0 + j)) cap)
      (sumTo (fun j => rungC lay + trX lay.val i (0 + j)) cap)
      (sumTo (fun _ => 1) cap) (sumTo (fun _ => 1) cap)
      (ClaudeWCT.WCT9.chainW lay tree leaf i 0 cap seed) (fun v t => ChainHeadS b s0 valp cap v t) := by
    unfold ClaudeWCT.WCT9.chainW
    exact TSim.foldlM_range' 0 cap _ seed (fun j v t => ChainHeadS b s0 valp j v t) _ _ _ _
      (fun j hj v t ht => (chain_step hsub sk hpre (m := 0 + j) (by omega) (by omega)
        (by simpa using ht)).mono (fun v' u hu => by simpa using hu.1)) h0
  rcases Nat.lt_or_ge cap e with hlt | hge
  ·
    have hsplit : ClaudeWCT.WCT9.chainW lay tree leaf i cap (e - cap) = fun v =>
        ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i cap) (ClaudeWCT.WCT9.chainInputW lay tree leaf i cap v) >>= fun v1 =>
          (List.range' (cap + 1) (e - cap - 1)).foldlM
            (fun value step => ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i step)
              (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) v1 := by
      funext v
      unfold ClaudeWCT.WCT9.chainW
      rw [show e - cap = e - cap - 1 + 1 by omega, List.range'_succ, List.foldlM_cons]
      rfl
    have rest : ∀ v t, ChainHeadS b s0 valp cap v t →
        TSim image sk t (rungK lay + 6 + trX lay.val i cap +
            (sumTo (fun j => rungK lay + trX lay.val i (cap + 1 + j)) (e - cap - 1) + 3))
          (rungC lay + 6 + trX lay.val i cap +
            (sumTo (fun j => rungC lay + trX lay.val i (cap + 1 + j)) (e - cap - 1) + 3))
          (1 + (sumTo (fun _ => 1) (e - cap - 1) + 0))
          (1 + (sumTo (fun _ => 1) (e - cap - 1) + 0))
          (do let last ← ClaudeWCT.WCT9.chainW lay tree leaf i cap (e - cap) v; pure (v, last))
          (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
            RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainWS valp)) := by
      intro v t ht
      rw [hsplit, bind_assoc]
      refine TSim.bind (chain_step_cap hsub sk hpre hlt rfl ht) (fun v1 u hu => ?_)
      have p2 := TSim.foldlM_range' (image := image) (sk := sk) (cap + 1) (e - cap - 1)
        (fun value step => ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i step)
          (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) v1
        (fun j v' w => ChainHeadS b s0 valp (cap + 1 + j) v' w ∧ DigAt w valp v)
        (fun j => rungK lay + trX lay.val i (cap + 1 + j)) (fun j => rungC lay + trX lay.val i (cap + 1 + j))
        (fun _ => 1) (fun _ => 1)
        (fun j hj v' w hw => (chain_step hsub sk hpre (m := cap + 1 + j) (by omega) (by omega)
          hw.1).mono (fun v'' w' hw' => ⟨by simpa [Nat.add_assoc] using hw'.1,
            hw.2.frame hw'.2 (by omega) (by simp; omega) (by simp; omega)⟩))
        ⟨by simpa using hu.1, hu.2.1⟩
      refine TSim.bind p2 (fun last w hw => ?_)
      have hw1 : ChainHeadS b s0 valp e last w := by
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
    have rest : ∀ v t, ChainHeadS b s0 valp cap v t →
        TSim image sk t 9 9 0 0
          (do let last ← ClaudeWCT.WCT9.chainW lay tree leaf i cap (e - cap) v; pure (v, last))
          (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
            RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainWS valp)) := by
      intro v t ht
      rw [hz]
      simp only [pure_bind]
      have ht' : ChainHeadS b s0 valp e v t := he ▸ ht
      obtain ⟨x, stx, xpc, xv, xr, xf⟩ := chain_exit_cap hsub hpre ht' he.symm
      exact TSim.pure_steps stx ⟨xpc, xv, ht'.val.frame xf (by decide) (by simp; omega)
        (by simp; omega), (ht'.regs.trans xr).mono (by simp [chainRegs]),
        (ht'.frame.trans xf).mono (fun A _ h => by
          unfold ChainWS at *; rcases h with h | h; exact h; exact Or.inr (Or.inr h))⟩
    refine (TSim.steps st0 (TSim.bind p1 rest)).of_eq rfl ?_ ?_ ?_ ?_
    · unfold chainK; subst he; simp only [Nat.zero_add]; omega
    · unfold chainCy; subst he; simp only [Nat.zero_add]; omega
    all_goals simp only [sumTo_const]
    all_goals subst he; omega
end loop
end SigGolfCandidate.T3M.Sign.Seed

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000
abbrev buffer (lay chain step : Nat) : Nat := 0x6e000 + 8192 * lay + 128 * chain + 16 * step
def copyCode : List (BitVec 32) := [0x6ee37,0xe0e13,0xd41393,0x7e0e33,0x799393,0x7e0e33,0x4a1393,0x7e0e33,0x20eb7,0x1d0e8e93,0xeb303,0x8eb383,0x6e3023,0x7e3423]
sym_block prefix_copy := symRun { noAlias := true } copyCode (pcOf 22032) 100
theorem buffer_bounds {lay chain step : Nat} (hl : 1 ≤ lay) (hh : lay ≤ 3)
    (hc : chain < 43) (hs : step < 8) :
    0x70000 ≤ buffer lay chain step ∧ buffer lay chain step + 16 ≤ 0x75580 ∧
    buffer lay chain step % 8 = 0 := by
  simp only [buffer]
  omega

theorem copy_steps {im : Image} (hc : CodeAt im (pcOf 22032) copyCode)
    (s : MachineState) (hp : s.pc = pcOf 22032) (lay chain step : Nat)
    (hl : 1 ≤ lay) (hh : lay ≤ 3) (hj : chain < 43) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 chain)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    ∃ t, Steps im s 14 14 t ∧ t.pc = pcOf 22046 ∧
      t.getMem (BitVec.ofNat 64 (buffer lay chain step)) = s.getMem 0x201d0 ∧
      t.getMem (BitVec.ofNat 64 (buffer lay chain step + 8)) = s.getMem 0x201d8 ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = buffer lay chain step ∨ A = buffer lay chain step + 8) := by
  have hb := buffer_bounds hl hh hj hs
  have ho : Oblig.all s prefix_copy.res.st.obl := by
    simp only [prefix_copy.res]
    t3n [h8, h19, h20]
    omega
  refine ⟨_, symRun_sound prefix_copy hc s hp ho, ?_, ?_, ?_, ?_, ?_⟩
  · simp [prefix_copy.res, Result.toState_pc, E.eval, pcOf]
  · simp only [Result.toState_getMem, prefix_copy.res]
    t3n [h8, h19, h20, buffer]
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, prefix_copy.res]
    t3n [h8, h19, h20, buffer]
    rw [if_pos (by omega)]
  · intro r hr; simp at hr; cases r <;> simp_all [prefix_copy.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, prefix_copy.res]
    t3n [h8, h19, h20, buffer]
    simp only [buffer] at hn
    rw [if_neg (by omega), if_neg (by omega)]
#print axioms copy_steps
end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.Legacy.Riscv

/-- Bind the checked prefix copy to the installed Sign program. -/
theorem copy_codeAt : CodeAt Images.signImage (pcOf 22032) copyCode := by
  apply codeAt_sign_last <;> decide +kernel

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

def entryCode : List (BitVec 32) := [0x6040c63]

sym_block prefix_entry := symRun { noAlias := true } entryCode (pcOf 22016) 100

theorem entry_steps {im : Image} (hc : CodeAt im (pcOf 22016) entryCode)
    (s : MachineState) (hp : s.pc = pcOf 22016) :
    Steps im s 1 1 (prefix_entry.res.toState s) := by
  apply symRun_sound prefix_entry hc s hp
  simp [prefix_entry.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def loadIndexCode : List (BitVec 32) := [0x20e37,0x550e0e13,0xe3303,0xfff40393,0x38a63]

sym_block prefix_loadIndex := symRun { noAlias := true } loadIndexCode (pcOf 22017) 100

theorem loadIndex_steps {im : Image} (hc : CodeAt im (pcOf 22017) loadIndexCode)
    (s : MachineState) (hp : s.pc = pcOf 22017) :
    Steps im s 5 5 (prefix_loadIndex.res.toState s) := by
  apply symRun_sound prefix_loadIndex hc s hp
  simp [prefix_loadIndex.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def testLayer2Code : List (BitVec 32) := [0xffe40393,0x38c63]

sym_block prefix_testLayer2 := symRun { noAlias := true } testLayer2Code (pcOf 22022) 100

theorem testLayer2_steps {im : Image} (hc : CodeAt im (pcOf 22022) testLayer2Code)
    (s : MachineState) (hp : s.pc = pcOf 22022) :
    Steps im s 2 2 (prefix_testLayer2.res.toState s) := by
  apply symRun_sound prefix_testLayer2 hc s hp
  simp [prefix_testLayer2.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def select3Code : List (BitVec 32) := [0x3f37313,0x180006f]

sym_block prefix_select3 := symRun { noAlias := true } select3Code (pcOf 22024) 100

theorem select3_steps {im : Image} (hc : CodeAt im (pcOf 22024) select3Code)
    (s : MachineState) (hp : s.pc = pcOf 22024) :
    Steps im s 2 2 (prefix_select3.res.toState s) := by
  apply symRun_sound prefix_select3 hc s hp
  simp [prefix_select3.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def select1Code : List (BitVec 32) := [0xc35313,0x7f37313,0xc0006f]

sym_block prefix_select1 := symRun { noAlias := true } select1Code (pcOf 22026) 100

theorem select1_steps {im : Image} (hc : CodeAt im (pcOf 22026) select1Code)
    (s : MachineState) (hp : s.pc = pcOf 22026) :
    Steps im s 3 3 (prefix_select1.res.toState s) := by
  apply symRun_sound prefix_select1 hc s hp
  simp [prefix_select1.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def select2Code : List (BitVec 32) := [0x635313,0x3f37313]

sym_block prefix_select2 := symRun { noAlias := true } select2Code (pcOf 22029) 100

theorem select2_steps {im : Image} (hc : CodeAt im (pcOf 22029) select2Code)
    (s : MachineState) (hp : s.pc = pcOf 22029) :
    Steps im s 2 2 (prefix_select2.res.toState s) := by
  apply symRun_sound prefix_select2 hc s hp
  simp [prefix_select2.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def selectedCode : List (BitVec 32) := [0x3231e63]

sym_block prefix_selected := symRun { noAlias := true } selectedCode (pcOf 22031) 100

theorem selected_steps {im : Image} (hc : CodeAt im (pcOf 22031) selectedCode)
    (s : MachineState) (hp : s.pc = pcOf 22031) :
    Steps im s 1 1 (prefix_selected.res.toState s) := by
  apply symRun_sound prefix_selected hc s hp
  simp [prefix_selected.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def resumeCode : List (BitVec 32) := [0x11a0463]

sym_block prefix_resume := symRun { noAlias := true } resumeCode (pcOf 22046) 100

theorem resume_steps {im : Image} (hc : CodeAt im (pcOf 22046) resumeCode)
    (s : MachineState) (hp : s.pc = pcOf 22046) :
    Steps im s 1 1 (prefix_resume.res.toState s) := by
  apply symRun_sound prefix_resume hc s hp
  simp [prefix_resume.res, rv_simp, accessValid_iff, MEMORY_BYTES]


theorem entry_pc (s : MachineState) :
    (prefix_entry.res.toState s).pc =
      if s.getReg .x8 = 0 then pcOf 22046 else pcOf 22017 := by
  simp [Result.toState_pc, prefix_entry.res, E.eval, CmpOp.eval, pcOf]

theorem loadIndex_mem (s : MachineState) :
    (prefix_loadIndex.res.toState s).getReg .x6 = s.getMem 0x20550 := by
  simp [prefix_loadIndex.res, rv_simp]

theorem selected_pc (s : MachineState) :
    (prefix_selected.res.toState s).pc =
      if s.getReg .x6 = s.getReg .x18 then pcOf 22032 else pcOf 22046 := by
  simp [Result.toState_pc, prefix_selected.res, E.eval, CmpOp.eval, pcOf]

theorem resume_pc (s : MachineState) :
    (prefix_resume.res.toState s).pc =
      if s.getReg .x20 = s.getReg .x17 then pcOf 22048 else pcOf 22047 := by
  simp [Result.toState_pc, prefix_resume.res, E.eval, CmpOp.eval, pcOf]

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
structure GuardAt (im : Image) : Prop where
  entry : CodeAt im (pcOf 22016) entryCode
  loadIndex : CodeAt im (pcOf 22017) loadIndexCode
  testLayer2 : CodeAt im (pcOf 22022) testLayer2Code
  select3 : CodeAt im (pcOf 22024) select3Code
  select1 : CodeAt im (pcOf 22026) select1Code
  select2 : CodeAt im (pcOf 22029) select2Code
  selected : CodeAt im (pcOf 22031) selectedCode

def selectionWord (index : Word) (lay : Nat) : Word :=
  if lay = 1 then (index >>> (12 : Word)) &&& 127
  else if lay = 2 then (index >>> (6 : Word)) &&& 63 else index &&& 63

/-- Every valid lower-layer prefix guard reaches exactly the selected-leaf branch.
It costs at most eleven ordinary instructions and writes no memory. -/
theorem guard_steps {im : Image} (hc : GuardAt im) (s : MachineState)
    (hp : s.pc = pcOf 22016) (lay : Nat) (hl : 1 ≤ lay) (hh : lay ≤ 3)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ n t, n ≤ 11 ∧ Steps im s n n t ∧
      t.pc = (if selectionWord (s.getMem 0x20550) lay = s.getReg .x18
        then pcOf 22032 else pcOf 22046) ∧
      t.getReg .x6 = selectionWord (s.getMem 0x20550) lay ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun _ => False) := by
  interval_cases lay
  ·
    let t0 := prefix_entry.res.toState s
    have r0 := entry_steps hc.entry s hp
    let t1 := prefix_loadIndex.res.toState t0
    have p1 : t0.pc = pcOf 22017 := by simp [t0, prefix_entry.res, rv_simp, h8, pcOf]
    have r1 := loadIndex_steps hc.loadIndex t0 p1
    let t2 := prefix_select1.res.toState t1
    have p2 : t1.pc = pcOf 22026 := by simp [t0, t1, prefix_entry.res, prefix_loadIndex.res, rv_simp, h8, pcOf]
    have r2 := select1_steps hc.select1 t1 p2
    let t3 := prefix_selected.res.toState t2
    have p3 : t2.pc = pcOf 22031 := by simp [t0, t1, t2, prefix_entry.res, prefix_loadIndex.res, prefix_select1.res, rv_simp, h8, pcOf]
    have r3 := selected_steps hc.selected t2 p3
    refine ⟨10, t3, by decide, (((r0.trans r1).trans r2).trans r3), ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, t3, prefix_entry.res, prefix_loadIndex.res, prefix_select1.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
    · simp [t0, t1, t2, t3, prefix_entry.res, prefix_loadIndex.res, prefix_select1.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, t3, prefix_entry.res, prefix_loadIndex.res, prefix_select1.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord] <;> rfl
    · intro A hA hn; simp [t0, t1, t2, t3, prefix_entry.res, prefix_loadIndex.res, prefix_select1.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
  ·
    let t0 := prefix_entry.res.toState s
    have r0 := entry_steps hc.entry s hp
    let t1 := prefix_loadIndex.res.toState t0
    have p1 : t0.pc = pcOf 22017 := by simp [t0, prefix_entry.res, rv_simp, h8, pcOf]
    have r1 := loadIndex_steps hc.loadIndex t0 p1
    let t2 := prefix_testLayer2.res.toState t1
    have p2 : t1.pc = pcOf 22022 := by simp [t0, t1, prefix_entry.res, prefix_loadIndex.res, rv_simp, h8, pcOf]
    have r2 := testLayer2_steps hc.testLayer2 t1 p2
    let t3 := prefix_select2.res.toState t2
    have p3 : t2.pc = pcOf 22029 := by simp [t0, t1, t2, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, rv_simp, h8, pcOf]
    have r3 := select2_steps hc.select2 t2 p3
    let t4 := prefix_selected.res.toState t3
    have p4 : t3.pc = pcOf 22031 := by simp [t0, t1, t2, t3, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select2.res, rv_simp, h8, pcOf]
    have r4 := selected_steps hc.selected t3 p4
    refine ⟨11, t4, by decide, ((((r0.trans r1).trans r2).trans r3).trans r4), ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select2.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
    · simp [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select2.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select2.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord] <;> rfl
    · intro A hA hn; simp [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select2.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
  ·
    let t0 := prefix_entry.res.toState s
    have r0 := entry_steps hc.entry s hp
    let t1 := prefix_loadIndex.res.toState t0
    have p1 : t0.pc = pcOf 22017 := by simp [t0, prefix_entry.res, rv_simp, h8, pcOf]
    have r1 := loadIndex_steps hc.loadIndex t0 p1
    let t2 := prefix_testLayer2.res.toState t1
    have p2 : t1.pc = pcOf 22022 := by simp [t0, t1, prefix_entry.res, prefix_loadIndex.res, rv_simp, h8, pcOf]
    have r2 := testLayer2_steps hc.testLayer2 t1 p2
    let t3 := prefix_select3.res.toState t2
    have p3 : t2.pc = pcOf 22024 := by simp [t0, t1, t2, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, rv_simp, h8, pcOf]
    have r3 := select3_steps hc.select3 t2 p3
    let t4 := prefix_selected.res.toState t3
    have p4 : t3.pc = pcOf 22031 := by simp [t0, t1, t2, t3, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select3.res, rv_simp, h8, pcOf]
    have r4 := selected_steps hc.selected t3 p4
    refine ⟨11, t4, by decide, ((((r0.trans r1).trans r2).trans r3).trans r4), ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select3.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
    · simp [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select3.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select3.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord] <;> rfl
    · intro A hA hn; simp [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select3.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

def resumeMissWord : BitVec 32 := 4153323631
def resumeHitWord : BitVec 32 := 4123963503

sym_block prefix_resumeMiss := symRun { noAlias := true } [resumeMissWord] (pcOf 22047) 10
sym_block prefix_resumeHit := symRun { noAlias := true } [resumeHitWord] (pcOf 22048) 10

/-- Return to the original chain branch with no additional HASH or memory write. -/
theorem resume_full_steps {im : Image}
    (hc : CodeAt im (pcOf 22046) resumeCode)
    (hm : CodeAt im (pcOf 22047) [resumeMissWord])
    (hh : CodeAt im (pcOf 22048) [resumeHitWord])
    (s : MachineState) (hp : s.pc = pcOf 22046) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if s.getReg .x20 = s.getReg .x17 then pcOf 1015 else pcOf 1021) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  let u := prefix_resume.res.toState s
  have first := resume_steps hc s hp
  have hpc : u.pc = if s.getReg .x20 = s.getReg .x17 then pcOf 22048 else pcOf 22047 := resume_pc s
  by_cases he : s.getReg .x20 = s.getReg .x17
  · rw [if_pos he] at hpc ⊢
    have last := symRun_sound prefix_resumeHit hh u hpc (by simp [prefix_resumeHit.res, rv_simp])
    refine ⟨prefix_resumeHit.res.toState u, first.trans last, ?_, ?_, ?_⟩
    · simp [prefix_resumeHit.res, rv_simp, pcOf]
    · intro r hr; cases r <;> simp [u, prefix_resume.res, prefix_resumeHit.res, rv_simp] <;> rfl
    · intro A hA hn; simp [u, prefix_resume.res, prefix_resumeHit.res, rv_simp]
  · rw [if_neg he] at hpc ⊢
    have last := symRun_sound prefix_resumeMiss hm u hpc (by simp [prefix_resumeMiss.res, rv_simp])
    refine ⟨prefix_resumeMiss.res.toState u, first.trans last, ?_, ?_, ?_⟩
    · simp [prefix_resumeMiss.res, rv_simp, pcOf]
    · intro r hr; cases r <;> simp [u, prefix_resume.res, prefix_resumeMiss.res, rv_simp] <;> rfl
    · intro A hA hn; simp [u, prefix_resume.res, prefix_resumeMiss.res, rv_simp]

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Preserve each selected lower-chain prefix and resume the original branch.
The extra storage is disjoint from all original producer buffers. -/
theorem prefix_steps {im : Image} (hg : GuardAt im)
    (hc : CodeAt im (pcOf 22032) copyCode)
    (hr : CodeAt im (pcOf 22046) resumeCode)
    (hm : CodeAt im (pcOf 22047) [resumeMissWord])
    (hhit : CodeAt im (pcOf 22048) [resumeHitWord])
    (s : MachineState) (hp : s.pc = pcOf 22016) (lay chain step : Nat)
    (hl : 1 ≤ lay) (hh : lay ≤ 3) (hj : chain < 43) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 chain)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    ∃ n t, n ≤ 27 ∧ Steps im s n n t ∧
      t.pc = (if s.getReg .x20 = s.getReg .x17 then pcOf 1015 else pcOf 1021) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = buffer lay chain step ∨ A = buffer lay chain step + 8) ∧
      (selectionWord (s.getMem 0x20550) lay = s.getReg .x18 →
        t.getMem (BitVec.ofNat 64 (buffer lay chain step)) = s.getMem 0x201d0 ∧
        t.getMem (BitVec.ofNat 64 (buffer lay chain step + 8)) = s.getMem 0x201d8) := by
  obtain ⟨n,u,hn,gu,upc,u6,ur,uf⟩ := guard_steps hg s hp lay hl hh h8
  by_cases selected : selectionWord (s.getMem 0x20550) lay = s.getReg .x18
  · rw [if_pos selected] at upc
    obtain ⟨v,cv,vpc,v0,v8,vr,vf⟩ := copy_steps hc u upc lay chain step hl hh hj hs
      (by rw [ur.get (by decide)]; exact h8)
      (by rw [ur.get (by decide)]; exact h19)
      (by rw [ur.get (by decide)]; exact h20)
    obtain ⟨t,rt,tpc,tr,tf⟩ := resume_full_steps hr hm hhit v vpc
    have v20 : v.getReg .x20 = s.getReg .x20 := (vr.get (by decide)).trans (ur.get (by decide))
    have v17 : v.getReg .x17 = s.getReg .x17 := (vr.get (by decide)).trans (ur.get (by decide))
    rw [v20,v17] at tpc
    refine ⟨n+16,t,by omega,gu.trans (cv.trans rt),tpc,?_,?_,?_⟩
    · exact ((ur.trans vr).trans tr).mono (by decide)
    · exact ((uf.trans vf).trans tf).mono (by intro A hA h; simpa using h)
    · intro _
      constructor
      · rw [tf _ (by have := buffer_bounds hl hh hj hs; omega) (by simp),v0]
        exact uf 0x201d0 (by decide) (by simp)
      · rw [tf _ (by have := buffer_bounds hl hh hj hs; omega) (by simp),v8]
        exact uf 0x201d8 (by decide) (by simp)
  · rw [if_neg selected] at upc
    obtain ⟨t,rt,tpc,tr,tf⟩ := resume_full_steps hr hm hhit u upc
    rw [ur.get (r := .x20) (by decide),ur.get (r := .x17) (by decide)] at tpc
    refine ⟨n+2,t,by omega,gu.trans rt,tpc,?_,?_,fun h => (selected h).elim⟩
    · exact (ur.trans tr).mono (by decide)
    · exact (uf.trans tf).mono (by intro A hA h; simp at h)

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M

/-- Prefix storage identifies the layer, chain, step, and 64-bit half uniquely. -/
theorem buffer_word_injective {lay lay' chain chain' step step' half half' : Nat}
    (hc : chain < 43) (hc' : chain' < 43) (hs : step < 8) (hs' : step' < 8)
    (hh : half < 2) (hh' : half' < 2)
    (he : buffer lay chain step + 8 * half = buffer lay' chain' step' + 8 * half') :
    lay = lay' ∧ chain = chain' ∧ step = step' ∧ half = half' := by
  simp only [buffer] at he
  omega

/-- Every saved prefix lies above the original chain/FTS scratch regions. -/
theorem buffer_above_scratch {lay chain step half : Nat} (hl : 1 ≤ lay) :
    0x67000 < buffer lay chain step + 8 * half := by
  simp only [buffer]
  omega

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.Legacy.Riscv
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every prefix-retention fragment is present in the executable Sign image. -/
theorem installed_guardAt : GuardAt Images.signImage := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> apply codeAt_sign_last <;> decide +kernel

theorem installed_resume : CodeAt Images.signImage (pcOf 22046) resumeCode := by
  apply codeAt_sign_last <;> decide +kernel

theorem installed_resumeMiss : CodeAt Images.signImage (pcOf 22047) [resumeMissWord] := by
  apply codeAt_sign_last <;> decide +kernel

theorem installed_resumeHit : CodeAt Images.signImage (pcOf 22048) [resumeHitWord] := by
  apply codeAt_sign_last <;> decide +kernel

theorem installed_prefixHook : CodeAt Images.signImage (pcOf 1014) [43073647] := by
  apply codeAt_sign_current_slice <;> decide +kernel

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000

sym_block prefix_hook := symRun { noAlias := true } [43073647] (pcOf 1014) 100

theorem hook_steps {im : Image} (hc : CodeAt im (pcOf 1014) [43073647])
    (s : MachineState) (hp : s.pc = pcOf 1014) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 22016 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound prefix_hook hc s hp (by simp [prefix_hook.res,rv_simp]),?_,?_,?_⟩
  · simp [prefix_hook.res, Result.toState_pc, E.eval, pcOf]
  · intro r hr; cases r <;> simp [prefix_hook.res, rv_simp] <;> rfl
  · intro A hA hn; simp [prefix_hook.res, rv_simp]

/-- The top tree takes the guard's constant-time skip path without memory writes. -/
theorem top_steps {im : Image} (hg : GuardAt im)
    (hr : CodeAt im (pcOf 22046) resumeCode)
    (hm : CodeAt im (pcOf 22047) [resumeMissWord])
    (hhit : CodeAt im (pcOf 22048) [resumeHitWord])
    (s : MachineState) (hp : s.pc = pcOf 22016) (h8 : s.getReg .x8 = 0) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if s.getReg .x20 = s.getReg .x17 then pcOf 1015 else pcOf 1021) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have st := entry_steps hg.1 s hp
  have ep : (prefix_entry.res.toState s).pc = pcOf 22046 := by rw [entry_pc, if_pos h8]
  obtain ⟨t,rt,tpc,tr,tf⟩ := resume_full_steps hr hm hhit _ ep
  have er : RegsExcept s (prefix_entry.res.toState s) [] := by
    intro r hr; cases r <;> simp [prefix_entry.res,rv_simp] <;> rfl
  have ef : Frame s (prefix_entry.res.toState s) (fun _ => False) := by
    intro A hA hn; simp [prefix_entry.res,rv_simp]
  rw [er.get (r := .x20) (by simp), er.get (r := .x17) (by simp)] at tpc
  exact ⟨t,st.trans rt,tpc,er.trans tr,(ef.trans tf).mono (by simp)⟩

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- The hooked lower-tree boundary saves the exact current chain value and
resumes the original branch. All additional instructions have unit tariff. -/
theorem hooked_steps {im : Image} (h0 : CodeAt im (pcOf 1014) [43073647])
    (hg : GuardAt im) (hc : CodeAt im (pcOf 22032) copyCode)
    (hr : CodeAt im (pcOf 22046) resumeCode)
    (hm : CodeAt im (pcOf 22047) [resumeMissWord])
    (hhit : CodeAt im (pcOf 22048) [resumeHitWord])
    (s : MachineState) (hp : s.pc = pcOf 1014) (lay chain step : Nat)
    (hl : 1 ≤ lay) (hh : lay ≤ 3) (hj : chain < 43) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 chain)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    ∃ n t, n ≤ 28 ∧ Steps im s n n t ∧
      t.pc = (if s.getReg .x20 = s.getReg .x17 then pcOf 1015 else pcOf 1021) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = buffer lay chain step ∨ A = buffer lay chain step + 8) ∧
      (selectionWord (s.getMem 0x20550) lay = s.getReg .x18 →
        t.getMem (BitVec.ofNat 64 (buffer lay chain step)) = s.getMem 0x201d0 ∧
        t.getMem (BitVec.ofNat 64 (buffer lay chain step + 8)) = s.getMem 0x201d8) := by
  obtain ⟨u,hu,upc,ur,uf⟩ := hook_steps h0 s hp
  obtain ⟨n,t,hn,ht,tpc,tr,tf,hval⟩ := prefix_steps hg hc hr hm hhit u upc lay chain step
    hl hh hj hs (by rw [ur.get (by simp)]; exact h8)
    (by rw [ur.get (by simp)]; exact h19) (by rw [ur.get (by simp)]; exact h20)
  rw [ur.get (r := .x20) (by simp),ur.get (r := .x17) (by simp)] at tpc
  refine ⟨1+n,t,by omega,hu.trans ht,tpc,(ur.trans tr).mono (by simp),?_,?_⟩
  · exact (uf.trans tf).mono (by intro A hA h; simpa using h)
  · intro h
    have hindex : u.getMem 0x20550 = s.getMem 0x20550 := uf 0x20550 (by decide) (by simp)
    rw [hindex,ur.get (r := .x18) (by simp)] at hval
    obtain ⟨hlo,hhi⟩ := hval h
    exact ⟨hlo.trans (uf 0x201d0 (by decide) (by simp)),
      hhi.trans (uf 0x201d8 (by decide) (by simp))⟩

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedHeader
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
structure Code (im : Image) : Prop where
  entry : CodeAt im (pcOf 1022) sign_entry
  layer0 : CodeAt im (pcOf 1483) sign_layer0
  layer1 : CodeAt im (pcOf 1485) sign_layer1
  layer23 : CodeAt im (pcOf 1487) sign_layer23
  inc : CodeAt im (pcOf 1488) sign_inc
  body : CodeAt im (pcOf 1489) sign_body
  store : CodeAt im (pcOf 1028) sign_store
theorem steps_sign_entry {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1022) :
    Steps im s 1 1 (run_sign_entry.res.toState s) := by
  exact symRun_sound run_sign_entry hc.entry s hpc (by simp [run_sign_entry.res, rv_simp])
theorem steps_sign_layer0 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1483) :
    Steps im s 2 2 (run_sign_layer0.res.toState s) := by
  exact symRun_sound run_sign_layer0 hc.layer0 s hpc (by simp [run_sign_layer0.res, rv_simp])
theorem steps_sign_layer1 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1485) :
    Steps im s 2 2 (run_sign_layer1.res.toState s) := by
  exact symRun_sound run_sign_layer1 hc.layer1 s hpc (by simp [run_sign_layer1.res, rv_simp])
theorem steps_sign_layer23 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1487) :
    Steps im s 2 2 (run_sign_layer23.res.toState s) := by
  exact symRun_sound run_sign_layer23 hc.layer23 s hpc (by simp [run_sign_layer23.res, rv_simp])
theorem steps_sign_inc {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1488) :
    Steps im s 1 1 (run_sign_inc.res.toState s) := by
  exact symRun_sound run_sign_inc hc.inc s hpc (by simp [run_sign_inc.res, rv_simp])
theorem steps_sign_body {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1489) :
    Steps im s 19 19 (run_sign_body.res.toState s) := by
  exact symRun_sound run_sign_body hc.body s hpc (by simp [run_sign_body.res, rv_simp])
theorem steps_sign_store {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1028) :
    Steps im s 3 3 (run_sign_store.res.toState s) := by
  exact symRun_sound run_sign_store hc.store s hpc (by simp [run_sign_store.res, rv_simp])
theorem sign_header_0 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 0#64) :
    ∃ t, Steps im s 25 25 t ∧ t.pc = pcOf 1031 ∧ SignHeaderPost s t 12 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry hc s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 hc s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_body.res.toState s1
  have h2 := steps_sign_body hc s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_store.res.toState s2
  have h3 := steps_sign_store hc s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, rv_simp, h8])
  refine ⟨s3, (((h0.trans h1).trans h2).trans h3), ?_, ?_⟩
  · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp]
  · constructor
    · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp, packedAt, routedAt]
    · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp, routedAt]
    · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem sign_header_1 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 1#64) :
    ∃ t, Steps im s 28 28 t ∧ t.pc = pcOf 1031 ∧ SignHeaderPost s t 7 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry hc s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 hc s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_layer1.res.toState s1
  have h2 := steps_sign_layer1 hc s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_inc.res.toState s2
  have h3 := steps_sign_inc hc s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, rv_simp, h8])
  let s4 := run_sign_body.res.toState s3
  have h4 := steps_sign_body hc s3 (by simp [s0, s1, s2, s3, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, rv_simp, h8])
  let s5 := run_sign_store.res.toState s4
  have h5 := steps_sign_store hc s4 (by simp [s0, s1, s2, s3, s4, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem sign_header_2 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 2#64) :
    ∃ t, Steps im s 29 29 t ∧ t.pc = pcOf 1031 ∧ SignHeaderPost s t 6 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry hc s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 hc s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_layer1.res.toState s1
  have h2 := steps_sign_layer1 hc s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_layer23.res.toState s2
  have h3 := steps_sign_layer23 hc s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, rv_simp, h8])
  let s4 := run_sign_body.res.toState s3
  have h4 := steps_sign_body hc s3 (by simp [s0, s1, s2, s3, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, rv_simp, h8])
  let s5 := run_sign_store.res.toState s4
  have h5 := steps_sign_store hc s4 (by simp [s0, s1, s2, s3, s4, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem sign_header_3 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 3#64) :
    ∃ t, Steps im s 29 29 t ∧ t.pc = pcOf 1031 ∧ SignHeaderPost s t 6 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry hc s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 hc s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_layer1.res.toState s1
  have h2 := steps_sign_layer1 hc s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_layer23.res.toState s2
  have h3 := steps_sign_layer23 hc s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, rv_simp, h8])
  let s4 := run_sign_body.res.toState s3
  have h4 := steps_sign_body hc s3 (by simp [s0, s1, s2, s3, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, rv_simp, h8])
  let s5 := run_sign_store.res.toState s4
  have h5 := steps_sign_store hc s4 (by simp [s0, s1, s2, s3, s4, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem header {im : Image} (hc : Code im) (s : MachineState)
    (hp : s.pc = pcOf 1022) (lay : SigGolfCandidate.T3.Layer)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) :
    ∃ t, Steps im s (headerK lay - 5) (headerK lay - 5) t ∧ t.pc = pcOf 1031 ∧
      SignHeaderPost s t (SigGolfCandidate.T3.height lay) := by
  fin_cases lay
  · exact sign_header_0 hc s hp h8
  · exact sign_header_1 hc s hp h8
  · exact sign_header_2 hc s hp h8
  · exact sign_header_3 hc s hp h8
#print axioms header
end ClaudeWCT.W9.Machine.Sign.SharedHeader

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest chainInput chain shortHash header pad64 zero16 height chainHeader)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
/-- The chain code of the installed producer. Pairing stage 1: the header ends at 1030 and 1031 jumps to the G/F step
block (`Seed.StepCode`: block 1732..1757, HASH at 1748/1756, the C3 tail trampoline 1667..1677). -/
structure Code (im : Image) : Prop where
  reset : CodeAt im (pcOf 1013) sub_0
  capCopy : CodeAt im (pcOf 1015) sub_2
  stop : CodeAt im (pcOf 1021) sub_8
  ret : CodeAt im (pcOf 1039) sub_26
  step : SigGolfCandidate.T3M.Sign.Seed.StepCode im
  header : SharedHeader.Code im
theorem sub0_spec {image : Image} (h : Code image) (s : MachineState)
    (hpc : s.pc = pcOf (1013 + 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (1013 + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_0 (b := 1013) (Or.inr rfl)
  refine ⟨_, symRun_sound hrun h.reset s hpc (by simp [st_0, blk117_0.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_0, Result.toState_pc, E.eval]
  · simp [st_0, blk117_0.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_0, blk117_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_0, blk117_0.res, rv_simp]

theorem sub2_spec {image : Image} (h : Code image) (s : MachineState)
    (hpc : s.pc = pcOf (1013 + 2)) (valp : Nat) (h23 : s.getReg .x23 = BitVec.ofNat 64 valp)
    (hv8 : valp % 8 = 0) (hv : valp + 16 ≤ 2 ^ 24) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (1013 + 8) ∧
      t.getMem (BitVec.ofNat 64 valp) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (valp + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x29] ∧ Frame s t (fun A => A = valp ∨ A = valp + 8) := by
  have hrun := run_2 (b := 1013) (Or.inr rfl)
  have hobl : Oblig.all s st_2.obl := by
    simp only [st_2, blk117_2.res]
    t3n [h23]
    omega
  refine ⟨_, symRun_sound hrun h.capCopy s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
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

theorem sub8_spec {image : Image} (h : Code image) (s : MachineState)
    (hpc : s.pc = pcOf (1013 + 8)) (m e : Nat) (hm : m < 2 ^ 64) (he : e < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h21 : s.getReg .x21 = BitVec.ofNat 64 e) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if m = e then pcOf (1013 + 26) else pcOf (1013 + 9)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_8 (b := 1013) (Or.inr rfl)
  refine ⟨_, symRun_sound hrun h.stop s hpc (by simp [st_8, blk117_8.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_8, rebase, blk117_8.res, E.eval, CmpOp.eval, h20, h21]
    by_cases hme : m = e
    · subst hme; simp
    · rw [if_neg hme]
      have : BitVec.ofNat 64 m ≠ BitVec.ofNat 64 e := fun he' => hme ((ofNat_inj hm he).mp he')
      simp [this]
  · intro r hr; cases r <;> simp_all [st_8, blk117_8.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_8, blk117_8.res, rv_simp]

theorem sub26_spec {image : Image} (h : Code image) (s : MachineState)
    (hpc : s.pc = pcOf (1013 + 26)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_26 (b := 1013) (Or.inr rfl)
  refine ⟨_, symRun_sound hrun h.ret s hpc (by simp [st_26, blk117_26.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_26, blk117_26.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_26, blk117_26.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_26, blk117_26.res, rv_simp]


theorem shared_header_source {image : Image} (h : Code image)
    (s : MachineState) (hpc : s.pc = pcOf (1013 + 9)) (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ height lay)
    (hi : i < 64) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    ∃ t, Steps image s (headerK lay - 5) (headerK lay - 5) t ∧ t.pc = pcOf (1013 + 18) ∧
      t.getReg .x28 = BitVec.ofNat 64 0x201A0 ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 16)) = (chainHeader lay tree leaf i step).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = (chainHeader lay tree leaf i step).extractLsb' 64 64 ∧
      RegsExcept s t [.x6, .x7, .x28, .x30] ∧
      Frame s t (fun A => A = 0x201A0 + 16 ∨ A = 0x201A0 + 24) := by
  obtain ⟨t, st, pc, post⟩ := SharedHeader.header h.header s hpc lay h8
  refine ⟨t, st, pc, post.x28,
    post.low.trans (packedAt_source s lay tree leaf i step hr hf hi hs h8 h9 h18 h19 h20),
    ?_, post.regs, post.frame⟩
  exact (post.high.trans (routedAt_high_zero s lay tree leaf hr h9 h18)).trans
    (source_high_actual lay tree leaf i step hr hf hi hs).symm

#print axioms shared_header_source
#print axioms sub2_spec
end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3M.Sign SigGolfCandidate.Rv
/-- The chain instructions (stage 2: with the C3 tail trampoline) and domain header occur in the installed
producer. -/
theorem installed_code : Code Images.signImage := by
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> (apply codeAt_sign_current_slice <;> decide +kernel)
end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

structure PrefixCode (im : Image) : Prop where
  hook : CodeAt im (pcOf 1014) [43073647]
  guard : SharedPrefixes.GuardAt im
  copy : CodeAt im (pcOf 22032) SharedPrefixes.copyCode
  resume : CodeAt im (pcOf 22046) SharedPrefixes.resumeCode
  miss : CodeAt im (pcOf 22047) [SharedPrefixes.resumeMissWord]
  hit : CodeAt im (pcOf 22048) [SharedPrefixes.resumeHitWord]

def boundaryWrites (lay chain step valp A : Nat) : Prop :=
  A = SharedPrefixes.buffer lay chain step ∨ A = SharedPrefixes.buffer lay chain step + 8 ∨
  A = valp ∨ A = valp + 8

/-- Each lower-chain boundary preserves its prefix before the old capture branch.
Its new instructions do not call HASH; all memory writes are explicit.
Stage 2: the cost is split as `28` plus the capture store (`6`, only at `step = cap`), so that the C3 tail
trampoline fits the unchanged chain budget `80 * e + 37` (`loopW_le`). -/
theorem boundary {im : Image} (hc : Code im) (hpref : PrefixCode im)
    (s : MachineState) (hp : s.pc = pcOf 1014) (lay chain step valp cap : Nat)
    (hl : 1 ≤ lay) (hh : lay ≤ 3) (hj : chain < 43) (hs : step < 8) (hcap : cap < 2 ^ 64)
    (hv8 : valp % 8 = 0) (hv : valp + 16 ≤ 0x67000)
    (hvc : valp + 16 ≤ CHAIN ∨ CHAIN + 80 ≤ valp)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 cap)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 chain)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 valp) (v : Digest)
    (hval : DigAt s (CHAIN + 48) v) :
    ∃ n t, n ≤ 28 + (if step = cap then 6 else 0) ∧ Steps im s n n t ∧ t.pc = pcOf 1021 ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (boundaryWrites lay chain step valp) ∧
      DigAt t (CHAIN + 48) v ∧
      (SharedPrefixes.selectionWord (s.getMem 0x20550) lay = s.getReg .x18 →
        DigAt t (SharedPrefixes.buffer lay chain step) v) := by
  obtain ⟨n,u,hn,hu,upc,ur,uf,usave⟩ := SharedPrefixes.hooked_steps
    hpref.hook hpref.guard hpref.copy hpref.resume hpref.miss hpref.hit s hp lay chain step
    hl hh hj hs h8 h19 h20
  have hb := SharedPrefixes.buffer_bounds hl hh hj hs
  have hba := SharedPrefixes.buffer_above_scratch (chain := chain) (step := step) (half := 0) hl
  simp only [Nat.mul_zero, Nat.add_zero] at hba
  have uv : DigAt u (CHAIN + 48) v := hval.frame uf (by decide)
    (by dsimp [CHAIN]; omega) (by dsimp [CHAIN]; omega)
  have saved : SharedPrefixes.selectionWord (s.getMem 0x20550) lay = s.getReg .x18 →
      DigAt u (SharedPrefixes.buffer lay chain step) v := by
    intro hh
    obtain ⟨h0,h8⟩ := usave hh
    exact ⟨h0.trans hval.1,h8.trans hval.2⟩
  by_cases hcap' : s.getReg .x20 = s.getReg .x17
  · rw [if_pos hcap'] at upc
    have hsc : step = cap := (ofNat_inj (by omega) hcap).mp (h20.symm.trans (hcap'.trans h17))
    obtain ⟨t,ht,tpc,t0,t8,tr,tf⟩ := sub2_spec hc u upc valp
      (by rw [ur.get (by decide)]; exact h23) hv8 (by omega)
    refine ⟨n+6,t,by rw [if_pos hsc]; omega,hu.trans ht,tpc,(ur.trans tr).mono (by decide),?_,?_,?_⟩
    · exact (uf.trans tf).mono (by intro A hA h; simp only [boundaryWrites]; tauto)
    · exact uv.frame tf (by decide) (by omega) (by omega)
    · intro hsel
      exact (saved hsel).frame tf (by omega) (by omega) (by omega)
  · rw [if_neg hcap'] at upc
    exact ⟨n,u,by split <;> omega,hu,upc,ur,uf.mono (by
      intro A hA h; simp only [boundaryWrites]; tauto),uv,saved⟩

#print axioms boundary
end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest chainInput shortHash pad64)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def hashWrites (A : Nat) : Prop :=
  (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112)

/-- The HASH rung follows prefix retention with its exact chain query. Pairing stage 1: the header, then the G/F step
block (`Seed.pair_rung`, `Seed.trX` extra steps); the rung keeps the half `WCT9.chainHigh lay i m` of
`WCT9.chainInputW`. -/
theorem hash_rung {im : Image} (hc : Code im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc = pcOf 1021) (lay : Layer)
    (tree leaf i m e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret) (hm : m < e)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (hval : DigAt s (CHAIN + 48) v) :
    TSim im sk s (headerK lay + 4 + SigGolfCandidate.T3M.Sign.Seed.trX lay.val i m)
      (headerK lay + 11 + SigGolfCandidate.T3M.Sign.Seed.trX lay.val i m) 1 1
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m) (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v))
      (fun v' t => t.pc = pcOf 1014 ∧ t.getReg .x20 = BitVec.ofNat 64 (m+1) ∧
        DigAt t (CHAIN + 48) v' ∧ RegsExcept s t chainRegs ∧ Frame s t hashWrites ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → SigGolfCandidate.T3M.Sign.Seed.Z32 t ∧
          Frame s t (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ A = CHAIN + 32 ∨ A = CHAIN + 40 ∨
            (CHAIN + 48 ≤ A ∧ A < CHAIN + 80)))) := by
  have he := hpre.he
  obtain ⟨u,hu,upc,ur,uf⟩ := sub8_spec hc s hp m e (by omega) (by omega) h20 hpre.x21
  rw [if_neg (by omega)] at upc
  obtain ⟨t,ht,tpc,t28,t16,t24,tr,tf⟩ := shared_header_source hc u upc lay tree leaf i m
    hpre.hroute hpre.hleaf hpre.hi (by omega)
    (by rw [ur.get (by simp)]; exact hpre.x8)
    (by rw [ur.get (by simp)]; exact hpre.x9)
    (by rw [ur.get (by simp)]; exact hpre.x18)
    (by rw [ur.get (by simp)]; exact hpre.x19)
    (by rw [ur.get (by simp)]; exact h20)
  have fr : Frame s t (fun A => A = CHAIN+16 ∨ A = CHAIN+24) :=
    (uf.trans tf).mono (by intro A hA h; simpa only [false_or] using h)
  have regs : RegsExcept s t [.x6,.x7,.x28,.x30] := (ur.trans tr).mono (by simp)
  have tv := hval.frame fr (by decide) (by simp) (by simp)
  have run := SigGolfCandidate.T3M.Sign.Seed.pair_rung hc.step sk t (by rw [tpc]) lay tree leaf i m v
    hpre.hi (by omega) (fun hl => by have := hpre.hlow hl; omega)
    (by rw [regs.get (by simp)]; exact hpre.x5) (by rw [regs.get (by simp)]; exact hpre.x8)
    (by rw [regs.get (by simp)]; exact hpre.x19) (by rw [regs.get (by simp)]; exact h20) t28
    (by rw [fr.get (by decide) (by simp only [CHAIN]; omega)]; exact hpre.z0)
    (by rw [fr.get (by decide) (by simp only [CHAIN]; omega)]; exact hpre.z8)
    t16 t24 (source_high_actual lay tree leaf i m hpre.hroute hpre.hleaf hpre.hi (by omega)) tv
  refine ((TSim.steps (hu.trans ht) run).of_eq rfl ?_ ?_ rfl rfl).mono ?_
  · unfold headerK; split_ifs <;> omega
  · unfold headerK; split_ifs <;> omega
  · intro v' w hw
    exact ⟨hw.1, hw.2.1, hw.2.2.1, (regs.trans hw.2.2.2.1).mono (by simp [chainRegs]),
      (fr.trans hw.2.2.2.2.1).mono (by
        intro A hA h; simp only [hashWrites]; rcases h with h | h
        · exact Or.inl h
        · exact Or.inr h), fun hF => by
        obtain ⟨z1, z2, zf⟩ := hw.2.2.2.2.2 hF
        exact ⟨⟨z1, z2⟩, (fr.trans zf).mono (fun A _ h => by
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr h)⟩⟩

#print axioms hash_rung
end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open SigGolfCandidate.T3M
/-- Every prefix-retention block is bound to the installed Sign image. -/
theorem installed_prefix_code : PrefixCode Images.signImage :=
  ⟨SharedPrefixes.installed_prefixHook, SharedPrefixes.installed_guardAt,
    SharedPrefixes.copy_codeAt, SharedPrefixes.installed_resume,
    SharedPrefixes.installed_resumeMiss, SharedPrefixes.installed_resumeHit⟩
end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer)

/-- Prefix storage is above all chain-domain padding, so the chain precondition
survives every complete rung and the optional capture store. -/
theorem pre_preserved {s t : MachineState} {lay : Layer} {tree leaf i cap e valp ret : Nat}
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hr : RegsExcept s t chainRegs)
    (hf : Frame s t (fun A => ChainWS valp A ∨ 0x67000 < A)) :
    ChainPreS t lay tree leaf i cap e valp ret := by
  have hvc := hpre.hvc
  simp only [CHAIN] at hvc
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,hpre.htree,hpre.hi,hpre.hroute,hpre.hleaf,
    hpre.hcap,hpre.he,hpre.hlow,hpre.hv8,hpre.hv,hpre.hvc,?_,?_⟩
  · exact (hr.get (by decide)).trans hpre.x5
  · exact (hr.get (by decide)).trans hpre.x1
  · exact (hr.get (by decide)).trans hpre.x8
  · exact (hr.get (by decide)).trans hpre.x9
  · exact (hr.get (by decide)).trans hpre.x18
  · exact (hr.get (by decide)).trans hpre.x17
  · exact (hr.get (by decide)).trans hpre.x19
  · exact (hr.get (by decide)).trans hpre.x21
  · exact (hr.get (by decide)).trans hpre.x23
  · exact (hf _ (by decide) (by simp only [ChainWS,CHAIN]; omega)).trans hpre.z0
  · exact (hf _ (by decide) (by simp only [ChainWS,CHAIN]; omega)).trans hpre.z8

#print axioms pre_preserved
end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest chainInput shortHash)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def rungWrites (lay i m valp A : Nat) : Prop :=
  ChainWS valp A ∨ A = SharedPrefixes.buffer lay i m ∨ A = SharedPrefixes.buffer lay i m + 8

/-- Stage 2: cycle bound of one lower rung `m`: boundary `28` (+ the capture store `6` at `m = cap`), header
`headerK ≤ 34`, the HASH `11`, and the C3 tail trampoline `Seed.trX`. -/
def rungW (lay i cap m : Nat) : Nat :=
  73 + SigGolfCandidate.T3M.Sign.Seed.trX lay i m + (if m = cap then 6 else 0)

/-- Stage 2: cycle bound of the rungs `m .. m + count - 1` and the exit (`30`, + the capture store at `cap`). -/
def loopW (lay i cap : Nat) : Nat → Nat → Nat
  | m, 0 => 30 + (if m = cap then 6 else 0)
  | m, count + 1 => rungW lay i cap m + loopW lay i cap (m + 1) count

/-- Pairing stage 1: the largest `Seed.trX` per step (G interior `11`; chain 0 of a lower layer at step 6: `14`). -/
def trXmax (m : Nat) : Nat := if m = 6 then 14 else 11

theorem trX_le_max (lay i m : Nat) : SigGolfCandidate.T3M.Sign.Seed.trX lay i m ≤ trXmax m := by
  unfold SigGolfCandidate.T3M.Sign.Seed.trX SigGolfCandidate.T3M.Sign.Seed.trX0 trXmax
  split_ifs <;> omega

def loopWmax (cap : Nat) : Nat → Nat → Nat
  | m, 0 => 30 + (if m = cap then 6 else 0)
  | m, count + 1 => 73 + trXmax m + (if m = cap then 6 else 0) + loopWmax cap (m + 1) count

theorem loopW_le_max (lay i cap : Nat) : ∀ count m, loopW lay i cap m count ≤ loopWmax cap m count
  | 0, _ => le_refl _
  | count + 1, m => by
    have h1 := trX_le_max lay i m
    have h2 := loopW_le_max lay i cap count (m + 1)
    simp only [loopW, loopWmax, rungW]
    omega

theorem loopW_worst : ∀ e, e < 9 → ∀ cap, cap ≤ e → 1 + loopWmax cap 0 e ≤ 85 * e + 37 := by
  decide +kernel

/-- Pairing stage 1: the G/F step block, the C3 trampoline and the capture store fit the chain budget `85 * e + 37`
(was `80 * e + 37`). -/
theorem loopW_le (lay i cap e : Nat) (he : e ≤ 8) (hcap : cap ≤ e) : 1 + loopW lay i cap 0 e ≤ 85 * e + 37 := by
  have h1 := loopW_le_max lay i cap e 0
  have h2 := loopW_worst e (by omega) cap hcap
  omega

/-- One installed prefix boundary and HASH rung, with the saved prefix framed. Stage 2: the rung keeps the half
`WCT9.chainHigh lay i m` (C3) and costs `rungW`. -/
theorem retained_rung {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc = pcOf 1014) (lay : Layer)
    (tree leaf i m e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hl : 1 ≤ lay.val) (hi : i < 43) (he : e < 8) (hm : m < e)
    (hv : valp + 16 ≤ 0x67000)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (hval : DigAt s (CHAIN + 48) v) :
    TBSim im sk s (rungW lay.val i cap m)
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m) (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v))
      (fun v' t => t.pc = pcOf 1014 ∧ t.getReg .x20 = BitVec.ofNat 64 (m+1) ∧
        DigAt t (CHAIN + 48) v' ∧ RegsExcept s t chainRegs ∧
        Frame s t (rungWrites lay.val i m valp) ∧
        (SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val = s.getReg .x18 →
          DigAt t (SharedPrefixes.buffer lay.val i m) v) ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  obtain ⟨n,u,hn,hu,upc,ur,uf,uv,usave⟩ := boundary hc hpref s hp lay.val i m valp cap
    hl (by omega) hi (by omega) (by have := hpre.hcap; omega) hpre.hv8 hv (hpre.hvc.imp id (fun h => by simp only [CHAIN] at *; omega)) hpre.x8 hpre.x17 hpre.x19 h20
    hpre.x23 v hval
  have ub : Frame s u (fun A => ChainWS valp A ∨ 0x67000 < A) := uf.mono (by
    intro A hA h
    have hb := SharedPrefixes.buffer_above_scratch (chain := i) (step := m) (half := 0) hl
    simp only [Nat.mul_zero,Nat.add_zero] at hb
    simp only [boundaryWrites] at h
    unfold ChainWS
    omega)
  have preu := pre_preserved hpre (ur.mono (by simp [chainRegs])) ub
  have run := hash_rung hc sk u upc lay tree leaf i m e cap valp ret v preu hm
    (by rw [ur.get (by decide)]; exact h20) uv
  have all := TSim.steps hu run
  refine all.toTBSim (by omega) |>.mono ?_ ?_
  · have hk : headerK lay ≤ 34 := by unfold headerK; split_ifs <;> omega
    unfold rungW
    omega
  · intro v' t ht
    refine ⟨ht.1,ht.2.1,ht.2.2.1,(ur.trans ht.2.2.2.1).mono (by simp [chainRegs]),?_,?_,
      fun hF => (ht.2.2.2.2.2 hF).1⟩
    · exact (uf.trans ht.2.2.2.2.1).mono (by
        intro A hA h
        simp only [boundaryWrites,hashWrites,rungWrites,ChainWS] at *
        omega)
    · intro hs
      have hb := SharedPrefixes.buffer_above_scratch (chain := i) (step := m) (half := 0) hl
      simp only [Nat.mul_zero,Nat.add_zero] at hb
      have hb8 := SharedPrefixes.buffer_bounds hl (by omega) hi (show m<8 by omega)
      exact (usave hs).frame ht.2.2.2.2.1 (by omega)
        (by simp only [hashWrites,CHAIN]; omega)
        (by simp only [hashWrites,CHAIN]; omega)

#print axioms retained_rung
end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem retained_exit {α : Type} (a : α) {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc = pcOf 1014) (lay : Layer)
    (tree leaf i e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hl : 1 ≤ lay.val) (hi : i < 43) (he : e < 8) (hv : valp + 16 ≤ 0x67000)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 e) (hval : DigAt s (CHAIN + 48) v) :
    TBSim im sk s (30 + (if e = cap then 6 else 0)) (pure a)
      (fun a' t => a' = a ∧ t.pc = pcOf ret ∧ DigAt t (CHAIN + 48) v ∧
        RegsExcept s t chainRegs ∧ Frame s t (rungWrites lay.val i e valp) ∧
        (SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val = s.getReg .x18 →
          DigAt t (SharedPrefixes.buffer lay.val i e) v) ∧
        (SigGolfCandidate.T3M.Sign.Seed.Z32 s → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  obtain ⟨n,u,hn,hu,upc,ur,uf,uv,usave⟩ := boundary hc hpref s hp lay.val i e valp cap
    hl (by omega) hi he (by have := hpre.hcap; omega) hpre.hv8 hv (hpre.hvc.imp id (fun h => by simp only [CHAIN] at *; omega)) hpre.x8 hpre.x17 hpre.x19 h20
    hpre.x23 v hval
  obtain ⟨t,ht,tpc,tr,tf⟩ := sub8_spec hc u upc e e (by omega) (by omega)
    (by rw [ur.get (by decide)]; exact h20)
    (by rw [ur.get (by decide)]; exact hpre.x21)
  rw [if_pos rfl] at tpc
  obtain ⟨w,hw,wpc,wr,wf⟩ := sub26_spec hc t tpc ret
    (by rw [tr.get (by simp),ur.get (by decide)]; exact hpre.x1)
  have fr : Frame u w (fun _ => False) := (tf.trans wf).mono (by simp)
  have rr : RegsExcept u w [] := (tr.trans wr).mono (by simp)
  exact (TSim.pure_steps (hu.trans (ht.trans hw)) ⟨rfl,wpc,
    uv.frame fr (by decide) (by simp) (by simp),
    (ur.trans rr).mono (by simp [chainRegs]),
    (uf.trans fr).mono (by
      intro A hA h
      simp only [boundaryWrites] at h
      rcases h with (h | h | h | h) | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl (Or.inr (Or.inr (by omega)))
      · exact Or.inl (Or.inr (Or.inr (by omega)))
      · exact h.elim),fun hs => (usave hs).frame fr (by
        have hb := SharedPrefixes.buffer_bounds hl (by omega) hi he
        omega) (by simp) (by simp), fun hz => by
        have hvc := hpre.hvc
        have hb := SharedPrefixes.buffer_above_scratch (chain := i) (step := e) (half := 0) hl
        simp only [Nat.mul_zero,Nat.add_zero] at hb
        simp only [CHAIN] at hvc
        exact hz.frame (uf.trans fr) (by intro h; simp only [boundaryWrites,CHAIN,or_false] at h; omega)
          (by intro h; simp only [boundaryWrites,CHAIN,or_false] at h; omega)⟩).toTBSim (by omega) |>.mono (by omega) (fun _ _ h => h)

#print axioms retained_exit
end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest)
open SigGolfCandidate.Research.SharedForest (chainPrefixes)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def loopWrites (lay i lo hi valp A : Nat) : Prop :=
  ChainWS valp A ∨ (SharedPrefixes.buffer lay i lo ≤ A ∧ A < SharedPrefixes.buffer lay i hi + 16)

/-- Stage 2 (C3, #866): one step of the retained-prefix chain keeps the half `WCT9.chainHigh lay i start`, i.e. the
spec `SharedForest.chainPrefixes` hashes with `WCT9.halfHash (WCT9.chainHigh lay i start)` as `WCT9.chainW` does. -/
theorem chainPrefixes_succ (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    chainPrefixes lay tree leaf i start (count + 1) value = (do
      let next ← ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i start)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value)
      let tail ← chainPrefixes lay tree leaf i (start + 1) count next
      pure (value :: tail)) := rfl

/-- The full retained-prefix chain executes every ordinary chain query once and
leaves each selected leaf prefix in its disjoint slot. -/
theorem retained_loop {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (lay : Layer) (tree leaf i e cap valp ret : Nat)
    (hl : 1 ≤ lay.val) (hi : i < 43) (he : e < 8) (hv : valp + 16 ≤ 0x67000)
    (hvi : valp + 16 ≤ 0x20550 ∨ 0x20558 ≤ valp) :
    ∀ (count m : Nat), m+count=e → ∀ (v : Digest) (s : MachineState),
    ChainPreS s lay tree leaf i cap e valp ret → s.pc = pcOf 1014 →
    s.getReg .x20 = BitVec.ofNat 64 m → DigAt s (CHAIN+48) v →
    TBSim im sk s (loopW lay.val i cap m count) (chainPrefixes lay tree leaf i m count v)
      (fun vs t => vs.length=count+1 ∧ t.pc=pcOf ret ∧ DigAt t (CHAIN+48) (vs.getD count 0) ∧
        RegsExcept s t chainRegs ∧ Frame s t (loopWrites lay.val i m e valp) ∧
        (SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val = s.getReg .x18 →
          ∀ j, j≤count → DigAt t (SharedPrefixes.buffer lay.val i (m+j)) (vs.getD j 0)) ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → SigGolfCandidate.T3M.Sign.Seed.Z32 s ∨ 0 < count → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  intro count
  induction count with
  | zero =>
    intro m hm v s hpre hp h20 hval
    have hme : m=e := by omega
    subst m
    simpa only [chainPrefixes,loopW] using
      (retained_exit [v] hc hpref sk s hp lay tree leaf i e cap valp ret v hpre hl hi he hv h20 hval).mono
        (le_refl _) (fun vs t ht => by
          rcases ht with ⟨rfl,ht⟩
          refine ⟨rfl,ht.1,?_,ht.2.2.1,?_,?_,fun _ hz => ht.2.2.2.2.2 (hz.resolve_right (by omega))⟩
          · simpa only [List.getD_cons_zero] using ht.2.1
          · exact ht.2.2.2.1.mono (by
              intro A hA h
              change ChainWS valp A ∨ A = SharedPrefixes.buffer lay.val i e ∨ A = SharedPrefixes.buffer lay.val i e + 8 at h
              change ChainWS valp A ∨ (SharedPrefixes.buffer lay.val i e ≤ A ∧ A < SharedPrefixes.buffer lay.val i e + 16)
              rcases h with h | h | h
              · exact Or.inl h
              · right; omega
              · right; omega)
          · intro hs j hj
            have hj0 : j=0 := by omega
            subst j
            simpa only [Nat.add_zero,List.getD_cons_zero] using ht.2.2.2.2.1 hs)
  | succ count ih =>
    intro m hm v s hpre hp h20 hval
    have hm' : m<e := by omega
    have one := retained_rung hc hpref sk s hp lay tree leaf i m e cap valp ret v
      hpre hl hi he hm' hv h20 hval
    rw [chainPrefixes_succ]
    show TBSim im sk s (rungW lay.val i cap m + loopW lay.val i cap (m+1) count) _ _
    refine TBSim.bind (W₁ := rungW lay.val i cap m) (W₂ := loopW lay.val i cap (m+1) count) one
      (fun v' u hu => ?_)
    have uf := hu.2.2.2.2.1
    have ub : Frame s u (fun A => ChainWS valp A ∨ 0x67000<A) := uf.mono (by
      intro A hA h
      have hb := SharedPrefixes.buffer_above_scratch (chain := i) (step := m) (half := 0) hl
      simp only [Nat.mul_zero,Nat.add_zero] at hb
      change ChainWS valp A ∨ A = SharedPrefixes.buffer lay.val i m ∨ A = SharedPrefixes.buffer lay.val i m + 8 at h
      rcases h with h | h | h
      · exact Or.inl h
      · right; omega
      · right; omega)
    have upre := pre_preserved hpre hu.2.2.2.1 ub
    have tail := ih (m+1) (by omega) v' u upre hu.1 hu.2.1 hu.2.2.1
    refine TBSim.bind (W₁ := loopW lay.val i cap (m+1) count) (W₂ := 0) tail (fun vs t ht => TBSim.pure ?_)
    refine ⟨by simpa only [List.length_cons] using congrArg (·+1) ht.1,ht.2.1,?_,
      (hu.2.2.2.1.trans ht.2.2.2.1).mono (by simp),?_,?_,
      fun hF _ => ht.2.2.2.2.2.2 hF (Or.inl (hu.2.2.2.2.2.2 hF))⟩
    · simpa only [List.getD_cons_succ] using ht.2.2.1
    · exact (uf.trans ht.2.2.2.2.1).mono (by
        intro A hA h
        change rungWrites lay.val i m valp A ∨ loopWrites lay.val i (m+1) e valp A at h
        change ChainWS valp A ∨ (SharedPrefixes.buffer lay.val i m ≤ A ∧ A < SharedPrefixes.buffer lay.val i e + 16)
        rcases h with (h | h | h) | (h | h)
        · exact Or.inl h
        · right; simp only [SharedPrefixes.buffer] at h ⊢; omega
        · right; simp only [SharedPrefixes.buffer] at h ⊢; omega
        · exact Or.inl h
        · right; simp only [SharedPrefixes.buffer] at h ⊢; omega)
    · intro hs j hj
      have usel : SharedPrefixes.selectionWord (u.getMem 0x20550) lay.val = u.getReg .x18 := by
        have idx : u.getMem (BitVec.ofNat 64 0x20550) = s.getMem (BitVec.ofNat 64 0x20550) :=
          uf 0x20550 (by decide) (by
            simp only [rungWrites,ChainWS,CHAIN,SharedPrefixes.buffer]
            omega)
        exact (congrArg (fun x => SharedPrefixes.selectionWord x lay.val) idx).trans
          (hs.trans (hu.2.2.2.1.get (by simp [chainRegs])).symm)
      cases j with
      | zero =>
        have saved := hu.2.2.2.2.2.1 hs
        have hb := SharedPrefixes.buffer_bounds hl (by omega) hi (show m<8 by omega)
        have lo := SharedPrefixes.buffer_above_scratch (chain := i) (step := m) (half := 0) hl
        simp only [Nat.mul_zero,Nat.add_zero] at lo
        simpa only [List.getD_cons_zero,Nat.add_zero] using saved.frame ht.2.2.2.2.1
          (by omega) (by simp only [loopWrites,ChainWS,CHAIN,SharedPrefixes.buffer] at *; omega)
          (by simp only [loopWrites,ChainWS,CHAIN,SharedPrefixes.buffer] at *; omega)
      | succ j =>
        have saved := ht.2.2.2.2.2.1 usel j (by omega)
        simpa only [List.getD_cons_succ,show m+(j+1)=m+1+j by omega] using saved
#print axioms retained_loop
end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest)
open SigGolfCandidate.Research.SharedForest (chainPrefixes)
set_option maxHeartbeats 2000000

theorem retained_chain {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc = pcOf 1013) (lay : Layer)
    (tree leaf i e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hl : 1 ≤ lay.val) (hi : i < 43) (he : e < 8) (hv : valp + 16 ≤ 0x67000)
    (hvi : valp + 16 ≤ 0x20550 ∨ 0x20558 ≤ valp) (hval : DigAt s (CHAIN+48) v) :
    TBSim im sk s (85*e+37) (chainPrefixes lay tree leaf i 0 e v)
      (fun vs t => vs.length=e+1 ∧ t.pc=pcOf ret ∧ DigAt t (CHAIN+48) (vs.getD e 0) ∧
        RegsExcept s t chainRegs ∧ Frame s t (loopWrites lay.val i 0 e valp) ∧
        (SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val = s.getReg .x18 →
          ∀ j, j≤e → DigAt t (SharedPrefixes.buffer lay.val i j) (vs.getD j 0)) ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → 0 < e → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  obtain ⟨u,hu,upc,u20,ur,uf⟩ := sub0_spec hc s hp
  have preu := pre_preserved hpre (ur.mono (by simp [chainRegs]))
    (uf.mono (by intro A hA h; exact h.elim))
  have run := retained_loop hc hpref sk lay tree leaf i e cap valp ret hl hi he hv hvi e 0
    (by omega) v u preu upc u20 (hval.frame uf (by decide) (by simp) (by simp))
  refine (TBSim.steps hu run).mono (loopW_le lay.val i cap e hpre.he hpre.hcap) ?_
  intro vs t ht
  refine ⟨ht.1,ht.2.1,ht.2.2.1,(ur.trans ht.2.2.2.1).mono (by simp [chainRegs]),
    (uf.trans ht.2.2.2.2.1).mono (by intro A hA h; exact h.elim False.elim id),?_,
    fun hF he0 => ht.2.2.2.2.2.2 hF (Or.inr he0)⟩
  intro hs j hj
  have us : SharedPrefixes.selectionWord (u.getMem 0x20550) lay.val = u.getReg .x18 := by
    have idx := uf 0x20550 (by decide) (by simp)
    exact (congrArg (fun x => SharedPrefixes.selectionWord x lay.val) idx).trans
      (hs.trans (ur.get (by decide)).symm)
  simpa only [Nat.zero_add] using ht.2.2.2.2.2.1 us j hj

#print axioms retained_chain
end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest chainInput shortHash)
open SigGolfCandidate.Research.SharedForest (chainPrefixes)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem unselected_boundary {im : Image} (hc : Code im) (hpref : PrefixCode im)
    (s : MachineState) (hp : s.pc=pcOf 1014) (lay valp step cap : Nat)
    (hl : 1≤lay) (hh : lay≤3) (hv8 : valp%8=0) (hv : valp+16≤0x67000)
    (hs : step<2^64) (hcap : cap<2^64)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (h23 : s.getReg .x23=BitVec.ofNat 64 valp)
    (h17 : s.getReg .x17=BitVec.ofNat 64 cap) (h20 : s.getReg .x20=BitVec.ofNat 64 step)
    (hmiss : SharedPrefixes.selectionWord (s.getMem 0x20550) lay ≠ s.getReg .x18) :
    ∃ n t, n≤28+(if step=cap then 6 else 0) ∧ Steps im s n n t ∧ t.pc=pcOf 1021 ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (fun A => A=valp ∨ A=valp+8) := by
  obtain ⟨u,hu,upc,ur,uf⟩ := SharedPrefixes.hook_steps hpref.hook s hp
  obtain ⟨n,v,hn,hv',vpc,_,vr,vf⟩ := SharedPrefixes.guard_steps hpref.guard u upc lay hl hh
    (by rw [ur.get (by simp)]; exact h8)
  have missu : SharedPrefixes.selectionWord (u.getMem 0x20550) lay ≠ u.getReg .x18 := by
    have idx : u.getMem 0x20550=s.getMem 0x20550 := uf 0x20550 (by decide) (by simp)
    rw [idx,ur.get (by simp)]
    exact hmiss
  rw [if_neg missu] at vpc
  obtain ⟨w,hw,wpc,wr,wf⟩ := SharedPrefixes.resume_full_steps hpref.resume hpref.miss hpref.hit v vpc
  have rr : RegsExcept s w [.x6,.x7,.x28,.x29] := ((ur.trans vr).trans wr).mono (by simp)
  have fr : Frame s w (fun _ => False) := ((uf.trans vf).trans wf).mono (by simp)
  rw [vr.get (r:=.x20) (by decide),vr.get (r:=.x17) (by decide),
      ur.get (r:=.x20) (by simp),ur.get (r:=.x17) (by simp)] at wpc
  by_cases hcap' : s.getReg .x20=s.getReg .x17
  · rw [if_pos hcap'] at wpc
    have hsc : step=cap := (ofNat_inj hs hcap).mp (h20.symm.trans (hcap'.trans h17))
    obtain ⟨t,ht,tpc,_,_,tr,tf⟩ := sub2_spec hc w wpc valp
      (by rw [rr.get (by decide)]; exact h23) hv8 (by omega)
    exact ⟨1+n+2+6,t,by rw [if_pos hsc]; omega,((hu.trans hv').trans hw).trans ht,tpc,
      (rr.trans tr).mono (by simp),(fr.trans tf).mono (by simp)⟩
  · rw [if_neg hcap'] at wpc
    exact ⟨1+n+2,w,by split <;> omega,(hu.trans hv').trans hw,wpc,rr,fr.mono (by simp)⟩

theorem unselected_rung {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc=pcOf 1014) (lay : Layer)
    (tree leaf i m e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hl : 1≤lay.val) (hm : m<e) (hv : valp+16≤0x67000)
    (h20 : s.getReg .x20=BitVec.ofNat 64 m) (hval : DigAt s (CHAIN+48) v)
    (hmiss : SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val ≠ s.getReg .x18) :
    TBSim im sk s (rungW lay.val i cap m)
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m) (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v))
      (fun v' t => t.pc=pcOf 1014 ∧ t.getReg .x20=BitVec.ofNat 64 (m+1) ∧
        DigAt t (CHAIN+48) v' ∧ RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs ∧ Frame s t (ChainWS valp) ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  obtain ⟨n,u,hn,hu,upc,ur,uf⟩ := unselected_boundary hc hpref s hp lay.val valp m cap hl
    (by have := lay.isLt; omega) hpre.hv8 hv (by have := hpre.he; omega) (by have := hpre.hcap; have := hpre.he; omega)
    hpre.x8 hpre.x23 hpre.x17 h20 hmiss
  have ub : Frame s u (fun A => ChainWS valp A ∨ 0x67000<A) := uf.mono (by
    intro A hA h; unfold ChainWS; omega)
  have preu := pre_preserved hpre (ur.mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs])) ub
  have uv := hval.frame uf (by decide) (by have := hpre.hvc; omega) (by have := hpre.hvc; omega)
  have run := hash_rung hc sk u upc lay tree leaf i m e cap valp ret v preu hm
    (by rw [ur.get (by decide)]; exact h20) uv
  refine (TSim.steps hu run).toTBSim (by omega) |>.mono ?_ ?_
  · have hk : headerK lay≤34 := by unfold headerK; split_ifs <;> omega
    unfold rungW
    omega
  · intro v' t ht
    refine ⟨ht.1,ht.2.1,ht.2.2.1,(ur.trans ht.2.2.2.1).mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]),?_,
      fun hF => (ht.2.2.2.2.2 hF).1⟩
    exact (uf.trans ht.2.2.2.2.1).mono (by intro A hA h; simp only [hashWrites,ChainWS] at *; omega)

theorem unselected_exit {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc=pcOf 1014) (lay : Layer)
    (tree leaf i e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hl : 1≤lay.val) (hv : valp+16≤0x67000)
    (h20 : s.getReg .x20=BitVec.ofNat 64 e) (hval : DigAt s (CHAIN+48) v)
    (hmiss : SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val ≠ s.getReg .x18) :
    TBSim im sk s (30+(if e=cap then 6 else 0)) (pure [v])
      (fun vs t => vs=[v] ∧ t.pc=pcOf ret ∧ DigAt t (CHAIN+48) v ∧
        RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs ∧ Frame s t (ChainWS valp) ∧
        (SigGolfCandidate.T3M.Sign.Seed.Z32 s → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  obtain ⟨n,u,hn,hu,upc,ur,uf⟩ := unselected_boundary hc hpref s hp lay.val valp e cap hl
    (by have := lay.isLt; omega) hpre.hv8 hv (by have := hpre.he; omega) (by have := hpre.hcap; have := hpre.he; omega)
    hpre.x8 hpre.x23 hpre.x17 h20 hmiss
  obtain ⟨t,ht,tpc,tr,tf⟩ := sub8_spec hc u upc e e (by have := hpre.he; omega) (by have := hpre.he; omega)
    (by rw [ur.get (by decide)]; exact h20) (by rw [ur.get (by decide)]; exact hpre.x21)
  rw [if_pos rfl] at tpc
  obtain ⟨w,hw,wpc,wr,wf⟩ := sub26_spec hc t tpc ret
    (by rw [tr.get (by simp),ur.get (by decide)]; exact hpre.x1)
  have fr : Frame s w (fun A => A=valp ∨ A=valp+8) := ((uf.trans tf).trans wf).mono (by simp)
  exact (TSim.pure_steps (hu.trans (ht.trans hw)) ⟨rfl,wpc,
    hval.frame fr (by decide) (by have := hpre.hvc; omega) (by have := hpre.hvc; omega),
    ((ur.trans tr).trans wr).mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]),fr.mono (by intro A hA h; unfold ChainWS; omega),
    fun hz => by
      have hvc := hpre.hvc
      exact hz.frame fr (by simp only [CHAIN] at *; omega) (by simp only [CHAIN] at *; omega)⟩).toTBSim
    (by omega) |>.mono (by omega) (fun _ _ h => h)

end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest)
open SigGolfCandidate.Research.SharedForest (chainPrefixes)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem unselected_loop {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (lay : Layer) (tree leaf i e cap valp ret : Nat)
    (hl : 1≤lay.val) (hv : valp+16≤0x67000) (hvi : valp+16≤0x20550 ∨ 0x20558≤valp) :
    ∀ (count m : Nat), m+count=e → ∀ (v : Digest) (s : MachineState),
    ChainPreS s lay tree leaf i cap e valp ret → s.pc=pcOf 1014 →
    s.getReg .x20=BitVec.ofNat 64 m → DigAt s (CHAIN+48) v →
    SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val ≠ s.getReg .x18 →
    TBSim im sk s (loopW lay.val i cap m count) (chainPrefixes lay tree leaf i m count v)
      (fun vs t => vs.length=count+1 ∧ t.pc=pcOf ret ∧ DigAt t (CHAIN+48) (vs.getD count 0) ∧
        RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs ∧ Frame s t (ChainWS valp) ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → SigGolfCandidate.T3M.Sign.Seed.Z32 s ∨ 0 < count → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  intro count
  induction count with
  | zero =>
      intro m hm v s hpre hp h20 hval hmiss
      have hme : m=e := by omega
      subst m
      simpa only [chainPrefixes,loopW] using
        (unselected_exit hc hpref sk s hp lay tree leaf i e cap valp ret v hpre hl hv h20 hval hmiss).mono
          (le_refl _) (fun vs t ht => by
            rcases ht with ⟨rfl,ht⟩
            exact ⟨rfl,ht.1,by simpa only [List.getD_cons_zero] using ht.2.1,ht.2.2.1,ht.2.2.2.1,
              fun _ hz => ht.2.2.2.2 (hz.resolve_right (by omega))⟩)
  | succ count ih =>
      intro m hm v s hpre hp h20 hval hmiss
      have run := unselected_rung hc hpref sk s hp lay tree leaf i m e cap valp ret v hpre hl
        (by omega) hv h20 hval hmiss
      rw [chainPrefixes_succ]
      show TBSim im sk s (rungW lay.val i cap m + loopW lay.val i cap (m+1) count) _ _
      refine TBSim.bind (W₂:=loopW lay.val i cap (m+1) count) run (fun v' u hu => ?_)
      obtain ⟨upc,u20,uval,ur,uf,uz⟩ := hu
      have preu := pre_preserved hpre ur (uf.mono (by intro A hA h; exact Or.inl h))
      have idx : u.getMem 0x20550=s.getMem 0x20550 := uf 0x20550 (by decide) (by unfold ChainWS CHAIN; omega)
      have missu : SharedPrefixes.selectionWord (u.getMem 0x20550) lay.val ≠ u.getReg .x18 := by
        rw [idx,ur.get (by decide)]
        exact hmiss
      have rest := ih (m+1) (by omega) v' u preu upc u20 uval missu
      refine TBSim.bind (W₂:=0) rest (fun vs t ht => TBSim.pure ?_) |>.mono (by omega) (fun _ _ h => h)
      obtain ⟨hlen,tpc,tval,tr,tf,tz⟩ := ht
      exact ⟨by simp only [List.length_cons,hlen],tpc,
        by simpa only [List.getD_cons_succ] using tval,
        (ur.trans tr).mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]),(uf.trans tf).mono (by simp),
        fun hF _ => tz hF (Or.inl (uz hF))⟩

theorem unselected_chain {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc=pcOf 1013) (lay : Layer)
    (tree leaf i e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hl : 1≤lay.val) (hv : valp+16≤0x67000)
    (hvi : valp+16≤0x20550 ∨ 0x20558≤valp) (hval : DigAt s (CHAIN+48) v)
    (hmiss : SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val ≠ s.getReg .x18) :
    TBSim im sk s (85*e+37) (chainPrefixes lay tree leaf i 0 e v)
      (fun vs t => vs.length=e+1 ∧ t.pc=pcOf ret ∧ DigAt t (CHAIN+48) (vs.getD e 0) ∧
        RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs ∧ Frame s t (ChainWS valp) ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → 0 < e → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  obtain ⟨u,hu,upc,u20,ur,uf⟩ := sub0_spec hc s hp
  have preu := pre_preserved hpre (ur.mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]))
    (uf.mono (by intro A hA h; exact h.elim))
  have missu : SharedPrefixes.selectionWord (u.getMem 0x20550) lay.val ≠ u.getReg .x18 := by
    have idx : u.getMem 0x20550=s.getMem 0x20550 := uf 0x20550 (by decide) (by simp)
    rw [idx,ur.get (by decide)]
    exact hmiss
  have run := unselected_loop hc hpref sk lay tree leaf i e cap valp ret hl hv hvi e 0
    (by omega) v u preu upc u20 (hval.frame uf (by decide) (by simp) (by simp)) missu
  refine (TBSim.steps hu run).mono (loopW_le lay.val i cap e hpre.he hpre.hcap) ?_
  intro vs t ht
  exact ⟨ht.1,ht.2.1,ht.2.2.1,(ur.trans ht.2.2.2.1).mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]),
    (uf.trans ht.2.2.2.2.1).mono (by simp), fun hF he0 => ht.2.2.2.2.2 hF (Or.inr he0)⟩

end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route)
set_option maxRecDepth 10000
theorem selection_mask (a m : Nat) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 (2 ^ m - 1) = BitVec.ofNat 64 (a % 2 ^ m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and]
  by_cases h : i < m <;> simp [h]
theorem selection_route (index : Nat) (hi : index<2^31) (lay : Layer) (hl : lay≠0) :
    selectionWord (BitVec.ofNat 64 index) lay.val=BitVec.ofNat 64 (route index lay).1 := by
  fin_cases lay
  · exact (hl rfl).elim
  · change (BitVec.ofNat 64 index >>> (12 : Nat)) &&& 127 = BitVec.ofNat 64 (index/2^12%2^7)
    rw [ofNat_shr index 12 (by omega)]
    exact selection_mask (index/2^12) 7
  · change (BitVec.ofNat 64 index >>> (6 : Nat)) &&& 63 = BitVec.ofNat 64 (index/2^6%2^6)
    rw [ofNat_shr index 6 (by omega)]
    exact selection_mask (index/2^6) 6
  · simpa [selectionWord,route,SigGolfCandidate.T3.height] using selection_mask index 6
end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3M.Sign.Seed
open SigGolfCandidate.T3 (Layer Digest chain chainInput shortHash)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem top_boundary {im : Image} (hpref : PrefixCode im) (s : MachineState)
    (hp : s.pc = pcOf 1014) (h8 : s.getReg .x8 = 0) :
    ∃ t, Steps im s 4 4 t ∧
      t.pc = (if s.getReg .x20 = s.getReg .x17 then pcOf 1015 else pcOf 1021) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨u,hu,up,ur,uf⟩ := SharedPrefixes.hook_steps hpref.hook s hp
  obtain ⟨t,ht,tp,tr,tf⟩ := SharedPrefixes.top_steps hpref.guard hpref.resume hpref.miss hpref.hit u up
    ((ur.get (by simp)).trans h8)
  rw [ur.get (r := .x20) (by simp),ur.get (r := .x17) (by simp)] at tp
  exact ⟨t,hu.trans ht,tp,(ur.trans tr).mono (by simp),(uf.trans tf).mono (by simp)⟩

/-- Extra steps of a top-layer rung: the F step block (`3`) and the C3 tail trampoline (`3` on chain 0, `2` on the
others; the top layer never keeps the HIGH half). -/
def topTr (i : Nat) : Nat := if i = 0 then 6 else 5

theorem trX_top (i m : Nat) : SigGolfCandidate.T3M.Sign.Seed.trX (0 : Layer).val i m = topTr i := by
  unfold SigGolfCandidate.T3M.Sign.Seed.trX SigGolfCandidate.T3M.Sign.Seed.trX0 topTr
  by_cases hi : i = 0
  · subst hi; simp
  · simp [hi]

section
variable {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : SecretKey)
  {s0 : MachineState} {tree leaf i e valp ret : Nat}
  (hpre : ChainPreS s0 0 tree leaf i e e valp ret)
include hc hpref hpre

/-- The top-chain loop state: the old (narrow) chain head, and the F pads still zero (the F step block rewrites them
with zeros, so they are not chain writes here). -/
def TopHead (s0 : MachineState) (valp m : Nat) (v : Digest) (t : MachineState) : Prop :=
  Keygen.ChainHead 1013 s0 valp m v t ∧ SigGolfCandidate.T3M.Sign.Seed.Z32 t

omit hc hpref in
theorem TopHead.pre {m : Nat} {v : Digest} {t : MachineState} (ht : TopHead s0 valp m v t) :
    ChainPreS t 0 tree leaf i e e valp ret :=
  pre_preserved hpre ht.1.regs (ht.1.frame.mono (by
    intro A hA h; left; exact SigGolfCandidate.T3M.Sign.Seed.ChainWS_of_chainW h))

theorem top_step {m : Nat} (hm : m < e) {v : Digest} {t : MachineState}
    (ht : TopHead s0 valp m v t) :
    TSim im sk t (headerK 0+8+topTr i) (headerK 0+15+topTr i) 1 1
      (shortHash (chainInput 0 tree leaf i m v))
      (fun v' u => TopHead s0 valp (m+1) v' u) := by
  have he := hpre.he
  have pt := ht.pre hpre
  obtain ⟨u,hu,up,ur,uf⟩ := top_boundary hpref t ht.1.pc pt.x8
  have hne : t.getReg .x20 ≠ t.getReg .x17 := by
    rw [ht.1.x20,pt.x17]
    intro hn
    have hn := congrArg BitVec.toNat hn
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show m < 2^64 by omega), Nat.mod_eq_of_lt (show e < 2^64 by omega)] at hn
    omega
  rw [if_neg hne] at up
  have pu := pre_preserved pt (ur.mono (by simp)) (uf.mono (by simp))
  have hv := ht.1.val.frame uf (by decide) (by simp) (by simp)
  have hzu : SigGolfCandidate.T3M.Sign.Seed.Z32 u := ht.2.frame uf (by simp) (by simp)
  have hx := trX_top i m
  refine (TSim.steps hu (hash_rung hc sk u up 0 tree leaf i m e e valp ret v pu hm
    ((ur.get (by simp)).trans ht.1.x20) hv)).of_eq
    (by rw [ClaudeWCT.WCT9.chainHigh_top, ClaudeWCT.WCT9.halfHash_false, ClaudeWCT.WCT9.chainInputW_top])
    (by omega) (by omega) rfl rfl |>.mono ?_
  intro v' w hw
  obtain ⟨hz, hfw⟩ := hw.2.2.2.2.2 (SigGolfCandidate.T3M.Sign.Seed.FCh_top i)
  -- the F pads are rewritten with zeros: the narrow frame `ChainW` holds semantically
  have hfn : Frame u w (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 48 ≤ A ∧ A < CHAIN + 80)) := by
    intro A hA hn
    by_cases h32 : A = CHAIN + 32
    · subst h32; exact hz.1.trans hzu.1.symm
    by_cases h40 : A = CHAIN + 40
    · subst h40; exact hz.2.trans hzu.2.symm
    exact hfw A hA (by simp only [CHAIN] at *; omega)
  refine ⟨⟨hw.1,hw.2.1,((ht.1.regs.trans ur).trans hw.2.2.2.1).mono (by simp),?_,hw.2.2.1⟩, hz⟩
  exact ((ht.1.frame.trans uf).trans hfn).mono (by
    intro A hA h
    rcases h with (h|h)|h
    · exact h
    · exact h.elim
    · rcases h with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  )

theorem top_exit {v : Digest} {t : MachineState}
    (ht : TopHead s0 valp e v t) :
    ∃ u, Steps im t 12 12 u ∧ u.pc = pcOf ret ∧ DigAt u valp v ∧
      RegsExcept t u [.x6,.x7,.x29] ∧ Frame t u (fun A => valp ≤ A ∧ A < valp+16) := by
  have he := hpre.he
  have pt := ht.pre hpre
  obtain ⟨t1,st1,t1pc,t1r,t1f⟩ := top_boundary hpref t ht.1.pc pt.x8
  rw [if_pos (ht.1.x20.trans pt.x17.symm)] at t1pc
  obtain ⟨t2,st2,t2pc,t2v0,t2v8,t2r,t2f⟩ := sub2_spec hc t1 t1pc valp
    ((t1r.get (by simp)).trans pt.x23) pt.hv8 pt.hv
  have hv1:=ht.1.val.frame t1f (by decide) (by simp) (by simp)
  obtain ⟨t3,st3,t3pc,t3r,t3f⟩ := sub8_spec hc t2 t2pc e e (by omega) (by omega)
    ((t2r.get (by simp)).trans ((t1r.get (by simp)).trans ht.1.x20))
    ((t2r.get (by simp)).trans ((t1r.get (by simp)).trans pt.x21))
  rw [if_pos rfl] at t3pc
  obtain ⟨t4,st4,t4pc,t4r,t4f⟩ := sub26_spec hc t3 t3pc ret
    ((t3r.get (by simp)).trans ((t2r.get (by simp)).trans ((t1r.get (by simp)).trans pt.x1)))
  refine ⟨t4,st1.trans (st2.trans (st3.trans st4)),t4pc,?_,
    (((t1r.trans t2r).trans t3r).trans t4r).mono (by simp),?_⟩
  · exact (show DigAt t2 valp v from ⟨t2v0.trans hv1.1,t2v8.trans hv1.2⟩).frame
      (t3f.trans t4f) (by have := pt.hv; omega) (by simp) (by simp)
  · exact (((t1f.trans t2f).trans t3f).trans t4f).mono (by
      intro A hA h
      rcases h with ((h|h)|h)|h
      · exact h.elim
      · rcases h with h|h <;> omega
      · exact h.elim
      · exact h.elim)

/-- A top chain. Pairing stage 1: each rung pays the F step block and the C3 tail trampoline (`topTr i` steps). The F
pads `CHAIN+32/40` are zero on entry and stay zero, so the chain writes the old set `ChainW valp`. -/
theorem top_chain {v : Digest} (hp : s0.pc = pcOf 1013) (hv : DigAt s0 (CHAIN+48) v)
    (hz : SigGolfCandidate.T3M.Sign.Seed.Z32 s0) :
    TSim im sk s0 ((headerK 0+8+topTr i)*e+13) ((headerK 0+15+topTr i)*e+13) e e
      (do let a ← chain 0 tree leaf i 0 e v; pure (a,a))
      (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN+48) r.2 ∧
        RegsExcept s0 t Keygen.chainRegs ∧ Frame s0 t (ChainW valp)) := by
  obtain ⟨u,hu,up,u20,ur,uf⟩ := sub0_spec hc s0 hp
  have h0 : TopHead s0 valp 0 v u :=
    ⟨⟨up,u20,ur.mono (by simp [Keygen.chainRegs]),uf.mono (by simp),hv.frame uf (by decide) (by simp) (by simp)⟩,
      hz.frame uf (by simp) (by simp)⟩
  have run : TSim im sk u (sumTo (fun _ => headerK 0+8+topTr i) e) (sumTo (fun _ => headerK 0+15+topTr i) e)
      (sumTo (fun _ => 1) e) (sumTo (fun _ => 1) e) (chain 0 tree leaf i 0 e v)
      (fun a t => TopHead s0 valp e a t) := by
    unfold chain
    exact TSim.foldlM_range' 0 e _ v (fun j a t => TopHead s0 valp j a t) _ _ _ _
      (fun j hj a t ht => by simpa using top_step hc hpref sk hpre hj ht) h0
  have rest : ∀ a t, TopHead s0 valp e a t →
      TSim im sk t 12 12 0 0 (pure (a,a))
        (fun r w => w.pc = pcOf ret ∧ DigAt w valp r.1 ∧ DigAt w (CHAIN+48) r.2 ∧
          RegsExcept s0 w Keygen.chainRegs ∧ Frame s0 w (ChainW valp)) := by
    intro a t ht
    obtain ⟨w,hw,wp,wv,wr,wf⟩ := top_exit hc hpref hpre ht
    have hvc:=hpre.hvc
    exact TSim.pure_steps hw ⟨wp,wv,ht.1.val.frame wf (by decide) (by simp; omega) (by simp; omega),
      (ht.1.regs.trans wr).mono (by simp [Keygen.chainRegs]),(ht.1.frame.trans wf).mono (by
        intro A hA h; rcases h with h|h; exact h; exact Or.inr (Or.inr h))⟩
  refine (TSim.steps hu (TSim.bind run rest)).of_eq rfl ?_ ?_ ?_ ?_
  all_goals simp only [sumTo_const,Nat.mul_comm]; omega
end
#print axioms top_boundary
#print axioms top_step
#print axioms top_exit
#print axioms top_chain
end ClaudeWCT.W9.Machine.Sign.SharedChain
