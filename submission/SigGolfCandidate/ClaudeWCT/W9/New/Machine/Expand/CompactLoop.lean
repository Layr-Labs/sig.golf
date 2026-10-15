import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.CompactCode

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
def copied (s0 : MachineState) (src dst i : Nat) (A : Nat) : Word :=
  if dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0 then s0.getMem (BitVec.ofNat 64 (src + (A - dst)))
  else s0.getMem (BitVec.ofNat 64 A)
def zeroed (s0 : MachineState) (dst i : Nat) (A : Nat) : Word :=
  if dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0 then 0 else s0.getMem (BitVec.ofNat 64 A)
theorem ofNat_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) + 18446744073709551615#64 = BitVec.ofNat 64 n := by
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 1) from rfl, ofNat_add_ofNat,
    show n + 1 + (2 ^ 64 - 1) = n + 2 ^ 64 by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.add_mod_right]
macro "c_regs" res:ident : tactic =>
  `(tactic| (intro r hr
             simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
             cases r <;> simp_all [rv_simp, $res:ident] <;> rfl))
section
variable {im : Image} (hc : NewCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem copy_iter (s : MachineState) (hpc : s.pc = pcOf 42130) (src dst n : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (n + 1)) (hn : n + 1 < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 8 ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = (if n = 0 then pcOf 42136 else pcOf 42130) ∧
      t.getReg .x10 = BitVec.ofNat 64 (src + 8) ∧ t.getReg .x11 = BitVec.ofNat 64 (dst + 8) ∧
      t.getReg .x12 = BitVec.ofNat 64 n ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = dst then s.getMem (BitVec.ofNat 64 src) else s.getMem (BitVec.ofNat 64 A)) := by
  have hS : MEMORY_BYTES < 2 ^ 64 := by decide
  refine ⟨_, symRun_sound RCopy (code_cCopy hc) s hpc (by
    simp [RCopy.res, rv_simp, accessValid_iff, h10, h11, BitVec.toNat_ofNat]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RCopy.res, E.eval, CmpOp.eval, BinOp.eval, h12]
    rw [ofNat_sub_one n]
    by_cases h0 : n = 0
    · subst h0; simp
    · have : (BitVec.ofNat 64 n != 0#64) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h; apply h0
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega
      simp [this, h0]
  · simp [RCopy.res, rv_simp, h10, ofNat_add_ofNat]
  · simp [RCopy.res, rv_simp, h11, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RCopy.res, RegFile.get, E.eval, BinOp.eval, h12]
    rw [ofNat_sub_one]
  · c_regs RCopy.res
  · intro A hA
    simp only [Result.toState_getMem, RCopy.res, memEval_cons, memEval_nil, Addr.eval, E.eval, h10, h11]
    by_cases hA' : A = dst
    · subst hA'; simp [BitVec.add_zero]
    · rw [if_neg hA', if_neg]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, BitVec.toNat_add] at this
      omega
theorem copy_ret (s : MachineState) (hpc : s.pc = pcOf 42136) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RCopyRet (code_copyRet hc) s hpc (by simp [RCopyRet.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RCopyRet.res, E.eval, h1]
    exact pcOf_and_not1 ret
  · intro r _; cases r <;> simp [RCopyRet.res, rv_simp] <;> rfl
  · intro A _ _; rfl
structure CopyInv (s : MachineState) (src dst n i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if i < n then pcOf 42130 else pcOf 42136)
  x10 : t.getReg .x10 = BitVec.ofNat 64 (src + 8 * i)
  x11 : t.getReg .x11 = BitVec.ofNat 64 (dst + 8 * i)
  x12 : t.getReg .x12 = BitVec.ofNat 64 (n - i)
  regs : RegsExcept s t [.x6, .x10, .x11, .x12]
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = copied s src dst i A
theorem copy_loop (s : MachineState) (hpc : s.pc = pcOf 42130) (src dst n : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (hn : 0 < n) (hn' : n < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 8 * n ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES)
    (hov : dst ≤ src ∨ src + 8 * n ≤ dst) :
    ∀ i, i ≤ n → ∃ t, Steps im s (6 * i) (6 * i) t ∧ CopyInv s src dst n i t := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, ⟨by rw [hpc, if_pos hn], by simpa using h10, by simpa using h11,
      by simpa using h12, fun r _ => rfl, fun A _ => ?_⟩⟩
    unfold copied; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 42130 := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u10, u11, u12, ru, mu⟩ := copy_iter hc t hpc' (src + 8 * i) (dst + 8 * i) (n - i - 1)
      hI.x10 hI.x11 (by rw [hI.x12]; congr 1; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : n - i - 1 = 0
      · rw [if_pos h, if_neg (by omega)]
      · rw [if_neg h, if_pos (by omega)]
    · rw [u10, show src + 8 * i + 8 = src + 8 * (i + 1) by ring]
    · rw [u11, show dst + 8 * i + 8 = dst + 8 * (i + 1) by ring]
    · rw [u12, show n - i - 1 = n - (i + 1) by omega]
    · exact (hI.regs.trans ru).mono (by decide)
    · intro A hA
      have hsrc : t.getMem (BitVec.ofNat 64 (src + 8 * i)) = s.getMem (BitVec.ofNat 64 (src + 8 * i)) := by
        rw [hI.mem _ (by omega)]; unfold copied; rw [if_neg (by omega)]
      rw [mu A hA, hsrc, hI.mem A hA]
      unfold copied
      by_cases hA' : A = dst + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega), show dst + 8 * i - dst = 8 * i by omega]
      · rw [if_neg hA']
        by_cases hin : dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]
theorem copy_spec (s : MachineState) (hpc : s.pc = pcOf 42130) (src dst n ret : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (h1 : s.getReg .x1 = pcOf ret) (hn : 0 < n) (hn' : n < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 8 * n ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES)
    (hov : dst ≤ src ∨ src + 8 * n ≤ dst) :
    ∃ t, Steps im s (6 * n + 1) (6 * n + 1) t ∧ t.pc = pcOf ret ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = copied s src dst n A) := by
  obtain ⟨t, st, hI⟩ := copy_loop hc s hpc src dst n h10 h11 h12 hn hn' hs hs' hd hd' hov n le_rfl
  have hpc' : t.pc = pcOf 42136 := by rw [hI.pc, if_neg (by omega)]
  obtain ⟨u, su, pu, ru, fu⟩ := copy_ret hc t hpc' ret (by rw [hI.regs.get (by decide), h1])
  exact ⟨u, st.trans su, pu, (hI.regs.trans ru).mono (by decide), fun A hA => by
    rw [fu A hA (fun h => h), hI.mem A hA]⟩
set_option maxRecDepth 20000 in
theorem zero_iter (s : MachineState) (hpc : s.pc = pcOf 42137) (dst n : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 (n + 1))
    (hn : n + 1 < 2 ^ 32) (hd : dst % 8 = 0) (hd' : dst + 8 ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = (if n = 0 then pcOf 42141 else pcOf 42137) ∧
      t.getReg .x11 = BitVec.ofNat 64 (dst + 8) ∧ t.getReg .x12 = BitVec.ofNat 64 n ∧
      RegsExcept s t [.x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = if A = dst then 0 else s.getMem (BitVec.ofNat 64 A)) := by
  have hS : MEMORY_BYTES < 2 ^ 64 := by decide
  refine ⟨_, symRun_sound RZero (code_cZero hc) s hpc (by
    simp [RZero.res, rv_simp, accessValid_iff, h11, BitVec.toNat_ofNat]
    refine ⟨?_, ?_⟩ <;> omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RZero.res, E.eval, CmpOp.eval, BinOp.eval, h12]
    rw [ofNat_sub_one n]
    by_cases h0 : n = 0
    · subst h0; simp
    · have : (BitVec.ofNat 64 n != 0#64) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h; apply h0
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega
      simp [this, h0]
  · simp [RZero.res, rv_simp, h11, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RZero.res, RegFile.get, E.eval, BinOp.eval, h12]
    rw [ofNat_sub_one]
  · c_regs RZero.res
  · intro A hA
    simp only [Result.toState_getMem, RZero.res, memEval_cons, memEval_nil, Addr.eval, E.eval, h11]
    by_cases hA' : A = dst
    · subst hA'; simp [BitVec.add_zero]
    · rw [if_neg hA', if_neg]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, BitVec.toNat_add] at this
      omega
theorem zero_ret (s : MachineState) (hpc : s.pc = pcOf 42141) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RZeroRet (code_zeroRet hc) s hpc (by simp [RZeroRet.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RZeroRet.res, E.eval, h1]
    exact pcOf_and_not1 ret
  · intro r _; cases r <;> simp [RZeroRet.res, rv_simp] <;> rfl
  · intro A _ _; rfl
structure ZeroInv (s : MachineState) (dst n i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if i < n then pcOf 42137 else pcOf 42141)
  x11 : t.getReg .x11 = BitVec.ofNat 64 (dst + 8 * i)
  x12 : t.getReg .x12 = BitVec.ofNat 64 (n - i)
  regs : RegsExcept s t [.x11, .x12]
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = zeroed s dst i A
theorem zero_loop (s : MachineState) (hpc : s.pc = pcOf 42137) (dst n : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (hn : 0 < n)
    (hn' : n < 2 ^ 32) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES) :
    ∀ i, i ≤ n → ∃ t, Steps im s (4 * i) (4 * i) t ∧ ZeroInv s dst n i t := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, ⟨by rw [hpc, if_pos hn], by simpa using h11, by simpa using h12,
      fun r _ => rfl, fun A _ => ?_⟩⟩
    unfold zeroed; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 42137 := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u11, u12, ru, mu⟩ := zero_iter hc t hpc' (dst + 8 * i) (n - i - 1)
      hI.x11 (by rw [hI.x12]; congr 1; omega) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : n - i - 1 = 0
      · rw [if_pos h, if_neg (by omega)]
      · rw [if_neg h, if_pos (by omega)]
    · rw [u11, show dst + 8 * i + 8 = dst + 8 * (i + 1) by ring]
    · rw [u12, show n - i - 1 = n - (i + 1) by omega]
    · exact (hI.regs.trans ru).mono (by decide)
    · intro A hA
      rw [mu A hA, hI.mem A hA]
      unfold zeroed
      by_cases hA' : A = dst + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg hA']
        by_cases hin : dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]
theorem zero_spec (s : MachineState) (hpc : s.pc = pcOf 42137) (dst n ret : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 n)
    (h1 : s.getReg .x1 = pcOf ret) (hn : 0 < n) (hn' : n < 2 ^ 32) (hd : dst % 8 = 0)
    (hd' : dst + 8 * n ≤ MEMORY_BYTES) :
    ∃ t, Steps im s (4 * n + 1) (4 * n + 1) t ∧ t.pc = pcOf ret ∧ RegsExcept s t [.x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = zeroed s dst n A) := by
  obtain ⟨t, st, hI⟩ := zero_loop hc s hpc dst n h11 h12 hn hn' hd hd' n le_rfl
  have hpc' : t.pc = pcOf 42141 := by rw [hI.pc, if_neg (by omega)]
  obtain ⟨u, su, pu, ru, fu⟩ := zero_ret hc t hpc' ret (by rw [hI.regs.get (by decide), h1])
  exact ⟨u, st.trans su, pu, (hI.regs.trans ru).mono (by decide), fun A hA => by
    rw [fu A hA (fun h => h), hI.mem A hA]⟩
end
end ClaudeWCT.W9.Machine.Expand.Compact
