import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_EndRoutine
set_option Elab.async false

/-! # The witness-stack post-pass of the img-merged expander (words 49400 .. 54175)

Entered from the `end` routine (`jal 49400`). In order:
1. save the old top chain area `[11768, 15224)` to `0x300000` and the old top path area `[11000, 11768)` to
   `0x301000` (forward word loops);
2. move `[24480, 26096)` up by 16, `[23744, 24464)` by 32, `[15224, 23728)` by 48 and the FTS block
   `[2904, 10568)` by 1224 (backward word loops, highest word first);
3. zero the new top layer area `[11792, 15272)`;
4. copy the 54 top chain values (words 49469 .. 50054, straight line) from the saved chain blocks into the 27 pairs;
5. place the twelve top siblings through two per-row blocks (row `leaf % 64` at `50078 + 32 r`, row
   `leaf / 64 % 64` at `52126 + 32 r`; `leaf = mem[0x20160] >> 52`), each copying six 16-byte siblings from the saved
   path area to the new plan slots;
6. `a0 := 0` and halt (`ecall` at 54175).

This file: the code, its symbolic runs and the machine-level loop/block specifications. -/

namespace ClaudeWCT.W9.Machine.Expand.PostPass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def cfgP : Config := { noAlias := true }

theorem valid8P (X : Nat) (h : X + 8 ≤ 16777216) (h8 : X % 8 = 0) : accessValid (BitVec.ofNat 64 X) 8 = true := by
  rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by rw [show MEMORY_BYTES = 16777216 from rfl]; omega, h8⟩

theorem ult_ofNat (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x < y) := by
  simp [BitVec.ult, toNat_ofNat_lt hx, toNat_ofNat_lt hy]

theorem ofNat_sub8 (c : Nat) (hc : 8 ≤ c) :
    BitVec.ofNat 64 c + 18446744073709551608#64 = BitVec.ofNat 64 (c - 8) := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 8 := ⟨c - 8, by omega⟩
  rw [show k + 8 - 8 = k by omega, ← ofNat_add_ofNat, BitVec.add_assoc,
    show (BitVec.ofNat 64 8 + 18446744073709551608#64 : BitVec 64) = 0#64 by decide]
  exact BitVec.add_zero _

/-! ### Code -/
def cPro1 : List (BitVec 32) := [0x3e37,0xdf8e0e13,0x300eb7,0xe8e93,0x4f37,0xb78f0f13]
def cPro2 : List (BitVec 32) := [0x3e37,0xaf8e0e13,0x301eb7,0xe8e93,0x3f37,0xdf8f0f13]
/-- Forward copy body (both save loops). -/
def fBody : List (BitVec 32) := [0xe3303,0x6eb023,0x8e0e13,0x8e8e93,0xffee68e3]
def cMv1 : List (BitVec 32) := [0x6e37,0x5e8e0e13,0x6f37,0xf98f0f13,0x1000393]
def cMv2 : List (BitVec 32) := [0x6e37,0xf88e0e13,0x6f37,0xcb8f0f13,0x2000393]
def cMv3 : List (BitVec 32) := [0x6e37,0xca8e0e13,0x4f37,0xb70f0f13,0x3000393]
def cMv4 : List (BitVec 32) := [0x3e37,0x940e0e13,0x1f37,0xb50f0f13,0x4c800393]
/-- Backward move body (all four moves). -/
def mBody : List (BitVec 32) := [0xe3303,0x7e0eb3,0x6eb023,0xff8e0e13,0xffcf48e3]
def cZPro : List (BitVec 32) := [0x3e37,0xe10e0e13,0x4f37,0xba8f0f13]
def zBody : List (BitVec 32) := [0xe3023,0x8e0e13,0xffee6ce3]

theorem code_last {b : Nat} {code : List (BitVec 32)} (hlo : 44032 ≤ b)
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (hc : (Images.expandCode_172.drop (b - 44032)).take code.length = code) :
    CodeAt Images.expandImage (pcOf b) code := codeAt_expand_last hlo hb hc

theorem code_pro1 : CodeAt Images.expandImage (pcOf 49400) cPro1 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_pro2 : CodeAt Images.expandImage (pcOf 49411) cPro2 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_f1 : CodeAt Images.expandImage (pcOf 49406) fBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_f2 : CodeAt Images.expandImage (pcOf 49417) fBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_mv1 : CodeAt Images.expandImage (pcOf 49422) cMv1 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_mv2 : CodeAt Images.expandImage (pcOf 49432) cMv2 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_mv3 : CodeAt Images.expandImage (pcOf 49442) cMv3 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_mv4 : CodeAt Images.expandImage (pcOf 49452) cMv4 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_m1 : CodeAt Images.expandImage (pcOf 49427) mBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_m2 : CodeAt Images.expandImage (pcOf 49437) mBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_m3 : CodeAt Images.expandImage (pcOf 49447) mBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_m4 : CodeAt Images.expandImage (pcOf 49457) mBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_zpro : CodeAt Images.expandImage (pcOf 49462) cZPro := code_last (by decide) (by decide) (by decide +kernel)
theorem code_z : CodeAt Images.expandImage (pcOf 49466) zBody := code_last (by decide) (by decide) (by decide +kernel)

/-! ### Symbolic results -/
/-- A prologue loading three constants into `t3`, `t4`/`t2` and `t5`. -/
def proRes (r : Reg) (a b c next n : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x28 (.c (BitVec.ofNat 64 a))).set r (.c (BitVec.ofNat 64 b))).set .x30
      (.c (BitVec.ofNat 64 c)), [], []⟩, .c (pcOf next), .endOfCode, n, n⟩
theorem run_pro1 : symRun cfgP cPro1 (pcOf 49400) 40 = some (proRes .x29 11768 0x300000 15224 49406 6) := by
  kernel_rfl
theorem run_pro2 : symRun cfgP cPro2 (pcOf 49411) 40 = some (proRes .x29 11000 0x301000 11768 49417 6) := by
  kernel_rfl
theorem run_mv1 : symRun cfgP cMv1 (pcOf 49422) 40 = some (proRes .x7 26088 16 24472 49427 5) := by kernel_rfl
theorem run_mv2 : symRun cfgP cMv2 (pcOf 49432) 40 = some (proRes .x7 24456 32 23736 49437 5) := by kernel_rfl
theorem run_mv3 : symRun cfgP cMv3 (pcOf 49442) 40 = some (proRes .x7 23720 48 15216 49447 5) := by kernel_rfl
theorem run_mv4 : symRun cfgP cMv4 (pcOf 49452) 40 = some (proRes .x7 10560 1224 2896 49457 5) := by kernel_rfl
def zProRes : Result :=
  ⟨⟨(RegFile.init.set .x28 (.c (BitVec.ofNat 64 11792))).set .x30 (.c (BitVec.ofNat 64 15272)), [], []⟩,
    .c (pcOf 49466), .endOfCode, 4, 4⟩
theorem run_zpro : symRun cfgP cZPro (pcOf 49462) 40 = some zProRes := by kernel_rfl

def fRes (p : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x6 (.ld (.reg .x28))).set .x28 (.bin .add (.reg .x28) (.c 8#64))).set .x29
      (.bin .add (.reg .x29) (.c 8#64)),
    [(⟨some (.reg .x29), 0#64⟩, .ld (.reg .x28))],
    [.valid ⟨some (.reg .x29), 0#64⟩ 8, .valid ⟨some (.reg .x28), 0#64⟩ 8]⟩,
   .ite .ltu (.bin .add (.reg .x28) (.c 8#64)) (.reg .x30) (.c (pcOf p)) (.c (pcOf (p + 5))), .branch, 5, 5⟩
theorem run_f (p : Nat) (hp : p = 49406 ∨ p = 49417) : symRun cfgP fBody (pcOf p) 40 = some (fRes p) := by
  rcases hp with rfl | rfl <;> kernel_rfl

def mRes (p : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x6 (.ld (.reg .x28))).set .x28 (.bin .add (.reg .x28) (.c 18446744073709551608#64))).set
      .x29 (.bin .add (.reg .x28) (.reg .x7)),
    [(⟨some (.bin .add (.reg .x28) (.reg .x7)), 0#64⟩, .ld (.reg .x28))],
    [.valid ⟨some (.bin .add (.reg .x28) (.reg .x7)), 0#64⟩ 8, .valid ⟨some (.reg .x28), 0#64⟩ 8]⟩,
   .ite .lt (.reg .x30) (.bin .add (.reg .x28) (.c 18446744073709551608#64)) (.c (pcOf p)) (.c (pcOf (p + 5))),
   .branch, 5, 5⟩
theorem run_m (p : Nat) (hp : p = 49427 ∨ p = 49437 ∨ p = 49447 ∨ p = 49457) :
    symRun cfgP mBody (pcOf p) 40 = some (mRes p) := by
  rcases hp with rfl | rfl | rfl | rfl <;> kernel_rfl

def zRes : Result :=
  ⟨⟨RegFile.init.set .x28 (.bin .add (.reg .x28) (.c 8#64)),
    [(⟨some (.reg .x28), 0#64⟩, .c 0#64)],
    [.valid ⟨some (.reg .x28), 0#64⟩ 8]⟩,
   .ite .ltu (.bin .add (.reg .x28) (.c 8#64)) (.reg .x30) (.c (pcOf 49466)) (.c (pcOf 49469)), .branch, 3, 3⟩
theorem run_z : symRun cfgP zBody (pcOf 49466) 40 = some zRes := by kernel_rfl

/-! ### Prologues -/
theorem pro_spec {im : Image} {code : List (BitVec 32)} {p : Nat} {r : Reg} {a b c next n : Nat}
    (hrun : symRun cfgP code (pcOf p) 40 = some (proRes r a b c next n)) (hc : CodeAt im (pcOf p) code)
    (hr : r = .x29 ∨ r = .x7)
    (s : MachineState) (hpc : s.pc = pcOf p) :
    ∃ t, Steps im s n n t ∧ t.pc = pcOf next ∧ t.getReg .x28 = BitVec.ofNat 64 a ∧
      t.getReg r = BitVec.ofNat 64 b ∧ t.getReg .x30 = BitVec.ofNat 64 c ∧
      RegsExcept s t [.x28, r, .x30] ∧ ∀ A, t.getMem A = s.getMem A := by
  refine ⟨_, symRun_sound hrun hc s hpc (by simp [proRes, Result.obligs, Oblig.all]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [proRes, E.eval]
  · rcases hr with rfl | rfl <;> simp [proRes, RegFile.get, RegFile.set, E.eval]
  · rcases hr with rfl | rfl <;> simp [proRes, RegFile.get, RegFile.set, E.eval]
  · rcases hr with rfl | rfl <;> simp [proRes, RegFile.get, RegFile.set, E.eval]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, proRes]
    rcases hr with rfl | rfl <;> cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A; rfl

/-! ### Forward copy loop -/
/-- Memory after `i` words of `[a, a + 8 n)` were copied to `b`. -/
def fcp (M : Nat → Word) (a b i : Nat) (A : Nat) : Word :=
  if b ≤ A ∧ A < b + 8 * i ∧ (A - b) % 8 = 0 then M (a + (A - b)) else M A

theorem f_iter {im : Image} {p : Nat} (hp : p = 49406 ∨ p = 49417) (hc : CodeAt im (pcOf p) fBody)
    (t : MachineState) (hpc : t.pc = pcOf p) (a b e : Nat)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 a) (h29 : t.getReg .x29 = BitVec.ofNat 64 b)
    (h30 : t.getReg .x30 = BitVec.ofNat 64 e)
    (ha : a % 8 = 0) (ha' : a + 8 ≤ 16777216) (hb : b % 8 = 0) (hb' : b + 8 ≤ 16777216) (he : e < 2 ^ 64) :
    ∃ u, Steps im t 5 5 u ∧ u.pc = (if a + 8 < e then pcOf p else pcOf (p + 5)) ∧
      u.getReg .x28 = BitVec.ofNat 64 (a + 8) ∧ u.getReg .x29 = BitVec.ofNat 64 (b + 8) ∧
      RegsExcept t u [.x6, .x28, .x29] ∧
      ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) =
        if A = b then t.getMem (BitVec.ofNat 64 a) else t.getMem (BitVec.ofNat 64 A) := by
  refine ⟨_, symRun_sound (run_f p hp) hc t hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Oblig.all t _
    simp only [fRes, Oblig.all, Oblig.holds, Addr.eval, E.eval, h28, h29, BitVec.add_zero]
    exact ⟨valid8P _ hb' hb, valid8P _ ha' ha⟩
  · simp only [Result.toState_pc, fRes, E.eval, CmpOp.eval, BinOp.eval, h28, h30, ofNat_add8']
    rw [ult_ofNat _ _ (by omega) he]
    by_cases h : a + 8 < e <;> simp [h]
  · simp [fRes, RegFile.get, RegFile.set, E.eval, BinOp.eval, h28, ofNat_add8']
  · simp [fRes, RegFile.get, RegFile.set, E.eval, BinOp.eval, h29, ofNat_add8']
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, fRes]
    cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A hA
    simp only [Result.toState_getMem, fRes, memEval_cons, memEval_nil, Addr.eval, E.eval, h28, h29,
      BitVec.add_zero]
    by_cases hAb : A = b
    · subst hAb; simp
    · rw [if_neg (fun h => hAb ((ofNat_inj hA (by omega)).mp h)), if_neg hAb]

structure FInv (M : Nat → Word) (p a b e i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if a + 8 * i < e then pcOf p else pcOf (p + 5))
  x28 : t.getReg .x28 = BitVec.ofNat 64 (a + 8 * i)
  x29 : t.getReg .x29 = BitVec.ofNat 64 (b + 8 * i)
  x30 : t.getReg .x30 = BitVec.ofNat 64 e
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = fcp M a b i A

theorem f_loop {im : Image} {p : Nat} (hp : p = 49406 ∨ p = 49417) (hc : CodeAt im (pcOf p) fBody)
    (s : MachineState) (M : Nat → Word) (a b n : Nat) (hn : 0 < n)
    (hpc : s.pc = pcOf p) (h28 : s.getReg .x28 = BitVec.ofNat 64 a) (h29 : s.getReg .x29 = BitVec.ofNat 64 b)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 (a + 8 * n))
    (hM : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = M A)
    (ha : a % 8 = 0) (hb : b % 8 = 0) (ha' : a + 8 * n ≤ 16777216) (hb' : b + 8 * n ≤ 16777216)
    (hov : a + 8 * n ≤ b) :
    ∀ i, i ≤ n → ∃ t, Steps im s (5 * i) (5 * i) t ∧ RegsExcept s t [.x6, .x28, .x29] ∧
      FInv M p a b (a + 8 * n) i t := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, RegsExcept.refl _ _, ⟨by rw [hpc, if_pos (by omega)], by simpa using h28,
      by simpa using h29, h30, fun A hA => ?_⟩⟩
    rw [hM A hA]; unfold fcp; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, rt, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf p := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u28, u29, ru, mu⟩ := f_iter hp hc t hpc' (a + 8 * i) (b + 8 * i) (a + 8 * n)
      hI.x28 hI.x29 hI.x30 (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), (rt.trans ru).mono (by decide), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : a + 8 * i + 8 < a + 8 * n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    · rw [u28, show a + 8 * i + 8 = a + 8 * (i + 1) by ring]
    · rw [u29, show b + 8 * i + 8 = b + 8 * (i + 1) by ring]
    · rw [ru.get (by decide), hI.x30]
    · intro A hA
      have hsrc : t.getMem (BitVec.ofNat 64 (a + 8 * i)) = M (a + 8 * i) := by
        rw [hI.mem _ (by omega)]; unfold fcp; rw [if_neg (by omega)]
      rw [mu A hA, hsrc, hI.mem A hA]
      unfold fcp
      by_cases hA' : A = b + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega), show b + 8 * i - b = 8 * i by omega]
      · rw [if_neg hA']
        by_cases hin : b ≤ A ∧ A < b + 8 * i ∧ (A - b) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]

/-! ### Backward move loop -/
/-- Memory after the `i` highest words `T, T - 8, ..` were moved up by `d`. -/
def bmv (M : Nat → Word) (T d i : Nat) (A : Nat) : Word :=
  if T + d + 8 ≤ A + 8 * i ∧ A ≤ T + d ∧ (T + d - A) % 8 = 0 then M (A - d) else M A

theorem m_iter {im : Image} {p : Nat} (hp : p = 49427 ∨ p = 49437 ∨ p = 49447 ∨ p = 49457)
    (hc : CodeAt im (pcOf p) mBody)
    (t : MachineState) (hpc : t.pc = pcOf p) (c d lo : Nat)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 c) (h7 : t.getReg .x7 = BitVec.ofNat 64 d)
    (h30 : t.getReg .x30 = BitVec.ofNat 64 lo)
    (hc8 : c % 8 = 0) (hd8 : d % 8 = 0) (hc' : 8 ≤ c) (hcd : c + d + 8 ≤ 16777216) (hlo : lo < 2 ^ 63) :
    ∃ u, Steps im t 5 5 u ∧ u.pc = (if lo < c - 8 then pcOf p else pcOf (p + 5)) ∧
      u.getReg .x28 = BitVec.ofNat 64 (c - 8) ∧ u.getReg .x7 = BitVec.ofNat 64 d ∧
      RegsExcept t u [.x6, .x28, .x29] ∧
      ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) =
        if A = c + d then t.getMem (BitVec.ofNat 64 c) else t.getMem (BitVec.ofNat 64 A) := by
  refine ⟨_, symRun_sound (run_m p hp) hc t hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Oblig.all t _
    simp only [mRes, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, h28, h7, BitVec.add_zero,
      ofNat_add_ofNat]
    exact ⟨valid8P _ hcd (by omega), valid8P _ (by omega) hc8⟩
  · simp only [Result.toState_pc, mRes, E.eval, CmpOp.eval, BinOp.eval, h28, h30, ofNat_sub8 c hc']
    rw [ofNat_slt _ _ hlo (by omega)]
    by_cases h : lo < c - 8 <;> simp [h]
  · simp [mRes, RegFile.get, RegFile.set, E.eval, BinOp.eval, h28, ofNat_sub8 c hc']
  · simp [mRes, RegFile.get, RegFile.set, RegFile.init, E.eval, h7]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, mRes]
    cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A hA
    simp only [Result.toState_getMem, mRes, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, h28, h7,
      BitVec.add_zero, ofNat_add_ofNat]
    by_cases hAb : A = c + d
    · subst hAb; simp
    · rw [if_neg (fun h => hAb ((ofNat_inj hA (by omega)).mp h)), if_neg hAb]

structure MInv (M : Nat → Word) (p T d lo i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if lo + 8 * i < T then pcOf p else pcOf (p + 5))
  x28 : t.getReg .x28 = BitVec.ofNat 64 (T - 8 * i)
  x7 : t.getReg .x7 = BitVec.ofNat 64 d
  x30 : t.getReg .x30 = BitVec.ofNat 64 lo
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = bmv M T d i A

/-- The move loop over the `n` words `T, T - 8, .., T - 8 (n - 1) = lo + 8` (`lo` is the exclusive bound in `t5`). -/
theorem m_loop {im : Image} {p : Nat} (hp : p = 49427 ∨ p = 49437 ∨ p = 49447 ∨ p = 49457)
    (hc : CodeAt im (pcOf p) mBody)
    (s : MachineState) (M : Nat → Word) (T d lo n : Nat) (hn : 0 < n) (hT : T = lo + 8 * n)
    (hpc : s.pc = pcOf p) (h28 : s.getReg .x28 = BitVec.ofNat 64 T) (h7 : s.getReg .x7 = BitVec.ofNat 64 d)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 lo)
    (hM : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = M A)
    (hT8 : T % 8 = 0) (hd8 : d % 8 = 0) (hd : 0 < d) (hlo : 8 ≤ lo) (hTd : T + d + 8 ≤ 16777216) :
    ∀ i, i ≤ n → ∃ t, Steps im s (5 * i) (5 * i) t ∧ RegsExcept s t [.x6, .x28, .x29] ∧
      MInv M p T d lo i t := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, RegsExcept.refl _ _, ⟨by rw [hpc, if_pos (by omega)], by simpa using h28,
      h7, h30, fun A hA => ?_⟩⟩
    rw [hM A hA]; unfold bmv; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, rt, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf p := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u28, u7, ru, mu⟩ := m_iter hp hc t hpc' (T - 8 * i) d lo hI.x28 hI.x7 hI.x30
      (by omega) hd8 (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), (rt.trans ru).mono (by decide), ⟨?_, ?_, u7, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : lo < T - 8 * i - 8
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    · rw [u28, show T - 8 * i - 8 = T - 8 * (i + 1) by omega]
    · rw [ru.get (by decide), hI.x30]
    · intro A hA
      have hsrc : t.getMem (BitVec.ofNat 64 (T - 8 * i)) = M (T - 8 * i) := by
        rw [hI.mem _ (by omega)]; unfold bmv; rw [if_neg (by omega)]
      rw [mu A hA, hsrc, hI.mem A hA]
      unfold bmv
      by_cases hA' : A = T - 8 * i + d
      · subst hA'; rw [if_pos rfl, if_pos (by omega), show T - 8 * i + d - d = T - 8 * i by omega]
      · rw [if_neg hA']
        by_cases hin : T + d + 8 ≤ A + 8 * i ∧ A ≤ T + d ∧ (T + d - A) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]

/-! ### Zero loop -/
def zfill (M : Nat → Word) (a i : Nat) (A : Nat) : Word :=
  if a ≤ A ∧ A < a + 8 * i ∧ (A - a) % 8 = 0 then 0 else M A

theorem z_iter {im : Image} (hc : CodeAt im (pcOf 49466) zBody)
    (t : MachineState) (hpc : t.pc = pcOf 49466) (a e : Nat)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 a) (h30 : t.getReg .x30 = BitVec.ofNat 64 e)
    (ha : a % 8 = 0) (ha' : a + 8 ≤ 16777216) (he : e < 2 ^ 64) :
    ∃ u, Steps im t 3 3 u ∧ u.pc = (if a + 8 < e then pcOf 49466 else pcOf 49469) ∧
      u.getReg .x28 = BitVec.ofNat 64 (a + 8) ∧ RegsExcept t u [.x28] ∧
      ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = if A = a then 0 else t.getMem (BitVec.ofNat 64 A) := by
  refine ⟨_, symRun_sound run_z hc t hpc ?_, ?_, ?_, ?_, ?_⟩
  · show Oblig.all t _
    simp only [zRes, Oblig.all, Oblig.holds, Addr.eval, E.eval, h28, BitVec.add_zero]
    exact valid8P _ ha' ha
  · simp only [Result.toState_pc, zRes, E.eval, CmpOp.eval, BinOp.eval, h28, h30, ofNat_add8']
    rw [ult_ofNat _ _ (by omega) he]
    by_cases h : a + 8 < e <;> simp [h]
  · simp [zRes, RegFile.get, RegFile.set, E.eval, BinOp.eval, h28, ofNat_add8']
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, zRes]
    cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A hA
    simp only [Result.toState_getMem, zRes, memEval_cons, memEval_nil, Addr.eval, E.eval, h28, BitVec.add_zero]
    by_cases hAb : A = a
    · subst hAb; simp
    · rw [if_neg (fun h => hAb ((ofNat_inj hA (by omega)).mp h)), if_neg hAb]

theorem z_loop {im : Image} (hc : CodeAt im (pcOf 49466) zBody)
    (s : MachineState) (M : Nat → Word) (a n : Nat) (hn : 0 < n)
    (hpc : s.pc = pcOf 49466) (h28 : s.getReg .x28 = BitVec.ofNat 64 a)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 (a + 8 * n))
    (hM : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = M A)
    (ha : a % 8 = 0) (ha' : a + 8 * n ≤ 16777216) :
    ∀ i, i ≤ n → ∃ t, Steps im s (3 * i) (3 * i) t ∧ RegsExcept s t [.x28] ∧
      t.pc = (if a + 8 * i < a + 8 * n then pcOf 49466 else pcOf 49469) ∧
      t.getReg .x28 = BitVec.ofNat 64 (a + 8 * i) ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = zfill M a i A := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, RegsExcept.refl _ _, by rw [hpc, if_pos (by omega)], by simpa using h28,
      fun A hA => ?_⟩
    rw [hM A hA]; unfold zfill; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, rt, pt, t28, mt⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 49466 := by rw [pt, if_pos (by omega)]
    obtain ⟨u, su, pu, u28, ru, mu⟩ := z_iter hc t hpc' (a + 8 * i) (a + 8 * n) t28
      (by rw [rt.get (by decide), h30]) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), (rt.trans ru).mono (by decide), ?_, ?_, ?_⟩
    · rw [pu]; by_cases h : a + 8 * i + 8 < a + 8 * n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    · rw [u28, show a + 8 * i + 8 = a + 8 * (i + 1) by ring]
    · intro A hA
      rw [mu A hA, mt A hA]
      unfold zfill
      by_cases hA' : A = a + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg hA']
        by_cases hin : a ≤ A ∧ A < a + 8 * i ∧ (A - a) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]

end ClaudeWCT.W9.Machine.Expand.PostPass
