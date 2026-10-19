import SigGolfCandidate.ClaudeWCT_W9_T3M_SigCodec48
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsChain
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsRuns
import SigGolfCandidate.T3M_Sign_TopBlocks
import SigGolfCandidate.ClaudeWCT_W9_T3M_Witness_Honest
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_ComposeBack
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_Routine

/-! # H2 expander prologue: the compact signature, un-shifted in place

Word 0 jumps to the prologue (words 42777..42794): it keeps the 14 tail bytes (sig 5296..5311, read as two words;
bytes 5310/5311 are zero), moves sig [2928, 5296) up by 16 bytes (backwards, one word per step), stores the kept
words at sig 2928 (the top sibling with its two omitted bytes zero), clears its scratch registers and jumps to word
1. The machine is then exactly in the old expander's state after word 0, for the full-layout bytes
`sigB (sigDecC b)`. -/

section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Expand (ex_valid ex_ne bytesToWordLE_bytes_e bytes_length_e extractByte_bytesToWordLE_e extractByte_toNat_e word_ext_bytes_e)
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG)
open ClaudeWCT.W9.T3M (sigDig sigDec sigDigests sigDigests_sigDec)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000

def frontTail : List (BitVec 32) := SigGolfCandidate.T3M.Expand.seg_0.drop 1

sym_block h2_front := symRun { noAlias := true } frontTail (pcOf 1) 200

theorem ofNat_sub8 (X : Nat) (hX : 8 ≤ X) (hX' : X < 2 ^ 64) :
    BitVec.ofNat 64 X + BitVec.ofNat 64 (2 ^ 64 - 8) = BitVec.ofNat 64 (X - 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h16 : 16 ≤ 2 ^ 64 := le_trans (by norm_num : (16 : Nat) ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  generalize (2 : Nat) ^ 64 = P at *
  rw [Nat.mod_eq_of_lt hX', Nat.mod_eq_of_lt (show P - 8 < P by omega), Nat.mod_eq_of_lt (show X - 8 < P by omega),
    show X + (P - 8) = (X - 8) + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (show X - 8 < P by omega)]

/-- r3w: unconditional form of a 64-bit subtraction of `ofNat`s (the sixth block stores at `-48(t3)`, `-40(t3)`). -/
theorem ofNat_sub_ofNat_u (x y : Nat) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y = BitVec.ofNat 64 (x + (18446744073709551616 - y % 18446744073709551616)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-! ### The move loop -/

/-! ### The un-shifted memory is the old expander's initial memory for `sigFull b` -/


end ClaudeWCT.W9.Machine.Expand
end

/-! Checked compact-layout prologue prototype; the image entrypoint is not yet redirected. -/
namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def prologueBase : Nat := 44096
def policyAddress : Nat := 417792
def prologueWords : List (BitVec 32) := [0x8eb7,0x470e8e93,0xeb303,0x8eb383,0x303de13,0x66f37,0xf0f13,0x1cf3023,0x1039393,0x103d393,0x27b7,0xe4078793,0x14fe7863,0x8eb7,0x468e8e93,0x8f37,0x4b8f0f13,0x87b7,0xb3078793,0xeb703,0xef3023,0xff8e8e93,0xff8f0f13,0xfefef8e3,0x8f37,0xb70f0f13,0x6f3023,0x7f3423,0x8eb7,0xb28e8e93,0x8f37,0xb68f0f13,0x77b7,0x58078793,0xeb703,0xef3023,0xff8e8e93,0xff8f0f13,0xfefef8e3,0x7f37,0x5b0f0f13,0xf3023,0xf3423,0x7eb7,0x578e8e93,0x7f37,0x5a8f0f13,0x77b7,0x3f078793,0xeb703,0xef3023,0xff8e8e93,0xff8f0f13,0xfefef8e3,0x7f37,0x410f0f13,0xf3023,0xf3423,0x7eb7,0x3e8e8e93,0x7f37,0x408f0f13,0x77b7,0x26078793,0xeb703,0xef3023,0xff8e8e93,0xff8f0f13,0xfefef8e3,0x7f37,0x270f0f13,0xf3023,0xf3423,0x7eb7,0x258e8e93,0x7f37,0x268f0f13,0x77b7,0xd078793,0xeb703,0xef3023,0xff8e8e93,0xff8f0f13,0xfefef8e3,0x7f37,0xd0f0f13,0xf3023,0xf3423,0x313,0x393,0x713,0x793,0xe13,0xe93,0xf13,0xd89d406f,0xb08d506f]
def tailWords : List (BitVec 32) := [0x8eb7,0x470e8e93,0xeb303,0x8eb383,0x303de13,0x66f37,0xf0f13,0x1cf3023,0x1039393,0x103d393]

sym_block tailRun := symRun { noAlias := true } tailWords (pcOf prologueBase) 50

end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def guardWords : List (BitVec 32) := [0x27b7,0xe4078793,0x14fe7863]
sym_block guardRun := symRun { noAlias := true } guardWords (pcOf 44106) 20

theorem guard_spec {im : Image} (hc : CodeAt im (pcOf 44106) guardWords)
    (s : MachineState) (hpc : s.pc = pcOf 44106)
    (H : Nat) (hH : H < 65536) (hr : s.getReg .x28 = BitVec.ofNat 64 H) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if H < 7744 then pcOf 44109 else pcOf 44192) ∧
      RegsExcept s t [.x15] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound guardRun hc s hpc ?_, ?_, ?_, ?_⟩
  · simp [guardRun.res, rv_simp]
  · simp only [Result.toState_pc, guardRun.res, rv_simp, hr]
    by_cases h : H < 7744
    · simp [h, BitVec.ult]
      omega
    · simp [h, BitVec.ult]
      omega
  · intro r h
    cases r <;> simp_all [rv_simp, guardRun.res] <;> rfl
  · intro A hA h
    rfl

#print axioms guard_spec

end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def copyWords : List (BitVec 32) := [0xeb703,0xef3023,0xff8e8e93,0xff8f0f13,0xfefef8e3]
sym_block copyRun := symRun { noAlias := true } copyWords (pcOf (prologueBase + 16)) 50

def copyResult (p : Word) : Result :=
  ⟨copyRun.res.st,
    .ite .geu (.bin .add (.reg .x29) (.c 18446744073709551608)) (.reg .x15)
      (.c (((((p + 4) + 4) + 4) + 4) + 18446744073709551600))
      (.c (((((p + 4) + 4) + 4) + 4) + 4)), .branch, 5, 5⟩

theorem copy_run (p : Word) :
    symRun { noAlias := true } copyWords p 50 = some (copyResult p) := by krfl

#print axioms copy_run
theorem ofNat_sub_eight (n : Nat) :
    (BitVec.ofNat 64 (n + 8) + 18446744073709551608 : Word) = BitVec.ofNat 64 n := by
  rw [show (18446744073709551608 : Word) = BitVec.ofNat 64 (2 ^ 64 - 8) from rfl,
    ofNat_add_ofNat,
    show n + 8 + (2 ^ 64 - 8) = n + 2 ^ 64 by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.add_mod_right]


theorem branch_not_lt {α : Type} (a b : α) (X Z : Nat) :
    (if (!decide (X < Z)) = true then a else b) = (if Z ≤ X then a else b) := by
  by_cases h : X < Z
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, if_false,
      show ¬Z ≤ X by omega]
  · simp only [h, decide_false, Bool.not_false, if_true, show Z ≤ X by omega]


theorem copy_regs (p : Word) (s : MachineState) :
    RegsExcept s ((copyResult p).toState s) [.x14,.x29,.x30] := by
  intro r hr
  rw [Result.toState_getReg]
  change (copyRun.res.st.regs.get r).eval s = s.getReg r
  clear p
  cases r
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hr (by decide)).elim
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hr (by decide)).elim
  · exact (hr (by decide)).elim
  · rfl

#print axioms copy_regs

theorem copy_mem_frame (p : Word) (s : MachineState) (a : Word)
    (ha : a ≠ s.getReg .x30) :
    ((copyResult p).toState s).getMem a = s.getMem a := by
  simp only [Result.toState_getMem, copyResult, copyRun.res, memEval, Addr.eval, E.eval,
    BitVec.add_zero, if_neg ha]

#print axioms copy_mem_frame

theorem copy_frame (p : Word) (s : MachineState) (Y : Nat) (hY : Y < 2 ^ 64)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 Y) :
    Frame s ((copyResult p).toState s) (fun A => A = Y) := by
  intro A hA hne
  apply copy_mem_frame p s (BitVec.ofNat 64 A)
  rw [h30]
  intro he
  exact hne ((ofNat_inj hA hY).mp he)

#print axioms copy_frame

theorem copy_step {im : Image} (p : Word) (hc : CodeAt im p copyWords)
    (s : MachineState) (hpc : s.pc = p) (X Y Z : Nat)
    (hX8 : X % 8 = 0) (hY8 : Y % 8 = 0)
    (hX : 8 ≤ X) (hY : 8 ≤ Y) (hX' : X ≤ 0x8500) (hY' : Y ≤ 0x8500) (hZ : Z < 2 ^ 64)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 X)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 Y)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 Z) :
    ∃ t, Steps im s 5 5 t ∧
      t.pc = (if Z ≤ X - 8 then p else p + 20) ∧
      t.getReg .x29 = BitVec.ofNat 64 (X - 8) ∧
      t.getReg .x30 = BitVec.ofNat 64 (Y - 8) ∧
      t.getMem (BitVec.ofNat 64 Y) = s.getMem (BitVec.ofNat 64 X) ∧
      RegsExcept s t [.x14, .x29, .x30] ∧ Frame s t (fun A => A = Y) := by
  refine ⟨_, symRun_sound (copy_run p) hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [copyResult, copyRun.res, rv_simp, h29, h30, accessValid_iff, MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc, copyResult, E.eval, BinOp.eval, CmpOp.eval, h29, h15]
    have hxsub : (BitVec.ofNat 64 X + 18446744073709551608 : Word) = BitVec.ofNat 64 (X - 8) := by
      simpa only [Nat.sub_add_cancel hX] using ofNat_sub_eight (X - 8)
    rw [hxsub]
    simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show X - 8 < 2 ^ 64 by omega), Nat.mod_eq_of_lt hZ]
    have hb : (((p + 4) + 4) + 4) + 4 + 18446744073709551600 = p := by
      simp only [BitVec.add_assoc]
      change p + 0 = p
      exact BitVec.add_zero p
    have he : (((p + 4) + 4) + 4) + 4 + 4 = p + 20 := by
      simp only [BitVec.add_assoc]
      rfl
    rw [hb, he]
    exact branch_not_lt p (p + 20) (X - 8) Z
  · rw [Result.toState_getReg]
    change s.getReg .x29 + 18446744073709551608 = _
    rw [h29]
    simpa only [Nat.sub_add_cancel hX] using ofNat_sub_eight (X - 8)
  · rw [Result.toState_getReg]
    change s.getReg .x30 + 18446744073709551608 = _
    rw [h30]
    simpa only [Nat.sub_add_cancel hY] using ofNat_sub_eight (Y - 8)
  · simp only [Result.toState_getMem, copyResult, copyRun.res]
    t3n [h29, h30]
    simp only [Nat.add_zero, if_true]
  · exact copy_regs p s
  · exact copy_frame p s Y (by omega) h30

#print axioms copy_step

theorem copy_loop {im : Image} (p : Word) (hc : CodeAt im p copyWords)
    (S D : Nat) (hS8 : S % 8 = 0) (hD8 : D % 8 = 0) (hS : 8 ≤ S) (hSD : S < D) :
    ∀ n (s : MachineState), D + 8 * n ≤ 0x8500 → s.pc = p →
      s.getReg .x29 = BitVec.ofNat 64 (S + 8 * n) →
      s.getReg .x30 = BitVec.ofNat 64 (D + 8 * n) →
      s.getReg .x15 = BitVec.ofNat 64 S →
      ∃ t, Steps im s (5 * (n + 1)) (5 * (n + 1)) t ∧ t.pc = p + 20 ∧
        t.getReg .x29 = BitVec.ofNat 64 (S - 8) ∧
        t.getReg .x30 = BitVec.ofNat 64 (D - 8) ∧
        (∀ i, i ≤ n → t.getMem (BitVec.ofNat 64 (D + 8 * i)) =
          s.getMem (BitVec.ofNat 64 (S + 8 * i))) ∧
        RegsExcept s t [.x14, .x29, .x30] ∧
        Frame s t (fun A => D ≤ A ∧ A < D + 8 * (n + 1)) := by
  intro n
  induction n with
  | zero =>
      intro s hbound hpc h29 h30 h15
      simp only [Nat.mul_zero, Nat.add_zero] at h29 h30 hbound
      obtain ⟨t, st, pt, r29, r30, mt, rt, ft⟩ := copy_step p hc s hpc S D S
        hS8 hD8 hS (by omega) (by omega) hbound (by omega) h29 h30 h15
      refine ⟨t, by simpa using st, ?_, r29, r30, ?_, rt, ?_⟩
      · simpa only [show ¬S ≤ S - 8 by omega, if_false] using pt
      · intro i hi
        have hi0 : i = 0 := by omega
        simpa only [hi0, Nat.mul_zero, Nat.add_zero] using mt
      · exact ft.mono (by intro A _ hA; omega)
  | succ n ih =>
      intro s hbound hpc h29 h30 h15
      obtain ⟨u, su, pu, u29, u30, mu, ru, fu⟩ := copy_step p hc s hpc
        (S + 8 * (n + 1)) (D + 8 * (n + 1)) S
        (by omega) (by omega) (by omega) (by omega) (by omega) hbound (by omega) h29 h30 h15
      have hu29 : u.getReg .x29 = BitVec.ofNat 64 (S + 8 * n) := by
        rw [u29, show S + 8 * (n + 1) - 8 = S + 8 * n by omega]
      have hu30 : u.getReg .x30 = BitVec.ofNat 64 (D + 8 * n) := by
        rw [u30, show D + 8 * (n + 1) - 8 = D + 8 * n by omega]
      have hpu : u.pc = p := by
        simpa only [show S ≤ S + 8 * (n + 1) - 8 by omega, if_true] using pu
      obtain ⟨t, ut, pt, r29, r30, mt, rt, ft⟩ := ih u (by omega) hpu hu29 hu30
        ((ru .x15 (by simp)).trans h15)
      refine ⟨t, ?_, pt, r29, r30, ?_, ?_, ?_⟩
      · convert su.trans ut using 1 <;> omega
      · intro i hi
        by_cases hin : i ≤ n
        · rw [mt i hin]
          exact fu _ (by omega) (by omega)
        · have hi' : i = n + 1 := by omega
          subst i
          rw [ft _ (by omega) (by omega)]
          exact mu
      · intro r hr
        exact (rt r hr).trans (ru r hr)
      · exact (fu.trans ft).mono (by intro A _ hA; rcases hA with hA | hA <;> omega)

#print axioms copy_loop


end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def mainHighSetupWords : List (BitVec 32) := [0x8eb7,0x468e8e93,0x8f37,0x4b8f0f13,0x87b7,0xb3078793]
sym_block mainHighSetup := symRun { noAlias := true } mainHighSetupWords (pcOf 44109) 30

theorem mainHigh_setup {im : Image} (hc : CodeAt im (pcOf 44109) mainHighSetupWords)
    (s : MachineState) (hpc : s.pc = pcOf 44109) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 44115 ∧
      t.getReg .x29 = BitVec.ofNat 64 33896 ∧
      t.getReg .x30 = BitVec.ofNat 64 33976 ∧
      t.getReg .x15 = BitVec.ofNat 64 31536 ∧
      RegsExcept s t [.x15,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound mainHighSetup hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mainHighSetup.res, rv_simp]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA h
    rfl

theorem mainHigh_move {im : Image} (hs : CodeAt im (pcOf 44109) mainHighSetupWords)
    (hc : CodeAt im (pcOf 44115) copyWords)
    (s : MachineState) (hpc : s.pc = pcOf 44109) :
    ∃ t, Steps im s 1486 1486 t ∧ t.pc = pcOf 44120 ∧
      (∀ i, i ≤ 295 → t.getMem (BitVec.ofNat 64 (31616 + 8 * i)) =
        s.getMem (BitVec.ofNat 64 (31536 + 8 * i))) ∧
      RegsExcept s t [.x14,.x15,.x29,.x30] ∧
      Frame s t (fun A => 31616 ≤ A ∧ A < 33984) := by
  obtain ⟨u,su,pu,u29,u30,u15,ru,fu⟩ := mainHigh_setup hs s hpc
  obtain ⟨t,ut,pt,r29,r30,mt,rt,ft⟩ := copy_loop (pcOf 44115) hc 31536 31616
    (by decide) (by decide) (by decide) (by decide) 295 u (by decide) pu u29 u30 u15
  refine ⟨t, su.trans ut, ?_, ?_, ?_, ?_⟩
  · exact pt
  · intro i hi
    rw [mt i hi]
    exact fu _ (by omega) (by simp)
  · exact (ru.trans rt).mono (by decide)
  · exact (fu.trans ft).mono (by intro A _ h; rcases h with h | h; exact h.elim; exact h)

#print axioms mainHigh_move


def middleSetupWords : List (BitVec 32) := [0x8eb7,0xb28e8e93,0x8f37,0xb68f0f13,0x77b7,0x58078793]
sym_block middleSetup := symRun { noAlias := true } middleSetupWords (pcOf 44124) 30

theorem middle_setup {im : Image} (hc : CodeAt im (pcOf 44124) middleSetupWords)
    (s : MachineState) (hpc : s.pc = pcOf 44124) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 44130 ∧
      t.getReg .x29 = BitVec.ofNat 64 31528 ∧
      t.getReg .x30 = BitVec.ofNat 64 31592 ∧
      t.getReg .x15 = BitVec.ofNat 64 30080 ∧
      RegsExcept s t [.x15,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound middleSetup hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [middleSetup.res, rv_simp]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA h
    rfl

theorem middle_move {im : Image} (hs : CodeAt im (pcOf 44124) middleSetupWords)
    (hc : CodeAt im (pcOf 44130) copyWords)
    (s : MachineState) (hpc : s.pc = pcOf 44124) :
    ∃ t, Steps im s 916 916 t ∧ t.pc = pcOf 44135 ∧
      (∀ i, i ≤ 181 → t.getMem (BitVec.ofNat 64 (30144 + 8 * i)) =
        s.getMem (BitVec.ofNat 64 (30080 + 8 * i))) ∧
      RegsExcept s t [.x14,.x15,.x29,.x30] ∧
      Frame s t (fun A => 30144 ≤ A ∧ A < 31600) := by
  obtain ⟨u,su,pu,u29,u30,u15,ru,fu⟩ := middle_setup hs s hpc
  obtain ⟨t,ut,pt,r29,r30,mt,rt,ft⟩ := copy_loop (pcOf 44130) hc 30080 30144
    (by decide) (by decide) (by decide) (by decide) 181 u (by decide) pu u29 u30 u15
  refine ⟨t, su.trans ut, ?_, ?_, ?_, ?_⟩
  · exact pt
  · intro i hi
    rw [mt i hi]
    exact fu _ (by omega) (by simp)
  · exact (ru.trans rt).mono (by decide)
  · exact (fu.trans ft).mono (by intro A _ h; rcases h with h | h; exact h.elim; exact h)

#print axioms middle_move


def pair3SetupWords : List (BitVec 32) := [0x7eb7,0x578e8e93,0x7f37,0x5a8f0f13,0x77b7,0x3f078793]
sym_block pair3Setup := symRun { noAlias := true } pair3SetupWords (pcOf 44139) 30

theorem pair3_setup {im : Image} (hc : CodeAt im (pcOf 44139) pair3SetupWords)
    (s : MachineState) (hpc : s.pc = pcOf 44139) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 44145 ∧
      t.getReg .x29 = BitVec.ofNat 64 30072 ∧
      t.getReg .x30 = BitVec.ofNat 64 30120 ∧
      t.getReg .x15 = BitVec.ofNat 64 29680 ∧
      RegsExcept s t [.x15,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound pair3Setup hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pair3Setup.res, rv_simp]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA h
    rfl

theorem pair3_move {im : Image} (hs : CodeAt im (pcOf 44139) pair3SetupWords)
    (hc : CodeAt im (pcOf 44145) copyWords)
    (s : MachineState) (hpc : s.pc = pcOf 44139) :
    ∃ t, Steps im s 256 256 t ∧ t.pc = pcOf 44150 ∧
      (∀ i, i ≤ 49 → t.getMem (BitVec.ofNat 64 (29728 + 8 * i)) =
        s.getMem (BitVec.ofNat 64 (29680 + 8 * i))) ∧
      RegsExcept s t [.x14,.x15,.x29,.x30] ∧
      Frame s t (fun A => 29728 ≤ A ∧ A < 30128) := by
  obtain ⟨u,su,pu,u29,u30,u15,ru,fu⟩ := pair3_setup hs s hpc
  obtain ⟨t,ut,pt,r29,r30,mt,rt,ft⟩ := copy_loop (pcOf 44145) hc 29680 29728
    (by decide) (by decide) (by decide) (by decide) 49 u (by decide) pu u29 u30 u15
  refine ⟨t, su.trans ut, ?_, ?_, ?_, ?_⟩
  · exact pt
  · intro i hi
    rw [mt i hi]
    exact fu _ (by omega) (by simp)
  · exact (ru.trans rt).mono (by decide)
  · exact (fu.trans ft).mono (by intro A _ h; rcases h with h | h; exact h.elim; exact h)

#print axioms pair3_move


def pair2SetupWords : List (BitVec 32) := [0x7eb7,0x3e8e8e93,0x7f37,0x408f0f13,0x77b7,0x26078793]
sym_block pair2Setup := symRun { noAlias := true } pair2SetupWords (pcOf 44154) 30

theorem pair2_setup {im : Image} (hc : CodeAt im (pcOf 44154) pair2SetupWords)
    (s : MachineState) (hpc : s.pc = pcOf 44154) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 44160 ∧
      t.getReg .x29 = BitVec.ofNat 64 29672 ∧
      t.getReg .x30 = BitVec.ofNat 64 29704 ∧
      t.getReg .x15 = BitVec.ofNat 64 29280 ∧
      RegsExcept s t [.x15,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound pair2Setup hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pair2Setup.res, rv_simp]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA h
    rfl

theorem pair2_move {im : Image} (hs : CodeAt im (pcOf 44154) pair2SetupWords)
    (hc : CodeAt im (pcOf 44160) copyWords)
    (s : MachineState) (hpc : s.pc = pcOf 44154) :
    ∃ t, Steps im s 256 256 t ∧ t.pc = pcOf 44165 ∧
      (∀ i, i ≤ 49 → t.getMem (BitVec.ofNat 64 (29312 + 8 * i)) =
        s.getMem (BitVec.ofNat 64 (29280 + 8 * i))) ∧
      RegsExcept s t [.x14,.x15,.x29,.x30] ∧
      Frame s t (fun A => 29312 ≤ A ∧ A < 29712) := by
  obtain ⟨u,su,pu,u29,u30,u15,ru,fu⟩ := pair2_setup hs s hpc
  obtain ⟨t,ut,pt,r29,r30,mt,rt,ft⟩ := copy_loop (pcOf 44160) hc 29280 29312
    (by decide) (by decide) (by decide) (by decide) 49 u (by decide) pu u29 u30 u15
  refine ⟨t, su.trans ut, ?_, ?_, ?_, ?_⟩
  · exact pt
  · intro i hi
    rw [mt i hi]
    exact fu _ (by omega) (by simp)
  · exact (ru.trans rt).mono (by decide)
  · exact (fu.trans ft).mono (by intro A _ h; rcases h with h | h; exact h.elim; exact h)

#print axioms pair2_move


def pair1SetupWords : List (BitVec 32) := [0x7eb7,0x258e8e93,0x7f37,0x268f0f13,0x77b7,0xd078793]
sym_block pair1Setup := symRun { noAlias := true } pair1SetupWords (pcOf 44169) 30

theorem pair1_setup {im : Image} (hc : CodeAt im (pcOf 44169) pair1SetupWords)
    (s : MachineState) (hpc : s.pc = pcOf 44169) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 44175 ∧
      t.getReg .x29 = BitVec.ofNat 64 29272 ∧
      t.getReg .x30 = BitVec.ofNat 64 29288 ∧
      t.getReg .x15 = BitVec.ofNat 64 28880 ∧
      RegsExcept s t [.x15,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound pair1Setup hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pair1Setup.res, rv_simp]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA h
    rfl

theorem pair1_move {im : Image} (hs : CodeAt im (pcOf 44169) pair1SetupWords)
    (hc : CodeAt im (pcOf 44175) copyWords)
    (s : MachineState) (hpc : s.pc = pcOf 44169) :
    ∃ t, Steps im s 256 256 t ∧ t.pc = pcOf 44180 ∧
      (∀ i, i ≤ 49 → t.getMem (BitVec.ofNat 64 (28896 + 8 * i)) =
        s.getMem (BitVec.ofNat 64 (28880 + 8 * i))) ∧
      RegsExcept s t [.x14,.x15,.x29,.x30] ∧
      Frame s t (fun A => 28896 ≤ A ∧ A < 29296) := by
  obtain ⟨u,su,pu,u29,u30,u15,ru,fu⟩ := pair1_setup hs s hpc
  obtain ⟨t,ut,pt,r29,r30,mt,rt,ft⟩ := copy_loop (pcOf 44175) hc 28880 28896
    (by decide) (by decide) (by decide) (by decide) 49 u (by decide) pu u29 u30 u15
  refine ⟨t, su.trans ut, ?_, ?_, ?_, ?_⟩
  · exact pt
  · intro i hi
    rw [mt i hi]
    exact fu _ (by omega) (by simp)
  · exact (ru.trans rt).mono (by decide)
  · exact (fu.trans ft).mono (by intro A _ h; rcases h with h | h; exact h.elim; exact h)

#print axioms pair1_move

end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def restoreTailWords : List (BitVec 32) := [0x8f37,0xb70f0f13,0x6f3023,0x7f3423]
sym_block restoreTailRun := symRun { noAlias := true } restoreTailWords (pcOf 44120) 20

theorem restoreTail_spec {im : Image} (hc : CodeAt im (pcOf 44120) restoreTailWords)
    (s : MachineState) (hpc : s.pc = pcOf 44120) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 44124 ∧
      t.getMem 31600 = s.getReg .x6 ∧ t.getMem 31608 = s.getReg .x7 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun A => A = 31600 ∨ A = 31608) := by
  refine ⟨_, symRun_sound restoreTailRun hc s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [restoreTailRun.res, rv_simp, accessValid_iff, MEMORY_BYTES]
  · rfl
  · simp [restoreTailRun.res, rv_simp]
  · simp [restoreTailRun.res, rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hne
    simp only [Result.toState_getMem, restoreTailRun.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by omega), if_neg (by omega)]

#print axioms restoreTail_spec

def zero91Words : List (BitVec 32) := [0x7f37,0x5b0f0f13,0xf3023,0xf3423]
sym_block zero91Run := symRun { noAlias := true } zero91Words (pcOf 44135) 20

theorem zero91_spec {im : Image} (hc : CodeAt im (pcOf 44135) zero91Words)
    (s : MachineState) (hpc : s.pc = pcOf 44135) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 44139 ∧
      t.getMem 30128 = 0 ∧ t.getMem 30136 = 0 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun A => A = 30128 ∨ A = 30136) := by
  refine ⟨_, symRun_sound zero91Run hc s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [zero91Run.res, rv_simp, accessValid_iff, MEMORY_BYTES]
  · rfl
  · simp [zero91Run.res, rv_simp]
  · simp [zero91Run.res, rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hne
    simp only [Result.toState_getMem, zero91Run.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by omega), if_neg (by omega)]

#print axioms zero91_spec

def zero65Words : List (BitVec 32) := [0x7f37,0x410f0f13,0xf3023,0xf3423]
sym_block zero65Run := symRun { noAlias := true } zero65Words (pcOf 44150) 20

theorem zero65_spec {im : Image} (hc : CodeAt im (pcOf 44150) zero65Words)
    (s : MachineState) (hpc : s.pc = pcOf 44150) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 44154 ∧
      t.getMem 29712 = 0 ∧ t.getMem 29720 = 0 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun A => A = 29712 ∨ A = 29720) := by
  refine ⟨_, symRun_sound zero65Run hc s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [zero65Run.res, rv_simp, accessValid_iff, MEMORY_BYTES]
  · rfl
  · simp [zero65Run.res, rv_simp]
  · simp [zero65Run.res, rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hne
    simp only [Result.toState_getMem, zero65Run.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by omega), if_neg (by omega)]

#print axioms zero65_spec

def zero39Words : List (BitVec 32) := [0x7f37,0x270f0f13,0xf3023,0xf3423]
sym_block zero39Run := symRun { noAlias := true } zero39Words (pcOf 44165) 20

theorem zero39_spec {im : Image} (hc : CodeAt im (pcOf 44165) zero39Words)
    (s : MachineState) (hpc : s.pc = pcOf 44165) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 44169 ∧
      t.getMem 29296 = 0 ∧ t.getMem 29304 = 0 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun A => A = 29296 ∨ A = 29304) := by
  refine ⟨_, symRun_sound zero39Run hc s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [zero39Run.res, rv_simp, accessValid_iff, MEMORY_BYTES]
  · rfl
  · simp [zero39Run.res, rv_simp]
  · simp [zero39Run.res, rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hne
    simp only [Result.toState_getMem, zero39Run.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by omega), if_neg (by omega)]

#print axioms zero39_spec

def zero13Words : List (BitVec 32) := [0x7f37,0xd0f0f13,0xf3023,0xf3423]
sym_block zero13Run := symRun { noAlias := true } zero13Words (pcOf 44180) 20

theorem zero13_spec {im : Image} (hc : CodeAt im (pcOf 44180) zero13Words)
    (s : MachineState) (hpc : s.pc = pcOf 44180) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 44184 ∧
      t.getMem 28880 = 0 ∧ t.getMem 28888 = 0 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun A => A = 28880 ∨ A = 28888) := by
  refine ⟨_, symRun_sound zero13Run hc s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [zero13Run.res, rv_simp, accessValid_iff, MEMORY_BYTES]
  · rfl
  · simp [zero13Run.res, rv_simp]
  · simp [zero13Run.res, rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hne
    simp only [Result.toState_getMem, zero13Run.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by omega), if_neg (by omega)]

#print axioms zero13_spec

def cleanupWords : List (BitVec 32) := [0x313,0x393,0x713,0x793,0xe13,0xe93,0xf13,0xd89d406f]
sym_block cleanupRun := symRun { noAlias := true } cleanupWords (pcOf 44184) 20

theorem cleanup_spec {im : Image} (hc : CodeAt im (pcOf 44184) cleanupWords)
    (s : MachineState) (hpc : s.pc = pcOf 44184) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = pcOf 1 ∧
      (∀ r ∈ [.x6,.x7,.x14,.x15,.x28,.x29,.x30], t.getReg r = 0) ∧
      RegsExcept s t [.x6,.x7,.x14,.x15,.x28,.x29,.x30] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound cleanupRun hc s hpc ?_, ?_, ?_, ?_, ?_⟩
  · simp [cleanupRun.res, rv_simp]
  · rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A _ _; rfl

#print axioms cleanup_spec

end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem tail_full {im : Image} (hc : CodeAt im (pcOf prologueBase) tailWords)
    (s : MachineState) (hpc : s.pc = pcOf prologueBase) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf (prologueBase + 10) ∧
      t.getReg .x6 = s.getMem 0x8470 ∧
      t.getReg .x7 = (s.getMem 0x8478 <<< 16) >>> 16 ∧
      t.getReg .x28 = s.getMem 0x8478 >>> 48 ∧
      t.getMem (BitVec.ofNat 64 policyAddress) = s.getMem 0x8478 >>> 48 ∧
      RegsExcept s t [.x6,.x7,.x28,.x29,.x30] ∧
      Frame s t (fun A => A = policyAddress) := by
  refine ⟨_, symRun_sound tailRun hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [tailRun.res, rv_simp, accessValid_iff, MEMORY_BYTES, prologueBase, policyAddress]
  · rfl
  · simp only [Result.toState_getReg, tailRun.res]; t3n []
  · simp only [Result.toState_getReg, tailRun.res]; t3n []
  · simp only [Result.toState_getReg, tailRun.res]; t3n []
  · simp only [Result.toState_getMem, tailRun.res]; t3n [policyAddress]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hne
    simp only [Result.toState_getMem, tailRun.res]
    t3n [policyAddress]
    rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by simpa [policyAddress] using hne)]

structure AdapterCodeAt (im : Image) : Prop where
  tail : CodeAt im (pcOf 44096) tailWords
  guard : CodeAt im (pcOf 44106) guardWords
  mainHighSetup : CodeAt im (pcOf 44109) mainHighSetupWords
  mainHighLoop : CodeAt im (pcOf 44115) copyWords
  middleSetup : CodeAt im (pcOf 44124) middleSetupWords
  middleLoop : CodeAt im (pcOf 44130) copyWords
  pair3Setup : CodeAt im (pcOf 44139) pair3SetupWords
  pair3Loop : CodeAt im (pcOf 44145) copyWords
  pair2Setup : CodeAt im (pcOf 44154) pair2SetupWords
  pair2Loop : CodeAt im (pcOf 44160) copyWords
  pair1Setup : CodeAt im (pcOf 44169) pair1SetupWords
  pair1Loop : CodeAt im (pcOf 44175) copyWords
  restoreTail : CodeAt im (pcOf 44120) restoreTailWords
  zero91 : CodeAt im (pcOf 44135) zero91Words
  zero65 : CodeAt im (pcOf 44150) zero65Words
  zero39 : CodeAt im (pcOf 44165) zero39Words
  zero13 : CodeAt im (pcOf 44180) zero13Words
  cleanup : CodeAt im (pcOf 44184) cleanupWords

theorem adapter_spec {im : Image} (hc : AdapterCodeAt im)
    (s : MachineState) (hpc : s.pc = pcOf 44096)
    (H : Nat) (hH : H < 7744) (hh : s.getMem 0x8478 >>> 48 = BitVec.ofNat 64 H) :
    ∃ t, Steps im s 3211 3211 t ∧ t.pc = pcOf 1 ∧
      (∀ r ∈ [.x6,.x7,.x14,.x15,.x28,.x29,.x30], t.getReg r = 0) ∧
      RegsExcept s t [.x6,.x7,.x14,.x15,.x28,.x29,.x30] ∧
      t.getMem (BitVec.ofNat 64 policyAddress) = BitVec.ofNat 64 H ∧
      t.getMem 31600 = s.getMem 33904 ∧
      t.getMem 31608 = (s.getMem 33912 <<< 16) >>> 16 ∧
      (∀ i, i ≤ 295 → t.getMem (BitVec.ofNat 64 (31616 + 8 * i)) = s.getMem (BitVec.ofNat 64 (31536 + 8 * i))) ∧
      (∀ i, i ≤ 181 → t.getMem (BitVec.ofNat 64 (30144 + 8 * i)) = s.getMem (BitVec.ofNat 64 (30080 + 8 * i))) ∧
      (∀ i, i ≤ 49 → t.getMem (BitVec.ofNat 64 (29728 + 8 * i)) = s.getMem (BitVec.ofNat 64 (29680 + 8 * i))) ∧
      (∀ i, i ≤ 49 → t.getMem (BitVec.ofNat 64 (29312 + 8 * i)) = s.getMem (BitVec.ofNat 64 (29280 + 8 * i))) ∧
      (∀ i, i ≤ 49 → t.getMem (BitVec.ofNat 64 (28896 + 8 * i)) = s.getMem (BitVec.ofNat 64 (28880 + 8 * i))) ∧
      t.getMem 30128 = 0 ∧ t.getMem 30136 = 0 ∧
      t.getMem 29712 = 0 ∧ t.getMem 29720 = 0 ∧
      t.getMem 29296 = 0 ∧ t.getMem 29304 = 0 ∧
      t.getMem 28880 = 0 ∧ t.getMem 28888 = 0 ∧
      Frame s t (fun A => A = policyAddress ∨ (0x70d0 ≤ A ∧ A < 0x84c0)) := by
  obtain ⟨s1, st1, pc1, x61, x71, x281, meta1, r1, f1⟩ := tail_full hc.tail s hpc
  obtain ⟨s2, st2, pc2, r2, f2⟩ := guard_spec hc.guard s1 pc1 H (by omega) (x281.trans hh)
  rw [if_pos hH] at pc2
  obtain ⟨s3, st3, pc3, m3, r3, f3⟩ := mainHigh_move hc.mainHighSetup hc.mainHighLoop s2 pc2
  obtain ⟨s4, st4, pc4, m4a, m4b, r4, f4⟩ := restoreTail_spec hc.restoreTail s3 pc3
  obtain ⟨s5, st5, pc5, m5, r5, f5⟩ := middle_move hc.middleSetup hc.middleLoop s4 pc4
  obtain ⟨s6, st6, pc6, m6a, m6b, r6, f6⟩ := zero91_spec hc.zero91 s5 pc5
  obtain ⟨s7, st7, pc7, m7, r7, f7⟩ := pair3_move hc.pair3Setup hc.pair3Loop s6 pc6
  obtain ⟨s8, st8, pc8, m8a, m8b, r8, f8⟩ := zero65_spec hc.zero65 s7 pc7
  obtain ⟨s9, st9, pc9, m9, r9, f9⟩ := pair2_move hc.pair2Setup hc.pair2Loop s8 pc8
  obtain ⟨s10, st10, pc10, m10a, m10b, r10, f10⟩ := zero39_spec hc.zero39 s9 pc9
  obtain ⟨s11, st11, pc11, m11, r11, f11⟩ := pair1_move hc.pair1Setup hc.pair1Loop s10 pc10
  obtain ⟨s12, st12, pc12, m12a, m12b, r12, f12⟩ := zero13_spec hc.zero13 s11 pc11
  obtain ⟨t, st13, pc13, zeros, r13, f13⟩ := cleanup_spec hc.cleanup s12 pc12
  change s4.getMem (BitVec.ofNat 64 31600) = _ at m4a
  change s4.getMem (BitVec.ofNat 64 31608) = _ at m4b
  change s6.getMem (BitVec.ofNat 64 30128) = _ at m6a
  change s6.getMem (BitVec.ofNat 64 30136) = _ at m6b
  change s8.getMem (BitVec.ofNat 64 29712) = _ at m8a
  change s8.getMem (BitVec.ofNat 64 29720) = _ at m8b
  change s10.getMem (BitVec.ofNat 64 29296) = _ at m10a
  change s10.getMem (BitVec.ofNat 64 29304) = _ at m10b
  change s12.getMem (BitVec.ofNat 64 28880) = _ at m12a
  change s12.getMem (BitVec.ofNat 64 28888) = _ at m12b
  refine ⟨t, ?_, pc13, zeros, ?_, ?_, ?_, ?_, ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
  · exact ((((((((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans st8).trans st9).trans st10).trans st11).trans st12).trans st13)
  · exact ((((((((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans r7).trans r8).trans r9).trans r10).trans r11).trans r12).trans r13).mono (by decide)
  · rw [f13 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f4 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f3 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f2 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), meta1, hh]
  · change t.getMem (BitVec.ofNat 64 31600) = _
    rw [f13 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m4a, r3.get (by decide), r2.get (by decide), x61]
  · change t.getMem (BitVec.ofNat 64 31608) = _
    rw [f13 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m4b, r3.get (by decide), r2.get (by decide), x71]
  · intro i hi
    rw [f13 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f4 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m3 i hi, f2 (31536 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f1 (31536 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega)]
  · intro i hi
    rw [f13 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m5 i hi, f4 (30080 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f3 (30080 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f2 (30080 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f1 (30080 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega)]
  · intro i hi
    rw [f13 (29728 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 (29728 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 (29728 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 (29728 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 (29728 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 (29728 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m7 i hi, f6 (29680 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 (29680 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f4 (29680 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f3 (29680 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f2 (29680 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f1 (29680 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega)]
  · intro i hi
    rw [f13 (29312 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 (29312 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 (29312 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 (29312 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m9 i hi, f8 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f4 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f3 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f2 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f1 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega)]
  · intro i hi
    rw [f13 (28896 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 (28896 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m11 i hi, f10 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f4 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f3 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f2 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f1 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega)]
  · change t.getMem (BitVec.ofNat 64 30128) = _
    rw [f13 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m6a]
  · change t.getMem (BitVec.ofNat 64 30136) = _
    rw [f13 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m6b]
  · change t.getMem (BitVec.ofNat 64 29712) = _
    rw [f13 29712 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 29712 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 29712 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 29712 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 29712 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m8a]
  · change t.getMem (BitVec.ofNat 64 29720) = _
    rw [f13 29720 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 29720 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 29720 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 29720 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 29720 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m8b]
  · change t.getMem (BitVec.ofNat 64 29296) = _
    rw [f13 29296 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 29296 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 29296 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m10a]
  · change t.getMem (BitVec.ofNat 64 29304) = _
    rw [f13 29304 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 29304 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 29304 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m10b]
  · change t.getMem (BitVec.ofNat 64 28880) = _
    rw [f13 28880 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m12a]
  · change t.getMem (BitVec.ofNat 64 28888) = _
    rw [f13 28888 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m12b]
  · exact ((((((((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans f9).trans f10).trans f11).trans f12).trans f13).mono (by intro A _ h; dsimp [policyAddress] at h ⊢; rcases h with ((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) <;> first | exact False.elim h | omega)

#print axioms adapter_spec
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
def adapterLayout : SigGolfCandidate.Rv.Layout := [(0, tailWords), (10, guardWords), (13, mainHighSetupWords), (19, copyWords), (24, restoreTailWords), (28, middleSetupWords), (34, copyWords), (39, zero91Words), (43, pair3SetupWords), (49, copyWords), (54, zero65Words), (58, pair2SetupWords), (64, copyWords), (69, zero39Words), (73, pair1SetupWords), (79, copyWords), (84, zero13Words), (88, cleanupWords), (96, [0xb08d506f])]

theorem adapterLayout_ok : layoutOk 0 adapterLayout = true := by decide +kernel

theorem adapterLayout_code : layoutCode adapterLayout = prologueWords := by decide +kernel

theorem adapter_codeAt {im : Image} (hc : CodeAt im (pcOf 44096) prologueWords) :
    AdapterCodeAt im := by
  have hl : CodeAt im (pcOf 44096) (layoutCode adapterLayout) := by
    rw [adapterLayout_code]; exact hc
  constructor
  · exact codeAt_sublayout hl adapterLayout_ok (i := 0) (o := 0) (seg := tailWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 1) (o := 10) (seg := guardWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 2) (o := 13) (seg := mainHighSetupWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 3) (o := 19) (seg := copyWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 5) (o := 28) (seg := middleSetupWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 6) (o := 34) (seg := copyWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 8) (o := 43) (seg := pair3SetupWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 9) (o := 49) (seg := copyWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 11) (o := 58) (seg := pair2SetupWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 12) (o := 64) (seg := copyWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 14) (o := 73) (seg := pair1SetupWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 15) (o := 79) (seg := copyWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 4) (o := 24) (seg := restoreTailWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 7) (o := 39) (seg := zero91Words) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 10) (o := 54) (seg := zero65Words) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 13) (o := 69) (seg := zero39Words) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 16) (o := 84) (seg := zero13Words) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 17) (o := 88) (seg := cleanupWords) (by decide +kernel)

#print axioms adapter_codeAt

end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def serializedWord (read : Nat → Word) (k : Nat) : Word :=
  if k < 26 then read k else if k < 28 then 0 else
  if k < 78 then read (k - 2) else if k < 80 then 0 else
  if k < 130 then read (k - 4) else if k < 132 then 0 else
  if k < 182 then read (k - 6) else if k < 184 then 0 else
  if k < 366 then read (k - 8) else if k = 366 then read 654 else
  if k = 367 then (read 655 <<< 16) >>> 16 else read (k - 10)

theorem adapter_readout {im : Image} (hc : AdapterCodeAt im)
    (s : MachineState) (hpc : s.pc = pcOf 44096)
    (H : Nat) (hH : H < 7744) (hh : s.getMem 0x8478 >>> 48 = BitVec.ofNat 64 H) :
    ∃ t, Steps im s 3211 3211 t ∧ t.pc = pcOf 1 ∧
      (∀ r ∈ [.x6,.x7,.x14,.x15,.x28,.x29,.x30], t.getReg r = 0) ∧
      RegsExcept s t [.x6,.x7,.x14,.x15,.x28,.x29,.x30] ∧
      t.getMem (BitVec.ofNat 64 policyAddress) = BitVec.ofNat 64 H ∧
      (∀ k, k < 664 → t.getMem (BitVec.ofNat 64 (0x7000 + 8 * k)) =
        serializedWord (fun j => s.getMem (BitVec.ofNat 64 (0x7000 + 8 * j))) k) ∧
      Frame s t (fun A => A = policyAddress ∨ (0x70d0 ≤ A ∧ A < 0x84c0)) := by
  obtain ⟨t, steps, pc, zregs, regs, hints, low, high, main, middle, pair3, pair2, pair1,
    z91a, z91b, z65a, z65b, z39a, z39b, z13a, z13b, frame⟩ := adapter_spec hc s hpc H hH hh
  refine ⟨t, steps, pc, zregs, regs, hints, ?_, frame⟩
  intro k hk
  unfold serializedWord
  split_ifs with h26 h28 h78 h80 h130 h132 h182 h184 h366 he366 he367
  · exact frame (0x7000 + 8 * k) (by omega) (by dsimp [policyAddress]; omega)
  · have e : k = 26 ∨ k = 27 := by omega
    rcases e with rfl | rfl
    · exact z13a
    · exact z13b
  · rw [show 0x7000 + 8 * k = 28896 + 8 * (k - 28) by omega,
      pair1 (k - 28) (by omega)]
    congr 2
    omega
  · have e : k = 78 ∨ k = 79 := by omega
    rcases e with rfl | rfl
    · exact z39a
    · exact z39b
  · rw [show 0x7000 + 8 * k = 29312 + 8 * (k - 80) by omega,
      pair2 (k - 80) (by omega)]
    congr 2
    omega
  · have e : k = 130 ∨ k = 131 := by omega
    rcases e with rfl | rfl
    · exact z65a
    · exact z65b
  · rw [show 0x7000 + 8 * k = 29728 + 8 * (k - 132) by omega,
      pair3 (k - 132) (by omega)]
    congr 2
    omega
  · have e : k = 182 ∨ k = 183 := by omega
    rcases e with rfl | rfl
    · exact z91a
    · exact z91b
  · rw [show 0x7000 + 8 * k = 30144 + 8 * (k - 184) by omega,
      middle (k - 184) (by omega)]
    congr 2
    omega
  · subst k; exact low
  · subst k; exact high
  · rw [show 0x7000 + 8 * k = 31616 + 8 * (k - 368) by omega,
      main (k - 368) (by omega)]
    congr 2
    omega

#print axioms adapter_readout

end ClaudeWCT.W9.Machine.Expand.SharedCompact


namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M

/-- img-v6 word 0: `jal 43250` (the codec pre-pass, which ends with `jal 44096`). -/
def entryWord : BitVec 32 := 0x3c82a06f

theorem entry_step {im : Image} (hc : CodeAt im (pcOf 0) [entryWord])
    (s : MachineState) (hpc : s.pc = pcOf 0) :
    Steps im s 1 1 (s.setPC (pcOf 43250)) := by
  obtain ⟨imm, hd, hoff⟩ := jalTo_sound (show jalTo entryWord 0 = some 43250 by decide +kernel)
  exact jal_x0_step hc hd hoff s hpc

/-- V74: starts at the old entry target 44096 (reached after the img-v6 pre-pass). -/
theorem front_readout {im : Image}
    (hc : AdapterCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 44096)
    (H : Nat) (hH : H < 7744) (hh : s.getMem 0x8478 >>> 48 = BitVec.ofNat 64 H) :
    ∃ t, Steps im s 3211 3211 t ∧ t.pc = pcOf 1 ∧
      (∀ r ∈ [.x6,.x7,.x14,.x15,.x28,.x29,.x30], t.getReg r = 0) ∧
      RegsExcept s t [.x6,.x7,.x14,.x15,.x28,.x29,.x30] ∧
      t.getMem (BitVec.ofNat 64 policyAddress) = BitVec.ofNat 64 H ∧
      (∀ k, k < 664 → t.getMem (BitVec.ofNat 64 (0x7000 + 8 * k)) =
        serializedWord (fun j => s.getMem (BitVec.ofNat 64 (0x7000 + 8 * j))) k) ∧
      Frame s t (fun A => A = policyAddress ∨ (0x70d0 ≤ A ∧ A < 0x84c0)) := by
  exact adapter_readout hc s hpc H hH hh

#print axioms front_readout
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3M SigGolfCandidate.Rv

theorem installed_adapter_codeAt : AdapterCodeAt Images.expandImage := by
  apply adapter_codeAt
  apply codeAt_expand_current_chunk
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem installed_entry_codeAt : CodeAt Images.expandImage (pcOf 0) [entryWord] := by
  apply codeAt_expand_current_chunk
  · decide +kernel
  · decide +kernel
  · decide +kernel
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
abbrev destination (region slot child : Nat) : Nat :=
  region + 16 * slot + 48 * (1 - child % 2)

def pathCode0 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x85313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0x608b303,0x688b383,0x6e3023,0x7e3423]
sym_block path0 := symRun { noAlias := true } pathCode0 (pcOf 45307) 100
theorem path0_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path0.res.st.obl := by
  rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
  all_goals
    simp only [path0.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit]
    norm_num
    omega
#print axioms path0_obligs

def pathCode1 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x185313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0x708b303,0x788b383,0x6e3023,0x7e3423]
sym_block path1 := symRun { noAlias := true } pathCode1 (pcOf 45321) 100
theorem path1_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path1.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
  all_goals
    simp only [path1.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms path1_obligs

def pathCode2 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x285313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0x808b303,0x888b383,0x6e3023,0x7e3423]
sym_block path2 := symRun { noAlias := true } pathCode2 (pcOf 45335) 100
theorem path2_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path2.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
  all_goals
    simp only [path2.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms path2_obligs

def pathCode3 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x385313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0x908b303,0x988b383,0x6e3023,0x7e3423]
sym_block path3 := symRun { noAlias := true } pathCode3 (pcOf 45349) 100
theorem path3_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path3.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
  all_goals
    simp only [path3.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms path3_obligs

def pathCode4 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x485313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0xa08b303,0xa88b383,0x6e3023,0x7e3423]
sym_block path4 := symRun { noAlias := true } pathCode4 (pcOf 45363) 100
theorem path4_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path4.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
  all_goals
    simp only [path4.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms path4_obligs

end ClaudeWCT.W9.Machine.Expand.SharedScatter


namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
sym_block rebased0_0 := symRun { noAlias := true } pathCode0 (pcOf 45307) 100
sym_block rebased0_1 := symRun { noAlias := true } pathCode0 (pcOf 45441) 100
sym_block rebased0_2 := symRun { noAlias := true } pathCode0 (pcOf 45584) 100
sym_block rebased0_3 := symRun { noAlias := true } pathCode0 (pcOf 45718) 100
sym_block rebased0_4 := symRun { noAlias := true } pathCode0 (pcOf 45861) 100
sym_block rebased0_5 := symRun { noAlias := true } pathCode0 (pcOf 45995) 100
sym_block rebased0_6 := symRun { noAlias := true } pathCode0 (pcOf 46138) 100
sym_block rebased0_7 := symRun { noAlias := true } pathCode0 (pcOf 46272) 100
sym_block rebased0_8 := symRun { noAlias := true } pathCode0 (pcOf 46417) 100
theorem run_path0 {b : Nat} (hb : b = 45307 ∨ b = 45441 ∨ b = 45584 ∨ b = 45718 ∨ b = 45861 ∨ b = 45995 ∨ b = 46138 ∨ b = 46272 ∨ b = 46417) :
    symRun { noAlias := true } pathCode0 (pcOf b) 100 =
      some ⟨path0.res.st, .c (pcOf (b + 13)), path0.res.stop, path0.res.steps, path0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased0_0.trans (congrArg some (by kernel_rfl))
  · exact rebased0_1.trans (congrArg some (by kernel_rfl))
  · exact rebased0_2.trans (congrArg some (by kernel_rfl))
  · exact rebased0_3.trans (congrArg some (by kernel_rfl))
  · exact rebased0_4.trans (congrArg some (by kernel_rfl))
  · exact rebased0_5.trans (congrArg some (by kernel_rfl))
  · exact rebased0_6.trans (congrArg some (by kernel_rfl))
  · exact rebased0_7.trans (congrArg some (by kernel_rfl))
  · exact rebased0_8.trans (congrArg some (by kernel_rfl))
theorem path0_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45307 ∨ b = 45441 ∨ b = 45584 ∨ b = 45718 ∨ b = 45861 ∨ b = 45995 ∨ b = 46138 ∨ b = 46272 ∨ b = 46417) (hc : CodeAt im (pcOf b) pathCode0)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot child)) =
        s.getMem (BitVec.ofNat 64 (source + 96)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 104)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot child ∨
        A = destination region slot child + 8) := by
  have ho := path0_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path0 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path0.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path0.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,destination]
      norm_num [ofNat_and1,hbit,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path0.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,destination]
      norm_num [ofNat_and1,hbit,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path0.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path0.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_and1,hbit,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

#print axioms path0_steps_rebased
sym_block rebased1_0 := symRun { noAlias := true } pathCode1 (pcOf 45321) 100
sym_block rebased1_1 := symRun { noAlias := true } pathCode1 (pcOf 45455) 100
sym_block rebased1_2 := symRun { noAlias := true } pathCode1 (pcOf 45598) 100
sym_block rebased1_3 := symRun { noAlias := true } pathCode1 (pcOf 45732) 100
sym_block rebased1_4 := symRun { noAlias := true } pathCode1 (pcOf 45875) 100
sym_block rebased1_5 := symRun { noAlias := true } pathCode1 (pcOf 46009) 100
sym_block rebased1_6 := symRun { noAlias := true } pathCode1 (pcOf 46152) 100
sym_block rebased1_7 := symRun { noAlias := true } pathCode1 (pcOf 46286) 100
sym_block rebased1_8 := symRun { noAlias := true } pathCode1 (pcOf 46431) 100
theorem run_path1 {b : Nat} (hb : b = 45321 ∨ b = 45455 ∨ b = 45598 ∨ b = 45732 ∨ b = 45875 ∨ b = 46009 ∨ b = 46152 ∨ b = 46286 ∨ b = 46431) :
    symRun { noAlias := true } pathCode1 (pcOf b) 100 =
      some ⟨path1.res.st, .c (pcOf (b + 13)), path1.res.stop, path1.res.steps, path1.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased1_0.trans (congrArg some (by kernel_rfl))
  · exact rebased1_1.trans (congrArg some (by kernel_rfl))
  · exact rebased1_2.trans (congrArg some (by kernel_rfl))
  · exact rebased1_3.trans (congrArg some (by kernel_rfl))
  · exact rebased1_4.trans (congrArg some (by kernel_rfl))
  · exact rebased1_5.trans (congrArg some (by kernel_rfl))
  · exact rebased1_6.trans (congrArg some (by kernel_rfl))
  · exact rebased1_7.trans (congrArg some (by kernel_rfl))
  · exact rebased1_8.trans (congrArg some (by kernel_rfl))
theorem path1_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45321 ∨ b = 45455 ∨ b = 45598 ∨ b = 45732 ∨ b = 45875 ∨ b = 46009 ∨ b = 46152 ∨ b = 46286 ∨ b = 46431) (hc : CodeAt im (pcOf b) pathCode1)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 2))) =
        s.getMem (BitVec.ofNat 64 (source + 112)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 2) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 120)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 2) ∨
        A = destination region slot (child / 2) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path1_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path1 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path1.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path1.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path1.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path1.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path1.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

#print axioms path1_steps_rebased
sym_block rebased2_0 := symRun { noAlias := true } pathCode2 (pcOf 45335) 100
sym_block rebased2_1 := symRun { noAlias := true } pathCode2 (pcOf 45469) 100
sym_block rebased2_2 := symRun { noAlias := true } pathCode2 (pcOf 45612) 100
sym_block rebased2_3 := symRun { noAlias := true } pathCode2 (pcOf 45746) 100
sym_block rebased2_4 := symRun { noAlias := true } pathCode2 (pcOf 45889) 100
sym_block rebased2_5 := symRun { noAlias := true } pathCode2 (pcOf 46023) 100
sym_block rebased2_6 := symRun { noAlias := true } pathCode2 (pcOf 46166) 100
sym_block rebased2_7 := symRun { noAlias := true } pathCode2 (pcOf 46300) 100
sym_block rebased2_8 := symRun { noAlias := true } pathCode2 (pcOf 46445) 100
theorem run_path2 {b : Nat} (hb : b = 45335 ∨ b = 45469 ∨ b = 45612 ∨ b = 45746 ∨ b = 45889 ∨ b = 46023 ∨ b = 46166 ∨ b = 46300 ∨ b = 46445) :
    symRun { noAlias := true } pathCode2 (pcOf b) 100 =
      some ⟨path2.res.st, .c (pcOf (b + 13)), path2.res.stop, path2.res.steps, path2.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased2_0.trans (congrArg some (by kernel_rfl))
  · exact rebased2_1.trans (congrArg some (by kernel_rfl))
  · exact rebased2_2.trans (congrArg some (by kernel_rfl))
  · exact rebased2_3.trans (congrArg some (by kernel_rfl))
  · exact rebased2_4.trans (congrArg some (by kernel_rfl))
  · exact rebased2_5.trans (congrArg some (by kernel_rfl))
  · exact rebased2_6.trans (congrArg some (by kernel_rfl))
  · exact rebased2_7.trans (congrArg some (by kernel_rfl))
  · exact rebased2_8.trans (congrArg some (by kernel_rfl))
theorem path2_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45335 ∨ b = 45469 ∨ b = 45612 ∨ b = 45746 ∨ b = 45889 ∨ b = 46023 ∨ b = 46166 ∨ b = 46300 ∨ b = 46445) (hc : CodeAt im (pcOf b) pathCode2)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 4))) =
        s.getMem (BitVec.ofNat 64 (source + 128)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 4) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 136)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 4) ∨
        A = destination region slot (child / 4) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path2_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path2 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path2.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path2.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path2.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path2.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path2.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

#print axioms path2_steps_rebased
sym_block rebased3_0 := symRun { noAlias := true } pathCode3 (pcOf 45349) 100
sym_block rebased3_1 := symRun { noAlias := true } pathCode3 (pcOf 45483) 100
sym_block rebased3_2 := symRun { noAlias := true } pathCode3 (pcOf 45626) 100
sym_block rebased3_3 := symRun { noAlias := true } pathCode3 (pcOf 45760) 100
sym_block rebased3_4 := symRun { noAlias := true } pathCode3 (pcOf 45903) 100
sym_block rebased3_5 := symRun { noAlias := true } pathCode3 (pcOf 46037) 100
sym_block rebased3_6 := symRun { noAlias := true } pathCode3 (pcOf 46180) 100
sym_block rebased3_7 := symRun { noAlias := true } pathCode3 (pcOf 46314) 100
sym_block rebased3_8 := symRun { noAlias := true } pathCode3 (pcOf 46459) 100
theorem run_path3 {b : Nat} (hb : b = 45349 ∨ b = 45483 ∨ b = 45626 ∨ b = 45760 ∨ b = 45903 ∨ b = 46037 ∨ b = 46180 ∨ b = 46314 ∨ b = 46459) :
    symRun { noAlias := true } pathCode3 (pcOf b) 100 =
      some ⟨path3.res.st, .c (pcOf (b + 13)), path3.res.stop, path3.res.steps, path3.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased3_0.trans (congrArg some (by kernel_rfl))
  · exact rebased3_1.trans (congrArg some (by kernel_rfl))
  · exact rebased3_2.trans (congrArg some (by kernel_rfl))
  · exact rebased3_3.trans (congrArg some (by kernel_rfl))
  · exact rebased3_4.trans (congrArg some (by kernel_rfl))
  · exact rebased3_5.trans (congrArg some (by kernel_rfl))
  · exact rebased3_6.trans (congrArg some (by kernel_rfl))
  · exact rebased3_7.trans (congrArg some (by kernel_rfl))
  · exact rebased3_8.trans (congrArg some (by kernel_rfl))
theorem path3_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45349 ∨ b = 45483 ∨ b = 45626 ∨ b = 45760 ∨ b = 45903 ∨ b = 46037 ∨ b = 46180 ∨ b = 46314 ∨ b = 46459) (hc : CodeAt im (pcOf b) pathCode3)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 8))) =
        s.getMem (BitVec.ofNat 64 (source + 144)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 8) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 152)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 8) ∨
        A = destination region slot (child / 8) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path3_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path3 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path3.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path3.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path3.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path3.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path3.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

#print axioms path3_steps_rebased
sym_block rebased4_0 := symRun { noAlias := true } pathCode4 (pcOf 45363) 100
sym_block rebased4_1 := symRun { noAlias := true } pathCode4 (pcOf 45497) 100
sym_block rebased4_2 := symRun { noAlias := true } pathCode4 (pcOf 45640) 100
sym_block rebased4_3 := symRun { noAlias := true } pathCode4 (pcOf 45774) 100
sym_block rebased4_4 := symRun { noAlias := true } pathCode4 (pcOf 45917) 100
sym_block rebased4_5 := symRun { noAlias := true } pathCode4 (pcOf 46051) 100
sym_block rebased4_6 := symRun { noAlias := true } pathCode4 (pcOf 46194) 100
sym_block rebased4_7 := symRun { noAlias := true } pathCode4 (pcOf 46328) 100
sym_block rebased4_8 := symRun { noAlias := true } pathCode4 (pcOf 46473) 100
theorem run_path4 {b : Nat} (hb : b = 45363 ∨ b = 45497 ∨ b = 45640 ∨ b = 45774 ∨ b = 45917 ∨ b = 46051 ∨ b = 46194 ∨ b = 46328 ∨ b = 46473) :
    symRun { noAlias := true } pathCode4 (pcOf b) 100 =
      some ⟨path4.res.st, .c (pcOf (b + 13)), path4.res.stop, path4.res.steps, path4.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased4_0.trans (congrArg some (by kernel_rfl))
  · exact rebased4_1.trans (congrArg some (by kernel_rfl))
  · exact rebased4_2.trans (congrArg some (by kernel_rfl))
  · exact rebased4_3.trans (congrArg some (by kernel_rfl))
  · exact rebased4_4.trans (congrArg some (by kernel_rfl))
  · exact rebased4_5.trans (congrArg some (by kernel_rfl))
  · exact rebased4_6.trans (congrArg some (by kernel_rfl))
  · exact rebased4_7.trans (congrArg some (by kernel_rfl))
  · exact rebased4_8.trans (congrArg some (by kernel_rfl))
theorem path4_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45363 ∨ b = 45497 ∨ b = 45640 ∨ b = 45774 ∨ b = 45917 ∨ b = 46051 ∨ b = 46194 ∨ b = 46328 ∨ b = 46473) (hc : CodeAt im (pcOf b) pathCode4)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 16))) =
        s.getMem (BitVec.ofNat 64 (source + 160)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 16) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 168)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 16) ∨
        A = destination region slot (child / 16) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path4_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path4 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path4.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path4.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path4.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path4.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path4.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

#print axioms path4_steps_rebased
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Load one validated path-plan byte without changing the source or witness memory. -/
theorem load_plan_step {im : Image} {w : BitVec 32} (pc : Word)
    (hc : CodeAt im pc [w]) (level : Fin 5)
    (hd : decodeInstruction w = some (.base (.LBU .x28 .x18 (BitVec.ofNat 12 level.val))))
    (s : MachineState) (hp : s.pc = pc) (table slot : Nat)
    (ht : table + 5 < 2^24) (hs : slot < 53)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table + level.val)) = BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pc + 4 ∧
      t.getReg .x28 = BitVec.ofNat 64 slot ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hoff : signExtend12 (BitVec.ofNat 12 level.val) = BitVec.ofNat 64 level.val := by
    fin_cases level <;> decide +kernel
  have haddr : s.getReg .x18 + signExtend12 (BitVec.ofNat 12 level.val) =
      BitVec.ofNat 64 (table + level.val) := by rw [h18, hoff, ofNat_add_ofNat]
  have hv : accessValid (s.getReg .x18 + signExtend12 (BitVec.ofNat 12 level.val)) 1 = true := by
    rw [haddr]; simp only [accessValid_iff, BitVec.toNat_ofNat, MEMORY_BYTES]
    have := level.isLt
    omega
  have hz : (BitVec.ofNat 8 slot).zeroExtend 64 = BitVec.ofNat 64 slot := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have st := steps_lbu hc hp hd hv
  rw [haddr, hbyte, hz] at st
  refine ⟨_, st, ?_, ?_, ?_, ?_⟩
  · change s.pc + 4 = pc + 4; rw [hp]
  · rfl
  · intro r hr; simp at hr; cases r <;> simp_all [MachineState.setReg, MachineState.getReg, MachineState.setPC]
  · intro A hA hn; simp [rv_simp]
#print axioms load_plan_step
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sixthCode : List (BitVec 32) := [0x34000e13,0x8e0e33,0x585313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0xb08b303,0xb88b383,0xfc6e3823,0xfc7e3c23]
sym_block sixth := symRun { noAlias := true } sixthCode (pcOf 45510) 100
theorem sixth_obligs (s : MachineState) (region source child : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s sixth.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [sixth.res]
    t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms sixth_obligs
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
private theorem low_slot_sub : (2952#64 - 48#64) = 2904#64 := rfl

abbrev topDest0 (child : Nat) : Nat := 9080 + 512 * (child / 32 % 2)
def topCode0 : List (BitVec 32) := [0x585313,0x137313,0x20000393,0x2730333,0x2e37,0x378e0e13,0x6e0e33,0xb08b303,0xb88b383,0x6e3023,0x7e3423]
sym_block top0 := symRun { noAlias := true } topCode0 (pcOf 45376) 100
theorem top0_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top0.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [top0.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top0_obligs
theorem top0_steps {im : Image} (hc : CodeAt im (pcOf 45376) topCode0)
    (s : MachineState) (hp : s.pc = pcOf 45376) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45387 ∧
      t.getMem (BitVec.ofNat 64 (topDest0 child)) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (topDest0 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest0 child ∨
        A = topDest0 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top0_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top0 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top0.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top0.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest0]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top0.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest0]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top0.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top0.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest0]
      simp only [topDest0,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top0_steps


abbrev topDest1 (child : Nat) : Nat := 8232 + 512 * (child / 64 % 2)
def topCode1 : List (BitVec 32) := [0x685313,0x137313,0x20000393,0x2730333,0x2e37,0x28e0e13,0x6e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top1 := symRun { noAlias := true } topCode1 (pcOf 45523) 100
theorem top1_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top1.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top1.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top1_obligs
theorem top1_steps {im : Image} (hc : CodeAt im (pcOf 45523) topCode1)
    (s : MachineState) (hp : s.pc = pcOf 45523) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45534 ∧
      t.getMem (BitVec.ofNat 64 (topDest1 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest1 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest1 child ∨
        A = topDest1 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top1_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top1 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top1.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top1.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest1]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top1.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest1]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top1.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top1.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest1]
      simp only [topDest1,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top1_steps


abbrev topDest2 (child : Nat) : Nat := 7384 + 512 * (child / 32 % 2)
def topCode2 : List (BitVec 32) := [0x585313,0x137313,0x20000393,0x2730333,0x2e37,0xcd8e0e13,0x6e0e33,0xb08b303,0xb88b383,0x6e3023,0x7e3423]
sym_block top2 := symRun { noAlias := true } topCode2 (pcOf 45653) 100
theorem top2_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top2.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [top2.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top2_obligs
theorem top2_steps {im : Image} (hc : CodeAt im (pcOf 45653) topCode2)
    (s : MachineState) (hp : s.pc = pcOf 45653) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45664 ∧
      t.getMem (BitVec.ofNat 64 (topDest2 child)) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (topDest2 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest2 child ∨
        A = topDest2 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top2_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top2 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top2.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top2.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest2]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top2.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest2]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top2.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top2.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest2]
      simp only [topDest2,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top2_steps


abbrev topDest3 (child : Nat) : Nat := 6536 + 512 * (child / 64 % 2)
def topCode3 : List (BitVec 32) := [0x685313,0x137313,0x20000393,0x2730333,0x2e37,0x988e0e13,0x6e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top3 := symRun { noAlias := true } topCode3 (pcOf 45800) 100
theorem top3_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top3.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top3.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top3_obligs
theorem top3_steps {im : Image} (hc : CodeAt im (pcOf 45800) topCode3)
    (s : MachineState) (hp : s.pc = pcOf 45800) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45811 ∧
      t.getMem (BitVec.ofNat 64 (topDest3 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest3 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest3 child ∨
        A = topDest3 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top3_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top3 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top3.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top3.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest3]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top3.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest3]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top3.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top3.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest3]
      simp only [topDest3,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top3_steps


abbrev topDest4 (child : Nat) : Nat := 5688 + 512 * (child / 32 % 2)
def topCode4 : List (BitVec 32) := [0x585313,0x137313,0x20000393,0x2730333,0x1e37,0x638e0e13,0x6e0e33,0xb08b303,0xb88b383,0x6e3023,0x7e3423]
sym_block top4 := symRun { noAlias := true } topCode4 (pcOf 45930) 100
theorem top4_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top4.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [top4.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top4_obligs
theorem top4_steps {im : Image} (hc : CodeAt im (pcOf 45930) topCode4)
    (s : MachineState) (hp : s.pc = pcOf 45930) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45941 ∧
      t.getMem (BitVec.ofNat 64 (topDest4 child)) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (topDest4 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest4 child ∨
        A = topDest4 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top4_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top4 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top4.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top4.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest4]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top4.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest4]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top4.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top4.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest4]
      simp only [topDest4,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top4_steps


abbrev topDest5 (child : Nat) : Nat := 4840 + 512 * (child / 64 % 2)
def topCode5 : List (BitVec 32) := [0x685313,0x137313,0x20000393,0x2730333,0x1e37,0x2e8e0e13,0x6e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top5 := symRun { noAlias := true } topCode5 (pcOf 46077) 100
theorem top5_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top5.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top5.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top5_obligs
theorem top5_steps {im : Image} (hc : CodeAt im (pcOf 46077) topCode5)
    (s : MachineState) (hp : s.pc = pcOf 46077) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 46088 ∧
      t.getMem (BitVec.ofNat 64 (topDest5 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest5 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest5 child ∨
        A = topDest5 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top5_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top5 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top5.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top5.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest5]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top5.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest5]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top5.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top5.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest5]
      simp only [topDest5,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top5_steps


abbrev topDest6 (child : Nat) : Nat := 3992 + 512 * (child / 32 % 2)
def topCode6 : List (BitVec 32) := [0x585313,0x137313,0x20000393,0x2730333,0x1e37,0xf98e0e13,0x6e0e33,0xb08b303,0xb88b383,0x6e3023,0x7e3423]
sym_block top6 := symRun { noAlias := true } topCode6 (pcOf 46207) 100
theorem top6_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top6.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [top6.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top6_obligs
theorem top6_steps {im : Image} (hc : CodeAt im (pcOf 46207) topCode6)
    (s : MachineState) (hp : s.pc = pcOf 46207) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 46218 ∧
      t.getMem (BitVec.ofNat 64 (topDest6 child)) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (topDest6 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest6 child ∨
        A = topDest6 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top6_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top6 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top6.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top6.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest6]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top6.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest6]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top6.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top6.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest6]
      simp only [topDest6,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top6_steps


abbrev topDest7 (child : Nat) : Nat := 3144 + 512 * (child / 64 % 2)
def topCode7 : List (BitVec 32) := [0x685313,0x137313,0x20000393,0x2730333,0xd5040e13,0x6e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top7 := symRun { noAlias := true } topCode7 (pcOf 46354) 100
theorem top7_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 3832) :
    Oblig.all s top7.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top7.res]
    t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top7_obligs
theorem top7_steps {im : Image} (hc : CodeAt im (pcOf 46354) topCode7)
    (s : MachineState) (hp : s.pc = pcOf 46354) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 3832) :
    ∃ t, Steps im s 10 13 t ∧ t.pc = pcOf 46364 ∧
      t.getMem (BitVec.ofNat 64 (topDest7 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest7 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest7 child ∨
        A = topDest7 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top7_obligs s source child hs0 hs1 hsa hj h16 h17 h8
  refine ⟨_, symRun_sound top7 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top7.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top7.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest7]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top7.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest7]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top7.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top7.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest7]
      simp only [topDest7,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top7_steps


abbrev topDest8 (child : Nat) : Nat := 2952 - 48 * (child / 64 % 2)
def topCode8 : List (BitVec 32) := [0x685313,0x137313,0x3000393,0x2730333,0xfe040e13,0x406e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top8 := symRun { noAlias := true } topCode8 (pcOf 46499) 100
theorem top8_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 2984) :
    Oblig.all s top8.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top8.res]
    t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top8_obligs
theorem top8_steps {im : Image} (hc : CodeAt im (pcOf 46499) topCode8)
    (s : MachineState) (hp : s.pc = pcOf 46499) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 2984) :
    ∃ t, Steps im s 10 13 t ∧ t.pc = pcOf 46509 ∧
      t.getMem (BitVec.ofNat 64 (topDest8 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest8 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest8 child ∨
        A = topDest8 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top8_obligs s source child hs0 hs1 hsa hj h16 h17 h8
  refine ⟨_, symRun_sound top8 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top8.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top8.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest8]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals (try simp only [BitVec.reduceSub, BitVec.reduceAdd] at *) <;> (try norm_num [ofNat_eq_iff] at *) <;> split_ifs <;> (first | rfl | omega | simp_all)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top8.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest8]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals (try simp only [BitVec.reduceSub, BitVec.reduceAdd] at *) <;> (try norm_num [ofNat_eq_iff] at *) <;> split_ifs <;> (first | rfl | omega | simp_all)
  · intro r hr; simp at hr; cases r <;> simp_all [top8.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top8.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest8]
      simp only [topDest8,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals (try simp only [BitVec.reduceSub, BitVec.reduceAdd] at *) <;> (try norm_num [ofNat_eq_iff] at *) <;> split_ifs <;> (first | rfl | omega | simp_all)
#print axioms top8_steps


end ClaudeWCT.W9.Machine.Expand.SharedScatter


namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
sym_block sixthRebase0 := symRun { noAlias := true } sixthCode (pcOf 45510) 100
sym_block sixthRebase1 := symRun { noAlias := true } sixthCode (pcOf 45787) 100
sym_block sixthRebase2 := symRun { noAlias := true } sixthCode (pcOf 46064) 100
sym_block sixthRebase3 := symRun { noAlias := true } sixthCode (pcOf 46341) 100
sym_block sixthRebase4 := symRun { noAlias := true } sixthCode (pcOf 46486) 100
theorem run_sixth {b : Nat} (hb : b = 45510 ∨ b = 45787 ∨ b = 46064 ∨ b = 46341 ∨ b = 46486) :
    symRun { noAlias := true } sixthCode (pcOf b) 100 =
      some ⟨sixth.res.st, .c (pcOf (b + 13)), sixth.res.stop, sixth.res.steps, sixth.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact sixthRebase0.trans (congrArg some (by kernel_rfl))
  · exact sixthRebase1.trans (congrArg some (by kernel_rfl))
  · exact sixthRebase2.trans (congrArg some (by kernel_rfl))
  · exact sixthRebase3.trans (congrArg some (by kernel_rfl))
  · exact sixthRebase4.trans (congrArg some (by kernel_rfl))
theorem sixth_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45510 ∨ b = 45787 ∨ b = 46064 ∨ b = 46341 ∨ b = 46486) (hc : CodeAt im (pcOf b) sixthCode)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b+13) ∧
      t.getMem (BitVec.ofNat 64 (destination region 49 (child / 32))) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (destination region 49 (child / 32) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region 49 (child / 32) ∨
        A = destination region 49 (child / 32) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := sixth_obligs s region source child hr0 hr1 hra hs0 hs1 hsa hj h8 h16 h17
  refine ⟨_, symRun_sound (run_sixth hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [sixth.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,sixth.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_sub_ofNat_u,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals first | rfl | (intro h; exfalso; omega) | (split_ifs <;> (first | rfl | omega))
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,sixth.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_sub_ofNat_u,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals first | rfl | (intro h; exfalso; omega) | (split_ifs <;> (first | rfl | omega))
  · intro r hr; simp at hr; cases r <;> simp_all [sixth.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,sixth.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_sub_ofNat_u,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals first | rfl | (intro h; exfalso; omega) | (split_ifs <;> (first | rfl | omega))

#print axioms sixth_steps_rebased
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def value0Code : List (BitVec 32) := bv_list% 32 [0x8b303,0x88b383,0x28643023,0x28743423]
sym_block value0_0 := symRun { noAlias := true } value0Code (pcOf 45266) 20
sym_block value0_1 := symRun { noAlias := true } value0Code (pcOf 45400) 20
sym_block value0_2 := symRun { noAlias := true } value0Code (pcOf 45543) 20
sym_block value0_3 := symRun { noAlias := true } value0Code (pcOf 45677) 20
sym_block value0_4 := symRun { noAlias := true } value0Code (pcOf 45820) 20
sym_block value0_5 := symRun { noAlias := true } value0Code (pcOf 45954) 20
sym_block value0_6 := symRun { noAlias := true } value0Code (pcOf 46097) 20
sym_block value0_7 := symRun { noAlias := true } value0Code (pcOf 46231) 20
sym_block value0_8 := symRun { noAlias := true } value0Code (pcOf 46376) 20
theorem value0_run {b : Nat} (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376) :
    symRun { noAlias := true } value0Code (pcOf b) 20 =
      some ⟨value0_0.res.st,.c (pcOf (b+4)),value0_0.res.stop,value0_0.res.steps,value0_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value0_0.trans (congrArg some (by kernel_rfl))
  · exact value0_1.trans (congrArg some (by kernel_rfl))
  · exact value0_2.trans (congrArg some (by kernel_rfl))
  · exact value0_3.trans (congrArg some (by kernel_rfl))
  · exact value0_4.trans (congrArg some (by kernel_rfl))
  · exact value0_5.trans (congrArg some (by kernel_rfl))
  · exact value0_6.trans (congrArg some (by kernel_rfl))
  · exact value0_7.trans (congrArg some (by kernel_rfl))
  · exact value0_8.trans (congrArg some (by kernel_rfl))
theorem value0_steps {im : Image} {b : Nat} (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376)
    (hc : CodeAt im (pcOf b) value0Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 4 4 t ∧ t.pc=pcOf (b+4) ∧
      t.getMem (BitVec.ofNat 64 (region+640))=s.getMem (BitVec.ofNat 64 (source+0)) ∧
      t.getMem (BitVec.ofNat 64 (region+648))=s.getMem (BitVec.ofNat 64 (source+8)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+640 ∨ A=region+648) := by
  have ho : Oblig.all s value0_0.res.st.obl := by
    simp only [value0_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value0_run hb) hc s hp ho,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value0_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value0_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value0_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
#print axioms value0_steps
def value1Code : List (BitVec 32) := bv_list% 32 [0x108b303,0x188b383,0x1e643c23,0x20743023,0x2a643823,0x2a743c23]
sym_block value1_0 := symRun { noAlias := true } value1Code (pcOf 45270) 20
sym_block value1_1 := symRun { noAlias := true } value1Code (pcOf 45404) 20
sym_block value1_2 := symRun { noAlias := true } value1Code (pcOf 45547) 20
sym_block value1_3 := symRun { noAlias := true } value1Code (pcOf 45681) 20
sym_block value1_4 := symRun { noAlias := true } value1Code (pcOf 45824) 20
sym_block value1_5 := symRun { noAlias := true } value1Code (pcOf 45958) 20
sym_block value1_6 := symRun { noAlias := true } value1Code (pcOf 46101) 20
sym_block value1_7 := symRun { noAlias := true } value1Code (pcOf 46235) 20
sym_block value1_8 := symRun { noAlias := true } value1Code (pcOf 46380) 20
theorem value1_run {b : Nat} (hb : b=45270 ∨ b=45404 ∨ b=45547 ∨ b=45681 ∨ b=45824 ∨ b=45958 ∨ b=46101 ∨ b=46235 ∨ b=46380) :
    symRun { noAlias := true } value1Code (pcOf b) 20 =
      some ⟨value1_0.res.st,.c (pcOf (b+6)),value1_0.res.stop,value1_0.res.steps,value1_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value1_0.trans (congrArg some (by kernel_rfl))
  · exact value1_1.trans (congrArg some (by kernel_rfl))
  · exact value1_2.trans (congrArg some (by kernel_rfl))
  · exact value1_3.trans (congrArg some (by kernel_rfl))
  · exact value1_4.trans (congrArg some (by kernel_rfl))
  · exact value1_5.trans (congrArg some (by kernel_rfl))
  · exact value1_6.trans (congrArg some (by kernel_rfl))
  · exact value1_7.trans (congrArg some (by kernel_rfl))
  · exact value1_8.trans (congrArg some (by kernel_rfl))
theorem value1_steps {im : Image} {b : Nat} (hb : b=45270 ∨ b=45404 ∨ b=45547 ∨ b=45681 ∨ b=45824 ∨ b=45958 ∨ b=46101 ∨ b=46235 ∨ b=46380)
    (hc : CodeAt im (pcOf b) value1Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+504))=s.getMem (BitVec.ofNat 64 (source+16)) ∧
      t.getMem (BitVec.ofNat 64 (region+512))=s.getMem (BitVec.ofNat 64 (source+24)) ∧
      t.getMem (BitVec.ofNat 64 (region+688))=s.getMem (BitVec.ofNat 64 (source+16)) ∧
      t.getMem (BitVec.ofNat 64 (region+696))=s.getMem (BitVec.ofNat 64 (source+24)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+504 ∨ A=region+512 ∨ A=region+688 ∨ A=region+696) := by
  have ho : Oblig.all s value1_0.res.st.obl := by
    simp only [value1_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value1_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
#print axioms value1_steps
def value2Code : List (BitVec 32) := bv_list% 32 [0x208b303,0x288b383,0x24643023,0x24743423,0x2c643023,0x2c743423]
sym_block value2_0 := symRun { noAlias := true } value2Code (pcOf 45276) 20
sym_block value2_1 := symRun { noAlias := true } value2Code (pcOf 45410) 20
sym_block value2_2 := symRun { noAlias := true } value2Code (pcOf 45553) 20
sym_block value2_3 := symRun { noAlias := true } value2Code (pcOf 45687) 20
sym_block value2_4 := symRun { noAlias := true } value2Code (pcOf 45830) 20
sym_block value2_5 := symRun { noAlias := true } value2Code (pcOf 45964) 20
sym_block value2_6 := symRun { noAlias := true } value2Code (pcOf 46107) 20
sym_block value2_7 := symRun { noAlias := true } value2Code (pcOf 46241) 20
sym_block value2_8 := symRun { noAlias := true } value2Code (pcOf 46386) 20
theorem value2_run {b : Nat} (hb : b=45276 ∨ b=45410 ∨ b=45553 ∨ b=45687 ∨ b=45830 ∨ b=45964 ∨ b=46107 ∨ b=46241 ∨ b=46386) :
    symRun { noAlias := true } value2Code (pcOf b) 20 =
      some ⟨value2_0.res.st,.c (pcOf (b+6)),value2_0.res.stop,value2_0.res.steps,value2_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value2_0.trans (congrArg some (by kernel_rfl))
  · exact value2_1.trans (congrArg some (by kernel_rfl))
  · exact value2_2.trans (congrArg some (by kernel_rfl))
  · exact value2_3.trans (congrArg some (by kernel_rfl))
  · exact value2_4.trans (congrArg some (by kernel_rfl))
  · exact value2_5.trans (congrArg some (by kernel_rfl))
  · exact value2_6.trans (congrArg some (by kernel_rfl))
  · exact value2_7.trans (congrArg some (by kernel_rfl))
  · exact value2_8.trans (congrArg some (by kernel_rfl))
theorem value2_steps {im : Image} {b : Nat} (hb : b=45276 ∨ b=45410 ∨ b=45553 ∨ b=45687 ∨ b=45830 ∨ b=45964 ∨ b=46107 ∨ b=46241 ∨ b=46386)
    (hc : CodeAt im (pcOf b) value2Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+576))=s.getMem (BitVec.ofNat 64 (source+32)) ∧
      t.getMem (BitVec.ofNat 64 (region+584))=s.getMem (BitVec.ofNat 64 (source+40)) ∧
      t.getMem (BitVec.ofNat 64 (region+704))=s.getMem (BitVec.ofNat 64 (source+32)) ∧
      t.getMem (BitVec.ofNat 64 (region+712))=s.getMem (BitVec.ofNat 64 (source+40)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+576 ∨ A=region+584 ∨ A=region+704 ∨ A=region+712) := by
  have ho : Oblig.all s value2_0.res.st.obl := by
    simp only [value2_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value2_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
#print axioms value2_steps
def value3Code : List (BitVec 32) := bv_list% 32 [0x308b303,0x388b383,0x18643823,0x18743c23,0x2c643823,0x2c743c23]
sym_block value3_0 := symRun { noAlias := true } value3Code (pcOf 45282) 20
sym_block value3_1 := symRun { noAlias := true } value3Code (pcOf 45416) 20
sym_block value3_2 := symRun { noAlias := true } value3Code (pcOf 45559) 20
sym_block value3_3 := symRun { noAlias := true } value3Code (pcOf 45693) 20
sym_block value3_4 := symRun { noAlias := true } value3Code (pcOf 45836) 20
sym_block value3_5 := symRun { noAlias := true } value3Code (pcOf 45970) 20
sym_block value3_6 := symRun { noAlias := true } value3Code (pcOf 46113) 20
sym_block value3_7 := symRun { noAlias := true } value3Code (pcOf 46247) 20
sym_block value3_8 := symRun { noAlias := true } value3Code (pcOf 46392) 20
theorem value3_run {b : Nat} (hb : b=45282 ∨ b=45416 ∨ b=45559 ∨ b=45693 ∨ b=45836 ∨ b=45970 ∨ b=46113 ∨ b=46247 ∨ b=46392) :
    symRun { noAlias := true } value3Code (pcOf b) 20 =
      some ⟨value3_0.res.st,.c (pcOf (b+6)),value3_0.res.stop,value3_0.res.steps,value3_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value3_0.trans (congrArg some (by kernel_rfl))
  · exact value3_1.trans (congrArg some (by kernel_rfl))
  · exact value3_2.trans (congrArg some (by kernel_rfl))
  · exact value3_3.trans (congrArg some (by kernel_rfl))
  · exact value3_4.trans (congrArg some (by kernel_rfl))
  · exact value3_5.trans (congrArg some (by kernel_rfl))
  · exact value3_6.trans (congrArg some (by kernel_rfl))
  · exact value3_7.trans (congrArg some (by kernel_rfl))
  · exact value3_8.trans (congrArg some (by kernel_rfl))
theorem value3_steps {im : Image} {b : Nat} (hb : b=45282 ∨ b=45416 ∨ b=45559 ∨ b=45693 ∨ b=45836 ∨ b=45970 ∨ b=46113 ∨ b=46247 ∨ b=46392)
    (hc : CodeAt im (pcOf b) value3Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+400))=s.getMem (BitVec.ofNat 64 (source+48)) ∧
      t.getMem (BitVec.ofNat 64 (region+408))=s.getMem (BitVec.ofNat 64 (source+56)) ∧
      t.getMem (BitVec.ofNat 64 (region+720))=s.getMem (BitVec.ofNat 64 (source+48)) ∧
      t.getMem (BitVec.ofNat 64 (region+728))=s.getMem (BitVec.ofNat 64 (source+56)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+400 ∨ A=region+408 ∨ A=region+720 ∨ A=region+728) := by
  have ho : Oblig.all s value3_0.res.st.obl := by
    simp only [value3_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value3_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
#print axioms value3_steps
def value4Code : List (BitVec 32) := bv_list% 32 [0x408b303,0x488b383,0x1c643c23,0x1e743023,0x2e643023,0x2e743423]
sym_block value4_0 := symRun { noAlias := true } value4Code (pcOf 45288) 20
sym_block value4_1 := symRun { noAlias := true } value4Code (pcOf 45422) 20
sym_block value4_2 := symRun { noAlias := true } value4Code (pcOf 45565) 20
sym_block value4_3 := symRun { noAlias := true } value4Code (pcOf 45699) 20
sym_block value4_4 := symRun { noAlias := true } value4Code (pcOf 45842) 20
sym_block value4_5 := symRun { noAlias := true } value4Code (pcOf 45976) 20
sym_block value4_6 := symRun { noAlias := true } value4Code (pcOf 46119) 20
sym_block value4_7 := symRun { noAlias := true } value4Code (pcOf 46253) 20
sym_block value4_8 := symRun { noAlias := true } value4Code (pcOf 46398) 20
theorem value4_run {b : Nat} (hb : b=45288 ∨ b=45422 ∨ b=45565 ∨ b=45699 ∨ b=45842 ∨ b=45976 ∨ b=46119 ∨ b=46253 ∨ b=46398) :
    symRun { noAlias := true } value4Code (pcOf b) 20 =
      some ⟨value4_0.res.st,.c (pcOf (b+6)),value4_0.res.stop,value4_0.res.steps,value4_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value4_0.trans (congrArg some (by kernel_rfl))
  · exact value4_1.trans (congrArg some (by kernel_rfl))
  · exact value4_2.trans (congrArg some (by kernel_rfl))
  · exact value4_3.trans (congrArg some (by kernel_rfl))
  · exact value4_4.trans (congrArg some (by kernel_rfl))
  · exact value4_5.trans (congrArg some (by kernel_rfl))
  · exact value4_6.trans (congrArg some (by kernel_rfl))
  · exact value4_7.trans (congrArg some (by kernel_rfl))
  · exact value4_8.trans (congrArg some (by kernel_rfl))
theorem value4_steps {im : Image} {b : Nat} (hb : b=45288 ∨ b=45422 ∨ b=45565 ∨ b=45699 ∨ b=45842 ∨ b=45976 ∨ b=46119 ∨ b=46253 ∨ b=46398)
    (hc : CodeAt im (pcOf b) value4Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+472))=s.getMem (BitVec.ofNat 64 (source+64)) ∧
      t.getMem (BitVec.ofNat 64 (region+480))=s.getMem (BitVec.ofNat 64 (source+72)) ∧
      t.getMem (BitVec.ofNat 64 (region+736))=s.getMem (BitVec.ofNat 64 (source+64)) ∧
      t.getMem (BitVec.ofNat 64 (region+744))=s.getMem (BitVec.ofNat 64 (source+72)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+472 ∨ A=region+480 ∨ A=region+736 ∨ A=region+744) := by
  have ho : Oblig.all s value4_0.res.st.obl := by
    simp only [value4_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value4_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
#print axioms value4_steps
def value5Code : List (BitVec 32) := bv_list% 32 [0x508b303,0x588b383,0x16643823,0x16743c23,0x2e643823,0x2e743c23]
sym_block value5_0 := symRun { noAlias := true } value5Code (pcOf 45294) 20
sym_block value5_1 := symRun { noAlias := true } value5Code (pcOf 45428) 20
sym_block value5_2 := symRun { noAlias := true } value5Code (pcOf 45571) 20
sym_block value5_3 := symRun { noAlias := true } value5Code (pcOf 45705) 20
sym_block value5_4 := symRun { noAlias := true } value5Code (pcOf 45848) 20
sym_block value5_5 := symRun { noAlias := true } value5Code (pcOf 45982) 20
sym_block value5_6 := symRun { noAlias := true } value5Code (pcOf 46125) 20
sym_block value5_7 := symRun { noAlias := true } value5Code (pcOf 46259) 20
sym_block value5_8 := symRun { noAlias := true } value5Code (pcOf 46404) 20
theorem value5_run {b : Nat} (hb : b=45294 ∨ b=45428 ∨ b=45571 ∨ b=45705 ∨ b=45848 ∨ b=45982 ∨ b=46125 ∨ b=46259 ∨ b=46404) :
    symRun { noAlias := true } value5Code (pcOf b) 20 =
      some ⟨value5_0.res.st,.c (pcOf (b+6)),value5_0.res.stop,value5_0.res.steps,value5_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value5_0.trans (congrArg some (by kernel_rfl))
  · exact value5_1.trans (congrArg some (by kernel_rfl))
  · exact value5_2.trans (congrArg some (by kernel_rfl))
  · exact value5_3.trans (congrArg some (by kernel_rfl))
  · exact value5_4.trans (congrArg some (by kernel_rfl))
  · exact value5_5.trans (congrArg some (by kernel_rfl))
  · exact value5_6.trans (congrArg some (by kernel_rfl))
  · exact value5_7.trans (congrArg some (by kernel_rfl))
  · exact value5_8.trans (congrArg some (by kernel_rfl))
theorem value5_steps {im : Image} {b : Nat} (hb : b=45294 ∨ b=45428 ∨ b=45571 ∨ b=45705 ∨ b=45848 ∨ b=45982 ∨ b=46125 ∨ b=46259 ∨ b=46404)
    (hc : CodeAt im (pcOf b) value5Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+368))=s.getMem (BitVec.ofNat 64 (source+80)) ∧
      t.getMem (BitVec.ofNat 64 (region+376))=s.getMem (BitVec.ofNat 64 (source+88)) ∧
      t.getMem (BitVec.ofNat 64 (region+752))=s.getMem (BitVec.ofNat 64 (source+80)) ∧
      t.getMem (BitVec.ofNat 64 (region+760))=s.getMem (BitVec.ofNat 64 (source+88)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+368 ∨ A=region+376 ∨ A=region+752 ∨ A=region+760) := by
  have ho : Oblig.all s value5_0.res.st.obl := by
    simp only [value5_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value5_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
#print axioms value5_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem rotate_raw (raw : Nat) (hr : raw<128) :
    (BitVec.ofNat 64 raw >>> 1) + ((BitVec.ofNat 64 raw &&& 1#64) <<< 6) =
      BitVec.ofNat 64 (raw/2+64*(raw%2)) := by
  have hm : BitVec.ofNat 64 raw &&& 1#64=BitVec.ofNat 64 (raw%2) := by
    simpa using SigGolfCandidate.T3M.Sign.ofNat_and_mask raw 1 (by decide)
  rw [ofNat_shr raw 1 (by omega),hm,ofNat_shl,ofNat_add_ofNat]
  congr 1
  simp only [pow_one]
  omega
def entry0Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x8b803,0x85813,0x7f87813,0x2437,0x62840413,0x78b7,0x1088893]
sym_block entry0 := symRun { noAlias := true } entry0Code (pcOf 45257) 32
theorem entry0_steps {im : Image} (hc : CodeAt im (pcOf 45257) entry0Code)
    (s : MachineState) (hp : s.pc=pcOf 45257) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131424) >>> 0 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 45266 ∧
      t.getReg .x16=BitVec.ofNat 64 raw ∧
      t.getReg .x8=BitVec.ofNat 64 9768 ∧
      t.getReg .x17=BitVec.ofNat 64 28688 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry0 hc s hp (by simp [entry0.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry0.res,E.eval]
  · simp only [Result.toState_getReg,entry0.res]
    t3n []
    simpa using hraw
  · simp [entry0.res,rv_simp]
  · simp [entry0.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry0.res,rv_simp]
#print axioms entry0_steps
def entry1Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x8b803,0x685813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0x2437,0x2d840413,0x78b7,0xe088893]
sym_block entry1 := symRun { noAlias := true } entry1Code (pcOf 45387) 32
theorem entry1_steps {im : Image} (hc : CodeAt im (pcOf 45387) entry1Code)
    (s : MachineState) (hp : s.pc=pcOf 45387) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131424) >>> 6 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=pcOf 45400 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 8920 ∧
      t.getReg .x17=BitVec.ofNat 64 28896 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry1 hc s hp (by simp [entry1.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry1.res,E.eval]
  · simp only [Result.toState_getReg,entry1.res]
    t3n []
    have hraw' : s.getMem 131424#64 >>> 6 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp [entry1.res,rv_simp]
  · simp [entry1.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry1.res,rv_simp]
#print axioms entry1_steps
def entry2Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x88b803,0x85813,0x7f87813,0x2437,0xf8840413,0x78b7,0x1b088893]
sym_block entry2 := symRun { noAlias := true } entry2Code (pcOf 45534) 32
theorem entry2_steps {im : Image} (hc : CodeAt im (pcOf 45534) entry2Code)
    (s : MachineState) (hp : s.pc=pcOf 45534) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131432) >>> 0 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 45543 ∧
      t.getReg .x16=BitVec.ofNat 64 raw ∧
      t.getReg .x8=BitVec.ofNat 64 8072 ∧
      t.getReg .x17=BitVec.ofNat 64 29104 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry2 hc s hp (by simp [entry2.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry2.res,E.eval]
  · simp only [Result.toState_getReg,entry2.res]
    t3n []
    simpa using hraw
  · simp [entry2.res,rv_simp]
  · simp [entry2.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry2.res,rv_simp]
#print axioms entry2_steps
def entry3Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x88b803,0x685813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0x2437,0xc3840413,0x78b7,0x28088893]
sym_block entry3 := symRun { noAlias := true } entry3Code (pcOf 45664) 32
theorem entry3_steps {im : Image} (hc : CodeAt im (pcOf 45664) entry3Code)
    (s : MachineState) (hp : s.pc=pcOf 45664) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131432) >>> 6 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=pcOf 45677 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 7224 ∧
      t.getReg .x17=BitVec.ofNat 64 29312 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry3 hc s hp (by simp [entry3.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry3.res,E.eval]
  · simp only [Result.toState_getReg,entry3.res]
    t3n []
    have hraw' : s.getMem 131432#64 >>> 6 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp [entry3.res,rv_simp]
  · simp [entry3.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry3.res,rv_simp]
#print axioms entry3_steps
def entry4Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x108b803,0x85813,0x7f87813,0x2437,0x8e840413,0x78b7,0x35088893]
sym_block entry4 := symRun { noAlias := true } entry4Code (pcOf 45811) 32
theorem entry4_steps {im : Image} (hc : CodeAt im (pcOf 45811) entry4Code)
    (s : MachineState) (hp : s.pc=pcOf 45811) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131440) >>> 0 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 45820 ∧
      t.getReg .x16=BitVec.ofNat 64 raw ∧
      t.getReg .x8=BitVec.ofNat 64 6376 ∧
      t.getReg .x17=BitVec.ofNat 64 29520 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry4 hc s hp (by simp [entry4.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry4.res,E.eval]
  · simp only [Result.toState_getReg,entry4.res]
    t3n []
    simpa using hraw
  · simp [entry4.res,rv_simp]
  · simp [entry4.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry4.res,rv_simp]
#print axioms entry4_steps
def entry5Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x108b803,0x685813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0x1437,0x59840413,0x78b7,0x42088893]
sym_block entry5 := symRun { noAlias := true } entry5Code (pcOf 45941) 32
theorem entry5_steps {im : Image} (hc : CodeAt im (pcOf 45941) entry5Code)
    (s : MachineState) (hp : s.pc=pcOf 45941) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131440) >>> 6 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=pcOf 45954 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 5528 ∧
      t.getReg .x17=BitVec.ofNat 64 29728 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry5 hc s hp (by simp [entry5.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry5.res,E.eval]
  · simp only [Result.toState_getReg,entry5.res]
    t3n []
    have hraw' : s.getMem 131440#64 >>> 6 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp [entry5.res,rv_simp]
  · simp [entry5.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry5.res,rv_simp]
#print axioms entry5_steps
def entry6Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x188b803,0x85813,0x7f87813,0x1437,0x24840413,0x78b7,0x4f088893]
sym_block entry6 := symRun { noAlias := true } entry6Code (pcOf 46088) 32
theorem entry6_steps {im : Image} (hc : CodeAt im (pcOf 46088) entry6Code)
    (s : MachineState) (hp : s.pc=pcOf 46088) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131448) >>> 0 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 46097 ∧
      t.getReg .x16=BitVec.ofNat 64 raw ∧
      t.getReg .x8=BitVec.ofNat 64 4680 ∧
      t.getReg .x17=BitVec.ofNat 64 29936 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry6 hc s hp (by simp [entry6.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry6.res,E.eval]
  · simp only [Result.toState_getReg,entry6.res]
    t3n []
    simpa using hraw
  · simp [entry6.res,rv_simp]
  · simp [entry6.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry6.res,rv_simp]
#print axioms entry6_steps
def entry7Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x188b803,0x685813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0x1437,0xef840413,0x78b7,0x5c088893]
sym_block entry7 := symRun { noAlias := true } entry7Code (pcOf 46218) 32
theorem entry7_steps {im : Image} (hc : CodeAt im (pcOf 46218) entry7Code)
    (s : MachineState) (hp : s.pc=pcOf 46218) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131448) >>> 6 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=pcOf 46231 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 3832 ∧
      t.getReg .x17=BitVec.ofNat 64 30144 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry7 hc s hp (by simp [entry7.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry7.res,E.eval]
  · simp only [Result.toState_getReg,entry7.res]
    t3n []
    have hraw' : s.getMem 131448#64 >>> 6 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp [entry7.res,rv_simp]
  · simp [entry7.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry7.res,rv_simp]
#print axioms entry7_steps
def entry8Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x188b803,0x2585813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0xcb040413,0x78b7,0x69088893]
sym_block entry8 := symRun { noAlias := true } entry8Code (pcOf 46364) 32
theorem entry8_steps {im : Image} (hc : CodeAt im (pcOf 46364) entry8Code)
    (s : MachineState) (hp : s.pc=pcOf 46364) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131448) >>> 37 &&& 127#64=BitVec.ofNat 64 raw)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 3832) :
    ∃ t, Steps im s 12 12 t ∧ t.pc=pcOf 46376 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 2984 ∧
      t.getReg .x17=BitVec.ofNat 64 30352 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry8 hc s hp (by simp [entry8.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry8.res,E.eval]
  · simp only [Result.toState_getReg,entry8.res]
    t3n []
    have hraw' : s.getMem 131448#64 >>> 37 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp only [Result.toState_getReg,entry8.res]
    t3n [h8]
  · simp [entry8.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry8.res,rv_simp]
#print axioms entry8_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def planCode : List (BitVec 32) := bv_list% 32 [0x1f87913,0x291313,0x690933,0xff9337,0xf9030313,0x690933]
sym_block plan0 := symRun { noAlias := true } planCode (pcOf 45300) 20
sym_block plan1 := symRun { noAlias := true } planCode (pcOf 45434) 20
sym_block plan2 := symRun { noAlias := true } planCode (pcOf 45577) 20
sym_block plan3 := symRun { noAlias := true } planCode (pcOf 45711) 20
sym_block plan4 := symRun { noAlias := true } planCode (pcOf 45854) 20
sym_block plan5 := symRun { noAlias := true } planCode (pcOf 45988) 20
sym_block plan6 := symRun { noAlias := true } planCode (pcOf 46131) 20
sym_block plan7 := symRun { noAlias := true } planCode (pcOf 46265) 20
sym_block plan8 := symRun { noAlias := true } planCode (pcOf 46410) 20
theorem plan_run {b : Nat} (hb : b=45300 ∨ b=45434 ∨ b=45577 ∨ b=45711 ∨ b=45854 ∨ b=45988 ∨ b=46131 ∨ b=46265 ∨ b=46410) :
    symRun { noAlias := true } planCode (pcOf b) 20 = some
      ⟨plan0.res.st,.c (pcOf (b+6)),plan0.res.stop,plan0.res.steps,plan0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact plan0.trans (congrArg some (by kernel_rfl))
  · exact plan1.trans (congrArg some (by kernel_rfl))
  · exact plan2.trans (congrArg some (by kernel_rfl))
  · exact plan3.trans (congrArg some (by kernel_rfl))
  · exact plan4.trans (congrArg some (by kernel_rfl))
  · exact plan5.trans (congrArg some (by kernel_rfl))
  · exact plan6.trans (congrArg some (by kernel_rfl))
  · exact plan7.trans (congrArg some (by kernel_rfl))
  · exact plan8.trans (congrArg some (by kernel_rfl))
theorem plan_steps {im : Image} {b : Nat} (hb : b=45300 ∨ b=45434 ∨ b=45577 ∨ b=45711 ∨ b=45854 ∨ b=45988 ∨ b=46131 ∨ b=46265 ∨ b=46410)
    (hc : CodeAt im (pcOf b) planCode) (s : MachineState) (hp : s.pc=pcOf b)
    (child : Nat) (hchild : child<128) (h16 : s.getReg .x16=BitVec.ofNat 64 child) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getReg .x18=BitVec.ofNat 64 (16748432+5*(child%32)) ∧
      RegsExcept s t [.x6,.x18] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (plan_run hb) hc s hp (by simp [plan0.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getReg,plan0.res]
    t3n [h16]
    have hm : BitVec.ofNat 64 child &&& 31#64 = BitVec.ofNat 64 (child%32) := by
      simpa using SigGolfCandidate.T3M.Sign.ofNat_and_mask child 5 (by decide)
    rw [hm,ofNat_shl]
    simp only [ofNat_add_ofNat]
    congr 1
    norm_num
    omega
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [plan0.res,rv_simp]
#print axioms plan_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
structure ValuesCode (im : Image) (b : Nat) : Prop where
  value0 : CodeAt im (pcOf (b+0)) value0Code
  value1 : CodeAt im (pcOf (b+4)) value1Code
  value2 : CodeAt im (pcOf (b+10)) value2Code
  value3 : CodeAt im (pcOf (b+16)) value3Code
  value4 : CodeAt im (pcOf (b+22)) value4Code
  value5 : CodeAt im (pcOf (b+28)) value5Code
def ValuesW (region A : Nat) : Prop :=
  ∃ i<6, A=region+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2)) ∨ A=region+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2)+8) ∨
    (0 < i ∧ (A=region+672+16*i ∨ A=region+680+16*i))
theorem values_steps {im : Image} {b : Nat} (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376) (hc : ValuesCode im b)
    (s : MachineState) (hp : s.pc=pcOf b) (region source : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 34 34 t ∧ t.pc=pcOf (b+34) ∧
      (∀ i<6,∀ half<2,t.getMem (BitVec.ofNat 64 (region+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8*half))=
        s.getMem (BitVec.ofNat 64 (source+16*i+8*half))) ∧
      (∀ i<6,0 < i → ∀ half<2,t.getMem (BitVec.ofNat 64 (region+672+16*i+8*half))=
        s.getMem (BitVec.ofNat 64 (source+16*i+8*half))) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (ValuesW region) := by
  obtain ⟨t0,st0,p0,v0lo,v0hi,r0,f0⟩ := value0_steps (b:=b+0) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value0 s (by simpa using hp) region source hr0 hr1 hra hs0 hs1 hsa h8 h17
  have fw0 : Frame s t0 (ValuesW region) := f0.mono (by
    intro A hA h
    refine ⟨0,by decide,?_⟩
    omega)
  have r00 := r0
  have f00 := fw0
  obtain ⟨t1,st1,p1,v1lo,v1hi,l1lo,l1hi,r1,f1⟩ := value1_steps (b:=b+4) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value1 t0 (by simpa using p0) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r00.get (by simp),h8]) (by rw [r00.get (by simp),h17])
  have fw1 : Frame t0 t1 (ValuesW region) := f1.mono (by
    intro A hA h
    refine ⟨1,by decide,?_⟩
    omega)
  have r01 : RegsExcept s t1 [.x6,.x7] := (r00.trans r1).mono (by simp)
  have f01 : Frame s t1 (ValuesW region) := (f00.trans fw1).mono (by intro A hA h; exact h.elim id id)
  rw [f00.get (A:=source+16) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v1lo
  rw [f00.get (A:=source+24) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v1hi
  rw [f00.get (A:=source+16) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l1lo
  rw [f00.get (A:=source+24) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l1hi
  obtain ⟨t2,st2,p2,v2lo,v2hi,l2lo,l2hi,r2,f2⟩ := value2_steps (b:=b+10) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value2 t1 (by simpa using p1) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r01.get (by simp),h8]) (by rw [r01.get (by simp),h17])
  have fw2 : Frame t1 t2 (ValuesW region) := f2.mono (by
    intro A hA h
    refine ⟨2,by decide,?_⟩
    omega)
  have r02 : RegsExcept s t2 [.x6,.x7] := (r01.trans r2).mono (by simp)
  have f02 : Frame s t2 (ValuesW region) := (f01.trans fw2).mono (by intro A hA h; exact h.elim id id)
  rw [f01.get (A:=source+32) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v2lo
  rw [f01.get (A:=source+40) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v2hi
  rw [f01.get (A:=source+32) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l2lo
  rw [f01.get (A:=source+40) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l2hi
  obtain ⟨t3,st3,p3,v3lo,v3hi,l3lo,l3hi,r3,f3⟩ := value3_steps (b:=b+16) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value3 t2 (by simpa using p2) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r02.get (by simp),h8]) (by rw [r02.get (by simp),h17])
  have fw3 : Frame t2 t3 (ValuesW region) := f3.mono (by
    intro A hA h
    refine ⟨3,by decide,?_⟩
    omega)
  have r03 : RegsExcept s t3 [.x6,.x7] := (r02.trans r3).mono (by simp)
  have f03 : Frame s t3 (ValuesW region) := (f02.trans fw3).mono (by intro A hA h; exact h.elim id id)
  rw [f02.get (A:=source+48) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v3lo
  rw [f02.get (A:=source+56) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v3hi
  rw [f02.get (A:=source+48) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l3lo
  rw [f02.get (A:=source+56) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l3hi
  obtain ⟨t4,st4,p4,v4lo,v4hi,l4lo,l4hi,r4,f4⟩ := value4_steps (b:=b+22) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value4 t3 (by simpa using p3) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r03.get (by simp),h8]) (by rw [r03.get (by simp),h17])
  have fw4 : Frame t3 t4 (ValuesW region) := f4.mono (by
    intro A hA h
    refine ⟨4,by decide,?_⟩
    omega)
  have r04 : RegsExcept s t4 [.x6,.x7] := (r03.trans r4).mono (by simp)
  have f04 : Frame s t4 (ValuesW region) := (f03.trans fw4).mono (by intro A hA h; exact h.elim id id)
  rw [f03.get (A:=source+64) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v4lo
  rw [f03.get (A:=source+72) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v4hi
  rw [f03.get (A:=source+64) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l4lo
  rw [f03.get (A:=source+72) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l4hi
  obtain ⟨t5,st5,p5,v5lo,v5hi,l5lo,l5hi,r5,f5⟩ := value5_steps (b:=b+28) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value5 t4 (by simpa using p4) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r04.get (by simp),h8]) (by rw [r04.get (by simp),h17])
  have fw5 : Frame t4 t5 (ValuesW region) := f5.mono (by
    intro A hA h
    refine ⟨5,by decide,?_⟩
    omega)
  have r05 : RegsExcept s t5 [.x6,.x7] := (r04.trans r5).mono (by simp)
  have f05 : Frame s t5 (ValuesW region) := (f04.trans fw5).mono (by intro A hA h; exact h.elim id id)
  rw [f04.get (A:=source+80) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v5lo
  rw [f04.get (A:=source+88) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v5hi
  rw [f04.get (A:=source+80) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l5lo
  rw [f04.get (A:=source+88) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l5hi
  have tail4 : Frame t4 t5 (ValuesW region) := fw5
  have exactTail4 := f5
  have tail3 : Frame t3 t5 (ValuesW region) := (fw4.trans tail4).mono (by intro A hA h; exact h.elim id id)
  have exactTail3 := (f4.trans f5)
  have tail2 : Frame t2 t5 (ValuesW region) := (fw3.trans tail3).mono (by intro A hA h; exact h.elim id id)
  have exactTail2 := ((f3.trans f4).trans f5)
  have tail1 : Frame t1 t5 (ValuesW region) := (fw2.trans tail2).mono (by intro A hA h; exact h.elim id id)
  have exactTail1 := (((f2.trans f3).trans f4).trans f5)
  have tail0 : Frame t0 t5 (ValuesW region) := (fw1.trans tail1).mono (by intro A hA h; exact h.elim id id)
  have exactTail0 := ((((f1.trans f2).trans f3).trans f4).trans f5)
  refine ⟨t5,(((((st0.trans st1).trans st2).trans st3).trans st4).trans st5),by simpa using p5,?_,?_,r05,f05⟩
  · intro i hi half hh
    interval_cases i <;> interval_cases half
    · rw [exactTail0.get (by omega) (by omega)]
      simpa using v0lo
    · rw [exactTail0.get (by omega) (by omega)]
      simpa using v0hi
    · rw [exactTail1.get (by omega) (by omega)]
      simpa using v1lo
    · rw [exactTail1.get (by omega) (by omega)]
      simpa using v1hi
    · rw [exactTail2.get (by omega) (by omega)]
      simpa using v2lo
    · rw [exactTail2.get (by omega) (by omega)]
      simpa using v2hi
    · rw [exactTail3.get (by omega) (by omega)]
      simpa using v3lo
    · rw [exactTail3.get (by omega) (by omega)]
      simpa using v3hi
    · rw [exactTail4.get (by omega) (by omega)]
      simpa using v4lo
    · rw [exactTail4.get (by omega) (by omega)]
      simpa using v4hi
    · simpa using v5lo
    · simpa using v5hi
  · intro i hi hz half hh
    have hp : 1 ≤ i := by omega
    interval_cases i <;> interval_cases half
    · rw [exactTail1.get (by omega) (by omega)]
      simpa using l1lo
    · rw [exactTail1.get (by omega) (by omega)]
      simpa using l1hi
    · rw [exactTail2.get (by omega) (by omega)]
      simpa using l2lo
    · rw [exactTail2.get (by omega) (by omega)]
      simpa using l2hi
    · rw [exactTail3.get (by omega) (by omega)]
      simpa using l3lo
    · rw [exactTail3.get (by omega) (by omega)]
      simpa using l3hi
    · rw [exactTail4.get (by omega) (by omega)]
      simpa using l4lo
    · rw [exactTail4.get (by omega) (by omega)]
      simpa using l4hi
    · simpa using l5lo
    · simpa using l5hi
#print axioms values_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def PathsW (dst : Nat → Nat) (n A : Nat) : Prop := ∃ i < n, A=dst i ∨ A=dst i+8
structure PathsInv (s : MachineState) (b source : Nat) (dst : Nat → Nat) (n : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (b+14*n)
  regs : RegsExcept s t [.x6,.x7,.x28]
  frame : Frame s t (PathsW dst n)
  reads : ∀ i<n,∀ half<2,t.getMem (BitVec.ofNat 64 (dst i+8*half))=
    s.getMem (BitVec.ofNat 64 (source+96+16*i+8*half))
theorem paths_join {im : Image} (s : MachineState) (b source : Nat) (dst : Nat → Nat)
    (hp : s.pc=pcOf b) (hd : ∀ j<5,dst j+16<2^64)
    (hdis : ∀ i<5,∀ j<5,i≠j → dst i+16≤dst j ∨ dst j+16≤dst i)
    (hstep : ∀ j<5,∀ u,PathsInv s b source dst j u →
      ∃ t,Steps im u 14 17 t ∧ t.pc=pcOf (b+14*(j+1)) ∧
        (∀ half<2,t.getMem (BitVec.ofNat 64 (dst j+8*half))=
          s.getMem (BitVec.ofNat 64 (source+96+16*j+8*half))) ∧
        RegsExcept u t [.x6,.x7,.x28] ∧ Frame u t (fun A=>A=dst j ∨ A=dst j+8)) :
    ∃ t,Steps im s 70 85 t ∧ PathsInv s b source dst 5 t := by
  have run : ∀ n,n≤5 → ∃ t,Steps im s (14*n) (17*n) t ∧ PathsInv s b source dst n t := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨s,Steps.refl _,?_,RegsExcept.refl _ _,Frame.refl _ _,?_⟩
      · simpa using hp
      · intro i hi; omega
    | succ n ih =>
      intro hn
      obtain ⟨u,su,hu⟩:=ih (by omega)
      obtain ⟨t,st,tp,tr,rr,ff⟩:=hstep n (by omega) u hu
      refine ⟨t,(su.trans st).of_eq (by omega) (by omega),tp,?_,?_,?_⟩
      · exact (hu.regs.trans rr).mono (by simp)
      · exact (hu.frame.trans ff).mono (by
          intro A hA h
          rcases h with h | h
          · obtain ⟨i,hi,h⟩:=h;exact ⟨i,by omega,h⟩
          · exact ⟨n,by omega,h⟩)
      · intro i hi half hh
        by_cases he:i=n
        · subst i;exact tr half hh
        · have hin:i<n:=by omega
          have hsep:=hdis i (by omega) n (by omega) he
          have hbound:=hd i (by omega)
          rw [ff.get (by omega) (by omega)]
          exact hu.reads i hin half hh
  exact run 5 (by omega)
#print axioms paths_join
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
theorem path_cell0 {im : Image} {b : Nat} (hb : b=45306 ∨ b=45440 ∨ b=45583 ∨ b=45717 ∨ b=45860 ∨ b=45994 ∨ b=46137 ∨ b=46271 ∨ b=46416)
    (hlc : CodeAt im (pcOf b) [609795]) (hpc : CodeAt im (pcOf (b+1)) pathCode0)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+0))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/1))) =
        s.getMem (BitVec.ofNat 64 (source+96)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/1)+8)) =
        s.getMem (BitVec.ofNat 64 (source+104)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/1) ∨ A=destination region slot (child/1)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨0,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path0_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
#print axioms path_cell0
theorem path_cell1 {im : Image} {b : Nat} (hb : b=45320 ∨ b=45454 ∨ b=45597 ∨ b=45731 ∨ b=45874 ∨ b=46008 ∨ b=46151 ∨ b=46285 ∨ b=46430)
    (hlc : CodeAt im (pcOf b) [1658371]) (hpc : CodeAt im (pcOf (b+1)) pathCode1)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+1))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/2))) =
        s.getMem (BitVec.ofNat 64 (source+112)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/2)+8)) =
        s.getMem (BitVec.ofNat 64 (source+120)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/2) ∨ A=destination region slot (child/2)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨1,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path1_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
#print axioms path_cell1
theorem path_cell2 {im : Image} {b : Nat} (hb : b=45334 ∨ b=45468 ∨ b=45611 ∨ b=45745 ∨ b=45888 ∨ b=46022 ∨ b=46165 ∨ b=46299 ∨ b=46444)
    (hlc : CodeAt im (pcOf b) [2706947]) (hpc : CodeAt im (pcOf (b+1)) pathCode2)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+2))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/4))) =
        s.getMem (BitVec.ofNat 64 (source+128)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/4)+8)) =
        s.getMem (BitVec.ofNat 64 (source+136)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/4) ∨ A=destination region slot (child/4)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨2,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path2_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
#print axioms path_cell2
theorem path_cell3 {im : Image} {b : Nat} (hb : b=45348 ∨ b=45482 ∨ b=45625 ∨ b=45759 ∨ b=45902 ∨ b=46036 ∨ b=46179 ∨ b=46313 ∨ b=46458)
    (hlc : CodeAt im (pcOf b) [3755523]) (hpc : CodeAt im (pcOf (b+1)) pathCode3)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+3))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/8))) =
        s.getMem (BitVec.ofNat 64 (source+144)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/8)+8)) =
        s.getMem (BitVec.ofNat 64 (source+152)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/8) ∨ A=destination region slot (child/8)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨3,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path3_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
#print axioms path_cell3
theorem path_cell4 {im : Image} {b : Nat} (hb : b=45362 ∨ b=45496 ∨ b=45639 ∨ b=45773 ∨ b=45916 ∨ b=46050 ∨ b=46193 ∨ b=46327 ∨ b=46472)
    (hlc : CodeAt im (pcOf b) [4804099]) (hpc : CodeAt im (pcOf (b+1)) pathCode4)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+4))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/16))) =
        s.getMem (BitVec.ofNat 64 (source+160)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/16)+8)) =
        s.getMem (BitVec.ofNat 64 (source+168)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/16) ∨ A=destination region slot (child/16)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨4,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path4_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
#print axioms path_cell4
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing
open SigGolfCandidate.Research.SharedPathPacking
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- The copied siblings occupy separate aligned digest slots and leave both carried pads intact
(C1, stage 1: the carried R pad of the pinned level-four window `X = 128` is at `+160`). -/
def ScatterSafe (child : Nat) : Prop :=
  (∀ l : Fin 5, block child l.val % 16 = 0 ∧ block child l.val / 16 < 53 ∧
    sibling child l.val + 16 ≤ 320 ∧ sibling child l.val ≠ 160) ∧
  (∀ i l : Fin 5, i ≠ l → sibling child i.val + 16 ≤ sibling child l.val ∨
    sibling child l.val + 16 ≤ sibling child i.val)
theorem scatterSafe : ∀ child : Fin 128, ScatterSafe child.val := by
  intro child
  fin_cases child <;> unfold ScatterSafe <;> decide +kernel

theorem slots_bound (child : Fin 128) (l : Fin 5) : block child.val l.val / 16 < 53 :=
  ((scatterSafe child).1 l).2.1

theorem block_reassemble (child : Fin 128) (l : Fin 5) :
    16 * (block child.val l.val / 16) = block child.val l.val := by
  have h:=((scatterSafe child).1 l).1
  omega

#print axioms scatterSafe
end ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing
open SigGolfCandidate.Research.SharedPathPacking
set_option maxRecDepth 100000
set_option maxHeartbeats 0
end ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def pathWords (j : Fin 5) : List (BitVec 32) :=
  match j.val with | 0=>pathCode0 | 1=>pathCode1 | 2=>pathCode2 | 3=>pathCode3 | _=>pathCode4
structure PathsCode (im : Image) (b : Nat) : Prop where
  load : ∀ j : Fin 5,CodeAt im (pcOf (b+14*j.val)) [BitVec.ofNat 32 (609795+1048576*j.val)]
  path : ∀ j : Fin 5,CodeAt im (pcOf (b+14*j.val+1)) (pathWords j)
theorem path_cell {im : Image} {b : Nat} (hb : b=45306 ∨ b=45440 ∨ b=45583 ∨ b=45717 ∨ b=45860 ∨ b=45994 ∨ b=46137 ∨ b=46271 ∨ b=46416)
    (hc : PathsCode im b) (j : Fin 5)
    (s : MachineState) (hp : s.pc=pcOf (b+14*j.val)) (region source child table slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+j.val))=BitVec.ofNat 8 slot) :
    ∃ t,Steps im s 14 17 t ∧ t.pc=pcOf (b+14*(j.val+1)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/2^j.val)))=
        s.getMem (BitVec.ofNat 64 (source+96+16*j.val)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/2^j.val)+8))=
        s.getMem (BitVec.ofNat 64 (source+96+16*j.val+8)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A=>A=destination region slot (child/2^j.val) ∨ A=destination region slot (child/2^j.val)+8) := by
  fin_cases j
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell0 (b:=b+14*0) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨0,by decide⟩) (by simpa [pathWords] using hc.path ⟨0,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell1 (b:=b+14*1) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨1,by decide⟩) (by simpa [pathWords] using hc.path ⟨1,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell2 (b:=b+14*2) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨2,by decide⟩) (by simpa [pathWords] using hc.path ⟨2,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell3 (b:=b+14*3) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨3,by decide⟩) (by simpa [pathWords] using hc.path ⟨3,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell4 (b:=b+14*4) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨4,by decide⟩) (by simpa [pathWords] using hc.path ⟨4,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte

#print axioms path_cell
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def pathDestination (region child : Nat) (slots : Nat → Nat) (j : Nat) : Nat :=
  destination region (slots j) (child/2^j)
theorem five_paths {im : Image} {b : Nat}
    (hb : b=45306 ∨ b=45440 ∨ b=45583 ∨ b=45717 ∨ b=45860 ∨ b=45994 ∨ b=46137 ∨ b=46271 ∨ b=46416)
    (hc : PathsCode im b) (s : MachineState) (hp : s.pc=pcOf b)
    (region source child table : Nat) (slots : Nat → Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hchild : child<128) (ht0 : 11048 ≤ table) (ht1 : table+5<2^24)
    (hslots : ∀j<5,slots j<53)
    (hdis : ∀i<5,∀j<5,i ≠ j → pathDestination region child slots i+16 ≤ pathDestination region child slots j ∨
      pathDestination region child slots j+16 ≤ pathDestination region child slots i)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (table+j))=BitVec.ofNat 8 (slots j)) :
    ∃ t,Steps im s 70 85 t ∧ PathsInv s b source (pathDestination region child slots) 5 t := by
  have hdst : ∀j<5,pathDestination region child slots j+16 ≤ 11048 := by
    intro j hj
    have hs:=hslots j hj
    unfold pathDestination destination
    omega
  apply paths_join s b source (pathDestination region child slots) hp
    (fun j hj=>by have:=hdst j hj;omega) hdis
  intro j hj u hu
  have ub : u.getByte (BitVec.ofNat 64 (table+j))=BitVec.ofNat 8 (slots j) := by
    rw [hu.frame.getByte (by omega) (by
      rintro ⟨i,hi,h⟩
      have hd:=hdst i (by omega)
      omega)]
    exact hbytes j hj
  obtain ⟨t,st,tp,tlo,thi,tr,tf⟩:=path_cell hb hc ⟨j,hj⟩ u hu.pc region source child table (slots j)
    hr0 hr1 hra hs0 hs1 hsa hchild (hslots j hj) ht1
    (by rw [hu.regs.get (by decide),h8]) (by rw [hu.regs.get (by decide),h16])
    (by rw [hu.regs.get (by decide),h17]) (by rw [hu.regs.get (by decide),h18]) ub
  have oldlo : u.getMem (BitVec.ofNat 64 (source+96+16*j))=s.getMem (BitVec.ofNat 64 (source+96+16*j)) :=
    hu.frame.get (by omega) (by
      rintro ⟨i,hi,h⟩;have hd:=hdst i (by omega);omega)
  have oldhi : u.getMem (BitVec.ofNat 64 (source+96+16*j+8))=s.getMem (BitVec.ofNat 64 (source+96+16*j+8)) :=
    hu.frame.get (by omega) (by
      rintro ⟨i,hi,h⟩;have hd:=hdst i (by omega);omega)
  rw [oldlo] at tlo
  rw [oldhi] at thi
  refine ⟨t,st,tp,?_,tr,tf⟩
  intro half hh
  interval_cases half
  · simpa [pathDestination] using tlo
  · simpa [pathDestination] using thi
#print axioms five_paths
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing
open SigGolfCandidate.Research.SharedPathPacking
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
theorem path_slot (region : Nat) (child : Fin 128) (level : Fin 5) :
    destination region (block child.val level.val / 16) (child.val / 2^level.val) =
      region + sibling child.val level.val := by
  unfold destination sibling bitAt
  rw [block_reassemble child level]
  omega

theorem path_slots_disjoint (region : Nat) (child : Fin 128) (i j : Fin 5) (hne : i ≠ j) :
    destination region (block child.val i.val / 16) (child.val / 2^i.val)+16 ≤
      destination region (block child.val j.val / 16) (child.val / 2^j.val) ∨
    destination region (block child.val j.val / 16) (child.val / 2^j.val)+16 ≤
      destination region (block child.val i.val / 16) (child.val / 2^i.val) := by
  rw [path_slot, path_slot]
  have h:=(scatterSafe child).2 i j hne
  omega

theorem path_slot_bound (region : Nat) (child : Fin 128) (level : Fin 5) :
    region ≤ destination region (block child.val level.val / 16) (child.val / 2^level.val) ∧
    destination region (block child.val level.val / 16) (child.val / 2^level.val)+16 ≤ region+320 := by
  rw [path_slot]
  have h:=((scatterSafe child).1 level).2.2.1
  omega

#print axioms path_slot
#print axioms path_slots_disjoint
#print axioms path_slot_bound
end ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def entryStart (k : Nat) : Nat := [45257, 45387, 45534, 45664, 45811, 45941, 46088, 46218, 46364].getD k 0
def valueStart (k : Nat) : Nat := [45266, 45400, 45543, 45677, 45820, 45954, 46097, 46231, 46376].getD k 0
def planStart (k : Nat) : Nat := [45300, 45434, 45577, 45711, 45854, 45988, 46131, 46265, 46410].getD k 0
def pathStart (k : Nat) : Nat := [45306, 45440, 45583, 45717, 45860, 45994, 46137, 46271, 46416].getD k 0
def topStart (k : Nat) : Nat := [45376, 45523, 45653, 45800, 45930, 46077, 46207, 46354, 46499].getD k 0
def sixthStart (k : Nat) : Nat := [45510, 45787, 46064, 46341, 46486].getD k 0
def entryWords (k : Nat) : List (BitVec 32) := [entry0Code, entry1Code, entry2Code, entry3Code, entry4Code, entry5Code, entry6Code, entry7Code, entry8Code].getD k []
def topWords (k : Nat) : List (BitVec 32) := [topCode0, topCode1, topCode2, topCode3, topCode4, topCode5, topCode6, topCode7, topCode8].getD k []
theorem valuesCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : ValuesCode im (valueStart k.val) := by
  fin_cases k
  · constructor
    · exact SharedCounterHooks.code_slice (off:=210) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=214) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=220) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=226) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=232) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=238) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=344) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=348) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=354) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=360) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=366) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=372) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=487) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=491) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=497) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=503) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=509) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=515) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=621) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=625) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=631) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=637) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=643) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=649) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=764) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=768) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=774) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=780) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=786) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=792) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=898) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=902) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=908) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=914) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=920) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=926) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1041) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1045) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1051) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1057) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1063) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1069) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1175) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1179) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1185) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1191) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1197) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1203) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1320) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1324) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1330) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1336) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1342) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1348) hc (by decide +kernel) (by decide +kernel)
theorem pathsCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : PathsCode im (pathStart k.val) := by
  fin_cases k
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=250) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=264) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=278) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=292) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=306) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=251) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=265) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=279) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=293) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=307) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=384) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=398) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=412) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=426) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=440) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=385) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=399) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=413) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=427) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=441) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=527) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=541) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=555) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=569) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=583) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=528) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=542) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=556) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=570) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=584) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=661) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=675) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=689) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=703) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=717) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=662) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=676) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=690) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=704) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=718) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=804) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=818) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=832) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=846) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=860) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=805) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=819) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=833) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=847) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=861) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=938) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=952) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=966) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=980) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=994) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=939) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=953) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=967) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=981) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=995) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1081) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1095) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1109) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1123) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1137) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1082) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1096) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1110) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1124) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1138) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1215) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1229) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1243) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1257) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1271) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1216) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1230) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1244) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1258) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1272) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1360) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1374) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1388) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1402) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1416) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1361) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1375) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1389) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1403) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1417) hc (by decide +kernel) (by decide +kernel)
theorem planCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : CodeAt im (pcOf (planStart k.val)) planCode := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=244) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=378) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=521) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=655) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=798) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=932) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1075) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1209) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1354) hc (by decide +kernel) (by decide +kernel)
theorem entryCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : CodeAt im (pcOf (entryStart k.val)) (entryWords k.val) := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=201) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=331) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=478) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=608) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=755) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=885) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1032) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1162) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1308) hc (by decide +kernel) (by decide +kernel)
theorem topCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : CodeAt im (pcOf (topStart k.val)) (topWords k.val) := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=320) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=467) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=597) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=744) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=874) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1021) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1151) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1298) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1443) hc (by decide +kernel) (by decide +kernel)
theorem sixthCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 5) : CodeAt im (pcOf (sixthStart k.val)) sixthCode := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=454) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=731) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1008) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1285) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1430) hc (by decide +kernel) (by decide +kernel)
#print axioms valuesCode_of_driver
#print axioms pathsCode_of_driver
#print axioms planCode_of_driver
#print axioms entryCode_of_driver
#print axioms topCode_of_driver
#print axioms sixthCode_of_driver
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing
open SigGolfCandidate.Research.SharedPathPacking
end ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def coordRegion (k : Nat) : Nat := 9768-848*k
def coordSource (k : Nat) : Nat := 28688+208*k
def coordPhysical (k raw : Nat) : Nat := if k<8 ∧ k%2=0 then raw else raw/2+64*(raw%2)
def rawAddress (k : Nat) : Nat := [131424,131424,131432,131432,131440,131440,131448,131448,131448].getD k 0
def rawShift (k : Nat) : Nat := [0,6,0,6,0,6,0,6,37].getD k 0
def entryCycles (k : Nat) : Nat := [9,13,9,13,9,13,9,13,12].getD k 0
theorem coordPhysical_lt (k : Nat) (raw : Fin 128) : coordPhysical k raw.val<128 := by
  unfold coordPhysical
  split_ifs
  · exact raw.isLt
  · have:=Nat.mod_lt raw.val (by decide : 0<2);omega

theorem entry_setup {im : Image} (k : Fin 9)
    (hc : CodeAt im (pcOf (entryStart k.val)) (entryWords k.val))
    (s : MachineState) (hp : s.pc=pcOf (entryStart k.val)) (raw : Fin 128)
    (hraw : s.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 raw.val)
    (h8in : k.val=8 → s.getReg .x8=BitVec.ofNat 64 3832) :
    ∃ t, Steps im s (entryCycles k.val) (entryCycles k.val) t ∧ t.pc=pcOf (valueStart k.val) ∧
      t.getReg .x16=BitVec.ofNat 64 (coordPhysical k.val raw.val) ∧
      t.getReg .x8=BitVec.ofNat 64 (coordRegion k.val) ∧
      t.getReg .x17=BitVec.ofNat 64 (coordSource k.val) ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _=>False) := by
  fin_cases k
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry0_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry1_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry2_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry3_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry4_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry5_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry6_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry7_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry8_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw (h8in rfl)
#print axioms entry_setup
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def topDest (k child : Nat) : Nat := [topDest0 child,topDest1 child,topDest2 child,topDest3 child,topDest4 child,topDest5 child,topDest6 child,topDest7 child,topDest8 child].getD k 0
def topInput (k : Nat) : Nat := if k<8 ∧ k%2=0 then 176 else 192
def nextEntry (k : Nat) : Nat := [45387,45534,45664,45811,45941,46088,46218,46364,46509].getD k 0
def topSteps (k : Nat) : Nat := if k<7 then 11 else 10
theorem top_copy {im : Image} (k : Fin 9)
    (hc : CodeAt im (pcOf (topStart k.val)) (topWords k.val))
    (s : MachineState) (hp : s.pc=pcOf (topStart k.val)) (source : Nat) (child : Fin 128)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h16 : s.getReg .x16=BitVec.ofNat 64 child.val) (h17 : s.getReg .x17=BitVec.ofNat 64 source)
    (h8 : s.getReg .x8=BitVec.ofNat 64 (coordRegion k.val)) :
    ∃ t,Steps im s (topSteps k.val) (topSteps k.val+3) t ∧ t.pc=pcOf (nextEntry k.val) ∧
      (∀half<2,t.getMem (BitVec.ofNat 64 (topDest k.val child.val+8*half))=
        s.getMem (BitVec.ofNat 64 (source+topInput k.val+8*half))) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A=>A=topDest k.val child.val ∨ A=topDest k.val child.val+8) := by
  fin_cases k
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top0_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top1_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top2_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top3_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top4_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top5_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top6_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top7_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17 (by simpa [coordRegion] using h8)
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top8_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17 (by simpa [coordRegion] using h8)
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
#print axioms top_copy
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def PayloadW (region child : Nat) (slots : Nat → Nat) (A : Nat) : Prop :=
  ValuesW region A ∨ PathsW (pathDestination region child slots) 5 A
structure PayloadPost (s : MachineState) (b region source child : Nat) (slots : Nat → Nat)
    (t : MachineState) : Prop where
  pc : t.pc=pcOf (b+110)
  values : ∀ i<6,∀ half<2,t.getMem (BitVec.ofNat 64 (region+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8*half))=
    s.getMem (BitVec.ofNat 64 (source+16*i+8*half))
  ends : ∀ i<6,0 < i → ∀ half<2,t.getMem (BitVec.ofNat 64 (region+672+16*i+8*half))=
    s.getMem (BitVec.ofNat 64 (source+16*i+8*half))
  paths : ∀ i<5,∀ half<2,t.getMem (BitVec.ofNat 64 (pathDestination region child slots i+8*half))=
    s.getMem (BitVec.ofNat 64 (source+96+16*i+8*half))
  regs : RegsExcept s t [.x6,.x7,.x18,.x28]
  frame : Frame s t (PayloadW region child slots)
theorem payload_steps {im : Image} {b : Nat}
    (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376)
    (hv : ValuesCode im b) (hp : CodeAt im (pcOf (b+34)) planCode) (hd : PathsCode im (b+40))
    (s : MachineState) (hpc : s.pc=pcOf b) (region source child : Nat) (slots : Nat → Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hchild : child<128) (hslots : ∀j<5,slots j<53)
    (hdst : ∀j<5,pathDestination region child slots j+16 ≤ region+320)
    (hdis : ∀i<5,∀j<5,i ≠ j → pathDestination region child slots i+16 ≤ pathDestination region child slots j ∨
      pathDestination region child slots j+16 ≤ pathDestination region child slots i)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source)
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(child%32)+j))=BitVec.ofNat 8 (slots j)) :
    ∃ t,Steps im s 110 125 t ∧ PayloadPost s b region source child slots t := by
  obtain ⟨u,su,up,uv,ue,ur,uf⟩:=values_steps hb hv s hpc region source hr0 hr1 hra hs0 hs1 hsa h8 h17
  obtain ⟨v,uvs,vp,vt,vr,vf⟩:=plan_steps (b:=b+34) (by omega) hp u up child hchild
    (by rw [ur.get (by decide),h16])
  have sf : Frame s v (ValuesW region) := (uf.trans vf).mono (by intro A hA h;exact h.elim id False.elim)
  have sr : RegsExcept s v [.x6,.x7,.x18] := (ur.trans vr).mono (by simp)
  have vb : ∀j<5,v.getByte (BitVec.ofNat 64 (16748432+5*(child%32)+j))=BitVec.ofNat 8 (slots j) := by
    intro j hj
    rw [sf.getByte (by have:=Nat.mod_lt child (by decide : 0<32);omega) (by
      rintro ⟨i,hi,h⟩;omega)]
    exact hbytes j hj
  obtain ⟨t,st,ht⟩:=five_paths (b:=b+40) (by omega) hd v (by simpa [Nat.add_assoc] using vp)
    region source child (16748432+5*(child%32)) slots hr0 hr1 hra hs0 hs1 hsa hchild
    (by omega) (by have:=Nat.mod_lt child (by decide : 0<32);omega) hslots hdis
    (by rw [sr.get (by decide),h8]) (by rw [sr.get (by decide),h16])
    (by rw [sr.get (by decide),h17]) vt vb
  refine ⟨t,((su.trans uvs).trans st).of_eq (by omega) (by omega),?_,?_,?_,?_,?_,?_⟩
  · simpa [Nat.add_assoc] using ht.pc
  · intro i hi half hh
    have key := uv i hi half hh
    obtain ⟨ilow, ihigh⟩ : 368 ≤ (640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2)) ∧
        (640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2)) ≤ 680 := by
      rcases (show i=0∨i=1∨i=2∨i=3∨i=4∨i=5 by omega) with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    generalize (640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2)) = ve at key ilow ihigh ⊢
    rw [ht.frame.get (by omega) (by rintro ⟨j,hj,h⟩;have:=hdst j hj;omega)]
    rw [vf.get (by omega) (by simp)]
    exact key
  · intro i hi hip half hh
    rw [ht.frame.get (by omega) (by rintro ⟨j,hj,h⟩;have:=hdst j hj;omega)]
    rw [vf.get (by omega) (by simp)]
    exact ue i hi hip half hh
  · intro i hi half hh
    rw [ht.reads i hi half hh]
    exact sf.get (by omega) (by rintro ⟨j,hj,h⟩;omega)
  · exact (sr.trans ht.regs).mono (by simp)
  · exact (sf.trans ht.frame).mono (by intro A hA h;exact h)
#print axioms payload_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Rv SigGolfCandidate.T3M
theorem installed_values (k : Fin 9) : ValuesCode Images.expandImage (valueStart k.val) :=
  valuesCode_of_driver codeAt_expand_shared_driver k
theorem installed_paths (k : Fin 9) : PathsCode Images.expandImage (pathStart k.val) :=
  pathsCode_of_driver codeAt_expand_shared_driver k
theorem installed_plan (k : Fin 9) : CodeAt Images.expandImage (pcOf (planStart k.val)) planCode :=
  planCode_of_driver codeAt_expand_shared_driver k
theorem installed_entry (k : Fin 9) : CodeAt Images.expandImage (pcOf (entryStart k.val)) (entryWords k.val) :=
  entryCode_of_driver codeAt_expand_shared_driver k
theorem installed_top (k : Fin 9) : CodeAt Images.expandImage (pcOf (topStart k.val)) (topWords k.val) :=
  topCode_of_driver codeAt_expand_shared_driver k
theorem installed_sixth (k : Fin 5) : CodeAt Images.expandImage (pcOf (sixthStart k.val)) sixthCode :=
  sixthCode_of_driver codeAt_expand_shared_driver k
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def SixthW (region child A : Nat) : Prop := A=destination region 49 (child/32) ∨ A=destination region 49 (child/32)+8
structure ExtendedPost (s : MachineState) (region source child : Nat) (slots : Nat → Nat) (t : MachineState) : Prop where
  values : ∀i<6,∀half<2,t.getMem (BitVec.ofNat 64 (region+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8*half))=s.getMem (BitVec.ofNat 64 (source+16*i+8*half))
  ends : ∀ i < 6, 0 < i → ∀half<2,t.getMem (BitVec.ofNat 64 (region+672+16*i+8*half))=s.getMem (BitVec.ofNat 64 (source+16*i+8*half))
  paths : ∀i<5,∀half<2,t.getMem (BitVec.ofNat 64 (pathDestination region child slots i+8*half))=s.getMem (BitVec.ofNat 64 (source+96+16*i+8*half))
  sixth : ∀half<2,t.getMem (BitVec.ofNat 64 (destination region 49 (child/32)+8*half))=s.getMem (BitVec.ofNat 64 (source+176+8*half))
  regs : RegsExcept s t [.x6,.x7,.x18,.x28]
  frame : Frame s t (fun A=>PayloadW region child slots A ∨ SixthW region child A)
theorem payload_sixth {im : Image} {b : Nat}
    (hb : b+110=45510 ∨ b+110=45787 ∨ b+110=46064 ∨ b+110=46341 ∨ b+110=46486)
    (hc : CodeAt im (pcOf (b+110)) sixthCode) {s u : MachineState}
    (region source child : Nat) (slots : Nat → Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0) (hchild : child<128)
    (hdst : ∀j<5,pathDestination region child slots j+16 ≤ region+320)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source)
    (hu : PayloadPost s b region source child slots u) :
    ∃t,Steps im u 13 16 t ∧ t.pc=pcOf (b+123) ∧ ExtendedPost s region source child slots t := by
  obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=sixth_steps_rebased hb hc u hu.pc region source child
    hr0 hr1 hra hs0 hs1 hsa hchild
    (by rw [hu.regs.get (by decide),h8]) (by rw [hu.regs.get (by decide),h16])
    (by rw [hu.regs.get (by decide),h17])
  have hd : region+784 ≤ destination region 49 (child/32) ∧ destination region 49 (child/32)+16 ≤ region+848 := by
    unfold destination
    have:=Nat.mod_lt (child/32) (by decide : 0<2)
    omega
  refine ⟨t,st,by simpa [Nat.add_assoc] using tp,?_,?_,?_,?_,?_,?_⟩
  · intro i hi half hh
    rw [tf.get (by omega) (by omega)]
    exact hu.values i hi half hh
  · intro i hi hip half hh
    rw [tf.get (by omega) (by omega)]
    exact hu.ends i hi hip half hh
  · intro i hi half hh
    have hdi:=hdst i hi
    rw [tf.get (by omega) (by omega)]
    exact hu.paths i hi half hh
  · intro half hh
    have hsfr : ∀off,176 ≤ off → off ≤184 → u.getMem (BitVec.ofNat 64 (source+off))=s.getMem (BitVec.ofNat 64 (source+off)) := by
      intro off hlo hhi
      apply hu.frame.get (by omega)
      rintro (h|h)
      · obtain ⟨j,hj,h⟩:=h;omega
      · obtain ⟨j,hj,h⟩:=h;have:=hdst j hj;omega
    interval_cases half
    · simpa only [Nat.mul_zero,Nat.add_zero,hsfr 176 (by omega) (by omega)] using lo
    · simpa only [Nat.mul_one,show source+176+8=source+184 by omega,hsfr 184 (by omega) (by omega)] using hi
  · exact (hu.regs.trans tr).mono (by simp)
  · exact (hu.frame.trans tf).mono (by intro A hA h;exact h)
#print axioms payload_sixth
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def packedSlots (child j : Nat) : Nat := block child j / 16

theorem payload_packed {im : Image} {b : Nat}
    (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376)
    (hv : ValuesCode im b) (hp : CodeAt im (pcOf (b+34)) planCode) (hd : PathsCode im (b+40))
    (s : MachineState) (hpc : s.pc=pcOf b) (region source : Nat) (child : Fin 128)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child.val)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source)
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=
      BitVec.ofNat 8 (packedSlots child.val j)) :
    ∃t,Steps im s 110 125 t ∧ PayloadPost s b region source child.val (packedSlots child.val) t := by
  apply payload_steps hb hv hp hd s hpc region source child.val (packedSlots child.val)
    hr0 hr1 hra hs0 hs1 hsa child.isLt
    (fun j hj=>Packing.slots_bound child ⟨j,hj⟩) ?_ ?_ h8 h16 h17 hbytes
  · intro j hj
    exact (Packing.path_slot_bound region child ⟨j,hj⟩).2
  · intro i hi j hj hne
    exact Packing.path_slots_disjoint region child ⟨i,hi⟩ ⟨j,hj⟩ (by intro h;exact hne (congrArg Fin.val h))

#print axioms payload_packed
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def firstCoord (k : Nat) : Prop := k<8 ∧ k%2=0
instance (k : Nat) : Decidable (firstCoord k) := inferInstanceAs (Decidable (k<8 ∧ k%2=0))
def bodyInstructions (k : Nat) : Nat := if firstCoord k then 110 else 123
def bodyCycles (k : Nat) : Nat := if firstCoord k then 125 else 141
def LocalW (region child A : Nat) : Prop := PayloadW region child (packedSlots child) A ∨ SixthW region child A
structure BodyPost (s : MachineState) (k child : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (topStart k)
  values : ∀i<6,∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  ends : ∀ i<6,0 < i → ∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+672+16*i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  paths : ∀i<5,∀half<2,t.getMem (BitVec.ofNat 64 (pathDestination (coordRegion k) child (packedSlots child) i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+96+16*i+8*half))
  sixth : ¬firstCoord k → ∀half<2,t.getMem (BitVec.ofNat 64 (destination (coordRegion k) 49 (child/32)+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+176+8*half))
  regs : RegsExcept s t [.x6,.x7,.x18,.x28]
  frame : Frame s t (LocalW (coordRegion k) child)
theorem body_steps {im : Image} (k : Fin 9)
    (hv : ValuesCode im (valueStart k.val))
    (hp : CodeAt im (pcOf (planStart k.val)) planCode)
    (hd : PathsCode im (pathStart k.val))
    (hx : ¬firstCoord k.val → CodeAt im (pcOf (valueStart k.val+110)) sixthCode)
    (s : MachineState) (hpc : s.pc=pcOf (valueStart k.val)) (child : Fin 128)
    (h8 : s.getReg .x8=BitVec.ofNat 64 (coordRegion k.val)) (h16 : s.getReg .x16=BitVec.ofNat 64 child.val)
    (h17 : s.getReg .x17=BitVec.ofNat 64 (coordSource k.val))
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=
      BitVec.ofNat 8 (packedSlots child.val j)) :
    ∃t,Steps im s (bodyInstructions k.val) (bodyCycles k.val) t ∧ BodyPost s k.val child.val t := by
  have hb : valueStart k.val=45266 ∨ valueStart k.val=45400 ∨ valueStart k.val=45543 ∨ valueStart k.val=45677 ∨ valueStart k.val=45820 ∨ valueStart k.val=45954 ∨ valueStart k.val=46097 ∨ valueStart k.val=46231 ∨ valueStart k.val=46376 := by fin_cases k <;> decide
  have hpl : valueStart k.val+34=planStart k.val := by fin_cases k <;> decide
  have hpa : valueStart k.val+40=pathStart k.val := by fin_cases k <;> decide
  have r0 : 2968 ≤ coordRegion k.val := by fin_cases k <;> decide
  have r1 : coordRegion k.val ≤ 10152 := by fin_cases k <;> decide
  have ra : coordRegion k.val%8=0 := by fin_cases k <;> decide
  have s0 : 28672 ≤ coordSource k.val := by fin_cases k <;> decide
  have s1 : coordSource k.val ≤ 31000 := by fin_cases k <;> decide
  have sa : coordSource k.val%8=0 := by fin_cases k <;> decide
  obtain ⟨u,su,hu⟩:=payload_packed hb hv (by rw [hpl];exact hp) (by rw [hpa];exact hd)
    s hpc (coordRegion k.val) (coordSource k.val) child r0 r1 ra s0 s1 sa h8 h16 h17 hbytes
  by_cases hf:firstCoord k.val
  · have pc : valueStart k.val+110=topStart k.val := by fin_cases k <;> simp_all [firstCoord,valueStart,topStart]
    refine ⟨u,by simpa [bodyInstructions,bodyCycles,hf] using su,?_,hu.values,hu.ends,hu.paths,?_,hu.regs,?_⟩
    · simpa [pc] using hu.pc
    · intro hn;exact (hn hf).elim
    · exact hu.frame.mono (by intro A hA h;exact Or.inl h)
  · have h6 : valueStart k.val+110=45510 ∨ valueStart k.val+110=45787 ∨ valueStart k.val+110=46064 ∨ valueStart k.val+110=46341 ∨ valueStart k.val+110=46486 := by
      fin_cases k <;> simp_all [firstCoord,valueStart]
    have pc : valueStart k.val+123=topStart k.val := by fin_cases k <;> simp_all [firstCoord,valueStart,topStart]
    obtain ⟨t,ut,tp,ht⟩:=payload_sixth h6 (hx hf) (coordRegion k.val) (coordSource k.val) child.val (packedSlots child.val)
      r0 r1 ra s0 s1 sa child.isLt (fun j hj=>(Packing.path_slot_bound (coordRegion k.val) child ⟨j,hj⟩).2) h8 h16 h17 hu
    refine ⟨t,?_,?_,ht.values,ht.ends,ht.paths,fun _=>ht.sixth,ht.regs,ht.frame⟩
    · simpa [bodyInstructions,bodyCycles,hf] using su.trans ut
    · simpa [pc] using tp
#print axioms body_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
theorem localW_bounds (region : Nat) (child : Fin 128) (A : Nat)
    (h : LocalW region child.val A) : region ≤ A ∧ A+8 ≤ region+848 := by
  rcases h with (h|h)|h
  · obtain ⟨i,hi,h⟩:=h
    omega
  · obtain ⟨i,hi,h⟩:=h
    have hb:=Packing.path_slot_bound region child ⟨i,hi⟩
    change region ≤ pathDestination region child.val (packedSlots child.val) i ∧
      pathDestination region child.val (packedSlots child.val) i+16 ≤ region+320 at hb
    omega
  · unfold SixthW destination at h
    have:=Nat.mod_lt (child.val/32) (by decide : 0<2)
    omega

theorem topDest_bound (k : Fin 9) (child : Fin 128) : topDest k.val child.val+16 ≤ coordRegion k.val := by
  have h32:=Nat.mod_lt (child.val/32) (by decide : 0<2)
  have h64:=Nat.mod_lt (child.val/64) (by decide : 0<2)
  fin_cases k <;> norm_num [topDest,topDest0,topDest1,topDest2,topDest3,topDest4,topDest5,topDest6,topDest7,topDest8,coordRegion] <;> omega

theorem coordRegion_bounds (k : Fin 9) : 2968 ≤ coordRegion k.val ∧ coordRegion k.val ≤ 10152 ∧ coordRegion k.val%8=0 := by
  fin_cases k <;> decide

theorem coordSource_bounds (k : Fin 9) : 28672 ≤ coordSource k.val ∧ coordSource k.val ≤ 31000 ∧ coordSource k.val%8=0 := by
  fin_cases k <;> decide

def coordinateInstructions (k : Nat) : Nat := entryCycles k+bodyInstructions k+topSteps k
def coordinateCycles (k : Nat) : Nat := entryCycles k+bodyCycles k+topSteps k+3

theorem coordinateTotals : ((List.range 9).map coordinateInstructions).sum=1252 ∧
    ((List.range 9).map coordinateCycles).sum=1429 := by decide
#print axioms localW_bounds
#print axioms topDest_bound
#print axioms coordinateTotals
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
structure CoordinateCode (im : Image) (k : Nat) : Prop where
  entry : CodeAt im (pcOf (entryStart k)) (entryWords k)
  values : ValuesCode im (valueStart k)
  plan : CodeAt im (pcOf (planStart k)) planCode
  paths : PathsCode im (pathStart k)
  sixth : ¬firstCoord k → CodeAt im (pcOf (valueStart k+110)) sixthCode
  top : CodeAt im (pcOf (topStart k)) (topWords k)
def CoordinateW (k child A : Nat) : Prop := LocalW (coordRegion k) child A ∨ A=topDest k child ∨ A=topDest k child+8
structure CoordinatePost (s : MachineState) (k child : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (nextEntry k)
  values : ∀i<6,∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  ends : ∀i<6,0 < i → ∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+672+16*i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  paths : ∀i<5,∀half<2,t.getMem (BitVec.ofNat 64 (pathDestination (coordRegion k) child (packedSlots child) i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+96+16*i+8*half))
  sixth : ¬firstCoord k → ∀half<2,t.getMem (BitVec.ofNat 64 (destination (coordRegion k) 49 (child/32)+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+176+8*half))
  top : ∀half<2,t.getMem (BitVec.ofNat 64 (topDest k child+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+topInput k+8*half))
  regs : RegsExcept s t [.x6,.x7,.x8,.x16,.x17,.x18,.x28]
  frame : Frame s t (CoordinateW k child)
  x8 : t.getReg .x8=BitVec.ofNat 64 (coordRegion k)
theorem coordinate_steps {im : Image} (k : Fin 9) (hc : CoordinateCode im k.val)
    (s : MachineState) (hp : s.pc=pcOf (entryStart k.val)) (raw : Fin 128)
    (hraw : s.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 raw.val)
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(coordPhysical k.val raw.val%32)+j))=
      BitVec.ofNat 8 (packedSlots (coordPhysical k.val raw.val) j))
    (h8in : k.val=8 → s.getReg .x8=BitVec.ofNat 64 3832) :
    ∃t,Steps im s (coordinateInstructions k.val) (coordinateCycles k.val) t ∧
      CoordinatePost s k.val (coordPhysical k.val raw.val) t := by
  let child : Fin 128 := ⟨coordPhysical k.val raw.val,coordPhysical_lt k.val raw⟩
  change ∃t,Steps im s (coordinateInstructions k.val) (coordinateCycles k.val) t ∧ CoordinatePost s k.val child.val t
  have rb:=coordRegion_bounds k
  have sb:=coordSource_bounds k
  obtain ⟨u,su,up,u16,u8,u17,ur,uf⟩:=entry_setup k hc.entry s hp raw hraw h8in
  obtain ⟨v,uv,hv⟩:=body_steps k hc.values hc.plan hc.paths hc.sixth u up child u8 u16 u17 (by
    intro j hj
    rw [uf.getByte (by have:=Nat.mod_lt child.val (by decide : 0<32);omega) (by simp)]
    exact hbytes j hj)
  obtain ⟨t,vt,tp,tt,tr,tf⟩:=top_copy k hc.top v hv.pc (coordSource k.val) child sb.1 sb.2.1 sb.2.2
    (by rw [hv.regs.get (by decide),u16]) (by rw [hv.regs.get (by decide),u17]) (by rw [hv.regs.get (by decide),u8])
  have td:=topDest_bound k child
  have local_eq : ∀A,coordRegion k.val ≤ A → A<2^64 → t.getMem (BitVec.ofNat 64 A)=v.getMem (BitVec.ofNat 64 A) := by
    intro A hA hi
    exact tf.get hi (by omega)
  have bf : Frame s v (LocalW (coordRegion k.val) child.val) :=
    (uf.trans hv.frame).mono (by intro A hA h;exact h.elim False.elim id)
  refine ⟨t,((su.trans uv).trans vt).of_eq (by rfl) (by unfold coordinateCycles;omega),tp,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi half hh
    rw [local_eq _ (by omega) (by omega),hv.values i hi half hh]
    exact uf.get (by omega) (by simp)
  · intro i hi hip half hh
    rw [local_eq _ (by omega) (by omega),hv.ends i hi hip half hh]
    exact uf.get (by omega) (by simp)
  · intro i hi half hh
    have pd:=Packing.path_slot_bound (coordRegion k.val) child ⟨i,hi⟩
    change coordRegion k.val ≤ pathDestination (coordRegion k.val) child.val (packedSlots child.val) i ∧
      pathDestination (coordRegion k.val) child.val (packedSlots child.val) i+16 ≤ coordRegion k.val+320 at pd
    rw [local_eq _ (by omega) (by omega),hv.paths i hi half hh]
    exact uf.get (by omega) (by simp)
  · intro hn half hh
    have ph:=Nat.mod_lt (child.val/32) (by decide : 0<2)
    rw [local_eq _ (by unfold destination;omega) (by unfold destination;omega),hv.sixth hn half hh]
    exact uf.get (by omega) (by simp)
  · intro half hh
    rw [tt half hh]
    have hb : topInput k.val ≤192 := by unfold topInput;split_ifs <;> omega
    apply bf.get (by omega)
    intro hw
    have h:=localW_bounds (coordRegion k.val) child _ hw
    omega
  · exact ((ur.trans hv.regs).trans tr).mono (by simp)
  · exact (bf.trans tf).mono (by intro A hA h;exact h)
  · rw [tr.get (by decide),hv.regs.get (by decide),u8]
#print axioms coordinate_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem localW_pad (region : Nat) (child : Fin 128) (half : Fin 2) (right : Bool) :
    ¬LocalW region child.val (region+(if right then 160 else 672)+8*half.val) := by
  intro h
  rcases h with (h|h)|h
  · obtain ⟨i,hi,h⟩:=h
    cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h <;> omega
  · obtain ⟨i,hi,h⟩:=h
    have hs:=((Packing.scatterSafe child).1 ⟨i,hi⟩)
    dsimp only at hs
    have hmod : sibling child.val i %16=0 := by
      simp only [sibling,Nat.add_mod,Nat.mul_mod,show 48%16=0 from rfl,zero_mul,Nat.zero_mod,Nat.add_zero,hs.1]
    change (region+(if right then 160 else 672)+8*half.val=destination region (block child.val i/16) (child.val/2^i) ∨ region+(if right then 160 else 672)+8*half.val=destination region (block child.val i/16) (child.val/2^i)+8) at h
    rw [Packing.path_slot region child ⟨i,hi⟩] at h
    cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h <;> omega
  · unfold SixthW destination at h
    have:=Nat.mod_lt (child.val/32) (by decide : 0<2)
    cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h <;> omega

theorem localW_pads (region : Nat) (child : Fin 128) (A : Nat)
    (ha:A=region+160 ∨ A=region+168 ∨ A=region+672 ∨ A=region+680) : ¬LocalW region child.val A := by
  rcases ha with rfl|rfl|rfl|rfl
  · exact localW_pad region child 0 true
  · simpa [Nat.add_assoc] using localW_pad region child 1 true
  · exact localW_pad region child 0 false
  · simpa [Nat.add_assoc] using localW_pad region child 1 false

theorem topDest_prev (k : Fin 8) (child : Fin 128) :
    topDest k.val child.val=coordRegion (k.val+1)+160 ∨
    topDest k.val child.val=coordRegion (k.val+1)+672 := by
  have h32:=Nat.mod_lt (child.val/32) (by decide : 0<2)
  have h64:=Nat.mod_lt (child.val/64) (by decide : 0<2)
  fin_cases k <;> norm_num [topDest,topDest0,topDest1,topDest2,topDest3,topDest4,topDest5,topDest6,topDest7,topDest8,coordRegion] <;> omega

theorem coordRegion_gap (j k : Fin 9) (hjk:j.val<k.val) :
    coordRegion k.val+848 ≤ coordRegion j.val := by
  unfold coordRegion
  omega

theorem coordinateW_bounds (k : Fin 9) (child : Fin 128) (A : Nat) (h:CoordinateW k.val child.val A) :
    1200 ≤ A ∧ A+8 ≤ coordRegion k.val+848 := by
  rcases h with h|h|h
  · have hb:=localW_bounds (coordRegion k.val) child A h
    have hr:=coordRegion_bounds k
    omega
  · have hb:=topDest_bound k child
    have hlo : 1216 ≤ topDest k.val child.val := by
      have h32:=Nat.mod_lt (child.val/32) (by decide : 0<2)
      have h64:=Nat.mod_lt (child.val/64) (by decide : 0<2)
      fin_cases k <;> norm_num [topDest,topDest0,topDest1,topDest2,topDest3,topDest4,topDest5,topDest6,topDest7,topDest8] <;> omega
    omega
  · have hb:=topDest_bound k child
    have hlo : 1216 ≤ topDest k.val child.val := by
      have h32:=Nat.mod_lt (child.val/32) (by decide : 0<2)
      have h64:=Nat.mod_lt (child.val/64) (by decide : 0<2)
      fin_cases k <;> norm_num [topDest,topDest0,topDest1,topDest2,topDest3,topDest4,topDest5,topDest6,topDest7,topDest8] <;> omega
    omega

def ReadArea (k child A : Nat) : Prop :=
  (coordRegion k≤A ∧ A+8≤coordRegion k+848) ∨ A=topDest k child ∨ A=topDest k child+8

theorem readArea_disjoint (j k : Fin 9) (hj:j.val<k.val) (cj ck : Fin 128) (A : Nat)
    (ha:ReadArea j.val cj.val A) : ¬CoordinateW k.val ck.val A := by
  intro hw
  have wb:=coordinateW_bounds k ck A hw
  have gap:=coordRegion_gap j k hj
  rcases ha with ha|ha|ha
  · omega
  all_goals
    have j8:j.val<8 := by omega
    have jp : topDest j.val cj.val=coordRegion (j.val+1)+160 ∨ topDest j.val cj.val=coordRegion (j.val+1)+672 := topDest_prev ⟨j.val,j8⟩ cj
    have kd:=topDest_bound k ck
    by_cases hk:k.val=j.val+1
    · have rg : coordRegion k.val=coordRegion (j.val+1) := congrArg coordRegion hk
      rcases hw with hw|hw|hw
      · exact localW_pads (coordRegion k.val) ck A (by rcases jp with jp|jp <;> omega) hw
      · omega
      · omega
    · have g2:coordRegion k.val+848≤coordRegion (j.val+1) := by
        unfold coordRegion
        omega
      omega
#print axioms localW_pad
#print axioms readArea_disjoint
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
structure CoordinateReadout (s : MachineState) (k child : Nat) (t : MachineState) : Prop where
  values : ∀i<6,∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  ends : ∀i<6,0 < i → ∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+672+16*i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  paths : ∀i<5,∀half<2,t.getMem (BitVec.ofNat 64 (pathDestination (coordRegion k) child (packedSlots child) i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+96+16*i+8*half))
  sixth : ¬firstCoord k → ∀half<2,t.getMem (BitVec.ofNat 64 (destination (coordRegion k) 49 (child/32)+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+176+8*half))
  top : ∀half<2,t.getMem (BitVec.ofNat 64 (topDest k child+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+topInput k+8*half))

theorem CoordinatePost.readout {s t : MachineState} {k child : Nat} (h:CoordinatePost s k child t) :
    CoordinateReadout s k child t := ⟨h.values,h.ends,h.paths,h.sixth,h.top⟩

theorem CoordinateReadout.congr {s u v : MachineState} (k : Fin 9) (child : Fin 128)
    (h:CoordinateReadout s k.val child.val u)
    (he:∀A,ReadArea k.val child.val A → v.getMem (BitVec.ofNat 64 A)=u.getMem (BitVec.ofNat 64 A)) :
    CoordinateReadout s k.val child.val v := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi half hh
    rw [he _ (Or.inl ⟨by omega,by omega⟩)]
    exact h.values i hi half hh
  · intro i hi hip half hh
    rw [he _ (Or.inl ⟨by omega,by omega⟩)]
    exact h.ends i hi hip half hh
  · intro i hi half hh
    have hb:=Packing.path_slot_bound (coordRegion k.val) child ⟨i,hi⟩
    change coordRegion k.val≤pathDestination (coordRegion k.val) child.val (packedSlots child.val) i ∧ pathDestination (coordRegion k.val) child.val (packedSlots child.val) i+16≤coordRegion k.val+320 at hb
    rw [he _ (Or.inl ⟨by omega,by omega⟩)]
    exact h.paths i hi half hh
  · intro hn half hh
    have hm:=Nat.mod_lt (child.val/32) (by decide:0<2)
    rw [he _ (Or.inl ⟨by unfold destination;omega,by unfold destination;omega⟩)]
    exact h.sixth hn half hh
  · intro half hh
    rw [he _ (Or.inr (by omega))]
    exact h.top half hh

theorem CoordinateReadout.source {s u t : MachineState} (k : Fin 9) (child : Fin 128)
    (h:CoordinateReadout u k.val child.val t)
    (he:∀A,coordSource k.val≤A → A<coordSource k.val+208 → u.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A)) :
    CoordinateReadout s k.val child.val t := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi half hh
    rw [h.values i hi half hh,he _ (by omega) (by omega)]
  · intro i hi hip half hh
    rw [h.ends i hi hip half hh,he _ (by omega) (by omega)]
  · intro i hi half hh
    rw [h.paths i hi half hh,he _ (by omega) (by omega)]
  · intro hn half hh
    rw [h.sixth hn half hh,he _ (by omega) (by omega)]
  · intro half hh
    have hb:topInput k.val≤192:=by unfold topInput;split_ifs <;>omega
    rw [h.top half hh,he _ (by omega) (by omega)]
#print axioms CoordinateReadout.congr
#print axioms CoordinateReadout.source
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem steps_same {im:Image} {s t u:MachineState} {n c d:Nat}
    (h:Steps im s n c t) (h':Steps im s n d u) : t=u := by
  induction h generalizing d u with
  | refl => cases h';rfl
  | @step s v t ins n c hf hs tail ih =>
    cases h' with
    | @step s' v' u' ins' n' d' hf' hs' tail' =>
      have he:ins'=ins:=Option.some.inj (hf'.symm.trans hf)
      subst ins'
      have hv:v'=v:=Option.some.inj (hs'.symm.trans hs)
      subst v'
      exact ih tail'

def PreciseBodyW (k child A:Nat) : Prop :=
  PayloadW (coordRegion k) child (packedSlots child) A ∨ (¬firstCoord k ∧ SixthW (coordRegion k) child A)

def PreciseCoordinateW (k child A:Nat) : Prop := PreciseBodyW k child A ∨ A=topDest k child ∨ A=topDest k child+8

theorem body_frame_exact {im:Image} (k:Fin 9) (hv:ValuesCode im (valueStart k.val))
    (hp:CodeAt im (pcOf (planStart k.val)) planCode) (hd:PathsCode im (pathStart k.val))
    (hx:¬firstCoord k.val → CodeAt im (pcOf (valueStart k.val+110)) sixthCode)
    (s t:MachineState) (hpc:s.pc=pcOf (valueStart k.val)) (child:Fin 128)
    (h8:s.getReg .x8=BitVec.ofNat 64 (coordRegion k.val)) (h16:s.getReg .x16=BitVec.ofNat 64 child.val)
    (h17:s.getReg .x17=BitVec.ofNat 64 (coordSource k.val))
    (hbytes:∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=BitVec.ofNat 8 (packedSlots child.val j))
    (hst:Steps im s (bodyInstructions k.val) (bodyCycles k.val) t) : Frame s t (PreciseBodyW k.val child.val) := by
  by_cases ha:firstCoord k.val
  · have hb : valueStart k.val=45266 ∨ valueStart k.val=45400 ∨ valueStart k.val=45543 ∨ valueStart k.val=45677 ∨ valueStart k.val=45820 ∨ valueStart k.val=45954 ∨ valueStart k.val=46097 ∨ valueStart k.val=46231 ∨ valueStart k.val=46376 := by fin_cases k <;> decide
    have hpl:valueStart k.val+34=planStart k.val:=by fin_cases k <;>decide
    have hpa:valueStart k.val+40=pathStart k.val:=by fin_cases k <;>decide
    have rb:=coordRegion_bounds k
    have sb:=coordSource_bounds k
    obtain ⟨u,su,hu⟩:=payload_packed hb hv (by rw [hpl];exact hp) (by rw [hpa];exact hd)
      s hpc (coordRegion k.val) (coordSource k.val) child rb.1 rb.2.1 rb.2.2 sb.1 sb.2.1 sb.2.2 h8 h16 h17 hbytes
    have ht:u=t:=steps_same su (by simpa [bodyInstructions,bodyCycles,ha] using hst)
    subst t
    exact hu.frame.mono (by intro A hA h;exact Or.inl h)
  · obtain ⟨u,su,hu⟩:=body_steps k hv hp hd hx s hpc child h8 h16 h17 hbytes
    have ht:u=t:=steps_same su hst
    subst t
    exact hu.frame.mono (by intro A hA h;rcases h with h|h;exact Or.inl h;exact Or.inr ⟨ha,h⟩)

theorem coordinate_frame_exact {im:Image} (k:Fin 9) (hc:CoordinateCode im k.val)
    (s t:MachineState) (hp:s.pc=pcOf (entryStart k.val)) (raw:Fin 128)
    (hraw:s.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 raw.val)
    (hbytes:∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(coordPhysical k.val raw.val%32)+j))=BitVec.ofNat 8 (packedSlots (coordPhysical k.val raw.val) j))
    (hst:Steps im s (coordinateInstructions k.val) (coordinateCycles k.val) t)
    (h8in : k.val=8 → s.getReg .x8=BitVec.ofNat 64 3832) :
    Frame s t (PreciseCoordinateW k.val (coordPhysical k.val raw.val)) := by
  let child:Fin 128:=⟨coordPhysical k.val raw.val,coordPhysical_lt k.val raw⟩
  obtain ⟨u,su,up,u16,u8,u17,ur,uf⟩:=entry_setup k hc.entry s hp raw hraw h8in
  have hbytesu:∀j<5,u.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=BitVec.ofNat 8 (packedSlots child.val j) := by
    intro j hj
    rw [uf.getByte (by have:=Nat.mod_lt child.val (by decide:0<32);omega) (by simp)]
    exact hbytes j hj
  obtain ⟨v,uv,hv⟩:=body_steps k hc.values hc.plan hc.paths hc.sixth u up child u8 u16 u17 hbytesu
  have hf:=body_frame_exact k hc.values hc.plan hc.paths hc.sixth u v up child u8 u16 u17 hbytesu uv
  have sb:=coordSource_bounds k
  obtain ⟨z,vz,zp,zt,zr,zf⟩:=top_copy k hc.top v hv.pc (coordSource k.val) child sb.1 sb.2.1 sb.2.2
    (by rw [hv.regs.get (by decide),u16]) (by rw [hv.regs.get (by decide),u17]) (by rw [hv.regs.get (by decide),u8])
  have hsz:Steps im s (coordinateInstructions k.val) (coordinateCycles k.val) z:=((su.trans uv).trans vz).of_eq (by rfl) (by unfold coordinateCycles;omega)
  have hz:z=t:=steps_same hsz hst
  subst t
  exact ((uf.trans hf).trans zf).mono (by intro A hA h;rcases h with (h|h)|h;exact h.elim;exact Or.inl h;exact Or.inr h)
#print axioms steps_same
#print axioms body_frame_exact
#print axioms coordinate_frame_exact
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def scatterPC (n:Nat) : Nat := if n<9 then entryStart n else 46509
/-- Pairing stage 1: the scatter writes stay below `11000 = WIT + 8096` (the compactor's layer area). -/
def ScatterW (A:Nat) : Prop := 1152≤A ∧ A<11000

theorem preciseCoordinateW_bounds (k : Fin 9) (child : Fin 128) (A : Nat)
    (h : PreciseCoordinateW k.val child.val A) : 1200 ≤ A ∧ A+8 ≤ 11000 := by
  have hr:=coordRegion_bounds k
  have hcw : CoordinateW k.val child.val A := by
    rcases h with (h|⟨_,h⟩)|h|h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hb:=coordinateW_bounds k child A hcw
  refine ⟨hb.1,?_⟩
  rcases h with (h|⟨hf,h⟩)|h|h
  · rcases h with h|h
    · obtain ⟨i,hi,h⟩:=h
      have : coordRegion k.val ≤ 10152 := hr.2.1
      omega
    · obtain ⟨i,hi,h⟩:=h
      have hb:=Packing.path_slot_bound (coordRegion k.val) child ⟨i,hi⟩
      change coordRegion k.val ≤ pathDestination (coordRegion k.val) child.val (packedSlots child.val) i ∧
        pathDestination (coordRegion k.val) child.val (packedSlots child.val) i+16 ≤ coordRegion k.val+320 at hb
      omega
  · have hk : k.val ≠ 0 := by intro h0; apply hf; unfold firstCoord; omega
    have : coordRegion k.val ≤ 9256 := by unfold coordRegion; omega
    omega
  · have hb:=topDest_bound k child; omega
  · have hb:=topDest_bound k child; omega
structure ScatterInv (s : MachineState) (raw:Fin 9 → Fin 128) (n:Nat) (t:MachineState) : Prop where
  pc:t.pc=pcOf (scatterPC n)
  readout:∀k:Fin 9,k.val<n → CoordinateReadout s k.val (coordPhysical k.val (raw k).val) t
  regs:RegsExcept s t [.x6,.x7,.x8,.x16,.x17,.x18,.x28]
  frame:Frame s t ScatterW
  exactFrame:Frame s t (fun A=>∃k:Fin 9,k.val<n ∧ PreciseCoordinateW k.val (coordPhysical k.val (raw k).val) A)
  x8:0<n → t.getReg .x8=BitVec.ofNat 64 (coordRegion (n-1))

def RawAt (s:MachineState) (raw:Fin 9 → Fin 128) : Prop := ∀k:Fin 9,
  s.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 (raw k).val

def PlanAt (s:MachineState) : Prop := ∀child:Fin 128,∀j<5,
  s.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=BitVec.ofNat 8 (packedSlots child.val j)

theorem ScatterInv.next {im:Image} {s t:MachineState} {raw:Fin 9 → Fin 128} (k:Fin 9)
    (hc:CoordinateCode im k.val) (hr:RawAt s raw) (hp:PlanAt s) (hi:ScatterInv s raw k.val t) :
    ∃u,Steps im t (coordinateInstructions k.val) (coordinateCycles k.val) u ∧ ScatterInv s raw (k.val+1) u := by
  have hrawaddr : 11064≤rawAddress k.val ∧ rawAddress k.val<2^64 := by fin_cases k <;> decide
  have hraw : t.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 (raw k).val := by
    rw [hi.frame.get hrawaddr.2 (by unfold ScatterW;omega)]
    exact hr k
  have hpc:t.pc=pcOf (entryStart k.val):=by simpa [scatterPC,k.isLt] using hi.pc
  have hbytes:∀j<5,t.getByte (BitVec.ofNat 64 (16748432+5*(coordPhysical k.val (raw k).val%32)+j))=BitVec.ofNat 8 (packedSlots (coordPhysical k.val (raw k).val) j) := by
    intro j hj
    rw [hi.frame.getByte (by have:=Nat.mod_lt (coordPhysical k.val (raw k).val) (by decide:0<32);omega) (by unfold ScatterW;omega)]
    exact hp ⟨coordPhysical k.val (raw k).val,coordPhysical_lt k.val (raw k)⟩ j hj
  have h8in : k.val=8 → t.getReg .x8=BitVec.ofNat 64 3832 := by
    intro hk8
    rw [hi.x8 (by omega),hk8]
    rfl
  obtain ⟨u,tu,hu⟩:=coordinate_steps k hc t hpc (raw k) hraw hbytes h8in
  have hprecise:=coordinate_frame_exact k hc t u hpc (raw k) hraw hbytes tu h8in
  have hw : ∀A,A<2^64 → PreciseCoordinateW k.val (coordPhysical k.val (raw k).val) A → ScatterW A := by
    intro A hA hw
    have hb:=preciseCoordinateW_bounds k ⟨coordPhysical k.val (raw k).val,coordPhysical_lt k.val (raw k)⟩ A hw
    unfold ScatterW
    omega
  refine ⟨u,tu,?_,?_,(hi.regs.trans hu.regs).mono (by simp),(hi.frame.trans (hprecise.mono hw)).mono (by intro A hA h;exact h.elim id id),?_,fun _=>by simpa using hu.x8⟩
  · have he:nextEntry k.val=scatterPC (k.val+1) := by fin_cases k <;> decide
    simpa [he] using hu.pc
  · intro j hj
    by_cases he:j.val=k.val
    · have je:j=k:=Fin.ext he
      subst j
      apply CoordinateReadout.source k ⟨coordPhysical k.val (raw k).val,coordPhysical_lt k.val (raw k)⟩ hu.readout
      intro A ha hb
      have sb:=coordSource_bounds k
      exact hi.frame.get (by omega) (by unfold ScatterW;omega)
    · have hjk:j.val<k.val:=by omega
      apply (hi.readout j hjk).congr j ⟨coordPhysical j.val (raw j).val,coordPhysical_lt j.val (raw j)⟩
      intro A ha
      have hA:A<2^64 := by
        rcases ha with ha|ha|ha
        · have rb:=coordRegion_bounds j;omega
        · have td:=topDest_bound j ⟨coordPhysical j.val (raw j).val,coordPhysical_lt j.val (raw j)⟩;have rb:=coordRegion_bounds j;omega
        · have td:=topDest_bound j ⟨coordPhysical j.val (raw j).val,coordPhysical_lt j.val (raw j)⟩;have rb:=coordRegion_bounds j;omega
      exact hu.frame.get hA (readArea_disjoint j k hjk ⟨_,coordPhysical_lt j.val (raw j)⟩ ⟨_,coordPhysical_lt k.val (raw k)⟩ A ha)
  · exact (hi.exactFrame.trans hprecise).mono (by
      intro A hA h
      rcases h with ⟨j,hj,h⟩|h
      · exact ⟨j,by omega,h⟩
      · exact ⟨k,by omega,h⟩)

def scatterInstructions (n:Nat) : Nat := ((List.range n).map coordinateInstructions).sum
def scatterCycles (n:Nat) : Nat := ((List.range n).map coordinateCycles).sum

theorem scatter_steps {im:Image} (hc:∀k:Fin 9,CoordinateCode im k.val) (s:MachineState)
    (raw:Fin 9 → Fin 128) (hr:RawAt s raw) (hp:PlanAt s) (hpc:s.pc=pcOf 45257) :
    ∃t,Steps im s 1252 1429 t ∧ ScatterInv s raw 9 t := by
  have hn : ∀n,n≤9 → ∃t,Steps im s (scatterInstructions n) (scatterCycles n) t ∧ ScatterInv s raw n t := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact ⟨s,Steps.refl s,hpc,fun k hk=>by omega,RegsExcept.refl _ _,Frame.refl _ _,Frame.refl _ _,fun h=>absurd h (Nat.lt_irrefl 0)⟩
    | succ n ih =>
      intro hn
      obtain ⟨t,st,ht⟩:=ih (by omega)
      obtain ⟨u,tu,hu⟩:=ht.next ⟨n,by omega⟩ (hc ⟨n,by omega⟩) hr hp
      refine ⟨u,?_,hu⟩
      simpa [scatterInstructions,scatterCycles,List.range_succ] using st.trans tu
  simpa [scatterInstructions,scatterCycles,coordinateTotals.1,coordinateTotals.2] using hn 9 (by decide)
#print axioms ScatterInv.next
#print axioms scatter_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
set_option maxHeartbeats 1000000
theorem coordinateCodes {im:Image}
    (he:∀k:Fin 9,CodeAt im (pcOf (entryStart k.val)) (entryWords k.val))
    (hv:∀k:Fin 9,ValuesCode im (valueStart k.val))
    (hp:∀k:Fin 9,CodeAt im (pcOf (planStart k.val)) planCode)
    (hd:∀k:Fin 9,PathsCode im (pathStart k.val))
    (hx:∀k:Fin 5,CodeAt im (pcOf (sixthStart k.val)) sixthCode)
    (ht:∀k:Fin 9,CodeAt im (pcOf (topStart k.val)) (topWords k.val)) :
    ∀k:Fin 9,CoordinateCode im k.val := by
  intro k
  refine ⟨he k,hv k,hp k,hd k,?_,ht k⟩
  intro hn
  fin_cases k <;> simp only [firstCoord] at hn
  · exact (hn (by decide)).elim
  · exact hx 0
  · exact (hn (by decide)).elim
  · exact hx 1
  · exact (hn (by decide)).elim
  · exact hx 2
  · exact (hn (by decide)).elim
  · exact hx 3
  · exact hx 4
#print axioms coordinateCodes
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv

theorem installed_coordinates : ∀k:Fin 9,CoordinateCode Images.expandImage k.val :=
  coordinateCodes installed_entry installed_values installed_plan installed_paths installed_sixth installed_top
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000

end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem inflated_coordinate_value (b : SharedCodec48.CBytes) (k : Fin 9) (i : Fin 6) :
    SharedCodec.inflatedRead (0 : Digest) (SharedCodec48.digC b) (1+13*k.val+i.val)=
      Paired.coordinateValues (SharedCodec48.sigDecC b).forest k i := by
  fin_cases k <;> fin_cases i <;> rfl

theorem inflated_coordinate_path (b : SharedCodec48.CBytes) (k : Fin 9) (level : Nat)
    (hl : level < if k.val<8 ∧ k.val%2=0 then 6 else 7) :
    SharedCodec.inflatedRead (0 : Digest) (SharedCodec48.digC b) (1+13*k.val+6+level)=
      Paired.coordinatePath (SharedCodec48.sigDecC b).forest k level := by
  fin_cases k <;> norm_num at hl
  all_goals interval_cases level <;> rfl
#print axioms inflated_coordinate_value
#print axioms inflated_coordinate_path
end ClaudeWCT.W9.Machine.Expand.SharedCompact
