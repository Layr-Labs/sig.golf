import SigGolfCandidate.FtsExpandSearch
set_option debug.skipKernelTC true
set_option linter.all false

/-! # Y5 #1: the expand heap-16..31 first-nonce search (`SEARCH16`, 84000..84053) behind a trampoline

A trampoline at word `b` (`trampWords b SEARCH16 ret`) calls `SEARCH16` with `jal a6`. If the coordinate's FTS frame
base `s0` is below `SEL16` (coordinates `4..8`), `SEARCH16` is the plain `ecall` of the replaced fold (84052) and
returns. Otherwise it hashes the 64-byte trial block at `a0` into `SCR16` for nonces `0, 1, ..` (pad at `a0 + 32`),
stops at the first answer whose kept half (the high half iff bit 0 of the node label at `a0 + 16` is clear) has its
top bit 0, or after nonce 255, copies the answer to the real destination `a2`, clears `SCR16`, records (witness pad
address `a0 + WADJ`, nonce) at `slot16 s0`, and restores every register. -/

namespace SigGolfCandidate.FtsGrind
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M publicHash nonceBytes pad64)
open SphincsSecurity (bytesLE bytesLE_length)

attribute [local rv_simp] Result.toState_getReg Result.toState_getMem Result.toState_pc
  Result.toState_code SymState.toState_getReg SymState.toState_getMem SymState.toState_pc
  RegFile.get E.eval BinOp.eval UnOp.eval CmpOp.eval LoadKind.fromWord StoreKind.merge
  Addr.eval memEval_cons memEval_nil BitVec.add_zero Oblig.all Oblig.holds Result.obligs
  Result.toState_getMem Result.pc Result.st Result.steps Result.cycles Result.stop
  SymState.regs SymState.mem SymState.obl BitVec.ofNat_eq_ofNat

/-! ## `SEARCH16` blocks -/

/-- `SEARCH16` slice `[a, b)` (word indices). -/
def sl16 (a b : Nat) : List (BitVec 32) := (search16Words.drop (a - SEARCH16)).take (b - a)

sym_block gS0 := symRun cfgS (sl16 84000 84007) (pcOf 84000) 20
sym_block gS1 := symRun cfgS (sl16 84007 84010) (pcOf 84007) 20
sym_block gSL := symRun cfgS (sl16 84010 84013) (pcOf 84010) 20
sym_block gSC0 := symRun cfgS (sl16 84013 84016) (pcOf 84013) 20
sym_block gSC1 := symRun cfgS (sl16 84016 84018) (pcOf 84016) 20
sym_block gSC2 := symRun cfgS (sl16 84018 84019) (pcOf 84018) 20
sym_block gSC3 := symRun cfgS (sl16 84019 84021) (pcOf 84019) 20
sym_block gSN := symRun cfgS (sl16 84021 84023) (pcOf 84021) 20
sym_block gSJ := symRun cfgS (sl16 84023 84025) (pcOf 84023) 20
sym_block gSF := symRun cfgS (sl16 84025 84052) (pcOf 84025) 40
sym_block gSP := symRun cfgS (sl16 84052 84053) (pcOf 84052) 20
sym_block gSR := symRun cfgS (sl16 84053 84054) (pcOf 84053) 20
sym_block gSRR := symRun cfgS (sl16 84043 84052) (pcOf 84043) 20

theorem code_sl16 {im : Image} (hS : CodeAt im (pcOf SEARCH16) search16Words) (a b : Nat) (ha : SEARCH16 ≤ a)
    (hb : b ≤ SEARCH16 + 54) (hab : a ≤ b) : CodeAt im (pcOf a) (sl16 a b) := by
  have := codeAt_sub (a - SEARCH16) hS (seg := sl16 a b) (by simp [sl16, search16Words_length]; omega) (by simp [sl16])
  rwa [show SEARCH16 + (a - SEARCH16) = a by omega] at this

/-- The one-bit test: `x >> 63 = 0` iff `x < 2^63`. -/
theorem shr63_eq_zero (x : Word) : x >>> 63 = 0#64 ↔ x.toNat < 2 ^ 63 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_zero, Nat.div_eq_zero_iff] at this
    rcases this with h | h
    · exact absurd h (by positivity)
    · exact h
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_zero]
    exact Nat.div_eq_of_lt h

section blocks16
variable {im : Image} (hS : CodeAt im (pcOf SEARCH16) search16Words) (s : MachineState)
include hS

/-- 84000..84006: save `a4 a7 t4 t6`, `t4 := SEL16`, branch to the plain hash (84052) when `s0 < SEL16`. -/
theorem s0_spec (hpc : s.pc = pcOf 84000) (S0 : Nat) (h8 : s.getReg .x8 = BitVec.ofNat 64 S0) (hS0 : S0 < 2 ^ 64) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = (if S0 < SEL16 then pcOf 84052 else pcOf 84007) ∧
      RegsExcept s t [.x29] ∧
      t.getMem (BitVec.ofNat 64 1104) = s.getReg .x14 ∧ t.getMem (BitVec.ofNat 64 1112) = s.getReg .x17 ∧
      t.getMem (BitVec.ofNat 64 1120) = s.getReg .x29 ∧ t.getMem (BitVec.ofNat 64 1128) = s.getReg .x31 ∧
      Frame s t (fun X => 1104 ≤ X ∧ X < 1136) := by
  have hc := code_sl16 hS 84000 84007 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gS0 hc s hpc (by simp [gS0.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gS0.res, rv_simp, h8]
    rw [show (BitVec.ofNat 64 S0).ult _ = decide (S0 < SEL16) from by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS0]; unfold SEL16; rfl]
    by_cases h : S0 < SEL16 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [gS0.res, rv_simp] <;> rfl
  all_goals try (simp only [Result.toState_getMem, gS0.res]; t3n []; done)
  · intro A hA hn
    simp only [Result.toState_getMem, gS0.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- 84007..84009: `a4 := a2`, `a2 := SCR16`, `a7 := 0`. -/
theorem s1_spec (hpc : s.pc = pcOf 84007) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 84010 ∧
      t.getReg .x12 = BitVec.ofNat 64 SCR16 ∧ t.getReg .x14 = s.getReg .x12 ∧ t.getReg .x17 = 0 ∧
      RegsExcept s t [.x12, .x14, .x17] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl16 hS 84007 84010 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gS1 hc s hpc (by simp [gS1.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gS1.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, gS1.res]; t3n [SCR16]
  · simp only [Result.toState_getReg, gS1.res]; t3n []
  · simp only [Result.toState_getReg, gS1.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [gS1.res, rv_simp] <;> rfl
  · intro A _ _; simp [gS1.res, rv_simp]

/-- 84010..84012: pad `a0+32 := a7`, `a0+40 := 0`, then the `ecall`. -/
theorem sl_spec (hpc : s.pc = pcOf 84010) (A : Nat) (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A + 64 ≤ 2 ^ 24) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 84012 ∧ RegsExcept s t [] ∧
      t.getMem (BitVec.ofNat 64 (A + 32)) = s.getReg .x17 ∧ t.getMem (BitVec.ofNat 64 (A + 40)) = 0 ∧
      Frame s t (fun X => X = A + 32 ∨ X = A + 40) ∧ fetch im t = some (.base .ECALL) := by
  have hc := code_sl16 hS 84010 84013 (by decide) (by decide) (by decide)
  have hob : gSL.res.obligs s := by simp only [gSL.res]; t3n [h10]; omega
  refine ⟨_, symRun_sound gSL hc s hpc hob, ?_, ?_, ?_, ?_, ?_, symRun_ecall gSL hc s hob rfl⟩
  · simp [gSL.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp [gSL.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, gSL.res]; t3n [h10]; rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, gSL.res]; t3n [h10]
  · intro X hX hn; simp only [Result.toState_getMem, gSL.res]; t3n [h10]
    rw [if_neg (by omega), if_neg (by omega)]

/-- 84013..84015: the label bit at `a0 + 16` picks the half (odd heap: the low half's top word at 84018). -/
theorem sc0_spec (hpc : s.pc = pcOf 84013) (A : Nat) (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A + 64 ≤ 2 ^ 24) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 (A + 16))) &&& 1#64 = 0#64 then pcOf 84016 else pcOf 84018) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl16 hS 84013 84016 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gSC0 hc s hpc (by simp only [gSC0.res]; t3n [h10]; omega), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gSC0.res, rv_simp, h10, ofNat_add_ofNat, bne_iff_ne, ne_eq]
    by_cases h : s.getMem (BitVec.ofNat 64 (A + 16)) &&& 1#64 = 0#64 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [gSC0.res, rv_simp] <;> rfl
  · intro X _ _; simp [gSC0.res, rv_simp]

/-- 84016..84017: the even heap's high-half top word `SCR16 + 24`. -/
theorem sc1_spec (hpc : s.pc = pcOf 84016) (h12 : s.getReg .x12 = BitVec.ofNat 64 SCR16) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 84019 ∧
      t.getReg .x29 = s.getMem (BitVec.ofNat 64 (SCR16 + 24)) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl16 hS 84016 84018 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gSC1 hc s hpc (by simp only [gSC1.res]; t3n [h12, SCR16]; norm_num), ?_, ?_, ?_, ?_⟩
  · simp [gSC1.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, gSC1.res]; t3n [h12, SCR16]
  · intro r hr; simp at hr; cases r <;> simp_all [gSC1.res, rv_simp] <;> rfl
  · intro X _ _; simp [gSC1.res, rv_simp]

/-- 84018: the odd heap's low-half top word `SCR16 + 8`. -/
theorem sc2_spec (hpc : s.pc = pcOf 84018) (h12 : s.getReg .x12 = BitVec.ofNat 64 SCR16) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 84019 ∧
      t.getReg .x29 = s.getMem (BitVec.ofNat 64 (SCR16 + 8)) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl16 hS 84018 84019 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gSC2 hc s hpc (by simp only [gSC2.res]; t3n [h12, SCR16]; norm_num), ?_, ?_, ?_, ?_⟩
  · simp [gSC2.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, gSC2.res]; t3n [h12, SCR16]
  · intro r hr; simp at hr; cases r <;> simp_all [gSC2.res, rv_simp] <;> rfl
  · intro X _ _; simp [gSC2.res, rv_simp]

/-- 84019..84020: the top-bit test on `t4`. -/
theorem sc3_spec (hpc : s.pc = pcOf 84019) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if (s.getReg .x29).toNat < 2 ^ 63 then pcOf 84025 else pcOf 84021) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl16 hS 84019 84021 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gSC3 hc s hpc (by simp [gSC3.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gSC3.res, rv_simp, beq_iff_eq]
    have hiff := shr63_eq_zero (s.getReg .x29)
    have e63 : ((63#64 : Word).toNat % 64) = 63 := rfl
    simp only [e63]
    by_cases h1 : s.getReg .x29 >>> 63 = 0#64
    · rw [if_pos h1]; exact (if_pos (hiff.mp h1)).symm
    · rw [if_neg h1]; exact (if_neg (fun h => h1 (hiff.mpr h))).symm
  · intro r hr; simp at hr; cases r <;> simp_all [gSC3.res, rv_simp] <;> rfl
  · intro X _ _; simp [gSC3.res, rv_simp]

/-- 84021..84022: stop after nonce 255. -/
theorem sn_spec (hpc : s.pc = pcOf 84021) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if s.getReg .x17 = BitVec.ofNat 64 255 then pcOf 84025 else pcOf 84023) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl16 hS 84021 84023 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gSN hc s hpc (by simp [gSN.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gSN.res, rv_simp, beq_iff_eq]
  · intro r hr; simp at hr; cases r <;> simp_all [gSN.res, rv_simp] <;> rfl
  · intro X _ _; simp [gSN.res, rv_simp]

/-- 84023..84024: next nonce, back to 84010. -/
theorem sj_spec (hpc : s.pc = pcOf 84023) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 84010 ∧ t.getReg .x17 = s.getReg .x17 + 1#64 ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl16 hS 84023 84025 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gSJ hc s hpc (by simp [gSJ.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [gSJ.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, gSJ.res]; simp [rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [gSJ.res, rv_simp] <;> rfl
  · intro A _ _; simp [gSJ.res, rv_simp]

set_option maxHeartbeats 1000000 in
/-- 84025..84051: copy the answer `SCR16 -> D`, clear `SCR16`, record at `slot16 s0`, `a2 := a4`, restore and
clear the saves, return through `a6`. -/
theorem sf_spec (hpc : s.pc = pcOf 84025) (A D S0 R : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (h14 : s.getReg .x14 = BitVec.ofNat 64 D)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 SCR16) (h8 : s.getReg .x8 = BitVec.ofNat 64 S0)
    (h16 : s.getReg .x16 = pcOf R) (hA : A < 2 ^ 24) (hD : D % 8 = 0) (hD1 : 1136 ≤ D) (hD2 : D + 32 ≤ SCR16)
    (hS0 : S0 % 8 = 0) (hS1 : 16 ≤ S0) (hS2 : S0 < 2 ^ 14) :
    ∃ t, Steps im s 27 27 t ∧ t.pc = pcOf R ∧
      t.getReg .x12 = BitVec.ofNat 64 D ∧ t.getReg .x14 = s.getMem (BitVec.ofNat 64 1104) ∧
      t.getReg .x17 = s.getMem (BitVec.ofNat 64 1112) ∧ t.getReg .x29 = s.getMem (BitVec.ofNat 64 1120) ∧
      t.getReg .x31 = s.getMem (BitVec.ofNat 64 1128) ∧ RegsExcept s t [.x12, .x14, .x17, .x29, .x31] ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (D + 8 * k)) = s.getMem (BitVec.ofNat 64 (SCR16 + 8 * k))) ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (SCR16 + 8 * k)) = 0) ∧
      t.getMem (BitVec.ofNat 64 (slot16 S0)) = BitVec.ofNat 64 (A + WADJ) ∧
      t.getMem (BitVec.ofNat 64 (slot16 S0 + 8)) = s.getReg .x17 ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (1104 + 8 * k)) = 0) ∧
      Frame s t (fun X => (X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) ∨ (SCR16 ≤ X ∧ X < SCR16 + 32) ∨
        (slot16 S0 ≤ X ∧ X < slot16 S0 + 16) ∨ (1104 ≤ X ∧ X < 1136)) := by
  have hc := code_sl16 hS 84025 84052 (by decide) (by decide) (by decide)
  simp only [SCR16, slot16, WADJ] at h12 hD2 ⊢
  have hob : gSF.res.obligs s := by
    simp only [gSF.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [Nat.mod_eq_of_lt, not_false_eq_true, and_true, true_and]
    and_intros <;> omega
  refine ⟨_, symRun_sound gSF hc s hpc hob, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear hob
  · simp only [Result.toState_pc, gSF.res]; t3n [h16, pcOf_and_max]
  · simp only [Result.toState_getReg, gSF.res]; t3n [h14]
  · simp only [Result.toState_getReg, gSF.res]; t3n []
  · simp only [Result.toState_getReg, gSF.res]; t3n []
  · simp only [Result.toState_getReg, gSF.res]; t3n []
  · simp only [Result.toState_getReg, gSF.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [gSF.res, rv_simp] <;> rfl
  · intro k hk
    simp only [Result.toState_getMem, gSF.res]; t3n [h10, h14, h12, h8]
    interval_cases k <;> simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, if_pos, if_neg, if_true, if_false] <;> rfl
  · intro k hk
    simp only [Result.toState_getMem, gSF.res]; t3n [h10, h14, h12, h8]
    interval_cases k <;> simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, if_pos, if_neg, if_true, if_false] <;> rfl
  · simp only [Result.toState_getMem, gSF.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]
  · simp only [Result.toState_getMem, gSF.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]
  · intro k hk
    simp only [Result.toState_getMem, gSF.res]; t3n [h10, h14, h12, h8]
    interval_cases k <;> simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, if_pos, if_neg, if_true, if_false] <;> rfl
  · intro X hX hn
    simp only [Result.toState_getMem, gSF.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]

/-- 84052: the plain fold `ecall` of an unselected coordinate. -/
theorem sp_spec (hpc : s.pc = pcOf 84052) :
    ∃ t, Steps im s 0 0 t ∧ t.pc = pcOf 84052 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) ∧
      fetch im t = some (.base .ECALL) := by
  have hc := code_sl16 hS 84052 84053 (by decide) (by decide) (by decide)
  have hob : gSP.res.obligs s := by simp [gSP.res, rv_simp]
  refine ⟨_, symRun_sound gSP hc s hpc hob, ?_, ?_, ?_, symRun_ecall gSP hc s hob rfl⟩
  · simp only [Result.toState_pc, gSP.res, E.eval]
  · intro r _; cases r <;> simp [gSP.res, rv_simp] <;> rfl
  · intro X _ _; simp [gSP.res, rv_simp]

/-- 84053: `j 84043` (the restore tail). -/
theorem sr_spec (hpc : s.pc = pcOf 84053) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 84043 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl16 hS 84053 84054 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gSR hc s hpc (by simp [gSR.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [gSR.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp [gSR.res, rv_simp] <;> rfl
  · intro X _ _; simp [gSR.res, rv_simp]

/-- 84043..84051: restore `a4 a7 t4 t6`, clear the saves, return through `a6`. -/
theorem srr_spec (hpc : s.pc = pcOf 84043) (R : Nat) (h16 : s.getReg .x16 = pcOf R) :
    ∃ t, Steps im s 9 9 t ∧ t.pc = pcOf R ∧
      t.getReg .x14 = s.getMem (BitVec.ofNat 64 1104) ∧ t.getReg .x17 = s.getMem (BitVec.ofNat 64 1112) ∧
      t.getReg .x29 = s.getMem (BitVec.ofNat 64 1120) ∧ t.getReg .x31 = s.getMem (BitVec.ofNat 64 1128) ∧
      RegsExcept s t [.x14, .x17, .x29, .x31] ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (1104 + 8 * k)) = 0) ∧
      Frame s t (fun X => 1104 ≤ X ∧ X < 1136) := by
  have hc := code_sl16 hS 84043 84052 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gSRR hc s hpc (by simp [gSRR.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gSRR.res]; t3n [h16, pcOf_and_max]
  · simp only [Result.toState_getReg, gSRR.res]; t3n []
  · simp only [Result.toState_getReg, gSRR.res]; t3n []
  · simp only [Result.toState_getReg, gSRR.res]; t3n []
  · simp only [Result.toState_getReg, gSRR.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [gSRR.res, rv_simp] <;> rfl
  · intro k hk
    simp only [Result.toState_getMem, gSRR.res]; t3n []
    interval_cases k <;> simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, if_pos, if_neg, if_true, if_false] <;> rfl
  · intro X hX hn
    simp only [Result.toState_getMem, gSRR.res]; t3n []
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]

end blocks16


/-! ## The search loop and the trampoline round trip -/

/-- Cycles of one selected `SEARCH16` round trip (256 trials at most). -/
def W_SEARCH16 : Nat := 21 * 255 + 61
/-- Cycles of an unselected round trip (the plain hash). -/
def W_PLAIN16 : Nat := 40
/-- Cycles of a level-2 round trip: selected (`sel`) or plain. -/
def W16 (sel : Bool) : Nat := if sel then W_SEARCH16 else W_PLAIN16

/-- The kept half has its top bit zero iff its top word is below `2^63`. -/
theorem zeroOkH_iff (hi : Bool) (a : HashOutput) :
    zeroOkH hi 1 a = true ↔ (a.extractLsb' (if hi then 192 else 64) 64).toNat < 2 ^ 63 := by
  unfold zeroOkH halfOf
  rw [decide_eq_true_iff]
  cases hi <;> simp only [Bool.false_eq_true, if_false, if_true, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  · have e : a.toNat / 2 ^ 64 % 2 ^ 64 = a.toNat % 2 ^ 128 / 2 ^ 64 := by
      rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self]
    rw [Nat.pow_zero, Nat.div_one, e, Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
  · have e : a.toNat / 2 ^ 192 % 2 ^ 64 = a.toNat / 2 ^ 128 % 2 ^ 128 / 2 ^ 64 := by
      rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self,
        Nat.div_div_eq_div_mul]
      norm_num
    rw [e, Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]

/-- What follows the trial-`n` hash in `searchH` (fuel = trials left). -/
def sTailH (hi : Bool) (b : Nat) (pre right : List UInt8) : Nat → Nat → HashOutput → M (Nat × HashOutput)
  | 0, n, a => pure (n, a)
  | fuel + 1, n, a => if zeroOkH hi b a then pure (n, a) else searchH hi b pre right fuel (n + 1)

theorem searchH_eq (hi : Bool) (b : Nat) (pre right : List UInt8) (fuel n : Nat) :
    searchH hi b pre right fuel n = publicHash (trialInput pre n right) >>= sTailH hi b pre right fuel n := by
  cases fuel <;> rfl

/-- A `SEARCH16` trampoline call at word `b` returning to `ret`: the trial block at `A` holds `pre` (32 bytes), any
pad, and `right` (16 bytes); the answer goes to `D`; the FTS frame base is `S0`; `hi` is the half the label bit
selects. -/
structure Search16In (b ret A D S0 : Nat) (hi : Bool) (pre right : List UInt8) (s : MachineState) : Prop where
  pc : s.pc = pcOf b
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 S0
  x10 : s.getReg .x10 = BitVec.ofNat 64 A
  x11 : s.getReg .x11 = BitVec.ofNat 64 64
  x12 : s.getReg .x12 = BitVec.ofNat 64 D
  lpre : pre.length = 32
  lright : right.length = 16
  mpre : s.readWords (BitVec.ofNat 64 A) 4 = wordsOf pre
  mright : s.readWords (BitVec.ofNat 64 (A + 48)) 2 = wordsOf right
  label : (s.getMem (BitVec.ofNat 64 (A + 16)) &&& 1#64 = 0#64) ↔ hi = true
  hA : A % 8 = 0
  hA1 : 1144 ≤ A
  hA2 : A + 64 ≤ SCR
  hD : D % 8 = 0
  hD1 : 1144 ≤ D
  hD2 : D + 32 ≤ SCR
  hS0 : S0 % 8 = 0
  hS1 : 16 ≤ S0
  hS2 : S0 < 2 ^ 14
  hb : b + 5 < 2 ^ 18
  hret : ret < 2 ^ 18

/-- Words a selected `SEARCH16` call may write. -/
def Search16W (A D S0 : Nat) (X : Nat) : Prop :=
  (X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) ∨ X = A + 32 ∨ X = A + 40 ∨ (slot16 S0 ≤ X ∧ X < slot16 S0 + 16) ∨
    (1104 ≤ X ∧ X < 1144) ∨ (SCR16 ≤ X ∧ X < SCR16 + 32)

/-- Back at `ret` with the answer of the level-2 ground fold at `D`. -/
structure Search16Out (s : MachineState) (ret A D S0 : Nat) (res : Nat × HashOutput) (t : MachineState) : Prop where
  pc : t.pc = pcOf ret
  regs : RegsExcept s t []
  ans : ∀ k < 4, t.getMem (BitVec.ofNat 64 (D + 8 * k)) = res.2.extractLsb' (64 * k) 64
  nle : res.1 ≤ 255
  pad32 : ¬ (D ≤ A + 32 ∧ A + 32 < D + 32) → t.getMem (BitVec.ofNat 64 (A + 32)) = BitVec.ofNat 64 res.1
  pad40 : ¬ (D ≤ A + 40 ∧ A + 40 < D + 32) → t.getMem (BitVec.ofNat 64 (A + 40)) = 0
  slot0 : t.getMem (BitVec.ofNat 64 (slot16 S0)) = BitVec.ofNat 64 (A + WADJ)
  slot1 : t.getMem (BitVec.ofNat 64 (slot16 S0 + 8)) = BitVec.ofNat 64 res.1
  saves : ∀ k < 5, t.getMem (BitVec.ofNat 64 (1104 + 8 * k)) = 0
  scr : ∀ k < 4, t.getMem (BitVec.ofNat 64 (SCR16 + 8 * k)) = 0
  frame : Frame s t (Search16W A D S0)

/-- Loop words: the pad, the saves and `SCR16`. -/
def Loop16W (A : Nat) (X : Nat) : Prop := X = A + 32 ∨ X = A + 40 ∨ (1104 ≤ X ∧ X < 1144) ∨ (SCR16 ≤ X ∧ X < SCR16 + 32)

def loop16Regs : List Reg := [.x12, .x14, .x16, .x17, .x29]

/-- At word `pcw` of `SEARCH16`, after the entry, with nonce `n`. -/
structure AtS16 (s : MachineState) (b A D pcw n : Nat) (u : MachineState) : Prop where
  pc : u.pc = pcOf pcw
  regs : RegsExcept s u loop16Regs
  x12 : u.getReg .x12 = BitVec.ofNat 64 SCR16
  x14 : u.getReg .x14 = BitVec.ofNat 64 D
  x16 : u.getReg .x16 = pcOf (b + 2)
  x17 : u.getReg .x17 = BitVec.ofNat 64 n
  sv0 : u.getMem (BitVec.ofNat 64 1104) = s.getReg .x14
  sv1 : u.getMem (BitVec.ofNat 64 1112) = s.getReg .x17
  sv2 : u.getMem (BitVec.ofNat 64 1120) = s.getReg .x29
  sv3 : u.getMem (BitVec.ofNat 64 1128) = s.getReg .x31
  sv4 : u.getMem (BitVec.ofNat 64 1136) = s.getReg .x16
  frame : Frame s u (Loop16W A)
  hn : n ≤ 255

/-- After the trial-`n` hash (answer `a` in `SCR16`, pad `n ‖ 0`). -/
structure Hashed16 (u : MachineState) (A n : Nat) (a : HashOutput) : Prop where
  scr : ∀ k < 4, u.getMem (BitVec.ofNat 64 (SCR16 + 8 * k)) = a.extractLsb' (64 * k) 64
  p32 : u.getMem (BitVec.ofNat 64 (A + 32)) = BitVec.ofNat 64 n
  p40 : u.getMem (BitVec.ofNat 64 (A + 40)) = 0


section run16
variable {im : Image} {sk : BitVec 256} {b ret A D S0 : Nat} {hi : Bool} {pre right : List UInt8} {s : MachineState}
  (hS : CodeAt im (pcOf SEARCH16) search16Words) (hT : CodeAt im (pcOf b) (trampWords b SEARCH16 ret))
  (F : Search16In b ret A D S0 hi pre right s)
include hS hT F

/-- The exit 84025 -> `ret`: copy, clear, record, restore; then the trampoline tail. -/
theorem exit16_spec {n : Nat} {a : HashOutput} {v : MachineState} (hv : AtS16 s b A D 84025 n v)
    (hh : Hashed16 v A n a) : TBSim im sk v 30 (pure (n, a)) (Search16Out s ret A D S0) := by
  have hb := F.hb; have hret := F.hret; have hA1 := F.hA1; have hA2 := F.hA2; have hD1 := F.hD1
  have hD2 := F.hD2; have hS1 := F.hS1; have hS2 := F.hS2
  simp only [SCR] at hA2 hD2
  obtain ⟨t1, s1, p1, x12, x14, x17, x29, x31, r1, ans, scr, sl0, sl1, sv, f1⟩ :=
    sf_spec hS v hv.pc A D S0 (b + 2) (by rw [hv.regs.get (by decide)]; exact F.x10) hv.x14 hv.x12
      (by rw [hv.regs.get (by decide)]; exact F.x8) hv.x16 (by omega) F.hD (by omega) (by simp only [SCR16]; omega)
      F.hS0 F.hS1 F.hS2
  obtain ⟨t2, s2, p2, x16, r2, m2, f2⟩ := tramp_tail hT hb hret t1 p1
  have g1136 : t1.getMem (BitVec.ofNat 64 1136) = s.getReg .x16 := by
    rw [f1.get (by decide) (by simp only [SCR16, slot16]; omega), hv.sv4]
  have t2m : ∀ X, X < 2 ^ 64 → X ≠ 1136 → t2.getMem (BitVec.ofNat 64 X) = t1.getMem (BitVec.ofNat 64 X) :=
    fun X hX h => f2.get hX h
  have t1m : ∀ X, X < 2 ^ 64 → ¬ (X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) → ¬ (SCR16 ≤ X ∧ X < SCR16 + 32) →
      ¬ (slot16 S0 ≤ X ∧ X < slot16 S0 + 16) → ¬ (1104 ≤ X ∧ X < 1136) →
      t1.getMem (BitVec.ofNat 64 X) = v.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 h3 h4 =>
    f1.get hX (by rintro (h | h | h | h) <;> contradiction)
  refine tb_pure_steps (s1.trans s2) ⟨p2, ?_, ?_, hv.hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r _
    by_cases h16 : r = .x16
    · subst h16; rw [x16, g1136]
    rw [r2.get (by simpa using h16)]
    by_cases hr : r ∈ [Reg.x12, .x14, .x17, .x29, .x31]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [x12, F.x12]
      · rw [x14, hv.sv0]
      · rw [x17, hv.sv1]
      · rw [x29, hv.sv2]
      · rw [x31, hv.sv3]
    · have hr' : r ∉ loop16Regs := by
        simp only [loop16Regs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto
      rw [r1.get hr, hv.regs.get hr']
  · intro k hk
    rw [t2m _ (by omega) (by omega), ans k hk, hh.scr k hk]
  · intro h
    rw [t2m _ (by omega) (by omega), t1m _ (by omega) (by omega) (by simp only [SCR16]; omega)
      (by simp only [slot16, SCR16]; omega) (by omega), hh.p32]
  · intro h
    rw [t2m _ (by omega) (by omega), t1m _ (by omega) (by omega) (by simp only [SCR16]; omega)
      (by simp only [slot16, SCR16]; omega) (by omega), hh.p40]
  · rw [t2m _ (by simp only [slot16, SCR16]; omega) (by simp only [slot16, SCR16]; omega), sl0]
  · rw [t2m _ (by simp only [slot16, SCR16]; omega) (by simp only [slot16, SCR16]; omega), sl1, hv.x17]
  · intro k hk
    by_cases h4 : k = 4
    · subst h4; exact m2
    · rw [t2m _ (by omega) (by omega), sv k (by omega)]
  · intro k hk
    rw [t2m _ (by simp only [SCR16]; omega) (by simp only [SCR16]; omega), scr k hk]
  · refine ((hv.frame.trans f1).trans f2).mono (fun X _ h => ?_)
    unfold Search16W
    unfold Loop16W at h
    rcases h with ((h | h | h | h) | (h | h | h | h)) | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))

omit hS hT F in
theorem AtS16.move {pcw pcw' n n' : Nat} {u w : MachineState} (h : AtS16 s b A D pcw n u) (hpc : w.pc = pcOf pcw')
    (hr : RegsExcept u w [.x17, .x29]) (hf : Frame u w (fun _ => False)) (h17 : w.getReg .x17 = BitVec.ofNat 64 n')
    (hn : n' ≤ 255) : AtS16 s b A D pcw' n' w where
  pc := hpc
  regs := (h.regs.trans hr).mono (by decide)
  x12 := by rw [hr.get (by decide)]; exact h.x12
  x14 := by rw [hr.get (by decide)]; exact h.x14
  x16 := by rw [hr.get (by decide)]; exact h.x16
  x17 := h17
  sv0 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv0
  sv1 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv1
  sv2 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv2
  sv3 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv3
  sv4 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv4
  frame := (h.frame.trans hf).mono (fun _ _ h => by rcases h with h | h; exact h; exact h.elim)
  hn := hn

omit hS hT F in
theorem Hashed16.move {n : Nat} {a : HashOutput} {u w : MachineState} (h : Hashed16 u A n a)
    (hf : Frame u w (fun _ => False)) (hA : A + 64 ≤ 2 ^ 24) : Hashed16 w A n a where
  scr k hk := by rw [hf.get (by simp only [SCR16]; omega) (fun h => h)]; exact h.scr k hk
  p32 := by rw [hf.get (by omega) (fun h => h)]; exact h.p32
  p40 := by rw [hf.get (by omega) (fun h => h)]; exact h.p40

/-- One trial: pad `n ‖ 0`, then the hash of the trial block into `SCR16`. -/
theorem trial16_spec {β : Type} {n : Nat} {u : MachineState} (hu : AtS16 s b A D 84010 n u) {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (h : ∀ a w, AtS16 s b A D 84013 n w → Hashed16 w A n a → TBSim im sk w W (f a) Q) :
    TBSim im sk u (2 + (8 + W)) (publicHash (trialInput pre n right) >>= f) Q := by
  have hA := F.hA; have hA1 := F.hA1; have hA2 := F.hA2; have hS2 := F.hS2
  simp only [SCR] at hA2
  have hnF : n < 2 ^ 64 := by have h1 := hu.hn; omega
  have g10 : u.getReg .x10 = BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)]; exact F.x10
  obtain ⟨u1, s1, p1, r1, m32, m40, f1, fe1⟩ := sl_spec hS u hu.pc A g10 hA (by omega)
  rw [hu.x17] at m32
  have fs1 : Frame s u1 (Loop16W A) := (hu.frame.trans f1).mono (fun X _ h => by
    rcases h with h | h | h
    · exact h
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have g1 : ∀ x, x ∉ loop16Regs → u1.getReg x = s.getReg x := fun x hx => by
    rw [r1.get (by simp), hu.regs.get hx]
  have h12 : u1.getReg .x12 = BitVec.ofNat 64 SCR16 := by rw [r1.get (by simp)]; exact hu.x12
  have hl := trialInput_length pre right n F.lpre F.lright
  have hq : hashInput u1 = toQ (pad64 (trialInput pre n right)) := by
    rw [pad64_of_aligned _ (by rw [hl])]
    refine hashInput_toQ u1 _ 0 A hl (by rw [g1 _ (by decide)]; exact F.x10) hA (by omega)
      (by rw [g1 _ (by decide)]; exact F.x11) (by norm_num) ?_
    rw [show 8 * (0 + 1) = 4 + 2 + 2 from rfl, readWords_add, readWords_add,
      frame_readWordsG fs1 A 4 (by omega) (fun i hi => by unfold Loop16W; simp only [SCR16]; omega),
      show A + 8 * 4 = A + 32 by ring, readWords_two, m32, m40, show A + 32 + 8 * 2 = A + 48 by ring,
      frame_readWordsG fs1 (A + 48) 2 (by omega) (fun i hi => by unfold Loop16W; simp only [SCR16]; omega),
      F.mpre, F.mright, trialInput, wordsOf_append _ _ (by rw [List.length_append, F.lpre]; simp [nonceBytes,
        bytesLE_length]), wordsOf_append _ _ (by rw [F.lpre]), nonce_words n hnF]
  have hv : hashArgumentsValid u1 = true := hashArgs_const u1 A 64 SCR16 (by rw [g1 _ (by decide)]; exact F.x10)
    (by rw [g1 _ (by decide)]; exact F.x11) h12 hA (by norm_num) (by omega) (by decide) (by decide)
  have h5 : u1.getReg .x5 = 0 := by rw [g1 _ (by decide)]; exact F.x5
  have e := tb_pub (sk := sk) (W := W) (f := f) (Q := Q) fe1 h5 hv hq (fun a => ?_)
  · have := TBSim.steps s1 e
    rwa [trial_blocks pre right n F.lpre F.lright] at this
  have hwf := Frame.writeHash u1 a SCR16 h12 (by decide)
  have fw : Frame s (writeHash u1 a) (Loop16W A) := (fs1.trans hwf).mono (fun X _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inr h)))
  have keep : ∀ X, X < 2 ^ 64 → ¬ (SCR16 ≤ X ∧ X < SCR16 + 32) →
      (writeHash u1 a).getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) := fun X hX h => hwf.get hX h
  have keepu : ∀ X, X < 2 ^ 64 → X ≠ A + 32 → X ≠ A + 40 →
      u1.getMem (BitVec.ofNat 64 X) = u.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 =>
    f1.get hX (by rintro (h | h) <;> contradiction)
  refine h a (writeHash u1 a) ⟨by rw [pc_writeHash, p1, pcOf_add4], fun x hx => by rw [getReg_writeHash, g1 x hx],
    by rw [getReg_writeHash]; exact h12, by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x14,
    by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x16, by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x17,
    by rw [keep _ (by decide) (by simp only [SCR16]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv0,
    by rw [keep _ (by decide) (by simp only [SCR16]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv1,
    by rw [keep _ (by decide) (by simp only [SCR16]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv2,
    by rw [keep _ (by decide) (by simp only [SCR16]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv3,
    by rw [keep _ (by decide) (by simp only [SCR16]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv4,
    fw, hu.hn⟩ ⟨fun k hk => ?_, by rw [keep _ (by omega) (by simp only [SCR16]; omega)]; exact m32,
      by rw [keep _ (by omega) (by simp only [SCR16]; omega)]; exact m40⟩
  rw [getMem_writeHash u1 a SCR16 _ h12 (by decide) (by simp only [SCR16]; omega)]
  interval_cases k <;> simp

/-- The search loop from 84010 with nonce `n` and `fuel` trials after this one. -/
theorem loop16_spec : ∀ fuel n u, AtS16 s b A D 84010 n u → n + fuel = 255 →
    TBSim im sk u (21 * fuel + 49) (searchH hi 1 pre right fuel n) (Search16Out s ret A D S0) := by
  have hA2 := F.hA2; have hA1 := F.hA1; simp only [SCR] at hA2
  -- the label at `a0 + 16` is not written by the loop (the pad is at `a0 + 32`)
  have hlab : ∀ n w, AtS16 s b A D 84013 n w →
      w.getMem (BitVec.ofNat 64 (A + 16)) = s.getMem (BitVec.ofNat 64 (A + 16)) := fun n w hw =>
    hw.frame.get (by omega) (by unfold Loop16W; simp only [SCR16]; omega)
  -- the half test at 84013
  have test : ∀ n a w, AtS16 s b A D 84013 n w → Hashed16 w A n a → ∃ k w1, k ≤ 7 ∧ Steps im w k k w1 ∧
      AtS16 s b A D (if zeroOkH hi 1 a = true then 84025 else 84021) n w1 ∧ Hashed16 w1 A n a := by
    intro n a w hw hh
    have g10 : w.getReg .x10 = BitVec.ofNat 64 A := by rw [hw.regs.get (by decide)]; exact F.x10
    obtain ⟨w1, s1, p1, r1, f1⟩ := sc0_spec hS w hw.pc A g10 F.hA (by omega)
    have hw1 := hw.move (pcw' := if (w.getMem (BitVec.ofNat 64 (A + 16))) &&& 1#64 = 0#64 then 84016 else 84018)
      (by rw [p1]; split_ifs <;> rfl) (r1.mono (by decide)) f1 (by rw [r1.get (by decide)]; exact hw.x17) hw.hn
    have hh1 := hh.move f1 (by omega)
    by_cases hb : (w.getMem (BitVec.ofNat 64 (A + 16))) &&& 1#64 = 0#64
    · have hhi : hi = true := F.label.mp (by rw [← hlab n w hw]; exact hb)
      rw [if_pos hb] at hw1
      obtain ⟨w2, s2, p2, x29, r2, f2⟩ := sc1_spec hS w1 hw1.pc hw1.x12
      obtain ⟨w3, s3, p3, r3, f3⟩ := sc3_spec hS w2 p2
      have e : (w2.getReg .x29).toNat < 2 ^ 63 ↔ zeroOkH hi 1 a = true := by
        rw [x29, zeroOkH_iff, hhi, show SCR16 + 24 = SCR16 + 8 * 3 from rfl, hh1.scr 3 (by decide)]
        simp only [if_true]
      have hpc : w3.pc = pcOf (if zeroOkH hi 1 a = true then 84025 else 84021) := by
        rw [p3]; by_cases hz : zeroOkH hi 1 a = true
        · rw [if_pos (e.mpr hz), if_pos hz]
        · rw [if_neg (fun h => hz (e.mp h)), if_neg hz]
      exact ⟨7, w3, le_rfl, s1.trans (s2.trans s3), hw1.move hpc ((r2.trans r3).mono (by decide))
        ((f2.trans f3).mono (fun _ _ h => by rcases h with h | h <;> exact h))
        (by rw [r3.get (by decide), r2.get (by decide)]; exact hw1.x17) hw.hn,
        (hh1.move f2 (by omega)).move f3 (by omega)⟩
    · have hhi : hi = false := by
        cases hh' : hi
        · rfl
        · exact (hb (by rw [hlab n w hw]; exact F.label.mpr hh')).elim
      rw [if_neg hb] at hw1
      obtain ⟨w2, s2, p2, x29, r2, f2⟩ := sc2_spec hS w1 hw1.pc hw1.x12
      obtain ⟨w3, s3, p3, r3, f3⟩ := sc3_spec hS w2 p2
      have e : (w2.getReg .x29).toNat < 2 ^ 63 ↔ zeroOkH hi 1 a = true := by
        rw [x29, zeroOkH_iff, hhi, show SCR16 + 8 = SCR16 + 8 * 1 from rfl, hh1.scr 1 (by decide)]
        simp only [Bool.false_eq_true, if_false]
      have hpc : w3.pc = pcOf (if zeroOkH hi 1 a = true then 84025 else 84021) := by
        rw [p3]; by_cases hz : zeroOkH hi 1 a = true
        · rw [if_pos (e.mpr hz), if_pos hz]
        · rw [if_neg (fun h => hz (e.mp h)), if_neg hz]
      exact ⟨6, w3, by omega, s1.trans (s2.trans s3), hw1.move hpc ((r2.trans r3).mono (by decide))
        ((f2.trans f3).mono (fun _ _ h => by rcases h with h | h <;> exact h))
        (by rw [r3.get (by decide), r2.get (by decide)]; exact hw1.x17) hw.hn,
        (hh1.move f2 (by omega)).move f3 (by omega)⟩
  -- the cap test at 84021
  have capT : ∀ n a w, AtS16 s b A D 84021 n w → Hashed16 w A n a → ∃ w1, Steps im w 2 2 w1 ∧
      AtS16 s b A D (if n = 255 then 84025 else 84023) n w1 ∧ Hashed16 w1 A n a := by
    intro n a w hw hh
    obtain ⟨w1, s1, p1, r1, f1⟩ := sn_spec hS w hw.pc
    refine ⟨w1, s1, hw.move ?_ (r1.mono (by decide)) f1 (by rw [r1.get (by decide)]; exact hw.x17) hw.hn,
      hh.move f1 (by omega)⟩
    have hnl : n < 2 ^ 64 := by have := hw.hn; omega
    rw [p1, hw.x17]
    by_cases hz : n = 255
    · rw [if_pos (by rw [hz]), if_pos hz]
    · rw [if_neg (fun h => hz ((ofNat_inj hnl (by norm_num)).mp h)), if_neg hz]
  intro fuel
  induction fuel with
  | zero =>
    intro n u hu hn
    simp only [Nat.add_zero] at hn
    rw [searchH_eq]
    refine (trial16_spec hS hT F hu (W := 39) (fun a w hw hh => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨k, w1, hk, s1, hw1, hh1⟩ := test n a w hw hh
    by_cases hz : zeroOkH hi 1 a = true
    · rw [if_pos hz] at hw1
      exact (TBSim.steps s1 (exit16_spec hS hT F hw1 hh1)).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at hw1
      obtain ⟨w2, s2, hw2, hh2⟩ := capT n a w1 hw1 hh1
      rw [if_pos hn] at hw2
      exact (TBSim.steps s1 (TBSim.steps s2 (exit16_spec hS hT F hw2 hh2))).mono (by omega) (fun _ _ h => h)
  | succ fuel ih =>
    intro n u hu hn
    rw [searchH_eq]
    refine (trial16_spec hS hT F hu (W := 21 * fuel + 60) (fun a w hw hh => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨k, w1, hk, s1, hw1, hh1⟩ := test n a w hw hh
    by_cases hz : zeroOkH hi 1 a = true
    · rw [if_pos hz] at hw1
      simp only [sTailH, hz, if_true]
      exact (TBSim.steps s1 (exit16_spec hS hT F hw1 hh1)).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at hw1
      simp only [sTailH, hz, Bool.false_eq_true, if_false]
      obtain ⟨w2, s2, hw2, hh2⟩ := capT n a w1 hw1 hh1
      rw [if_neg (by omega)] at hw2
      obtain ⟨w3, s3, p3, x17, r3, f3⟩ := sj_spec hS w2 hw2.pc
      have hw3 : AtS16 s b A D 84010 (n + 1) w3 := hw2.move p3 (r3.mono (by decide)) f3
        (by rw [x17, hw2.x17, ofNat_add_ofNat]) (by omega)
      have := TBSim.steps s1 (TBSim.steps s2 (TBSim.steps s3 (ih (n + 1) w3 hw3 (by omega))))
      exact this.mono (by omega) (fun _ _ h => h)

/-- **The trampoline round trip into `SEARCH16` on a selected coordinate refines the level-2 ground fold.** -/
theorem tramp_search16 (hsel : SEL16 ≤ S0) :
    TBSim im sk s W_SEARCH16 (groundFoldH hi 1 pre right) (Search16Out s ret A D S0) := by
  have hS2 := F.hS2
  obtain ⟨u0, s0, p0, x16, r0, m0, f0⟩ := tramp_head hT F.hb (by decide) s F.pc
  obtain ⟨u1, s1, p1, r1, sv0, sv1, sv2, sv3, f1⟩ :=
    s0_spec hS u0 p0 S0 (by rw [r0.get (by decide)]; exact F.x8) (by omega)
  rw [if_neg (by omega)] at p1
  obtain ⟨u2, s2, p2, x12, x14, x17, r2, f2⟩ := s1_spec hS u1 p1
  have hu2 : AtS16 s b A D 84010 0 u2 :=
    { pc := p2
      regs := ((r0.trans r1).trans r2).mono (by decide)
      x12 := x12
      x14 := by rw [x14, r1.get (by decide), r0.get (by decide)]; exact F.x12
      x16 := by rw [r2.get (by decide), r1.get (by decide)]; exact x16
      x17 := x17
      sv0 := by rw [f2.get (by decide) (fun h => h), sv0, r0.get (by decide)]
      sv1 := by rw [f2.get (by decide) (fun h => h), sv1, r0.get (by decide)]
      sv2 := by rw [f2.get (by decide) (fun h => h), sv2, r0.get (by decide)]
      sv3 := by rw [f2.get (by decide) (fun h => h), sv3, r0.get (by decide)]
      sv4 := by rw [f2.get (by decide) (fun h => h), f1.get (by decide) (by omega)]; exact m0
      frame := ((f0.trans f1).trans f2).mono (fun X _ h => by
        unfold Loop16W; rcases h with (h | h) | h
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact h.elim)
      hn := Nat.zero_le _ }
  show TBSim im sk s W_SEARCH16 (searchH hi 1 pre right 255 0) _
  have := TBSim.steps s0 (TBSim.steps s1 (TBSim.steps s2
    (loop16_spec (sk := sk) hS hT F 255 0 u2 hu2 (by omega))))
  exact this.mono (by unfold W_SEARCH16; omega) (fun _ _ h => h)

end run16


/-! ## The unselected path (coordinates 4..8): the plain hash -/

/-- Back at `ret` after an unselected `SEARCH16` call: the hash `a` at `D`, saves cleared. -/
structure Plain16Out (s : MachineState) (ret D : Nat) (a : HashOutput) (t : MachineState) : Prop where
  pc : t.pc = pcOf ret
  regs : RegsExcept s t []
  ans : ∀ k < 4, t.getMem (BitVec.ofNat 64 (D + 8 * k)) = a.extractLsb' (64 * k) 64
  saves : ∀ k < 5, t.getMem (BitVec.ofNat 64 (1104 + 8 * k)) = 0
  frame : Frame s t (fun X => (X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) ∨ (1104 ≤ X ∧ X < 1144))

theorem blocks64 (inp : List UInt8) (hl : inp.length = 64) : (toQ (pad64 inp)).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [hl]), blocks_toQ ⟨by rw [hl]; omega, by rw [hl]⟩, hl]

/-- **The trampoline round trip into `SEARCH16` on an unselected coordinate is the plain hash** of the block at `A`
into `D`. -/
theorem tramp_plain16 {im : Image} {sk : BitVec 256} {b ret A D S0 : Nat} {inp : List UInt8} {s : MachineState}
    (hS : CodeAt im (pcOf SEARCH16) search16Words) (hT : CodeAt im (pcOf b) (trampWords b SEARCH16 ret))
    (hpc : s.pc = pcOf b) (h5 : s.getReg .x5 = 0) (h8 : s.getReg .x8 = BitVec.ofNat 64 S0) (hsel : S0 < SEL16)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (h11 : s.getReg .x11 = BitVec.ofNat 64 64)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 D) (hl : inp.length = 64)
    (hq0 : hashInput s = toQ (pad64 inp)) (hA : A % 8 = 0) (hA1 : 1144 ≤ A)
    (hA2 : A + 64 ≤ 2 ^ 24) (hD : D % 8 = 0) (hD1 : 1144 ≤ D) (hD2 : D + 32 ≤ 2 ^ 24)
    (hb : b + 5 < 2 ^ 18) (hret : ret < 2 ^ 18) :
    TBSim im sk s W_PLAIN16 (publicHash inp) (Plain16Out s ret D) := by
  obtain ⟨u0, s0, p0, x16, r0, m0, f0⟩ := tramp_head hT hb (by decide) s hpc
  obtain ⟨u1, s1, p1, r1, sv0, sv1, sv2, sv3, f1⟩ :=
    s0_spec hS u0 p0 S0 (by rw [r0.get (by decide)]; exact h8) (by unfold SEL16 at hsel; omega)
  rw [if_pos hsel] at p1
  obtain ⟨u2, s2, p2, r2, f2, fe⟩ := sp_spec hS u1 p1
  have g : ∀ x, x ≠ .x16 → x ≠ .x29 → u2.getReg x = s.getReg x := fun x a b => by
    rw [r2.get (by simp), r1.get (by simpa using b), r0.get (by simpa using a)]
  have fu : Frame s u2 (fun X => 1104 ≤ X ∧ X < 1144) := ((f0.trans f1).trans f2).mono (fun X _ h => by
    rcases h with (h | h) | h
    · omega
    · omega
    · exact h.elim)
  have g10 : u2.getReg .x10 = BitVec.ofNat 64 A := by rw [g _ (by decide) (by decide)]; exact h10
  have g11 : u2.getReg .x11 = BitVec.ofNat 64 64 := by rw [g _ (by decide) (by decide)]; exact h11
  have g12 : u2.getReg .x12 = BitVec.ofNat 64 D := by rw [g _ (by decide) (by decide)]; exact h12
  have hq : hashInput u2 = toQ (pad64 inp) := by
    have hAl : (BitVec.ofNat 64 A).toNat % 8 = 0 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show A < 2 ^ 64 by omega)]; exact hA
    rw [← hq0, hashInput_eq_words u2 0 (by rw [g11]) (by norm_num) (by rw [g10]; exact hAl),
      hashInput_eq_words s 0 (by rw [h11]) (by norm_num) (by rw [h10]; exact hAl), g10, h10,
      show 8 * (0 + 1) = 8 from rfl, frame_readWordsG fu A 8 (by omega) (fun i hi => by omega)]
  have hv : hashArgumentsValid u2 = true := hashArgs_const u2 A 64 D g10 g11 g12 hA (by norm_num) (by omega) hD
    (by omega)
  have e := tb_pub (sk := sk) (W := 13) (f := pure) (Q := Plain16Out s ret D) fe
    (by rw [g _ (by decide) (by decide)]; exact h5) hv hq (fun a => ?_)
  · rw [bind_pure, blocks64 inp hl] at e
    exact (TBSim.steps s0 (TBSim.steps s1 (TBSim.steps s2 e))).mono (by unfold W_PLAIN16; omega) (fun _ _ h => h)
  set w := writeHash u2 a with hw
  have wp : w.pc = pcOf 84053 := by rw [hw, pc_writeHash, p2, pcOf_add4]
  obtain ⟨w1, s3, p3, r3, f3⟩ := sr_spec hS w wp
  have x16w : w1.getReg .x16 = pcOf (b + 2) := by
    rw [r3.get (by simp), hw, getReg_writeHash, r2.get (by simp), r1.get (by decide)]; exact x16
  obtain ⟨w2, s4, p4, y14, y17, y29, y31, r4, z4, f4⟩ := srr_spec hS w1 p3 (b + 2) x16w
  obtain ⟨w3, s5, p5, y16, r5, m5, f5⟩ := tramp_tail hT hb hret w2 p4
  have fw : Frame u2 w (fun X => X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) := by
    intro X hX hn
    simp only [not_or] at hn
    rw [hw, getMem_writeHash u2 a D X g12 (by omega) hX, if_neg hn.1, if_neg hn.2.1, if_neg hn.2.2.1, if_neg hn.2.2.2]
  -- the saves: `u1` holds the entry registers, kept to `w1`
  have keep1 : ∀ X, X < 2 ^ 64 → ¬ (X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) →
      w1.getMem (BitVec.ofNat 64 X) = u2.getMem (BitVec.ofNat 64 X) :=
    fun X hX h => by rw [f3.get hX (fun h => h), fw.get hX h]
  have u21 : ∀ X, X < 2 ^ 64 → u2.getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) :=
    fun X hX => f2.get hX (fun h => h)
  have e1104 : w1.getMem (BitVec.ofNat 64 1104) = s.getReg .x14 := by
    rw [keep1 _ (by decide) (by omega), u21 _ (by decide), sv0, r0.get (by decide)]
  have e1112 : w1.getMem (BitVec.ofNat 64 1112) = s.getReg .x17 := by
    rw [keep1 _ (by decide) (by omega), u21 _ (by decide), sv1, r0.get (by decide)]
  have e1120 : w1.getMem (BitVec.ofNat 64 1120) = s.getReg .x29 := by
    rw [keep1 _ (by decide) (by omega), u21 _ (by decide), sv2, r0.get (by decide)]
  have e1128 : w1.getMem (BitVec.ofNat 64 1128) = s.getReg .x31 := by
    rw [keep1 _ (by decide) (by omega), u21 _ (by decide), sv3, r0.get (by decide)]
  have e1136 : w2.getMem (BitVec.ofNat 64 1136) = s.getReg .x16 := by
    rw [f4.get (by decide) (by omega), keep1 _ (by decide) (by omega), u21 _ (by decide),
      f1.get (by decide) (by omega)]
    exact m0
  refine tb_pure_steps (s3.trans (s4.trans s5)) ⟨p5, fun r _ => ?_, fun k hk => ?_, fun k hk => ?_, ?_⟩
  · by_cases h16 : r = .x16
    · subst h16; rw [y16, e1136]
    rw [r5.get (by simpa using h16)]
    by_cases hr : r ∈ [Reg.x14, .x17, .x29, .x31]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [y14, e1104]
      · rw [y17, e1112]
      · rw [y29, e1120]
      · rw [y31, e1128]
    · have h29 : r ≠ .x29 := by rintro rfl; simp at hr
      rw [r4.get hr, r3.get (by simp), hw, getReg_writeHash, g r h16 h29]
  · rw [f5.get (by omega) (by omega), f4.get (by omega) (by omega), f3.get (by omega) (fun h => h), hw,
      getMem_writeHash u2 a D _ g12 (by omega) (by omega)]
    interval_cases k <;> simp
  · by_cases h4 : k = 4
    · subst h4; exact m5
    · rw [f5.get (by omega) (by omega), z4 k (by omega)]
  · intro X hX hn
    simp only [not_or] at hn
    rw [f5.get hX (by omega), f4.get hX (by omega), keep1 X hX (by omega), fu.get hX (by omega)]

end SigGolfCandidate.FtsGrind
