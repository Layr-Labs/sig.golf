import SigGolfCandidate.T3M_Keygen_Tree
import SigGolfCandidate.T3M_Keygen_SimB

/-!
# Keygen top tree with node nonces (top-bytes layer, opus-topbytes A)

The keygen tree routine (subroutine at 117, offsets 113..159) is hooked at three words:
* 230 (`b + 113`) `jal 721` (KINIT: `s4 = 1`, `a3 = 1`, back to 231);
* 274 (`b + 157`) `jal 724` (KNEXT: `s4 >>= 1`, `a3 += 1`, back to 233);
* 264 (`b + 147`, right after the node hash) `jal 727` (KCHK): `a3` is the height `h` of the node level. For `h = 12`
  (the root) go straight to KOK; else `b = min (max h 2) 8`, the mask `a6` (top `b` bits of the high word, or
  `0xFF << 40` for `h = 11`) and the cap `a7 = 104 << b`; then the trial loop 746..759: test the high word of the
  selected half, on failure `pad += 1` (`NODE + 32`) and rehash unless `pad` reached the cap (then the last trial is
  kept). KOK 760..769 resets the pad and runs the original node store, then 272..273.

This file proves the blocks and the bounded refinement (`TBSim`) of `T3.buildTopLevels`.
-/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest nodeHash topZeroBits topNonceCap topZeroOk nonceBytes topNodeInput topNodeHashN
  topNonceSearch topNodeAt buildTopLevel buildTopLevels pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)

local instance instDecidableCodeAtTopTree (image : Image) (pc : Word) (code : List (BitVec 32)) :
    Decidable (CodeAt image pc code) := by
  unfold CodeAt
  infer_instance

/-! ## Blocks -/
def kt230 : List (BitVec 32) := sub113K.take 1
def kt231 : List (BitVec 32) := sub113K.drop 1
def kt264 : List (BitVec 32) := sub147K.take 1
def kt272 : List (BitVec 32) := sub147K.drop 8
def kt274 : List (BitVec 32) := sub157K.take 1
def ktI : List (BitVec 32) := kchkCode.take 3
def ktN : List (BitVec 32) := (kchkCode.drop 3).take 3
def ktC0 : List (BitVec 32) := (kchkCode.drop 6).take 2
def ktC1 : List (BitVec 32) := (kchkCode.drop 8).take 3
def ktC2 : List (BitVec 32) := (kchkCode.drop 11).take 1
def ktC3 : List (BitVec 32) := (kchkCode.drop 12).take 2
def ktC5 : List (BitVec 32) := (kchkCode.drop 15).take 6
def ktC6 : List (BitVec 32) := (kchkCode.drop 21).take 2
def ktC7 : List (BitVec 32) := (kchkCode.drop 23).take 2
def ktL0 : List (BitVec 32) := (kchkCode.drop 25).take 4
def ktL1 : List (BitVec 32) := (kchkCode.drop 29).take 4
def ktL2 : List (BitVec 32) := (kchkCode.drop 33).take 4
def ktL3 : List (BitVec 32) := (kchkCode.drop 38).take 1
def ktOK : List (BitVec 32) := (kchkCode.drop 39).take 10

theorem codeAt_kt230 : CodeAt image (pcOf 230) kt230 := by decide +kernel
theorem codeAt_kt231 : CodeAt image (pcOf 231) kt231 := by decide +kernel
theorem codeAt_kt264 : CodeAt image (pcOf 264) kt264 := by decide +kernel
theorem codeAt_kt272 : CodeAt image (pcOf 272) kt272 := by decide +kernel
theorem codeAt_kt274 : CodeAt image (pcOf 274) kt274 := by decide +kernel
theorem codeAt_ktI : CodeAt image (pcOf 721) ktI := by decide +kernel
theorem codeAt_ktN : CodeAt image (pcOf 724) ktN := by decide +kernel
theorem codeAt_ktC0 : CodeAt image (pcOf 727) ktC0 := by decide +kernel
theorem codeAt_ktC1 : CodeAt image (pcOf 729) ktC1 := by decide +kernel
theorem codeAt_ktC2 : CodeAt image (pcOf 732) ktC2 := by decide +kernel
theorem codeAt_ktC3 : CodeAt image (pcOf 733) ktC3 := by decide +kernel
theorem codeAt_ktC5 : CodeAt image (pcOf 736) ktC5 := by decide +kernel
theorem codeAt_ktC6 : CodeAt image (pcOf 742) ktC6 := by decide +kernel
theorem codeAt_ktC7 : CodeAt image (pcOf 744) ktC7 := by decide +kernel
theorem codeAt_ktL0 : CodeAt image (pcOf 746) ktL0 := by decide +kernel
theorem codeAt_ktL1 : CodeAt image (pcOf 750) ktL1 := by decide +kernel
theorem codeAt_ktL2 : CodeAt image (pcOf 754) ktL2 := by decide +kernel
theorem codeAt_kt758 : CodeAt image (pcOf 758) [115] := by decide +kernel
theorem codeAt_ktL3 : CodeAt image (pcOf 759) ktL3 := by decide +kernel
theorem codeAt_ktOK : CodeAt image (pcOf 760) ktOK := by decide +kernel

sym_block bt230 := symRun { noAlias := true } kt230 (pcOf 230) 100
sym_block bt231 := symRun { noAlias := true } kt231 (pcOf 231) 100
sym_block bt264 := symRun { noAlias := true } kt264 (pcOf 264) 100
sym_block bt272 := symRun { noAlias := true } kt272 (pcOf 272) 100
sym_block bt274 := symRun { noAlias := true } kt274 (pcOf 274) 100
sym_block btI := symRun { noAlias := true } ktI (pcOf 721) 100
sym_block btN := symRun { noAlias := true } ktN (pcOf 724) 100
sym_block btC0 := symRun { noAlias := true } ktC0 (pcOf 727) 100
sym_block btC1 := symRun { noAlias := true } ktC1 (pcOf 729) 100
sym_block btC2 := symRun { noAlias := true } ktC2 (pcOf 732) 100
sym_block btC3 := symRun { noAlias := true } ktC3 (pcOf 733) 100
sym_block btC5 := symRun { noAlias := true } ktC5 (pcOf 736) 100
sym_block btC6 := symRun { noAlias := true } ktC6 (pcOf 742) 100
sym_block btC7 := symRun { noAlias := true } ktC7 (pcOf 744) 100
sym_block btL0 := symRun { noAlias := true } ktL0 (pcOf 746) 100
sym_block btL1 := symRun { noAlias := true } ktL1 (pcOf 750) 100
sym_block btL2 := symRun { noAlias := true } ktL2 (pcOf 754) 100
sym_block btL3 := symRun { noAlias := true } ktL3 (pcOf 759) 100
sym_block btOK := symRun { noAlias := true } ktOK (pcOf 760) 100

/-- Mask of the zero test on the high word of a top node of height `h` (`1 ≤ h ≤ 11`). Campaign T51: `h = 11` tests
node bits 104..111 (high-word mask `0xFF << 40`). -/
def maskN (h : Nat) : Nat :=
  if h = 11 then (2 ^ 8 - 1) * 2 ^ 40 else (2 ^ topZeroBits h - 1) * 2 ^ (64 - topZeroBits h)

/-! ### Jumps -/
theorem kt230_spec (s : MachineState) (hpc : s.pc = pcOf 230) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 721 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bt230 codeAt_kt230 s hpc (by simp [bt230.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bt230.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bt230.res, rv_simp] <;> rfl
  · intro A _ _; simp [bt230.res, rv_simp]
theorem kt264_spec (s : MachineState) (hpc : s.pc = pcOf 264) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 727 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bt264 codeAt_kt264 s hpc (by simp [bt264.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bt264.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bt264.res, rv_simp] <;> rfl
  · intro A _ _; simp [bt264.res, rv_simp]
theorem kt274_spec (s : MachineState) (hpc : s.pc = pcOf 274) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 724 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bt274 codeAt_kt274 s hpc (by simp [bt274.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bt274.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bt274.res, rv_simp] <;> rfl
  · intro A _ _; simp [bt274.res, rv_simp]
theorem ktL3_spec (s : MachineState) (hpc : s.pc = pcOf 759) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 746 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btL3 codeAt_ktL3 s hpc (by simp [btL3.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [btL3.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [btL3.res, rv_simp] <;> rfl
  · intro A _ _; simp [btL3.res, rv_simp]
theorem fetch_kt758 (s : MachineState) (hpc : s.pc = pcOf 758) : fetch image s = some (.base .ECALL) :=
  (codeAt_kt758.fetch s hpc).trans rfl

/-! ### KINIT / KNEXT -/
theorem ktI_spec (s : MachineState) (hpc : s.pc = pcOf 721) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 231 ∧ t.getReg .x20 = BitVec.ofNat 64 1 ∧
      t.getReg .x13 = BitVec.ofNat 64 1 ∧ RegsExcept s t [.x13, .x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btI codeAt_ktI s hpc (by simp [btI.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [btI.res, Result.toState_pc, E.eval]
  · simp [btI.res, rv_simp]
  · simp [btI.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [btI.res, rv_simp] <;> rfl
  · intro A _ _; simp [btI.res, rv_simp]
theorem kt231_spec (s : MachineState) (hpc : s.pc = pcOf 231) (hh : Nat) (h1 : 1 ≤ hh) (h2 : hh ≤ 32)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) (h20 : s.getReg .x20 = BitVec.ofNat 64 1) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 233 ∧ t.getReg .x20 = BitVec.ofNat 64 (2 ^ (hh - 1)) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bt231 codeAt_kt231 s hpc (by simp [bt231.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [bt231.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, bt231.res, rv_simp, h15, h20]
    apply BitVec.eq_of_toNat_eq
    have e : (BitVec.ofNat 64 hh - 1#64).toNat = hh - 1 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    have e' : (BitVec.ofNat 64 hh + BitVec.ofNat 64 18446744073709551615).toNat = hh - 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    first
      | (rw [BitVec.toNat_shiftLeft, e', BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
          Nat.mod_eq_of_lt (show hh - 1 < 64 by omega)])
      | (rw [BitVec.toNat_shiftLeft, e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
          Nat.mod_eq_of_lt (show hh - 1 < 64 by omega)])
    have : 2 ^ (hh - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    simp only [Nat.one_mod, Nat.one_mul, Nat.mod_eq_of_lt this]
  · intro r hr; simp at hr; cases r <;> simp_all [bt231.res, rv_simp] <;> rfl
  · intro A _ _; simp [bt231.res, rv_simp]
theorem ktN_spec (s : MachineState) (hpc : s.pc = pcOf 724) (lo h : Nat) (hlo : lo < 2 ^ 64) (hh : h + 1 < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 233 ∧ t.getReg .x20 = BitVec.ofNat 64 (lo / 2) ∧
      t.getReg .x13 = BitVec.ofNat 64 (h + 1) ∧ RegsExcept s t [.x13, .x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btN codeAt_ktN s hpc (by simp [btN.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [btN.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, btN.res, rv_simp, h20]
    rw [ofNat_shr _ _ hlo]; rfl
  · simp only [Result.toState_getReg, btN.res, rv_simp, h13]
    rw [ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [btN.res, rv_simp] <;> rfl
  · intro A _ _; simp [btN.res, rv_simp]

/-! ### KCHK setup (727..745) -/
theorem kult (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
theorem ktC0_spec (s : MachineState) (hpc : s.pc = pcOf 727) (h : Nat) (hh : h < 2 ^ 64)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if h = 12 then pcOf 760 else pcOf 729) ∧ RegsExcept s t [.x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC0 codeAt_ktC0 s hpc (by simp [btC0.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, btC0.res, E.eval, CmpOp.eval, RegFile.get, h13]
    by_cases hc : h = 12
    · subst hc; simp
    · have : BitVec.ofNat 64 h ≠ BitVec.ofNat 64 12 := by rw [Ne, ofNat_inj hh (by norm_num)]; exact hc
      simp [hc, this]
  · intro r hr; simp at hr; cases r <;> simp_all [btC0.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC0.res, rv_simp]
/-- 729..731 (campaign T51): `a4 = h - 3`, `t3 = 3`, `blt a3, t3, 760` (heights 1, 2: no nonce search). -/
theorem ktC1_spec (s : MachineState) (hpc : s.pc = pcOf 729) (h : Nat) (hh : h < 2 ^ 63)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if h < 3 then pcOf 760 else pcOf 732) ∧
      (3 ≤ h → t.getReg .x14 = BitVec.ofNat 64 (h - 3)) ∧ RegsExcept s t [.x14, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC1 codeAt_ktC1 s hpc (by simp [btC1.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, btC1.res, E.eval, CmpOp.eval, RegFile.get, h13]
    rw [show (3#64 : Word) = BitVec.ofNat 64 3 from rfl, ofNat_slt h 3 hh (by norm_num)]
    by_cases hc : h < 3 <;> simp [hc]
  · intro h3
    simp only [Result.toState_getReg, btC1.res, rv_simp, h13]
    apply BitVec.eq_of_toNat_eq
    first
      | (rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega)
      | (rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega)
  · intro r hr; simp at hr; cases r <;> simp_all [btC1.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC1.res, rv_simp]
/-- 732 (campaign T51): `bne a4, zero, 736` (`h = 3` falls through to 733). -/
theorem ktC2_spec (s : MachineState) (hpc : s.pc = pcOf 732) (b : Nat) (hb : b < 2 ^ 64)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 b) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if b = 0 then pcOf 733 else pcOf 736) ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC2 codeAt_ktC2 s hpc (by simp [btC2.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, btC2.res, E.eval, CmpOp.eval, RegFile.get, h14]
    by_cases hc : b = 0
    · subst hc; simp
    · have : BitVec.ofNat 64 b ≠ 0#64 := by
        rw [Ne, show (0#64) = BitVec.ofNat 64 0 from rfl, ofNat_inj hb (by norm_num)]; exact hc
      simp [hc, this]
  · intro r hr; cases r <;> simp_all [btC2.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC2.res, rv_simp]
/-- 733..734 (campaign T51, `h = 3`): `a4 = 1`, `j 736`. -/
theorem ktC3_spec (s : MachineState) (hpc : s.pc = pcOf 733) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 736 ∧ t.getReg .x14 = BitVec.ofNat 64 1 ∧ RegsExcept s t [.x14] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC3 codeAt_ktC3 s hpc (by simp [btC3.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [btC3.res, Result.toState_pc, E.eval]
  · simp [btC3.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [btC3.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC3.res, rv_simp]
theorem ktC5_spec (s : MachineState) (hpc : s.pc = pcOf 736) (b h : Nat) (hb : 1 ≤ b) (hb' : b ≤ 11)
    (hh : h < 2 ^ 64) (h14 : s.getReg .x14 = BitVec.ofNat 64 b) (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = (if h = 11 then pcOf 742 else pcOf 744) ∧
      t.getReg .x16 = BitVec.ofNat 64 ((2 ^ b - 1) * 2 ^ (64 - b)) ∧
      RegsExcept s t [.x16, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC5 codeAt_ktC5 s hpc (by simp [btC5.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, btC5.res, E.eval, CmpOp.eval, RegFile.get, h13]
    by_cases hc : h = 11
    · subst hc; simp
    · have : BitVec.ofNat 64 h ≠ BitVec.ofNat 64 11 := by rw [Ne, ofNat_inj hh (by norm_num)]; exact hc
      simp [hc, this]
  · simp only [Result.toState_getReg, btC5.res, rv_simp, h14]
    interval_cases b <;> decide
  · intro r hr; simp at hr; cases r <;> simp_all [btC5.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC5.res, rv_simp]
theorem ktC6_spec (s : MachineState) (hpc : s.pc = pcOf 742) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 744 ∧ t.getReg .x16 = BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 40) ∧
      RegsExcept s t [.x16] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC6 codeAt_ktC6 s hpc (by simp [btC6.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [btC6.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, btC6.res, rv_simp]; decide
  · intro r hr; simp at hr; cases r <;> simp_all [btC6.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC6.res, rv_simp]
theorem ktC7_spec (s : MachineState) (hpc : s.pc = pcOf 744) (b : Nat) (hb' : b ≤ 11)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 b) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 746 ∧ t.getReg .x17 = BitVec.ofNat 64 (104 * 2 ^ b) ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC7 codeAt_ktC7 s hpc (by simp [btC7.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [btC7.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, btC7.res, rv_simp, h14]
    interval_cases b <;> decide
  · intro r hr; simp at hr; cases r <;> simp_all [btC7.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC7.res, rv_simp]

/-! ### Trial loop (746..759), KOK (760..769) and 272..273 -/
theorem nout_sub (p : Nat) (hp : p < 2) :
    BitVec.ofNat 64 NOUT - BitVec.ofNat 64 (p * 2 ^ 4) = BitVec.ofNat 64 (NOUT - 16 * p) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, NOUT]
  rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl <;> norm_num
theorem ktL0_spec (s : MachineState) (hpc : s.pc = pcOf 746) (p : Nat) (hp : p < 2)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 NOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 (p * 2 ^ 4)) :
    ∃ t, Steps image s 4 4 t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 (NOUT + 16 - 16 * p + 8)) &&& s.getReg .x16) = 0#64 then pcOf 760
        else pcOf 750) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  have e : s.getReg .x12 - s.getReg .x29 = BitVec.ofNat 64 (NOUT - 16 * p) := by rw [h12, h29, nout_sub p hp]
  have hobl : Oblig.all s btL0.res.st.obl := by
    simp only [btL0.res]
    t3n [e]
    simp only [NOUT] at *
    omega
  refine ⟨_, symRun_sound btL0 codeAt_ktL0 s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, btL0.res, E.eval, CmpOp.eval, RegFile.get]
    t3n [e]
    have ea : NOUT - 16 * p + 24 = NOUT + 16 - 16 * p + 8 := by simp only [NOUT]; omega
    rw [ea]
    split_ifs <;> simp_all
  · intro r hr; simp at hr; cases r <;> simp_all [btL0.res, rv_simp] <;> rfl
  · intro A _ _; simp [btL0.res, rv_simp]
theorem ktL1_spec (s : MachineState) (hpc : s.pc = pcOf 750) (n c : Nat) (hn : n + 1 < 2 ^ 64) (hc : c < 2 ^ 64)
    (hpad : s.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = (if c ≤ n + 1 then pcOf 760 else pcOf 754) ∧
      t.getReg .x28 = BitVec.ofNat 64 0x20000 ∧ t.getReg .x30 = BitVec.ofNat 64 (n + 1) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  have hobl : Oblig.all s btL1.res.st.obl := by
    simp only [btL1.res]
    t3n []
  have hm : memEval s btL1.res.st.mem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n := by
    simp only [btL1.res]; t3n [hpad]
  refine ⟨_, symRun_sound btL1 codeAt_ktL1 s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, btL1.res, E.eval, CmpOp.eval, RegFile.get, h17]
    t3n [hpad]
    rw [kult (n + 1) c hn hc]
    by_cases hcn : c ≤ n + 1
    · simp [hcn, show ¬ n + 1 < c by omega]
    · simp [hcn, show n + 1 < c by omega]
  · simp [btL1.res, rv_simp]
  · simp only [Result.toState_getReg, btL1.res]
    t3n [hpad]
  · intro r hr; simp at hr; cases r <;> simp_all [btL1.res, rv_simp] <;> rfl
  · intro A _ _; simp [btL1.res, rv_simp]
theorem ktL2_spec (s : MachineState) (hpc : s.pc = pcOf 754) (h28 : s.getReg .x28 = BitVec.ofNat 64 0x20000) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf 758 ∧ t.getMem (BitVec.ofNat 64 (NODE + 32)) = s.getReg .x30 ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      RegsExcept s t [.x10, .x11] ∧ Frame s t (fun X => X = NODE + 32) := by
  have hobl : Oblig.all s btL2.res.st.obl := by
    simp only [btL2.res]
    t3n [h28]
    try decide
  refine ⟨_, symRun_sound btL2 codeAt_ktL2 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [btL2.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, btL2.res, NODE]
    t3n [h28]
  · simp [btL2.res, rv_simp]
  · simp [btL2.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [btL2.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, btL2.res]
    t3n [h28]
    rw [if_neg (by omega)]
theorem ktOK_spec (s : MachineState) (hpc : s.pc = pcOf 760) (arena k p : Nat) (hp : p < 2)
    (ha8 : arena % 8 = 0) (hk : arena + 16 * k + 16 ≤ 2 ^ 24)
    (hdis : NOUT + 32 ≤ arena + 16 * k ∨ arena + 16 * k + 16 ≤ NODE + 32)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 (p * 2 ^ 4)) (h12 : s.getReg .x12 = BitVec.ofNat 64 NOUT) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 272 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k)) = s.getMem (BitVec.ofNat 64 (NOUT + 16 - 16 * p)) ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 16 - 16 * p + 8)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun X => X = NODE + 32 ∨ X = arena + 16 * k ∨ X = arena + 16 * k + 8) := by
  have e : s.getReg .x12 - s.getReg .x29 = BitVec.ofNat 64 (NOUT - 16 * p) := by rw [h12, h29, nout_sub p hp]
  have hobl : Oblig.all s btOK.res.st.obl := by
    simp only [btOK.res]
    t3n [h2, h24, e]
    simp only [NOUT, NODE] at *
    omega
  refine ⟨_, symRun_sound btOK codeAt_ktOK s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [btOK.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, btOK.res]
    t3n [h2, h24, e]
    simp only [NOUT, NODE] at hdis ⊢
    rw [if_neg (by omega), if_neg (by omega)]
  · simp only [Result.toState_getMem, btOK.res]
    t3n [h2, h24, e]
    simp only [NOUT, NODE] at hdis ⊢
    rw [if_neg (by omega), if_pos (by omega)]
    congr 2
    omega
  · simp only [Result.toState_getMem, btOK.res]
    t3n [h2, h24, e]
    simp only [NOUT, NODE] at hdis ⊢
    rw [if_pos (by omega)]
    congr 2
    omega
  · intro r hr; simp at hr; cases r <;> simp_all [btOK.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [Result.toState_getMem, btOK.res]
    t3n [h2, h24, e]
    simp only [NOUT, NODE] at hn ⊢
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem kt272_spec (s : MachineState) (hpc : s.pc = pcOf 272) (k : Nat)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 235 ∧ t.getReg .x24 = BitVec.ofNat 64 (k + 1) ∧
      RegsExcept s t [.x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bt272 codeAt_kt272 s hpc (by simp [bt272.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [bt272.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, bt272.res, rv_simp, h24]; rw [ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [bt272.res, rv_simp] <;> rfl
  · intro A _ _; simp [bt272.res, rv_simp]

/-! ## The zero test, the setup and the node input -/
theorem land_mask_eq_zero (n k w : Nat) :
    n &&& ((2 ^ w - 1) * 2 ^ k) = 0 ↔ n / 2 ^ k % 2 ^ w = 0 := by
  have hM : (2 ^ w - 1) * 2 ^ k = (2 ^ w - 1) <<< k := by rw [Nat.shiftLeft_eq]
  rw [hM]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    have := congrArg (fun y => Nat.testBit y (j + k)) h
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Nat.zero_testBit] at this
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit]
    by_cases hj : j < w
    · have e : j + k - k = j := by omega
      simp only [e, hj, decide_true, Bool.and_true, ge_iff_le, Nat.le_add_left] at this
      simp [hj, this]
    · simp [hj]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
    by_cases hik : k ≤ i
    · by_cases hiw : i - k < w
      · have := congrArg (fun y => Nat.testBit y (i - k)) h
        simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit, hiw, decide_true,
          Bool.true_and] at this
        rw [show i - k + k = i by omega] at this
        simp [this]
      · simp [hiw]
    · simp [hik]
theorem hiword_toNat (v : BitVec 128) : (v.extractLsb' 64 64).toNat = v.toNat / 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  apply Nat.mod_eq_of_lt
  omega
theorem zero_test_hi (v : BitVec 128) (b : Nat) (hb : b ≤ 64) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 ((2 ^ b - 1) * 2 ^ (64 - b)) = 0#64) ↔
      v.toNat / 2 ^ (128 - b) = 0 := by
  have hlt : (2 ^ b - 1) * 2 ^ (64 - b) < 2 ^ 64 := by
    have h1 : 2 ^ b - 1 < 2 ^ b := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
    calc (2 ^ b - 1) * 2 ^ (64 - b) < 2 ^ b * 2 ^ (64 - b) :=
          Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, hiword_toNat,
    BitVec.toNat_zero, land_mask_eq_zero, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show 64 + (64 - b) = 128 - b by omega]
  have hv : v.toNat / 2 ^ (128 - b) < 2 ^ b := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show b + (128 - b) = 128 by omega]
    exact v.isLt
  rw [Nat.mod_eq_of_lt hv]
/-- Campaign T51: the `h = 11` zero test, high-word mask `0xFF << 40` = node bits 104..111. -/
theorem zero_test_bits104 (v : BitVec 128) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 40) = 0#64) ↔
      v.toNat / 2 ^ 104 % 2 ^ 8 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), hiword_toNat,
    BitVec.toNat_zero, land_mask_eq_zero, Nat.div_div_eq_div_mul, ← Nat.pow_add]
/-- Campaign T51: `b_h = 0,0,1,1,2,3,4,5,6,7,8` (#938: `b_h = h`). -/
theorem topZeroBits_eq (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) : topZeroBits h = SigGolfCandidate.T3.topZeroAlloc.getD h 0 := rfl
theorem topZeroBits_ge3 (h : Nat) (h3 : 3 ≤ h) (h11 : h ≤ 11) : topZeroBits h = if h = 3 then 1 else h - 3 := by
  interval_cases h <;> rfl
theorem ktopZeroBits_le (h : Nat) : topZeroBits h ≤ 8 := by
  unfold topZeroBits T3.topZeroAlloc
  rcases h with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | h <;> simp
/-- The machine's zero test (KCHK 746..749) is `topZeroOk`. -/
theorem zero_test (v : Digest) (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 (maskN h) = 0#64) ↔ topZeroOk h v = true := by
  unfold maskN topZeroOk
  by_cases hc : h = 11
  · rw [if_pos hc, if_pos hc, zero_test_bits104, beq_iff_eq]
  · rw [if_neg hc, if_neg hc, zero_test_hi v _ (by have := ktopZeroBits_le h; omega), beq_iff_eq]
/-- Steps (= cycles) of the KCHK setup 727..745 at height `h ∈ 3..11` (campaign T51: `b = h - 3`, `h = 3` sets
`b = 1` at 733..734). -/
def setupK (h : Nat) : Nat :=
  14 + (if h = 3 then 2 else 0) + (if h = 11 then 2 else 0)
theorem setupK_le (h : Nat) : setupK h ≤ 18 := by unfold setupK; split_ifs <;> omega
theorem ksetup_spec (s : MachineState) (hpc : s.pc = pcOf 727) (h : Nat) (h3 : 3 ≤ h) (h11 : h ≤ 11)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s (setupK h) (setupK h) t ∧ t.pc = pcOf 746 ∧
      t.getReg .x16 = BitVec.ofNat 64 (maskN h) ∧ t.getReg .x17 = BitVec.ofNat 64 (topNonceCap h) ∧
      RegsExcept s t [.x14, .x16, .x17, .x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, st1, p1, r1, f1⟩ := ktC0_spec s hpc h (by omega) h13
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, st2, p2, x14_2, r2, f2⟩ := ktC1_spec t1 p1 h (by omega) (by rw [r1.get (by simp)]; exact h13)
  rw [if_neg (by omega)] at p2
  obtain ⟨t3, st3, p3, r3, f3⟩ := ktC2_spec t2 p2 (h - 3) (by omega) (x14_2 h3)
  have hb := topZeroBits_ge3 h h3 h11
  obtain ⟨t4, st4, p4, x14_4, r4, f4⟩ : ∃ t4, Steps image t3 (if h = 3 then 2 else 0) (if h = 3 then 2 else 0) t4 ∧
      t4.pc = pcOf 736 ∧ t4.getReg .x14 = BitVec.ofNat 64 (topZeroBits h) ∧ RegsExcept t3 t4 [.x14] ∧
      Frame t3 t4 (fun _ => False) := by
    by_cases hc : h = 3
    · rw [if_pos (show h - 3 = 0 by omega)] at p3
      obtain ⟨u, su, pu, xu, ru, fu⟩ := ktC3_spec t3 p3
      exact ⟨u, by rw [if_pos hc]; exact su, pu, by rw [xu, hb, if_pos hc], ru, fu⟩
    · rw [if_neg (show h - 3 ≠ 0 by omega)] at p3
      refine ⟨t3, by rw [if_neg hc]; exact Steps.refl _, p3, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
      rw [r3.get (by simp), x14_2 h3, hb, if_neg hc]
  have r14 : RegsExcept s t4 ([.x28] ++ [.x14, .x28] ++ [] ++ [.x14]) := ((r1.trans r2).trans r3).trans r4
  have hb1 : 1 ≤ topZeroBits h := by rw [hb]; split_ifs <;> omega
  have hb8 : topZeroBits h ≤ 11 := by have := ktopZeroBits_le h; omega
  obtain ⟨t6, st6, p6, x16_6, r6, f6⟩ := ktC5_spec t4 p4 (topZeroBits h) h hb1 hb8 (by omega)
    x14_4 (by rw [r14.get (by simp)]; exact h13)
  obtain ⟨t7, st7, p7, x16_7, r7, f7⟩ : ∃ t7, Steps image t6 (if h = 11 then 2 else 0) (if h = 11 then 2 else 0) t7 ∧
      t7.pc = pcOf 744 ∧ t7.getReg .x16 = BitVec.ofNat 64 (maskN h) ∧ RegsExcept t6 t7 [.x16] ∧
      Frame t6 t7 (fun _ => False) := by
    by_cases hc : h = 11
    · rw [if_pos hc] at p6
      obtain ⟨u, su, pu, xu, ru, fu⟩ := ktC6_spec t6 p6
      exact ⟨u, by rw [if_pos hc]; exact su, pu, by rw [xu]; unfold maskN; rw [if_pos hc], ru, fu⟩
    · rw [if_neg hc] at p6
      refine ⟨t6, by rw [if_neg hc]; exact Steps.refl _, p6, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
      rw [x16_6]; unfold maskN; rw [if_neg hc]
  obtain ⟨t8, st8, p8, x17_8, r8, f8⟩ := ktC7_spec t7 p7 (topZeroBits h) hb8
    (by rw [r7.get (by simp), r6.get (by simp)]; exact x14_4)
  refine ⟨t8, Steps.of_eq (st1.trans (st2.trans (st3.trans (st4.trans (st6.trans (st7.trans st8))))))
    ?_ ?_, p8, by rw [r8.get (by simp)]; exact x16_7, by rw [x17_8]; rfl, ?_, ?_⟩
  · unfold setupK; split_ifs <;> omega
  · unfold setupK; split_ifs <;> omega
  · exact (((r14.trans r6).trans r7).trans r8).mono (by simp)
  · exact ((((((f1.trans f2).trans f3).trans f4).trans f6).trans f7).trans f8).mono
      (fun _ _ h => by simp_all)

theorem nonce_words (n : Nat) (hn : n < 2 ^ 64) : wordsOf (nonceBytes n) = [BitVec.ofNat 64 n, 0] := by
  unfold nonceBytes
  rw [wordsOf_bytesLE16]
  congr 1
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    have h0 : n % 2 ^ 64 % 2 ^ 128 / 2 ^ 64 = 0 := by omega
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h0, Nat.zero_mod]
    rfl
theorem topNodeInput_length (heap n : Nat) (l r : Digest) : (topNodeInput heap n l r).length = 64 := by
  simp [topNodeInput, nonceBytes, bytesLE_length]
theorem wordsOf_topNodeInput (heap n : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) (hn : n < 2 ^ 64) (l r : Digest) :
    wordsOf (topNodeInput heap n l r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 heap, 0, BitVec.ofNat 64 n, 0,
        r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  unfold topNodeInput
  rw [wordsOf_append _ _ (by simp [bytesLE_length, nonceBytes]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, nonce_words n hn,
    wordsOf_bytesLE16, nodeTweak_3_top 0 heap h1 h2, T3.append64_low]
  have hhi : (0#64 ++ BitVec.ofNat 64 (nodeLo 0 0 + heap)).extractLsb' 64 64 = 0#64 :=
    BitVec.extractLsb'_append_eq_left
  rw [hhi]
  simp [nodeLo]
theorem topNodeInput_blocks (heap n : Nat) (l r : Digest) :
    (toQ (pad64 (topNodeInput heap n l r))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [topNodeInput_length]),
    blocks_toQ ⟨by rw [topNodeInput_length]; omega, by rw [topNodeInput_length]⟩, topNodeInput_length]
/-- The 64-byte node block at `NODE` with pad `n` is the trial-`n` input. -/
theorem hashInput_topNode (t : MachineState) (heap n : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) (hn : n < 2 ^ 64)
    (l r : Digest) (h10 : t.getReg .x10 = BitVec.ofNat 64 NODE) (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (w0 : t.getMem (BitVec.ofNat 64 NODE) = l.extractLsb' 0 64)
    (w8 : t.getMem (BitVec.ofNat 64 (NODE + 8)) = l.extractLsb' 64 64)
    (w16 : t.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 heap)
    (w24 : t.getMem (BitVec.ofNat 64 (NODE + 24)) = 0)
    (w32 : t.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n)
    (w40 : t.getMem (BitVec.ofNat 64 (NODE + 40)) = 0)
    (w48 : t.getMem (BitVec.ofNat 64 (NODE + 48)) = r.extractLsb' 0 64)
    (w56 : t.getMem (BitVec.ofNat 64 (NODE + 56)) = r.extractLsb' 64 64) :
    hashInput t = toQ (pad64 (topNodeInput heap n l r)) := by
  rw [pad64_of_aligned _ (by rw [topNodeInput_length])]
  refine hashInput_toQ t _ 0 NODE (topNodeInput_length _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
  rw [wordsOf_topNodeInput heap n h1 h2 hn, readWords_eight, w0, w8, w16, w24, w32, w40, w48, w56]
theorem out_after_hash (t : MachineState) (a : BitVec 256) (heap : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 NOUT) :
    DigAt (writeHash t a) (NOUT + 16 - 16 * (heap % 2)) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by
  rw [T3.nodeHalfHigh_top]
  rcases Nat.mod_two_eq_zero_or_one heap with hp | hp
  · have hd : decide (heap % 2 = 0) = true := by simp [hp]
    rw [hd, T3.projHalf_true, hp, show NOUT + 16 - 16 * 0 = NOUT + 16 from rfl]
    exact DigAt.writeHash_hi t a NOUT h12 (by decide)
  · have hd : decide (heap % 2 = 0) = false := by simp [hp]
    rw [hd, T3.projHalf_false, hp, show NOUT + 16 - 16 * 1 = NOUT from rfl]
    exact DigAt.writeHash_lo t a NOUT h12 (by decide)

/-! ## The trial loop -/
/-- What follows the trial-`n` hash in `topNonceSearch` (fuel = trials left). -/
def trialTail (h heap : Nat) (l r : Digest) : Nat → Nat → Digest → T3.M (Nat × Digest)
  | 0, n, v => pure (n, v)
  | fuel + 1, n, v => if topZeroOk h v then pure (n, v) else topNonceSearch h heap l r fuel (n + 1)
theorem topNonceSearch_eq (h heap : Nat) (l r : Digest) (fuel n : Nat) :
    topNonceSearch h heap l r fuel n = topNodeHashN heap n l r >>= trialTail h heap l r fuel n := by
  cases fuel <;> rfl
theorem topNodeHashN_bind {β : Type} (heap n : Nat) (l r : Digest) (g : Digest → T3.M β) :
    topNodeHashN heap n l r >>= g =
      T3.publicHash (topNodeInput heap n l r) >>= fun a => g (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by
  unfold topNodeHashN T3.projHash; rw [bind_assoc]; simp only [pure_bind]
theorem topNonceCap_le (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) : 1 ≤ topNonceCap h ∧ topNonceCap h ≤ 104 * 2048 := by
  interval_cases h <;> decide

/-- The state right before the first node hash (263): arguments, node words and the store slot. -/
structure T2Facts (t2 : MachineState) (arena heap : Nat) (l r : Digest) : Prop where
  x2 : t2.getReg .x2 = BitVec.ofNat 64 arena
  x5 : t2.getReg .x5 = 0
  x12 : t2.getReg .x12 = BitVec.ofNat 64 NOUT
  x24 : t2.getReg .x24 = BitVec.ofNat 64 heap
  x29 : t2.getReg .x29 = BitVec.ofNat 64 (heap % 2 * 2 ^ 4)
  w0 : t2.getMem (BitVec.ofNat 64 NODE) = l.extractLsb' 0 64
  w8 : t2.getMem (BitVec.ofNat 64 (NODE + 8)) = l.extractLsb' 64 64
  w16 : t2.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 heap
  w24 : t2.getMem (BitVec.ofNat 64 (NODE + 24)) = 0
  w40 : t2.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  w48 : t2.getMem (BitVec.ofNat 64 (NODE + 48)) = r.extractLsb' 0 64
  w56 : t2.getMem (BitVec.ofNat 64 (NODE + 56)) = r.extractLsb' 64 64
  h1 : 1 ≤ heap
  h2 : heap < 4096
  ha8 : arena % 8 = 0
  hk : arena + 16 * heap + 16 ≤ 2 ^ 24
  hdis : NOUT + 32 ≤ arena + 16 * heap ∨ arena + 16 * heap + 16 ≤ NODE + 32

def trialRegs : List Reg := [.x10, .x11, .x14, .x16, .x17, .x28, .x30]
def TrialW (X : Nat) : Prop := X = NODE + 32 ∨ (NOUT ≤ X ∧ X < NOUT + 32)

/-- At 746 after the trial-`n` hash (answer `a`). -/
structure TrialSt (t2 : MachineState) (h heap n : Nat) (a : BitVec 256) (u : MachineState) : Prop where
  pc : u.pc = pcOf 746
  regs : RegsExcept t2 u trialRegs
  x16 : u.getReg .x16 = BitVec.ofNat 64 (maskN h)
  x17 : u.getReg .x17 = BitVec.ofNat 64 (topNonceCap h)
  pad : u.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n
  frame : Frame t2 u TrialW
  out : DigAt u (NOUT + 16 - 16 * (heap % 2)) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)

def kokRegs : List Reg := [.x6, .x7, .x10, .x11, .x14, .x16, .x17, .x24, .x28, .x29, .x30]
def KokW (arena heap : Nat) (X : Nat) : Prop := TrialW X ∨ X = arena + 16 * heap ∨ X = arena + 16 * heap + 8

/-- After KOK and 272..273: back at 235 with the node stored and the pad cleared. -/
structure KokPost (t2 : MachineState) (arena heap : Nat) (v : Digest) (w : MachineState) : Prop where
  pc : w.pc = pcOf 235
  x24 : w.getReg .x24 = BitVec.ofNat 64 (heap + 1)
  pad : w.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  dig : DigAt w (arena + 16 * heap) v
  regs : RegsExcept t2 w kokRegs
  frame : Frame t2 w (KokW arena heap)

theorem kok_run {t2 u : MachineState} {arena heap : Nat} {l r : Digest} (F : T2Facts t2 arena heap l r)
    (hpc : u.pc = pcOf 760) {L : List Reg} (hL : ∀ x ∈ L, x ∈ trialRegs) (hr : RegsExcept t2 u L)
    (hf : Frame t2 u TrialW) {v : Digest} (hv : DigAt u (NOUT + 16 - 16 * (heap % 2)) v) :
    ∃ w, Steps image u 12 12 w ∧ KokPost t2 arena heap v w := by
  have g : ∀ x, x ∉ trialRegs → u.getReg x = t2.getReg x := fun x hx => hr.get (fun hm => hx (hL x hm))
  obtain ⟨u1, s1, p1, m32, ma, mb, r1, f1⟩ := ktOK_spec u hpc arena heap (heap % 2) (Nat.mod_lt _ (by decide))
    F.ha8 F.hk F.hdis (by rw [g _ (by simp [trialRegs])]; exact F.x2) (by rw [g _ (by simp [trialRegs])]; exact F.x24)
    (by rw [g _ (by simp [trialRegs])]; exact F.x29) (by rw [g _ (by simp [trialRegs])]; exact F.x12)
  obtain ⟨w, s2, p2, x24w, r2, f2⟩ := kt272_spec u1 p1 heap
    (by rw [r1.get (by simp), g _ (by simp [trialRegs])]; exact F.x24)
  have hk := F.hk
  refine ⟨w, s1.trans s2, ⟨p2, x24w, ?_, ?_, ?_, ?_⟩⟩
  · rw [f2.get (by decide) (fun h => h), m32]
  · exact ⟨by rw [f2.get (by omega) (fun h => h), ma, hv.1], by rw [f2.get (by omega) (fun h => h), mb, hv.2]⟩
  · refine ((hr.trans r1).trans r2).mono (fun x hx => ?_)
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact (by decide : ∀ y ∈ trialRegs, y ∈ kokRegs) x (hL x hx)
    · exact (by decide : ∀ y ∈ [Reg.x6, .x7, .x28, .x29], y ∈ kokRegs) x hx
    · exact (by decide : ∀ y ∈ [Reg.x24], y ∈ kokRegs) x hx
  · exact ((hf.trans f1).trans f2).mono (fun X _ h => by
      unfold KokW
      rcases h with (h | h | h | h) | h
      · exact Or.inl h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact h.elim)

section loop
variable (sk : BitVec 256) {t2 : MachineState} {arena heap : Nat} {l r : Digest} (F : T2Facts t2 arena heap l r)
  (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11)
include F h1 h11

theorem trial_check {n : Nat} {a : BitVec 256} {u : MachineState} (hu : TrialSt t2 h heap n a u) :
    ∃ u1, Steps image u 4 4 u1 ∧
      u1.pc = (if topZeroOk h (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true then pcOf 760 else pcOf 750) ∧
      RegsExcept u u1 [.x30] ∧ Frame u u1 (fun _ => False) := by
  obtain ⟨u1, s1, p1, r1, f1⟩ := ktL0_spec u hu.pc (heap % 2) (Nat.mod_lt _ (by decide))
    (by rw [hu.regs.get (by simp [trialRegs]), F.x12]) (by rw [hu.regs.get (by simp [trialRegs]), F.x29])
  refine ⟨u1, s1, ?_, r1, f1⟩
  rw [p1, hu.x16, hu.out.2]
  by_cases hz : topZeroOk h (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true
  · rw [if_pos ((zero_test _ h h1 h11).mpr hz), if_pos hz]
  · rw [if_neg (fun hc => hz ((zero_test _ h h1 h11).mp hc)), if_neg hz]

theorem trial_pad {n : Nat} {a : BitVec 256} {u u1 : MachineState} (hu : TrialSt t2 h heap n a u)
    (hn : n < topNonceCap h) (r1 : RegsExcept u u1 [.x30]) (f1 : Frame u u1 (fun _ => False))
    (p1 : u1.pc = pcOf 750) :
    ∃ u2, Steps image u1 4 4 u2 ∧ u2.pc = (if topNonceCap h ≤ n + 1 then pcOf 760 else pcOf 754) ∧
      u2.getReg .x28 = BitVec.ofNat 64 0x20000 ∧ u2.getReg .x30 = BitVec.ofNat 64 (n + 1) ∧
      RegsExcept u1 u2 [.x28, .x30] ∧ Frame u1 u2 (fun _ => False) := by
  have hc := topNonceCap_le h h1 h11
  exact ktL1_spec u1 p1 n (topNonceCap h) (by omega) (by omega)
    (by rw [f1.get (by decide) (fun h => h), hu.pad]) (by rw [r1.get (by simp), hu.x17])

theorem trial_loop : ∀ fuel n (a : BitVec 256) u, TrialSt t2 h heap n a u → n + fuel + 1 = topNonceCap h →
    TBSim image sk u (21 * fuel + 20)
      (trialTail h heap l r fuel n (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a))
      (fun res w => KokPost t2 arena heap res.2 w) := by
  have hcap := topNonceCap_le h h1 h11
  intro fuel
  induction fuel with
  | zero =>
    intro n a u hu hn
    obtain ⟨u1, s1, p1, r1, f1⟩ := trial_check F h h1 h11 hu
    by_cases hz : topZeroOk h (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true
    · rw [if_pos hz] at p1
      obtain ⟨w, sw, hw⟩ := kok_run F p1 (L := trialRegs ++ [.x30]) (by simp [trialRegs]) (hu.regs.trans r1)
        ((hu.frame.trans f1).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
        (hu.out.frame f1 (by simp only [NOUT]; omega) (fun h => h) (fun h => h))
      exact (TBSim.pure_steps (sk := sk) (Q := fun res w => KokPost t2 arena heap res.2 w)
        (a := (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)) (s1.trans sw) hw).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at p1
      obtain ⟨u2, s2, p2, -, -, r2, f2⟩ := trial_pad F h h1 h11 hu (by omega) r1 f1 p1
      rw [if_pos (by omega)] at p2
      have f12 : Frame u u2 (fun _ => False) := (f1.trans f2).mono (fun X _ h => by simp_all)
      obtain ⟨w, sw, hw⟩ := kok_run F p2 (L := trialRegs ++ [.x30] ++ [.x28, .x30]) (by simp [trialRegs])
        ((hu.regs.trans r1).trans r2)
        ((hu.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
        (hu.out.frame f12 (by simp only [NOUT]; omega) (fun h => h) (fun h => h))
      exact (TBSim.pure_steps (sk := sk) (Q := fun res w => KokPost t2 arena heap res.2 w)
        (a := (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)) (s1.trans (s2.trans sw)) hw).mono (by omega)
        (fun _ _ h => h)
  | succ fuel ih =>
    intro n a u hu hn
    obtain ⟨u1, s1, p1, r1, f1⟩ := trial_check F h h1 h11 hu
    by_cases hz : topZeroOk h (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true
    · rw [if_pos hz] at p1
      obtain ⟨w, sw, hw⟩ := kok_run F p1 (L := trialRegs ++ [.x30]) (by simp [trialRegs]) (hu.regs.trans r1)
        ((hu.frame.trans f1).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
        (hu.out.frame f1 (by simp only [NOUT]; omega) (fun h => h) (fun h => h))
      have e : trialTail h heap l r (fuel + 1) n (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) =
          pure (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by simp only [trialTail, hz, if_true]
      rw [e]
      exact (TBSim.pure_steps (sk := sk) (Q := fun res w => KokPost t2 arena heap res.2 w)
        (a := (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)) (s1.trans sw) hw).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at p1
      obtain ⟨u2, s2, p2, x28_2, x30_2, r2, f2⟩ := trial_pad F h h1 h11 hu (by omega) r1 f1 p1
      rw [if_neg (by omega)] at p2
      obtain ⟨u3, s3, p3, m32_3, x10_3, x11_3, r3, f3⟩ := ktL2_spec u2 p2 x28_2
      have r03 : RegsExcept t2 u3 (trialRegs ++ [.x30] ++ [.x28, .x30] ++ [.x10, .x11]) :=
        ((hu.regs.trans r1).trans r2).trans r3
      have g3 : ∀ x, x ∉ trialRegs → u3.getReg x = t2.getReg x := fun x hx => r03.get (fun hm => hx
        ((by decide : ∀ y ∈ trialRegs ++ [Reg.x30] ++ [.x28, .x30] ++ [.x10, .x11], y ∈ trialRegs) x hm))
      have f03 : Frame t2 u3 TrialW := (((hu.frame.trans f1).trans f2).trans f3).mono (fun X _ h => by
        rcases h with ((h | h) | h) | h
        · exact h
        · exact h.elim
        · exact h.elim
        · exact Or.inl h)
      have fr : ∀ X, X < 2 ^ 64 → ¬ TrialW X → u3.getMem (BitVec.ofNat 64 X) = t2.getMem (BitVec.ofNat 64 X) :=
        fun X hX hn => f03.get hX hn
      have nW : ∀ X, X < NODE + 32 ∨ (NODE + 32 < X ∧ X < NOUT) → ¬ TrialW X := by
        intro X hX hw; unfold TrialW at hw; simp only [NODE, NOUT] at hX hw; omega
      have x12_3 : u3.getReg .x12 = BitVec.ofNat 64 NOUT := by rw [g3 _ (by simp [trialRegs]), F.x12]
      have hq : hashInput u3 = toQ (pad64 (topNodeInput heap (n + 1) l r)) :=
        hashInput_topNode u3 heap (n + 1) F.h1 F.h2 (by omega) l r x10_3 x11_3
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w0])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w8])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w16])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w24])
          (by rw [m32_3, x30_2])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE, NOUT]; omega)), F.w40])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE, NOUT]; omega)), F.w48])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE, NOUT]; omega)), F.w56])
      have hv : hashArgumentsValid u3 = true :=
        hashArgs_const u3 NODE 64 NOUT x10_3 x11_3 x12_3 (by decide) (by decide) (by decide) (by decide) (by decide)
      have h5 : u3.getReg .x5 = 0 := by rw [g3 _ (by simp [trialRegs]), F.x5]
      have e : trialTail h heap l r (fuel + 1) n (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) =
          T3.publicHash (topNodeInput heap (n + 1) l r) >>= fun a' =>
            trialTail h heap l r fuel (n + 1) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a') := by
        rw [trialTail.eq_2, if_neg hz, topNonceSearch_eq, topNodeHashN_bind]
      rw [e]
      refine (TBSim.steps (s1.trans (s2.trans s3)) (TBSim.publicHash_bind (fetch_kt758 u3 p3) h5 hv hq
        (W := 1 + (21 * fuel + 20)) (fun a' => ?_))).mono (by rw [topNodeInput_blocks]; omega) (fun _ _ h => h)
      have hwf := Frame.writeHash u3 a' NOUT x12_3 (by decide)
      obtain ⟨w, s4, p4, r4, f4⟩ := ktL3_spec (writeHash u3 a') (by rw [pc_writeHash, p3, pcOf_add4])
      refine TBSim.steps s4 (ih (n + 1) a' w ⟨p4, ?_, ?_, ?_, ?_, ?_, ?_⟩ (by omega))
      · have hw0 : RegsExcept u3 (writeHash u3 a') [] := fun r _ => getReg_writeHash u3 a' r
        exact ((r03.trans hw0).trans r4).mono (by decide)
      · rw [r4.get (by simp), getReg_writeHash, r3.get (by simp), r2.get (by simp), r1.get (by simp), hu.x16]
      · rw [r4.get (by simp), getReg_writeHash, r3.get (by simp), r2.get (by simp), r1.get (by simp), hu.x17]
      · rw [f4.get (by decide) (fun h => h), hwf.get (by decide) (by simp only [NODE, NOUT]; omega), m32_3, x30_2]
      · exact ((f03.trans hwf).trans f4).mono (fun X _ h => by
          rcases h with (h | h) | h
          · exact h
          · exact Or.inr h
          · exact h.elim)
      · exact (out_after_hash u3 a' heap x12_3).frame f4 (by simp only [NOUT]; omega) (fun h => h) (fun h => h)
end loop

/-! ## Nodes -/
/-- Registers the top-tree routine may change (the lower-tree `levRegs` plus KCHK's `a3 a4 a6 a7`). -/
def topLevRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x13, .x14, .x16, .x17, .x20, .x24, .x28, .x29, .x30]

structure TNodeInv (s0 : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest))
    (pre : List Digest) (t : MachineState) : Prop where
  x13 : t.getReg .x13 = BitVec.ofNat 64 (ℓ + 1)
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (B.h - ℓ - 1))
  x24 : t.getReg .x24 = BitVec.ofNat 64 (2 ^ (B.h - ℓ - 1) + pre.length)
  regs : RegsExcept s0 t topLevRegs
  frame : Frame s0 t (LevW B)
  heap : HeapAt t B ℓ levels
  cur : DigsAt t (B.arena + 16 * 2 ^ (B.h - ℓ - 1)) pre

structure TLevInv (s0 : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest))
    (t : MachineState) : Prop where
  x13 : t.getReg .x13 = BitVec.ofNat 64 (ℓ + 1)
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ B.h / 2 ^ (ℓ + 1))
  regs : RegsExcept s0 t topLevRegs
  frame : Frame s0 t (LevW B)
  heap : HeapAt t B ℓ levels

/-- The node computation of `buildTopLevel level` at index `i`. -/
def topNodeProg (level heap : Nat) (l r : Digest) : T3.M Digest :=
  if level = 12 then nodeHash 3 0 0 heap l r else Prod.snd <$> topNodeAt level heap l r

/-- Cycle bound of one node at height `h` (`h = 12`: the root, no nonce). -/
def nodeW (h : Nat) : Nat := if h = 12 then 51 else 75 + 21 * (topNonceCap h - 1)

theorem nonceBytes_zero : nonceBytes 0 = zero16 := by decide
theorem nodeHash_top (heap : Nat) (l r : Digest) :
    nodeHash 3 0 0 heap l r = T3.publicHash (topNodeInput heap 0 l r) >>= fun a =>
      pure (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by
  unfold nodeHash T3.projHash topNodeInput
  rw [nonceBytes_zero]
/-- Campaign T51: a height with `b_h = 0` (heights 1, 2) keeps its first trial (nonce 0): the node is the plain node
hash. -/
theorem topNodeAt_b0 (h heap : Nat) (l r : Digest) (hb : topZeroBits h = 0) :
    Prod.snd <$> topNodeAt h heap l r = nodeHash 3 0 0 heap l r := by
  have h11 : h ≠ 11 := by intro e; subst e; simp [topZeroBits, T3.topZeroAlloc] at hb
  have hcap : topNonceCap h - 1 = 102 + 1 := by unfold topNonceCap; simp [hb]
  unfold topNodeAt
  rw [hcap, topNonceSearch_eq, topNodeHashN_bind, nodeHash_top, map_bind]
  congr 1; funext a
  have hz : topZeroOk h (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true := by
    unfold topZeroOk
    rw [if_neg h11, hb, Nat.sub_zero, Nat.div_eq_of_lt (BitVec.isLt _)]
    rfl
  simp only [trialTail, hz, if_true, map_pure]

section node
variable {image' : Image} (sk : BitVec 256) {s0 : MachineState} {B : LevArgs} {leaves : List Digest}
  (hpre : LevPre s0 B leaves) (htop : B.lay = 0 ∧ B.tree = 0) (hh12 : B.h = 12)
include hpre htop hh12

/-- From 235 to the first node hash (263): the node block is in place with a zero pad. -/
theorem node_prefix {ℓ : Nat} (hl : ℓ < 12) {levels : List (List Digest)} {pre : List Digest}
    (hi : pre.length < 2 ^ (12 - ℓ - 1)) {t : MachineState} (ht : TNodeInv s0 B ℓ levels pre t)
    (hpc : t.pc = pcOf 235) :
    ∃ t2, Steps image t 28 28 t2 ∧ t2.pc = pcOf 263 ∧
      t2.getReg .x10 = BitVec.ofNat 64 NODE ∧ t2.getReg .x11 = BitVec.ofNat 64 64 ∧
      t2.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 ∧
      T2Facts t2 B.arena (2 ^ (12 - ℓ - 1) + pre.length) ((levels.getD ℓ []).getD (2 * pre.length) 0)
        ((levels.getD ℓ []).getD (2 * pre.length + 1) 0) ∧
      RegsExcept t t2 [.x6, .x6, .x7, .x28, .x29, .x30, .x10, .x11, .x12, .x29] ∧
      Frame t t2 (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56) := by
  have ha := hpre.ha
  have has := hpre.has
  have ha8 := hpre.ha8
  rw [hh12] at ha has
  set lo := 2 ^ (12 - ℓ - 1) with hlo_def
  set i := pre.length with hi_def
  have hY : 2 ^ (12 - ℓ) = 2 * lo := two_pow_split hl
  have hYZ : 2 ^ (12 - ℓ) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have g : ∀ r, r ∉ topLevRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r2 : t.getReg .x2 = BitVec.ofNat 64 B.arena := by rw [g _ (by simp [topLevRegs]), hpre.x2]
  have r9 : t.getReg .x9 = BitVec.ofNat 64 B.tree := by rw [g _ (by simp [topLevRegs]), hpre.x9]
  have r5 : t.getReg .x5 = 0 := by rw [g _ (by simp [topLevRegs]), hpre.x5]
  have r21 : t.getReg .x21 = BitVec.ofNat 64 (nodeLo B.lay B.tree) := by
    rw [g _ (by simp [topLevRegs]), hpre.x21]
  have x20 : t.getReg .x20 = BitVec.ofNat 64 lo := by rw [ht.x20, hh12]
  have x24 : t.getReg .x24 = BitVec.ofNat 64 (lo + i) := by rw [ht.x24, hh12]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub118_spec subAt_keygen t hpc lo (lo + i) (by omega) (by omega) x20 x24
  rw [if_pos (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x10, t2x11, t2x12, t2x29, t2n0, t2n8, t2n16, t2n24, t2n48, t2n56, t2r, t2f⟩ :=
    sub120_full subAt_keygen t1 t1pc B.arena (lo + i) B.tree (nodeLo B.lay B.tree) ha8 (by omega) hpre.htree
      (by simp only [NODE, NOUT] at has ⊢; omega) (by rw [t1r.get (by simp)]; exact r2)
      (by rw [t1r.get (by simp)]; exact x24) (by rw [t1r.get (by simp)]; exact r9)
      (by rw [t1r.get (by simp)]; exact r21)
  obtain ⟨hlen, hlev⟩ := ht.heap
  obtain ⟨hll, hlv⟩ := hlev ℓ le_rfl
  rw [hh12] at hll hlv
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
      ht.frame.get hX' (by unfold LevW; rw [hh12]; simp only [NODE, NOUT] at hX has ⊢; omega)]
  have e16 : t2.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 (lo + i) := by
    rw [t2n16, t1r.get (by simp), r21, htop.1, htop.2]
    simp only [nodeLo, if_true, BitVec.ofNat_eq_ofNat, BitVec.zero_shiftLeft, BitVec.or_zero]
    rw [BitVec.zero_add]
  have hfr : ∀ r, r ∉ [Reg.x6] → r ∉ [Reg.x6, .x7, .x28, .x29, .x30, .x10, .x11, .x12, .x29] →
      t2.getReg r = t.getReg r := fun r h1 h2 => by rw [t2r.get h2, t1r.get h1]
  refine ⟨t2, (st1.trans st2).of_eq (by omega) (by omega), t2pc, t2x10, t2x11, by rw [fr _ (by simp), hpre.z32],
    ⟨by rw [hfr _ (by simp) (by simp)]; exact r2, by rw [hfr _ (by simp) (by simp)]; exact r5, t2x12,
      by rw [hfr _ (by simp) (by simp)]; exact x24, t2x29,
      by rw [t2n0, hL1.1], by rw [t2n8, hL1.2], e16, t2n24, by rw [fr _ (by simp), hpre.z40],
      by rw [t2n48, hR1.1], by rw [t2n56, hR1.2], by omega, by omega, ha8, by omega, by simp only [NODE, NOUT] at has ⊢; omega⟩,
    t1r.trans t2r, (t1f.trans t2f).mono (fun X _ hX => by rcases hX with hX | hX; exact hX.elim; exact hX)⟩
theorem node_post {ℓ : Nat} (hl : ℓ < 12) {levels : List (List Digest)} {pre : List Digest}
    (hi : pre.length < 2 ^ (12 - ℓ - 1)) {t t2 w : MachineState} (ht : TNodeInv s0 B ℓ levels pre t)
    (r02 : RegsExcept t t2 [.x6, .x6, .x7, .x28, .x29, .x30, .x10, .x11, .x12, .x29])
    (f02 : Frame t t2 (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56)) {v : Digest} (hw : KokPost t2 B.arena (2 ^ (12 - ℓ - 1) + pre.length) v w) :
    w.pc = pcOf 235 ∧ TNodeInv s0 B ℓ levels (pre ++ [v]) w := by
  have ha := hpre.ha
  have has := hpre.has
  rw [hh12] at ha has
  set lo := 2 ^ (12 - ℓ - 1) with hlo_def
  set i := pre.length with hi_def
  have hY : 2 ^ (12 - ℓ) = 2 * lo := two_pow_split hl
  have hYZ : 2 ^ (12 - ℓ) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have fall : Frame t w (fun X => (X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
      X = NODE + 56) ∨ KokW B.arena (lo + i) X) := f02.trans hw.frame
  have gk : ∀ x, x ∉ kokRegs → x ∉ [Reg.x6, .x6, .x7, .x28, .x29, .x30, .x10, .x11, .x12, .x29] →
      w.getReg x = t.getReg x := fun x h1 h2 => by rw [hw.regs.get h1, r02.get h2]
  refine ⟨hw.pc, ⟨?_, ?_, ?_, ?_, ?_, ⟨ht.heap.1, fun l hl' => ?_⟩, ?_⟩⟩
  · rw [gk _ (by decide) (by decide)]; exact ht.x13
  · rw [gk _ (by decide) (by decide)]; exact ht.x20
  · rw [hw.x24, List.length_append, List.length_singleton, hh12, Nat.add_assoc]
  · exact ((ht.regs.trans r02).trans hw.regs).mono (by decide)
  · intro X hX hn
    by_cases h32 : X = NODE + 32
    · subst h32; rw [hw.pad, hpre.z32]
    · rw [fall.get hX (fun h => by
        unfold LevW at hn; unfold KokW TrialW at h; rw [hh12] at hn
        simp only [NODE, NOUT] at hn h h32 has
        omega), ht.frame.get hX hn]
  · obtain ⟨hl1, hl2⟩ := ht.heap.2 l hl'
    rw [hh12] at hl1 hl2 ⊢
    have hYl : 2 * lo ≤ 2 ^ (12 - l) := by
      rw [← hY]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hYlZ : 2 ^ (12 - l) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨hl1, hl2.frame fall (by rw [hl1]; omega) (fun X h1 h2 h => ?_)⟩
    rw [hl1] at h2
    unfold KokW TrialW at h
    simp only [NODE, NOUT] at h has
    omega
  · have hc := ht.cur
    rw [hh12] at hc ⊢
    refine (hc.frame fall (by omega) (fun X h1 h2 h => ?_)).snoc ?_
    · unfold KokW TrialW at h
      simp only [NODE, NOUT] at h has
      omega
    · rw [show B.arena + 16 * lo + 16 * i = B.arena + 16 * (lo + i) by ring]; exact hw.dig

theorem tnode {ℓ : Nat} (hl : ℓ < 12) {levels : List (List Digest)} {pre : List Digest}
    (hi : pre.length < 2 ^ (12 - ℓ - 1)) {t : MachineState} (ht : TNodeInv s0 B ℓ levels pre t)
    (hpc : t.pc = pcOf 235) :
    TBSim image sk t (nodeW (ℓ + 1))
      (topNodeProg (ℓ + 1) (2 ^ (12 - ℓ - 1) + pre.length) ((levels.getD ℓ []).getD (2 * pre.length) 0)
        ((levels.getD ℓ []).getD (2 * pre.length + 1) 0))
      (fun v u => u.pc = pcOf 235 ∧ TNodeInv s0 B ℓ levels (pre ++ [v]) u) := by
  obtain ⟨t2, st, p2, x10, x11, z32, F, r02, f02⟩ := node_prefix hpre htop hh12 hl hi ht hpc
  have hq := hashInput_topNode t2 _ 0 F.h1 F.h2 (by norm_num) _ _ x10 x11 F.w0 F.w8 F.w16 F.w24
    (by rw [z32]; rfl) F.w40 F.w48 F.w56
  have hv : hashArgumentsValid t2 = true :=
    hashArgs_const t2 NODE 64 NOUT x10 x11 F.x12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hf : fetch image t2 = some (.base .ECALL) := fetch_sub146 subAt_keygen t2 p2
  have x13 : t2.getReg .x13 = BitVec.ofNat 64 (ℓ + 1) := by rw [r02.get (by decide)]; exact ht.x13
  have hwf : ∀ a, Frame t2 (writeHash t2 a) TrialW := fun a =>
    (Frame.writeHash t2 a NOUT F.x12 (by decide)).mono (fun X _ h => Or.inr h)
  have hw0 : ∀ a, RegsExcept t2 (writeHash t2 a) [] := fun a r _ => getReg_writeHash t2 a r
  unfold topNodeProg
  by_cases hroot : ℓ + 1 = 12
  · rw [if_pos hroot, nodeHash_top]
    refine (TBSim.steps st (TBSim.publicHash_bind hf F.x5 hv hq (W := 15) (fun a => ?_))).mono
      (by unfold nodeW; rw [if_pos hroot, topNodeInput_blocks]) (fun _ _ h => h)
    obtain ⟨u1, s1, p1, r1, f1⟩ := kt264_spec (writeHash t2 a) (by rw [pc_writeHash, p2, pcOf_add4])
    obtain ⟨u2, s2, p2', r2, f2⟩ := ktC0_spec u1 p1 (ℓ + 1) (by omega)
      (by rw [r1.get (by simp), getReg_writeHash]; exact x13)
    rw [if_pos hroot] at p2'
    obtain ⟨w, sw, hw⟩ := kok_run F p2' (L := [] ++ [] ++ [.x28]) (by decide) (((hw0 a).trans r1).trans r2)
      ((((hwf a).trans f1).trans f2).mono (fun X _ h => by
        rcases h with (h | h) | h; exact h; exact h.elim; exact h.elim))
      ((out_after_hash t2 a _ F.x12).frame (f1.trans f2) (by simp only [NOUT]; omega)
        (fun h => by rcases h with h | h <;> exact h) (fun h => by rcases h with h | h <;> exact h))
    exact TBSim.pure_steps (s1.trans (s2.trans sw)) (node_post hpre htop hh12 hl hi ht r02 f02 hw)
  by_cases hsmall : ℓ + 1 ≤ 2
  · -- campaign T51: heights 1, 2 (`b_h = 0`): 727..731 jump to KOK with the first trial
    have hb0 : topZeroBits (ℓ + 1) = 0 := by
      have : ℓ ≤ 1 := by omega
      interval_cases ℓ <;> rfl
    rw [if_neg hroot, topNodeAt_b0 _ _ _ _ hb0, nodeHash_top]
    refine (TBSim.steps st (TBSim.publicHash_bind hf F.x5 hv hq (W := 18) (fun a => ?_))).mono
      (by unfold nodeW; rw [if_neg hroot, topNodeInput_blocks]; have : 1 ≤ topNonceCap (ℓ + 1) := by
            unfold topNonceCap; exact Nat.mul_pos (by norm_num) (Nat.two_pow_pos _)
          omega) (fun _ _ h => h)
    obtain ⟨u1, s1, p1, r1, f1⟩ := kt264_spec (writeHash t2 a) (by rw [pc_writeHash, p2, pcOf_add4])
    obtain ⟨u2, s2, p2', r2, f2⟩ := ktC0_spec u1 p1 (ℓ + 1) (by omega)
      (by rw [r1.get (by simp), getReg_writeHash]; exact x13)
    rw [if_neg hroot] at p2'
    obtain ⟨u3, s3, p3, -, r3, f3⟩ := ktC1_spec u2 p2' (ℓ + 1) (by omega)
      (by rw [r2.get (by simp), r1.get (by simp), getReg_writeHash]; exact x13)
    rw [if_pos (by omega)] at p3
    obtain ⟨w, sw, hw⟩ := kok_run F p3 (L := [] ++ [] ++ [.x28] ++ [.x14, .x28]) (by decide)
      ((((hw0 a).trans r1).trans r2).trans r3)
      (((((hwf a).trans f1).trans f2).trans f3).mono (fun X _ h => by
        rcases h with ((h | h) | h) | h; exact h; exact h.elim; exact h.elim; exact h.elim))
      ((out_after_hash t2 a _ F.x12).frame ((f1.trans f2).trans f3) (by simp only [NOUT]; omega)
        (fun h => by rcases h with (h | h) | h <;> exact h) (fun h => by rcases h with (h | h) | h <;> exact h))
    exact TBSim.pure_steps (s1.trans (s2.trans (s3.trans sw))) (node_post hpre htop hh12 hl hi ht r02 f02 hw)
  · rw [if_neg hroot]
    have h1 : 3 ≤ ℓ + 1 := by omega
    have h1' : 1 ≤ ℓ + 1 := by omega
    have h11 : ℓ + 1 ≤ 11 := by omega
    have hcap := topNonceCap_le (ℓ + 1) h1' h11
    apply TBSim.map
    unfold topNodeAt
    rw [topNonceSearch_eq, topNodeHashN_bind]
    refine (TBSim.steps st (TBSim.publicHash_bind hf F.x5 hv hq
      (W := 1 + setupK (ℓ + 1) + (21 * (topNonceCap (ℓ + 1) - 1) + 20)) (fun a => ?_))).mono
      (by unfold nodeW; rw [if_neg hroot, topNodeInput_blocks]; have := setupK_le (ℓ + 1); omega)
      (fun _ _ h => h)
    obtain ⟨u1, s1, p1, r1, f1⟩ := kt264_spec (writeHash t2 a) (by rw [pc_writeHash, p2, pcOf_add4])
    obtain ⟨u2, s2, p2', x16, x17, r2, f2⟩ := ksetup_spec u1 p1 (ℓ + 1) h1 h11
      (by rw [r1.get (by simp), getReg_writeHash]; exact x13)
    have hts : TrialSt t2 (ℓ + 1) (2 ^ (12 - ℓ - 1) + pre.length) 0 a u2 :=
      ⟨p2', (((hw0 a).trans r1).trans r2).mono (by decide), x16, x17,
        by rw [f2.get (by decide) (fun h => h), f1.get (by decide) (fun h => h),
          (Frame.writeHash t2 a NOUT F.x12 (by decide)).get (by decide) (by simp only [NODE, NOUT]; omega), z32]; rfl,
        (((hwf a).trans f1).trans f2).mono (fun X _ h => by
          rcases h with (h | h) | h; exact h; exact h.elim; exact h.elim),
        (out_after_hash t2 a _ F.x12).frame (f1.trans f2) (by simp only [NOUT]; omega)
          (fun h => by rcases h with h | h <;> exact h) (fun h => by rcases h with h | h <;> exact h)⟩
    exact (TBSim.steps (s1.trans s2) (trial_loop sk F (ℓ + 1) h1' h11 _ 0 a u2 hts (by omega))).mono
      (by omega) (fun res w hw => node_post hpre htop hh12 hl hi ht r02 f02 hw)

/-- Cycle bound of tree level `ℓ` (nodes of height `ℓ + 1`). -/
def levelW (ℓ : Nat) : Nat := 8 + 2 ^ (11 - ℓ) * nodeW (ℓ + 1)
/-- Cycle bound of the top-tree routine (230 to the return). -/
def treeW : Nat := 6 + (sumTo levelW 12 + 2)

theorem tlev_level {ℓ : Nat} (hl : ℓ < 12) {levels : List (List Digest)} {t : MachineState}
    (ht : TLevInv s0 B ℓ levels t) (hpc : t.pc = pcOf 233) :
    TBSim image sk t (levelW ℓ)
      (do let nodes ← buildTopLevel (1 + ℓ) (levels.getD (1 + ℓ - 1) [])
          pure (levels ++ [nodes]))
      (fun levels' u => u.pc = pcOf 233 ∧ TLevInv s0 B (ℓ + 1) levels' u) := by
  have ha := hpre.ha
  rw [hh12] at ha
  set lo := 2 ^ (12 - ℓ - 1) with hlo_def
  have hY : 2 ^ (12 - ℓ) = 2 * lo := two_pow_split hl
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have hloZ : lo ≤ 2048 := by
    calc lo ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2048 := by norm_num
  have hx20 : 2 ^ B.h / 2 ^ (ℓ + 1) = lo := by
    rw [hh12, hlo_def, show 12 = (ℓ + 1) + (12 - ℓ - 1) by omega, Nat.pow_add, Nat.mul_div_cancel_left _
      (by positivity)]
    congr 1; omega
  have hx20' : 2 ^ B.h / 2 ^ (ℓ + 1 + 1) = lo / 2 := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hx20]
  have hl1 : 2 ^ (11 - ℓ) = lo := by rw [hlo_def]; congr 1; omega
  have r20 : t.getReg .x20 = BitVec.ofNat 64 lo := by rw [ht.x20, hx20]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub116_spec subAt_keygen t hpc lo (by omega) r20
  rw [if_neg (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x24, t2r, t2f⟩ := sub117_spec subAt_keygen t1 t1pc
  have f02 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  have h0 : TNodeInv s0 B ℓ levels [] t2 := by
    refine ⟨?_, ?_, ?_, ?_, (ht.frame.trans f02).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim),
      ⟨ht.heap.1, fun l hl' => ⟨(ht.heap.2 l hl').1, (ht.heap.2 l hl').2.frame f02 (by
        rw [(ht.heap.2 l hl').1, hh12]
        have : 2 ^ (12 - l) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega) (fun X _ _ h => h.elim)⟩⟩, DigsAt.nil _ _⟩
    · rw [t2r.get (by simp), t1r.get (by simp), ht.x13]
    · rw [t2r.get (by simp), t1r.get (by simp), r20, hh12]
    · rw [t2x24, t1r.get (by simp), r20, List.length_nil, Nat.add_zero, hh12]
    · exact (ht.regs.trans (t1r.trans t2r)).mono (by decide)
  have hnodes : (levels.getD (1 + ℓ - 1) []).length / 2 = lo := by
    have := (ht.heap.2 ℓ le_rfl).1
    rw [hh12] at this
    rw [show 1 + ℓ - 1 = ℓ by omega, this, hY]; omega
  unfold buildTopLevel
  rw [hnodes, show 1 + ℓ - 1 = ℓ by omega, show 1 + ℓ = ℓ + 1 by omega, show 12 - (ℓ + 1) = 12 - ℓ - 1 by omega]
  refine (TBSim.steps (st1.trans st2) (TBSim.bind (W₂ := 6)
    (TBSim.mapM_range lo _ (nodeW (ℓ + 1))
      (fun pre w => w.pc = pcOf 235 ∧ TNodeInv s0 B ℓ levels pre w)
      (fun pre w hpre' hw => tnode sk hpre htop hh12 hl hpre' hw.2 hw.1) ⟨t2pc, h0⟩) (fun nodes w hw => ?_))).mono
    (by unfold levelW; rw [hl1]; omega) (fun _ _ h => h)
  obtain ⟨hlen, wpc, hw⟩ := hw
  have w20 : w.getReg .x20 = BitVec.ofNat 64 lo := by rw [hw.x20, hh12]
  obtain ⟨w1, st3, w1pc, w1r, w1f⟩ := sub118_spec subAt_keygen w wpc lo (lo + nodes.length) (by omega) (by omega)
    w20 (by rw [hw.x24, hh12])
  rw [if_neg (by omega)] at w1pc
  obtain ⟨w2, st4, w2pc, w2r, w2f⟩ := kt274_spec w1 w1pc
  obtain ⟨w3, st5, w3pc, w3x20, w3x13, w3r, w3f⟩ := ktN_spec w2 w2pc lo (ℓ + 1) (by omega) (by omega)
    (by rw [w2r.get (by simp), w1r.get (by simp)]; exact w20)
    (by rw [w2r.get (by simp), w1r.get (by simp)]; exact hw.x13)
  have f13 : Frame w w3 (fun _ => False) := ((w1f.trans w2f).trans w3f).mono (fun X _ h => by simp_all)
  refine TBSim.pure_steps (st3.trans (st4.trans st5)) ⟨w3pc, w3x13, ?_, ?_, ?_, ?_⟩
  · rw [w3x20, hx20']
  · exact (hw.regs.trans ((w1r.trans w2r).trans w3r)).mono (by decide)
  · exact (hw.frame.trans f13).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
  · obtain ⟨hlen0, hlev⟩ := hw.heap
    refine ⟨by simp [hlen0], fun l hl' => ?_⟩
    rw [hh12]
    by_cases hle : l ≤ ℓ
    · have hg : (levels ++ [nodes]).getD l [] = levels.getD l [] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show l < levels.length by omega)]
      rw [hg]
      obtain ⟨h1, h2⟩ := hlev l hle
      rw [hh12] at h1 h2
      have : 2 ^ (12 - l) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact ⟨h1, h2.frame f13 (by rw [h1]; omega) (fun X _ _ h => h.elim)⟩
    · have hl2 : l = ℓ + 1 := by omega
      subst hl2
      have hg : (levels ++ [nodes]).getD (ℓ + 1) [] = nodes := by
        simp [List.getD_eq_getElem?_getD, hlen0]
      rw [hg, show 12 - (ℓ + 1) = 12 - ℓ - 1 by omega]
      have hc := hw.cur
      rw [hh12] at hc
      exact ⟨hlen, hc.frame f13 (by rw [hlen]; omega) (fun X _ _ h => h.elim)⟩

/-- The keygen top-tree routine (entry 230 = `117 + 113`, return to `B.ret`) refines `buildTopLevels`. -/
theorem buildTopLevels_tbsim (hpc : s0.pc = pcOf 230) :
    TBSim image sk s0 treeW (buildTopLevels leaves)
      (fun levels t => t.pc = pcOf B.ret ∧ HeapAt t B B.h levels ∧ RegsExcept s0 t topLevRegs ∧
        Frame s0 t (LevW B)) := by
  have ha := hpre.ha
  rw [hh12] at ha
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := kt230_spec s0 hpc
  obtain ⟨t2, st2, t2pc, t2x20, t2x13, t2r, t2f⟩ := ktI_spec t1 t1pc
  obtain ⟨t3, st3, t3pc, t3x20, t3r, t3f⟩ := kt231_spec t2 t2pc 12 (by norm_num) (by norm_num)
    (by rw [t2r.get (by simp), t1r.get (by simp), hpre.x15, hh12]) t2x20
  have f03 : Frame s0 t3 (fun _ => False) := ((t1f.trans t2f).trans t3f).mono (fun X _ h => by simp_all)
  have h0 : TLevInv s0 B 0 [leaves] t3 := by
    refine ⟨by rw [t3r.get (by simp)]; exact t2x13, by rw [t3x20, hh12]; rfl,
      ((t1r.trans t2r).trans t3r).mono (by decide), f03.mono (fun X _ h => h.elim), ⟨rfl, fun l hl => ?_⟩⟩
    have hl0 : l = 0 := by omega
    subst hl0
    simp only [List.getD_cons_zero, Nat.sub_zero]
    have hlv := hpre.hleaves
    rw [hh12] at hlv ⊢
    exact ⟨by rw [hpre.hlen, hh12], hlv.frame f03 (by rw [hpre.hlen, hh12]; omega) (fun X _ _ h => h.elim)⟩
  unfold buildTopLevels
  refine (TBSim.steps (st1.trans (st2.trans st3)) (TBSim.bind (W₂ := 2) (f := Pure.pure)
    (TBSim.foldlM_range'_var 1 12 _ [leaves]
      (fun j levels t => t.pc = pcOf 233 ∧ TLevInv s0 B j levels t) levelW
      (fun j hj levels t ht => tlev_level sk hpre htop hh12 hj ht.2 ht.1) ⟨t3pc, h0⟩)
    (fun levels t ht => ?_))).of_eq (bind_pure _) |>.mono (by unfold treeW; omega) (fun _ _ h => h)
  obtain ⟨tpc, hinv⟩ := ht
  have hx : 2 ^ B.h / 2 ^ (12 + 1) = 0 := by rw [hh12]; norm_num
  obtain ⟨u1, st4, u1pc, u1r, u1f⟩ := sub116_spec subAt_keygen t tpc 0 (by omega) (by rw [hinv.x20, hx])
  rw [if_pos rfl] at u1pc
  obtain ⟨u2, st5, u2pc, u2r, u2f⟩ := sub159_spec subAt_keygen u1 u1pc B.ret
    (by rw [u1r.get (by simp), hinv.regs.get (by decide), hpre.x1])
  have f12 : Frame t u2 (fun _ => False) := (u1f.trans u2f).mono (fun X _ h => by simp_all)
  refine TBSim.pure_steps (st4.trans st5) ⟨u2pc, ⟨by rw [hh12]; exact hinv.heap.1, fun l hl => ?_⟩,
    (hinv.regs.trans (u1r.trans u2r)).mono (by decide),
    (hinv.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)⟩
  obtain ⟨h1, h2⟩ := hinv.heap.2 l (by rw [hh12] at hl; exact hl)
  rw [hh12] at h1 h2 ⊢
  have : 2 ^ (12 - l) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨h1, h2.frame f12 (by rw [h1]; omega) (fun X _ _ h => h.elim)⟩

end node

end SigGolfCandidate.T3M.Keygen
