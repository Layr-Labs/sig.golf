import SigGolfCandidate.T3M_Keygen_Leaf
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_GfMul

/-!
# Keygen top leaf with family seeds (campaign T8D, TOP2 NF17)

The keygen image's top-leaf routine (entry 144) first runs KTOP (img-v6, 612 -> 1149..1168 + the pair loop 618..640:
at a family start `leaf % 4 = 0` the family's private pairs `privatePair 0 0 0 (31 f / 2 + j) 0`, `j ∈ [f % 2, 16)`,
copied to the coefficient buffer at `KCOEF`, an odd family first copying the carry slot 31 to slot 0; otherwise
nothing: `topFamilyCoefs`), then for every chain `i < 51` (campaign T51) runs
HORN (642 -> KHORN 1169..1176, loop 647..682: `familyEval coefs (topPoint leaf i)`, 31 coefficients, into `CHAIN + 48`), the per-chain cap table CAP (684..688: `maxDigit 0 i`),
the shared chain routine (117) and stores the chain end; finally the leaf hash. This file proves the blocks, the two
new loops and `buildLeafTop_tsim` (refinement of `T3.buildLeafTop leaf []` with exact step/cycle/hash counts).
-/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chainCount maxDigit chain leafHash privatePair header privateInput
  topCoefsK topPairsFrom topFamilyCoefs topCoefCount topSeedPair topSeed topPoint buildLeafTopC pad64)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign.Gf ClaudeWCT.Arith

local instance (image : Image) (pc : Word) (code : List (BitVec 32)) :
    Decidable (CodeAt image pc code) := by
  unfold CodeAt
  infer_instance

/-! ## Blocks -/
def kg27 : List (BitVec 32) := sub27K
def kg159 : List (BitVec 32) := sub42K
def kg161 : List (BitVec 32) := sub44K.take 1
def kg188 : List (BitVec 32) := [20647475]
def kg192 : List (BitVec 32) := sub75K
def kg612 : List (BitVec 32) := coefgenCode.take 1
def kgCG1 : List (BitVec 32) := (coefgenCode.drop 6).take 5
def kgCG2 : List (BitVec 32) := (coefgenCode.drop 12).take 15
def kgCG3 : List (BitVec 32) := (coefgenCode.drop 27).take 2
def kgH0 : List (BitVec 32) := hornCode.take 1
def kgHK : List (BitVec 32) := (hornCode.drop 5).take 6
def kgHB1 : List (BitVec 32) := (hornCode.drop 11).take 2
def kgHB2 : List (BitVec 32) := (hornCode.drop 13).take 3
def kgHB3 : List (BitVec 32) := (hornCode.drop 16).take 9
def kgHF : List (BitVec 32) := (hornCode.drop 25).take 12
def kgHE : List (BitVec 32) := (hornCode.drop 37).take 4
def kgC1 : List (BitVec 32) := capCode.take 3
def kgC2 : List (BitVec 32) := capCode.drop 3
/-- Campaign T51: the CAP continuation at 770 (`i < 48`, `i < 50`, chain 50). -/
def kgC3 : List (BitVec 32) := capCont.take 2
def kgC4 : List (BitVec 32) := (capCont.drop 2).take 3
def kgC5 : List (BitVec 32) := capCont.drop 5
def kfA : List (BitVec 32) := ktopCode.take 2
def kfB : List (BitVec 32) := (ktopCode.drop 2).take 10
def kfD : List (BitVec 32) := (ktopCode.drop 12).take 5
def kfE : List (BitVec 32) := (ktopCode.drop 17).take 1
def kfF : List (BitVec 32) := (ktopCode.drop 18).take 2
def khA : List (BitVec 32) := (ktopCode.drop 20).take 8

theorem codeAt_kg27 : CodeAt image (pcOf 144) kg27 := by decide +kernel
theorem codeAt_kg159 : CodeAt image (pcOf 159) kg159 := by decide +kernel
theorem codeAt_kg161 : CodeAt image (pcOf 161) kg161 := by decide +kernel
theorem codeAt_kg188 : CodeAt image (pcOf 188) kg188 := by decide +kernel
theorem codeAt_kg192 : CodeAt image (pcOf 192) kg192 := by decide +kernel
theorem codeAt_kg612 : CodeAt image (pcOf 612) kg612 := by decide +kernel
theorem codeAt_kgCG1 : CodeAt image (pcOf 618) kgCG1 := by decide +kernel
theorem codeAt_kg623 : CodeAt image (pcOf 623) [115] := by decide +kernel
theorem codeAt_kgCG2 : CodeAt image (pcOf 624) kgCG2 := by decide +kernel
theorem codeAt_kgCG3 : CodeAt image (pcOf 639) kgCG3 := by decide +kernel
theorem codeAt_kgH0 : CodeAt image (pcOf 642) kgH0 := by decide +kernel
theorem codeAt_kgHK : CodeAt image (pcOf 647) kgHK := by decide +kernel
theorem codeAt_kgHB1 : CodeAt image (pcOf 653) kgHB1 := by decide +kernel
theorem codeAt_kgHB2 : CodeAt image (pcOf 655) kgHB2 := by decide +kernel
theorem codeAt_kgHB3 : CodeAt image (pcOf 658) kgHB3 := by decide +kernel
theorem codeAt_kgHF : CodeAt image (pcOf 667) kgHF := by decide +kernel
theorem codeAt_kgHE : CodeAt image (pcOf 679) kgHE := by decide +kernel
theorem codeAt_kgC1 : CodeAt image (pcOf 684) kgC1 := by decide +kernel
theorem codeAt_kgC2 : CodeAt image (pcOf 687) kgC2 := by decide +kernel
theorem codeAt_kgC3 : CodeAt image (pcOf 770) kgC3 := by decide +kernel
theorem codeAt_kgC4 : CodeAt image (pcOf 772) kgC4 := by decide +kernel
theorem codeAt_kgC5 : CodeAt image (pcOf 775) kgC5 := by decide +kernel
theorem codeAt_kfA : CodeAt image (pcOf 1149) kfA := by decide +kernel
theorem codeAt_kfB : CodeAt image (pcOf 1151) kfB := by decide +kernel
theorem codeAt_kfD : CodeAt image (pcOf 1161) kfD := by decide +kernel
theorem codeAt_kfE : CodeAt image (pcOf 1166) kfE := by decide +kernel
theorem codeAt_kfF : CodeAt image (pcOf 1167) kfF := by decide +kernel
theorem codeAt_khA : CodeAt image (pcOf 1169) khA := by decide +kernel

sym_block bk27 := symRun { noAlias := true } kg27 (pcOf 144) 100
sym_block bk159 := symRun { noAlias := true } kg159 (pcOf 159) 100
sym_block bk161 := symRun { noAlias := true } kg161 (pcOf 161) 100
sym_block bk188 := symRun { noAlias := true } kg188 (pcOf 188) 100
sym_block bk192 := symRun { noAlias := true } kg192 (pcOf 192) 100
sym_block bk612 := symRun { noAlias := true } kg612 (pcOf 612) 100
sym_block bkCG1 := symRun { noAlias := true } kgCG1 (pcOf 618) 100
sym_block bkCG2 := symRun { noAlias := true } kgCG2 (pcOf 624) 100
sym_block bkCG3 := symRun { noAlias := true } kgCG3 (pcOf 639) 100
sym_block bkH0 := symRun { noAlias := true } kgH0 (pcOf 642) 100
sym_block bkHK := symRun { noAlias := true } kgHK (pcOf 647) 100
sym_block bkHB1 := symRun { noAlias := true } kgHB1 (pcOf 653) 100
sym_block bkHB2 := symRun { noAlias := true } kgHB2 (pcOf 655) 100
sym_block bkHB3 := symRun { noAlias := true } kgHB3 (pcOf 658) 100
sym_block bkHF := symRun { noAlias := true } kgHF (pcOf 667) 100
sym_block bkHE := symRun { noAlias := true } kgHE (pcOf 679) 100
sym_block bkC1 := symRun { noAlias := true } kgC1 (pcOf 684) 100
sym_block bkC2 := symRun { noAlias := true } kgC2 (pcOf 687) 100
sym_block bkC3 := symRun { noAlias := true } kgC3 (pcOf 770) 100
sym_block bkC4 := symRun { noAlias := true } kgC4 (pcOf 772) 100
sym_block bkC5 := symRun { noAlias := true } kgC5 (pcOf 775) 100
sym_block bkfA := symRun { noAlias := true } kfA (pcOf 1149) 100
sym_block bkfB := symRun { noAlias := true } kfB (pcOf 1151) 100
sym_block bkfD := symRun { noAlias := true } kfD (pcOf 1161) 100
sym_block bkfE := symRun { noAlias := true } kfE (pcOf 1166) 100
sym_block bkfF := symRun { noAlias := true } kfF (pcOf 1167) 100
sym_block bkhA := symRun { noAlias := true } khA (pcOf 1169) 100

theorem kshl (x : Word) (k : Nat) (hk : k < 64) : BinOp.eval .sll x (BitVec.ofNat 64 k) = x <<< k := by
  simp only [BinOp.eval, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]
theorem kshr (x : Word) (k : Nat) (hk : k < 64) : BinOp.eval .srl x (BitVec.ofNat 64 k) = x >>> k := by
  simp only [BinOp.eval, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]

/-- Leaf entry (144..157): leaf header words, `gp = ra`, then `jal ra, COEFGEN`. -/
theorem kg27_spec (s : MachineState) (hpc : s.pc = pcOf 144) (lay leaf : Nat) (hlay : lay < 256)
    (hleaf : leaf < 2 ^ 32) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 612 ∧ t.getReg .x1 = pcOf 158 ∧ t.getReg .x3 = s.getReg .x1 ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay leaf ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧
      RegsExcept s t [.x1, .x3, .x6, .x28, .x30] ∧
      Frame s t (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
  refine ⟨_, symRun_sound bk27 codeAt_kg27 s hpc
    (by simp [bk27.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bk27.res, Result.toState_pc, E.eval]
  · simp [bk27.res, rv_simp]
  · simp [bk27.res, rv_simp]
  · simp only [Result.toState_getMem, bk27.res, LEAFPK]
    t3n [h8, h18]
    rw [show (513#64) = BitVec.ofNat 64 513 from rfl,
      ofNat_or_disjoint 513 (leaf * 65536) 16 (by decide) (by omega),
      ofNat_or_disjoint' _ (lay * 281474976710656) 48 (by omega) (by omega),
      show (13907115649320091648#64) = BitVec.ofNat 64 (193 * 2 ^ 56) from rfl,
      ofNat_or_disjoint' _ (193 * 2 ^ 56) 56 (by omega) (by omega)]
    unfold T3.hyperWord
    congr 1
    rw [Nat.mod_eq_of_lt hleaf, Nat.mod_eq_of_lt hlay]
    omega
  · simp only [Result.toState_getMem, bk27.res, LEAFPK]
    t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [bk27.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [LEAFPK] at hn
    simp only [Result.toState_getMem, bk27.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

/-- 159..160: `addi a3, s3, 1; jal ra, HORN`. -/
theorem kg159_spec (s : MachineState) (hpc : s.pc = pcOf 159) (i : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 642 ∧ t.getReg .x1 = pcOf 161 ∧
      t.getReg .x13 = BitVec.ofNat 64 (i + 1) ∧ RegsExcept s t [.x1, .x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bk159 codeAt_kg159 s hpc (by simp [bk159.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [bk159.res, Result.toState_pc, E.eval]
  · simp [bk159.res, rv_simp]
  · t3n [bk159.res, h19]
  · intro r hr; simp at hr; cases r <;> simp_all [bk159.res, rv_simp] <;> rfl
  · intro A _ _; simp [bk159.res, rv_simp]

/-- 161: `j 188`. -/
theorem kg161_spec (s : MachineState) (hpc : s.pc = pcOf 161) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 188 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bk161 codeAt_kg161 s hpc (by simp [bk161.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bk161.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bk161.res, rv_simp] <;> rfl
  · intro A _ _; simp [bk161.res, rv_simp]

/-- 188: `add t3, s6, s3` (digit address). -/
theorem kg188_spec (s : MachineState) (hpc : s.pc = pcOf 188) (i digp : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h22 : s.getReg .x22 = BitVec.ofNat 64 digp) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 189 ∧ t.getReg .x28 = BitVec.ofNat 64 (digp + i) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bk188 codeAt_kg188 s hpc (by simp [bk188.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [bk188.res, Result.toState_pc, E.eval]
  · t3n [bk188.res, h19, h22]
  · intro r hr; simp at hr; cases r <;> simp_all [bk188.res, rv_simp] <;> rfl
  · intro A _ _; simp [bk188.res, rv_simp]

/-- 192: `j CAP`. -/
theorem kg192_spec (s : MachineState) (hpc : s.pc = pcOf 192) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 684 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bk192 codeAt_kg192 s hpc (by simp [bk192.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bk192.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bk192.res, rv_simp] <;> rfl
  · intro A _ _; simp [bk192.res, rv_simp]

/-- Steps of CAP (campaign T51): 3 (`i < 27`), 7 (`i < 48`), 10 (`i < 50`), 12 (chain 50). -/
def capK (i : Nat) : Nat := if i < 27 then 3 else if i < 48 then 7 else if i < 50 then 10 else 12
/-- CAP (684..688, 770..776): `s5 = maxDigit 0 i`, then 193. -/
theorem kgCap_spec (s : MachineState) (hpc : s.pc = pcOf 684) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s (capK i) (capK i) t ∧ t.pc = pcOf 193 ∧
      t.getReg .x21 = BitVec.ofNat 64 (maxDigit 0 i) ∧ RegsExcept s t [.x21, .x30] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨t1, st1, t1pc, t1x21, t1r, t1f⟩ : ∃ t, Steps image s 3 3 t ∧
      t.pc = (if i < 27 then pcOf 193 else pcOf 687) ∧ t.getReg .x21 = BitVec.ofNat 64 5 ∧
      RegsExcept s t [.x21, .x30] ∧ Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound bkC1 codeAt_kgC1 s hpc (by simp [bkC1.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, bkC1.res, E.eval, CmpOp.eval, h19,
        ofNat_slt i 27 hi (by norm_num)]
      by_cases h : i < 27 <;> simp [h]
    · simp [bkC1.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [bkC1.res, rv_simp] <;> rfl
    · intro A _ _; simp [bkC1.res, rv_simp]
  by_cases h27 : i < 27
  · rw [if_pos h27] at t1pc
    refine ⟨t1, by simpa [capK, h27] using st1, t1pc, ?_, t1r, t1f⟩
    rw [t1x21]; simp [maxDigit, h27]
  rw [if_neg h27] at t1pc
  obtain ⟨t2, st2, t2pc, t2x21, t2r, t2f⟩ : ∃ t, Steps image t1 2 2 t ∧ t.pc = pcOf 770 ∧
      t.getReg .x21 = BitVec.ofNat 64 4 ∧ RegsExcept t1 t [.x21] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound bkC2 codeAt_kgC2 t1 t1pc (by simp [bkC2.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [bkC2.res, Result.toState_pc, E.eval]
    · simp [bkC2.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [bkC2.res, rv_simp] <;> rfl
    · intro A _ _; simp [bkC2.res, rv_simp]
  have r19 : t2.getReg .x19 = BitVec.ofNat 64 i := by rw [t2r.get (by simp), t1r.get (by simp)]; exact h19
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ : ∃ t, Steps image t2 2 2 t ∧
      t.pc = (if i < 48 then pcOf 193 else pcOf 772) ∧ RegsExcept t2 t [.x30] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound bkC3 codeAt_kgC3 t2 t2pc (by simp [bkC3.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, bkC3.res, E.eval, CmpOp.eval, r19,
        ofNat_slt i 48 hi (by norm_num)]
      by_cases h : i < 48 <;> simp [h]
    · intro r hr; simp at hr; cases r <;> simp_all [bkC3.res, rv_simp] <;> rfl
    · intro A _ _; simp [bkC3.res, rv_simp]
  have r12 : RegsExcept s t3 ([.x21, .x30] ++ [.x21] ++ [.x30]) := (t1r.trans t2r).trans t3r
  have f12 : Frame s t3 (fun _ => False) := ((t1f.trans t2f).trans t3f).mono (fun _ _ h => by simp_all)
  by_cases h48 : i < 48
  · rw [if_pos h48] at t3pc
    refine ⟨t3, by simpa [capK, h27, h48] using (st1.trans st2).trans st3, t3pc, ?_, r12.mono (by simp), f12⟩
    rw [t3r.get (by simp), t2x21]; simp [maxDigit, h27, h48]
  rw [if_neg h48] at t3pc
  have r19' : t3.getReg .x19 = BitVec.ofNat 64 i := by rw [t3r.get (by simp)]; exact r19
  obtain ⟨t4, st4, t4pc, t4x21, t4r, t4f⟩ : ∃ t, Steps image t3 3 3 t ∧
      t.pc = (if i < 50 then pcOf 193 else pcOf 775) ∧ t.getReg .x21 = BitVec.ofNat 64 6 ∧
      RegsExcept t3 t [.x21, .x30] ∧ Frame t3 t (fun _ => False) := by
    refine ⟨_, symRun_sound bkC4 codeAt_kgC4 t3 t3pc (by simp [bkC4.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, bkC4.res, E.eval, CmpOp.eval, r19',
        ofNat_slt i 50 hi (by norm_num)]
      by_cases h : i < 50 <;> simp [h]
    · simp [bkC4.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [bkC4.res, rv_simp] <;> rfl
    · intro A _ _; simp [bkC4.res, rv_simp]
  have r14 : RegsExcept s t4 ([.x21, .x30] ++ [.x21] ++ [.x30] ++ [.x21, .x30]) := r12.trans t4r
  have f14 : Frame s t4 (fun _ => False) := (f12.trans t4f).mono (fun _ _ h => by simp_all)
  by_cases h50 : i < 50
  · rw [if_pos h50] at t4pc
    refine ⟨t4, by simpa [capK, h27, h48, h50] using ((st1.trans st2).trans st3).trans st4, t4pc, ?_,
      r14.mono (by simp), f14⟩
    rw [t4x21]; simp [maxDigit, h27, h48, h50]
  rw [if_neg h50] at t4pc
  obtain ⟨t5, st5, t5pc, t5x21, t5r, t5f⟩ : ∃ t, Steps image t4 2 2 t ∧ t.pc = pcOf 193 ∧
      t.getReg .x21 = BitVec.ofNat 64 5 ∧ RegsExcept t4 t [.x21] ∧ Frame t4 t (fun _ => False) := by
    refine ⟨_, symRun_sound bkC5 codeAt_kgC5 t4 t4pc (by simp [bkC5.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [bkC5.res, Result.toState_pc, E.eval]
    · simp [bkC5.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [bkC5.res, rv_simp] <;> rfl
    · intro A _ _; simp [bkC5.res, rv_simp]
  refine ⟨t5, by simpa [capK, h27, h48, h50] using (((st1.trans st2).trans st3).trans st4).trans st5, t5pc, ?_,
    (r14.trans t5r).mono (by simp), (f14.trans t5f).mono (fun _ _ h => by simp_all)⟩
  rw [t5x21]; simp [maxDigit, h27, h48, h50]

/-! ## COEFGEN blocks -/
/-! ## img-v6 KTOP / KHORN blocks (1149..1176) -/
/-- 612 (img-v6): `jal 1149` (KTOP). -/
theorem kg612_spec (s : MachineState) (hpc : s.pc = pcOf 612) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1149 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bk612 codeAt_kg612 s hpc (by simp [bk612.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bk612.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bk612.res, rv_simp] <;> rfl
  · intro A _ _; simp [bk612.res, rv_simp]

theorem kand3 (q : Nat) : BitVec.ofNat 64 q &&& 3#64 = BitVec.ofNat 64 (q % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show 3 % 2 ^ 64 = 2 ^ 2 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- 1149..1150: `t5 = s2 & 3; bne t5, zero, 1167`. -/
theorem kfA_spec (s : MachineState) (hpc : s.pc = pcOf 1149) (leaf : Nat)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if leaf % 4 = 0 then pcOf 1151 else pcOf 1167) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkfA codeAt_kfA s hpc (by simp [bkfA.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkfA.res, E.eval, CmpOp.eval, RegFile.get, h18, BinOp.eval, kand3]
    by_cases h : leaf % 4 = 0
    · simp [h]
    · have : BitVec.ofNat 64 (leaf % 4) ≠ 0#64 := by
        rw [Ne, show (0#64) = BitVec.ofNat 64 0 from rfl, ofNat_inj (by omega) (by norm_num)]; exact h
      simp [h, this]
  · intro r hr; simp at hr; cases r <;> simp_all [bkfA.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkfA.res, rv_simp]

theorem kshr2 (q : Nat) (hq : q < 2 ^ 64) :
    BitVec.ofNat 64 q >>> (2 : Nat) &&& 1#64 = BitVec.ofNat 64 (q / 4 % 2) := by
  rw [ofNat_shr q 2 hq, ofNat_and1]; rfl
theorem kfB_x14 (leaf : Nat) (hleaf : leaf < 2 ^ 32) :
    (BitVec.ofNat 64 leaf >>> (2 : Nat) * 31#64 + BitVec.ofNat 64 (leaf / 4 % 2)) >>> (1 : Nat) <<< (32 : Nat) |||
      1#64 = BitVec.ofNat 64 (1 + 2 ^ 32 * (31 * (leaf / 4) / 2 + leaf / 4 % 2)) := by
  have e1 : BitVec.ofNat 64 leaf >>> (2 : Nat) = BitVec.ofNat 64 (leaf / 4) := by
    rw [ofNat_shr leaf 2 (by omega)]; rfl
  have e2 : BitVec.ofNat 64 (leaf / 4) * 31#64 = BitVec.ofNat 64 (leaf / 4 * 31) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]
  rw [e1, e2, ofNat_add_ofNat, ofNat_shr _ 1 (by omega), ofNat_shl, show (1#64) = BitVec.ofNat 64 1 from rfl,
    ofNat_or_disjoint 1 ((leaf / 4 * 31 + leaf / 4 % 2) / 2 ^ 1 * 2 ^ 32) 32 (by norm_num) (by omega)]
  congr 1; omega
/-- 1151..1160: `s8 = KCOEF`, `f = s2 >> 2`, `t4 = f & 1`, `a4 = ((31 f + t4) >> 1) << 32 | 1`, `beq t4, zero, 1166`
(the `mul` costs 4 cycles). -/
theorem kfB_spec (s : MachineState) (hpc : s.pc = pcOf 1151) (leaf : Nat) (hleaf : leaf < 2 ^ 32)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 10 13 t ∧ t.pc = (if leaf / 4 % 2 = 0 then pcOf 1166 else pcOf 1161) ∧
      t.getReg .x14 = BitVec.ofNat 64 (1 + 2 ^ 32 * (31 * (leaf / 4) / 2 + leaf / 4 % 2)) ∧
      t.getReg .x24 = BitVec.ofNat 64 KCOEF ∧ t.getReg .x29 = BitVec.ofNat 64 (leaf / 4 % 2) ∧
      RegsExcept s t [.x14, .x24, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  have h2 : (2#64).toNat % 64 = 2 := by decide
  have h1 : (1#64).toNat % 64 = 1 := by decide
  have h32 : (32#64).toNat % 64 = 32 := by decide
  refine ⟨_, symRun_sound bkfB codeAt_kfB s hpc (by simp [bkfB.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkfB.res, E.eval, CmpOp.eval, RegFile.get, h18, BinOp.eval, h2,
      kshr2 leaf (by omega)]
    by_cases h : leaf / 4 % 2 = 0
    · simp [h]
    · have : BitVec.ofNat 64 (leaf / 4 % 2) ≠ 0#64 := by
        rw [Ne, show (0#64) = BitVec.ofNat 64 0 from rfl, ofNat_inj (by omega) (by norm_num)]; exact h
      simp [h, this]
  · simp only [Result.toState_getReg, bkfB.res, RegFile.get, E.eval, h18, BinOp.eval, h2, h1, h32,
      kshr2 leaf (by omega)]
    exact kfB_x14 leaf hleaf
  · simp [bkfB.res, rv_simp]
  · simp only [Result.toState_getReg, bkfB.res, RegFile.get, E.eval, h18, BinOp.eval, h2,
      kshr2 leaf (by omega)]
  · intro r hr; simp at hr; cases r <;> simp_all [bkfB.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkfB.res, rv_simp]

/-- 1161..1165 (odd family): copy the carry slot 31 to slot 0, `s8 += 16`. -/
theorem kfD_spec (s : MachineState) (hpc : s.pc = pcOf 1161) (h24 : s.getReg .x24 = BitVec.ofNat 64 KCOEF) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf 1166 ∧
      t.getMem (BitVec.ofNat 64 KCOEF) = s.getMem (BitVec.ofNat 64 (KCOEF + 496)) ∧
      t.getMem (BitVec.ofNat 64 (KCOEF + 8)) = s.getMem (BitVec.ofNat 64 (KCOEF + 504)) ∧
      t.getReg .x24 = BitVec.ofNat 64 (KCOEF + 16) ∧
      RegsExcept s t [.x4, .x24] ∧ Frame s t (fun A => A = KCOEF ∨ A = KCOEF + 8) := by
  have hobl : Oblig.all s bkfD.res.st.obl := by
    simp only [bkfD.res]
    t3n [h24]
    simp only [KCOEF]
    and_intros <;> first | trivial | omega
  refine ⟨_, symRun_sound bkfD codeAt_kfD s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bkfD.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, bkfD.res]
    t3n [h24]
    all_goals (try simp only [KCOEF])
    all_goals (repeat rw [if_neg (by omega)])
  · simp only [Result.toState_getMem, bkfD.res]
    t3n [h24]
    all_goals (try simp only [KCOEF])
    all_goals (repeat rw [if_neg (by omega)])
  · t3n [bkfD.res, h24]
  · intro r hr; simp at hr; cases r <;> simp_all [bkfD.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, bkfD.res]
    t3n [h24]
    simp only [KCOEF] at hn ⊢
    rw [if_neg (by omega), if_neg (by omega)]

/-- 1166: `jal 618` (the pair loop). -/
theorem kfE_spec (s : MachineState) (hpc : s.pc = pcOf 1166) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 618 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkfE codeAt_kfE s hpc (by simp [bkfE.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bkfE.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bkfE.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkfE.res, rv_simp]

/-- 1167..1168 (not a family start): `s3 = 0; ret`. -/
theorem kfF_spec (s : MachineState) (hpc : s.pc = pcOf 1167) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf ret ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkfF codeAt_kfF s hpc (by simp [bkfF.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkfF.res, rv_simp, h1, pcOf_and_max]
  · simp [bkfF.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bkfF.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkfF.res, rv_simp]

/-- 1169..1176 (KHORN): point `a3 += (s2 & 3) << 6`, `a4 = a5 = 0`, `a1 = KCOEF`, `a0 = KCOEF + 16 · 31`,
`jal 647`. -/
theorem khA_spec (s : MachineState) (hpc : s.pc = pcOf 1169) (leaf d : Nat) (hd : d < 2 ^ 32)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h13 : s.getReg .x13 = BitVec.ofNat 64 d) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = pcOf 647 ∧ t.getReg .x13 = BitVec.ofNat 64 (d + leaf % 4 * 64) ∧
      t.getReg .x10 = BitVec.ofNat 64 (KCOEF + 16 * 31) ∧ t.getReg .x11 = BitVec.ofNat 64 KCOEF ∧
      t.getReg .x14 = BitVec.ofNat 64 0 ∧ t.getReg .x15 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x10, .x11, .x13, .x14, .x15, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkhA codeAt_khA s hpc (by simp [bkhA.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [bkhA.res, Result.toState_pc, E.eval]
  · have h6 : (6#64).toNat % 64 = 6 := by decide
    simp only [Result.toState_getReg, bkhA.res, RegFile.get, E.eval, h18, h13, BinOp.eval, kand3,
      ofNat_shl, ofNat_add_ofNat, h6]
    rfl
  all_goals first
    | (simp [bkhA.res, rv_simp] <;> rfl)
    | (intro r hr; simp at hr; cases r <;> simp_all [bkhA.res, rv_simp] <;> rfl)
    | (intro A _ _; simp [bkhA.res, rv_simp])

/-- 642 (img-v6): `jal 1169` (KHORN). -/
theorem kgH0_spec (s : MachineState) (hpc : s.pc = pcOf 642) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1169 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkH0 codeAt_kgH0 s hpc (by simp [bkH0.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bkH0.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bkH0.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkH0.res, rv_simp]

/-- 618..622: private-pair header (low word `a4`, high word 0) and the hash arguments. -/
theorem kgCG1_spec (s : MachineState) (hpc : s.pc = pcOf 618) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf 623 ∧ t.getReg .x10 = BitVec.ofNat 64 PRIV ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 SEEDS ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 16)) = s.getReg .x14 ∧ t.getMem (BitVec.ofNat 64 (PRIV + 24)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun A => A = PRIV + 16 ∨ A = PRIV + 24) := by
  refine ⟨_, symRun_sound bkCG1 codeAt_kgCG1 s hpc (by simp [bkCG1.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [bkCG1.res, Result.toState_pc, E.eval]
  · simp [bkCG1.res, rv_simp]
  · simp [bkCG1.res, rv_simp]
  · simp [bkCG1.res, rv_simp]
  · simp only [Result.toState_getMem, bkCG1.res, PRIV]; t3n []
  · simp only [Result.toState_getMem, bkCG1.res, PRIV]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [bkCG1.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem, bkCG1.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

theorem fetch_kg623 (s : MachineState) (hpc : s.pc = pcOf 623) : fetch image s = some (.base .ECALL) :=
  (codeAt_kg623.fetch s hpc).trans rfl

/-- 624..638: copy the 32-byte answer to `KCOEF + a`, next pair, `bne t4, 16` (campaign T51: count 16). -/
theorem kgCG2_spec (s : MachineState) (hpc : s.pc = pcOf 624) (j p a : Nat) (hj : j < 16) (ha : a + 32 ≤ 640) (ha8 : a % 8 = 0)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 PRIV) (h24 : s.getReg .x24 = BitVec.ofNat 64 (KCOEF + a))
    (h29 : s.getReg .x29 = BitVec.ofNat 64 j) (h14 : s.getReg .x14 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 15 15 t ∧ t.pc = (if j + 1 < 16 then pcOf 618 else pcOf 639) ∧
      t.getReg .x14 = BitVec.ofNat 64 (p + 2 ^ 32) ∧ t.getReg .x24 = BitVec.ofNat 64 (KCOEF + a + 32) ∧
      t.getReg .x29 = BitVec.ofNat 64 (j + 1) ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (KCOEF + a + 8 * k)) = s.getMem (BitVec.ofNat 64 (SEEDS + 8 * k))) ∧
      RegsExcept s t [.x4, .x14, .x24, .x29, .x30] ∧
      Frame s t (fun A => KCOEF + a ≤ A ∧ A < KCOEF + a + 32) := by
  have hobl : Oblig.all s bkCG2.res.st.obl := by
    simp only [bkCG2.res]
    t3n [h10, h24]
    simp only [PRIV, KCOEF]
    and_intros <;> first | trivial | omega
  refine ⟨_, symRun_sound bkCG2 codeAt_kgCG2 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkCG2.res, E.eval, CmpOp.eval, h29]
    by_cases h : j + 1 < 16
    · rw [if_pos h]
      simp only [BinOp.eval, ofNat_add_ofNat, bne_iff_ne, ne_eq, ofNat_inj (show j + 1 < 2 ^ 64 by omega)
        (show 16 < 2 ^ 64 by norm_num)]
      rw [if_pos (by omega)]
    · rw [if_neg h]
      simp only [BinOp.eval, ofNat_add_ofNat, bne_iff_ne, ne_eq, ofNat_inj (show j + 1 < 2 ^ 64 by omega)
        (show 16 < 2 ^ 64 by norm_num)]
      rw [if_neg (by omega)]
  · t3n [bkCG2.res, h14]
  · t3n [bkCG2.res, h24] <;> (try simp only [KCOEF]) <;> omega
  · t3n [bkCG2.res, h29]
  · intro k hk
    simp only [Result.toState_getMem, bkCG2.res]
    t3n [h10, h24]
    interval_cases k <;> split_ifs <;> first | omega | simp only [PRIV, SEEDS]
  · intro r hr; simp at hr; cases r <;> simp_all [bkCG2.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, bkCG2.res]
    t3n [h24]
    simp only [KCOEF] at hn ⊢
    repeat rw [if_neg (by omega)]

/-- 639..640: `s3 = 0; ret`. -/
theorem kgCG3_spec (s : MachineState) (hpc : s.pc = pcOf 639) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf ret ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkCG3 codeAt_kgCG3 s hpc (by simp [bkCG3.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkCG3.res, rv_simp, h1, pcOf_and_max]
  · simp [bkCG3.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bkCG3.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkCG3.res, rv_simp]

/-! ## HORN blocks -/
/-- 647..652 (HK): next coefficient address, product limbs and `tp` cleared, `t4 = a3`. -/
theorem kgHK_spec (s : MachineState) (hpc : s.pc = pcOf 647) (m : Nat) (hm : 1 ≤ m) (hm' : m ≤ 40)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (KCOEF + 16 * m)) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf 653 ∧ t.getReg .x10 = BitVec.ofNat 64 (KCOEF + 16 * (m - 1)) ∧
      t.getReg .x4 = BitVec.ofNat 64 0 ∧ t.getReg .x12 = BitVec.ofNat 64 0 ∧ t.getReg .x16 = BitVec.ofNat 64 0 ∧
      t.getReg .x24 = BitVec.ofNat 64 0 ∧ t.getReg .x29 = s.getReg .x13 ∧
      RegsExcept s t [.x4, .x10, .x12, .x16, .x24, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkHK codeAt_kgHK s hpc (by simp [bkHK.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [bkHK.res, Result.toState_pc, E.eval]
  · t3n [bkHK.res, h10]; simp only [KCOEF]; omega
  all_goals first
    | (simp [bkHK.res, rv_simp] <;> rfl)
    | (intro r hr; simp at hr; cases r <;> simp_all [bkHK.res, rv_simp] <;> rfl)
    | (intro A _ _; simp [bkHK.res, rv_simp])

/-- 653..654 (HB, test): `t5 = t4 & 1; beq t5, zero`. -/
theorem kgHB1_spec (s : MachineState) (hpc : s.pc = pcOf 653) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if (s.getReg .x29 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = true then pcOf 658 else pcOf 655) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkHB1 codeAt_kgHB1 s hpc (by simp [bkHB1.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkHB1.res, E.eval, CmpOp.eval, RegFile.get, BinOp.eval]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [bkHB1.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkHB1.res, rv_simp]

/-- 655..657 (HB, add): `a6 ^= a4; s8 ^= a5; tp ^= a2`. -/
theorem kgHB2_spec (s : MachineState) (hpc : s.pc = pcOf 655) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 658 ∧ t.getReg .x16 = s.getReg .x16 ^^^ s.getReg .x14 ∧
      t.getReg .x24 = s.getReg .x24 ^^^ s.getReg .x15 ∧ t.getReg .x4 = s.getReg .x4 ^^^ s.getReg .x12 ∧
      RegsExcept s t [.x4, .x16, .x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkHB2 codeAt_kgHB2 s hpc (by simp [bkHB2.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bkHB2.res, Result.toState_pc, E.eval]
  all_goals first
    | (simp only [Result.toState_getReg, bkHB2.res, RegFile.get, E.eval, BinOp.eval]; done)
    | (intro r hr; simp at hr; cases r <;> simp_all [bkHB2.res, rv_simp] <;> rfl)
    | (intro A _ _; simp [bkHB2.res, rv_simp])

/-- 658..666 (HB, shift): shift the multiplicand limbs `(a4, a5, a2)` and `t4`; loop while `t4 >> 1 ≠ 0`. -/
theorem kgHB3_spec (s : MachineState) (hpc : s.pc = pcOf 658) :
    ∃ t, Steps image s 9 9 t ∧
      t.pc = (if (s.getReg .x29 >>> 1 != BitVec.ofNat 64 0) = true then pcOf 653 else pcOf 667) ∧
      t.getReg .x14 = s.getReg .x14 <<< 1 ∧ t.getReg .x15 = (s.getReg .x15 <<< 1) ||| (s.getReg .x14 >>> 63) ∧
      t.getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x15 >>> 63) ∧ t.getReg .x29 = s.getReg .x29 >>> 1 ∧
      RegsExcept s t [.x12, .x14, .x15, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkHB3 codeAt_kgHB3 s hpc (by simp [bkHB3.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkHB3.res, E.eval, CmpOp.eval, RegFile.get,
      kshr _ 1 (by norm_num)]
  all_goals first
    | (simp only [Result.toState_getReg, bkHB3.res, RegFile.get, E.eval, BinOp.eval.eq_4,
        kshl _ 1 (by norm_num), kshr _ 1 (by norm_num), kshr _ 63 (by norm_num)]; done)
    | (intro r hr; simp at hr; cases r <;> simp_all [bkHB3.res, rv_simp] <;> rfl)
    | (intro A _ _; simp [bkHB3.res, rv_simp])

/-- 667..678 (HF): fold `tp` into `a6` with 0x87, add the coefficient at `a0`; loop while `a0 ≠ a1`. -/
theorem kgHF_spec (s : MachineState) (hpc : s.pc = pcOf 667) {A : Nat} (h10 : s.getReg .x10 = BitVec.ofNat 64 A)
    (hA : A % 8 = 0) (hA' : A + 16 ≤ 2 ^ 24) :
    ∃ t, Steps image s 12 12 t ∧
      t.pc = (if (s.getReg .x10 != s.getReg .x11) = true then pcOf 647 else pcOf 679) ∧
      t.getReg .x14 = foldLo (s.getReg .x16) (s.getReg .x4) ^^^ s.getMem (BitVec.ofNat 64 A) ∧
      t.getReg .x15 = s.getReg .x24 ^^^ s.getMem (BitVec.ofNat 64 (A + 8)) ∧
      RegsExcept s t [.x14, .x15, .x16, .x30] ∧ Frame s t (fun _ => False) := by
  have hobl : Oblig.all s bkHF.res.st.obl := by
    simp only [bkHF.res]
    t3n [h10]
    omega
  refine ⟨_, symRun_sound bkHF codeAt_kgHF s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkHF.res, E.eval, CmpOp.eval, RegFile.get]; rfl
  · simp only [Result.toState_getReg, bkHF.res, RegFile.get, E.eval, h10, foldLo,
      kshl _ 1 (by norm_num), kshl _ 2 (by norm_num), kshl _ 7 (by norm_num)]
    rfl
  · simp only [Result.toState_getReg, bkHF.res, RegFile.get, E.eval, h10, BinOp.eval, ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [bkHF.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkHF.res, rv_simp]

/-- 679..682 (HE): store the seed at `CHAIN + 48`, return. -/
theorem kgHE_spec (s : MachineState) (hpc : s.pc = pcOf 679) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf ret ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 48)) = s.getReg .x14 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 56)) = s.getReg .x15 ∧ RegsExcept s t [.x30] ∧
      Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  refine ⟨_, symRun_sound bkHE codeAt_kgHE s hpc (by simp [bkHE.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkHE.res, rv_simp, h1, pcOf_and_max]
  · simp only [Result.toState_getMem, bkHE.res, CHAIN]; t3n []
  · simp only [Result.toState_getMem, bkHE.res, CHAIN]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [bkHE.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [CHAIN] at hn
    simp only [Result.toState_getMem, bkHE.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

/-! ## HORN loops -/
/-- Registers of the bit loop. -/
def khbRegs : List Reg := [.x4, .x12, .x14, .x15, .x16, .x24, .x29, .x30]

theorem kgHB_spec (s : MachineState) (hpc : s.pc = pcOf 653) (b1 b2 : Bool)
    (h1 : (s.getReg .x29 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = b1)
    (h2 : (s.getReg .x29 >>> 1 != BitVec.ofNat 64 0) = b2) :
    ∃ t, Steps image s (if b1 then 11 else 14) (if b1 then 11 else 14) t ∧
      t.pc = (if b2 then pcOf 653 else pcOf 667) ∧
      t.getReg .x14 = s.getReg .x14 <<< 1 ∧ t.getReg .x15 = (s.getReg .x15 <<< 1) ||| (s.getReg .x14 >>> 63) ∧
      t.getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x15 >>> 63) ∧
      t.getReg .x16 = (if b1 then s.getReg .x16 else s.getReg .x16 ^^^ s.getReg .x14) ∧
      t.getReg .x24 = (if b1 then s.getReg .x24 else s.getReg .x24 ^^^ s.getReg .x15) ∧
      t.getReg .x4 = (if b1 then s.getReg .x4 else s.getReg .x4 ^^^ s.getReg .x12) ∧
      t.getReg .x29 = s.getReg .x29 >>> 1 ∧ RegsExcept s t khbRegs ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := kgHB1_spec s hpc
  rw [h1] at t1pc
  obtain ⟨t2, st2, t2pc, t2x16, t2x24, t2x4, t2r, t2f⟩ : ∃ t2, Steps image t1 (if b1 then 0 else 3)
      (if b1 then 0 else 3) t2 ∧ t2.pc = pcOf 658 ∧
      t2.getReg .x16 = (if b1 then s.getReg .x16 else s.getReg .x16 ^^^ s.getReg .x14) ∧
      t2.getReg .x24 = (if b1 then s.getReg .x24 else s.getReg .x24 ^^^ s.getReg .x15) ∧
      t2.getReg .x4 = (if b1 then s.getReg .x4 else s.getReg .x4 ^^^ s.getReg .x12) ∧
      RegsExcept t1 t2 [.x4, .x16, .x24] ∧ Frame t1 t2 (fun _ => False) := by
    cases b1
    · simp only [Bool.false_eq_true, if_false] at t1pc ⊢
      obtain ⟨t2, st2, t2pc, a, b, c, r, f⟩ := kgHB2_spec t1 t1pc
      refine ⟨t2, st2, t2pc, ?_, ?_, ?_, r, f⟩
      · rw [a, t1r.get (by simp), t1r.get (by simp)]
      · rw [b, t1r.get (by simp), t1r.get (by simp)]
      · rw [c, t1r.get (by simp), t1r.get (by simp)]
    · simp only [if_true] at t1pc ⊢
      exact ⟨t1, Steps.refl _, t1pc, t1r.get (by simp), t1r.get (by simp), t1r.get (by simp), RegsExcept.refl _ _,
        Frame.refl _ _⟩
  obtain ⟨t3, st3, t3pc, t3x14, t3x15, t3x12, t3x29, t3r, t3f⟩ := kgHB3_spec t2 t2pc
  have e : ∀ r, r ∉ [Reg.x30, .x4, .x16, .x24] → t2.getReg r = s.getReg r := fun r hr =>
    ((t1r.trans t2r).mono (by simp)).get hr
  refine ⟨t3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ((t1r.trans t2r).trans t3r).mono (by simp [khbRegs]),
    ((t1f.trans t2f).trans t3f).mono (fun _ _ h => by simp_all)⟩
  · exact Steps.of_eq (st1.trans (st2.trans st3)) (by cases b1 <;> rfl) (by cases b1 <;> rfl)
  · rw [t3pc, e _ (by simp), h2]
  · rw [t3x14, e _ (by simp)]
  · rw [t3x15, e _ (by simp), e _ (by simp)]
  · rw [t3x12, e _ (by simp), e _ (by simp)]
  · rw [t3r.get (by simp), t2x16]
  · rw [t3r.get (by simp), t2x24]
  · rw [t3r.get (by simp), t2x4]
  · rw [t3x29, e _ (by simp)]

/-- Steps of the bit loop over the remaining bits `q` (fuel `n`): 11 per zero bit, 14 per one bit. -/
def hbCost : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, q => (if q % 2 = 0 then 11 else 14) + (if q / 2 = 0 then 0 else hbCost n (q / 2))

structure KHbSt (t0 : MachineState) (d a k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 653
  sh : lim3 (t.getReg .x14) (t.getReg .x15) (t.getReg .x12) = a * 2 ^ k
  pr : lim3 (t.getReg .x16) (t.getReg .x24) (t.getReg .x4) = clmulSmall a d k
  dd : t.getReg .x29 = BitVec.ofNat 64 (d / 2 ^ k)
  regs : RegsExcept t0 t khbRegs
  frame : Frame t0 t (fun _ => False)

structure KHfSt (t0 : MachineState) (d a : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 667
  pr : lim3 (t.getReg .x16) (t.getReg .x24) (t.getReg .x4) = clmulSmall a d 10
  regs : RegsExcept t0 t khbRegs
  frame : Frame t0 t (fun _ => False)

theorem klim3_ite (b : Bool) (a0 a1 a2 x0 x1 x2 : BitVec 64) :
    lim3 (if b then a0 else a0 ^^^ x0) (if b then a1 else a1 ^^^ x1) (if b then a2 else a2 ^^^ x2) =
      if b then lim3 a0 a1 a2 else lim3 a0 a1 a2 ^^^ lim3 x0 x1 x2 := by
  cases b
  · simp only [Bool.false_eq_true, if_false]; exact lim3_xor ..
  · rfl

theorem kb1 (q : Nat) : (BitVec.ofNat 64 q &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = decide (q % 2 = 0) := by
  rw [show BitVec.ofNat 64 1 = 1#64 from rfl, ofNat_and1]
  have h2 : q % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> rw [h] <;> decide

theorem kb2 (q : Nat) (hq : q < 2 ^ 64) :
    (BitVec.ofNat 64 q >>> 1 != BitVec.ofNat 64 0) = decide (q / 2 ≠ 0) := by
  rw [ofNat_shr q 1 hq, pow_one]
  have h := ofNat_inj (x := q / 2) (y := 0) (by omega) (by norm_num)
  by_cases hz : q / 2 = 0
  · rw [hz]; rfl
  · simp only [bne_iff_ne, ne_eq, h, hz, not_false_eq_true, decide_true]

theorem khb_loop {t0 : MachineState} {d a : Nat} (ha : a < 2 ^ 128) (hd : d < 2 ^ 10) :
    ∀ n k, k + n = 10 → (k = 0 ∨ 2 ^ k ≤ d) → ∀ t, KHbSt t0 d a k t →
      ∃ u, Steps image t (hbCost n (d / 2 ^ k)) (hbCost n (d / 2 ^ k)) u ∧ KHfSt t0 d a u := by
  intro n
  induction n with
  | zero =>
    intro k hk hk0 t _
    exfalso
    rcases hk0 with h | h
    · omega
    · have : k = 10 := by omega
      subst this; omega
  | succ n ih =>
    intro k hk hk0 t ht
    have hk9 : k ≤ 9 := by omega
    have hp9 : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk9
    have hdk : d / 2 ^ k < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have hq2 : d / 2 ^ k / 2 = d / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    obtain ⟨u, su, upc, u14, u15, u12, u16, u24, u4, u29, uregs, uframe⟩ :=
      kgHB_spec t ht.pc _ _ rfl rfl
    rw [ht.dd, kb1] at su u16 u24 u4
    rw [ht.dd, kb2 _ hdk] at upc
    have hlt12 : (t.getReg .x12).toNat < 2 ^ 63 := by
      have := lim3_lt (t.getReg .x14) (t.getReg .x15) (t.getReg .x12) (n := 9) (by
        rw [ht.sh, Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_le ha hp9 (Nat.two_pow_pos _))
      omega
    have hbit : decide (d / 2 ^ k % 2 = 0) = !(d.testBit k) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (d / 2 ^ k) with h | h <;> simp [h]
    have hsh : lim3 (u.getReg .x14) (u.getReg .x15) (u.getReg .x12) = a * 2 ^ (k + 1) := by
      rw [u14, u15, u12, lim3_shl1 _ _ _ hlt12, ht.sh, Nat.pow_succ]; ring
    have hpr : lim3 (u.getReg .x16) (u.getReg .x24) (u.getReg .x4) = clmulSmall a d (k + 1) := by
      rw [u16, u24, u4, klim3_ite, hbit, ht.pr, ht.sh]
      rw [← clmul_step a d k _ rfl (d.testBit k) rfl]
      cases d.testBit k <;> rfl
    have hdd : u.getReg .x29 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) := by
      rw [u29, ht.dd, ofNat_shr _ 1 hdk, pow_one, hq2]
    have hregs : RegsExcept t0 u khbRegs := (ht.regs.trans uregs).mono (by simp [khbRegs])
    have hframe : Frame t0 u (fun _ => False) := (ht.frame.trans uframe).mono (fun _ _ h => by simpa using h)
    have hcost : ∀ (c : Nat), hbCost (n + 1) (d / 2 ^ k) =
        (if decide (d / 2 ^ k % 2 = 0) = true then 11 else 14) +
          (if d / 2 ^ (k + 1) = 0 then 0 else hbCost n (d / 2 ^ (k + 1))) := by
      intro _; simp only [hbCost, decide_eq_true_eq, hq2]
    by_cases hz : d / 2 ^ (k + 1) = 0
    · have hdlt : d < 2 ^ (k + 1) := by
        by_contra hc
        have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos (k + 1))
        omega
      rw [hq2, hz] at upc
      refine ⟨u, Steps.of_eq su (by rw [hcost 0, hz]; simp) (by rw [hcost 0, hz]; simp),
        ⟨by rw [upc]; rfl, ?_, hregs, hframe⟩⟩
      rw [hpr, clmulSmall_stable a hdlt 10 (by omega)]
    · have hge : 2 ^ (k + 1) ≤ d := by
        by_contra hc
        exact hz (Nat.div_eq_of_lt (Nat.lt_of_not_le hc))
      rw [hq2] at upc
      simp only [ne_eq, hz, not_false_eq_true, decide_true, if_true] at upc
      obtain ⟨v, sv, hv⟩ := ih (k + 1) (by omega) (Or.inr hge) u ⟨upc, hsh, hpr, hdd, hregs, hframe⟩
      refine ⟨v, Steps.of_eq (su.trans sv) ?_ ?_, hv⟩ <;> rw [hcost 0, if_neg hz]

/-- Steps of one Horner step (HK, bit loop, HF). -/
def hornStepK (d : Nat) : Nat := 18 + hbCost 10 d
/-- Steps (= cycles) of HORN at the point `d`. -/
def hornK (d : Nat) : Nat := 13 + 31 * hornStepK d

/-- Registers HORN may change. -/
def khornRegs : List Reg := [.x4, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x24, .x29, .x30]

structure KHkSt (s0 : MachineState) (d : Nat) (coefs : List Digest) (m : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 647
  x13 : t.getReg .x13 = BitVec.ofNat 64 d
  x10 : t.getReg .x10 = BitVec.ofNat 64 (KCOEF + 16 * m)
  x11 : t.getReg .x11 = BitVec.ofNat 64 KCOEF
  acc : lim2 (t.getReg .x14) (t.getReg .x15) = (familyEval (coefs.drop m) d).toNat
  regs : RegsExcept s0 t khornRegs
  frame : Frame s0 t (fun _ => False)

theorem kfamilyEval_drop (coefs : List Digest) (m : Nat) (hm : m < coefs.length) (d : Nat) :
    familyEval (coefs.drop m) d = gfMulPt (familyEval (coefs.drop (m + 1)) d) d ^^^ coefs.getD m 0 := by
  rw [List.drop_eq_getElem_cons hm, familyEval_cons, List.getD_eq_getElem _ _ hm]

theorem kcoef_limbs {s0 u : MachineState} {coefs : List Digest} (hcoef : DigsAt s0 KCOEF coefs)
    (hf : Frame s0 u (fun _ => False)) {m : Nat} (hm : m < coefs.length) (hl : coefs.length ≤ 40) :
    lim2 (u.getMem (BitVec.ofNat 64 (KCOEF + 16 * m))) (u.getMem (BitVec.ofNat 64 (KCOEF + 16 * m + 8))) =
      (coefs.getD m 0).toNat := by
  have h := hcoef m hm
  rw [hf.get (by simp only [KCOEF]; omega) id, hf.get (by simp only [KCOEF]; omega) id, h.1, h.2, lim2_toNat]

theorem lim3_zero_hi' (a b : BitVec 64) : lim3 a b (BitVec.ofNat 64 0) = lim2 a b := by
  unfold lim3 lim2; simp

/-- One Horner step: HK, the bit loop and HF. -/
theorem khorner_step {s0 : MachineState} {d : Nat} {coefs : List Digest} (hd : d < 2 ^ 10)
    (hlen : coefs.length = 31) (hcoef : DigsAt s0 KCOEF coefs) {m : Nat} (hm : m < 31) {t : MachineState}
    (ht : KHkSt s0 d coefs (m + 1) t) :
    ∃ v, Steps image t (hornStepK d) (hornStepK d) v ∧ v.pc = (if m = 0 then pcOf 679 else pcOf 647) ∧
      v.getReg .x13 = BitVec.ofNat 64 d ∧ v.getReg .x10 = BitVec.ofNat 64 (KCOEF + 16 * m) ∧
      v.getReg .x11 = BitVec.ofNat 64 KCOEF ∧
      lim2 (v.getReg .x14) (v.getReg .x15) = (familyEval (coefs.drop m) d).toNat ∧
      RegsExcept s0 v khornRegs ∧ Frame s0 v (fun _ => False) := by
  obtain ⟨t1, st1, p1, x10, x4, x12, x16, x24, x29, r1, f1⟩ :=
    kgHK_spec t ht.pc (m + 1) (by omega) (by omega) ht.x10
  rw [Nat.add_sub_cancel] at x10
  have h0 : KHbSt t1 d (familyEval (coefs.drop (m + 1)) d).toNat 0 t1 := by
    refine ⟨p1, ?_, ?_, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [x12, lim3_zero_hi', r1.get (by simp), r1.get (by simp), ht.acc]; simp
    · rw [x16, x24, x4]; unfold lim3; simp [clmulSmall]
    · rw [x29, ht.x13]; simp
  obtain ⟨u, su, hu⟩ := khb_loop (BitVec.isLt _) hd 10 0 (by norm_num) (Or.inl rfl) t1 h0
  have u10 : u.getReg .x10 = BitVec.ofNat 64 (KCOEF + 16 * m) := by rw [hu.regs.get (by simp [khbRegs]), x10]
  have u11 : u.getReg .x11 = BitVec.ofNat 64 KCOEF := by
    rw [hu.regs.get (by simp [khbRegs]), r1.get (by simp), ht.x11]
  obtain ⟨v, sv, vpc, v14, v15, vr, vf⟩ := kgHF_spec u hu.pc u10 (by simp only [KCOEF]; omega)
    (by simp only [KCOEF]; omega)
  have fu : Frame s0 u (fun _ => False) :=
    ((ht.frame.trans f1).trans hu.frame).mono (fun _ _ h => by simp_all)
  have hl := horner_limbs hu.pr (kcoef_limbs hcoef fu (m := m) (by omega) (by omega))
  rw [← kfamilyEval_drop coefs m (by omega)] at hl
  refine ⟨v, Steps.of_eq (st1.trans (su.trans sv)) (by simp [hornStepK]; omega) (by simp [hornStepK]; omega),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vpc, u10, u11]
    by_cases h : m = 0
    · subst h; simp
    · rw [if_neg h]
      have : BitVec.ofNat 64 (KCOEF + 16 * m) ≠ BitVec.ofNat 64 KCOEF := by
        rw [Ne, ofNat_inj (by simp only [KCOEF]; omega) (by simp only [KCOEF]; omega)]; omega
      simp [this]
  · rw [vr.get (by simp), hu.regs.get (by simp [khbRegs]), r1.get (by simp), ht.x13]
  · rw [vr.get (by simp), u10]
  · rw [vr.get (by simp), u11]
  · rw [v14, v15]; exact hl
  · exact (((ht.regs.trans r1).trans hu.regs).trans vr).mono (by simp [khornRegs, khbRegs])
  · exact (fu.trans vf).mono (fun _ _ h => by simp_all)

theorem khorner_loop {s0 : MachineState} {d : Nat} {coefs : List Digest} (hd : d < 2 ^ 10)
    (hlen : coefs.length = 31) (hcoef : DigsAt s0 KCOEF coefs) {ret : Nat} (h1 : s0.getReg .x1 = pcOf ret) :
    ∀ m, m < 31 → ∀ t, KHkSt s0 d coefs (m + 1) t →
      ∃ u, Steps image t ((m + 1) * hornStepK d + 4) ((m + 1) * hornStepK d + 4) u ∧ u.pc = pcOf ret ∧
        DigAt u (CHAIN + 48) (familyEval coefs d) ∧ RegsExcept s0 u khornRegs ∧
        Frame s0 u (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  intro m
  induction m with
  | zero =>
    intro hm t ht
    obtain ⟨v, sv, vpc, -, -, -, vacc, vr, vf⟩ := khorner_step hd hlen hcoef hm ht
    rw [if_pos rfl] at vpc
    obtain ⟨w, sw, wpc, w48, w56, wr, wf⟩ := kgHE_spec v vpc ret (by rw [vr.get (by simp [khornRegs]), h1])
    rw [List.drop_zero] at vacc
    obtain ⟨l0, l1⟩ := limbs_of_lim2 vacc
    refine ⟨w, Steps.of_eq (sv.trans sw) (by ring) (by ring), wpc, ⟨by rw [w48, l0], by rw [w56, l1]⟩,
      (vr.trans wr).mono (by simp [khornRegs]), (vf.trans wf).mono (fun _ _ h => by simp_all)⟩
  | succ m ih =>
    intro hm t ht
    obtain ⟨v, sv, vpc, v13, v10, v11, vacc, vr, vf⟩ := khorner_step hd hlen hcoef hm ht
    rw [if_neg (by omega)] at vpc
    obtain ⟨w, sw, hw⟩ := ih (by omega) v ⟨vpc, v13, v10, v11, vacc, vr, vf⟩
    exact ⟨w, Steps.of_eq (sv.trans sw) (by ring) (by ring), hw⟩

/-- HORN from its entry 642 (img-v6: `jal 1169`, KHORN sets the point `topPoint leaf i = (leaf % 4) · 64 + i + 1`):
`topSeed coefs leaf i` (31 coefficients at KCOEF) into `CHAIN + 48`, return to `x1`. -/
theorem khorn_run (s : MachineState) (hpc : s.pc = pcOf 642) {i leaf : Nat} (hi : i < 64)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 (i + 1)) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    {coefs : List Digest} (hlen : coefs.length = 31)
    (hcoef : DigsAt s KCOEF coefs) {ret : Nat} (h1 : s.getReg .x1 = pcOf ret) :
    ∃ u, Steps image s (hornK (topPoint leaf i)) (hornK (topPoint leaf i)) u ∧ u.pc = pcOf ret ∧
      DigAt u (CHAIN + 48) (topSeed coefs leaf i) ∧
      RegsExcept s u khornRegs ∧ Frame s u (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  obtain ⟨t0, st0, t0pc, t0r, t0f⟩ := kgH0_spec s hpc
  obtain ⟨t, st, tpc, t13, t10, t11, t14, t15, tr, tf⟩ := khA_spec t0 t0pc leaf (i + 1) (by omega)
    (by rw [t0r.get (by simp)]; exact h18) (by rw [t0r.get (by simp)]; exact h13)
  have hd : topPoint leaf i < 2 ^ 10 := by unfold topPoint; omega
  have hcoef0 : DigsAt s KCOEF coefs := hcoef
  have ht : KHkSt s (topPoint leaf i) coefs (30 + 1) t := by
    refine ⟨tpc, by rw [t13]; unfold topPoint; congr 1; omega, t10, t11, ?_, (t0r.trans tr).mono
      (by simp [khornRegs]), (t0f.trans tf).mono (fun _ _ h => by simp_all)⟩
    rw [t14, t15, List.drop_eq_nil_of_le (by omega)]
    rfl
  obtain ⟨u, su, upc, ud, ur, uf⟩ := khorner_loop hd hlen hcoef0 h1 30 (by norm_num) t ht
  exact ⟨u, Steps.of_eq (st0.trans (st.trans su)) (by unfold hornK; ring) (by unfold hornK; ring), upc, ud, ur,
    uf⟩

/-! ## COEFGEN loop -/
/-- The secret-key words of the private block at 0x20000 (and `t0 = 0`), as the private-pair queries need them. -/
structure KPriv (sk : BitVec 256) (s : MachineState) : Prop where
  x5 : s.getReg .x5 = 0
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0

/-- Registers COEFGEN may change (besides `s3`). -/
def cgRegs : List Reg := [.x4, .x10, .x11, .x12, .x14, .x24, .x29, .x30]
/-- Memory COEFGEN may change (img-v6: the 40 coefficient slots, 640 bytes). -/
def CgW (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ (KCOEF ≤ X ∧ X < KCOEF + 640)

/-- img-v6 pair loop (618..638) at counter `j` (pairs `first + j`), `odd` = whether the carry occupies slot 0. -/
structure CgInv (s0 : MachineState) (first odd j : Nat) (acc : List Digest) (t : MachineState) : Prop where
  pc : t.pc = (if j < 16 then pcOf 618 else pcOf 639)
  x14 : t.getReg .x14 = BitVec.ofNat 64 (1 + 2 ^ 32 * (first + j))
  x24 : t.getReg .x24 = BitVec.ofNat 64 (KCOEF + 16 * acc.length)
  x29 : t.getReg .x29 = BitVec.ofNat 64 j
  len : acc.length + odd = 2 * j
  coefs : DigsAt t KCOEF acc
  regs : RegsExcept s0 t cgRegs
  frame : Frame s0 t CgW

theorem kcg_body (sk : BitVec 256) {s0 : MachineState} (hp : KPriv sk s0) {first odd : Nat}
    (hfirst : first + 16 < 2 ^ 32) {j : Nat} (hj : j < 16) (acc : List Digest) (t : MachineState)
    (ht : CgInv s0 first odd j acc t) :
    TSim image sk t 21 28 1 1 (do let p ← topSeedPair (first + j); pure (acc ++ [p.1, p.2]))
      (CgInv s0 first odd (j + 1)) := by
  have tpc : t.pc = pcOf 618 := by rw [ht.pc, if_pos hj]
  have hlen := ht.len
  obtain ⟨t1, st1, t1pc, t10, t11, t12, t1a, t1b, t1r, t1f⟩ := kgCG1_spec t tpc
  have hpos : first + j < 2 ^ 32 := by omega
  have t1a' : t1.getMem (BitVec.ofNat 64 (PRIV + 16)) = BitVec.ofNat 64 (hdr0 0 0 0 (first + j)) := by
    rw [t1a, ht.x14, hdr0_eq 0 0 0 _ (by norm_num) (by norm_num) (by norm_num) hpos]
  have t1b' : t1.getMem (BitVec.ofNat 64 (PRIV + 24)) = BitVec.ofNat 64 (hdr1 0 0) := by
    rw [t1b, hdr1_eq 0 0 (by norm_num) (by norm_num)]; rfl
  have fr : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → t1.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := by
    intro X hX
    have hX' : X < 2 ^ 64 := by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide)
    rw [t1f.get hX' (by simp only [PRIV] at hX ⊢; omega),
      ht.frame.get hX' (by unfold CgW; simp only [PRIV, SEEDS, KCOEF] at hX ⊢; omega)]
  have hq : hashInput t1 = toQ (privateInput sk (.inl (header 0 0 0 (first + j) 0))) := by
    refine hashInput_toQ t1 _ 0 PRIV (privateInput_tweak_length _ _) t10 (by decide) (by decide) t11
      (by decide) ?_
    rw [wordsOf_privateInput_tweak, header_lo, header_hi, readWords_eight, fr PRIV (by simp),
      fr (PRIV + 8) (by simp), t1a', t1b', fr (PRIV + 32) (by simp), fr (PRIV + 40) (by simp),
      fr (PRIV + 48) (by simp), fr (PRIV + 56) (by simp), hp.p0, hp.p8, hp.p32, hp.p40, hp.p48, hp.p56]
    rfl
  have hv : hashArgumentsValid t1 = true :=
    hashArgs_const t1 PRIV 64 SEEDS t10 t11 t12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 : t1.getReg .x5 = 0 := by rw [t1r.get (by simp), ht.regs.get (by simp [cgRegs]), hp.x5]
  refine (TSim.steps st1 (TSim.privatePair_bind (k := 15) (c := 15) (n := 0) (b := 0)
    (fetch_kg623 t1 t1pc) h5 hv hq (fun a => ?_))).of_eq rfl rfl rfl rfl rfl
  have hwf := Frame.writeHash t1 a SEEDS t12 (by decide)
  have hlo := DigAt.writeHash_lo t1 a SEEDS t12 (by decide)
  have hhi := DigAt.writeHash_hi t1 a SEEDS t12 (by decide)
  obtain ⟨u, su, upc, u14, u24, u29, umem, ur, uf⟩ := kgCG2_spec (writeHash t1 a)
    (by rw [pc_writeHash, t1pc, pcOf_add4]) j _ (16 * acc.length) hj (by omega) (by omega) (by rw [getReg_writeHash, t10])
    (by rw [getReg_writeHash, t1r.get (by simp), ht.x24]) (by rw [getReg_writeHash, t1r.get (by simp), ht.x29])
    (by rw [getReg_writeHash, t1r.get (by simp), ht.x14])
  have ftu : Frame t u (fun X => (X = PRIV + 16 ∨ X = PRIV + 24) ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨
      (KCOEF + 16 * acc.length ≤ X ∧ X < KCOEF + 16 * acc.length + 32)) :=
    (t1f.trans (hwf.trans uf)).mono (fun _ _ h => h)
  refine TSim.pure_steps su ⟨?_, ?_, ?_, u29, ?_, ?_, ?_, ?_⟩
  · rw [upc]
  · rw [u14, show 1 + 2 ^ 32 * (first + j) + 2 ^ 32 = 1 + 2 ^ 32 * (first + (j + 1)) by ring]
  · rw [u24]; simp only [List.length_append, List.length_cons, List.length_nil]; (try congr 1); (try ring)
  · simp; omega
  · have hold : DigsAt u KCOEF acc := ht.coefs.frame ftu (by simp only [KCOEF]; omega)
      (fun X h1 h2 h => by simp only [PRIV, SEEDS, KCOEF] at h h1 h2; omega)
    have hd1 : DigAt u (KCOEF + 16 * acc.length) (a.extractLsb' 0 128) := by
      rw [show KCOEF + 16 * acc.length = KCOEF + 16 * acc.length + 8 * 0 by ring]
      refine ⟨by rw [umem 0 (by norm_num)]; exact hlo.1, ?_⟩
      rw [show KCOEF + 16 * acc.length + 8 * 0 + 8 = KCOEF + 16 * acc.length + 8 * 1 by ring, umem 1 (by norm_num)]
      exact hlo.2
    have hd2 : DigAt u (KCOEF + 16 * (acc ++ [a.extractLsb' 0 128]).length) (a.extractLsb' 128 128) := by
      rw [List.length_append, List.length_singleton,
        show KCOEF + 16 * (acc.length + 1) = KCOEF + 16 * acc.length + 8 * 2 by ring]
      refine ⟨by rw [umem 2 (by norm_num)]; exact hhi.1, ?_⟩
      rw [show KCOEF + 16 * acc.length + 8 * 2 + 8 = KCOEF + 16 * acc.length + 8 * 3 by ring, umem 3 (by norm_num),
        show SEEDS + 8 * 3 = SEEDS + 16 + 8 by rfl]
      exact hhi.2
    have := (hold.snoc hd1).snoc hd2
    simpa using this
  · have hw0 : RegsExcept t1 (writeHash t1 a) [] := fun r _ => getReg_writeHash t1 a r
    exact (ht.regs.trans ((t1r.trans hw0).trans ur)).mono (by simp [cgRegs])
  · refine (ht.frame.trans ftu).mono (fun X _ h => ?_)
    unfold CgW at *
    rcases h with h | (h | h) | h | h
    · exact h
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; simp only [KCOEF] at h ⊢; omega

theorem DigsAt.take' {t : MachineState} {A : Nat} {ds : List Digest} (h : DigsAt t A ds) (n : Nat) :
    DigsAt t A (ds.take n) := fun i hi => by
  simp only [List.length_take] at hi
  have := h i (by omega)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_take, show i < n by omega] using this

/-- img-v6: the keygen coefficient buffer before top leaf `leaf` (state `cc = (coefficients, carry)`): inside a family
the family's 31 coefficients at KCOEF; the carry at slot 31 whenever the next family start is odd. -/
def KcPre (s : MachineState) (leaf : Nat) (cc : List Digest × Digest) : Prop :=
  (leaf % 4 ≠ 0 → cc.1.length = 31 ∧ DigsAt s KCOEF cc.1) ∧
    ((leaf + 3) / 4 % 2 = 1 → DigAt s (KCOEF + 496) cc.2)
/-- img-v6: the coefficient buffer after KTOP for leaf `leaf` (and after the leaf). -/
def KcPost (s : MachineState) (leaf : Nat) (cc : List Digest × Digest) : Prop :=
  cc.1.length = 31 ∧ DigsAt s KCOEF cc.1 ∧ ((leaf + 4) / 4 % 2 = 1 → DigAt s (KCOEF + 496) cc.2)

theorem KcPre.frame {s t : MachineState} {W : Nat → Prop} {leaf : Nat} {cc : List Digest × Digest}
    (h : KcPre s leaf cc) (hf : Frame s t W) (hW : ∀ X, KCOEF ≤ X → X < KCOEF + 640 → ¬ W X) :
    KcPre t leaf cc :=
  ⟨fun h0 => ⟨(h.1 h0).1, (h.1 h0).2.frame hf (by rw [(h.1 h0).1]; simp only [KCOEF]; omega)
      (fun X h1 h2 => hW X h1 (by rw [(h.1 h0).1] at h2; omega))⟩,
    fun h1 => (h.2 h1).frame hf (by simp only [KCOEF]; omega) (hW _ (by omega) (by omega))
      (hW _ (by omega) (by omega))⟩
theorem KcPost.frame {s t : MachineState} {W : Nat → Prop} {leaf : Nat} {cc : List Digest × Digest}
    (h : KcPost s leaf cc) (hf : Frame s t W) (hW : ∀ X, KCOEF ≤ X → X < KCOEF + 640 → ¬ W X) :
    KcPost t leaf cc :=
  ⟨h.1, h.2.1.frame hf (by rw [h.1]; simp only [KCOEF]; omega) (fun X h1 h2 => hW X h1 (by rw [h.1] at h2; omega)),
    fun h1 => (h.2.2 h1).frame hf (by simp only [KCOEF]; omega) (hW _ (by omega) (by omega))
      (hW _ (by omega) (by omega))⟩

/-- Steps of KTOP at a family start (`o = f % 2`): 612, 1149..1160, [1161..1165], 1166, the pair loop, 639..640. -/
def kfK (o : Nat) : Nat := 16 + 5 * o + 21 * (16 - o)
/-- Cycles of KTOP at a family start. -/
def kfC (o : Nat) : Nat := 19 + 5 * o + 28 * (16 - o)

/-- img-v6 KTOP from 612 (called from 157 with `ra = 158`): `topFamilyCoefs leaf cc` into the coefficient buffer,
`s3 = 0`. -/
theorem kfam_tsim (sk : BitVec 256) {s : MachineState} (hpc : s.pc = pcOf 612) {leaf : Nat}
    (hleaf : leaf < 4096) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (hp : KPriv sk s)
    (h1 : s.getReg .x1 = pcOf 158) {cc : List Digest × Digest} (hk : KcPre s leaf cc) :
    TSim image sk s (if leaf % 4 = 0 then kfK (leaf / 4 % 2) else 5) (if leaf % 4 = 0 then kfC (leaf / 4 % 2) else 5)
      (if leaf % 4 = 0 then 16 - leaf / 4 % 2 else 0) (if leaf % 4 = 0 then 16 - leaf / 4 % 2 else 0)
      (topFamilyCoefs leaf cc)
      (fun cc' t => t.pc = pcOf 158 ∧ KcPost t leaf cc' ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
        RegsExcept s t (cgRegs ++ [.x19]) ∧ Frame s t CgW) := by
  obtain ⟨t0, st0, t0pc, t0r, t0f⟩ := kg612_spec s hpc
  obtain ⟨tA, stA, tApc, tAr, tAf⟩ := kfA_spec t0 t0pc leaf (by rw [t0r.get (by simp)]; exact h18)
  have r0A : RegsExcept s tA ([] ++ [.x30]) := t0r.trans tAr
  have f0A : Frame s tA (fun _ => False) := (t0f.trans tAf).mono (fun _ _ h => by simp_all)
  unfold topFamilyCoefs
  by_cases h0 : leaf % 4 = 0
  · rw [if_pos h0] at tApc
    simp only [h0, ↓reduceIte]
    have o2 : leaf / 4 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    obtain ⟨tB, stB, tBpc, tB14, tB24, tB29, tBr, tBf⟩ := kfB_spec tA tApc leaf (by omega)
      (by rw [r0A.get (by simp)]; exact h18)
    -- the state at 618 with the initial accumulator
    obtain ⟨tE, kE, cE, stE, hkE, hcE, ⟨tEpc, tE14, tE24, tE29, tEr, tEf, tEc⟩⟩ : ∃ tE kE cE, Steps image tB kE cE tE ∧
        kE = 1 + 5 * (leaf / 4 % 2) ∧ cE = 1 + 5 * (leaf / 4 % 2) ∧
        (tE.pc = pcOf 618 ∧ tE.getReg .x14 = tB.getReg .x14 ∧
          tE.getReg .x24 = BitVec.ofNat 64 (KCOEF + 16 * (leaf / 4 % 2)) ∧ tE.getReg .x29 = tB.getReg .x29 ∧
          RegsExcept tB tE [.x4, .x24] ∧ Frame tB tE (fun A => A = KCOEF ∨ A = KCOEF + 8) ∧
          DigsAt tE KCOEF (if leaf / 4 % 2 = 0 then [] else [cc.2])) := by
      by_cases ho : leaf / 4 % 2 = 0
      · rw [if_pos ho] at tBpc
        obtain ⟨u, su, upc, ur, uf⟩ := kfE_spec tB tBpc
        refine ⟨u, 1, 1, su, by rw [ho], by rw [ho], upc, ur.get (by simp), ?_, ur.get (by simp),
          ur.mono (by simp), uf.mono (fun _ _ h => h.elim), ?_⟩
        · rw [ur.get (by simp), tB24, ho]
        · rw [if_pos ho]; exact DigsAt.nil _ _
      · rw [if_neg ho] at tBpc
        obtain ⟨u, su, upc, um0, um8, u24, ur, uf⟩ := kfD_spec tB tBpc tB24
        obtain ⟨v, sv, vpc, vr, vf⟩ := kfE_spec u upc
        have hcar : DigAt tB (KCOEF + 496) cc.2 := by
          have := hk.2 (by omega)
          exact this.frame (f0A.trans tBf) (by simp only [KCOEF]; omega) (by simp) (by simp)
        refine ⟨v, 5 + 1, 5 + 1, su.trans sv, by omega, by omega, vpc, ?_, ?_, ?_, (ur.trans vr).mono (by simp),
          (uf.trans vf).mono (fun _ _ h => by simp_all), ?_⟩
        · rw [vr.get (by simp), ur.get (by simp)]
        · rw [vr.get (by simp), u24, show leaf / 4 % 2 = 1 by omega]
        · rw [vr.get (by simp), ur.get (by simp)]
        · rw [if_neg ho]
          intro i hi
          simp only [List.length_singleton] at hi
          have hi0 : i = 0 := by omega
          subst hi0
          refine ⟨?_, ?_⟩
          · rw [show KCOEF + 16 * 0 = KCOEF by rfl, vf.get (by decide) (by simp), um0]; exact hcar.1
          · rw [show KCOEF + 16 * 0 + 8 = KCOEF + 8 by rfl, vf.get (by decide) (by simp), um8]
            exact hcar.2
    have hfirst : 31 * (leaf / 4) / 2 + 16 < 2 ^ 32 := by omega
    have hI : CgInv s (31 * (leaf / 4) / 2) (leaf / 4 % 2) (leaf / 4 % 2 + 0)
        (if leaf / 4 % 2 = 0 then [] else [cc.2]) tE := by
      refine ⟨by rw [tEpc, if_pos (by omega)], by rw [tE14, tB14]; rfl, ?_, by rw [tE29, tB29]; rfl, ?_, tEc, ?_, ?_⟩
      · rw [tE24]; split <;> simp_all
      · split <;> simp_all <;> omega
      · exact ((r0A.trans tBr).trans tEr).mono (by simp [cgRegs])
      · refine ((f0A.trans tBf).trans tEf).mono (fun X _ h => ?_)
        unfold CgW; simp only [KCOEF] at h ⊢
        rcases h with (h | h) | h
        · exact h.elim
        · exact h.elim
        · omega
    have hloop := TSim.foldlM_range' (image := image) (sk := sk) (leaf / 4 % 2) (16 - leaf / 4 % 2)
      (fun acc j => do let p ← topSeedPair (31 * (leaf / 4) / 2 + j); pure (acc ++ [p.1, p.2]))
      (if leaf / 4 % 2 = 0 then [] else [cc.2])
      (fun j acc t => CgInv s (31 * (leaf / 4) / 2) (leaf / 4 % 2) (leaf / 4 % 2 + j) acc t)
      (fun _ => 21) (fun _ => 28) (fun _ => 1) (fun _ => 1)
      (fun j hj acc t ht => kcg_body sk hp hfirst (by omega) acc t ht) hI
    unfold topCoefsK topPairsFrom
    refine (TSim.steps (st0.trans (stA.trans (stB.trans stE))) (TSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0)
      (f := fun acc => pure (acc.take topCoefCount, acc.getD topCoefCount 0))
      hloop (fun acc t ht => ?_))).of_eq rfl ?_ ?_ ?_ ?_
    · have hl := ht.len
      have tpc : t.pc = pcOf 639 := by rw [ht.pc, if_neg (by omega)]
      obtain ⟨u, su, upc, u19, ur, uf⟩ := kgCG3_spec t tpc 158
        (by rw [ht.regs.get (by simp [cgRegs]), h1])
      have hc : DigsAt u KCOEF acc := ht.coefs.frame uf (by simp only [KCOEF]; omega) (fun _ _ _ h => h)
      refine TSim.pure_steps su ⟨upc, ⟨?_, DigsAt.take' hc 31, fun ho => ?_⟩, u19, ht.regs.trans ur,
        (ht.frame.trans uf).mono (fun _ _ h => by simp_all)⟩
      · simp only [List.length_take, topCoefCount]; omega
      · have ho' : leaf / 4 % 2 = 0 := by omega
        have := hc 31 (by omega)
        simpa [topCoefCount] using this
    all_goals simp only [sumTo_const, kfK, kfC]; omega
  · rw [if_neg h0] at tApc
    simp only [h0, ↓reduceIte]
    obtain ⟨u, su, upc, u19, ur, uf⟩ := kfF_spec tA tApc 158 (by rw [r0A.get (by simp)]; exact h1)
    have fsu : Frame s u (fun _ => False) := (f0A.trans uf).mono (fun _ _ h => by simp_all)
    have hk' := hk.frame fsu (fun _ _ _ h => h)
    refine TSim.pure_steps (st0.trans (stA.trans su)) ⟨upc, ⟨(hk'.1 h0).1, (hk'.1 h0).2,
      fun h1 => hk'.2 (by omega)⟩, u19, (r0A.trans ur).mono (by simp [cgRegs]), fsu.mono (fun _ _ h => h.elim)⟩

/-! ## The top leaf -/
macro "tl_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, KCOEF] at *); omega))

/-- Registers the top-leaf routine may change. -/
def tRegs : List Reg := leafRegs ++ [.x4, .x13, .x14, .x15, .x16, .x24]
/-- Memory the top-leaf routine may change: the leaf writes, `end_0`'s slot (campaign T51: `LEAFPK`, below the
tweak) and the coefficient buffer. -/
def TW (A : LeafArgs) (X : Nat) : Prop := LeafW A X ∨ (LEAFPK ≤ X ∧ X < LEAFPK + 16) ∨ (KCOEF ≤ X ∧ X < KCOEF + 640)

/-- Campaign T51 ("endpad"): the slot of chain `c`'s end in the top leaf buffer: `end_0` at `LEAFPK`, the tweak at
`LEAFPK + 16`, `end_c` at `LEAFPK + 16 (c + 1)` (`c ≥ 1`). -/
def tslot (c : Nat) : Nat := if c = 0 then LEAFPK else LEAFPK + 16 * (c + 1)
theorem tslot_eq (c : Nat) : tslot c = LEAFPK + 16 * (c + (if c = 0 then 0 else 1)) := by
  unfold tslot; split_ifs <;> omega
theorem tslot_ge (c : Nat) : LEAFPK ≤ tslot c := by unfold tslot; split_ifs <;> omega
theorem tslot_lt {c n : Nat} (hc : c < n) : tslot c + 16 ≤ LEAFPK + 16 * (n + 1) := by
  unfold tslot; split_ifs <;> omega
theorem tslot_disj {c j : Nat} (h : c ≠ j) : tslot c + 16 ≤ tslot j ∨ tslot j + 16 ≤ tslot c := by
  unfold tslot; split_ifs <;> omega
theorem tslot_hdr (c : Nat) : tslot c + 16 ≤ LEAFPK + 16 ∨ LEAFPK + 32 ≤ tslot c := by
  unfold tslot; split_ifs <;> omega
theorem TW_of_tslot {A : LeafArgs} (h0 : A.lay = 0) {j X : Nat} (hj : j < A.n) (h : tslot j ≤ X ∧ X < tslot j + 16) :
    TW A X := by
  unfold TW LeafW tslot at *
  rw [if_pos h0]
  by_cases hj0 : j = 0
  · rw [if_pos hj0] at h; right; left; omega
  · rw [if_neg hj0] at h; left; right; right; right; right; right; right; left; constructor <;> omega

/-- Campaign T51: the keygen top leaf's precondition (= `LeafPre` without the zero head: `LEAFPK` now holds
`end_0` of the previous leaf). -/
structure TopPre (sk : BitVec 256) (s : MachineState) (A : LeafArgs) : Prop where
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x22 : s.getReg .x22 = BitVec.ofNat 64 A.digp
  x23 : s.getReg .x23 = BitVec.ofNat 64 A.valp
  x25 : s.getReg .x25 = BitVec.ofNat 64 A.dest
  x26 : s.getReg .x26 = BitVec.ofNat 64 A.n
  x27 : s.getReg .x27 = BitVec.ofNat 64 (n4 A.lay)
  x31 : s.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  hroute : A.tree * 2 ^ T3.height A.lay + A.leaf < 2 ^ 31
  hleafHeight : A.leaf < 2 ^ T3.height A.lay
  hsteps : ∀ i < A.n, A.e i ≤ 8
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  z0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  top0 : A.lay = 0 ∧ A.tree = 0
  hdig : ∀ i < A.n, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i)
  hdigb : ∀ i < A.n, A.d i < 256 ∧ (A.so = false → A.d i ≤ maxDigit A.lay i)
  hdigp : A.digp + A.n ≤ 2 ^ 24
  hdigW : ∀ i < A.n, ¬ LeafW A ((A.digp + i) / 8 * 8)
  hv8 : A.valp % 8 = 0
  hv : A.valp + 16 * A.n ≤ 2 ^ 24
  hvs : A.valp + 16 * A.n ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp
  hd8 : A.dest % 8 = 0
  hd : A.dest + 16 ≤ 2 ^ 24
  hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 112 ≤ A.dest ∧ A.dest + 16 ≤ LOUT)
  hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * A.n ≤ A.dest

/-- The keygen top-leaf arguments: signature-free, no digits, buffers clear of KCOEF. -/
structure TopArgs (A : LeafArgs) : Prop where
  so : A.so = false
  dig : A.digits = []
  cv : A.valp + 16 * A.n ≤ KCOEF ∨ KCOEF + 640 ≤ A.valp
  cd : A.dest + 16 ≤ KCOEF ∨ KCOEF + 640 ≤ A.dest
  cdig : A.digp + A.n ≤ KCOEF ∨ KCOEF + 640 ≤ A.digp
  /-- Campaign T51: the digits are clear of `end_0`'s slot. -/
  cdigL : A.digp + A.n ≤ LEAFPK ∨ LEAFPK + 16 ≤ A.digp

structure TInv (s0 : MachineState) (A : LeafArgs) (coefs extra : List Digest) (j : Nat) (st : List Digest × List Digest)
    (t : MachineState) : Prop where
  x19 : t.getReg .x19 = BitVec.ofNat 64 j
  x23 : t.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * j)
  x3 : t.getReg .x3 = pcOf A.ret
  regs : RegsExcept s0 t tRegs
  frame : Frame s0 t (TW A)
  lh16 : t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord A.lay.val (A.tree * 2 ^ T3.height A.lay + A.leaf)
  lh24 : t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0
  elen : st.1.length = j
  vlen : st.2.length = j
  ends : ∀ c < j, DigAt t (tslot c) (st.1.getD c 0)
  vals : DigsAt t A.valp st.2
  coef : DigsAt t KCOEF coefs
  ext : DigsAt t (KCOEF + 496) extra

/-- Registers changed between the loop head and the chain routine's return. -/
def preRegs : List Reg :=
  [.x1, .x4, .x6, .x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x20, .x21, .x24, .x28, .x29, .x30]

section top
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : TopPre sk s0 A) (hta : TopArgs A)
  {coefs extra : List Digest} (hcl : coefs.length = 31) (hel : extra.length ≤ 1)
include hpre hta hcl hel

theorem ktop_post {j : Nat} (hj : j < A.n) {st : List Digest × List Digest} {t u : MachineState}
    (ht : TInv s0 A coefs extra j st t) (hupc : u.pc = pcOf 196) (hur : RegsExcept t u preRegs)
    (huf : Frame t u (fun X => (X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X))
    (v last : Digest) (hv : DigAt u (A.valp + 16 * j) v) (hl : DigAt u (CHAIN + 48) last) :
    ∃ w, Steps image u 16 16 w ∧ w.pc = pcOf 158 ∧ TInv s0 A coefs extra (j + 1) (st.1 ++ [last], st.2 ++ [v]) w := by
  have hn : A.n = 51 := by show chainCount A.lay = 51; rw [hpre.top0.1]; rfl
  have h0 := hpre.top0.1
  have hvs := hpre.hvs
  have hvb := hpre.hv
  have hv8 := hpre.hv8
  have hcv := hta.cv
  have g : ∀ r, r ∉ tRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r31 : u.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0) := by
    rw [hur.get (by simp [preRegs]), g _ (by simp [tRegs, leafRegs]), hpre.x31]
  rw [hta.so] at r31
  obtain ⟨u1, st1, u1pc, u1r, u1f⟩ := sub79_spec subAt_keygen u hupc false r31
  simp only [Bool.false_eq_true, if_false] at u1pc
  have r19 : u1.getReg .x19 = BitVec.ofNat 64 j := by
    rw [u1r.get (by simp), hur.get (by simp [preRegs])]; exact ht.x19
  obtain ⟨u3, st3, u3pc, u3x28, u3r, u3f⟩ := sub80_spec subAt_keygen u1 u1pc j (by omega) r19
  have hl1 : DigAt u1 (CHAIN + 48) last := hl.frame u1f (by decide) (by simp) (by simp)
  have hk1 : (if j = 0 then 0 else 1) ≤ 1 := by split_ifs <;> omega
  have hs := tslot_eq j
  generalize hkk : (if j = 0 then 0 else 1) = k at u3x28 hk1 hs
  obtain ⟨u4, st4, u4pc, u4x28, u4r, u4f⟩ := sub82_spec subAt_keygen u3 u3pc (j + k) (by omega) u3x28
  obtain ⟨u5, st5, u5pc, u5a, u5b, u5r, u5f⟩ := sub83_spec subAt_keygen u4 u4pc (16 * (j + k)) (by omega)
    (by sc_omega) u4x28
  have hl4 := hl1.frame (u3f.trans u4f) (by decide) (by simp) (by simp)
  have u5s : DigAt u5 (tslot j) last := ⟨by rw [hs, u5a]; exact hl4.1, by rw [hs, u5b]; exact hl4.2⟩
  have u5f' : Frame u1 u5 (fun X => tslot j ≤ X ∧ X < tslot j + 16) :=
    ((u3f.trans u4f).trans u5f).mono (fun X _ h => by rw [hs]; simp at h ⊢; omega)
  have r19' : u5.getReg .x19 = BitVec.ofNat 64 j := by
    rw [u5r.get (by simp), u4r.get (by simp), u3r.get (by simp)]; exact r19
  have r23' : u5.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * j) := by
    rw [u5r.get (by simp), u4r.get (by simp), u3r.get (by simp), u1r.get (by simp), hur.get (by simp [preRegs])]
    exact ht.x23
  obtain ⟨w, st6, wpc, wx19, wx23, wr, wf⟩ := sub92_spec subAt_keygen u5 u5pc j (A.valp + 16 * j) r19' r23'
  have hsl : LEAFPK ≤ tslot j ∧ tslot j + 16 ≤ LEAFPK + 16 * (A.n + 1) :=
    ⟨tslot_ge j, tslot_lt hj⟩
  have fuw : Frame u w (fun X => tslot j ≤ X ∧ X < tslot j + 16) :=
    ((u1f.trans u5f').trans wf).mono (fun X _ h => by
      rcases h with (h | h) | h
      · exact h.elim
      · exact h
      · exact h.elim)
  have ftw : Frame t w (fun X => ((X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X) ∨
      (tslot j ≤ X ∧ X < tslot j + 16)) := huf.trans fuw
  refine ⟨w, Steps.of_eq (st1.trans ((st3.trans (st4.trans st5)).trans st6)) (by omega) (by omega), wpc,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [wx19]
  · rw [wx23, show A.valp + 16 * j + 16 = A.valp + 16 * (j + 1) by ring]
  · rw [wr.get (by simp), u5r.get (by simp), u4r.get (by simp), u3r.get (by simp), u1r.get (by simp),
      hur.get (by simp [preRegs])]; exact ht.x3
  · refine ((ht.regs.trans hur).trans ((((u1r.trans u3r).trans u4r).trans u5r).trans wr)).mono ?_
    simp [tRegs, leafRegs, preRegs]
  · refine (ht.frame.trans ftw).mono (fun X _ h => ?_)
    rcases h with h | ((h | h) | h)
    · exact h
    · exact Or.inl (LeafW_of_c48 h)
    · exact Or.inl (LeafW_of_chainW hj h)
    · exact TW_of_tslot h0 hj h
  · have := tslot_hdr j
    rw [ftw.get (by decide) (by unfold ChainW; tl_omega), ht.lh16]
  · have := tslot_hdr j
    rw [ftw.get (by decide) (by unfold ChainW; tl_omega), ht.lh24]
  · simp [ht.elen]
  · simp [ht.vlen]
  · intro c hc
    by_cases hcj : c = j
    · subst hcj
      have hl5 : DigAt w (tslot c) last := u5s.frame wf (by tl_omega) (by simp) (by simp)
      simpa [List.getD_eq_getElem?_getD, ht.elen] using hl5
    · have hc' : c < j := by omega
      have hsc := tslot_lt (show c < A.n by omega)
      have hsc0 := tslot_ge c
      have hd := tslot_disj hcj
      have hnot : ∀ X, tslot c ≤ X → X < tslot c + 16 →
          ¬ (((X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X) ∨
            (tslot j ≤ X ∧ X < tslot j + 16)) := by
        intro X h1 h2 h
        unfold ChainW at h
        tl_omega
      have h2 : DigAt w (tslot c) (st.1.getD c 0) :=
        (ht.ends c hc').frame ftw (by tl_omega) (hnot _ le_rfl (by omega)) (hnot _ (by omega) (by omega))
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [ht.elen]; omega : c < st.1.length)] using h2
  · have hsj0 := tslot_ge j
    have hvw : DigAt w (A.valp + 16 * j) v := hv.frame fuw (by omega) (by tl_omega) (by tl_omega)
    have hvals : DigsAt w A.valp st.2 :=
      ht.vals.frame ftw (by rw [ht.vlen]; omega) (fun X h1 h2 h => by
        rw [ht.vlen] at h2
        unfold ChainW at h
        tl_omega)
    exact hvals.snoc (by rw [ht.vlen]; exact hvw)
  · exact ht.coef.frame ftw (by rw [hcl]; tl_omega) (fun X h1 h2 h => by
      rw [hcl] at h2
      have := tslot_ge j
      unfold ChainW at h
      tl_omega)
  · exact ht.ext.frame ftw (by tl_omega) (fun X h1 h2 h => by
      have := tslot_ge j
      unfold ChainW at h
      tl_omega)
end top

/-- The chain loop body of `buildLeafTop leaf []` (chain `i`, family seed). -/
def topBody (leaf : Nat) (coefs : List Digest) (state : List Digest × List Digest) (i : Nat) :
    T3.M (List Digest × List Digest) := do
  let digit := ([] : List Nat).getD i 0
  let value ← T3.topChain leaf i 0 digit (topSeed coefs leaf i)
  if false then return (state.1, state.2 ++ [value])
  let last ← T3.topChain leaf i digit (maxDigit 0 i - digit) value
  pure (state.1 ++ [last], state.2 ++ [value])

theorem topBody_eq (leaf : Nat) (coefs : List Digest) (st : List Digest × List Digest) (i : Nat) :
    topBody leaf coefs st i =
      (do let v ← T3.topChain leaf i 0 0 (topSeed coefs leaf i)
          let last ← T3.topChain leaf i 0 (maxDigit 0 i - 0) v
          pure (v, last)) >>= fun r => pure (st.1 ++ [r.2], st.2 ++ [r.1]) := by
  simp only [topBody, List.getD_nil, bind_assoc, pure_bind, Bool.false_eq_true, if_false]

/-- Steps of one chain iteration of the top leaf. -/
def titerK (r j : Nat) : Nat := 11 + capK j + hornK (r * 64 + j + 1) + kChainK j (maxDigit 0 j) + 16
/-- Cycles of one chain iteration of the top leaf. -/
def titerC (r j : Nat) : Nat := 11 + capK j + hornK (r * 64 + j + 1) + kChainCy j (maxDigit 0 j) + 16

section top
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : TopPre sk s0 A) (hta : TopArgs A)
  {coefs extra : List Digest} (hcl : coefs.length = 31) (hel : extra.length ≤ 1)
include hpre hta hcl hel

theorem ktop_iter {j : Nat} (hj : j < 51) {st : List Digest × List Digest} {t : MachineState}
    (ht : TInv s0 A coefs extra j st t) (hpc : t.pc = pcOf 158) :
    TSim image sk t (titerK (A.leaf % 4) j) (titerC (A.leaf % 4) j) (maxDigit 0 j) (maxDigit 0 j) (topBody A.leaf coefs st j)
      (fun st' u => u.pc = pcOf 158 ∧ TInv s0 A coefs extra (j + 1) st' u) := by
  have hn : A.n = 51 := by show chainCount A.lay = 51; rw [hpre.top0.1]; rfl
  have h0 := hpre.top0
  have hvs := hpre.hvs
  have hvb := hpre.hv
  have hv8 := hpre.hv8
  have hds := hpre.hds
  have hdv := hpre.hdv
  have hcv := hta.cv
  have hcd := hta.cd
  have g : ∀ r, r ∉ tRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub41_spec subAt_keygen t hpc j 51 (by omega) (by omega) ht.x19
    (by rw [g _ (by simp [tRegs, leafRegs]), hpre.x26, hn])
  rw [if_pos hj] at t1pc
  obtain ⟨t2, st2, t2pc, t2x1, t2x13, t2r, t2f⟩ := kg159_spec t1 t1pc j (by rw [t1r.get (by simp)]; exact ht.x19)
  have hc2 : DigsAt t2 KCOEF coefs :=
    ht.coef.frame (t1f.trans t2f) (by rw [hcl]; tl_omega) (fun _ _ _ h => by simp_all)
  have r18 : t2.getReg .x18 = BitVec.ofNat 64 A.leaf := by
    rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [tRegs, leafRegs]), hpre.x18]
  obtain ⟨t3, st3, t3pc, t3seed, t3r, t3f⟩ := khorn_run t2 t2pc (i := j) (by omega) t2x13 r18 hcl hc2 t2x1
  obtain ⟨t4, st4, t4pc, t4r, t4f⟩ := kg161_spec t3 t3pc
  have e14 : RegsExcept t t4 ([] ++ [.x1, .x13] ++ khornRegs ++ []) := ((t1r.trans t2r).trans t3r).trans t4r
  have f14 : Frame t t4 (fun X => X = CHAIN + 48 ∨ X = CHAIN + 56) :=
    (((t1f.trans t2f).trans t3f).trans t4f).mono (fun X _ h => by simp_all)
  have r19 : t4.getReg .x19 = BitVec.ofNat 64 j := by rw [e14.get (by simp [khornRegs])]; exact ht.x19
  have r22 : t4.getReg .x22 = BitVec.ofNat 64 A.digp := by
    rw [e14.get (by simp [khornRegs]), g _ (by simp [tRegs, leafRegs]), hpre.x22]
  obtain ⟨t5, st5, t5pc, t5x28, t5r, t5f⟩ := kg188_spec t4 t4pc j A.digp r19 r22
  have hdj : A.d j = 0 := by show A.digits.getD j 0 = 0; rw [hta.dig]; rfl
  have hw := hpre.hdigW j (by omega)
  have hdp := hpre.hdigp
  have hcdig := hta.cdig
  have hcdigL := hta.cdigL
  have hbyte : t5.getByte (BitVec.ofNat 64 (A.digp + j)) = BitVec.ofNat 8 0 := by
    rw [t5f.getByte (by omega) (fun h => h), f14.getByte (by omega) (fun h => hw (by
        simp only [LeafW, CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at h ⊢; omega)),
      ht.frame.getByte (by omega) (fun h => by
        rcases h with h | h | h
        · exact hw h
        · simp only [LEAFPK] at h hcdigL; omega
        · simp only [KCOEF] at h hcdig; omega), hpre.hdig j (by omega), hdj]
  obtain ⟨t6, st6, t6pc, t6x17, t6r, t6f⟩ := sub72_spec subAt_keygen t5 t5pc (A.digp + j) (by omega) 0
    (by norm_num) t5x28 hbyte
  have r8 : t6.getReg .x8 = BitVec.ofNat 64 0 := by
    rw [t6r.get (by simp), t5r.get (by simp), e14.get (by simp [khornRegs]), g _ (by simp [tRegs, leafRegs]),
      hpre.x8, h0.1]; rfl
  obtain ⟨t7, st7, t7pc, t7x21, t7r, t7f⟩ := sub73_spec subAt_keygen t6 t6pc 0 (by norm_num) r8
  rw [if_pos rfl] at t7pc
  obtain ⟨t8, st8, t8pc, t8r, t8f⟩ := kg192_spec t7 t7pc
  obtain ⟨t9, st9, t9pc, t9x21, t9r, t9f⟩ := kgCap_spec t8 t8pc j (by omega)
    (by rw [t8r.get (by simp), t7r.get (by simp), t6r.get (by simp), t5r.get (by simp)]; exact r19)
  have e49 : RegsExcept t4 t9 ([.x28] ++ [.x17] ++ [.x21] ++ [] ++ [.x21, .x30]) :=
    (((t5r.trans t6r).trans t7r).trans t8r).trans t9r
  have r31 : t9.getReg .x31 = BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [e49.get (by simp), e14.get (by simp [khornRegs]), g _ (by simp [tRegs, leafRegs]), hpre.x31, hta.so]
  obtain ⟨t10, st10, t10pc, t10r, t10f⟩ := sub76_spec subAt_keygen t9 t9pc false r31
  simp only [Bool.false_eq_true, if_false] at t10pc
  obtain ⟨t11, st11, t11pc, t11x1, t11r, t11f⟩ := sub78_spec subAt_keygen t10 t10pc
  have e111 : RegsExcept t t11 preRegs :=
    ((e14.trans e49).trans (t10r.trans t11r)).mono (by simp [preRegs, khornRegs])
  have f111 : Frame t t11 (fun X => X = CHAIN + 48 ∨ X = CHAIN + 56) :=
    (f14.trans ((((((t5f.trans t6f).trans t7f).trans t8f).trans t9f).trans t10f).trans t11f)).mono
      (fun X _ h => by simp_all)
  have g11 : ∀ r, r ∉ preRegs → r ∉ tRegs → t11.getReg r = s0.getReg r := fun r h1 h2 =>
    (e111.get h1).trans (g r h2)
  have hL : ∀ X, (X = CHAIN ∨ X = CHAIN + 8) →
      t11.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := by
    intro X hX
    have hX' : X < 2 ^ 64 := by rcases hX with h | h <;> (rw [h]; decide)
    rw [f111.get hX' (by simp only [CHAIN] at hX ⊢; omega), ht.frame.get hX' (fun h => by
      rcases h with h | h | h
      · unfold LeafW at h
        rw [if_pos h0.1] at h
        tl_omega
      · tl_omega
      · tl_omega)]
  have hcp : ChainPre t11 0 0 A.leaf j 0 (maxDigit 0 j) (A.valp + 16 * j) (117 + 79) :=
    { x5 := by rw [g11 _ (by simp [preRegs]) (by simp [tRegs, leafRegs]), hpre.x5]
      x1 := t11x1
      x8 := by
        rw [t11r.get (by simp), t10r.get (by simp), e49.get (by simp), e14.get (by simp [khornRegs]),
          g _ (by simp [tRegs, leafRegs]), hpre.x8, h0.1]
      x9 := by rw [g11 _ (by simp [preRegs]) (by simp [tRegs, leafRegs]), hpre.x9, h0.2]
      x18 := by rw [g11 _ (by simp [preRegs]) (by simp [tRegs, leafRegs]), hpre.x18]
      x17 := by rw [t11r.get (by simp), t10r.get (by simp), t9r.get (by simp), t8r.get (by simp),
        t7r.get (by simp), t6x17]
      x19 := by rw [e111.get (by simp [preRegs])]; exact ht.x19
      x21 := by rw [t11r.get (by simp), t10r.get (by simp), t9x21]
      x23 := by rw [e111.get (by simp [preRegs])]; exact ht.x23
      htree := by norm_num
      hi := by omega
      l0 := rfl
      t0 := rfl
      hroute := by have := hpre.hroute; rw [h0.1, h0.2] at this; simpa using this
      hleaf := by have := hpre.hleafHeight; rw [h0.1] at this; exact this
      hcap := Nat.zero_le _
      he := rfl
      hv8 := by omega
      hv := by omega
      hvc := by tl_omega
      z0 := by rw [hL _ (by simp), hpre.z0]
      z8 := by rw [hL _ (by simp), hpre.z8] }
  have hseed : DigAt t11 (CHAIN + 48) (topSeed coefs A.leaf j) :=
    t3seed.frame (((((((t4f.trans t5f).trans t6f).trans t7f).trans t8f).trans t9f).trans t10f).trans t11f)
      (by decide) (by simp) (by simp)
  have hch := chainRun_tsim subAt_keygen sk hcp t11pc (topSeed coefs A.leaf j) hseed
  rw [topBody_eq]
  refine (TSim.steps (((((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans
    st8).trans st9).trans (st10.trans st11)) (TSim.bind (k₂ := 16) (c₂ := 16) (n₂ := 0) (b₂ := 0) hch
    (fun r u hu => ?_))).of_eq rfl ?_ ?_ (by omega) (by omega)
  · obtain ⟨hupc, hv, hl, hur, huf⟩ := hu
    obtain ⟨w, stw, wpc, hw⟩ := ktop_post sk hpre hta hcl hel (j := j) (by omega) ht hupc
      ((e111.trans hur).mono (by simp [preRegs, chainRegs])) ((f111.trans huf).mono (fun _ _ h => h))
      r.1 r.2 hv hl
    exact TSim.pure_steps stw ⟨wpc, hw⟩
  · unfold titerK topPoint; omega
  · unfold titerC topPoint; omega
end top

section top
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : TopPre sk s0 A) (hta : TopArgs A)
  {coefs extra : List Digest} (hcl : coefs.length = 31) (hel : extra.length ≤ 1)
include hpre hta hcl hel

/-- Leaf exit (158 with all 51 chains done): leaf hash of the chain ends into `dest`, return. -/
theorem ktop_exit {st : List Digest × List Digest} {t : MachineState} (ht : TInv s0 A coefs extra 51 st t)
    (hpc : t.pc = pcOf 158) :
    TSim image sk t 19 (18 + 8 * leafBlocks A.lay) 1 (leafBlocks A.lay)
      (leafHash 0 0 A.leaf st.1 >>= fun root => pure (root, st.2))
      (fun r u => u.pc = pcOf A.ret ∧ DigAt u A.dest r.1 ∧ DigsAt u A.valp r.2 ∧ RegsExcept s0 u tRegs ∧
        Frame s0 u (TW A) ∧ DigsAt u KCOEF coefs ∧ DigsAt u (KCOEF + 496) extra) := by
  have hn : A.n = 51 := by show chainCount A.lay = 51; rw [hpre.top0.1]; rfl
  have h0 := hpre.top0
  have g : ∀ r, r ∉ tRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r26 : t.getReg .x26 = BitVec.ofNat 64 51 := by
    rw [g _ (by simp [tRegs, leafRegs]), hpre.x26, hn]
  have r31 : t.getReg .x31 = BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [g _ (by simp [tRegs, leafRegs]), hpre.x31, hta.so]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub41_spec subAt_keygen t hpc 51 51 (by omega) (by omega) ht.x19 r26
  rw [if_neg (lt_irrefl _)] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub95_spec subAt_keygen t1 t1pc false (by rw [t1r.get (by simp)]; exact r31)
  simp only [Bool.false_eq_true, if_false] at t2pc
  have e12 : RegsExcept t t2 [] := (t1r.trans t2r).mono (by simp)
  have f12 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  have r18 : t.getReg .x18 = BitVec.ofNat 64 A.leaf := by rw [g _ (by simp [tRegs, leafRegs]), hpre.x18]
  obtain ⟨t3, st3, t3pc, t3x10, t3x11, t3x12, t3x29, t3r, t3f⟩ := sub96_spec subAt_keygen t2 t2pc 51 (Or.inl rfl)
    (by rw [e12.get (by simp)]; exact r26) A.leaf (by rw [e12.get (by simp)]; exact r18)
  have r13 : RegsExcept t t3 [.x10, .x11, .x12, .x29] := (e12.trans t3r).mono (by simp)
  have f13 : Frame t t3 (fun _ => False) := (f12.trans t3f).mono (fun X _ h => by simp_all)
  have hlen : st.1.length = A.n := by rw [ht.elen, hn]
  have hvs := hpre.hvs
  have hds := hpre.hds
  have hdv := hpre.hdv
  have hcv := hta.cv
  have hcd := hta.cd
  have hw : t3.readWords (BitVec.ofNat 64 LEAFPK) (8 * leafBlocks A.lay) =
      wordsOf (pad64 (T3.leafInput A.lay A.tree A.leaf st.1)) := by
    rw [leafInput_words A h0.1 st.1 hlen]
    have h0d : DigAt t3 LEAFPK (st.1.getD 0 0) := by
      have e0 : tslot 0 = LEAFPK := rfl
      have := (ht.ends 0 (by omega)).frame f13 (by rw [e0]; decide) (by simp) (by simp)
      rw [e0] at this
      exact this
    have hall : DigsAt t3 (LEAFPK + 32) (st.1.drop 1) := by
      intro c hc
      simp only [List.length_drop] at hc
      have e1 : tslot (c + 1) = LEAFPK + 32 + 16 * c := by unfold tslot; rw [if_neg (by omega)]; omega
      have := (ht.ends (c + 1) (by omega)).frame f13 (by rw [e1]; simp only [LEAFPK]; omega) (by simp)
        (by simp)
      rw [e1] at this
      simpa [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm] using this
    have hhd : t3.readWords (BitVec.ofNat 64 (LEAFPK + 16)) 2 =
        [T3.hyperWord A.lay.val (A.tree * 2 ^ T3.height A.lay + A.leaf), 0] := by
      rw [readWords_two, f13.get (by decide) (by simp), f13.get (by decide) (by simp), ht.lh16,
        show LEAFPK + 16 + 8 = LEAFPK + 24 from rfl, ht.lh24]
    have hb : 8 * leafBlocks A.lay = 2 + (2 + 2 * (st.1.drop 1).length) := by
      simp only [List.length_drop, hlen, leafBlocks, show chainCount A.lay = A.n from rfl, hn]
    rw [hb, readWords_add, readWords_add, h0d.words, hhd,
      show LEAFPK + 8 * 2 + 8 * 2 = LEAFPK + 32 from rfl, hall.words, List.append_assoc]
  have hl := leafInput_length A h0.1 st.1 hlen
  have hnb : leafBlocks A.lay = 13 := by unfold leafBlocks; rw [show chainCount A.lay = A.n from rfl, hn]
  have hq : hashInput t3 = toQ (pad64 (T3.leafInput A.lay A.tree A.leaf st.1)) := by
    refine hashInput_toQ t3 _ (leafBlocks A.lay - 1) LEAFPK (by rw [hl]; omega) t3x10 (by decide)
      (by decide) ?_ (by omega) (by rw [show 8 * (leafBlocks A.lay - 1 + 1) = 8 * leafBlocks A.lay by omega]; exact hw)
    rw [t3x11, hnb] <;> rfl
  have hblk : (toQ (pad64 (T3.leafInput A.lay A.tree A.leaf st.1))).blocks = leafBlocks A.lay := by
    rw [blocks_toQ ⟨by rw [hl]; omega, by rw [hl]; omega⟩, hl]; omega
  have hv : hashArgumentsValid t3 = true := by
    refine hashArgs_const t3 LEAFPK (64 * leafBlocks A.lay) LOUT t3x10 ?_ t3x12 (by decide) (by omega)
      (by simp only [LEAFPK]; omega) (by decide) (by decide)
    rw [t3x11, hnb] <;> rfl
  have h5 : t3.getReg .x5 = 0 := by rw [r13.get (by simp), g _ (by simp [tRegs, leafRegs]), hpre.x5]
  have hlh : leafHash 0 0 A.leaf st.1 =
      T3.projHash (T3.leafHalfHigh 0 A.leaf) (T3.leafInput A.lay A.tree A.leaf st.1) := by
    rw [h0.1, h0.2]; rfl
  rw [hlh]
  refine (TSim.steps (st1.trans (st2.trans st3)) (tsim_projHash_bind (k := 7) (c := 7) (n := 0) (b := 0)
    (f := fun root => pure (root, st.2)) (fetch_sub105 subAt_keygen t3 t3pc) h5 hv hq (fun a => ?_))).of_eq rfl
    (by omega) (by rw [hblk]; omega) (by omega) (by rw [hblk]; omega)
  have hdb := hpre.hd
  have hd8 := hpre.hd8
  have hwf := Frame.writeHash t3 a LOUT t3x12 (by decide)
  obtain ⟨u2, st5, u2pc, u2a, u2b, u2r, u2f⟩ := sub106_spec subAt_keygen (writeHash t3 a)
    (by rw [pc_writeHash, t3pc, pcOf_add4]) A.dest hd8 hdb (by tl_omega)
    (by rw [getReg_writeHash, r13.get (by simp), g _ (by simp [tRegs, leafRegs]), hpre.x25])
    (A.leaf % 2) (Nat.mod_lt _ (by decide)) (by rw [getReg_writeHash]; exact t3x29)
    (by rw [getReg_writeHash]; exact t3x12)
  have hd2 : DigAt u2 A.dest (T3.projHalf (T3.leafHalfHigh 0 A.leaf) a) := by
    rcases Nat.mod_two_eq_zero_or_one A.leaf with hp | hp
    · have hhi := DigAt.writeHash_hi t3 a LOUT t3x12 (by decide)
      have hh : T3.leafHalfHigh 0 A.leaf = true := by simp [T3.leafHalfHigh, hp]
      rw [hh, T3.projHalf_true]
      rw [hp] at u2a u2b
      exact ⟨u2a.trans hhi.1, by rw [u2b]; exact hhi.2⟩
    · have hlo := DigAt.writeHash_lo t3 a LOUT t3x12 (by decide)
      have hh : T3.leafHalfHigh 0 A.leaf = false := by simp [T3.leafHalfHigh, hp]
      rw [hh, T3.projHalf_false]
      rw [hp] at u2a u2b
      exact ⟨u2a.trans hlo.1, by rw [u2b]; exact hlo.2⟩
  obtain ⟨u3, st6, u3pc, u3r, u3f⟩ := sub112_spec subAt_keygen u2 u2pc A.ret
    (by rw [u2r.get (by simp), getReg_writeHash, r13.get (by simp)]; exact ht.x3)
  have fall : Frame t u3 (fun X => (LOUT ≤ X ∧ X < LOUT + 32) ∨ (X = A.dest ∨ X = A.dest + 8)) :=
    ((f13.trans hwf).trans (u2f.trans u3f)).mono (fun X _ h => by
      rcases h with (h | h) | (h | h)
      · exact h.elim
      · left; exact h
      · right; exact h
      · exact h.elim)
  refine TSim.pure_steps (st5.trans st6) ⟨u3pc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hd2.frame u3f (by omega) (by simp) (by simp)
  · have hvb := hpre.hv
    exact ht.vals.frame fall (by rw [ht.vlen]; omega) (fun X h1 h2 => by rw [ht.vlen] at h2; tl_omega)
  · have hw0 : RegsExcept t3 (writeHash t3 a) [] := fun r _ => getReg_writeHash t3 a r
    exact ((ht.regs.trans r13).trans ((hw0.trans u2r).trans u3r)).mono (by simp [tRegs, leafRegs])
  · refine (ht.frame.trans fall).mono (fun X _ h => ?_)
    rcases h with h | h | h
    · exact h
    · left; unfold LeafW; right; right; right; right; right; right; right; left; exact h
    · left; unfold LeafW; right; right; right; right; right; right; right; right; right
      rcases h with h | h <;> omega
  · exact ht.coef.frame fall (by rw [hcl]; tl_omega) (fun X h1 h2 h => by rw [hcl] at h2; tl_omega)
  · exact ht.ext.frame fall (by tl_omega) (fun X h1 h2 h => by tl_omega)
end top

theorem buildLeafTopC_eq' (leaf : Nat) (coefs : List Digest) : buildLeafTopC leaf coefs [] = (do
    let state ← (List.range 51).foldlM (topBody leaf coefs) ([], [])
    leafHash 0 0 leaf state.1 >>= fun root => pure (root, state.2)) := rfl

/-- Steps of a keygen top leaf (`r = leaf % 4`, `o = leaf / 4 % 2`). -/
def topLeafK (r o : Nat) : Nat := 14 + ((if r = 0 then kfK o else 5) + (sumTo (titerK r) 51 + 19))
/-- Cycles of a keygen top leaf. -/
def topLeafC (r o : Nat) : Nat := 14 + ((if r = 0 then kfC o else 5) + (sumTo (titerC r) 51 + (18 + 8 * 13)))
/-- Hash calls of a keygen top leaf. -/
def topLeafN (r o : Nat) : Nat := (if r = 0 then 16 - o else 0) + (sumTo (fun j => maxDigit 0 j) 51 + 1)
/-- Compression blocks of a keygen top leaf. -/
def topLeafB (r o : Nat) : Nat := (if r = 0 then 16 - o else 0) + (sumTo (fun j => maxDigit 0 j) 51 + 13)

section top
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : TopPre sk s0 A) (hta : TopArgs A)
include hpre hta

/-- img-v6: one keygen top leaf (entry 144, return to `A.ret`): KTOP (`topFamilyCoefs`, the family coefficients and
carry in the buffer at KCOEF) then the leaf (`buildLeafTopC`), with exact counts. -/
theorem topLeaf_tsim (hpc : s0.pc = pcOf 144) {cc : List Digest × Digest} (hk : KcPre s0 A.leaf cc) :
    TSim image sk s0 (topLeafK (A.leaf % 4) (A.leaf / 4 % 2)) (topLeafC (A.leaf % 4) (A.leaf / 4 % 2))
      (topLeafN (A.leaf % 4) (A.leaf / 4 % 2)) (topLeafB (A.leaf % 4) (A.leaf / 4 % 2))
      (topFamilyCoefs A.leaf cc >>= fun cc' => buildLeafTopC A.leaf cc'.1 [] >>= fun r => pure (r, cc'))
      (fun rc t => t.pc = pcOf A.ret ∧ DigAt t A.dest rc.1.1 ∧ DigsAt t A.valp rc.1.2 ∧ KcPost t A.leaf rc.2 ∧
        RegsExcept s0 t tRegs ∧ Frame s0 t (TW A)) := by
  have hn : A.n = 51 := by show chainCount A.lay = 51; rw [hpre.top0.1]; rfl
  have h0 := hpre.top0
  have hlay : A.lay.val < 256 := by have := A.lay.isLt; omega
  have hnb : leafBlocks A.lay = 13 := by unfold leafBlocks; rw [show chainCount A.lay = A.n from rfl, hn]
  obtain ⟨t1, st1, t1pc, t1x1, t1x3, t1l16, t1l24, t1r, t1f⟩ :=
    kg27_spec s0 hpc A.lay.val A.leaf hlay hpre.hleaf hpre.x8 hpre.x18
  have hleaf : A.leaf < 4096 := by have := hpre.hleafHeight; rw [h0.1] at this; exact this
  have fp : ∀ X, X < PRIV + 64 → t1.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX =>
    t1f.get (by simp only [PRIV] at hX; omega) (by simp only [PRIV, LEAFPK] at hX ⊢; omega)
  have hp : KPriv sk t1 :=
    { x5 := by rw [t1r.get (by simp), hpre.x5]
      p0 := by rw [fp _ (by decide), hpre.p0]
      p8 := by rw [fp _ (by decide), hpre.p8]
      p32 := by rw [fp _ (by decide), hpre.p32]
      p40 := by rw [fp _ (by decide), hpre.p40]
      p48 := by rw [fp _ (by decide), hpre.p48]
      p56 := by rw [fp _ (by decide), hpre.p56] }
  have hk1 : KcPre t1 A.leaf cc := hk.frame t1f (fun X h1 h2 h => by simp only [LEAFPK, KCOEF] at h h1 h2; omega)
  have hkf := kfam_tsim sk t1pc hleaf (by rw [t1r.get (by simp)]; exact hpre.x18) hp t1x1 hk1
  refine (TSim.steps st1 (TSim.bind (k₂ := sumTo (titerK (A.leaf % 4)) 51 + 19)
    (c₂ := sumTo (titerC (A.leaf % 4)) 51 + (18 + 8 * leafBlocks A.lay)) (n₂ := sumTo (fun j => maxDigit 0 j) 51 + 1)
    (b₂ := sumTo (fun j => maxDigit 0 j) 51 + leafBlocks A.lay) hkf (fun cc' t ht => ?_))).of_eq rfl rfl
    (by rw [hnb]; rfl) rfl (by rw [hnb]; rfl)
  obtain ⟨tpc, ⟨hcl, hcoef, hslot⟩, t19, tr, tf⟩ := ht
  obtain ⟨extra, hel, hext, hpost⟩ : ∃ extra : List Digest, extra.length ≤ 1 ∧ DigsAt t (KCOEF + 496) extra ∧
      ∀ v, DigsAt v KCOEF cc'.1 → DigsAt v (KCOEF + 496) extra → KcPost v A.leaf cc' := by
    by_cases hs : (A.leaf + 4) / 4 % 2 = 1
    · refine ⟨[cc'.2], by simp, fun i hi => ?_, fun v h1 h2 => ⟨hcl, h1, fun _ => ?_⟩⟩
      · simp only [List.length_singleton] at hi
        have : i = 0 := by omega
        subst this; simpa using hslot hs
      · simpa using h2 0 (by simp)
    · exact ⟨[], by simp, DigsAt.nil _ _, fun v h1 _ => ⟨hcl, h1, fun h => absurd h hs⟩⟩
  have hinv : TInv s0 A cc'.1 extra 0 ([], []) t := by
    refine ⟨t19, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, fun c hc => absurd hc (by omega), DigsAt.nil _ _, hcoef, hext⟩
    · rw [tr.get (by simp [cgRegs]), t1r.get (by simp), hpre.x23]; simp
    · rw [tr.get (by simp [cgRegs]), t1x3, hpre.x1]
    · exact (t1r.trans tr).mono (by simp [tRegs, leafRegs, cgRegs])
    · refine (t1f.trans tf).mono (fun X _ h => ?_)
      rcases h with h | h
      · left; unfold LeafW; rw [if_pos h0.1]; simp only [LEAFPK, CHAIN] at h ⊢; omega
      · unfold CgW at h
        rcases h with h | h | h | h
        · left; unfold LeafW; left; exact h
        · left; unfold LeafW; right; left; exact h
        · left; unfold LeafW; right; right; left; exact h
        · right; right; exact h
    · rw [tf.get (by decide) (by unfold CgW; simp only [PRIV, SEEDS, KCOEF, LEAFPK]; omega), t1l16, h0.2]; simp
    · rw [tf.get (by decide) (by unfold CgW; simp only [PRIV, SEEDS, KCOEF, LEAFPK]; omega), t1l24]
  rw [buildLeafTopC_eq', bind_assoc]
  exact TSim.bind (TSim.foldlM_range 51 (topBody A.leaf cc'.1) ([], [])
    (fun j st t => t.pc = pcOf 158 ∧ TInv s0 A cc'.1 extra j st t) (titerK (A.leaf % 4)) (titerC (A.leaf % 4))
    (fun j => maxDigit 0 j) (fun j => maxDigit 0 j)
    (fun j hj st t ht => ktop_iter sk hpre hta hcl hel hj ht.2 ht.1) ⟨tpc, hinv⟩)
    (fun st u hu => TSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0) (ktop_exit sk hpre hta hcl hel hu.2 hu.1)
      (fun r v hv => TSim.pure ⟨hv.1, hv.2.1, hv.2.2.1, hpost v hv.2.2.2.2.2.1 hv.2.2.2.2.2.2, hv.2.2.2.1,
        hv.2.2.2.2.1⟩))
end top

/-- Cycle bound of one keygen top leaf (COMPUTED by `decide` over the 8 leaf classes; campaign T51: max 205,853 at
`leaf % 4 = 3`). -/
def topLeafW : Nat := 205853
theorem topLeaf_bound (r o : Nat) (hr : r < 4) (ho : o < 2) :
    topLeafK r o ≤ topLeafC r o ∧ topLeafC r o ≤ topLeafW := by
  interval_cases r <;> interval_cases o <;> decide

end SigGolfCandidate.T3M.Keygen
