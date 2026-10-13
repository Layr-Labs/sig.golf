import SigGolfCandidate.T3M.Keygen.Leaf
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.GfMul

/-!
# Keygen top leaf with family seeds (campaign T8D, TOP2 NF17)

The keygen image's top-leaf routine (entry 144) first runs COEFGEN (612..640: the 12 private pairs
`privatePair 0 0 0 (12 leaf + j) 0`, copied to the 24 coefficients at `KCOEF`), then for every chain `i < 54` runs
HORN (642..682: `familyEval coefs (i + 1)` into `CHAIN + 48`), the per-chain cap table CAP (684..688: `maxDigit 0 i`),
the shared chain routine (117) and stores the chain end; finally the leaf hash. This file proves the blocks, the two
new loops and `buildLeafTop_tsim` (refinement of `T3.buildLeafTop leaf []` with exact step/cycle/hash counts).
-/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chainCount maxDigit chain leafHash privatePair header privateInput
  topCoefs topSeedPair topSeed buildLeafTop pad64)
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
def kgCG0 : List (BitVec 32) := coefgenCode.take 6
def kgCG1 : List (BitVec 32) := (coefgenCode.drop 6).take 5
def kgCG2 : List (BitVec 32) := (coefgenCode.drop 12).take 15
def kgCG3 : List (BitVec 32) := (coefgenCode.drop 27).take 2
def kgH0 : List (BitVec 32) := hornCode.take 5
def kgHK : List (BitVec 32) := (hornCode.drop 5).take 6
def kgHB1 : List (BitVec 32) := (hornCode.drop 11).take 2
def kgHB2 : List (BitVec 32) := (hornCode.drop 13).take 3
def kgHB3 : List (BitVec 32) := (hornCode.drop 16).take 9
def kgHF : List (BitVec 32) := (hornCode.drop 25).take 12
def kgHE : List (BitVec 32) := (hornCode.drop 37).take 4
def kgC1 : List (BitVec 32) := capCode.take 3
def kgC2 : List (BitVec 32) := capCode.drop 3

theorem codeAt_kg27 : CodeAt image (pcOf 144) kg27 := by decide +kernel
theorem codeAt_kg159 : CodeAt image (pcOf 159) kg159 := by decide +kernel
theorem codeAt_kg161 : CodeAt image (pcOf 161) kg161 := by decide +kernel
theorem codeAt_kg188 : CodeAt image (pcOf 188) kg188 := by decide +kernel
theorem codeAt_kg192 : CodeAt image (pcOf 192) kg192 := by decide +kernel
theorem codeAt_kgCG0 : CodeAt image (pcOf 612) kgCG0 := by decide +kernel
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

sym_block bk27 := symRun { noAlias := true } kg27 (pcOf 144) 100
sym_block bk159 := symRun { noAlias := true } kg159 (pcOf 159) 100
sym_block bk161 := symRun { noAlias := true } kg161 (pcOf 161) 100
sym_block bk188 := symRun { noAlias := true } kg188 (pcOf 188) 100
sym_block bk192 := symRun { noAlias := true } kg192 (pcOf 192) 100
sym_block bkCG0 := symRun { noAlias := true } kgCG0 (pcOf 612) 100
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

/-- CAP (684..688): `s5 = maxDigit 0 i`, then 193. -/
theorem kgCap_spec (s : MachineState) (hpc : s.pc = pcOf 684) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s (if i < 51 then 3 else 5) (if i < 51 then 3 else 5) t ∧ t.pc = pcOf 193 ∧
      t.getReg .x21 = BitVec.ofNat 64 (maxDigit 0 i) ∧ RegsExcept s t [.x21, .x30] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨t1, st1, t1pc, t1x21, t1r, t1f⟩ : ∃ t, Steps image s 3 3 t ∧
      t.pc = (if i < 51 then pcOf 193 else pcOf 687) ∧ t.getReg .x21 = BitVec.ofNat 64 4 ∧
      RegsExcept s t [.x21, .x30] ∧ Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound bkC1 codeAt_kgC1 s hpc (by simp [bkC1.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, bkC1.res, E.eval, CmpOp.eval, h19,
        ofNat_slt i 51 hi (by norm_num)]
      by_cases h : i < 51 <;> simp [h]
    · simp [bkC1.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [bkC1.res, rv_simp] <;> rfl
    · intro A _ _; simp [bkC1.res, rv_simp]
  by_cases h : i < 51
  · rw [if_pos h] at t1pc
    refine ⟨t1, by simpa [h] using st1, t1pc, ?_, t1r, t1f⟩
    rw [t1x21]; simp [maxDigit, h]
  · rw [if_neg h] at t1pc
    obtain ⟨t2, st2, t2pc, t2x21, t2r, t2f⟩ : ∃ t, Steps image t1 2 2 t ∧ t.pc = pcOf 193 ∧
        t.getReg .x21 = BitVec.ofNat 64 7 ∧ RegsExcept t1 t [.x21] ∧ Frame t1 t (fun _ => False) := by
      refine ⟨_, symRun_sound bkC2 codeAt_kgC2 t1 t1pc (by simp [bkC2.res, rv_simp]), ?_, ?_, ?_, ?_⟩
      · simp [bkC2.res, Result.toState_pc, E.eval]
      · simp [bkC2.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [bkC2.res, rv_simp] <;> rfl
      · intro A _ _; simp [bkC2.res, rv_simp]
    refine ⟨t2, by simpa [h] using st1.trans st2, t2pc, ?_, (t1r.trans t2r).mono (by simp),
      (t1f.trans t2f).mono (fun _ _ h => by simp_all)⟩
    rw [t2x21]; simp [maxDigit, h]

/-! ## COEFGEN blocks -/
/-- 612..617: `s8 = KCOEF`, `a4 = (12 leaf) << 32 | 1`, `t4 = 0` (the `mul` costs 4 cycles). -/
theorem kgCG0_spec (s : MachineState) (hpc : s.pc = pcOf 612) (leaf : Nat)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 6 9 t ∧ t.pc = pcOf 618 ∧ t.getReg .x14 = BitVec.ofNat 64 (1 + 2 ^ 32 * (12 * leaf)) ∧
      t.getReg .x24 = BitVec.ofNat 64 KCOEF ∧ t.getReg .x29 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x14, .x24, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkCG0 codeAt_kgCG0 s hpc (by simp [bkCG0.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bkCG0.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, bkCG0.res, RegFile.get, E.eval, h18]
    have hm : BinOp.eval .mul (BitVec.ofNat 64 leaf) (BitVec.ofNat 64 12) = BitVec.ofNat 64 (leaf * 12) := by
      apply BitVec.eq_of_toNat_eq; simp [BinOp.eval, BitVec.toNat_mul]
    rw [show (12#64) = BitVec.ofNat 64 12 from rfl, hm, show (32#64) = BitVec.ofNat 64 32 from rfl,
      kshl _ 32 (by norm_num), ofNat_shl, show (1#64) = BitVec.ofNat 64 1 from rfl]
    show BitVec.ofNat 64 (leaf * 12 * 2 ^ 32) ||| BitVec.ofNat 64 1 = _
    rw [ofNat_or_disjoint 1 (leaf * 12 * 2 ^ 32) 32 (by norm_num) (by omega)]
    congr 1; ring
  · simp [bkCG0.res, rv_simp]
  · simp [bkCG0.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bkCG0.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkCG0.res, rv_simp]

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

/-- 624..638: copy the 32-byte answer to `KCOEF + 32 j`, next pair, `bne t4, 12`. -/
theorem kgCG2_spec (s : MachineState) (hpc : s.pc = pcOf 624) (j p : Nat) (hj : j < 12)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 PRIV) (h24 : s.getReg .x24 = BitVec.ofNat 64 (KCOEF + 32 * j))
    (h29 : s.getReg .x29 = BitVec.ofNat 64 j) (h14 : s.getReg .x14 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 15 15 t ∧ t.pc = (if j + 1 < 12 then pcOf 618 else pcOf 639) ∧
      t.getReg .x14 = BitVec.ofNat 64 (p + 2 ^ 32) ∧ t.getReg .x24 = BitVec.ofNat 64 (KCOEF + 32 * (j + 1)) ∧
      t.getReg .x29 = BitVec.ofNat 64 (j + 1) ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (KCOEF + 32 * j + 8 * k)) = s.getMem (BitVec.ofNat 64 (SEEDS + 8 * k))) ∧
      RegsExcept s t [.x4, .x14, .x24, .x29, .x30] ∧
      Frame s t (fun A => KCOEF + 32 * j ≤ A ∧ A < KCOEF + 32 * j + 32) := by
  have hobl : Oblig.all s bkCG2.res.st.obl := by
    simp only [bkCG2.res]
    t3n [h10, h24]
    simp only [PRIV, KCOEF]
    and_intros <;> first | trivial | omega
  refine ⟨_, symRun_sound bkCG2 codeAt_kgCG2 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkCG2.res, E.eval, CmpOp.eval, h29]
    by_cases h : j + 1 < 12
    · rw [if_pos h]
      simp only [BinOp.eval, ofNat_add_ofNat, bne_iff_ne, ne_eq, ofNat_inj (show j + 1 < 2 ^ 64 by omega)
        (show 12 < 2 ^ 64 by norm_num)]
      rw [if_pos (by omega)]
    · rw [if_neg h]
      simp only [BinOp.eval, ofNat_add_ofNat, bne_iff_ne, ne_eq, ofNat_inj (show j + 1 < 2 ^ 64 by omega)
        (show 12 < 2 ^ 64 by norm_num)]
      rw [if_neg (by omega)]
  · t3n [bkCG2.res, h14]
  · t3n [bkCG2.res, h24]; simp only [KCOEF]; omega
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
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

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
/-- 642..646: `a4 = a5 = 0` (accumulator), `a0 = KCOEF + 16 * 24`, `a1 = KCOEF`. -/
theorem kgH0_spec (s : MachineState) (hpc : s.pc = pcOf 642) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf 647 ∧ t.getReg .x10 = BitVec.ofNat 64 (KCOEF + 16 * 24) ∧
      t.getReg .x11 = BitVec.ofNat 64 KCOEF ∧ t.getReg .x14 = BitVec.ofNat 64 0 ∧
      t.getReg .x15 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x10, .x11, .x14, .x15] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkH0 codeAt_kgH0 s hpc (by simp [bkH0.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bkH0.res, Result.toState_pc, E.eval]
  all_goals first
    | (simp [bkH0.res, rv_simp] <;> rfl)
    | (intro r hr; simp at hr; cases r <;> simp_all [bkH0.res, rv_simp] <;> rfl)
    | (intro A _ _; simp [bkH0.res, rv_simp])

/-- 647..652 (HK): next coefficient address, product limbs and `tp` cleared, `t4 = a3`. -/
theorem kgHK_spec (s : MachineState) (hpc : s.pc = pcOf 647) (m : Nat) (hm : 1 ≤ m) (hm' : m ≤ 24)
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
def hornK (d : Nat) : Nat := 9 + 24 * hornStepK d

/-- Registers HORN may change. -/
def khornRegs : List Reg := [.x4, .x10, .x11, .x12, .x14, .x15, .x16, .x24, .x29, .x30]

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
    (hf : Frame s0 u (fun _ => False)) {m : Nat} (hm : m < coefs.length) (hl : coefs.length ≤ 24) :
    lim2 (u.getMem (BitVec.ofNat 64 (KCOEF + 16 * m))) (u.getMem (BitVec.ofNat 64 (KCOEF + 16 * m + 8))) =
      (coefs.getD m 0).toNat := by
  have h := hcoef m hm
  rw [hf.get (by simp only [KCOEF]; omega) id, hf.get (by simp only [KCOEF]; omega) id, h.1, h.2, lim2_toNat]

theorem lim3_zero_hi' (a b : BitVec 64) : lim3 a b (BitVec.ofNat 64 0) = lim2 a b := by
  unfold lim3 lim2; simp

/-- One Horner step: HK, the bit loop and HF. -/
theorem khorner_step {s0 : MachineState} {d : Nat} {coefs : List Digest} (hd : d < 2 ^ 10)
    (hlen : coefs.length = 24) (hcoef : DigsAt s0 KCOEF coefs) {m : Nat} (hm : m < 24) {t : MachineState}
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
    (hlen : coefs.length = 24) (hcoef : DigsAt s0 KCOEF coefs) {ret : Nat} (h1 : s0.getReg .x1 = pcOf ret) :
    ∀ m, m < 24 → ∀ t, KHkSt s0 d coefs (m + 1) t →
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

/-- HORN from its entry 642: `familyEval coefs d` (24 coefficients at KCOEF) into `CHAIN + 48`, return to `x1`. -/
theorem khorn_run (s : MachineState) (hpc : s.pc = pcOf 642) {d : Nat} (hd : d < 2 ^ 10)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 d) {coefs : List Digest} (hlen : coefs.length = 24)
    (hcoef : DigsAt s KCOEF coefs) {ret : Nat} (h1 : s.getReg .x1 = pcOf ret) :
    ∃ u, Steps image s (hornK d) (hornK d) u ∧ u.pc = pcOf ret ∧ DigAt u (CHAIN + 48) (familyEval coefs d) ∧
      RegsExcept s u khornRegs ∧ Frame s u (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  obtain ⟨t, st, tpc, t10, t11, t14, t15, tr, tf⟩ := kgH0_spec s hpc
  have ht : KHkSt s d coefs (23 + 1) t := by
    refine ⟨tpc, by rw [tr.get (by simp)]; exact h13, t10, t11, ?_, tr.mono (by simp [khornRegs]), tf⟩
    rw [t14, t15, List.drop_eq_nil_of_le (by omega)]
    rfl
  obtain ⟨u, su, upc, ud, ur, uf⟩ := khorner_loop hd hlen hcoef h1 23 (by norm_num) t ht
  exact ⟨u, Steps.of_eq (st.trans su) (by unfold hornK; ring) (by unfold hornK; ring), upc, ud, ur, uf⟩

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
/-- Memory COEFGEN may change. -/
def CgW (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ (KCOEF ≤ X ∧ X < KCOEF + 384)

structure CgInv (s0 : MachineState) (leaf j : Nat) (acc : List Digest) (t : MachineState) : Prop where
  pc : t.pc = (if j < 12 then pcOf 618 else pcOf 639)
  x14 : t.getReg .x14 = BitVec.ofNat 64 (1 + 2 ^ 32 * (12 * leaf + j))
  x24 : t.getReg .x24 = BitVec.ofNat 64 (KCOEF + 32 * j)
  x29 : t.getReg .x29 = BitVec.ofNat 64 j
  len : acc.length = 2 * j
  coefs : DigsAt t KCOEF acc
  regs : RegsExcept s0 t cgRegs
  frame : Frame s0 t CgW

theorem kcg_body (sk : BitVec 256) {s0 : MachineState} (hp : KPriv sk s0) {leaf : Nat} (hleaf : leaf < 4096)
    {j : Nat} (hj : j < 12) (acc : List Digest) (t : MachineState) (ht : CgInv s0 leaf j acc t) :
    TSim image sk t 21 28 1 1 (do let p ← topSeedPair (12 * leaf + j); pure (acc ++ [p.1, p.2]))
      (CgInv s0 leaf (j + 1)) := by
  have tpc : t.pc = pcOf 618 := by rw [ht.pc, if_pos hj]
  obtain ⟨t1, st1, t1pc, t10, t11, t12, t1a, t1b, t1r, t1f⟩ := kgCG1_spec t tpc
  have hpos : 12 * leaf + j < 2 ^ 32 := by omega
  have t1a' : t1.getMem (BitVec.ofNat 64 (PRIV + 16)) = BitVec.ofNat 64 (hdr0 0 0 0 (12 * leaf + j)) := by
    rw [t1a, ht.x14, hdr0_eq 0 0 0 _ (by norm_num) (by norm_num) (by norm_num) hpos]
  have t1b' : t1.getMem (BitVec.ofNat 64 (PRIV + 24)) = BitVec.ofNat 64 (hdr1 0 0) := by
    rw [t1b, hdr1_eq 0 0 (by norm_num) (by norm_num)]; rfl
  have fr : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → t1.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := by
    intro X hX
    have hX' : X < 2 ^ 64 := by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide)
    rw [t1f.get hX' (by simp only [PRIV] at hX ⊢; omega),
      ht.frame.get hX' (by unfold CgW; simp only [PRIV, SEEDS, KCOEF] at hX ⊢; omega)]
  have hq : hashInput t1 = toQ (privateInput sk (.inl (header 0 0 0 (12 * leaf + j) 0))) := by
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
    (by rw [pc_writeHash, t1pc, pcOf_add4]) j _ hj (by rw [getReg_writeHash, t10])
    (by rw [getReg_writeHash, t1r.get (by simp), ht.x24]) (by rw [getReg_writeHash, t1r.get (by simp), ht.x29])
    (by rw [getReg_writeHash, t1r.get (by simp), ht.x14])
  have ftu : Frame t u (fun X => (X = PRIV + 16 ∨ X = PRIV + 24) ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨
      (KCOEF + 32 * j ≤ X ∧ X < KCOEF + 32 * j + 32)) :=
    (t1f.trans (hwf.trans uf)).mono (fun _ _ h => h)
  refine TSim.pure_steps su ⟨?_, ?_, u24, u29, ?_, ?_, ?_, ?_⟩
  · rw [upc]
  · rw [u14, show 1 + 2 ^ 32 * (12 * leaf + j) + 2 ^ 32 = 1 + 2 ^ 32 * (12 * leaf + (j + 1)) by ring]
  · simp [ht.len]; ring
  · have hold : DigsAt u KCOEF acc := ht.coefs.frame ftu (by rw [ht.len]; simp only [KCOEF]; omega)
      (fun X h1 h2 h => by rw [ht.len] at h2; simp only [PRIV, SEEDS, KCOEF] at h h1 h2; omega)
    have hd1 : DigAt u (KCOEF + 16 * acc.length) (a.extractLsb' 0 128) := by
      rw [ht.len, show KCOEF + 16 * (2 * j) = KCOEF + 32 * j + 8 * 0 by ring]
      refine ⟨by rw [umem 0 (by norm_num)]; exact hlo.1, ?_⟩
      rw [show KCOEF + 32 * j + 8 * 0 + 8 = KCOEF + 32 * j + 8 * 1 by ring, umem 1 (by norm_num)]
      exact hlo.2
    have hd2 : DigAt u (KCOEF + 16 * (acc ++ [a.extractLsb' 0 128]).length) (a.extractLsb' 128 128) := by
      rw [List.length_append, ht.len, List.length_singleton,
        show KCOEF + 16 * (2 * j + 1) = KCOEF + 32 * j + 8 * 2 by ring]
      refine ⟨by rw [umem 2 (by norm_num)]; exact hhi.1, ?_⟩
      rw [show KCOEF + 32 * j + 8 * 2 + 8 = KCOEF + 32 * j + 8 * 3 by ring, umem 3 (by norm_num),
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

/-- COEFGEN from its entry 612 (called from 157 with `ra = 158`): `topCoefs leaf` into `KCOEF`, `s3 = 0`. -/
theorem kcoefgen_tsim (sk : BitVec 256) {s : MachineState} (hpc : s.pc = pcOf 612) {leaf : Nat}
    (hleaf : leaf < 4096) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (hp : KPriv sk s)
    (h1 : s.getReg .x1 = pcOf 158) :
    TSim image sk s 260 347 12 12 (topCoefs leaf)
      (fun coefs t => t.pc = pcOf 158 ∧ coefs.length = 24 ∧ DigsAt t KCOEF coefs ∧
        t.getReg .x19 = BitVec.ofNat 64 0 ∧ RegsExcept s t (cgRegs ++ [.x19]) ∧ Frame s t CgW) := by
  obtain ⟨t0, st0, t0pc, t014, t024, t029, t0r, t0f⟩ := kgCG0_spec s hpc leaf h18
  have h0 : CgInv s leaf 0 [] t0 := by
    refine ⟨by rw [t0pc]; rfl, by rw [t014]; rfl, by rw [t024], t029, rfl, DigsAt.nil _ _,
      t0r.mono (by simp [cgRegs]), t0f.mono (fun _ _ h => h.elim)⟩
  have hfold := TSim.foldlM_range (image := image) (sk := sk) 12
    (fun acc j => do let p ← topSeedPair (12 * leaf + j); pure (acc ++ [p.1, p.2])) []
    (CgInv s leaf) (fun _ => 21) (fun _ => 28) (fun _ => 1) (fun _ => 1)
    (fun j hj acc t ht => kcg_body sk hp hleaf hj acc t ht) h0
  refine (TSim.steps st0 (TSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0) (f := Pure.pure) hfold
    (fun coefs t ht => ?_))).of_eq (by rw [bind_pure]; rfl) ?_ ?_ ?_ ?_
  · obtain ⟨u, su, upc, u19, ur, uf⟩ := kgCG3_spec t (by rw [ht.pc]; rfl) 158
      (by rw [ht.regs.get (by simp [cgRegs]), h1])
    refine TSim.pure_steps su ⟨upc, by rw [ht.len], ht.coefs.frame uf (by rw [ht.len]; simp only [KCOEF]; omega)
      (fun _ _ _ h => h), u19, (ht.regs.trans ur), (ht.frame.trans uf).mono (fun _ _ h => by simp_all)⟩
  all_goals simp only [sumTo_const]

/-! ## The top leaf -/
macro "tl_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, KCOEF] at *); omega))

/-- Registers the top-leaf routine may change. -/
def tRegs : List Reg := leafRegs ++ [.x4, .x13, .x14, .x15, .x16, .x24]
/-- Memory the top-leaf routine may change: the leaf writes plus the coefficient buffer. -/
def TW (A : LeafArgs) (X : Nat) : Prop := LeafW A X ∨ (KCOEF ≤ X ∧ X < KCOEF + 384)

/-- The keygen top-leaf arguments: signature-free, no digits, buffers clear of KCOEF. -/
structure TopArgs (A : LeafArgs) : Prop where
  so : A.so = false
  dig : A.digits = []
  cv : A.valp + 16 * A.n ≤ KCOEF ∨ KCOEF + 384 ≤ A.valp
  cd : A.dest + 16 ≤ KCOEF ∨ KCOEF + 384 ≤ A.dest
  cdig : A.digp + A.n ≤ KCOEF ∨ KCOEF + 384 ≤ A.digp

structure TInv (s0 : MachineState) (A : LeafArgs) (coefs : List Digest) (j : Nat) (st : List Digest × List Digest)
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
  ends : ∀ c < j, DigAt t (slot A.lay c) (st.1.getD c 0)
  vals : DigsAt t A.valp st.2
  coef : DigsAt t KCOEF coefs

/-- Registers changed between the loop head and the chain routine's return. -/
def preRegs : List Reg :=
  [.x1, .x4, .x6, .x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x20, .x21, .x24, .x28, .x29, .x30]

section top
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : LeafPre sk s0 A) (hta : TopArgs A)
  {coefs : List Digest} (hcl : coefs.length = 24)
include hpre hta hcl

theorem ktop_post {j : Nat} (hj : j < A.n) {st : List Digest × List Digest} {t u : MachineState}
    (ht : TInv s0 A coefs j st t) (hupc : u.pc = pcOf 196) (hur : RegsExcept t u preRegs)
    (huf : Frame t u (fun X => (X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X))
    (v last : Digest) (hv : DigAt u (A.valp + 16 * j) v) (hl : DigAt u (CHAIN + 48) last) :
    ∃ w, Steps image u 16 16 w ∧ w.pc = pcOf 158 ∧ TInv s0 A coefs (j + 1) (st.1 ++ [last], st.2 ++ [v]) w := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hpre.top0.1]; rfl
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
  obtain ⟨u4, st4, u4pc, u4x28, u4r, u4f⟩ := sub82_spec subAt_keygen u3 u3pc (16 * j + 16) u3x28
  obtain ⟨u5, st5, u5pc, u5a, u5b, u5r, u5f⟩ := sub83_spec subAt_keygen u4 u4pc (16 * j + 16 + 16) (by omega)
    (by sc_omega) u4x28
  have hs : slot A.lay j = LEAFPK + (16 * j + 16 + 16) := by simp only [slot, if_pos h0]; ring
  have hl4 := hl1.frame (u3f.trans u4f) (by decide) (by simp) (by simp)
  have u5s : DigAt u5 (slot A.lay j) last := ⟨by rw [hs, u5a]; exact hl4.1, by rw [hs, u5b]; exact hl4.2⟩
  have u5f' : Frame u1 u5 (fun X => slot A.lay j ≤ X ∧ X < slot A.lay j + 16) :=
    ((u3f.trans u4f).trans u5f).mono (fun X _ h => by rw [hs]; simp at h ⊢; omega)
  have r19' : u5.getReg .x19 = BitVec.ofNat 64 j := by
    rw [u5r.get (by simp), u4r.get (by simp), u3r.get (by simp)]; exact r19
  have r23' : u5.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * j) := by
    rw [u5r.get (by simp), u4r.get (by simp), u3r.get (by simp), u1r.get (by simp), hur.get (by simp [preRegs])]
    exact ht.x23
  obtain ⟨w, st6, wpc, wx19, wx23, wr, wf⟩ := sub92_spec subAt_keygen u5 u5pc j (A.valp + 16 * j) r19' r23'
  have hsl : LEAFPK ≤ slot A.lay j ∧ slot A.lay j + 16 ≤ LEAFPK + 16 * (A.n + 2) :=
    ⟨slot_ge A.lay j, slot_lt A.lay hj⟩
  have fuw : Frame u w (fun X => slot A.lay j ≤ X ∧ X < slot A.lay j + 16) :=
    ((u1f.trans u5f').trans wf).mono (fun X _ h => by
      rcases h with (h | h) | h
      · exact h.elim
      · exact h
      · exact h.elim)
  have ftw : Frame t w (fun X => ((X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X) ∨
      (slot A.lay j ≤ X ∧ X < slot A.lay j + 16)) := huf.trans fuw
  refine ⟨w, Steps.of_eq (st1.trans ((st3.trans (st4.trans st5)).trans st6)) (by omega) (by omega), wpc,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
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
    · exact Or.inl (LeafW_of_slot hj h)
  · have := slot_hdr A.lay j
    rw [ftw.get (by decide) (by unfold ChainW; tl_omega), ht.lh16]
  · have := slot_hdr A.lay j
    rw [ftw.get (by decide) (by unfold ChainW; tl_omega), ht.lh24]
  · simp [ht.elen]
  · simp [ht.vlen]
  · intro c hc
    by_cases hcj : c = j
    · subst hcj
      have hl5 : DigAt w (slot A.lay c) last := u5s.frame wf (by tl_omega) (by simp) (by simp)
      simpa [List.getD_eq_getElem?_getD, ht.elen] using hl5
    · have hc' : c < j := by omega
      have hsc := slot_lt A.lay (show c < A.n by omega)
      have hsc0 := slot_ge A.lay c
      have hd := slot_disj A.lay hcj
      have hnot : ∀ X, slot A.lay c ≤ X → X < slot A.lay c + 16 →
          ¬ (((X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X) ∨
            (slot A.lay j ≤ X ∧ X < slot A.lay j + 16)) := by
        intro X h1 h2 h
        unfold ChainW at h
        tl_omega
      have h2 : DigAt w (slot A.lay c) (st.1.getD c 0) :=
        (ht.ends c hc').frame ftw (by tl_omega) (hnot _ le_rfl (by omega)) (hnot _ (by omega) (by omega))
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [ht.elen]; omega : c < st.1.length)] using h2
  · have hsj0 := slot_ge A.lay j
    have hvw : DigAt w (A.valp + 16 * j) v := hv.frame fuw (by omega) (by tl_omega) (by tl_omega)
    have hvals : DigsAt w A.valp st.2 :=
      ht.vals.frame ftw (by rw [ht.vlen]; omega) (fun X h1 h2 h => by
        rw [ht.vlen] at h2
        unfold ChainW at h
        tl_omega)
    exact hvals.snoc (by rw [ht.vlen]; exact hvw)
  · exact ht.coef.frame ftw (by rw [hcl]; tl_omega) (fun X h1 h2 h => by
      rw [hcl] at h2
      have := slot_ge A.lay j
      unfold ChainW at h
      tl_omega)
end top

/-- The chain loop body of `buildLeafTop leaf []` (chain `i`, family seed). -/
def topBody (leaf : Nat) (coefs : List Digest) (state : List Digest × List Digest) (i : Nat) :
    T3.M (List Digest × List Digest) := do
  let digit := ([] : List Nat).getD i 0
  let value ← chain 0 0 leaf i 0 digit (topSeed coefs i)
  if false then return (state.1, state.2 ++ [value])
  let last ← chain 0 0 leaf i digit (maxDigit 0 i - digit) value
  pure (state.1 ++ [last], state.2 ++ [value])

theorem topBody_eq (leaf : Nat) (coefs : List Digest) (st : List Digest × List Digest) (i : Nat) :
    topBody leaf coefs st i =
      (do let v ← chain 0 0 leaf i 0 0 (topSeed coefs i)
          let last ← chain 0 0 leaf i 0 (maxDigit 0 i - 0) v
          pure (v, last)) >>= fun r => pure (st.1 ++ [r.2], st.2 ++ [r.1]) := by
  simp only [topBody, List.getD_nil, bind_assoc, pure_bind, Bool.false_eq_true, if_false]

/-- Steps of one chain iteration of the top leaf. -/
def titerK (j : Nat) : Nat := 11 + (if j < 51 then 3 else 5) + hornK (j + 1) + (rungK 0 * maxDigit 0 j + 10) + 16
/-- Cycles of one chain iteration of the top leaf. -/
def titerC (j : Nat) : Nat := 11 + (if j < 51 then 3 else 5) + hornK (j + 1) + (rungC 0 * maxDigit 0 j + 10) + 16

section top
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : LeafPre sk s0 A) (hta : TopArgs A)
  {coefs : List Digest} (hcl : coefs.length = 24)
include hpre hta hcl

theorem ktop_iter {j : Nat} (hj : j < 54) {st : List Digest × List Digest} {t : MachineState}
    (ht : TInv s0 A coefs j st t) (hpc : t.pc = pcOf 158) :
    TSim image sk t (titerK j) (titerC j) (maxDigit 0 j) (maxDigit 0 j) (topBody A.leaf coefs st j)
      (fun st' u => u.pc = pcOf 158 ∧ TInv s0 A coefs (j + 1) st' u) := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hpre.top0.1]; rfl
  have h0 := hpre.top0
  have hvs := hpre.hvs
  have hvb := hpre.hv
  have hv8 := hpre.hv8
  have hds := hpre.hds
  have hdv := hpre.hdv
  have hcv := hta.cv
  have hcd := hta.cd
  have g : ∀ r, r ∉ tRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub41_spec subAt_keygen t hpc j 54 (by omega) (by omega) ht.x19
    (by rw [g _ (by simp [tRegs, leafRegs]), hpre.x26, hn])
  rw [if_pos hj] at t1pc
  obtain ⟨t2, st2, t2pc, t2x1, t2x13, t2r, t2f⟩ := kg159_spec t1 t1pc j (by rw [t1r.get (by simp)]; exact ht.x19)
  have hc2 : DigsAt t2 KCOEF coefs :=
    ht.coef.frame (t1f.trans t2f) (by rw [hcl]; tl_omega) (fun _ _ _ h => by simp_all)
  obtain ⟨t3, st3, t3pc, t3seed, t3r, t3f⟩ := khorn_run t2 t2pc (d := j + 1) (by omega) t2x13 hcl hc2 t2x1
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
  have hbyte : t5.getByte (BitVec.ofNat 64 (A.digp + j)) = BitVec.ofNat 8 0 := by
    rw [t5f.getByte (by omega) (fun h => h), f14.getByte (by omega) (fun h => hw (by
        simp only [LeafW, CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at h ⊢; omega)),
      ht.frame.getByte (by omega) (fun h => by
        rcases h with h | h
        · exact hw h
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
  have hL : ∀ X, (X = CHAIN ∨ X = CHAIN + 8 ∨ X = CHAIN + 32 ∨ X = CHAIN + 40) →
      t11.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := by
    intro X hX
    have hX' : X < 2 ^ 64 := by rcases hX with h | h | h | h <;> (rw [h]; decide)
    rw [f111.get hX' (by simp only [CHAIN] at hX ⊢; omega), ht.frame.get hX' (fun h => by
      rcases h with h | h
      · unfold LeafW at h
        rw [if_pos h0.1] at h
        tl_omega
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
      hroute := by have := hpre.hroute; rw [h0.1, h0.2] at this; simpa using this
      hleaf := by have := hpre.hleafHeight; rw [h0.1] at this; exact this
      hcap := Nat.zero_le _
      he := by unfold maxDigit; split_ifs <;> omega
      hv8 := by omega
      hv := by omega
      hvc := by tl_omega
      z0 := by rw [hL _ (by simp), hpre.z0]
      z8 := by rw [hL _ (by simp), hpre.z8]
      z32 := by rw [hL _ (by simp), hpre.z32]
      z40 := by rw [hL _ (by simp), hpre.z40] }
  have hseed : DigAt t11 (CHAIN + 48) (topSeed coefs j) :=
    t3seed.frame (((((((t4f.trans t5f).trans t6f).trans t7f).trans t8f).trans t9f).trans t10f).trans t11f)
      (by decide) (by simp) (by simp)
  have hch := chainRun_tsim subAt_keygen sk hcp t11pc (topSeed coefs j) hseed
  rw [topBody_eq]
  refine (TSim.steps (((((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans
    st8).trans st9).trans (st10.trans st11)) (TSim.bind (k₂ := 16) (c₂ := 16) (n₂ := 0) (b₂ := 0) hch
    (fun r u hu => ?_))).of_eq rfl ?_ ?_ (by omega) (by omega)
  · obtain ⟨hupc, hv, hl, hur, huf⟩ := hu
    obtain ⟨w, stw, wpc, hw⟩ := ktop_post sk hpre hta hcl (j := j) (by omega) ht hupc
      ((e111.trans hur).mono (by simp [preRegs, chainRegs])) ((f111.trans huf).mono (fun _ _ h => h))
      r.1 r.2 hv hl
    exact TSim.pure_steps stw ⟨wpc, hw⟩
  · unfold titerK; omega
  · unfold titerC; omega
end top

section top
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : LeafPre sk s0 A) (hta : TopArgs A)
  {coefs : List Digest} (hcl : coefs.length = 24)
include hpre hta hcl

omit hcl in
/-- Leaf exit (158 with all 54 chains done): leaf hash of the chain ends into `dest`, return. -/
theorem ktop_exit {st : List Digest × List Digest} {t : MachineState} (ht : TInv s0 A coefs 54 st t)
    (hpc : t.pc = pcOf 158) :
    TSim image sk t 19 (18 + 8 * leafBlocks A.lay) 1 (leafBlocks A.lay)
      (leafHash 0 0 A.leaf st.1 >>= fun root => pure (root, st.2))
      (fun r u => u.pc = pcOf A.ret ∧ DigAt u A.dest r.1 ∧ DigsAt u A.valp r.2 ∧ RegsExcept s0 u tRegs ∧
        Frame s0 u (TW A)) := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hpre.top0.1]; rfl
  have h0 := hpre.top0
  have g : ∀ r, r ∉ tRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r26 : t.getReg .x26 = BitVec.ofNat 64 54 := by
    rw [g _ (by simp [tRegs, leafRegs]), hpre.x26, hn]
  have r31 : t.getReg .x31 = BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [g _ (by simp [tRegs, leafRegs]), hpre.x31, hta.so]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub41_spec subAt_keygen t hpc 54 54 (by omega) (by omega) ht.x19 r26
  rw [if_neg (lt_irrefl _)] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub95_spec subAt_keygen t1 t1pc false (by rw [t1r.get (by simp)]; exact r31)
  simp only [Bool.false_eq_true, if_false] at t2pc
  have e12 : RegsExcept t t2 [] := (t1r.trans t2r).mono (by simp)
  have f12 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  obtain ⟨t3, st3, t3pc, t3x10, t3x11, t3x12, t3r, t3f⟩ := sub96_spec subAt_keygen t2 t2pc 54 (Or.inl rfl)
    (by rw [e12.get (by simp)]; exact r26)
  have r13 : RegsExcept t t3 [.x6, .x10, .x11, .x12] := (e12.trans t3r).mono (by simp)
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
    have hall : DigsAt t3 (LEAFPK + 32) st.1 := by
      intro c hc
      have hsl := slot_lt A.lay (show c < A.n by omega)
      simp only [slot, if_pos h0.1, LEAFPK] at hsl
      have := (ht.ends c (by omega)).frame f13 (by simp only [slot, if_pos h0.1, LEAFPK]; omega) (by simp)
        (by simp)
      simp only [slot, if_pos h0.1] at this
      rw [show LEAFPK + 32 + 16 * c = LEAFPK + 16 * (c + 2) by ring]
      exact this
    have hhd : t3.readWords (BitVec.ofNat 64 (LEAFPK + 16)) 2 =
        [T3.hyperWord A.lay.val (A.tree * 2 ^ T3.height A.lay + A.leaf), 0] := by
      rw [readWords_two, f13.get (by decide) (by simp), f13.get (by decide) (by simp), ht.lh16,
        show LEAFPK + 16 + 8 = LEAFPK + 24 from rfl, ht.lh24]
    have hnw : ∀ X, (X = LEAFPK ∨ X = LEAFPK + 8) → ¬ TW A X := by
      intro X hX hw'
      rcases hw' with hw' | hw'
      · unfold LeafW at hw'
        rw [if_pos h0.1] at hw'
        tl_omega
      · tl_omega
    have hz : t3.readWords (BitVec.ofNat 64 LEAFPK) 2 = [0, 0] := by
      rw [readWords_two, f13.get (by decide) (by simp), f13.get (by decide) (by simp),
        ht.frame.get (by decide) (hnw _ (Or.inl rfl)),
        ht.frame.get (by decide) (hnw _ (Or.inr rfl)), hpre.zhead.1, hpre.zhead.2]
    have hb : 8 * leafBlocks A.lay = 2 + (2 + 2 * st.1.length) := by
      simp only [hlen, leafBlocks, show chainCount A.lay = A.n from rfl, hn]
    rw [hb, readWords_add, readWords_add, hz, hhd,
      show LEAFPK + 8 * 2 + 8 * 2 = LEAFPK + 32 from rfl, hall.words, List.append_assoc]
  have hl := leafInput_length A h0.1 st.1 hlen
  have hnb : leafBlocks A.lay = 14 := by unfold leafBlocks; rw [show chainCount A.lay = A.n from rfl, hn]
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
  have hlh : leafHash 0 0 A.leaf st.1 = T3.shortHash (T3.leafInput A.lay A.tree A.leaf st.1) := by
    rw [h0.1, h0.2]; rfl
  rw [hlh]
  refine (TSim.steps (st1.trans (st2.trans st3)) (TSim.shortHash_bind (k := 7) (c := 7) (n := 0) (b := 0)
    (f := fun root => pure (root, st.2)) (fetch_sub105 subAt_keygen t3 t3pc) h5 hv hq (fun a => ?_))).of_eq rfl
    (by omega) (by rw [hblk]; omega) (by omega) (by rw [hblk]; omega)
  have hdb := hpre.hd
  have hd8 := hpre.hd8
  have hwf := Frame.writeHash t3 a LOUT t3x12 (by decide)
  obtain ⟨u2, st5, u2pc, u2a, u2b, u2r, u2f⟩ := sub106_spec subAt_keygen (writeHash t3 a)
    (by rw [pc_writeHash, t3pc, pcOf_add4]) A.dest hd8 hdb (by tl_omega)
    (by rw [getReg_writeHash, r13.get (by simp), g _ (by simp [tRegs, leafRegs]), hpre.x25])
  have hlo := DigAt.writeHash_lo t3 a LOUT t3x12 (by decide)
  obtain ⟨u3, st6, u3pc, u3r, u3f⟩ := sub112_spec subAt_keygen u2 u2pc A.ret
    (by rw [u2r.get (by simp), getReg_writeHash, r13.get (by simp)]; exact ht.x3)
  have fall : Frame t u3 (fun X => (LOUT ≤ X ∧ X < LOUT + 32) ∨ (X = A.dest ∨ X = A.dest + 8)) :=
    ((f13.trans hwf).trans (u2f.trans u3f)).mono (fun X _ h => by
      rcases h with (h | h) | (h | h)
      · exact h.elim
      · left; exact h
      · right; exact h
      · exact h.elim)
  refine TSim.pure_steps (st5.trans st6) ⟨u3pc, ?_, ?_, ?_, ?_⟩
  · have hd2 : DigAt u2 A.dest (a.extractLsb' 0 128) := ⟨u2a.trans hlo.1, by rw [u2b]; exact hlo.2⟩
    exact hd2.frame u3f (by omega) (by simp) (by simp)
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
end top

theorem buildLeafTop_eq (leaf : Nat) : buildLeafTop leaf [] = (do
    let coefs ← topCoefs leaf
    let state ← (List.range 54).foldlM (topBody leaf coefs) ([], [])
    leafHash 0 0 leaf state.1 >>= fun root => pure (root, state.2)) := rfl

/-- Steps of a keygen top leaf. -/
def topLeafK : Nat := 14 + (260 + (sumTo titerK 54 + 19))
/-- Cycles of a keygen top leaf. -/
def topLeafC : Nat := 14 + (347 + (sumTo titerC 54 + (18 + 8 * 14)))
/-- Hash calls of a keygen top leaf. -/
def topLeafN : Nat := 12 + (sumTo (fun j => maxDigit 0 j) 54 + 1)
/-- Compression blocks of a keygen top leaf. -/
def topLeafB : Nat := 12 + (sumTo (fun j => maxDigit 0 j) 54 + 14)

section top
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : LeafPre sk s0 A) (hta : TopArgs A)
include hpre hta

/-- The keygen top leaf (entry 144, return to `A.ret`) refines `buildLeafTop A.leaf []` with exact counts. -/
theorem buildLeafTop_tsim (hpc : s0.pc = pcOf 144) :
    TSim image sk s0 topLeafK topLeafC topLeafN topLeafB (buildLeafTop A.leaf [])
      (fun r t => t.pc = pcOf A.ret ∧ DigAt t A.dest r.1 ∧ DigsAt t A.valp r.2 ∧ RegsExcept s0 t tRegs ∧
        Frame s0 t (TW A)) := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hpre.top0.1]; rfl
  have h0 := hpre.top0
  have hlay : A.lay.val < 256 := by have := A.lay.isLt; omega
  have hnb : leafBlocks A.lay = 14 := by unfold leafBlocks; rw [show chainCount A.lay = A.n from rfl, hn]
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
  have hcg := kcoefgen_tsim sk t1pc hleaf (by rw [t1r.get (by simp)]; exact hpre.x18) hp t1x1
  rw [buildLeafTop_eq]
  refine (TSim.steps st1 (TSim.bind (k₂ := sumTo titerK 54 + 19)
    (c₂ := sumTo titerC 54 + (18 + 8 * leafBlocks A.lay)) (n₂ := sumTo (fun j => maxDigit 0 j) 54 + 1)
    (b₂ := sumTo (fun j => maxDigit 0 j) 54 + leafBlocks A.lay) hcg (fun coefs t ht => ?_))).of_eq rfl rfl
    (by rw [hnb]; rfl) rfl (by rw [hnb]; rfl)
  obtain ⟨tpc, hcl, hcoef, t19, tr, tf⟩ := ht
  have hinv : TInv s0 A coefs 0 ([], []) t := by
    refine ⟨t19, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, fun c hc => absurd hc (by omega), DigsAt.nil _ _, hcoef⟩
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
        · right; exact h
    · rw [tf.get (by decide) (by unfold CgW; simp only [PRIV, SEEDS, KCOEF, LEAFPK]; omega), t1l16, h0.2]; simp
    · rw [tf.get (by decide) (by unfold CgW; simp only [PRIV, SEEDS, KCOEF, LEAFPK]; omega), t1l24]
  exact TSim.bind (TSim.foldlM_range 54 (topBody A.leaf coefs) ([], [])
    (fun j st t => t.pc = pcOf 158 ∧ TInv s0 A coefs j st t) titerK titerC (fun j => maxDigit 0 j)
    (fun j => maxDigit 0 j) (fun j hj st t ht => ktop_iter sk hpre hta hcl hj ht.2 ht.1) ⟨tpc, hinv⟩)
    (fun st t ht => ktop_exit sk hpre hta ht.2 ht.1)
end top

theorem topLeaf_counts : topLeafK = 115508 ∧ topLeafC = 117281 ∧ topLeafN = 238 ∧ topLeafB = 251 := by
  decide

end SigGolfCandidate.T3M.Keygen
