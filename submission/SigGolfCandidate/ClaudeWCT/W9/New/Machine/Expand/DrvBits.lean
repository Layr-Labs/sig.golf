import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Defs
import SigGolfCandidate.T3M.Search.DigestSearch
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Base

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIG NBUF ENC)
set_option autoImplicit false
set_option maxRecDepth 8192
abbrev FLEAF : Nat := 0x202C0
abbrev FOREST : Nat := 0x20320
abbrev FOUT : Nat := 0x203A0
theorem shl_shr_33 (w : BitVec 64) : w <<< 33 >>> 33 = BitVec.ofNat 64 (w.toNat % 2 ^ 31) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 64 = 2 ^ 31 * 2 ^ 33 by norm_num, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (by positivity)]
  have := Nat.mod_lt w.toNat (show 0 < 2 ^ 31 by positivity)
  omega
section blocks
variable (s : MachineState)
theorem s0_spec (hpc : s.pc = pcOf 0) :
    ∃ t, Steps image s 30 30 t ∧ t.pc = pcOf 30 ∧ t.getReg .x5 = 0 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 0x800) = s.getMem (BitVec.ofNat 64 0x7000) ∧
      t.getMem (BitVec.ofNat 64 0x808) = s.getMem (BitVec.ofNat 64 0x7008) ∧
      t.getMem (BitVec.ofNat 64 DIG) = s.getMem (BitVec.ofNat 64 0x7000) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 8)) = s.getMem (BitVec.ofNat 64 0x7008) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 32)) = s.getMem (BitVec.ofNat 64 0x40) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 40)) = s.getMem (BitVec.ofNat 64 0x48) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 48)) = s.getMem (BitVec.ofNat 64 0x50) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 56)) = s.getMem (BitVec.ofNat 64 0x58) ∧
      RegsExcept s t [.x5, .x6, .x7, .x19, .x29, .x30] ∧
      Frame s t (fun A => A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨
        A = DIG + 48 ∨ A = DIG + 56) := by
  refine ⟨_, symRun_sound eblk_0 codeAt_0 s hpc (by simp [eblk_0.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_0.res, E.eval]
  · simp [eblk_0.res, rv_simp]
  · simp [eblk_0.res, rv_simp]
  iterate 8
    · simp only [Result.toState_getMem, eblk_0.res, DIG]
      t3n []
  · ex_regs eblk_0.res
  · intro A hA hn
    simp only [DIG] at hn
    simp only [Result.toState_getMem, eblk_0.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem s49_spec (hpc : s.pc = pcOf 49) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 16 16 t ∧ t.pc = pcOf 65 ∧
      t.getReg .x9 = BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 NBUF)).toNat % 2 ^ 31) ∧
      t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 NBUF)).toNat % 2 ^ 31) ∧
      t.getMem (BitVec.ofNat 64 0x810) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x810)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x2 = BitVec.ofNat 64 0x22000 ∧ t.getReg .x18 = BitVec.ofNat 64 0 ∧
      t.getReg .x22 = BitVec.ofNat 64 0xC40 ∧ t.getReg .x8 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x2, .x8, .x9, .x18, .x22, .x28] ∧ Frame s t (fun A => A = IDXV ∨ A = 0x810) := by
  refine ⟨_, symRun_sound eblk_49 codeAt_49 s hpc (by simp [eblk_49.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_49.res, E.eval]
  · simp only [Result.toState_getReg, eblk_49.res, rv_simp, NBUF]
    t3n []
    rw [shl_shr_33]
    norm_num
  · simp only [Result.toState_getMem, eblk_49.res, NBUF, IDXV]
    t3n []
    rw [shl_shr_33]
    norm_num
  · simp only [Result.toState_getMem, eblk_49.res]
    t3n [h19]
  · simp [eblk_49.res, rv_simp]
  · simp [eblk_49.res, rv_simp]
  · simp [eblk_49.res, rv_simp]
  · simp [eblk_49.res, rv_simp]
  · ex_regs eblk_49.res
  · intro A hA hn
    simp only [IDXV] at hn
    simp only [Result.toState_getMem, eblk_49.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem s215_spec (hpc : s.pc = pcOf 215) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 216 ∧ t.getReg .x13 = s.getReg .x18 ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_215 codeAt_215 s hpc (by simp [eblk_215.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_215.res, E.eval]
  · simp [eblk_215.res, rv_simp]
  · ex_regs eblk_215.res
  · intro A _ _; simp [eblk_215.res, rv_simp]
theorem s216_spec (hpc : s.pc = pcOf 216) (j : Nat) (hj : j ≤ 115) (h13 : s.getReg .x13 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if 115 ≤ j then pcOf 228 else pcOf 218) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_216 codeAt_216 s hpc (by simp [eblk_216.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_216.res, E.eval, CmpOp.eval, rebase, rv_simp, h13]
    rw [ex_slt j 115 (by omega) (by omega)]
    by_cases h : 115 ≤ j
    · simp [h, show ¬ j < 115 by omega]
    · simp [h, show j < 115 by omega]
  · ex_regs eblk_216.res
  · intro A _ _; simp [eblk_216.res, rv_simp]
theorem slot_addr (j : Nat) :
    BitVec.ofNat 64 j <<< ((4#64 : BitVec 64).toNat % 64) + 29024#64 = BitVec.ofNat 64 (0x7160 + 16 * j) := by
  rw [show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl, ofNat_shl]
  apply BitVec.eq_of_toNat_eq; simp; omega
theorem s218_spec (hpc : s.pc = pcOf 218) (j : Nat) (hj : j < 115) (h13 : s.getReg .x13 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 6 6 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (0x7160 + 16 * j)) = 0 then pcOf 224 else pcOf 354) ∧
      t.getReg .x28 = BitVec.ofNat 64 (0x7160 + 16 * j) ∧
      RegsExcept s t [.x6, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_218 codeAt_218 s hpc ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_218.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h13, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    rw [slot_addr]
    exact ex_valid _ (by omega) (by omega)
  · simp only [Result.toState_pc, eblk_218.res, E.eval, CmpOp.eval, rebase, rv_simp, h13]
    rw [slot_addr]
    by_cases h : s.getMem (BitVec.ofNat 64 (0x7160 + 16 * j)) = 0
    · simp [h]
    · simp [h]
  · simp only [Result.toState_getReg, eblk_218.res, rv_simp, h13]
    t3n []
    congr 1; omega
  · ex_regs eblk_218.res
  · intro A _ _; simp [eblk_218.res, rv_simp]
theorem s224_spec (hpc : s.pc = pcOf 224) (j : Nat) (hj : j < 115)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (0x7160 + 16 * j)) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (0x7160 + 16 * j + 8)) = 0 then pcOf 226 else pcOf 354) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_224 codeAt_224 s hpc ?_, ?_, ?_, ?_⟩
  · simp only [eblk_224.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h28, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    exact ex_valid _ (by omega) (by omega)
  · simp only [Result.toState_pc, eblk_224.res, E.eval, CmpOp.eval, rebase, rv_simp, h28, ofNat_add_ofNat]
    by_cases h : s.getMem (BitVec.ofNat 64 (0x7160 + 16 * j + 8)) = 0
    · simp [h]
    · simp [h]
  · ex_regs eblk_224.res
  · intro A _ _; simp [eblk_224.res, rv_simp]
theorem s226_spec (hpc : s.pc = pcOf 226) (j : Nat) (hj : j < 115) (h13 : s.getReg .x13 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 216 ∧ t.getReg .x13 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_226 codeAt_226 s hpc (by simp [eblk_226.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_226.res, E.eval]
  · simp only [Result.toState_getReg, eblk_226.res, rv_simp, h13, ofNat_add_ofNat]
  · ex_regs eblk_226.res
  · intro A _ _; simp [eblk_226.res, rv_simp]
theorem s228_spec (hpc : s.pc = pcOf 228) (index : Nat) (hi : index < 2 ^ 31)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf 240 ∧
      t.getMem (BitVec.ofNat 64 (FOREST + 16)) = BitVec.ofNat 64 2817 ∧
      t.getMem (BitVec.ofNat 64 (FOREST + 24)) = BitVec.ofNat 64 index ∧
      t.getReg .x10 = BitVec.ofNat 64 FOREST ∧ t.getReg .x11 = BitVec.ofNat 64 128 ∧
      t.getReg .x12 = BitVec.ofNat 64 FOUT ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = FOREST + 16 ∨ A = FOREST + 24) := by
  refine ⟨_, symRun_sound eblk_228 codeAt_228 s hpc (by simp [eblk_228.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_228.res, E.eval]
  · simp only [Result.toState_getMem, eblk_228.res, FOREST]
    t3n []
  · simp only [Result.toState_getMem, eblk_228.res, FOREST]
    t3n [h9]
  · simp [eblk_228.res, rv_simp]
  · simp [eblk_228.res, rv_simp]
  · simp [eblk_228.res, rv_simp]
  · ex_regs eblk_228.res
  · intro A hA hn
    simp only [FOREST] at hn
    simp only [Result.toState_getMem, eblk_228.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem fetch_240 (hpc : s.pc = pcOf 240) : fetch image s = some (.base .ECALL) :=
  (codeAt_240.fetch s hpc).trans rfl
theorem s241_spec (hpc : s.pc = pcOf 241) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = pcOf 249 ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 FOUT) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (FOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧ Frame s t (fun A => A = ENC ∨ A = ENC + 8) := by
  refine ⟨_, symRun_sound eblk_241 codeAt_241 s hpc (by simp [eblk_241.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_241.res, E.eval]
  · simp only [Result.toState_getMem, eblk_241.res, ENC, FOUT]
    t3n []
  · simp only [Result.toState_getMem, eblk_241.res, ENC, FOUT]
    t3n []
  · ex_regs eblk_241.res
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, eblk_241.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
end blocks
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Expand (IDXV)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192
theorem extractLsb'_256_toNat (a : BitVec 256) (w : Nat) :
    (a.extractLsb' (64 * w) 64).toNat = a.toNat / 2 ^ (64 * w) % 2 ^ 64 := by
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem mod_div_mod (X k m : Nat) (h : k + m ≤ 64) : X % 2 ^ 64 / 2 ^ k % 2 ^ m = X / 2 ^ k % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < m
  · simp only [hi, decide_true, Bool.true_and]
    have : i + k < 64 := by omega
    simp [this]
  · simp [hi]
theorem field_toNat (a : BitVec 256) (w sh : Nat) (h : sh + 21 ≤ 64) :
    ((a.extractLsb' (64 * w) 64 >>> sh >>> 7) &&& 16383#64).toNat = a.toNat / 2 ^ (64 * w + sh + 7) % 2 ^ 14 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, extractLsb'_256_toNat,
    show (16383#64).toNat = 2 ^ 14 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add, mod_div_mod _ _ _ (by omega),
    Nat.div_div_eq_div_mul, ← Nat.pow_add]
  ring_nf
theorem field_toNat0 (a : BitVec 256) (w : Nat) :
    ((a.extractLsb' (64 * w) 64 >>> 7) &&& 16383#64).toNat = a.toNat / 2 ^ (64 * w + 7) % 2 ^ 14 := by
  have := field_toNat a w 0 (by omega)
  simpa using this
theorem gate21_toNat (a : BitVec 256) :
    ((a.extractLsb' 192 64) >>> 43).toNat = a.toNat / 2 ^ 235 % 2 ^ 21 := by
  rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 64 = 2 ^ 43 * 2 ^ 21 by norm_num, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul,
    ← pow_add]
theorem index_eq (a : BitVec 256) :
    a.extractLsb' 0 64 <<< 33 >>> 33 = BitVec.ofNat 64 (a.toNat % 2 ^ 31) := by
  rw [SigGolfCandidate.T3M.Expand.shl_shr_33]
  congr 1
  rw [show (0 : Nat) = 64 * 0 from rfl, extractLsb'_256_toNat]
  rw [show 64 * 0 = 0 from rfl, pow_zero, Nat.div_one, Nat.mod_mod_of_dvd _ (by norm_num)]
def fieldN (a : BitVec 256) (c : Nat) : Nat := a.toNat / 2 ^ (WCT9.coordBase c + 7) % 2 ^ 14
theorem admissible_iff (a : BitVec 256) :
    WCT9.admissible a = true ↔ a.toNat / 2 ^ 235 % 2 ^ 21 < 1091 ∧ ∀ c', 0 ≤ c' → c' < 9 → fieldN a c' < 16200 := by
  rw [WCT9.admissible_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun c _ hc => h2 ⟨c, hc⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun c => h2 c.val (Nat.zero_le _) c.isLt⟩
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.Driver
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 16384
def base : Nat := 3164
def seg_0 : List (BitVec 32) := [16777327]
def seg_1 : List (BitVec 32) := [1049235,1049875,115]
def seg_4 : List (BitVec 32) := [0x6003b03,0x7803183,45207955,19,0x4431b193]
def seg_9 : List (BitVec 32) := [0xfe0180e3]
def seg_10 : List (BitVec 32) := [35330835,35347219,1049491,29038483,66359,197395,2098835,3148179,4196883,5245587,6294803,7343891,34281619,5175,0x84040413,0xffee37,0x600e0e13,65847,0xffc10113,20151,0x4a4e8e93,52279,0x4a4c0c13,67110291]
def seg_34 : List (BitVec 32) := [0x6003803,45633939,0x7f1f193,33657363,23224883,21077907,0xffefb3,8493971,31165363,0x9c0e3d83,18738611,50878227,2586419,25626419,0x42000493,458983]
def seg_50 : List (BitVec 32) := [0x6803803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,5789459,2586419,25626419,0x44000493,458983]
def seg_68 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,27809555,2586419,25626419,0x46000493,458983]
def seg_86 : List (BitVec 32) := [44585363,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,49829651,2586419,25626419,0x48000493,458983]
def seg_104 : List (BitVec 32) := [0x7003803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,5789459,2586419,25626419,0x4a000493,458983]
def seg_122 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,27809555,2586419,25626419,0x4c000493,458983]
def seg_140 : List (BitVec 32) := [44585363,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,49829651,2586419,25626419,0x4e000493,458983]
def seg_158 : List (BitVec 32) := [0x7803803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,5789459,2586419,25626419,0x50000493,458983]
def seg_176 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,27809555,2586419,25626419,0x52000493,458983]
def seg_194 : List (BitVec 32) := [4535,0xf0118193,0x40303823,0x41603c23,0x40003023,0x40003423,0x40000513,335545747,268437011]
def seg_203 : List (BitVec 32) := [115]
def seg_204 : List (BitVec 32) := [0x6f92206f]
def layout : SigGolfCandidate.Rv.Layout := [(0, seg_0), (1, seg_1), (4, seg_4), (9, seg_9), (10, seg_10), (34, seg_34), (50, seg_50), (68, seg_68), (86, seg_86), (104, seg_104), (122, seg_122), (140, seg_140), (158, seg_158), (176, seg_176), (194, seg_194), (203, seg_203), (204, seg_204)]
def code : List (BitVec 32) := layoutCode layout
theorem layout_ok : layoutOk 0 layout = true := by decide +kernel
theorem window : windowOK base code = true := by decide +kernel
theorem codeAt_region {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf base) code :=
  codeAt_of_window hc (by decide) window
theorem codeAt_0 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 0)) seg_0 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 0) (by kernel_rfl)
theorem codeAt_1 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 1)) seg_1 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 1) (by kernel_rfl)
theorem codeAt_4 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 4)) seg_4 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 2) (by kernel_rfl)
theorem codeAt_9 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 9)) seg_9 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 3) (by kernel_rfl)
theorem codeAt_10 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 10)) seg_10 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 4) (by kernel_rfl)
theorem codeAt_34 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 34)) seg_34 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 5) (by kernel_rfl)
theorem codeAt_50 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 50)) seg_50 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 6) (by kernel_rfl)
theorem codeAt_68 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 68)) seg_68 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 7) (by kernel_rfl)
theorem codeAt_86 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 86)) seg_86 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 8) (by kernel_rfl)
theorem codeAt_104 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 104)) seg_104 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 9) (by kernel_rfl)
theorem codeAt_122 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 122)) seg_122 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 10) (by kernel_rfl)
theorem codeAt_140 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 140)) seg_140 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 11) (by kernel_rfl)
theorem codeAt_158 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 158)) seg_158 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 12) (by kernel_rfl)
theorem codeAt_176 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 176)) seg_176 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 13) (by kernel_rfl)
theorem codeAt_194 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 194)) seg_194 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 14) (by kernel_rfl)
theorem codeAt_203 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 203)) seg_203 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 15) (by kernel_rfl)
theorem codeAt_204 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 204)) seg_204 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 16) (by kernel_rfl)
sym_block blk_0 := symRun { noAlias := true } seg_0 (pcOf (base + 0)) 200
sym_block blk_1 := symRun { noAlias := true } seg_1 (pcOf (base + 1)) 200
sym_block blk_4 := symRun { noAlias := true } seg_4 (pcOf (base + 4)) 200
sym_block blk_9 := symRun { noAlias := true } seg_9 (pcOf (base + 9)) 200
sym_block blk_10 := symRun { noAlias := true } seg_10 (pcOf (base + 10)) 200
sym_block blk_34 := symRun { noAlias := true } seg_34 (pcOf (base + 34)) 200
sym_block blk_50 := symRun { noAlias := true } seg_50 (pcOf (base + 50)) 200
sym_block blk_68 := symRun { noAlias := true } seg_68 (pcOf (base + 68)) 200
sym_block blk_86 := symRun { noAlias := true } seg_86 (pcOf (base + 86)) 200
sym_block blk_104 := symRun { noAlias := true } seg_104 (pcOf (base + 104)) 200
sym_block blk_122 := symRun { noAlias := true } seg_122 (pcOf (base + 122)) 200
sym_block blk_140 := symRun { noAlias := true } seg_140 (pcOf (base + 140)) 200
sym_block blk_158 := symRun { noAlias := true } seg_158 (pcOf (base + 158)) 200
sym_block blk_176 := symRun { noAlias := true } seg_176 (pcOf (base + 176)) 200
sym_block blk_194 := symRun { noAlias := true } seg_194 (pcOf (base + 194)) 200
sym_block blk_204 := symRun { noAlias := true } seg_204 (pcOf (base + 204)) 200
end ClaudeWCT.W9.Machine.Expand.Driver
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false
def jt0 : Nat := 11561
def cb0 : Nat := 3369
theorem child_bits (a : BitVec 256) (w sh : Nat) (h : sh + 7 ≤ 64) :
    ((a.extractLsb' (64 * w) 64 >>> sh) &&& 127#64).toNat = a.toNat / 2 ^ (64 * w + sh) % 128 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, extractLsb'_256_toNat,
    show (127#64).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    mod_div_mod _ _ _ (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rfl
theorem field4_bits (a : BitVec 256) (w sh : Nat) (h : sh + 21 ≤ 64) :
    ((a.extractLsb' (64 * w) 64 >>> (sh + 5)) &&& 65532#64).toNat =
      4 * (a.toNat / 2 ^ (64 * w + sh + 7) % 2 ^ 14) := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, extractLsb'_256_toNat, Nat.shiftRight_eq_div_pow]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, show (65532#64 : Word).toNat = 65532 from rfl]
  have hm : (65532 : Nat).testBit i = (decide (2 ≤ i) && decide (i < 16)) := by
    rcases Nat.lt_or_ge i 16 with h16 | h16
    · interval_cases i <;> decide
    · have : (65532 : Nat).testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide)
        (Nat.pow_le_pow_right (by decide) h16))
      rw [this]; simp; omega
  rw [hm, Nat.mul_comm 4, show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_mul_two_pow]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  rcases Nat.lt_or_ge i 2 with h2 | h2
  · simp [show ¬ 2 ≤ i by omega]
  · rcases Nat.lt_or_ge i 16 with h16 | h16
    · simp only [show 2 ≤ i from h2, show i < 16 from h16, decide_true, Bool.and_true, Bool.true_and,
        show i - 2 < 14 by omega, show i + (sh + 5) < 64 by omega]
      rw [show i + (sh + 5) + 64 * w = i - 2 + (64 * w + sh + 7) by omega]
    · simp [show ¬ i < 16 by omega, show ¬ i - 2 < 14 by omega]
theorem not1_eq : (18446744073709551614#64 : Word) = ~~~1#64 := by decide
theorem disp_pc (v : Word) (f : Nat) (hv : v.toNat = 4 * f) (hf : f < 2 ^ 14) :
    v + 50340#64 &&& 18446744073709551614#64 = pcOf (11561 + f) := by
  have : v + 50340#64 = pcOf (11561 + f) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, hv, pcOf, BitVec.toNat_ofNat]
    omega
  rw [this, not1_eq, pcOf_and_not1]
theorem disp_x4 (c : Word) (n index : Nat) (hc : c.toNat = n) (_hn : n < 128) (hidx : index < 2 ^ 31) :
    c <<< 32 ||| BitVec.ofNat 64 index = BitVec.ofNat 64 (index + 2 ^ 32 * n) := by
  have e : c <<< 32 = BitVec.ofNat 64 (n * 2 ^ 32) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, hc, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [e, ofNat_or_add index n 32 (by omega)]
  congr 1; ring
theorem disp_x23 (c : Word) (n : Nat) (hc : c.toNat = n) (hn : n < 128) :
    c <<< 8 + 17572#64 = BitVec.ofNat 64 (17572 + 256 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, hc, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega
theorem disp_x15 (index k : Nat) :
    BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * k) + BitVec.ofNat 64 65536 =
      BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * (k + 1)) := by
  rw [ofNat_add_ofNat, show index * 2 ^ 27 + 65536 * k + 65536 = index * 2 ^ 27 + 65536 * (k + 1) by ring]
theorem disp_x31 (c : Word) (n index k : Nat) (hc : c.toNat = n) (hn : n < 128) (hk : k < 16) :
    c <<< 20 ||| BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * k) =
      BitVec.ofNat 64 (n * 2 ^ 20 + index * 2 ^ 27 + 65536 * k) := by
  have e : c <<< 20 = BitVec.ofNat 64 (n * 2 ^ 20) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, hc, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have e1 : BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * k) =
      BitVec.ofNat 64 (index * 2 ^ 27) ||| BitVec.ofNat 64 (65536 * k) :=
    (ofNat_or_add (65536 * k) index 27 (by omega)).symm
  rw [e, e1, ← BitVec.or_assoc, BitVec.or_comm (BitVec.ofNat 64 (n * 2 ^ 20)), BitVec.or_assoc,
    ofNat_or_add (65536 * k) n 20 (by omega), ofNat_or_add (n * 2 ^ 20 + 65536 * k) index 27 (by omega),
    show index * 2 ^ 27 + (n * 2 ^ 20 + 65536 * k) = n * 2 ^ 20 + index * 2 ^ 27 + 65536 * k by ring]
theorem disp_x31n (c : Word) (n index K K' : Nat) (hc : c.toNat = n) (hn : n < 128) (hK : K < 16) (hK' : K' = K) :
    c <<< 20 ||| BitVec.ofNat 64 (index * 134217728 + 65536 * K) =
      BitVec.ofNat 64 (n * 1048576 + index * 134217728 + 65536 * K') := by
  rw [hK']; exact disp_x31 c n index K hc hn hK
theorem disp_x31s (c : Word) (n index K K' : Nat) (hc : c.toNat = n) (hn : n < 128) (hK : K + 1 < 16)
    (hK' : K' = K + 1) :
    c <<< 20 ||| (BitVec.ofNat 64 (index * 134217728 + 65536 * K) + 65536#64) =
      BitVec.ofNat 64 (n * 1048576 + index * 134217728 + 65536 * K') := by
  subst hK'
  have := disp_x15 index K
  simp only [show (2 : Nat) ^ 27 = 134217728 by norm_num] at this
  rw [show (65536#64 : Word) = BitVec.ofNat 64 65536 from rfl, this]
  exact disp_x31 c n index (K + 1) hc hn hK
theorem disp_x27 (b index : Nat) (hb : b < 2 ^ 32) :
    BitVec.ofNat 64 b ||| BitVec.ofNat 64 index <<< 32 = BitVec.ofNat 64 (b + 2 ^ 32 * index) := by
  rw [ofNat_shl, BitVec.or_comm, ofNat_or_add b index 32 hb, show index * 2 ^ 32 + b = b + 2 ^ 32 * index by ring]
end ClaudeWCT.W9.Machine.Expand
end
