import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_Defs
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_Base

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIG NBUF ENC)
set_option autoImplicit false
set_option maxRecDepth 8192
section blocks
variable (s : MachineState)
-- [h2 lane] removed s0_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
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
def seg_4 : List (BitVec 32) := [100678403,125841795,52547987,19,0x5491b193]
def seg_9 : List (BitVec 32) := [0xfe0180e3]
def seg_10 : List (BitVec 32) := [727827,35347219,1049491,29038483,66359,6784947,2098835,3148179,4196883,5245587,6294803,7343891,34281619,5175,0x84040413,16772663,0x600e0e13,4407,0xffc10113,20151,0x4a4e8e93,52279,0x4a4c0c13,67110291]
def seg_34 : List (BitVec 32) := [0x6003803,545171,0x7f1f193,33657363,23224883,21077907,0xffefb3,8493971,31165363,0x60178d93,19,5789459,2586419,25626419,0x42000493,458983]
def seg_50 : List (BitVec 32) := [0x6803803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,5789459,2586419,25626419,0x44000493,458983]
def seg_68 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,27809555,2586419,25626419,0x46000493,458983]
def seg_86 : List (BitVec 32) := [60314003,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,43538195,2586419,25626419,0x48000493,458983]
def seg_104 : List (BitVec 32) := [0x7003803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,5789459,2586419,25626419,0x4a000493,458983]
def seg_122 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,27809555,2586419,25626419,0x4c000493,458983]
def seg_140 : List (BitVec 32) := [60314003,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,43538195,2586419,25626419,0x4e000493,458983]
def seg_158 : List (BitVec 32) := [0x7803803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,5789459,2586419,25626419,0x50000493,458983]
def seg_176 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,27809555,2586419,25626419,0x52000493,458983]
/-- Nested FTS (r1-1): the forest hash is replaced by copying `(L8, R8)` from the forest-buffer pair 8 (`0x520`) to
`0x100` (copied to the L3 encoding block by 39142) and to the encoding R slot `0x20290`; 203 is now a NOP. -/
def seg_194 : List (BitVec 32) := [1375744387,1384134403,271593507,283128867,1392521603,1400911619,134711,675166243,686701603]
def seg_203 : List (BitVec 32) := [19]
def seg_204 : List (BitVec 32) := [0x6f92206f]
def layout : SigGolfCandidate.Rv.Layout := [(0, seg_0), (1, seg_1), (4, seg_4), (9, seg_9), (10, seg_10), (34, seg_34), (50, seg_50), (68, seg_68), (86, seg_86), (104, seg_104), (122, seg_122), (140, seg_140), (158, seg_158), (176, seg_176), (194, seg_194), (203, seg_203), (204, seg_204)]
def code : List (BitVec 32) := layoutCode layout
theorem window : windowOK base code = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand.Driver
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false
theorem child_bits (a : BitVec 256) (w sh : Nat) (h : sh + 7 ≤ 64) :
    ((a.extractLsb' (64 * w) 64 >>> sh) &&& 127#64).toNat = a.toNat / 2 ^ (64 * w + sh) % 128 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, extractLsb'_256_toNat,
    show (127#64).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    mod_div_mod _ _ _ (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rfl
end ClaudeWCT.W9.Machine.Expand
end
