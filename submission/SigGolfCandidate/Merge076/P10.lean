import SigGolfCandidate.ExpandLabel
import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge059
import SigGolfCandidate.Merge060
import SigGolfCandidate.Merge070
import SigGolfCandidate.Merge075
import SigGolfCandidate.Merge076.P1
import SigGolfCandidate.Merge076.P4
import SigGolfCandidate.Merge076.P6

set_option debug.skipKernelTC false
set_option linter.all false

-- ==== merged from T3M_Expand_LayerBlocks ====
section

section
namespace SigGolfCandidate.T3M.Expand.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
end SigGolfCandidate.T3M.Expand.BCBlocks
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
section blocks
variable (s : MachineState)
end blocks
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand.BCBlocks
variable {im : Image} [Code im]
end SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
/-! img-v6 top-node nonce routine (words 43195 .. 43249, hooked at 1139 `jal 43195`; topfold-v6, NOTES V49). -/
variable {im : Image} [Code im]
variable                    [PackedBlocks.Code im]
variable (s : MachineState)
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
variable {im : Image} [Code im] (s : MachineState)
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace Grind
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (NODE NOUT)
open SigGolfCandidate.T3 (Digest nonceBytes pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.WCT9 (lowerZeroBits lowerNonceCap lowerZeroOk lowerNodeInputN lowerNodeHashN lowerNonceSearch
  lowerNodeAt)
section blocks
variable {im : Image} [Code im] (s : MachineState)

/-- Loop setup (54838..54846): `t5` = the used half's top byte, `t6` = cap `128 << b`, `t4 = 8 - b`. -/
theorem b8b_spec (hpc : s.pc = pcOf 54838) :
    ∃ t, Steps im s 9 9 t ∧ t.pc = pcOf 54847 ∧
      t.getReg .x30 = ((s.getReg .x7 &&& 1#64) ^^^ 1#64) <<< 4 + s.getReg .x12 + 15#64 ∧
      t.getReg .x31 = 128#64 <<< ((s.getReg .x29).toNat % 64) ∧ t.getReg .x29 = 8#64 - s.getReg .x29 ∧
      RegsExcept s t [.x28, .x29, .x30, .x31] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl (Code.codeAt_stub (im := im)) 54838 54847 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound gB8b hc s hpc (by simp [gB8b.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gB8b.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, gB8b.res]; t3n []
  · simp only [Result.toState_getReg, gB8b.res]; t3n []
  · simp only [Result.toState_getReg, gB8b.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [gB8b.res, rv_simp] <;> rfl
  · intro A _ _; simp [gB8b.res, rv_simp]

end blocks

/-! U16b grind stub: tweak-word arithmetic. -/

section cls
variable {im : Image} [Code im]

end cls

/-! U16b grind stub: loop setup and the zero test. -/

section setup
variable {im : Image} [Code im]

theorem setup_spec (u : MachineState) (hpc : u.pc = pcOf 54838) (lay heap : Nat)
    (hh2 : 2 ≤ heap) (hh : heap < 32) (hl1 : 1 ≤ lay) (h7 : u.getReg .x7 = BitVec.ofNat 64 heap)
    (h29 : u.getReg .x29 = BitVec.ofNat 64 (ClaudeWCT.WCT9.lowerZeroBits lay heap))
    (h12 : u.getReg .x12 = BitVec.ofNat 64 NOUT) :
    ∃ v k, Steps im u k k v ∧ k ≤ 9 ∧ v.pc = pcOf 54847 ∧
      v.getReg .x29 = BitVec.ofNat 64 (8 - ClaudeWCT.WCT9.lowerZeroBits lay heap) ∧
      v.getReg .x30 = BitVec.ofNat 64 (topByteA heap) ∧
      v.getReg .x31 = BitVec.ofNat 64 (ClaudeWCT.WCT9.lowerNonceCap lay heap) ∧
      RegsExcept u v [.x28, .x29, .x30, .x31] ∧ Frame u v (fun _ => False) := by
  have hb : ClaudeWCT.WCT9.lowerZeroBits lay heap ≤ 4 ∧ 1 ≤ ClaudeWCT.WCT9.lowerZeroBits lay heap := by
    unfold ClaudeWCT.WCT9.lowerZeroBits; split_ifs <;> omega
  obtain ⟨v, sv, pv, x30, x31, x29, rv, fv⟩ := b8b_spec (im := im) u hpc
  refine ⟨v, 9, sv, le_rfl, pv, ?_, ?_, ?_, rv, fv⟩
  · rw [x29, h29, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    norm_num; omega
  · rw [x30, h7, h12]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_ofNat]
    unfold topByteA NOUT
    rcases Nat.mod_two_eq_zero_or_one heap with he | ho
    · have : heap % 18446744073709551616 &&& 1 = 0 := by
        rw [Nat.mod_eq_of_lt (by omega), Nat.and_one_is_mod]; exact he
      simp only [this]; norm_num; omega
    · have : heap % 18446744073709551616 &&& 1 = 1 := by
        rw [Nat.mod_eq_of_lt (by omega), Nat.and_one_is_mod]; exact ho
      simp only [this]; norm_num; omega
  · rw [x31, h29, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show ClaudeWCT.WCT9.lowerZeroBits lay heap < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show ClaudeWCT.WCT9.lowerZeroBits lay heap < 64 by omega)]
    unfold ClaudeWCT.WCT9.lowerNonceCap
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rfl
end setup

/-! U16b grind stub: node input, zero test, trial invariant. -/

section sim
variable {im : Image} {sk : BitVec 256}
end sim

section found
variable {im : Image} [Code im]

end found

/-! U16b grind stub: the search loop and the whole stub (word 1138 -> 1139). -/

section loop
variable {im : Image} [Code im] (sk : BitVec 256)

end loop

/-! U16b grind stub: the pass-through of a non-lower node (top tree). -/

section pass
variable {im : Image} [Code im] {sk : BitVec 256}

end pass

end Grind


end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_Basic ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
section tb
variable {image : Image} {sk : BitVec 256}
end tb
end SigGolfCandidate.T3M.Expand
end
-- ==== merged from T3M_Expand_LayerChain ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chain chainInput shortHash pad64 zero16 header)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS)
set_option autoImplicit false
section chain
variable {sk : BitVec 256}
end chain
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [Code im]                    [PackedBlocks.Code im] {sk : BitVec 256}
end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_LayersBlocks ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
set_option autoImplicit false
set_option maxRecDepth 8192
section blocks
variable (s : MachineState)
-- [h2 lane] removed c342_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
open SigGolfCandidate.T3M.Expand
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image}               
section
variable (s : MachineState)
end
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
end SigGolfCandidate.T3M.Expand.SharedRecover

/-! ## T51 KCOPY (54522..54531, from 331 `jal ra, 54522`): copy the 1,896-byte shared kernel table window
`0xFF9E00 .. 0xFFA568` (237 doublewords; the 1,892-byte block + 4 bytes) to RAM `0xA0000`, then `j 457`. -/
namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

end SigGolfCandidate.T3M.Expand.KCopy
end
-- ==== merged from T3M_Search_DigestSearch ====
section

section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
section blocks
variable {image : Image} {b : Nat}
end blocks
section sort
variable {image : Image} {b : Nat}
end sort
section loop
variable {image : Image} {b : Nat}
end loop
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer HashOutput)
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
section blocks
variable {image : Image} {d b : Nat}
end blocks
section loop
variable {image : Image} {d b : Nat} {sk : BitVec 256}
end loop
end SigGolfCandidate.T3M.Search
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Defs ====
section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC FailedAt KernAt)
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ExpSearch ====
section

section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Search (DIG NBUF)
open SigGolfCandidate.T3M.Expand (IDXV)
open ClaudeWCT.W9.Machine.Sign (run)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE)
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand.ESearch
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign (run memEval_cons_ofNat)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE costByte costChk
  costChk_getD costByte_lt piece regs_rfs shl0_shr33 sll_eval srl_eval fieldE_eval psum psum_succ psum_le fieldN_lt
  psum_nine digestInput_length' pad64_digestInput' wordsOf_digestInput' blocks_digestInput' childN childN_lt childE_eval)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
section pieces
variable {im : Image}
end pieces
section loop
variable {im : Image} {sk : BitVec 256}
end loop
end ClaudeWCT.W9.Machine.Expand.ESearch
end
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Base ====
section

section
namespace ClaudeWCT.W9.Machine.Expand
open Lean Meta Elab Tactic
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_DrvBits ====
section

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
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.Driver
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 16384
end ClaudeWCT.W9.Machine.Expand.Driver
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Merkle_ChildDefs ====
section

namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE)
end ClaudeWCT.W9.Machine.Merkle
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Region ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput readDigest readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (chainBytes leafBytes)
set_option linter.unusedSimpArgs false
section windows
variable (c : Nat) (op : WCT9.Opening)
end windows
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_LayoutCode ====
section

/-! Pairing stage 1: code tables of the leaf / digest layout block 48100 .. 49225 (proofs in `LayoutBlock`). -/
namespace ClaudeWCT.W9.Machine.Expand.Layout
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
/-! Generated by pair1-expand (from sol-pair1/img-candidate/expand.code, words 48119 .. 49224).
T51 (VERA2, round 2; regenerated from the T51 expand image t51/sign/img/t51e, words 48119 .. 49225): the top group
keeps the 51 items of values 0..50 (item 129, value 0: `sd t1,-32(a1)`, so `xK 129 = 2^64 - 32` and its slot is
`(dK + xK) % 2^64 = 25200`; item 129 + i: `X = 16 (i - 1)`). #938's items 180..182 (values 51..53) lost their
stores (`nop`): with the return word they form the straight tail `cRet` (49207 .. 49225, 19 words). -/
end ClaudeWCT.W9.Machine.Expand.Layout
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactCode ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib

namespace PairCopy
/-! Pairing stage 1: the lower-chain pair copy block at 48000 (outside the compact lookup scope). -/
end PairCopy
end ClaudeWCT.W9.Machine.Expand

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
section code
variable {im : Image}                        
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Lv ====
section

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
section code
variable {im : Image}                                                    
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
set_option linter.unusedSimpArgs false
section eval
variable {s : MachineState} {r : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 r) (hr : r < 2 ^ 7)
include h19 hr
end eval
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section
namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
set_option linter.unusedSimpArgs false
/-! C3 (FULL, E6): the root level of each lower layer runs in three pieces: `cLvA` (Z low word copy, then
`jal rtAt`), the trampoline `cRT` (Z high word copy, LE64(1) at window + 24, `jal` back) and `cLvB` (sibling copy). -/
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end
end
