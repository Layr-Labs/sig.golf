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
variable {im : Image}          
end SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
/-! img-v6 top-node nonce routine (words 43195 .. 43249, hooked at 1139 `jal 43195`; topfold-v6, NOTES V49). -/
variable {im : Image}          
variable                    [PackedBlocks.Code im]
variable (s : MachineState)
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
variable {im : Image}           (s : MachineState)
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
variable {im : Image}           (s : MachineState)

end blocks

/-! U16b grind stub: tweak-word arithmetic. -/

section cls
variable {im : Image}          

end cls

/-! U16b grind stub: loop setup and the zero test. -/

section setup
variable {im : Image}          

end setup

/-! U16b grind stub: node input, zero test, trial invariant. -/

section sim
variable {im : Image} {sk : BitVec 256}
end sim

section found
variable {im : Image}          

end found

/-! U16b grind stub: the search loop and the whole stub (word 1138 -> 1139). -/

section loop
variable {im : Image}           (sk : BitVec 256)

end loop

/-! U16b grind stub: the pass-through of a non-lower node (top tree). -/

section pass
variable {im : Image}           {sk : BitVec 256}

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
variable {im : Image}                              [PackedBlocks.Code im] {sk : BitVec 256}
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
-- (open dropped: nothing it names is in this part)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ExpSearch ====
section

section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Search (DIG NBUF)
-- (open dropped: nothing it names is in this part)
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
-- (open dropped: nothing it names is in this part)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF FailedAt)
-- (open dropped: nothing it names is in this part)
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
-- (open dropped: nothing it names is in this part)
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
def cfgC : Config := { noAlias := true }
def coordAt (k : Nat) : Nat := 41121 + 111 * k
def sibAt (k l : Nat) : Nat := coordAt k + 13 + 14 * l
def cStart : List (BitVec 32) := [5431,0x84050513,2098615,361875,1591,0x48060613,0x7e1000ef]
def cRegs : List (BitVec 32) := [2098231,263187,5303,0x84048493,0xffa937,0xa0090913]
def cRow : List (BitVec 32) := [66712467,4428691,7932467]
def cStep : List (BitVec 32) := [0x40040413,939820179]
def cFinal : List (BitVec 32) := [13623,0xc4050513,9655,0x7c058593,1591,0x6b160613,16777455]
def cHalt : List (BitVec 32) := [62914671]
def cCopy : List (BitVec 32) := [340739,6664227,8717587,8750483,0xfff60613,0xfe0616e3,32871]
def cZero : List (BitVec 32) := [372771,8750483,0xfff60613,0xfe061ae3,32871]
def cHeads : List (List (BitVec 32)) :=[[0x6003303,217875,0x7f37993,296339,41944595,0x7cd000ef],[0x6803303,217875,0x7f37993,296339,41944595,0x611000ef],[0x6803303,22237971,0x7f37993,296339,41944595,0x455000ef],[0x6803303,59986707,0x7f37993,296339,41944595,697303279],[0x7003303,217875,0x7f37993,296339,41944595,0xdd000ef],[0x7003303,22237971,0x7f37993,296339,41944595,0x720000ef],[0x7003303,59986707,0x7f37993,296339,41944595,0x564000ef],[0x7803303,217875,0x7f37993,296339,41944595,981467375],[0x7803303,22237971,0x7f37993,296339,41944595,515899631]]
def cHead (k : Nat) : List (BitVec 32) := cHeads.getD k []
def cMids : List (List (BitVec 32)) :=[[470025491,335840659,75499027,0x7a1000ef],[470025491,335840659,75499027,0x5e5000ef],[470025491,335840659,75499027,0x429000ef],[470025491,335840659,75499027,651165935],[470025491,335840659,75499027,0xb1000ef],[470025491,335840659,75499027,0x6f4000ef],[470025491,335840659,75499027,0x538000ef],[470025491,335840659,75499027,935330031],[470025491,335840659,75499027,469762287]]
def cMid (k : Nat) : List (BitVec 32) := cMids.getD k []
section code
variable {im : Image}                        
-- (include dropped in this part)
end code
sym_block RStart := symRun cfgC cStart (pcOf 41108) 40
sym_block RRegs := symRun cfgC cRegs (pcOf 41115) 40
sym_block RFinal := symRun cfgC cFinal (pcOf 42120) 40
sym_block RHalt := symRun cfgC cHalt (pcOf 42127) 40
sym_block RCopy := symRun cfgC cCopy (pcOf 42130) 40
sym_block RCopyRet := symRun cfgC [0x8067] (pcOf 42136) 40
sym_block RZero := symRun cfgC cZero (pcOf 42137) 40
sym_block RZeroRet := symRun cfgC [0x8067] (pcOf 42141) 40
sym_block RHead0 := symRun cfgC (cHead 0) (pcOf (coordAt 0)) 40
sym_block RMid0 := symRun cfgC (cMid 0) (pcOf (coordAt 0 + 6)) 40
sym_block RHead1 := symRun cfgC (cHead 1) (pcOf (coordAt 1)) 40
sym_block RMid1 := symRun cfgC (cMid 1) (pcOf (coordAt 1 + 6)) 40
sym_block RHead2 := symRun cfgC (cHead 2) (pcOf (coordAt 2)) 40
sym_block RMid2 := symRun cfgC (cMid 2) (pcOf (coordAt 2 + 6)) 40
sym_block RHead3 := symRun cfgC (cHead 3) (pcOf (coordAt 3)) 40
sym_block RMid3 := symRun cfgC (cMid 3) (pcOf (coordAt 3 + 6)) 40
sym_block RHead4 := symRun cfgC (cHead 4) (pcOf (coordAt 4)) 40
sym_block RMid4 := symRun cfgC (cMid 4) (pcOf (coordAt 4 + 6)) 40
sym_block RHead5 := symRun cfgC (cHead 5) (pcOf (coordAt 5)) 40
sym_block RMid5 := symRun cfgC (cMid 5) (pcOf (coordAt 5 + 6)) 40
sym_block RHead6 := symRun cfgC (cHead 6) (pcOf (coordAt 6)) 40
sym_block RMid6 := symRun cfgC (cMid 6) (pcOf (coordAt 6 + 6)) 40
sym_block RHead7 := symRun cfgC (cHead 7) (pcOf (coordAt 7)) 40
sym_block RMid7 := symRun cfgC (cMid 7) (pcOf (coordAt 7 + 6)) 40
sym_block RHead8 := symRun cfgC (cHead 8) (pcOf (coordAt 8)) 40
sym_block RMid8 := symRun cfgC (cMid 8) (pcOf (coordAt 8 + 6)) 40
sym_block RRow := symRun cfgC cRow (pcOf (coordAt 0 + 10)) 40
sym_block RStep := symRun cfgC cStep (pcOf (coordAt 0 + 109)) 40
theorem run_row (k : Nat) (hk : k < 9) : symRun cfgC cRow (pcOf (coordAt k + 10)) 40 =
    some ⟨RRow.res.st, .c (pcOf (coordAt k + 13)), .endOfCode, 3, 3⟩ := by
  interval_cases k <;> kernel_rfl
theorem run_step (k : Nat) (hk : k < 9) : symRun cfgC cStep (pcOf (coordAt k + 109)) 40 =
    some ⟨RStep.res.st, .c (pcOf (coordAt k + 111)), .endOfCode, 2, 2⟩ := by
  interval_cases k <;> kernel_rfl
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
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
def cIdx : List (BitVec 32) := [0x6003b03,35347219,0xff9937,0x40090913]
def cRow1 : List (BitVec 32) := [0xcb5993,0x7f9f993,3774995,19532339,537528851]
def cLv10 : List (BitVec 32) := [3224887,478479635,672515,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv11 : List (BitVec 32) := [3224887,411370771,1721091,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv12 : List (BitVec 32) := [3224887,344261907,2769667,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv13 : List (BitVec 32) := [3224887,277153043,3818243,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv14 : List (BitVec 32) := [3224887,210044179,4866819,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv15 : List (BitVec 32) := [3224887,142935315,5915395,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv16 : List (BitVec 32) := [3224887,75826451,6963971,4395795,17847,3078981011,6653363,33898115,42286851,64335907,243273839,6935315,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cRow2 : List (BitVec 32) := [7035283,66714003,3774995,19532339]
def cLv20 : List (BitVec 32) := [3228983,3766813971,672515,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv21 : List (BitVec 32) := [3228983,3699705107,1721091,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv22 : List (BitVec 32) := [3228983,3632596243,2769667,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv23 : List (BitVec 32) := [3228983,3565487379,3818243,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv24 : List (BitVec 32) := [3228983,3498378515,4866819,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv25 : List (BitVec 32) := [3228983,3431269651,5915395,4395795,17847,1560642963,6653363,33898115,42286851,64335907,1783627887,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cRow3 : List (BitVec 32) := [66812307,3774995,19532339]
def cLv30 : List (BitVec 32) := [3233079,2760181011,672515,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv31 : List (BitVec 32) := [3233079,2693072147,1721091,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv32 : List (BitVec 32) := [3233079,2625963283,2769667,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv33 : List (BitVec 32) := [3233079,2558854419,3818243,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv34 : List (BitVec 32) := [3233079,2491745555,4866819,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv35 : List (BitVec 32) := [3233079,2424636691,5915395,4395795,21943,4253386131,6653363,33898115,42286851,64335907,1179648111,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cTail : List (BitVec 32) := [3212599,328979,26039,2651162003,343683,8732419,30781475,31831075,17133187,374819,30784547]
def lvAt (lay j : Nat) : Nat := if lay = 1 then 42247 + 23 * j else if lay = 2 then 42419 + 23 * j else 42567 + 23 * j
def cLvs : List (List (BitVec 32)) := [cLv10, cLv11, cLv12, cLv13, cLv14, cLv15, cLv16, cLv20, cLv21, cLv22, cLv23, cLv24, cLv25, cLv30, cLv31, cLv32, cLv33, cLv34, cLv35]
def lvIdx (lay j : Nat) : Nat := if lay = 1 then j else if lay = 2 then 7 + j else 13 + j
def cLv (lay j : Nat) : List (BitVec 32) := cLvs.getD (lvIdx lay j) []
/-- C3 (FULL, E6): the root level of each lower layer jumps after its Z-pad copy to a trampoline that writes LE64(1)
at window + 24 (the encoding row tweak's high word, honest 1) and returns. -/
def rtAt (lay : Nat) : Nat := if lay = 1 then 43477 else if lay = 2 then 43481 else 43485
def cRT (lay : Nat) : List (BitVec 32) :=
  if lay = 1 then [65385507,1052307,30784547,4045398127] else if lay = 2 then [65385507,1052307,30784547,2505044079]
  else [65385507,1052307,30784547,3109023855]
def rootJ (lay : Nat) : Nat := if lay = 1 then 6 else 5
def cLvA (lay : Nat) : List (BitVec 32) := (cLv lay (rootJ lay)).take 11
def cLvB (lay : Nat) : List (BitVec 32) := (cLv lay (rootJ lay)).drop 11
section code
variable {im : Image}                                                    
-- (include dropped in this part)
end code
sym_block RIdx := symRun cfgC cIdx (pcOf 42231) 40
sym_block RRow1 := symRun cfgC cRow1 (pcOf 42242) 40
sym_block RRow2 := symRun cfgC cRow2 (pcOf 42415) 40
sym_block RRow3 := symRun cfgC cRow3 (pcOf 42564) 40
sym_block RTail := symRun cfgC cTail (pcOf 42705) 40
sym_block RLv10 := symRun cfgC (cLv 1 0) (pcOf (lvAt 1 0)) 40
sym_block RLv11 := symRun cfgC (cLv 1 1) (pcOf (lvAt 1 1)) 40
sym_block RLv12 := symRun cfgC (cLv 1 2) (pcOf (lvAt 1 2)) 40
sym_block RLv13 := symRun cfgC (cLv 1 3) (pcOf (lvAt 1 3)) 40
sym_block RLv14 := symRun cfgC (cLv 1 4) (pcOf (lvAt 1 4)) 40
sym_block RLv15 := symRun cfgC (cLv 1 5) (pcOf (lvAt 1 5)) 40
sym_block RLv16 := symRun cfgC (cLv 1 6) (pcOf (lvAt 1 6)) 40
sym_block RLv20 := symRun cfgC (cLv 2 0) (pcOf (lvAt 2 0)) 40
sym_block RLv21 := symRun cfgC (cLv 2 1) (pcOf (lvAt 2 1)) 40
sym_block RLv22 := symRun cfgC (cLv 2 2) (pcOf (lvAt 2 2)) 40
sym_block RLv23 := symRun cfgC (cLv 2 3) (pcOf (lvAt 2 3)) 40
sym_block RLv24 := symRun cfgC (cLv 2 4) (pcOf (lvAt 2 4)) 40
sym_block RLv25 := symRun cfgC (cLv 2 5) (pcOf (lvAt 2 5)) 40
sym_block RLv30 := symRun cfgC (cLv 3 0) (pcOf (lvAt 3 0)) 40
sym_block RLv31 := symRun cfgC (cLv 3 1) (pcOf (lvAt 3 1)) 40
sym_block RLv32 := symRun cfgC (cLv 3 2) (pcOf (lvAt 3 2)) 40
sym_block RLv33 := symRun cfgC (cLv 3 3) (pcOf (lvAt 3 3)) 40
sym_block RLv34 := symRun cfgC (cLv 3 4) (pcOf (lvAt 3 4)) 40
sym_block RLv35 := symRun cfgC (cLv 3 5) (pcOf (lvAt 3 5)) 40
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
def nbE (j : Nat) : E := .bin .xor (.bin .and (.bin .srl (.reg .x19) (.c (BitVec.ofNat 64 j))) (.c 1#64)) (.c 1#64)
def t6E (j : Nat) : E := .bin .add (.bin .sll (nbE j) (.c 4#64)) (.bin .sll (nbE j) (.c 5#64))
def pbE (j : Nat) : E := .un (.ld .bu j) (E.ld (.reg .x20))
def slotE (j : Nat) : E := .bin .sll (pbE j) (.c 4#64)
def a0E (j S : Nat) : E := .bin .add (t6E j) (.c (BitVec.ofNat 64 S))
def a1E (j D : Nat) : E := .bin .add (.bin .add (slotE j) (.c (BitVec.ofNat 64 D))) (t6E j)
def lvRegs (j S D : Nat) : RegFile :=
  (((((RegFile.init.set .x6 (t6E j)).set .x7 (.bin .sll (nbE j) (.c 5#64))).set .x10 (a0E j S)).set .x11
    (a1E j D)).set .x29 (a0E j S).ld).set .x30 (a0E j (S + 8)).ld
def lvMem (j S D : Nat) : SymMem :=
  [(⟨some (a1E j D), 8#64⟩, (a0E j (S + 8)).ld), (⟨some (a1E j D), 0#64⟩, (a0E j S).ld),
   (⟨some (slotE j), BitVec.ofNat 64 (D + 40)⟩, (E.c (BitVec.ofNat 64 (S + 40))).ld),
   (⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩, (E.c (BitVec.ofNat 64 (S + 32))).ld)]
def lvObl (j S D : Nat) : List Oblig :=
  [.valid ⟨some (a1E j D), 8#64⟩ 8, .valid ⟨some (a1E j D), 0#64⟩ 8,
   .ne ⟨some (t6E j), BitVec.ofNat 64 (S + 8)⟩ ⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩,
   .ne ⟨some (t6E j), BitVec.ofNat 64 (S + 8)⟩ ⟨some (slotE j), BitVec.ofNat 64 (D + 40)⟩,
   .valid ⟨some (t6E j), BitVec.ofNat 64 (S + 8)⟩ 8,
   .ne ⟨some (t6E j), BitVec.ofNat 64 S⟩ ⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩,
   .ne ⟨some (t6E j), BitVec.ofNat 64 S⟩ ⟨some (slotE j), BitVec.ofNat 64 (D + 40)⟩,
   .valid ⟨some (t6E j), BitVec.ofNat 64 S⟩ 8,
   .valid ⟨some (slotE j), BitVec.ofNat 64 (D + 40)⟩ 8, .valid ⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩ 8,
   .align8 (.reg .x20), .valid ⟨some (.reg .x20), BitVec.ofNat 64 j⟩ 1]
def rLvs : List Result := [RLv10.res, RLv11.res, RLv12.res, RLv13.res, RLv14.res, RLv15.res, RLv16.res, RLv20.res,
  RLv21.res, RLv22.res, RLv23.res, RLv24.res, RLv25.res, RLv30.res, RLv31.res, RLv32.res, RLv33.res, RLv34.res,
  RLv35.res]
section eval
variable {s : MachineState} {r : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 r) (hr : r < 2 ^ 7)
include h19 hr
theorem nbE_eval (j : Nat) (hj : j < 7) : (nbE j).eval s = BitVec.ofNat 64 (1 - r / 2 ^ j % 2) := by
  have hb : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  apply BitVec.eq_of_toNat_eq
  simp only [nbE, E.eval, BinOp.eval, h19, BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show j < 64 by omega), show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod]
  rcases (show r / 2 ^ j % 2 = 0 ∨ r / 2 ^ j % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
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
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
/-! C3 (FULL, E6): the root level of each lower layer runs in three pieces: `cLvA` (Z low word copy, then
`jal rtAt`), the trampoline `cRT` (Z high word copy, LE64(1) at window + 24, `jal` back) and `cLvB` (sibling copy). -/
sym_block RLvA1 := symRun cfgC (cLvA 1) (pcOf (lvAt 1 (rootJ 1))) 40
sym_block RLvA2 := symRun cfgC (cLvA 2) (pcOf (lvAt 2 (rootJ 2))) 40
sym_block RLvA3 := symRun cfgC (cLvA 3) (pcOf (lvAt 3 (rootJ 3))) 40
sym_block RRT1 := symRun cfgC (cRT 1) (pcOf (rtAt 1)) 40
sym_block RRT2 := symRun cfgC (cRT 2) (pcOf (rtAt 2)) 40
sym_block RRT3 := symRun cfgC (cRT 3) (pcOf (rtAt 3)) 40
sym_block RLvB1 := symRun cfgC (cLvB 1) (pcOf (lvAt 1 (rootJ 1) + 11)) 40
sym_block RLvB2 := symRun cfgC (cLvB 2) (pcOf (lvAt 2 (rootJ 2) + 11)) 40
sym_block RLvB3 := symRun cfgC (cLvB 3) (pcOf (lvAt 3 (rootJ 3) + 11)) 40
def lvARegs (j S D : Nat) : RegFile :=
  ((((RegFile.init.set .x6 (slotE j)).set .x10 (.c (BitVec.ofNat 64 S))).set .x11
    (.bin .add (slotE j) (.c (BitVec.ofNat 64 D)))).set .x29 (E.c (BitVec.ofNat 64 (S + 32))).ld).set .x30
    (E.c (BitVec.ofNat 64 (S + 40))).ld
def lvAMem (j S D : Nat) : SymMem :=
  [(⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩, (E.c (BitVec.ofNat 64 (S + 32))).ld)]
def lvAObl (j D : Nat) : List Oblig :=
  [.valid ⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩ 8, .align8 (.reg .x20),
   .valid ⟨some (.reg .x20), BitVec.ofNat 64 j⟩ 1]
def rtRegs : RegFile := RegFile.init.set .x29 (.c 1#64)
def rtMem : SymMem := [(⟨some (.reg .x11), 24#64⟩, .c 1#64), (⟨some (.reg .x11), 40#64⟩, .reg .x30)]
def rtObl : List Oblig := [.valid ⟨some (.reg .x11), 24#64⟩ 8, .valid ⟨some (.reg .x11), 40#64⟩ 8]
def aBE (j : Nat) : E := .bin .add (.reg .x10) (t6E j)
def dBE (j : Nat) : E := .bin .add (.reg .x11) (t6E j)
def lvBRegs (j : Nat) : RegFile :=
  (((((RegFile.init.set .x6 (t6E j)).set .x7 (.bin .sll (nbE j) (.c 5#64))).set .x10 (aBE j)).set .x11
    (dBE j)).set .x29 (aBE j).ld).set .x30 (E.bin .add (aBE j) (.c 8#64)).ld
def lvBMem (j : Nat) : SymMem :=
  [(⟨some (dBE j), 8#64⟩, (E.bin .add (aBE j) (.c 8#64)).ld), (⟨some (dBE j), 0#64⟩, (aBE j).ld)]
def lvBObl (j : Nat) : List Oblig :=
  [.valid ⟨some (dBE j), 8#64⟩ 8, .valid ⟨some (dBE j), 0#64⟩ 8, .valid ⟨some (aBE j), 8#64⟩ 8,
   .valid ⟨some (aBE j), 0#64⟩ 8]
def rRT (lay : Nat) : Result := [RRT1.res, RRT2.res, RRT3.res].getD (lay - 1) RRT1.res
def rLvB (lay : Nat) : Result := [RLvB1.res, RLvB2.res, RLvB3.res].getD (lay - 1) RLvB1.res
theorem rRT_eq (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    rRT lay = ⟨⟨rtRegs, rtMem, rtObl⟩, .c (pcOf (lvAt lay (rootJ lay) + 11)), .jump, 4, 4⟩ := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem run_rt (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    symRun cfgC (cRT lay) (pcOf (rtAt lay)) 40 = some (rRT lay) := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem rLvB_eq (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    rLvB lay = ⟨⟨lvBRegs (rootJ lay), lvBMem (rootJ lay), lvBObl (rootJ lay)⟩,
      .c (pcOf (lvAt lay (rootJ lay) + 23)), .endOfCode, 12, 12⟩ := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem run_lvB (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    symRun cfgC (cLvB lay) (pcOf (lvAt lay (rootJ lay) + 11)) 40 = some (rLvB lay) := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end
end
