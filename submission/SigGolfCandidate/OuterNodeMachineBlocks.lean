import SigGolfCandidate.SimCore
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeMachineBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
def b_saveCode : List (BitVec 32) := [0x48603023,0x48703423,0x313,0x2053423]
sym_block b_save := symRun {noAlias:=true} b_saveCode (pcOf 246499) 40
theorem b_save_counts : b_save.res.steps=4 ∧ b_save.res.cycles=4 := by decide +kernel
def b_preHashCode : List (BitVec 32) := [0x2653023,0x73]
sym_block b_preHash := symRun {noAlias:=true} b_preHashCode (pcOf 246503) 40
theorem b_preHash_counts : b_preHash.res.steps=1 ∧ b_preHash.res.cycles=1 := by decide +kernel
def b_checkCode : List (BitVec 32) := [0x1863383,0x3b3d393,0x38a63]
sym_block b_check := symRun {noAlias:=true} b_checkCode (pcOf 246505) 40
theorem b_check_counts : b_check.res.steps=3 ∧ b_check.res.cycles=3 := by decide +kernel
def b_failureCode : List (BitVec 32) := [0x130313,0xc35393,0xfe0382e3]
sym_block b_failure := symRun {noAlias:=true} b_failureCode (pcOf 246508) 40
theorem b_failure_counts : b_failure.res.steps=3 ∧ b_failure.res.cycles=3 := by decide +kernel
def b_lastCode : List (BitVec 32) := [0xfff30313]
sym_block b_last := symRun {noAlias:=true} b_lastCode (pcOf 246511) 40
theorem b_last_counts : b_last.res.steps=1 ∧ b_last.res.cycles=1 := by decide +kernel
def b_postCode : List (BitVec 32) := [0x1053383,0xb3d393,0xf3f393,0x7f03e393,0xc39393,0x63b023,0x48003303,0x48803383,0xfa9ff06f]
sym_block b_post := symRun {noAlias:=true} b_postCode (pcOf 246512) 40
theorem b_post_counts : b_post.res.steps=9 ∧ b_post.res.cycles=9 := by decide +kernel
def c_saveCode : List (BitVec 32) := [0x48603023,0x48703423,0x313,0x2053423]
sym_block c_save := symRun {noAlias:=true} c_saveCode (pcOf 235811) 40
theorem c_save_counts : c_save.res.steps=4 ∧ c_save.res.cycles=4 := by decide +kernel
def c_preHashCode : List (BitVec 32) := [0x2653023,0x73]
sym_block c_preHash := symRun {noAlias:=true} c_preHashCode (pcOf 235815) 40
theorem c_preHash_counts : c_preHash.res.steps=1 ∧ c_preHash.res.cycles=1 := by decide +kernel
def c_checkCode : List (BitVec 32) := [0x1853383,0x7033b3,0x439393,0x407603b3,0x183b383,0x3c3d393,0x38a63]
sym_block c_check := symRun {noAlias:=true} c_checkCode (pcOf 235817) 40
theorem c_check_counts : c_check.res.steps=7 ∧ c_check.res.cycles=7 := by decide +kernel
def c_failureCode : List (BitVec 32) := [0x130313,0xc35393,0xfc038ae3]
sym_block c_failure := symRun {noAlias:=true} c_failureCode (pcOf 235824) 40
theorem c_failure_counts : c_failure.res.steps=3 ∧ c_failure.res.cycles=3 := by decide +kernel
def c_lastCode : List (BitVec 32) := [0xfff30313]
sym_block c_last := symRun {noAlias:=true} c_lastCode (pcOf 235827) 40
theorem c_last_counts : c_last.res.steps=1 ∧ c_last.res.cycles=1 := by decide +kernel
/-- C47: the c8 grinder's exit (expand only): the ground-pad slot is the constant `0x7fb000` (`lui t2,0x7fb`, four
`nop`s), then `sd t1,0(t2); ld t1,1152(zero); ld t2,1160(zero)`. The final `jal zero,46862` (straight to the expand
continuation; `ra` holds the c8 heap-6 label) is site dependent and not part of this block. -/
def c_postCode : List (BitVec 32) := [0x7fb3b7,0x13,0x13,0x13,0x13,0x63b023,0x48003303,0x48803383]
sym_block c_post := symRun {noAlias:=true} c_postCode (pcOf 235828) 40
theorem c_post_counts : c_post.res.steps=8 ∧ c_post.res.cycles=8 := by decide +kernel
#print axioms b_check_counts
#print axioms c_check_counts
#print axioms b_post_counts
#print axioms c_post_counts
end OuterNodeMachineBlocks
