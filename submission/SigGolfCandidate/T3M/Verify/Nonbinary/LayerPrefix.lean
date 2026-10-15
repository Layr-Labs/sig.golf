import SigGolfCandidate.Choice.MachineSelect

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
abbrev prefixHead := Choice.MachineSelect.head
abbrev prefixChoose := Choice.MachineSelect.choose
abbrev prefixReadLow := Choice.MachineSelect.readLow
abbrev prefixReadHigh := Choice.MachineSelect.readHigh
def prefixTailWordsOf (a : Nat) : List (BitVec 32) :=
  [0x3a8de93,0x0e84b303,
   BitVec.ofNat 32 ((4096 - (a - 11808)) % 4096 * 2 ^ 20 + 10 * 2 ^ 15 + 8 * 2 ^ 7 + 0x13),
   0xc81713,0x677733,0x49070067]
def prefixWordsOf (a : Nat) : List (BitVec 32) :=
  prefixHead ++ prefixChoose ++ prefixReadLow ++ prefixReadHigh ++ prefixTailWordsOf a
def aVals : List Nat := [13664,13680,13712,13728,13760,13776,13808,13824,13856]
sym_block prefixBase := symRun { noAlias := true } (prefixTailWordsOf 13760) (BitVec.ofNat 64 (0x1000 + 4 * 1080)) 200
def prefixRegs (a : Nat) : RegFile :=
  prefixBase.res.st.regs.set .x8 (.bin .add (.reg .x10) (.c (BitVec.ofNat 64 (2 ^ 64 - (a - 11808)))))
def prefixRes (a : Nat) : Result :=
  { prefixBase.res with st := { prefixBase.res.st with regs := prefixRegs a } }
end SigGolfCandidate.T3M.Verify.Nonbinary
