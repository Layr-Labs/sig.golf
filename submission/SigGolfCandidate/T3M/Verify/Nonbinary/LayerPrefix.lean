import SigGolfCandidate.Rv

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
def prefixWordsOf (a : Nat) : List (BitVec 32) :=
  [0x63803,0x863883,0x378de93,0x0e84b303,
   BitVec.ofNat 32 ((4096 - (a - 12480)) % 4096 * 2 ^ 20 + 10 * 2 ^ 15 + 8 * 2 ^ 7 + 0x13),
   0xa81713,0x677733,0x42070067]
def aVals : List Nat := [14272,14288,14304,14336,14368,14384,14400,14432,14464,14480,14496,14528]
sym_block prefixBase := symRun { noAlias := true } (prefixWordsOf 14464) (BitVec.ofNat 64 (0x1000 + 4 * 48176)) 200
def prefixRegs (a : Nat) : RegFile :=
  prefixBase.res.st.regs.set .x8 (.bin .add (.reg .x10) (.c (BitVec.ofNat 64 (2 ^ 64 - (a - 12480)))))
def prefixRes (a : Nat) : Result :=
  { prefixBase.res with st := { prefixBase.res.st with regs := prefixRegs a } }
end SigGolfCandidate.T3M.Verify.Nonbinary
