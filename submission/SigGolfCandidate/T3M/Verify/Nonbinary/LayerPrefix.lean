import SigGolfCandidate.Rv

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
/-- Campaign S2: the L1 root-block tail after the top encoding hash. `s0` (`x8`, the top-chain anchor 11920) is set
earlier, in the L1 path level with the lowest window, so the tail no longer depends on the root window `a`. -/
def prefixWordsOf (_a : Nat) : List (BitVec 32) :=
  [0x63803,0x863883,0x3a8de93,0x0e84b303,0xc81713,0x677733,0x20023c23,0x49070067]
def aVals : List Nat := [13712,14016]
sym_block prefixBase := symRun { noAlias := true } (prefixWordsOf 13712) (BitVec.ofNat 64 (0x1000 + 4 * 1070)) 200
def prefixRegs (_a : Nat) : RegFile := prefixBase.res.st.regs
def prefixRes (a : Nat) : Result :=
  { prefixBase.res with st := { prefixBase.res.st with regs := prefixRegs a } }
end SigGolfCandidate.T3M.Verify.Nonbinary
