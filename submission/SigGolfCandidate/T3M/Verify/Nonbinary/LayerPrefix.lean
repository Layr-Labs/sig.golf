import SigGolfCandidate.Rv

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
def prefixHead : List (BitVec 32) := [0x863883,0x8d663]
def prefixLow : List (BitVec 32) := [0x63803,0xc0006f]
def prefixHigh : List (BitVec 32) := [0x1063803,0x1863883]
def prefixTailWordsOf (a : Nat) : List (BitVec 32) :=
  [0x3a8de93,0x0e84b303,
   BitVec.ofNat 32 ((4096 - (a - 11808)) % 4096 * 2 ^ 20 + 10 * 2 ^ 15 + 8 * 2 ^ 7 + 0x13),
   0xc81713,0x677733,0x49070067]
def prefixWordsOf (a : Nat) : List (BitVec 32) :=
  prefixHead ++ prefixLow ++ prefixHigh ++ prefixTailWordsOf a
def aVals : List Nat := [13664,13680,13712,13728,13760,13776,13808,13824,13856]
sym_block prefixBase := symRun { noAlias := true } (prefixTailWordsOf 13760) (BitVec.ofNat 64 (0x1000 + 4 * 1080)) 200
def prefixRegs (a : Nat) : RegFile :=
  prefixBase.res.st.regs.set .x8 (.bin .add (.reg .x10) (.c (BitVec.ofNat 64 (2 ^ 64 - (a - 11808)))))
def prefixRes (a : Nat) : Result :=
  { prefixBase.res with st := { prefixBase.res.st with regs := prefixRegs a } }
sym_block prefixHeadBase := symRun { noAlias := true } prefixHead (BitVec.ofNat 64 (0x1000 + 4*1074)) 200
sym_block prefixLowBase := symRun { noAlias := true } prefixLow (BitVec.ofNat 64 (0x1000 + 4*1076)) 200
sym_block prefixHighBase := symRun { noAlias := true } prefixHigh (BitVec.ofNat 64 (0x1000 + 4*1078)) 200

def prefixHeadRes (p : Word) : Result :=
  {prefixHeadBase.res with pc := (E.ite .ge (.ld (.bin .add (.reg .x12) (.c 8))) (.c 0)
    (.c (p+4+12)) (.c (p+4+4)))}
def prefixLowRes (p : Word) : Result :=
  {prefixLowBase.res with pc := .c (p+4+12)}
def prefixHighRes (p : Word) : Result :=
  {prefixHighBase.res with pc := .c (p+4+4)}
theorem prefixHead_run (p : Word) :
    symRun {noAlias := true} prefixHead p 200 = some (prefixHeadRes p) := by rfl
theorem prefixLow_run (p : Word) :
    symRun {noAlias := true} prefixLow p 200 = some (prefixLowRes p) := by rfl
theorem prefixHigh_run (p : Word) :
    symRun {noAlias := true} prefixHigh p 200 = some (prefixHighRes p) := by rfl
end SigGolfCandidate.T3M.Verify.Nonbinary
