import SigGolfCandidate.Rv

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
/-- Configuration (1)+(2), e7b head: the top-half selector (7 words at `h+6..h+12`).
`lb gp,528(tp); bge gp,zero,L` (hint byte at abs 25216: bit 7 clear = LOW, 4 cycles);
`lbu gp,15(a2); bltu gp,a1,L` (LOW forced when its top byte is `< 64`, i.e. LOW `< 2^126`: 6 cycles);
`addi a2,a2,16` (HIGH, 7 cycles); `L: ld a7,8(a2); ld a6,0(a2)`. -/
def prefixHint : List (BitVec 32) := [0x21020183,0x1d863]
def prefixHead : List (BitVec 32) := [0xf64183,0xb1e463]
def prefixHigh : List (BitVec 32) := [0x1060613]
def prefixLoad : List (BitVec 32) := [0x863883,0x63803]
def prefixTailWordsOf (a : Nat) : List (BitVec 32) :=
  [0x3a8de93,0x0e84b303,
   BitVec.ofNat 32 ((4096 - (a - 13432)) % 4096 * 2 ^ 20 + 10 * 2 ^ 15 + 8 * 2 ^ 7 + 0x13),
   0xc81713,0x677733,0x49070067]
/-! Top-half selector parameters. The head of every top copy is `prefixSel` (at `h+6`) followed by the 6-word
dispatch tail. To swap the selector, change `prefixSel`/`selLen`/`selHintBit` here and `selCost` + the proof of
`prefix_select_spec` (Nonbinary/LayerContext.lean); `topTransition` and `Compose.top_after_hash` only use the spec
(exact cost `selCost high a ≤ selMax`). -/
def prefixSel : List (BitVec 32) := prefixHint ++ prefixHead ++ prefixHigh ++ prefixLoad
def selLen : Nat := 7
theorem prefixSel_length : prefixSel.length = selLen := rfl
/-- The bit of the witness choice byte (abs 25216) that requests HIGH. -/
def selHintBit : Nat := 7
def prefixWordsOf (a : Nat) : List (BitVec 32) :=
  prefixSel ++ prefixTailWordsOf a
def aVals : List Nat := [15288,15304,15336,15352,15384,15400,15432,15448,15480]
sym_block prefixBase := symRun { noAlias := true } (prefixTailWordsOf 15384) (BitVec.ofNat 64 (0x1000 + 4 * 1080)) 200
def prefixRegs (a : Nat) : RegFile :=
  prefixBase.res.st.regs.set .x8 (.bin .add (.reg .x10) (.c (BitVec.ofNat 64 (2 ^ 64 - (a - 13432)))))
def prefixRes (a : Nat) : Result :=
  { prefixBase.res with st := { prefixBase.res.st with regs := prefixRegs a } }
sym_block prefixHintBase := symRun { noAlias := true } prefixHint (BitVec.ofNat 64 (0x1000 + 4*1070)) 200
sym_block prefixHeadBase := symRun { noAlias := true } prefixHead (BitVec.ofNat 64 (0x1000 + 4*1072)) 200
sym_block prefixHighBase := symRun { noAlias := true } prefixHigh (BitVec.ofNat 64 (0x1000 + 4*1074)) 200
sym_block prefixLoadBase := symRun { noAlias := true } prefixLoad (BitVec.ofNat 64 (0x1000 + 4*1075)) 200
def hintByte : E := .un (.ld .b 0) (.ld (.bin .add (.reg .x4) (.c 528)))
def headByte : E := .un (.ld .bu 7) (.ld (.bin .add (.reg .x12) (.c 8)))
def prefixHintRes (p : Word) : Result :=
  {prefixHintBase.res with pc := (E.ite .ge hintByte (.c 0) (.c (p+4+16)) (.c (p+4+4)))}
def prefixHeadRes (p : Word) : Result :=
  {prefixHeadBase.res with pc := (E.ite .ltu headByte (.reg .x11) (.c (p+4+8)) (.c (p+4+4)))}
def prefixHighRes (p : Word) : Result := {prefixHighBase.res with pc := .c (p+4)}
def prefixLoadRes (p : Word) : Result := {prefixLoadBase.res with pc := .c (p+4+4)}
theorem prefixHint_run (p : Word) :
    symRun {noAlias := true} prefixHint p 200 = some (prefixHintRes p) := by rfl
theorem prefixHead_run (p : Word) :
    symRun {noAlias := true} prefixHead p 200 = some (prefixHeadRes p) := by rfl
theorem prefixHigh_run (p : Word) :
    symRun {noAlias := true} prefixHigh p 200 = some (prefixHighRes p) := by rfl
theorem prefixLoad_run (p : Word) :
    symRun {noAlias := true} prefixLoad p 200 = some (prefixLoadRes p) := by rfl
end SigGolfCandidate.T3M.Verify.Nonbinary
