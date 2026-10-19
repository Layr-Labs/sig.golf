import SigGolfCandidate.Rv

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
/-- The `addi s0,a0,K` row-offset word of a top copy whose row address is `a` (`s0 = a0 - (a - 14128) = 14128`). -/
def rowWordOf (a : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((4096 - (a - 14128)) % 4096 * 2 ^ 20 + 10 * 2 ^ 15 + 8 * 2 ^ 7 + 0x13)
/-! ### d6b top head (img-v4 / img-v6): 18 words at `h+6..h+23` of every top copy
```
h+6   ld t1,232(s1); addi s0,a0,K          (dPro)
h+8   lb gp,528(tp); bge gp,zero,h+12      (dHint: hint byte at abs 25232, bit 7 clear = LOW)
h+10  lbu gp,15(a2); bgeu gp,a1,h+18       (dHead: LOW forced iff its top byte < 64, i.e. LOW < 2^126)
h+12  LOW:  ld a7,8(a2);  ld a6,0(a2);  srli t4,a7,58; slli a4,a6,12; and a4,a4,t1; jalr zero,1168(a4)
h+18  HIGH: ld a7,24(a2); ld a6,16(a2); srli t4,a7,58; slli a4,a6,12; and a4,a4,t1; jalr zero,1168(a4)
```
Selector costs (before the 6-word dispatch block): hint clear 4, hint set 6 (HIGH, or LOW forced). -/
def dProWordsOf (a : Nat) : List (BitVec 32) := [0xe84b303, rowWordOf a]
def dHint : List (BitVec 32) := [0x21020183,0x1d663]
def dHead : List (BitVec 32) := [0xf64183,0xb1fe63]
def dLow : List (BitVec 32) := [0x863883,0x63803,0x3a8de93,0xc81713,0x677733,0x49070067]
def dHigh : List (BitVec 32) := [0x1863883,0x1063803,0x3a8de93,0xc81713,0x677733,0x49070067]
/-- The bit of the witness choice byte (abs 25232) that requests HIGH. -/
def selHintBit : Nat := 7
def prefixWordsOf (a : Nat) : List (BitVec 32) :=
  dProWordsOf a ++ dHint ++ dHead ++ dLow ++ dHigh
def aVals : List Nat := [15336,15352,15384,15400,15432,15448,15480,15496,15528]
sym_block dProBase := symRun { noAlias := true } (dProWordsOf 15432) (BitVec.ofNat 64 (0x1000 + 4 * 1070)) 200
def dProRegs (a : Nat) : RegFile :=
  dProBase.res.st.regs.set .x8 (.bin .add (.reg .x10) (.c (BitVec.ofNat 64 (2 ^ 64 - (a - 14128)))))
def dProRes (a : Nat) (p : Word) : Result :=
  { dProBase.res with st := { dProBase.res.st with regs := dProRegs a }, pc := .c (p+4+4) }
sym_block dHintBase := symRun { noAlias := true } dHint (BitVec.ofNat 64 (0x1000 + 4*1072)) 200
sym_block dHeadBase := symRun { noAlias := true } dHead (BitVec.ofNat 64 (0x1000 + 4*1074)) 200
sym_block dLowBase := symRun { noAlias := true } dLow (BitVec.ofNat 64 (0x1000 + 4*1076)) 200
sym_block dHighBase := symRun { noAlias := true } dHigh (BitVec.ofNat 64 (0x1000 + 4*1082)) 200
def hintByte : E := .un (.ld .b 0) (.ld (.bin .add (.reg .x4) (.c 528)))
def headByte : E := .un (.ld .bu 7) (.ld (.bin .add (.reg .x12) (.c 8)))
def dHintRes (p : Word) : Result :=
  {dHintBase.res with pc := (E.ite .ge hintByte (.c 0) (.c (p+4+12)) (.c (p+4+4)))}
def dHeadRes (p : Word) : Result :=
  {dHeadBase.res with pc := (E.ite .geu headByte (.reg .x11) (.c (p+4+28)) (.c (p+4+4)))}
theorem dHint_run (p : Word) :
    symRun {noAlias := true} dHint p 200 = some (dHintRes p) := by rfl
theorem dHead_run (p : Word) :
    symRun {noAlias := true} dHead p 200 = some (dHeadRes p) := by rfl
theorem dLow_run (p : Word) :
    symRun {noAlias := true} dLow p 200 = some dLowBase.res := by rfl
theorem dHigh_run (p : Word) :
    symRun {noAlias := true} dHigh p 200 = some dHighBase.res := by rfl
theorem dPro_run (a : Nat) (ha : a ∈ aVals) (p : Word) :
    symRun { noAlias := true } (dProWordsOf a) p 200 = some (dProRes a p) := by
  simp only [aVals, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end SigGolfCandidate.T3M.Verify.Nonbinary
