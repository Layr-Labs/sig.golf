import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Base

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
def eI (rd rs1 imm : Nat) : BitVec 32 := BitVec.ofNat 32 (imm % 4096 * 2 ^ 20 + rs1 * 2 ^ 15 + rd * 2 ^ 7 + 0x13)
def eL (rd rs1 imm : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (imm % 4096 * 2 ^ 20 + rs1 * 2 ^ 15 + 3 * 2 ^ 12 + rd * 2 ^ 7 + 0x03)
def eS (f3 rs2 off rs1 : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (off / 32 * 2 ^ 25 + rs2 * 2 ^ 20 + rs1 * 2 ^ 15 + f3 * 2 ^ 12 + off % 32 * 2 ^ 7 + 0x23)
/-- T8 expand scratch region: chain `t`'s 64-byte block (value at +48; chain 0's value is the leaf start 816). -/
def offC (t : Nat) : Nat := 768 - 64 * t
/-- Leaf slot of chain `t`: `end0 | hdr 832 | pad 848 | end1..end5` at 816 / 848 + 16 t. -/
def slotC (t : Nat) : Nat := if t = 0 then 816 else 848 + 16 * t
def qK (t st : Nat) : Nat := 0x80 + 4 * t + 256 * st
def headW (t st a2 : Nat) : List (BitVec 32) :=
  [eI 10 8 (offC t), eI 12 8 a2, eI 25 31 (qK t st), eS 3 25 16 10, 0x00000073]
/-- Register holding the step byte: x7 = 1, x13 = 2, x19 = 3. -/
def stepReg (step : Nat) : Nat := if step = 1 then 7 else if step = 2 then 13 else 19
def rungW (step : Nat) (dst : Option Nat) : List (BitVec 32) :=
  [eS 0 (stepReg step) 17 10] ++ (match dst with | some d => [eI 12 8 d] | none => []) ++ [0x00000073]
def copyW (t : Nat) : List (BitVec 32) :=
  [eL 3 8 (offC t + 48), eL 14 8 (offC t + 56), eS 3 3 (slotC t) 8, eS 3 14 (slotC t + 8) 8]
def leafW : List (BitVec 32) :=
  [eI 25 31 1537, eS 3 25 832 8, eS 3 0 840 8, eI 10 8 816, eI 11 0 128, 0x000b8067]
def ownC (z : List Nat) (t : Nat) : Bool := decide (0 < t) && decide (t < 5) && decide (z.getD (t + 1) 0 = 0)
def a2C (t d : Nat) (own : Bool) : Nat := if d = 1 then (if own then offC t + 48 else slotC t) else offC t + 48
def rungDst (t step : Nat) (own : Bool) : Option Nat :=
  if step = 3 ∧ own = false ∧ t ≠ 0 then some (slotC t) else none
def rungsW (t d : Nat) (own : Bool) : List (BitVec 32) :=
  (List.range' (5 - d) (d - 1)).flatMap fun step => rungW step (rungDst t step own)
def chainW (t d : Nat) (own : Bool) : List (BitVec 32) :=
  headW t (4 - d) (a2C t d own) ++ rungsW t d own ++ (if own then copyW t else [])
def aX (r : Reg) (o : Nat) : Addr := ⟨some (.reg r), BitVec.ofNat 64 o⟩
def eX (r : Reg) (o : Nat) : E := .bin .add (.reg r) (.c (BitVec.ofNat 64 o))
def hbO (w : Nat) : Nat := 2 ^ 64 - 2048 + w
def headSt (t st a2 : Nat) : SymState :=
  ⟨((RegFile.init.set .x10 (eX .x8 (offC t))).set .x12 (eX .x8 a2)).set .x25 (eX .x31 (qK t st)),
    [(aX .x8 (offC t + 16), eX .x31 (qK t st))],
    [.valid (aX .x8 (offC t + 16)) 8]⟩
def headR (t st a2 : Nat) (p : Word) : Result := ⟨headSt t st a2, .c (p + 4 + 4 + 4 + 4), .ecall, 4, 4⟩
def rungSt (step : Nat) (dst : Option Nat) : SymState :=
  ⟨match dst with
    | some d => RegFile.init.set .x12 (eX .x8 d)
    | none => RegFile.init,
    [(aX .x10 16, .bin (.st .b 1) (.ld (eX .x10 16)) (.reg (if step = 1 then .x7 else if step = 2 then .x13 else .x19)))],
    [.align8 (.reg .x10), .valid (aX .x10 17) 1]⟩
def rungR (step : Nat) (dst : Option Nat) (p : Word) : Result :=
  match dst with
  | some _ => ⟨rungSt step dst, .c (p + 4 + 4), .ecall, 2, 2⟩
  | none => ⟨rungSt step dst, .c (p + 4), .ecall, 1, 1⟩
def copySt (t : Nat) : SymState :=
  ⟨(RegFile.init.set .x3 (.ld (eX .x8 (offC t + 48)))).set .x14 (.ld (eX .x8 (offC t + 56))),
    [(aX .x8 (slotC t + 8), .ld (eX .x8 (offC t + 56))), (aX .x8 (slotC t), .ld (eX .x8 (offC t + 48)))],
    [.valid (aX .x8 (slotC t + 8)) 8, .valid (aX .x8 (slotC t)) 8, .valid (aX .x8 (offC t + 56)) 8,
      .valid (aX .x8 (offC t + 48)) 8]⟩
def copyR (t : Nat) (p : Word) : Result := ⟨copySt t, .c (p + 4 + 4 + 4 + 4), .fuel, 4, 4⟩
def leafSt : SymState :=
  ⟨((RegFile.init.set .x25 (.bin .add (.reg .x31) (.c 0x601#64))).set .x10 (eX .x8 816)).set .x11 (.c 128#64),
    [(aX .x8 840, .c 0#64), (aX .x8 832, .bin .add (.reg .x31) (.c 0x601#64))],
    [.valid (aX .x8 840) 8, .valid (aX .x8 832) 8]⟩
def leafR : Result := ⟨leafSt, .bin .and (.reg .x23) (.c 0xfffffffffffffffe#64), .jump, 6, 6⟩
abbrev cfgE : Config := { noAlias := true }
end ClaudeWCT.W9.Machine.Expand
