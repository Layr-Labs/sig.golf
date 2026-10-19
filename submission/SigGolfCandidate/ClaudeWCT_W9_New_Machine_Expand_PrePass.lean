import SigGolfCandidate.T3M_Expand_Blocks
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_PrePassBits

/-! # img-v6 expand pre-pass (words 43250 .. 43333, r3-lean-topbytes)

Entered from word 0 (`jal 43250`). Unpacks the 5,239-byte signature (at `0x7000`) in place into the 5,248-byte layout
read by the rest of the expander: the 55-bit field `X` stored in the top `j` bits of path node `j = 1..10`
(digest `168 + j`, top half-word at `0x7000 + 16 (168 + j) + 14`) is collected (`X |= (w >> (16 - j)) << xOff j`) and
cleared; byte `5239 := X % 2^8`; dword `5240 := (X / 2^8) % 2^34 + (X / 2^42) * 2^48` (top sibling bits 64..97 and the
hint at `5246`); then `jal 44096` (the old entry). -/

namespace ClaudeWCT.W9.Machine.Expand.PrePass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def cPre : List (BitVec 32) := [0x8f37,0x393,0xa9ef5e03,0xfe5313,0x63e3b3,0x31e1e13,0x31e5e13,0xa9cf1f23,0xaaef5e03,0xee5313,0x131313,0x63e3b3,0x32e1e13,0x32e5e13,0xabcf1723,0xabef5e03,0xde5313,0x331313,0x63e3b3,0x33e1e13,0x33e5e13,0xabcf1f23,0xacef5e03,0xce5313,0x631313,0x63e3b3,0x34e1e13,0x34e5e13,0xadcf1723,0xadef5e03,0xbe5313,0xa31313,0x63e3b3,0x35e1e13,0x35e5e13,0xadcf1f23,0xaeef5e03,0xae5313,0xf31313,0x63e3b3,0x36e1e13,0x36e5e13,0xafcf1723,0xafef5e03,0x9e5313,0x1531313,0x63e3b3,0x37e1e13,0x37e5e13,0xafcf1f23,0xb0ef5e03,0x8e5313,0x1c31313,0x63e3b3,0x38e1e13,0x38e5e13,0xb1cf1723,0xb1ef5e03,0x7e5313,0x2431313,0x63e3b3,0x39e1e13,0x39e5e13,0xb1cf1f23,0xb2ef5e03,0x6e5313,0x2d31313,0x63e3b3,0x3ae1e13,0x3ae5e13,0xb3cf1723,0x467f0ba3,0x83d313,0x1e31313,0x1e35313,0x2a3de13,0x30e1e13,0x1c36333,0x466f3c23,0x313,0x393,0xe13,0xf13,0x3ed0006f]

theorem cPre_length : cPre.length = 84 := rfl

theorem codeAt_pre : CodeAt Images.expandImage (pcOf 43250) cPre :=
  codeAt_expand_current_chunk (by decide) (by decide) (by decide +kernel)

sym_block ePre := symRun { noAlias := true } cPre (pcOf 43250) 100
#eval (ePre.res.st.mem.map (·.1.off.toNat), ePre.res.st.obl.length, ePre.res.steps, ePre.res.cycles)

/-- Memory after the pre-pass, as a function of the memory `M` before it (absolute dword addresses:
`33912 = 0x7000 + 5240`, `33904 = 0x7000 + 5232`, `pA i = 0x7000 + 16 (168 + i) + 8`). -/
def preMem (M : Word → Word) (A : Word) : Word :=
  if A = BitVec.ofNat 64 33912 then dW (xW M)
  else if A = BitVec.ofNat 64 33904 then replaceByte (M (BitVec.ofNat 64 33904)) 7 ((xW M).truncate 8)
  else if A = BitVec.ofNat 64 (pA 10) then clrW 10 (M (BitVec.ofNat 64 (pA 10)))
  else if A = BitVec.ofNat 64 (pA 9) then clrW 9 (M (BitVec.ofNat 64 (pA 9)))
  else if A = BitVec.ofNat 64 (pA 8) then clrW 8 (M (BitVec.ofNat 64 (pA 8)))
  else if A = BitVec.ofNat 64 (pA 7) then clrW 7 (M (BitVec.ofNat 64 (pA 7)))
  else if A = BitVec.ofNat 64 (pA 6) then clrW 6 (M (BitVec.ofNat 64 (pA 6)))
  else if A = BitVec.ofNat 64 (pA 5) then clrW 5 (M (BitVec.ofNat 64 (pA 5)))
  else if A = BitVec.ofNat 64 (pA 4) then clrW 4 (M (BitVec.ofNat 64 (pA 4)))
  else if A = BitVec.ofNat 64 (pA 3) then clrW 3 (M (BitVec.ofNat 64 (pA 3)))
  else if A = BitVec.ofNat 64 (pA 2) then clrW 2 (M (BitVec.ofNat 64 (pA 2)))
  else if A = BitVec.ofNat 64 (pA 1) then clrW 1 (M (BitVec.ofNat 64 (pA 1)))
  else M A

theorem ePre_mem (s : MachineState) (A : Word) : memEval s ePre.res.st.mem A = preMem s.getMem A := rfl

/-- The pre-pass: from pc 43250, 84 straight-line steps to the old entry 44096. -/
theorem pre_spec (s : MachineState) (hpc : s.pc = pcOf 43250) :
    ∃ t, Steps Images.expandImage s 84 84 t ∧ t.pc = pcOf 44096 ∧
      t.getReg .x6 = 0 ∧ t.getReg .x7 = 0 ∧ t.getReg .x28 = 0 ∧ t.getReg .x30 = 0 ∧
      RegsExcept s t [.x6, .x7, .x28, .x30] ∧ ∀ A, t.getMem A = preMem s.getMem A := by
  refine ⟨_, symRun_sound ePre codeAt_pre s hpc trivial, rfl, rfl, rfl, rfl, rfl, ?_, fun A => ePre_mem s A⟩
  intro x hx
  rw [Result.toState_getReg]
  cases x <;> first | rfl | (exfalso; simp at hx)

#print axioms pre_spec
end ClaudeWCT.W9.Machine.Expand.PrePass
