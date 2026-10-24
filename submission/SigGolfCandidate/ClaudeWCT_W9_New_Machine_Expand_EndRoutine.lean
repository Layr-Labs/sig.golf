import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_Canon

/-! # Expand `end` routine (configuration e7b)

Word 47011 (formerly `addi a0,zero,0`) is `jal zero, 43071`. The routine at 43071..43076 loads the choice flag word
`mem[0x667F8]` (0, or 128 after the producer took HIGH), stores its low byte at abs 25216 = `WIT + choiceOff`
(`sb t1, 640(0x6000)`), sets `a0 := 0` and jumps to the witness-stack post-pass at 49400 (img-merged; was the halting `ecall` at
47012). -/

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def endCode : List (BitVec 32) := bv_list% 32 [0x00066e37,0x7f8e3303,0x00006e37,0x286e0023,0x00000513,0x2d00606f]
sym_block endRun := symRun { noAlias := true } endCode (pcOf 43071) 20

/-- The flag byte written by `end`. -/
def flagByte (s : MachineState) : BitVec 8 := (s.getMem (BitVec.ofNat 64 0x667F8)).truncate 8

theorem end_mem (s : MachineState) (A : Nat) (hA : A < 2^64) :
    (endRun.res.toState s).getMem (BitVec.ofNat 64 A) =
      if A = 25216 then replaceByte (s.getMem (BitVec.ofNat 64 25216)) 0 (flagByte s)
      else s.getMem (BitVec.ofNat 64 A) := by
  simp only [Result.toState_getMem,endRun.res,flagByte]
  t3n []
  all_goals (try rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA)])
  all_goals (split_ifs <;> first | rfl | omega)

theorem end_steps {im : Image} (hc : CodeAt im (pcOf 43071) endCode)
    (s : MachineState) (hpc : s.pc=pcOf 43071) :
    ∃t, Steps im s 6 6 t ∧ t.pc=pcOf 49400 ∧ t.getReg .x10=0#64 ∧
      t.getMem (BitVec.ofNat 64 25216)=replaceByte (s.getMem (BitVec.ofNat 64 25216)) 0 (flagByte s) ∧
      RegsExcept s t [.x6,.x10,.x28] ∧ Frame s t (fun A=>A=25216) := by
  refine ⟨_,symRun_sound endRun hc s hpc (by simp [endRun.res,rv_simp,accessValid_iff,MEMORY_BYTES]),?_,?_,?_,?_,?_⟩
  · simp [endRun.res, Result.toState_pc, E.eval]
  · simp [endRun.res, rv_simp]
  · rw [end_mem s 25216 (by norm_num), if_pos rfl]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    rw [end_mem s A hA, if_neg hn]

theorem installed_end : CodeAt Images.expandImage (pcOf 43071) endCode := by
  apply codeAt_expand_current_chunk <;> decide +kernel
end ClaudeWCT.W9.Machine.Expand.SharedScatter
