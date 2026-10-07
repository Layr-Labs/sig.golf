import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.CompactCoord
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Rotate

namespace ClaudeWCT.W9.Machine.Expand.Rotation
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
def cfgR : Config := { noAlias := true }
def startWords : List (BitVec 32) :=
  [6455,2148087683,2156476419,2164877443,2181629203,2148074899,5687,2857764371,4204785903]
def tailWords : List (BitVec 32) :=
  [26935,3539549219,3574149155,3523819555,19,3541644323,1049235,1299,115]
sym_block RStart := symRun cfgR startWords (pcOf 42144) 40
sym_block RTail := symRun cfgR tailWords (pcOf 42153) 40

section
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem code_start : CodeAt im (pcOf 42144) startWords :=
  codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_tail : CodeAt im (pcOf 42153) tailWords :=
  codeAt_of_window hc (by decide) (by decide +kernel)

theorem start_spec (s : MachineState) (hpc : s.pc = pcOf 42144) :
    ∃ t, Steps im s 9 9 t ∧ t.pc = pcOf 42130 ∧
      t.getReg .x10 = BitVec.ofNat 64 2080 ∧ t.getReg .x11 = BitVec.ofNat 64 2048 ∧
      t.getReg .x12 = BitVec.ofNat 64 2725 ∧ t.getReg .x1 = pcOf 42153 ∧
      t.getReg .x15 = s.getMem (BitVec.ofNat 64 2048) ∧
      t.getReg .x16 = s.getMem (BitVec.ofNat 64 2056) ∧
      t.getReg .x17 = LoadKind.wu.fromWord (s.getMem (BitVec.ofNat 64 2064)) 0 ∧
      RegsExcept s t [.x1,.x10,.x11,.x12,.x15,.x16,.x17,.x18] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RStart (code_start hc) s hpc (by simp [RStart.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, RStart.res, E.eval]
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]
  · c_regs RStart.res
  · intro A _ _; rfl

theorem tail_spec (s : MachineState) (hpc : s.pc = pcOf 42153) :
    Steps im s 8 8 (RTail.res.toState s) ∧
      (RTail.res.toState s).pc = pcOf 42161 ∧
      (RTail.res.toState s).getReg .x5 = 1 ∧
      (RTail.res.toState s).getReg .x10 = 0 ∧
      fetch im (RTail.res.toState s) = some (.base .ECALL) := by
  have he : CodeAt im (pcOf 42161) [115] := codeAt_of_window hc (by decide) (by decide +kernel)
  refine ⟨symRun_sound RTail (code_tail hc) s hpc (by simp [RTail.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [RTail.res, Result.toState_pc, E.eval]
  · simp [RTail.res, rv_simp]
  · simp [RTail.res, rv_simp]
  · rw [he.fetch _ (by simp [RTail.res, Result.toState_pc, E.eval])]; rfl
end
#print axioms start_spec
#print axioms tail_spec
end ClaudeWCT.W9.Machine.Expand.Rotation
