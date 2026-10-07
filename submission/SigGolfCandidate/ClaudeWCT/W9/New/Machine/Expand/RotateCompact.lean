import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Compact
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RotateCorrect

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M

def rotatedCompactC : Nat := compactC + 16369
def RotatedCompactGood (im : Image) : Prop :=
  NewCodeAt im → CodeAt im (pcOf 351) [compactJal] → ∀ N w s, CompactPre N w s →
    ∃ t, Steps im s rotatedCompactC rotatedCompactC t ∧ t.pc = pcOf 42161 ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
      t.readWords (BitVec.ofNat 64 2048) 2729 = wordsOf (ClaudeWCT.W9.T3M.witList N w)

namespace Rotation
def jumpWord : BitVec 32 := 62914671
theorem jump_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hp : s.pc = pcOf 42129) :
    Steps im s 1 1 (s.setPC (pcOf 42144)) := by
  have hcode : CodeAt im (pcOf 42129) [jumpWord] := codeAt_of_window hc (by decide) (by decide +kernel)
  obtain ⟨imm, hd, hoff⟩ := jalTo_sound (show jalTo jumpWord 42129 = some 42144 by decide)
  exact jal_x0_step hcode hd hoff s hp
end Rotation

theorem rotatedCompactGood_holds (im : Image) : RotatedCompactGood im := by
  intro hc hJ N w s hpre
  obtain ⟨u, su, pu, u5, u10, uw⟩ := compactGood_holds im hc hJ N w s hpre
  have sj := Rotation.jump_spec hc u pu
  have hu : (u.setPC (pcOf 42144)).readWords (BitVec.ofNat 64 2048) 2729 =
      wordsOf (ClaudeWCT.W9.T3M.legacyWitList N w) := by
    change u.readWords (BitVec.ofNat 64 2048) 2729 = _
    exact uw
  obtain ⟨t, st, pt, t5, t10, ht, tw⟩ := Rotation.rotate_witness_spec hc N w (u.setPC (pcOf 42144)) rfl hu
  exact ⟨t, ((su.trans sj).trans st).of_eq (by unfold rotatedCompactC; omega)
    (by unfold rotatedCompactC; omega), pt, t5, t10, tw⟩

#print axioms rotatedCompactGood_holds
end ClaudeWCT.W9.Machine.Expand
