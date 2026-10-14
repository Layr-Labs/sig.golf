import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Compact2Final
import SigGolfCandidate.Choice.ProducerFinish

namespace SigGolfCandidate.Choice.ProducerHintMemory
open RiscvZkvm.Rv64
open ClaudeWCT.W9.Machine.Expand.Compact2
set_option Elab.async false
set_option maxRecDepth 100000

/-- Witness compaction leaves the saved selector outside its write ranges.
The 42-slot tail stores sit 96 bytes below the 48-slot addresses; the hint word does not. -/
theorem run2_hint (M : Nat → Word) (idx : Nat) :
    run2Mem M idx ProducerSelector.HINT=M ProducerSelector.HINT := by
  change run2Mem M idx 132184=M 132184
  unfold run2Mem
  have htail : tailMem (layMem (layMem (layMem (topMem (stMem M)) 1 idx) 2 idx) 3 idx) 132184
      = layMem (layMem (layMem (topMem (stMem M)) 1 idx) 2 idx) 3 idx 132184 := by
    unfold tailMem WIT
    rw [if_neg (show (132184 : Nat) ≠ 2048 + 20872 by decide),
      if_neg (show (132184 : Nat) ≠ 2048 + 20864 by decide),
      if_neg (show (132184 : Nat) ≠ 2048 + 20856 by decide),
      if_neg (show (132184 : Nat) ≠ 2048 + 20848 by decide)]
  rw [htail]
  rw [layMem_out _ 3 (by decide) _ _ (by decide),
    layMem_out _ 2 (by decide) _ _ (by decide),
    layMem_out _ 1 (by decide) _ _ (by decide)]
  unfold topMem WIT
  rw [if_neg (by decide)]
  unfold stMem
  rw [plMem_out _ 9 le_rfl _ (by decide)]
  unfold regsMem ctrMem zMem snapMem WOUT SNAP2
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]

end SigGolfCandidate.Choice.ProducerHintMemory
#print axioms SigGolfCandidate.Choice.ProducerHintMemory.run2_hint
