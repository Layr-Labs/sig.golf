import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsRuns

namespace ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
theorem okCoord_5 : okCoord 5 = true := by
  unfold okCoord
  have hF : okF 5 = true := by decide +kernel
  have hQ : okQ 5 = true := by decide +kernel
  have hP : okP 5 = true := by decide +kernel
  have hS : okS 5 = true := by decide +kernel
  have hChk : okChk 5 = true := by decide +kernel
  have hStp : okStp 5 = true := by decide +kernel
  have hLc : okLc 5 = true := by decide +kernel
  have hTail : okTail 5 = true := by decide +kernel
  simp only [hF, hQ, hP, hS, hChk, hStp, hLc, hTail, Bool.and_true]
end ClaudeWCT.W9.Machine.Sign
