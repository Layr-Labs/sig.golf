import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsRuns

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_7 : okF 7 = true := by decide +kernel
private theorem component_okC_7 : okC 7 = true := by decide +kernel
private theorem component_okQ_7 : okQ 7 = true := by decide +kernel
private theorem component_okS_7 : okS 7 = true := by decide +kernel
private theorem component_okChk_7 : okChk 7 = true := by decide +kernel
private theorem component_okStp_7 : okStp 7 = true := by decide +kernel
private theorem component_okLc_7 : okLc 7 = true := by decide +kernel
private theorem component_okTail_7 : okTail 7 = true := by decide +kernel
theorem okCoord_7 : okCoord 7 = true := by
  simp only [okCoord, component_okF_7, component_okC_7, component_okQ_7, component_okS_7, component_okChk_7, component_okStp_7, component_okLc_7, component_okTail_7, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_7 : SigGolfCandidate.T3M.Verify.optBeq (runZ 7) (expZ 7) = true := by decide +kernel
private theorem component_okC_7 : okC 7 = true := by decide +kernel
private theorem component_okQ_7 : okQ 7 = true := by decide +kernel
private theorem component_okS_7 : okS 7 = true := by decide +kernel
private theorem component_okChk_7 : okChk 7 = true := by decide +kernel
private theorem component_okStp_7 : okStp 7 = true := by decide +kernel
private theorem component_okLc_7 : okLc 7 = true := by decide +kernel
theorem okCoord_7 : okCoord 7 = true := by
  simp only [okCoord, component_z_7, component_okC_7, component_okQ_7, component_okS_7, component_okChk_7, component_okStp_7, component_okLc_7, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
