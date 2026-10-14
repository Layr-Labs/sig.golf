import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsRuns

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_5 : okF 5 = true := by decide +kernel
private theorem component_okC_5 : okC 5 = true := by decide +kernel
private theorem component_okQ_5 : okQ 5 = true := by decide +kernel
private theorem component_okS_5 : okS 5 = true := by decide +kernel
private theorem component_okChk_5 : okChk 5 = true := by decide +kernel
private theorem component_okStp_5 : okStp 5 = true := by decide +kernel
private theorem component_okLc_5 : okLc 5 = true := by decide +kernel
private theorem component_okTail_5 : okTail 5 = true := by decide +kernel
theorem okCoord_5 : okCoord 5 = true := by
  simp only [okCoord, component_okF_5, component_okC_5, component_okQ_5, component_okS_5, component_okChk_5, component_okStp_5, component_okLc_5, component_okTail_5, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_5 : SigGolfCandidate.T3M.Verify.optBeq (runZ 5) (expZ 5) = true := by decide +kernel
private theorem component_okC_5 : okC 5 = true := by decide +kernel
private theorem component_okQ_5 : okQ 5 = true := by decide +kernel
private theorem component_okS_5 : okS 5 = true := by decide +kernel
private theorem component_okChk_5 : okChk 5 = true := by decide +kernel
private theorem component_okStp_5 : okStp 5 = true := by decide +kernel
private theorem component_okLc_5 : okLc 5 = true := by decide +kernel
theorem okCoord_5 : okCoord 5 = true := by
  simp only [okCoord, component_z_5, component_okC_5, component_okQ_5, component_okS_5, component_okChk_5, component_okStp_5, component_okLc_5, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
