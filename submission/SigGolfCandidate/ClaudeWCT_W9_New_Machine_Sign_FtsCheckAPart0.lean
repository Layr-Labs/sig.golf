import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsRuns

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_0 : okF 0 = true := by decide +kernel
private theorem component_okC_0 : okC 0 = true := by decide +kernel
private theorem component_okQ_0 : okQ 0 = true := by decide +kernel
private theorem component_okS_0 : okS 0 = true := by decide +kernel
private theorem component_okChk_0 : okChk 0 = true := by decide +kernel
private theorem component_okStp_0 : okStp 0 = true := by decide +kernel
private theorem component_okLc_0 : okLc 0 = true := by decide +kernel
private theorem component_okTail_0 : okTail 0 = true := by decide +kernel
theorem okCoord_0 : okCoord 0 = true := by
  simp only [okCoord, component_okF_0, component_okC_0, component_okQ_0, component_okS_0, component_okChk_0, component_okStp_0, component_okLc_0, component_okTail_0, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_0 : SigGolfCandidate.T3M.Verify.optBeq (runZ 0) (expZ 0) = true := by decide +kernel
private theorem component_okC_0 : okC 0 = true := by decide +kernel
private theorem component_okQ_0 : okQ 0 = true := by decide +kernel
private theorem component_okS_0 : okS 0 = true := by decide +kernel
private theorem component_okChk_0 : okChk 0 = true := by decide +kernel
private theorem component_okStp_0 : okStp 0 = true := by decide +kernel
private theorem component_okLc_0 : okLc 0 = true := by decide +kernel
theorem okCoord_0 : okCoord 0 = true := by
  simp only [okCoord, component_z_0, component_okC_0, component_okQ_0, component_okS_0, component_okChk_0, component_okStp_0, component_okLc_0, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
