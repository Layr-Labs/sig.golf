import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsRuns

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_3 : okF 3 = true := by decide +kernel
private theorem component_okC_3 : okC 3 = true := by decide +kernel
private theorem component_okQ_3 : okQ 3 = true := by decide +kernel
private theorem component_okS_3 : okS 3 = true := by decide +kernel
private theorem component_okChk_3 : okChk 3 = true := by decide +kernel
private theorem component_okStp_3 : okStp 3 = true := by decide +kernel
private theorem component_okLc_3 : okLc 3 = true := by decide +kernel
private theorem component_okTail_3 : okTail 3 = true := by decide +kernel
theorem okCoord_3 : okCoord 3 = true := by
  simp only [okCoord, component_okF_3, component_okC_3, component_okQ_3, component_okS_3, component_okChk_3, component_okStp_3, component_okLc_3, component_okTail_3, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_3 : SigGolfCandidate.T3M.Verify.optBeq (runZ 3) (expZ 3) = true := by decide +kernel
private theorem component_okC_3 : okC 3 = true := by decide +kernel
private theorem component_okQ_3 : okQ 3 = true := by decide +kernel
private theorem component_okS_3 : okS 3 = true := by decide +kernel
private theorem component_okChk_3 : okChk 3 = true := by decide +kernel
private theorem component_okStp_3 : okStp 3 = true := by decide +kernel
private theorem component_okLc_3 : okLc 3 = true := by decide +kernel
theorem okCoord_3 : okCoord 3 = true := by
  simp only [okCoord, component_z_3, component_okC_3, component_okQ_3, component_okS_3, component_okChk_3, component_okStp_3, component_okLc_3, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
