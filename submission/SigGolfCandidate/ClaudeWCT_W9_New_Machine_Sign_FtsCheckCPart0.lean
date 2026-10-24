import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsRuns

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_6 : okF 6 = true := by decide +kernel
private theorem component_okC_6 : okC 6 = true := by decide +kernel
private theorem component_okQ_6 : okQ 6 = true := by decide +kernel
private theorem component_okS_6 : okS 6 = true := by decide +kernel
private theorem component_okChk_6 : okChk 6 = true := by decide +kernel
private theorem component_okStp_6 : okStp 6 = true := by decide +kernel
private theorem component_okLc_6 : okLc 6 = true := by decide +kernel
private theorem component_okTail_6 : okTail 6 = true := by decide +kernel
theorem okCoord_6 : okCoord 6 = true := by
  simp only [okCoord, component_okF_6, component_okC_6, component_okQ_6, component_okS_6, component_okChk_6, component_okStp_6, component_okLc_6, component_okTail_6, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_6 : SigGolfCandidate.T3M.Verify.optBeq (runZ 6) (expZ 6) = true := by decide +kernel
private theorem component_okC_6 : okC 6 = true := by decide +kernel
private theorem component_okQ_6 : okQ 6 = true := by decide +kernel
private theorem component_okS_6 : okS 6 = true := by decide +kernel
private theorem component_okChk_6 : okChk 6 = true := by decide +kernel
private theorem component_okStp_6 : okStp 6 = true := by decide +kernel
private theorem component_okLc_6 : okLc 6 = true := by decide +kernel
theorem okCoord_6 : okCoord 6 = true := by
  simp only [okCoord, component_z_6, component_okC_6, component_okQ_6, component_okS_6, component_okChk_6, component_okStp_6, component_okLc_6, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
