import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsRuns

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_2 : okF 2 = true := by decide +kernel
private theorem component_okC_2 : okC 2 = true := by decide +kernel
private theorem component_okQ_2 : okQ 2 = true := by decide +kernel
private theorem component_okS_2 : okS 2 = true := by decide +kernel
private theorem component_okChk_2 : okChk 2 = true := by decide +kernel
private theorem component_okStp_2 : okStp 2 = true := by decide +kernel
private theorem component_okLc_2 : okLc 2 = true := by decide +kernel
private theorem component_okTail_2 : okTail 2 = true := by decide +kernel
theorem okCoord_2 : okCoord 2 = true := by
  simp only [okCoord, component_okF_2, component_okC_2, component_okQ_2, component_okS_2, component_okChk_2, component_okStp_2, component_okLc_2, component_okTail_2, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_2 : SigGolfCandidate.T3M.Verify.optBeq (runZ 2) (expZ 2) = true := by decide +kernel
private theorem component_okC_2 : okC 2 = true := by decide +kernel
private theorem component_okQ_2 : okQ 2 = true := by decide +kernel
private theorem component_okS_2 : okS 2 = true := by decide +kernel
private theorem component_okChk_2 : okChk 2 = true := by decide +kernel
private theorem component_okStp_2 : okStp 2 = true := by decide +kernel
private theorem component_okLc_2 : okLc 2 = true := by decide +kernel
theorem okCoord_2 : okCoord 2 = true := by
  simp only [okCoord, component_z_2, component_okC_2, component_okQ_2, component_okS_2, component_okChk_2, component_okStp_2, component_okLc_2, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
