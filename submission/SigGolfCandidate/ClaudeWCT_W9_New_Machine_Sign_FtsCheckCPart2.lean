import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsRuns

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_8 : okF 8 = true := by decide +kernel
private theorem component_okC_8 : okC 8 = true := by decide +kernel
private theorem component_okQ_8 : okQ 8 = true := by decide +kernel
private theorem component_okS_8 : okS 8 = true := by decide +kernel
private theorem component_okChk_8 : okChk 8 = true := by decide +kernel
private theorem component_okStp_8 : okStp 8 = true := by decide +kernel
private theorem component_okLc_8 : okLc 8 = true := by decide +kernel
private theorem component_okTail_8 : okTail 8 = true := by decide +kernel
theorem okCoord_8 : okCoord 8 = true := by
  simp only [okCoord, component_okF_8, component_okC_8, component_okQ_8, component_okS_8, component_okChk_8, component_okStp_8, component_okLc_8, component_okTail_8, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_8 : SigGolfCandidate.T3M.Verify.optBeq (runZ 8) (expZ 8) = true := by decide +kernel
private theorem component_okC_8 : okC 8 = true := by decide +kernel
private theorem component_okQ_8 : okQ 8 = true := by decide +kernel
private theorem component_okS_8 : okS 8 = true := by decide +kernel
private theorem component_okChk_8 : okChk 8 = true := by decide +kernel
private theorem component_okStp_8 : okStp 8 = true := by decide +kernel
private theorem component_okLc_8 : okLc 8 = true := by decide +kernel
theorem okCoord_8 : okCoord 8 = true := by
  simp only [okCoord, component_z_8, component_okC_8, component_okQ_8, component_okS_8, component_okChk_8, component_okStp_8, component_okLc_8, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
