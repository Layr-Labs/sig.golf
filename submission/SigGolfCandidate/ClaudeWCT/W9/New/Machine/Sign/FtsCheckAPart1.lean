import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsRuns

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_1 : okF 1 = true := by decide +kernel
private theorem component_okC_1 : okC 1 = true := by decide +kernel
private theorem component_okQ_1 : okQ 1 = true := by decide +kernel
private theorem component_okS_1 : okS 1 = true := by decide +kernel
private theorem component_okChk_1 : okChk 1 = true := by decide +kernel
private theorem component_okStp_1 : okStp 1 = true := by decide +kernel
private theorem component_okLc_1 : okLc 1 = true := by decide +kernel
private theorem component_okTail_1 : okTail 1 = true := by decide +kernel
theorem okCoord_1 : okCoord 1 = true := by
  simp only [okCoord, component_okF_1, component_okC_1, component_okQ_1, component_okS_1, component_okChk_1, component_okStp_1, component_okLc_1, component_okTail_1, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_1 : SigGolfCandidate.T3M.Verify.optBeq (runZ 1) (expZ 1) = true := by decide +kernel
private theorem component_okC_1 : okC 1 = true := by decide +kernel
private theorem component_okQ_1 : okQ 1 = true := by decide +kernel
private theorem component_okS_1 : okS 1 = true := by decide +kernel
private theorem component_okChk_1 : okChk 1 = true := by decide +kernel
private theorem component_okStp_1 : okStp 1 = true := by decide +kernel
private theorem component_okLc_1 : okLc 1 = true := by decide +kernel
theorem okCoord_1 : okCoord 1 = true := by
  simp only [okCoord, component_z_1, component_okC_1, component_okQ_1, component_okS_1, component_okChk_1, component_okStp_1, component_okLc_1, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
