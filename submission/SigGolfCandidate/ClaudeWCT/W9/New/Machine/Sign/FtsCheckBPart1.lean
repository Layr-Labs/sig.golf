import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsRuns

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_4 : okF 4 = true := by decide +kernel
private theorem component_okC_4 : okC 4 = true := by decide +kernel
private theorem component_okQ_4 : okQ 4 = true := by decide +kernel
private theorem component_okS_4 : okS 4 = true := by decide +kernel
private theorem component_okChk_4 : okChk 4 = true := by decide +kernel
private theorem component_okStp_4 : okStp 4 = true := by decide +kernel
private theorem component_okLc_4 : okLc 4 = true := by decide +kernel
private theorem component_okTail_4 : okTail 4 = true := by decide +kernel
theorem okCoord_4 : okCoord 4 = true := by
  simp only [okCoord, component_okF_4, component_okC_4, component_okQ_4, component_okS_4, component_okChk_4, component_okStp_4, component_okLc_4, component_okTail_4, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_4 : SigGolfCandidate.T3M.Verify.optBeq (runZ 4) (expZ 4) = true := by decide +kernel
private theorem component_okC_4 : okC 4 = true := by decide +kernel
private theorem component_okQ_4 : okQ 4 = true := by decide +kernel
private theorem component_okS_4 : okS 4 = true := by decide +kernel
private theorem component_okChk_4 : okChk 4 = true := by decide +kernel
private theorem component_okStp_4 : okStp 4 = true := by decide +kernel
private theorem component_okLc_4 : okLc 4 = true := by decide +kernel
theorem okCoord_4 : okCoord 4 = true := by
  simp only [okCoord, component_z_4, component_okC_4, component_okQ_4, component_okS_4, component_okChk_4, component_okStp_4, component_okLc_4, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
