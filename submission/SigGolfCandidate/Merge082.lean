import SigGolfCandidate.Merge080
import SigGolfCandidate.Merge081

-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckBPart2 ====
section

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
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckB ====
section

namespace ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Sign
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckCPart0 ====
section

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
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckCPart1 ====
section

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
end
