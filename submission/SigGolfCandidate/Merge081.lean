import SigGolfCandidate.Merge080

-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckAPart2 ====
section

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
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckAPart3 ====
section

set_option Elab.async false

namespace ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
theorem okGlobal_ok : okGlobal = true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem okHorn_ok : okHorn = true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedReuse
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckA ====
section

namespace ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Sign
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckBPart0 ====
section

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
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckBPart1 ====
section

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
end
