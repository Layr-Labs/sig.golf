import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsRuns

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
