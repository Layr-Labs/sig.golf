import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsRuns
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.JTCheck3

set_option Elab.async false

namespace ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
theorem okCoord_0 : okCoord 0 = true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign
