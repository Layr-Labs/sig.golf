import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsCheckAPart0

set_option Elab.async false

namespace ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
theorem okCoord_1 : okCoord 1 = true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign
