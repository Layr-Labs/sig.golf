import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsCheckBPart0

set_option Elab.async false

namespace ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
theorem okCoord_4 : okCoord 4 = true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign
