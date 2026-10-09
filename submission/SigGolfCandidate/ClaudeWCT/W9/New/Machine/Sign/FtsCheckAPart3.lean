import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsCheckAPart2

set_option Elab.async false

namespace ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
theorem okGlobal_ok : okGlobal = true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign
