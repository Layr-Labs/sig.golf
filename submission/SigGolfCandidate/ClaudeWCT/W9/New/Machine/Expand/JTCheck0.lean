import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.JTCheckParts

set_option Elab.async false

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem jtOK_0 : (List.range' 0 64).all jtOK = true := by decide +kernel
theorem jtOK_64 : (List.range' 64 64).all jtOK = true := by decide +kernel
theorem jtOK_128 : (List.range' 128 64).all jtOK = true := by decide +kernel
theorem jtOK_192 : (List.range' 192 64).all jtOK = true := by decide +kernel
theorem jtOK_256 : (List.range' 256 64).all jtOK = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
