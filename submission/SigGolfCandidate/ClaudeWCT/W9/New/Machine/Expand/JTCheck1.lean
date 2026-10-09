import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.JTCheck0

set_option Elab.async false

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem jtOK_320 : (List.range' 320 64).all jtOK = true := by decide +kernel
theorem jtOK_384 : (List.range' 384 64).all jtOK = true := by decide +kernel
theorem jtOK_448 : (List.range' 448 64).all jtOK = true := by decide +kernel
theorem jtOK_512 : (List.range' 512 51).all jtOK = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
