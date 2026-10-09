import SigGolfCandidate.ClaudeR3.E3
import SigGolfCandidate.ClaudeR3.K8

namespace ClaudeR3.Ev

set_option maxRecDepth 100000
theorem diagF_r15 : diagCheckL 15 = true := by decide +kernel
theorem diagF_r16 : diagCheckL 16 = true := by decide +kernel
theorem diagF_r17 : diagCheckL 17 = true := by decide +kernel

end ClaudeR3.Ev
