import SigGolfCandidate.ClaudeR3.C1
import SigGolfCandidate.ClaudeR3.C2
namespace ClaudeR3.Tab
open ClaudeWCT.Numerics.N600 (g1T g2T)
set_option maxRecDepth 100000
theorem same_miss : missCheck tabS g2T = true := by decide +kernel
theorem same_bound : histBound tabS g2T 25 = true := by decide +kernel
theorem same_chunk : chunkCheck tabS g2T 25 0 8219 0 = true := by decide +kernel
end ClaudeR3.Tab
