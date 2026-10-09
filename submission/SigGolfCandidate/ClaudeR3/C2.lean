import SigGolfCandidate.ClaudeR3.C1
namespace ClaudeR3.Tab
open ClaudeWCT.Numerics.N600 (g1T g2T)
set_option maxRecDepth 100000
theorem mean_miss : missCheck tabM g1T = true := by decide +kernel
theorem mean_bound : histBound tabM g1T 17 = true := by decide +kernel
theorem mean_chunk : chunkCheck tabM g1T 17 0 1101 0 = true := by decide +kernel
theorem near_miss : missCheck tabN gNearT = true := by decide +kernel
theorem near_bound : histBound tabN gNearT 18 = true := by decide +kernel
theorem near_chunk : chunkCheck tabN gNearT 18 0 1101 0 = true := by decide +kernel
end ClaudeR3.Tab
