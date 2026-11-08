import SigGolfCandidate.Cap776.FirstInput
set_option debug.skipKernelTC true
namespace SigGolfResearch.ProbabilityCache
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def First19_0 : Nat := first19% 0
theorem first19_0 : pairChunkWith cache 19 0 1=First19_0 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.ProbabilityCache
