import SigGolfCandidate.Cap776.FirstChunk16
set_option debug.skipKernelTC true
namespace SigGolfResearch.ProbabilityCache
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def First19_17 : Nat := first19% 17
theorem first19_17 : pairChunkWith cache 19 17 1=First19_17 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.ProbabilityCache
