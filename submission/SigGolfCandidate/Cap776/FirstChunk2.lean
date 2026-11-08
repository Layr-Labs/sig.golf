import SigGolfCandidate.Cap776.FirstChunk1
set_option debug.skipKernelTC true
namespace SigGolfResearch.ProbabilityCache
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def First19_2 : Nat := first19% 2
theorem first19_2 : pairChunkWith cache 19 2 1=First19_2 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.ProbabilityCache
