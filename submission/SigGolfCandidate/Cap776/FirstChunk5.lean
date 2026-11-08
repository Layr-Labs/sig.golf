import SigGolfCandidate.Cap776.FirstChunk4
set_option debug.skipKernelTC true
namespace SigGolfResearch.ProbabilityCache
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def First19_5 : Nat := first19% 5
theorem first19_5 : pairChunkWith cache 19 5 1=First19_5 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.ProbabilityCache
