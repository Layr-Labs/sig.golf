import SigGolfCandidate.Cap776.FirstChunk3
set_option debug.skipKernelTC true
namespace SigGolfResearch.ProbabilityCache
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def First19_4 : Nat := first19% 4
theorem first19_4 : pairChunkWith cache 19 4 1=First19_4 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.ProbabilityCache
