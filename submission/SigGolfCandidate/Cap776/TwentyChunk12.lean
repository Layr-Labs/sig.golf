import SigGolfCandidate.Cap776.TwentyChunk11
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_12 : Nat := twenty_chunk% 0 12
theorem count20_12 : rowFast cache64 20 12=Count20_12 := by decide +kernel
noncomputable def First20_12 : Nat := twenty_chunk% 1 12
theorem first20_12 : pairChunkWith cache 20 12 1=First20_12 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
