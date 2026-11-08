import SigGolfCandidate.Cap776.TwentyChunk9
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_10 : Nat := twenty_chunk% 0 10
theorem count20_10 : rowFast cache64 20 10=Count20_10 := by decide +kernel
noncomputable def First20_10 : Nat := twenty_chunk% 1 10
theorem first20_10 : pairChunkWith cache 20 10 1=First20_10 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
