import SigGolfCandidate.Cap776.TwentyChunk13
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_14 : Nat := twenty_chunk% 0 14
theorem count20_14 : rowFast cache64 20 14=Count20_14 := by decide +kernel
noncomputable def First20_14 : Nat := twenty_chunk% 1 14
theorem first20_14 : pairChunkWith cache 20 14 1=First20_14 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
