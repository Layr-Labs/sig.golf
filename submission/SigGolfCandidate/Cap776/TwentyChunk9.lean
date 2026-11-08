import SigGolfCandidate.Cap776.TwentyChunk8
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_9 : Nat := twenty_chunk% 0 9
theorem count20_9 : rowFast cache64 20 9=Count20_9 := by decide +kernel
noncomputable def First20_9 : Nat := twenty_chunk% 1 9
theorem first20_9 : pairChunkWith cache 20 9 1=First20_9 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
