import SigGolfCandidate.Cap776.TwentyChunk2
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_3 : Nat := twenty_chunk% 0 3
theorem count20_3 : rowFast cache64 20 3=Count20_3 := by decide +kernel
noncomputable def First20_3 : Nat := twenty_chunk% 1 3
theorem first20_3 : pairChunkWith cache 20 3 1=First20_3 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
