import SigGolfCandidate.Cap776.TwentyChunk0
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_1 : Nat := twenty_chunk% 0 1
theorem count20_1 : rowFast cache64 20 1=Count20_1 := by decide +kernel
noncomputable def First20_1 : Nat := twenty_chunk% 1 1
theorem first20_1 : pairChunkWith cache 20 1 1=First20_1 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
