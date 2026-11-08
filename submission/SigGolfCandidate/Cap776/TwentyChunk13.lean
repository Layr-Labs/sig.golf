import SigGolfCandidate.Cap776.TwentyChunk12
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_13 : Nat := twenty_chunk% 0 13
theorem count20_13 : rowFast cache64 20 13=Count20_13 := by decide +kernel
noncomputable def First20_13 : Nat := twenty_chunk% 1 13
theorem first20_13 : pairChunkWith cache 20 13 1=First20_13 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
