import SigGolfCandidate.Cap776.TwentyChunk18
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_19 : Nat := twenty_chunk% 0 19
theorem count20_19 : rowFast cache64 20 19=Count20_19 := by decide +kernel
noncomputable def First20_19 : Nat := twenty_chunk% 1 19
theorem first20_19 : pairChunkWith cache 20 19 1=First20_19 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
