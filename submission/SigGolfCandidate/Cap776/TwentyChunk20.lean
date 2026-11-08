import SigGolfCandidate.Cap776.TwentyChunk19
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_20 : Nat := twenty_chunk% 0 20
theorem count20_20 : rowFast cache64 20 20=Count20_20 := by decide +kernel
noncomputable def First20_20 : Nat := twenty_chunk% 1 20
theorem first20_20 : pairChunkWith cache 20 20 1=First20_20 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
