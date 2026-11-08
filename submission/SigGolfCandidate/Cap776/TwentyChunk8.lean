import SigGolfCandidate.Cap776.TwentyChunk7
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_8 : Nat := twenty_chunk% 0 8
theorem count20_8 : rowFast cache64 20 8=Count20_8 := by decide +kernel
noncomputable def First20_8 : Nat := twenty_chunk% 1 8
theorem first20_8 : pairChunkWith cache 20 8 1=First20_8 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
