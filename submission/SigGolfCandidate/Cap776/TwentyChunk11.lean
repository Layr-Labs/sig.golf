import SigGolfCandidate.Cap776.TwentyChunk10
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_11 : Nat := twenty_chunk% 0 11
theorem count20_11 : rowFast cache64 20 11=Count20_11 := by decide +kernel
noncomputable def First20_11 : Nat := twenty_chunk% 1 11
theorem first20_11 : pairChunkWith cache 20 11 1=First20_11 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
