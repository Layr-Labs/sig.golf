import SigGolfCandidate.Cap776.TwentyChunk17
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_18 : Nat := twenty_chunk% 0 18
theorem count20_18 : rowFast cache64 20 18=Count20_18 := by decide +kernel
noncomputable def First20_18 : Nat := twenty_chunk% 1 18
theorem first20_18 : pairChunkWith cache 20 18 1=First20_18 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
