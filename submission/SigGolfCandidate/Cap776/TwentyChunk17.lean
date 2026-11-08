import SigGolfCandidate.Cap776.TwentyChunk16
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_17 : Nat := twenty_chunk% 0 17
theorem count20_17 : rowFast cache64 20 17=Count20_17 := by decide +kernel
noncomputable def First20_17 : Nat := twenty_chunk% 1 17
theorem first20_17 : pairChunkWith cache 20 17 1=First20_17 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
