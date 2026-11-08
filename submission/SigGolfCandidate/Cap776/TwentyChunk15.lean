import SigGolfCandidate.Cap776.TwentyChunk14
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_15 : Nat := twenty_chunk% 0 15
theorem count20_15 : rowFast cache64 20 15=Count20_15 := by decide +kernel
noncomputable def First20_15 : Nat := twenty_chunk% 1 15
theorem first20_15 : pairChunkWith cache 20 15 1=First20_15 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
