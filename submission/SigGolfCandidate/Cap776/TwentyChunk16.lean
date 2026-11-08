import SigGolfCandidate.Cap776.TwentyChunk15
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_16 : Nat := twenty_chunk% 0 16
theorem count20_16 : rowFast cache64 20 16=Count20_16 := by decide +kernel
noncomputable def First20_16 : Nat := twenty_chunk% 1 16
theorem first20_16 : pairChunkWith cache 20 16 1=First20_16 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
