import SigGolfCandidate.Cap776.TwentyChunk6
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_7 : Nat := twenty_chunk% 0 7
theorem count20_7 : rowFast cache64 20 7=Count20_7 := by decide +kernel
noncomputable def First20_7 : Nat := twenty_chunk% 1 7
theorem first20_7 : pairChunkWith cache 20 7 1=First20_7 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
