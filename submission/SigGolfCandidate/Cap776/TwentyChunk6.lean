import SigGolfCandidate.Cap776.TwentyChunk5
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_6 : Nat := twenty_chunk% 0 6
theorem count20_6 : rowFast cache64 20 6=Count20_6 := by decide +kernel
noncomputable def First20_6 : Nat := twenty_chunk% 1 6
theorem first20_6 : pairChunkWith cache 20 6 1=First20_6 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
