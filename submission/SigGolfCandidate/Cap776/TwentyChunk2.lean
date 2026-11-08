import SigGolfCandidate.Cap776.TwentyChunk1
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_2 : Nat := twenty_chunk% 0 2
theorem count20_2 : rowFast cache64 20 2=Count20_2 := by decide +kernel
noncomputable def First20_2 : Nat := twenty_chunk% 1 2
theorem first20_2 : pairChunkWith cache 20 2 1=First20_2 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
