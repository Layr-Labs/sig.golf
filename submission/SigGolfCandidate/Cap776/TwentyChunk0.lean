import SigGolfCandidate.Cap776.TwentyInput
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def Count20_0 : Nat := twenty_chunk% 0 0
theorem count20_0 : rowFast cache64 20 0=Count20_0 := by decide +kernel
noncomputable def First20_0 : Nat := twenty_chunk% 1 0
theorem first20_0 : pairChunkWith cache 20 0 1=First20_0 := by
  rw [pairChunkWith_eq_fast]
  decide +kernel
end SigGolfResearch.Twenty
