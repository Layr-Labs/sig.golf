import SigGolfCandidate.LocalRouteIndex
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace SigGolfCandidate.Research.SharedForest.LocalRoute
open SigGolfCandidate.T3 ClaudeWCT.WCT9 ClaudeWCT.Numerics
theorem ownSave_layer (index : Nat) (lay : SigGolfCandidate.T3.Layer) :
    ownSave index lay.val=CanonicalPolicy.lowerPathSave lay.val (route index lay).1 := by
  fin_cases lay <;> rfl
theorem ownSave_one_div (index : Nat) : ownSave index 1=CanonicalPolicy.lowerPathSave 1 (index/4096) := by
  rw [own1_index]; rfl
theorem ownSave_two_div (index : Nat) : ownSave index 2=CanonicalPolicy.lowerPathSave 2 (index/64) := by
  rw [own2_index]; simp [CanonicalPolicy.lowerPathSave,LocalRouteUniform.pairSave]
theorem ownSave_three_div (index : Nat) : ownSave index 3=CanonicalPolicy.lowerPathSave 3 index := by
  rw [own3_index]; simp [CanonicalPolicy.lowerPathSave,LocalRouteUniform.pairSave]
end SigGolfCandidate.Research.SharedForest.LocalRoute
