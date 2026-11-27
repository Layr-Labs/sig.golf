import SigGolfCandidate.OuterSigning
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterHintFloor
open SigGolfCandidate.T3 ClaudeWCT.WCT9 SigGolfCandidate.Research

theorem eq (index : Nat) (hints : BitVec 16) (lay : Layer) :
    OuterSigning.hintFloor index hints lay=SharedForest.hintFloor index hints lay := by
  by_cases h : lay=0
  · subst lay
    simp only [OuterSigning.hintFloor,SharedForest.hintFloor,if_true]
    rfl
  · simp only [OuterSigning.hintFloor,SharedForest.hintFloor,if_neg h]

#print axioms eq
end OuterHintFloor
