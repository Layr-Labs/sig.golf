import SigGolfCandidate.OuterSecurityFrozen1
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterHintBridge
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9

theorem hintFloor_eq (index : Nat) (hints : BitVec 16) (lay : Layer) :
    hintFloor index hints lay=OuterLifted.SigGolfCandidate.Research.SharedForest.hintFloor index hints lay := by
  unfold hintFloor OuterLifted.SigGolfCandidate.Research.SharedForest.hintFloor
  by_cases h : lay=0
  · subst lay
    rw [if_pos rfl,if_pos rfl,OuterSigning.root_floor,Policy75Safe23.threshold_top]
    have hb:=requiredCredit_bounds index
    omega
  · rw [if_neg h,if_neg h]

theorem valid_eq (index : Nat) (hints : BitVec 16) (ds : List (List Nat)) (ls : List Bool) :
    OuterSigning.policyHintsValid index hints ds ls=
      OuterLifted.SigGolfCandidate.Research.SharedForest.policyHintsValid index hints ds ls := by
  rfl
#print axioms hintFloor_eq
#print axioms valid_eq
end OuterHintBridge
