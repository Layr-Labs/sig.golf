import SigGolfCandidate.OuterRootNumerics
import SigGolfCandidate.OuterSigning
import SigGolfCandidate.LocalRouteIndex
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
open scoped BigOperators
namespace OuterIndexMean
open Finset ClaudeWCT.Numerics

def meanInitial : Nat := OuterGroundNumerics.mean74
def initialF (rootSave s1 s2 s3 : Nat) : Nat := OuterRootNumerics.initialAt (74-rootSave) (4*s1+2*s2+s3)
def indexInitial (index : Nat) : Nat := LocalRouteUniform.evalIndex initialF index

theorem cases_checked : (∑ a : Fin 2,∑ b : Fin 2,∑ c : Fin 2,∑ d : Fin 2,∑ e : Fin 2,
    initialF (a.val+b.val) c.val d.val e.val)≤32*meanInitial := by decide +kernel

theorem index_initial_sum : (∑ i : Fin (2^31),indexInitial i.val)≤2^31*meanInitial := by
  unfold indexInitial
  rw [LocalRouteUniform.index_uniform]
  calc
    _ ≤ 2^26*(32*meanInitial) := Nat.mul_le_mul_left _ cases_checked
    _ = _ := by ring

theorem index_initial_matches (index : Nat) : indexInitial index=
    OuterRootNumerics.initialAt (OuterSigning.requiredCredit index)
      (4*SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1+
        2*SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2+
          SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 3) := by
  unfold indexInitial LocalRouteUniform.evalIndex initialF OuterSigning.requiredCredit OuterSigning.rootPool
  rw [SigGolfCandidate.Research.SharedForest.LocalRoute.own1_index,
    SigGolfCandidate.Research.SharedForest.LocalRoute.own2_index,
    SigGolfCandidate.Research.SharedForest.LocalRoute.own3_index,
    SigGolfCandidate.Research.SharedForest.LocalRoute.root_index index]
#print axioms index_initial_sum
#print axioms index_initial_matches
end OuterIndexMean
