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
def initialF (rootSave s1 s2 s3 : Nat) : Nat := OuterRootNumerics.initialAt (75-rootSave) (4*s1+2*s2+s3)
def indexInitial (index : Nat) : Nat := LocalRouteUniform.evalIndex initialF index

/-- Root saves 0/1/2/3 carry weights 132/1044/1996/924 (of 4096), layer-1 saves 0/1/2 weights 2/66/60
(of 128); `2097152 = 4096*128*4`. -/
theorem cases_checked : (∑ d : Fin 2,∑ e : Fin 2,
    LocalRouteUniform.topWeighted initialF d.val e.val)≤2097152*meanInitial := by decide +kernel

theorem index_initial_sum : (∑ i : Fin (2^31),indexInitial i.val)≤2^31*meanInitial := by
  unfold indexInitial
  rw [LocalRouteUniform.index_uniform]
  calc
    _ ≤ 2^10*(2097152*meanInitial) := Nat.mul_le_mul_left _ cases_checked
    _ = _ := by ring

/-- C47 (B): the layers are routed by `hyperIndex`, an involution of `[0, 2^31)`, so the sum is unchanged. -/
theorem index_initial_sum_hyper :
    (∑ i : Fin (2^31),indexInitial (SigGolfCandidate.T3.hyperIndex i.val))≤2^31*meanInitial := by
  let e : Equiv.Perm (Fin (2^31)) := Function.Involutive.toPerm
    (fun i => ⟨SigGolfCandidate.T3.hyperIndex i.val, SigGolfCandidate.T3.hyperIndex_lt _⟩)
    (fun i => Fin.ext (SigGolfCandidate.T3.hyperIndex_invol i.isLt))
  calc (∑ i : Fin (2^31),indexInitial (SigGolfCandidate.T3.hyperIndex i.val))
      = ∑ i : Fin (2^31),indexInitial (e i).val := rfl
    _ = ∑ i : Fin (2^31),indexInitial i.val := Equiv.sum_comp e (fun i => indexInitial i.val)
    _ ≤ _ := index_initial_sum

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
#print axioms index_initial_sum_hyper
end OuterIndexMean
