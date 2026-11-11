import SigGolfCandidate.Merge033
import SigGolfCandidate.LocalRouteNumerics
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace SigGolfCandidate.Research.SharedForest.LocalRoute
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open ClaudeWCT.Numerics
theorem own1_index (index : Nat) : ownSave index 1=LocalRouteUniform.oneSave (index/4096) := by
  change (46/2^(((index/4096)%128)%8))%2=(46/2^((index/4096)%8))%2
  have hm : ((index/4096)%128)%8=(index/4096)%8 := by omega
  rw [hm]

theorem own2_index (index : Nat) : ownSave index 2=LocalRouteUniform.pairSave (index/64) := by
  have hm : ((index/64)%64)%4=(index/64)%4 := by omega
  simp [ownSave,CanonicalPolicy.lowerPathSave,route,height,LocalRouteUniform.pairSave,hm]

theorem own3_index (index : Nat) : ownSave index 3=LocalRouteUniform.pairSave index := by
  have hm : (index%64)%4=index%4 := by omega
  simp [ownSave,CanonicalPolicy.lowerPathSave,route,height,LocalRouteUniform.pairSave,hm]

theorem root_index (index : Nat) :
    CanonicalPolicy.topPathSave (route index 0).1 =
      LocalRouteUniform.pairSave (index/524288)+LocalRouteUniform.pairSave (index/33554432) := by
  have h1 : ((index/524288)%4096)%4=(index/524288)%4 := by omega
  have h2 : (((index/524288)%4096)/64)%4=(index/33554432)%4 := by omega
  change CanonicalPolicy.topPathSave ((index/524288)%4096)=_
  simp only [CanonicalPolicy.topPathSave,CanonicalPolicy.topPairSave,LocalRouteUniform.pairSave,h1,h2]

theorem index_initial_matches (index : Nat) :
    ClaudeWCT.Numerics.LocalRoute.Tables.indexInitial index =
      ClaudeWCT.Numerics.LocalRoute.Tables.initialAt (pool index)
        (4*ownSave index 1+2*ownSave index 2+ownSave index 3) := by
  unfold ClaudeWCT.Numerics.LocalRoute.Tables.indexInitial LocalRouteUniform.evalIndex
    ClaudeWCT.Numerics.LocalRoute.Tables.initialF pool
  rw [own1_index,own2_index,own3_index,root_index index]
#print axioms index_initial_matches
end SigGolfCandidate.Research.SharedForest.LocalRoute
