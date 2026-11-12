import SigGolfCandidate.OuterSecurityFrozen2
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualMessageDeps
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase OuterResidualValues
open OuterResidualGroundChildren (keygenDisclosed topTrialsDisclosed)
open OuterResidualPadModel (coordTrialDeps msgDeps)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual (msgSlots trialDeps trialCoord wTrialDeps wTrialCoord trialsDisclosed keygenCacheDisclosed encodingDisclosed)
attribute [local instance] Classical.propDecidable

theorem trialDeps_keygen {n : TreeNode} {c : Coord} (hc : c∈trialDeps n) : c∈keygenDisclosed := by
  unfold trialDeps at hc
  split_ifs at hc with h1
  · simp at hc
  · obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hc
    have hj' := List.mem_range.mp hj
    change trialCoord n j∈(keygenCacheDisclosed++encodingDisclosed)++topTrialsDisclosed
    apply List.mem_append_right
    apply List.mem_append_left
    unfold trialsDisclosed
    refine List.mem_map.mpr ⟨withNonce n j,?_,rfl⟩
    simp only [Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨h1,?_⟩
    rw [withNonce_nonce n (by have :=trialCap_le n.1.lay n.1.level.val;omega)]
    exact hj'

theorem wTrialDeps_keygen {n : WctNodePos} {c : Coord} (hc : c∈wTrialDeps n) : c∈keygenDisclosed := by
  by_cases h1 : Paired.wTrialCap n.1.coord.val n.1.level.val=1
  · unfold wTrialDeps at hc
    rw [if_pos h1] at hc
    cases hc
  · exact OuterResidualGroundChildren.wGround_mem_keygen h1 (List.mem_append_left _ hc)

theorem coordTrialDeps_keygen (x : Coord) {c : Coord} (hc : c∈coordTrialDeps x) : c∈keygenDisclosed := by
  cases x with
  | inr s=>cases hc
  | inl N=>
    cases N with
    | node n=>exact trialDeps_keygen hc
    | wctNode n=>exact wTrialDeps_keygen hc
    | _=>cases hc

theorem msgSlot_mem_keygen {L : EncLeaf} {cs : Coord×Nat} (hc : cs∈msgSlots L) : cs.1∈keygenDisclosed := by
  exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.msgSlot_mem_keygen hc

theorem msgDeps_keygen (L : EncLeaf) {c : Coord} (hc : c∈msgDeps L) : c∈keygenDisclosed := by
  rcases List.mem_append.mp hc with hc|hc
  · obtain ⟨cs,hcs,rfl⟩:=List.mem_map.mp hc
    exact msgSlot_mem_keygen hcs
  · obtain ⟨cs,hcs,hc⟩:=List.mem_flatMap.mp hc
    exact coordTrialDeps_keygen cs.1 hc
#print axioms msgDeps_keygen
end OuterResidualMessageDeps
