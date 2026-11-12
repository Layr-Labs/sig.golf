import SigGolfCandidate.OuterCanonicalHeapFold
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterBankAllowed
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.Security
structure ForestAllowed (Q : SigGolfCandidate.T3.Spec.Domain → Prop) : Prop where
  coefs : ∀ index coord, AllQueriesSatisfy (ftsCoefs index coord) Q
  child : ∀ heap index coord selected word coefs pad,
    AllQueriesSatisfy (ClaudeWCT.WCT9.buildChildH heap index coord selected word coefs pad) Q
  node : ∀ first coord index heap pads left right,
    AllQueriesSatisfy (OuterCanonicalNode.node first coord index heap pads left right) Q

section
variable (Q : SigGolfCandidate.T3.Spec.Domain → Prop) (hQ : ForestAllowed Q)
include hQ

theorem sharedHeap_allowed (first : Bool) (index coord : Nat) (pads : Nat → PairRoot)
    (leaves : List Digest) : AllQueriesSatisfy (OuterCanonicalModel.heap first index coord pads leaves) Q := by
  rw [OuterCanonicalModel.heap_fold]
  exact SourceQueries.foldlM_allowed Q _ _ (fun _ _ =>
    SourceQueries.bind_allowed Q (hQ.node ..) fun _ => SourceQueries.pure_allowed Q _) _

theorem sharedCoordinate_allowed (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    AllQueriesSatisfy (OuterCanonicalModel.coordinate first index coord selected word pads) Q := by
  unfold OuterCanonicalModel.coordinate
  exact SourceQueries.bind_allowed Q (hQ.coefs ..) fun _ =>
    SourceQueries.bind_allowed Q (SourceQueries.foldlM_allowed Q _ _
      (fun _ _ => SourceQueries.bind_allowed Q (hQ.child ..) fun _ => SourceQueries.pure_allowed Q _) _) fun _ =>
      SourceQueries.bind_allowed Q (sharedHeap_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem pair_allowed (index pair : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (prev : PairRoot) : AllQueriesSatisfy (OuterForestMoment.pair index pair s aWord bWord prev) Q := by
  unfold OuterForestMoment.pair
  simp only [←OuterCanonicalModel.coordinate_eq]
  exact SourceQueries.bind_allowed Q (sharedCoordinate_allowed Q hQ ..) fun _ =>
    SourceQueries.bind_allowed Q (sharedCoordinate_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem singleton_allowed (index : Nat) (selected : Child) (word : Rank) (prev : PairRoot) :
    AllQueriesSatisfy (OuterForestMoment.singleton index selected word prev) Q := by
  unfold OuterForestMoment.singleton
  simp only [←OuterCanonicalModel.coordinate_eq]
  exact SourceQueries.bind_allowed Q (sharedCoordinate_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem forest_allowed (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    AllQueriesSatisfy (OuterForestMoment.forest index selected words) Q := by
  unfold OuterForestMoment.forest
  exact SourceQueries.bind_allowed Q (SourceQueries.foldlM_allowed Q _ _
    (fun _ _ => SourceQueries.bind_allowed Q (pair_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _) _) fun _ =>
    SourceQueries.bind_allowed Q (singleton_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _
end

theorem hash_public (Q : SigGolfCandidate.T3.Spec.Domain→Prop) (hp : ∀ input,Q (.inl (.inr input)))
    (coord index heap n : Nat) (left right : Digest) :
    AllQueriesSatisfy (OuterGroundCore.hashN coord index heap n left right) Q := by
  unfold OuterGroundCore.hashN
  exact SourceQueries.bind_allowed Q ((allQueriesSatisfy_query_iff _ _).mpr (hp _)) fun _=>SourceQueries.pure_allowed _ _
theorem search_public (Q : SigGolfCandidate.T3.Spec.Domain→Prop) (hp : ∀ input,Q (.inl (.inr input)))
    (coord index heap : Nat) (left right : Digest) : ∀fuel n,
    AllQueriesSatisfy (OuterGroundCore.search coord index heap left right fuel n) Q := by
  intro fuel
  induction fuel with
  | zero=>intro n;unfold OuterGroundCore.search;exact SourceQueries.bind_allowed Q (hash_public Q hp ..) fun _=>SourceQueries.pure_allowed _ _
  | succ fuel ih=>
    intro n
    unfold OuterGroundCore.search
    apply SourceQueries.bind_allowed Q (hash_public Q hp ..)
    intro v
    split
    · exact SourceQueries.pure_allowed _ _
    · exact ih (n+1)
theorem node_public (Q : SigGolfCandidate.T3.Spec.Domain→Prop) (hp : ∀ input,Q (.inl (.inr input)))
    (first : Bool) (coord index heap : Nat) (pads : Nat→PairRoot) (left right : Digest) :
    AllQueriesSatisfy (OuterCanonicalNode.node first coord index heap pads left right) Q := by
  unfold OuterCanonicalNode.node
  split
  · exact SourceQueries.map_allowed Q _ (search_public Q hp coord index heap left right _ _)
  · exact ClaudeWCT.W9.T3.Security.Signer.sharedNode_allowed Q hp ..
theorem forest_public (Q : SigGolfCandidate.T3.Spec.Domain→Prop) (hpublic : ∀ input,Q (.inl (.inr input)))
    (hpair : ∀ tweak,Q (.inr (.inl tweak))) : ForestAllowed Q where
  coefs := fun _ _=>ClaudeWCT.W9.T3.Security.Signer.ftsCoefs_allowed Q (fun _ _ _ _=>hpair _) _ _
  child := ClaudeWCT.W9.T3.Security.Signer.buildChildH_allowed Q hpublic
  node := node_public Q hpublic
#print axioms forest_allowed
#print axioms forest_public
end OuterBankAllowed
