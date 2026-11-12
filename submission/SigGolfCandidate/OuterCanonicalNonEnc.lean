import SigGolfCandidate.OuterCanonicalHonest
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonicalNonEnc
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Security SigGolfCandidate.Research.SharedForest
open SourceQueries
open SigGolfCandidate.T3.Security.Wots.Enc (NonEnc)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
theorem hashN_nonEnc (coord index heap n : Nat) (hc : coord<9) (left right : Digest) :
    AllQueriesSatisfy (OuterGroundCore.hashN coord index heap n left right) NonEnc := by
  rw [OuterVerifierHash.hashN_eq]
  split
  · exact topLow_nonEnc _ _ _ hc _ _ _
  · exact topHigh_nonEnc _ _ _ hc _ _ _

theorem search_nonEnc (coord index heap : Nat) (hc : coord<9) (left right : Digest) : ∀fuel n,
    AllQueriesSatisfy (OuterGroundCore.search coord index heap left right fuel n) NonEnc := by
  intro fuel
  induction fuel with
  | zero=>intro n;unfold OuterGroundCore.search;exact bind_allowed NonEnc (hashN_nonEnc _ _ _ _ hc _ _) fun _=>pure_allowed _ _
  | succ fuel ih=>
    intro n
    unfold OuterGroundCore.search
    apply bind_allowed NonEnc (hashN_nonEnc _ _ _ _ hc _ _)
    intro value
    split
    · exact pure_allowed _ _
    · exact ih _

theorem node_nonEnc (coord index heap : Nat) (hc : coord<9) (left right : Digest) :
    AllQueriesSatisfy (OuterGroundCore.nodeAt coord index heap left right) NonEnc :=search_nonEnc _ _ _ hc _ _ _ _

theorem inner_nonEnc (first : Bool) (index coord : Nat) (hc : coord<9) (pads : Nat→PairRoot) (leaves : List Digest) :
    AllQueriesSatisfy (OuterInnerMoment.innerHeap first index coord pads leaves) NonEnc := by
  unfold OuterInnerMoment.innerHeap
  apply foldlM_allowed NonEnc
  intro nodes heap
  unfold ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.heapStep
  exact bind_allowed NonEnc (sharedNode_nonEnc _ _ _ _ hc _ _ _) fun _=>pure_allowed _ _

theorem finish_nonEnc (coord index : Nat) (hc : coord<9) (nodes : Array Digest) :
    AllQueriesSatisfy (OuterHeapMoment.finish coord index nodes) NonEnc := by
  unfold OuterHeapMoment.finish
  exact bind_allowed NonEnc (node_nonEnc _ _ _ hc _ _) fun _=>bind_allowed NonEnc (node_nonEnc _ _ _ hc _ _) fun _=>pure_allowed _ _

theorem heap_nonEnc (index coord : Nat) (hc : coord<9) (pads : Nat→PairRoot) (leaves : List Digest) :
    AllQueriesSatisfy (OuterHeapMoment.heap coord index pads leaves) NonEnc :=
  bind_allowed NonEnc (inner_nonEnc _ _ _ hc _ _) fun _=>finish_nonEnc _ _ hc _


theorem hybrid_nonEnc (first : Bool) (index coord : Nat) (hc : coord<9) (pads : Nat→PairRoot) (leaves : List Digest) :
    AllQueriesSatisfy (OuterCanonicalModel.heap first index coord pads leaves) NonEnc := by
  cases first
  · exact heap_nonEnc _ _ hc _ _
  · exact sharedHeap_nonEnc _ _ _ hc _ _
#print axioms hybrid_nonEnc
end OuterCanonicalNonEnc
