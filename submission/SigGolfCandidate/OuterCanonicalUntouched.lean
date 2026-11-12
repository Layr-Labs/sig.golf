import SigGolfCandidate.OuterCanonicalHeapFold
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonicalUntouched
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Security SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots
open SourceQueries
open ClaudeWCT.W9.T3.Security.Wots
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

theorem hashN (a : ChainAddr) (coord index heap n : Nat) (left right : Digest) :
    AllQueriesSatisfy (OuterGroundCore.hashN coord index heap n left right) (UntouchedP a) := by
  unfold OuterGroundCore.hashN
  exact bind_allowed (UntouchedP a) ((allQueriesSatisfy_query_iff _ _).mpr
    (topInput_untouched a coord index heap left (BitVec.ofNat 128 (n%2^64)) right)) fun _=>pure_allowed _ _

theorem search (a : ChainAddr) (coord index heap : Nat) (left right : Digest) : ∀fuel n,
    AllQueriesSatisfy (OuterGroundCore.search coord index heap left right fuel n) (UntouchedP a) := by
  intro fuel
  induction fuel with
  | zero=>intro n;unfold OuterGroundCore.search;exact bind_allowed _ (hashN a ..) fun _=>pure_allowed _ _
  | succ fuel ih=>
    intro n
    unfold OuterGroundCore.search
    apply bind_allowed _ (hashN a ..)
    intro v
    split
    · exact pure_allowed _ _
    · exact ih (n+1)

theorem node (a : ChainAddr) (first : Bool) (coord index heap : Nat) (pads : Nat→PairRoot) (left right : Digest) :
    AllQueriesSatisfy (OuterCanonicalNode.node first coord index heap pads left right) (UntouchedP a) := by
  unfold OuterCanonicalNode.node
  split
  · exact map_allowed _ _ (search a coord index heap left right _ _)
  · exact sharedNode_untouched a first coord index heap pads left right

theorem heap (a : ChainAddr) (first : Bool) (index coord : Nat) (pads : Nat→PairRoot) (leaves : List Digest) :
    AllQueriesSatisfy (OuterCanonicalModel.heap first index coord pads leaves) (UntouchedP a) := by
  rw [OuterCanonicalModel.heap_fold]
  exact foldlM_allowed (UntouchedP a) _ _ (fun nodes h=>
    bind_allowed _ (node a first coord index h pads _ _) fun _=>pure_allowed _ _) _
#print axioms node
#print axioms heap
end OuterCanonicalUntouched
