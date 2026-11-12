import SigGolfCandidate.OuterCanonicalNode
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonicalNodeQueries
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Security SigGolfCandidate.Research.SharedForest
open SourceQueries
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Security.Wots.Enc (NonEnc)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open ClaudeWCT.W9.T3.Security.WPair

theorem free (first : Bool) (coord index heap : Nat) (pads : Nat→PairRoot) (left right : Digest) :
    AllQueriesSatisfy (OuterCanonicalNode.node first coord index heap pads left right) WFree := by
  unfold OuterCanonicalNode.node
  split
  · exact map_allowed WFree _ (OuterWorldFree.node_free _ _ _ _ _)
  · exact Paired.sharedNode_free _ _ _ _ _ _ _

theorem short (first : Bool) (coord index heap : Nat) (pads : Nat→PairRoot) (left right : Digest) :
    ShortRespects (OuterCanonicalNode.node first coord index heap pads left right) := by
  unfold OuterCanonicalNode.node
  split
  · exact ShortRespects.map _ (OuterCanonicalShort.node_short _ _ _ _ _)
  · exact sharedNode_short _ _ _ _ _ _ _

theorem nonEnc (first : Bool) (coord index heap : Nat) (hc : coord<9) (pads : Nat→PairRoot) (left right : Digest) :
    AllQueriesSatisfy (OuterCanonicalNode.node first coord index heap pads left right) NonEnc := by
  unfold OuterCanonicalNode.node
  split
  · exact map_allowed NonEnc _ (OuterCanonicalNonEnc.node_nonEnc _ _ _ hc _ _)
  · exact sharedNode_nonEnc _ _ _ _ hc _ _ _

#print axioms free
#print axioms short
#print axioms nonEnc
end OuterCanonicalNodeQueries
