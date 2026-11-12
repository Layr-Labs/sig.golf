import SigGolfCandidate.OuterBankAllowed
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterBankNotDigest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Security SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots
open SourceQueries
open ClaudeWCT.W9.T3.Security.Wots
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open ClaudeWCT.Bank.Paired
open OuterBankAllowed

theorem hashN (coord index heap n : Nat) (left right : Digest) :
    AllQueriesSatisfy (OuterGroundCore.hashN coord index heap n left right) BPB.NotDigestQ := by
  rw [OuterVerifierHash.hashN_eq]
  split
  · exact topInput_notDigest ..
  · exact ClaudeWCT.WCT9.allQ_highHash_of_shortHash _ (topInput_notDigest ..)

theorem search (coord index heap : Nat) (left right : Digest) : ∀fuel n,
    AllQueriesSatisfy (OuterGroundCore.search coord index heap left right fuel n) BPB.NotDigestQ := by
  intro fuel
  induction fuel with
  | zero=>intro n;unfold OuterGroundCore.search;exact bind_allowed _ (hashN ..) fun _=>pure_allowed _ _
  | succ fuel ih=>
    intro n
    unfold OuterGroundCore.search
    apply bind_allowed _ (hashN ..)
    intro v
    split
    · exact pure_allowed _ _
    · exact ih (n+1)

theorem node (first : Bool) (coord index heap : Nat) (pads : Nat→PairRoot) (left right : Digest) :
    AllQueriesSatisfy (OuterCanonicalNode.node first coord index heap pads left right) BPB.NotDigestQ := by
  unfold OuterCanonicalNode.node
  split
  · exact map_allowed _ _ (search coord index heap left right _ _)
  · exact ClaudeWCT.Bank.Paired.forest_notDigest.node first coord index heap pads left right

theorem forest_notDigest : OuterBankAllowed.ForestAllowed BPB.NotDigestQ where
  coefs := ClaudeWCT.Bank.Paired.forest_notDigest.coefs
  child := ClaudeWCT.Bank.Paired.forest_notDigest.child
  node := node
#print axioms forest_notDigest
end OuterBankNotDigest
