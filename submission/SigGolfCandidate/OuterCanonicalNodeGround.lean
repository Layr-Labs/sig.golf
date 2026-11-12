import SigGolfCandidate.OuterCanonGraphBase
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterCanonicalNodeGround
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest

theorem groundG (f : Bool) (coord index heap : Nat) (ps : Nat→PairRoot)
    (hg : ftsGround coord heap) (left right : Digest) :
    OuterCanonicalNode.node f coord index heap ps left right=ftsNodeG coord index heap left right := by
  have h8:=ftsGround_ge8 hg
  unfold OuterCanonicalNode.node
  rw [if_neg (by omega)]
  exact ClaudeWCT.W9.T3M.Extract.Paired.sharedNode_groundG f coord index heap ps hg left right

theorem ground (f : Bool) (coord index heap : Nat) (ps : Nat→PairRoot)
    (h8 : 8≤heap) (h16 : heap<16) (left right : Digest) :
    OuterCanonicalNode.node f coord index heap ps left right=ftsNodeG coord index heap left right := by
  unfold OuterCanonicalNode.node
  rw [if_neg (by omega)]
  exact ClaudeWCT.W9.T3M.Extract.Paired.sharedNode_ground f coord index heap ps h8 h16 left right
#print axioms groundG
end OuterCanonicalNodeGround
