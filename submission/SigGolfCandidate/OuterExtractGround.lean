import SigGolfCandidate.OuterCanonicalNodeGround
import SigGolfCandidate.OuterCanonGraphTrials
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterExtractGround
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.Extract.Paired

def ftsNonceLevel (coord level : Nat) : Prop :=
  ClaudeWCT.W9.T3M.Extract.Paired.ftsNonceLevel coord level ∨ (level=5 ∧ first coord=false)
instance (coord level : Nat) : Decidable (ftsNonceLevel coord level) := inferInstanceAs (Decidable (_ ∨ _))

def nodeAt (coord index heap : Nat) (left right : Digest) : M (Nat×Digest) :=
  if heap<4 then OuterGroundCore.nodeAt coord index heap left right
  else ClaudeWCT.WCT9.ftsNodeAt coord index heap left right

theorem sharedNode_eq_nodeProgramP (index coord level nd : Nat) (hc : coord<9) (hl : level<6)
    (hn : nd<2^(6-level)) (hu : first coord=true→level<5) (ps : Nat→PairRoot)
    (left right : Digest) (h3 : ¬ftsNonceLevel coord level) :
    OuterCanonicalNode.node (first coord) coord index (2^(6-level)+nd) ps left right =
      nodeProgram coord level nd (ClaudeWCT.WCT9.wctTopInput coord index (2^(6-level)+nd) left
        (if level=4 then (ps ((2^(6-level)+nd)/2-2)).2 else 0) right) := by
  have h5 : level≠5:=by
    intro h
    by_cases hf : first coord=true
    · have hh:=hu hf;omega
    · exact h3 (Or.inr ⟨h,Bool.eq_false_iff.mpr hf⟩)
  have hg : ¬ClaudeWCT.W9.T3M.Extract.Paired.ftsNonceLevel coord level :=fun h=>h3 (Or.inl h)
  have h4 : 4≤2^(6-level)+nd := by
    have hle : level≤4:=by omega
    have hp : 2^2≤2^(6-level):=Nat.pow_le_pow_right (by decide) (by omega)
    omega
  unfold OuterCanonicalNode.node
  rw [if_neg (by omega)]
  exact ClaudeWCT.W9.T3M.Extract.Paired.sharedNode_eq_nodeProgramP index coord level nd hc hl hn hu ps left right hg
#print axioms sharedNode_eq_nodeProgramP
end OuterExtractGround
