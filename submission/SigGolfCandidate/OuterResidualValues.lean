import SigGolfCandidate.OuterForgeryCanonical
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable section
namespace OuterResidualValues
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
abbrev Coord:=OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Coord
abbrev EncLeaf:=OuterLifted.ClaudeWCT.W9.T3.Security.CanonEncoding.EncLeaf
open OuterCanonBase

def wTrialFailsV (v : Coord → Digest) (n : WctNodePos) (j : Nat) : Prop :=
  (if n.1.level.val=5 then OuterGroundCore.zeroOk n.1.coord.val else
    WCT9.ftsZeroOk n.1.coord.val (2^(6-n.1.level.val)))
      (v (OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.wTrialCoord n j))=false
instance instDecidableWTrialFailsV (v : Coord → Digest) (n : WctNodePos) (j : Nat) : Decidable (wTrialFailsV v n j) := by
  unfold wTrialFailsV;infer_instance
def WActiveV (v : Coord → Digest) (n : WctNodePos) : Prop :=
  n.1.nonce.val<Paired.wTrialCap n.1.coord.val n.1.level.val ∧ ∀j<n.1.nonce.val,wTrialFailsV v n j
instance instDecidableWActiveV (v : Coord → Digest) (n : WctNodePos) : Decidable (WActiveV v n) := by
  unfold WActiveV;infer_instance
def wSelNonceV (v : Coord → Digest) (n : WctNodePos) : Nat :=
  ((List.range (Paired.wTrialCap n.1.coord.val n.1.level.val)).find? fun j=> !decide (wTrialFailsV v n j)).getD
    (Paired.wTrialCap n.1.coord.val n.1.level.val-1)
def selCoordV (v : Coord → Digest) : Coord → Coord
  | .inl (.node n)=>.inl (.node (withNonce n (OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.selNonceV v n)))
  | .inl (.wctNode n)=>.inl (.wctNode (Paired.wWithNonce n (wSelNonceV v n)))
  | c=>c
def selVals (v : Coord → Digest) : Coord → Digest := fun c=>v (selCoordV v c)
def msgVals (vals : Coord → Digest) (L : EncLeaf) : WCT9.LayerMsg :=
  if h : L.1.lay.val<3 then
    .pair (selVals vals (.inl (.node (topNode ⟨L.1.lay.val+1,by omega⟩
      (OuterLifted.ClaudeWCT.W9.T3.Security.CanonEncoding.childIndex L)
      (OuterLifted.ClaudeWCT.W9.T3.Security.CanonEncoding.childIndex_treeBits L h) 0))))
      (selVals vals (.inl (.node (topNode ⟨L.1.lay.val+1,by omega⟩
      (OuterLifted.ClaudeWCT.W9.T3.Security.CanonEncoding.childIndex L)
      (OuterLifted.ClaudeWCT.W9.T3.Security.CanonEncoding.childIndex_treeBits L h) 1))))
  else .pair (selVals vals (.inl (.wctNode (ftsTopNode (OuterLifted.ClaudeWCT.W9.T3.Security.CanonEncoding.childIndex L) 8 0))))
    (selVals vals (.inl (.wctNode (ftsTopNode (OuterLifted.ClaudeWCT.W9.T3.Security.CanonEncoding.childIndex L) 8 1))))
end OuterResidualValues
