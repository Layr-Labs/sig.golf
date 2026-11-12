import SigGolfCandidate.OuterResidualValues
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualProjection
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired
attribute [local instance] Classical.propDecidable

theorem wTrialFailsV_coordVal (s : Secrets) (labels : Labels) (n : WctNodePos) (j : Nat) :
    OuterResidualValues.wTrialFailsV (coordVal s labels) n j ↔ Paired.wTrialFails labels n j := by
  rfl

theorem wSelNonceV_coordVal (s : Secrets) (labels : Labels) (n : WctNodePos) :
    OuterResidualValues.wSelNonceV (coordVal s labels) n=Paired.wSelNonce labels n := by
  unfold OuterResidualValues.wSelNonceV Paired.wSelNonce
  congr 1

theorem wActiveV_coordVal (s : Secrets) (labels : Labels) (n : WctNodePos) :
    OuterResidualValues.WActiveV (coordVal s labels) n ↔ Paired.WActive labels n := by
  unfold OuterResidualValues.WActiveV Paired.WActive
  simp only [wTrialFailsV_coordVal]

theorem paired_ftsLabel_top (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) :
    Paired.ftsLabel labels index coord 6 b.val=
      ClaudeWCT.W9.T3M.Extract.Paired.proj (Node.wctNode (ftsTopNode index coord b)).toPos
        (labels (.wctNode (Paired.wSelNode labels (ftsTopNode index coord b)))) := by
  unfold Paired.ftsLabel
  rw [if_neg (by omega)]
  unfold ftsNodeAt
  rw [dif_pos (show 6-1<6 ∧ b.val<2^(7-(6-1)-1) by have :=b.isLt;omega)]
  rfl
#print axioms wSelNonceV_coordVal
#print axioms paired_ftsLabel_top
end OuterResidualProjection
