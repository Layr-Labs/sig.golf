import SigGolfCandidate.OuterResidualChildGeometry
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualReductionHelpers
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase OuterResidualValues OuterResidualPadModel
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual (wTrialCoord mem_wTrialDeps)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (RouterState)
open OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (Known)
attribute [local instance] Classical.propDecidable

theorem wtrial_cellDepsP {n : WctNodePos} (h1 : Paired.wTrialCap n.1.coord.val n.1.level.val≠1) {j : Nat}
    (hj : j<Paired.wTrialCap n.1.coord.val n.1.level.val) : wTrialCoord n j∈cellDepsP (.wctNode n) := by
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_wTrialDeps h1 hj))))

theorem msgDeps_known (st : RouterState) (L : EncLeaf) : ∀c∈msgDeps L,
    OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.RouterState.known st c := by
  intro c hc
  exact Known.base (Or.inl (OuterResidualMessageDeps.msgDeps_keygen L hc))
#print axioms wtrial_cellDepsP
#print axioms msgDeps_known
end OuterResidualReductionHelpers
