import SigGolfCandidate.OuterResidualDependencyLaws
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualLeafMessage
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open OuterResidualValues
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual (WCoord)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (AuxData)
open OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (Coherent)
attribute [local instance] Classical.propDecidable

theorem Coherent.leafMsg {U : Finset HashInput} {T : Answers} {vals : Coord → Digest}
    {nv : Message×Fin 2 → Digest} {τ : Cell U → HashOutput} {a : AuxData}
    (h : Coherent U T vals nv τ a) (L : EncLeaf) :
    OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages T L.toWots=msgVals vals L := by
  rw [OuterLifted.ClaudeWCT.W9.T3.Security.CanonEncoding.Paired.sourceMessages_eq_filtered h.agrees L]
  exact OuterResidualRouter.msgLabel_router vals a L
#print axioms Coherent.leafMsg
end OuterResidualLeafMessage
