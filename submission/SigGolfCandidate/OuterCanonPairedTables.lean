import SigGolfCandidate.OuterCanonWorld
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
attribute [local instance] OuterCanonBase.instFintypeCoordinate_canonGraph
  OuterCanonBase.instSampleableTypeFullTable_canonGraph
  OuterCanonBase.instSampleableTypeHashOutput_canonGraph_1
  OuterCanonBase.instSampleableTypeLabels_1 OuterCanonBase.instSampleableTypeSecrets
  OuterCanonBase.instSampleableTypeOtherHalves OuterCanonBase.instFintypeSecrets_canonGraph
  OuterCanonBase.instFintypeOtherHalves_canonGraph OuterCanonBase.instSampleableTypeProdSecretsOtherHalves
  OuterCanonBase.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1
theorem tables_bind {Result : Type} (U : Finset HashInput) (hU : canonInputs ⊆ U)
    (next : FullGame.FullTable → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
      let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
      next privateTable publicTable] =
      𝒮[do
        let secrets ← ($ᵗ Secrets : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (privateEquiv.symm (secrets, other)) (programmed U hU secrets labels residual)] := by
  rw [private_bind (fun privateTable => do
    let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
    next privateTable publicTable)]
  apply evalSPMF_bind_congr_left
  intro secrets
  apply evalSPMF_bind_congr_left
  intro other
  exact uniform_bind_programmed U hU secrets (fun table => next (privateEquiv.symm (secrets, other)) table)

#print axioms tables_bind
end OuterCanonBase.Paired
