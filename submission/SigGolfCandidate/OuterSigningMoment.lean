import SigGolfCandidate.OuterLayerMoment
import SigGolfCandidate.OuterForestPreserves
import SigGolfCandidate.OuterGlobalFresh
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterSigningMoment
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Budgets (V_bind_bounded)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9 ClaudeWCT.W9.T3.CanonicalSearch
open SigGolfCandidate.Research.SharedSigningBudget
open ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh
noncomputable def outerE : ENNReal := mG 3^8*mG 4^2
theorem V_signFromOutput_fixed (secret : BitVec 256) (z L P : ENNReal) {F : ENNReal}
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32)
    (output : HashOutput) (rcache : RCache)
    (hforest : V secret z (OuterForestMoment.forest (digestIndex output)
      (SigGolfCandidate.Research.SharedForest.forestSelectionFromOutput output)
      (SigGolfCandidate.Research.SharedForest.forestWordsFromOutput output)) rcache ≤ F)
    (hprep : ∀ forest ∈ support (roRun secret
        (OuterForestMoment.forest (digestIndex output) (SigGolfCandidate.Research.SharedForest.forestSelectionFromOutput output)
          (SigGolfCandidate.Research.SharedForest.forestWordsFromOutput output)) rcache),
      V secret z (SigGolfCandidate.Research.SharedForest.prepareRoots (digestIndex output)) forest.2 ≤ P)
    (hsearch : ∀ forest ∈ support (roRun secret
        (OuterForestMoment.forest (digestIndex output) (SigGolfCandidate.Research.SharedForest.forestSelectionFromOutput output)
          (SigGolfCandidate.Research.SharedForest.forestWordsFromOutput output)) rcache),
      ∀ prepared ∈ support (roRun secret (SigGolfCandidate.Research.SharedForest.prepareRoots (digestIndex output)) forest.2),
      V secret z (OuterSigning.searchPreparedLayers cache (digestIndex output) prepared.1 forest.1.2)
        prepared.2 ≤ L) :
    V secret z (OuterSigning.signFromOutput cache rho counter output) rcache ≤
      F * (P * L) := by
  unfold OuterSigning.signFromOutput
  refine V_bind_bounded secret z _ _ rcache F (P * L) hforest ?_
  intro forest hforest
  refine V_bind_bounded secret z _ _ forest.2 P L (hprep forest hforest) ?_
  intro prepared hprepared
  refine (V_bind_bounded secret z _ _ prepared.2 L 1
    (hsearch forest hforest prepared hprepared) ?_).trans_eq (mul_one L)
  intro layers _
  cases layers.1 <;> simp only [V_pure, le_refl]


theorem V_signFromOutput_certified (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache) (hg : AllGFresh rcache) (hf : OuterGlobalFresh.AllFFresh rcache) :
    V secret Budgets.signingZ (OuterSigning.signFromOutput cache rho counter output) rcache≤
      Budgets.signingZ^111993*(groundE*(ftsE*(outerE*
        OuterLayerMoment.initialValue (OuterSigning.requiredCredit (digestIndex output))
          (LocalRoute.ownSave (digestIndex output) 1) (LocalRoute.ownSave (digestIndex output) 2)
          (LocalRoute.ownSave (digestIndex output) 3)))) := by
  have h:=V_signFromOutput_fixed secret Budgets.signingZ
    (Budgets.signingZ^168*OuterLayerMoment.initialValue (OuterSigning.requiredCredit (digestIndex output))
      (LocalRoute.ownSave (digestIndex output) 1) (LocalRoute.ownSave (digestIndex output) 2) (LocalRoute.ownSave (digestIndex output) 3))
    (Budgets.signingZ^80704*groundE) cache rho counter output rcache
    (OuterForestConcrete.V_forest secret (digestIndex output) (digestIndex_lt output) _ _ rcache
      (OuterGlobalFresh.freshF_of_all (digestIndex_lt output) hf)) ?_ ?_
  · refine h.trans (le_of_eq ?_)
    rw [show 111993=31121+80704+168 by decide,pow_add,pow_add]
    unfold ftsE outerE
    ac_rfl
  · intro forest hforest
    exact V_prepareRoots_U16 secret (digestIndex output) (digestIndex_lt output) forest.2
      (prepFresh_of_all _ (digestIndex_lt output) _
        (OuterForestPreserves.forest_allGFresh secret _ _ _ rcache hg forest hforest))
  · intro forest hforest prepared hprepared
    exact OuterLayerMoment.V_layers_certified secret cache (digestIndex output) prepared.1 forest.1.2 prepared.2
      (prepareRoots_preserves_rows secret (digestIndex output) 0 forest.2
        (OuterForestPreserves.forest_preserves_rows secret (digestIndex output) 0 _ _ rcache hfresh forest hforest)
        prepared hprepared)

#print axioms V_signFromOutput_certified
end OuterSigningMoment
