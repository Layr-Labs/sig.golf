import SigGolfCandidate.OuterPhaseCostEval
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterPhaseBudget
open OracleComp OracleSpec OracleComp.EvalDist ENNReal SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Spec keygen)
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final ClaudeWCT.W9.T3M.Final
open OuterImageValidity
set_option allowUnsafeReducibility true in
attribute [local reducible] OuterRuntime.runtimeSub SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
attribute [local irreducible] SigGolfCandidate.Legacy.Submission.run

theorem allQ_sign {Q : Spec.Domain→Prop} (hk : AllQueriesSatisfy keygen Q)
    (hs : ∀ c m,AllQueriesSatisfy (OuterLooseSource.signCompact c m) Q) (m : Message) :
    AllQueriesSatisfy (OuterLooseBudget.honestSignCount m) Q :=
  allQ_bind hk fun _=>allQ_countWith _ (hs _ _)

theorem allQ_joint {Q : Spec.Domain→Prop} (hk : AllQueriesSatisfy keygen Q)
    (hs : ∀ c m,AllQueriesSatisfy (OuterLooseSource.signCompact c m) Q)
    (he : ∀ m pk sig,AllQueriesSatisfy (OuterExpand.expandCompact m pk sig) Q) (m : Message) :
    AllQueriesSatisfy (OuterLooseMoment.joint m) Q := by
  unfold OuterLooseMoment.joint SigGolfCandidate.T3.ExpansionClosure.jointCounts
  refine allQ_bind hk fun keys=>allQ_bind (allQ_countWith _ (hs _ _)) fun signed=>?_
  rcases signed with ⟨_|sig,n⟩
  · exact allQ_pure _
  · exact allQ_bind (allQ_countWith _ (he _ _ _)) fun _=>allQ_pure _

theorem sign_bound (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle (sub.honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .sign : ℝ) / (Phase.sign.budget : ℝ)))) ≤ 2 := by
  have hgood : AllQueriesSatisfy (OuterLooseBudget.honestSignCount m)
      SigGolfCandidate.T3.Cost.GoodQuery :=
    allQ_sign SigGolfCandidate.T3M.goodQ_keygen OuterGoodQueries.compactSign m
  have hhash : AllQueriesSatisfy (OuterLooseBudget.honestSignCount m) isHash :=
    allQ_sign SigGolfCandidate.T3.SourceReplay.hashOnly_keygen OuterLooseHashOnly.signCompact m
  have h := randomOracle_congr _ _ (OuterPhaseCostEval.sign sk m)
  calc expectedValue (withRandomOracle (sub.honest sk m)) (fun result => ENNReal.ofReal
        (Real.rpow 2 ((result.costs .sign : ℝ) / (Phase.sign.budget : ℝ))))
      = expectedValue (withRandomOracle ((fun r => r.costs .sign) <$> sub.honest sk m))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.sign.budget : ℝ)))) := by
        rw [withRandomOracle_map', expectedValue_map]
    _ = expectedValue (withRandomOracle ((fun r => r.2) <$>
          mrealize sk (OuterLooseBudget.honestSignCount m)))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.sign.budget : ℝ)))) :=
        expectedValue_congr_evalSPMF h _
    _ = expectedValue (SigGolfCandidate.T3.Sampling.roRun sk (OuterLooseBudget.honestSignCount m) ∅)
          (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 131072)) := by
        rw [withRandomOracle_map', withRandomOracle_mrealize sk hgood hhash, Functor.map_map, expectedValue_map]
        refine congrArg _ (funext fun r => ?_)
        rw [two_rpow_eq', show Phase.sign.budget = 2 ^ 17 from rfl]
        norm_num
    _ ≤ 2 := OuterLooseBudget.honest_sign_exponential_budget sk m
set_option maxRecDepth 100000 in
theorem expand_bound (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle (sub.honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .expand : ℝ) / (Phase.expand.budget : ℝ)))) ≤ 2 := by
  have hgood : AllQueriesSatisfy (OuterLooseMoment.joint m)
      SigGolfCandidate.T3.Cost.GoodQuery :=
    allQ_joint SigGolfCandidate.T3M.goodQ_keygen OuterGoodQueries.compactSign OuterGoodQueries.compactExpand m
  have hhash : AllQueriesSatisfy (OuterLooseMoment.joint m) isHash :=
    allQ_joint SigGolfCandidate.T3.SourceReplay.hashOnly_keygen OuterLooseHashOnly.signCompact OuterHashOnly.expandCompact m
  have h := randomOracle_congr _ _ (OuterPhaseCostEval.expand sk m)
  calc expectedValue (withRandomOracle (sub.honest sk m)) (fun result => ENNReal.ofReal
        (Real.rpow 2 ((result.costs .expand : ℝ) / (Phase.expand.budget : ℝ))))
      = expectedValue (withRandomOracle ((fun r => r.costs .expand) <$> sub.honest sk m))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.expand.budget : ℝ)))) := by
        rw [withRandomOracle_map', expectedValue_map]
    _ = expectedValue (withRandomOracle ((fun r => r.2) <$>
          mrealize sk (OuterLooseMoment.joint m)))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.expand.budget : ℝ)))) :=
        expectedValue_congr_evalSPMF h _
    _ = expectedValue (SigGolfCandidate.T3.Sampling.roRun sk
          (OuterLooseMoment.joint m) ∅)
          (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 1048576)) := by
        rw [withRandomOracle_map', withRandomOracle_mrealize sk hgood hhash, Functor.map_map, expectedValue_map]
        refine congrArg _ (funext fun r => ?_)
        rw [two_rpow_eq', show Phase.expand.budget = 2 ^ 20 from rfl]
        norm_num
    _ ≤ 2 := OuterLooseExpansionBudget.honest_expand_exponential_budget sk m

#print axioms sign_bound
#print axioms expand_bound
end OuterPhaseBudget
