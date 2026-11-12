import SigGolfCandidate.OuterKeygenRun
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterKeygenBudget
open OracleComp OracleSpec OracleComp.EvalDist ENNReal SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (keygen)
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final ClaudeWCT.W9.T3M.Final
open OuterImageValidity
set_option allowUnsafeReducibility true in
attribute [local reducible] OuterRuntime.runtimeSub SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
attribute [local irreducible] SigGolfCandidate.Legacy.Submission.run

theorem cost_eval (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r=>r.costs .keygen) <$> sub.honest sk m)=
      evalWithAnswerFn hash ((fun r=>r.2) <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks keygen)) := by
  rw [evalWithAnswerFn_map,eval_costs_keygen,evalWithAnswerFn_map]
  exact abstract_count_refinement sk hash keygen (sub.run .keygen sk)
    (fun p=>some (p.1,cacheB p.2)) (OuterKeygenRun.counts sk) goodQ_keygen

theorem keygen_bound (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle (sub.honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ)))) ≤ 2 := by
  have hgood : AllQueriesSatisfy (SigGolfCandidate.T3.Cost.countBlocks keygen) SigGolfCandidate.T3.Cost.GoodQuery :=
    allQ_countWith SigGolfCandidate.T3.Cost.weight SigGolfCandidate.T3M.goodQ_keygen
  have hhash : AllQueriesSatisfy (SigGolfCandidate.T3.Cost.countBlocks keygen) isHash :=
    allQ_countWith SigGolfCandidate.T3.Cost.weight SigGolfCandidate.T3.SourceReplay.hashOnly_keygen
  have h := randomOracle_congr _ _ (cost_eval sk m)
  calc expectedValue (withRandomOracle (sub.honest sk m)) (fun result => ENNReal.ofReal
        (Real.rpow 2 ((result.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ))))
      = expectedValue (withRandomOracle ((fun r => r.costs .keygen) <$> sub.honest sk m))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.keygen.budget : ℝ)))) := by
        rw [withRandomOracle_map', expectedValue_map]
    _ = expectedValue (withRandomOracle ((fun r => r.2) <$>
          mrealize sk (SigGolfCandidate.T3.Cost.countBlocks keygen)))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.keygen.budget : ℝ)))) :=
        expectedValue_congr_evalSPMF h _
    _ = expectedValue (SigGolfCandidate.T3.Sampling.roRun sk (SigGolfCandidate.T3.Cost.countBlocks keygen) ∅)
          (fun result => (2 : ENNReal) ^ ((result.1.2 : ℝ) / 1048576)) := by
        rw [withRandomOracle_map', withRandomOracle_mrealize sk hgood hhash, Functor.map_map, expectedValue_map]
        refine congrArg _ (funext fun r => ?_)
        rw [two_rpow_eq', show Phase.keygen.budget = 2 ^ 20 from rfl]
        norm_num
    _ ≤ 2 := ClaudeWCT.W9.T3.TopMoment.keygen_moment_v6 sk

#print axioms keygen_bound
end OuterKeygenBudget
