import SigGolfCandidate.OuterSourceCompleteness
import SigGolfCandidate.OuterCodecChecks
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterCompletenessProbability
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload
open SigGolfCandidate.T3.Correctness SigGolfCandidate.T3.SourceReplay
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.QuerySpace
open SphincsSecurity.Completeness
open ClaudeWCT.W9.T3.TopMoment
open OuterSourceCompleteness (SigningComplete tableGoodForNonces_signing)
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType (ClaudeWCT.W9.T3.QuerySpace.SearchKey→HashOutput) := ClaudeWCT.W9.T3.Presampling.tableSampler
noncomputable local instance : SampleableType ClaudeWCT.W9.T3.NonceSampling.NonceOutputs := ClaudeWCT.W9.T3.NonceSampling.nonceSampler
noncomputable def fullCheck : M Bool := do
  let levels←buildTopTree
  let b←OuterCodecChecks.checks
  pure (decide (TopLevelsOK levels) && b.1 && b.2)
noncomputable def checkedProgram (P : M Bool) : M (Bool×Bool) := do
  let g←fullCheck
  let b←P
  pure (g,b)
noncomputable def checkedOK (P : M Bool) : M Bool := (fun p : Bool×Bool=>!p.1 || p.2) <$> checkedProgram P

theorem hashOnly_fullCheck : HashOnly fullCheck :=
  hashOnly_bind hashOnly_buildTopTree (fun _=>hashOnly_bind OuterCodecChecks.checks_hashOnly (fun _=>hashOnly_pure _))
theorem hashOnly_checkedOK {P : M Bool} (hP : HashOnly P) : HashOnly (checkedOK P) :=
  hashOnly_map _ (hashOnly_bind hashOnly_fullCheck (fun _=>hashOnly_bind hP (fun _=>hashOnly_pure _)))

theorem checkedOK_true_of_good (P : M Bool) (answers : Answers)
    (hP : TopTreeOK answers→LowerTreesOK answers→OuterHybridGlobalCorrectness.ForestsOK answers→evalWithAnswerFn answers P=true) :
    evalWithAnswerFn answers (checkedOK P)=true := by
  unfold checkedOK checkedProgram fullCheck
  simp only [evalWithAnswerFn_map,evalWithAnswerFn_bind,evalWithAnswerFn_pure,eval_buildTopTree,OuterCodecChecks.checks_eval]
  by_cases ht : TopTreeOK answers
  · have ht' : TopLevelsOK (builtTree answers 0 0) := ht
    cases hf : evalWithAnswerFn answers OuterHybridGlobalComplete.check <;>
      cases hl : evalWithAnswerFn answers ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.lowerCheck
    · simp [ht',hf,hl]
    · simp [ht',hf,hl]
    · simp [ht',hf,hl]
    · simp [ht',hf,hl,hP ht
        (ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.eval_lowerCheck_true answers hl)
        (OuterHybridGlobalCorrectness.eval_check_true answers hf)]
  · have ht' : ¬TopLevelsOK (builtTree answers 0 0) := ht
    simp [ht']

theorem checked_prepared_failure_zero (P : M Bool) (hPh : HashOnly P)
    (hP : ∀ answers : Answers, OuterSourceCompleteness.SigningComplete answers (evalWithAnswerFn answers keygen).2 → TopTreeOK answers →
      LowerTreesOK answers → OuterHybridGlobalCorrectness.ForestsOK answers → evalWithAnswerFn answers P = true) (secret : BitVec 256)
    (nonces : ClaudeWCT.W9.T3.NonceSampling.NonceOutputs) (outputs : ClaudeWCT.W9.T3.NonceSampling.SearchOutputs)
    (hgood : TableGoodForNonces (fun message => BitVec.ofNat 128 (SigGolfCandidate.T3.rhoMod (nonces message))) outputs) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret (checkedOK P))).run'
        (ClaudeWCT.W9.T3.NonceSampling.preparedCache secret nonces outputs)]=0 := by
  refine SigGolfCandidate.T3.Completeness.failure_zero_of_fixed_replay secret (checkedOK P) _ ?_
  intro hash hagree
  have hsearch : ClaudeWCT.W9.T3.Budgets.SearchAgreement outputs (fixedAnswers secret hash) := by
    intro key
    change hash (ClaudeWCT.W9.T3.QuerySpace.searchQuery key)=outputs key
    exact hagree (ClaudeWCT.W9.T3.NonceSampling.preparedCache_search secret nonces outputs key)
  have hnonce : ∀ message, evalWithAnswerFn (fixedAnswers secret hash) (privateNonce message)=
      BitVec.ofNat 128 (SigGolfCandidate.T3.rhoMod (nonces message)) := by
    intro message
    have h := hagree (ClaudeWCT.W9.T3.NonceSampling.preparedCache_nonce secret nonces outputs message)
    exact congrArg (fun output : HashOutput => BitVec.ofNat 128 (SigGolfCandidate.T3.rhoMod output)) h
  have hcomplete := OuterSourceCompleteness.tableGoodForNonces_signing outputs (fixedAnswers secret hash)
    (fun message => BitVec.ofNat 128 (SigGolfCandidate.T3.rhoMod (nonces message))) hgood hsearch hnonce
  exact (fixed_replay secret hash _ (hashOnly_checkedOK hPh)).trans
    (congrArg (pure : Bool → ProbComp Bool) (checkedOK_true_of_good P _ (hP _ hcomplete)))

theorem checked_failure_small (P : M Bool) (hPh : HashOnly P)
    (hP : ∀ answers : Answers, OuterSourceCompleteness.SigningComplete answers (evalWithAnswerFn answers keygen).2 → TopTreeOK answers →
      LowerTreesOK answers → OuterHybridGlobalCorrectness.ForestsOK answers → evalWithAnswerFn answers P = true) (secret : BitVec 256) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret (checkedOK P))).run' ∅]≤
        1/(2:ENNReal)^138 := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value=false))
    (ClaudeWCT.W9.T3.NonceSampling.presample_source secret (checkedOK P))
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_of_forall_le
  intro nonces _
  refine (probEvent_bind_le_probEvent
    (p:=fun outputs => ¬TableGoodForNonces (fun message => BitVec.ofNat 128 (SigGolfCandidate.T3.rhoMod (nonces message))) outputs)
    (fun outputs _ hgood => checked_prepared_failure_zero P hPh hP secret nonces outputs (not_not.mp hgood))).trans ?_
  exact tableGoodForNonces_failure _


theorem fullCheck_bad_moment (secret : BitVec 256) :
    Ev secret fullCheck ∅ (fun r=>if r.1 then 0 else 1)≤
      ENNReal.ofReal (1/(2:ℝ)^135)+(ENNReal.ofReal (1/(2:ℝ)^146)+ENNReal.ofReal (1/(2:ℝ)^150)) := by
  unfold fullCheck
  rw [Ev_bind]
  have hinner : ∀ r∈support (Sampling.roRun secret buildTopTree ∅),
      Ev secret (OuterCodecChecks.checks >>= fun b=>pure (decide (TopLevelsOK r.1) && b.1 && b.2)) r.2
        (fun x=>if x.1 then 0 else 1)≤(if TopLevelsOK r.1 then 0 else 1)+
          (ENNReal.ofReal (1/(2:ℝ)^146)+ENNReal.ofReal (1/(2:ℝ)^150)) := by
    intro r hr
    rw [Ev_bind]
    have hpt : ∀ x : (Bool×Bool)×Sampling.RCache,
        Ev secret (pure (decide (TopLevelsOK r.1) && x.1.1 && x.1.2)) x.2 (fun y=>if y.1 then 0 else 1)≤
          (if TopLevelsOK r.1 then 0 else 1)+(if x.1.1 && x.1.2 then 0 else 1) := by
      intro x
      rw [Ev_pure]
      by_cases ht : TopLevelsOK r.1 <;> cases x.1.1 <;> cases x.1.2 <;> simp [ht]
    refine le_trans (Ev_mono _ _ _ hpt) ?_
    have hadd : Ev secret OuterCodecChecks.checks r.2
        (fun x=>(if TopLevelsOK r.1 then 0 else 1)+(if x.1.1 && x.1.2 then 0 else 1))=
        Ev secret OuterCodecChecks.checks r.2 (fun _=>if TopLevelsOK r.1 then 0 else 1)+
        Ev secret OuterCodecChecks.checks r.2 (fun x=>if x.1.1 && x.1.2 then 0 else 1) := by
      unfold Ev
      rw [expectedValue_add]
    rw [hadd]
    exact add_le_add (Ev_const_le secret _ _ _)
      (OuterCodecChecks.checks_failure secret r.2
        (ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.buildTopTree_allGFresh secret ∅
          ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.allGFresh_empty r hr)
        (ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete.buildTopTree_allFFresh secret ∅
          ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.allFFresh_empty r hr)
        (OuterCodecChecks.buildTopTree_fresh secret r hr))
  refine le_trans (expectedValue_mono_of_support hinner) ?_
  change Ev secret buildTopTree ∅ (fun r=>(if TopLevelsOK r.1 then 0 else 1)+
    (ENNReal.ofReal (1/(2:ℝ)^146)+ENNReal.ofReal (1/(2:ℝ)^150)))≤_
  unfold Ev
  rw [expectedValue_add]
  exact add_le_add (Ev_buildTopTree_bad secret) (Ev_const_le secret _ _ _)

theorem fullCheck_failure_small (secret : BitVec 256) :
    Pr[fun value=>value=false | (simulateQ SphincsSecurity.romImpl (realize secret fullCheck)).run' ∅]≤
      ENNReal.ofReal (1/(2:ℝ)^135)+(ENNReal.ofReal (1/(2:ℝ)^146)+ENNReal.ofReal (1/(2:ℝ)^150)) := by
  refine le_trans (le_of_eq ?_) (fullCheck_bad_moment secret)
  rw [StateT.run'_eq]
  change Pr[fun value=>value=false | Prod.fst <$> Sampling.roRun secret fullCheck ∅]=_
  rw [probEvent_map,probEvent_eq_tsum_ite]
  unfold Ev
  rw [expectedValue_def]
  apply tsum_congr
  intro r
  cases h : r.1 <;> simp [h]

theorem failure_le (P : M Bool) (secret : BitVec 256) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret P)).run' ∅] ≤
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret (checkedOK P))).run' ∅] +
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret fullCheck)).run' ∅] := by
  classical
  -- the joint law
  set A := Sampling.roRun secret fullCheck ∅ with hA
  set J : ProbComp (Bool × Bool) := A >>= fun r =>
    (fun b => (r.1, b)) <$> (Prod.fst <$> Sampling.roRun secret P r.2) with hJ
  have hev : 𝒮[(simulateQ SphincsSecurity.romImpl (realize secret P)).run' ∅] =
      𝒮[Prod.snd <$> J] := by
    rw [SphincsSecurity.Seeded.evalDist_presample_computation (realize secret P)
      (realize secret fullCheck) ∅]
    rw [hJ, map_bind]
    simp only [Functor.map_map]
    rfl
  have hck : (simulateQ SphincsSecurity.romImpl (realize secret (checkedOK P))).run' ∅ =
      (fun p : Bool × Bool => !p.1 || p.2) <$> J := by
    rw [StateT.run'_eq]
    change Prod.fst <$> Sampling.roRun secret (checkedOK P) ∅ = _
    unfold checkedOK checkedProgram
    rw [Sampling.roRun_map, Sampling.roRun_bind, hJ]
    simp only [Sampling.roRun_pure, Sampling.roRun_map, map_bind, Functor.map_map,
      bind_pure_comp]
    rfl
  have htc : (simulateQ SphincsSecurity.romImpl (realize secret fullCheck)).run' ∅ = Prod.fst <$> A := by
    rw [StateT.run'_eq]; rfl
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value=false)) hev
  simp only [probEvent_evalSPMF] at hp
  rw [hp, hck, htc, probEvent_map, probEvent_map, probEvent_map]
  refine le_trans (probEvent_mono'' (q := fun x : Bool × Bool => (!x.1 || x.2) = false ∨ x.1 = false)
    (fun x hx => by cases x.1 <;> simp_all)) ?_
  refine le_trans (probEvent_or_le _ _ _) (add_le_add le_rfl ?_)
  rw [hJ]
  refine probEvent_bind_le_probEvent (p := fun r : Bool × Sampling.RCache => r.1 = false) (fun r _ hr => ?_)
  rw [probEvent_map]
  have : r.1 = true := by simpa using hr
  simp [Function.comp_def, this]

theorem failure_small (P : M Bool) (hPh : HashOnly P)
    (hP : ∀ answers : Answers, OuterSourceCompleteness.SigningComplete answers (evalWithAnswerFn answers keygen).2→
      TopTreeOK answers→LowerTreesOK answers→OuterHybridGlobalCorrectness.ForestsOK answers→evalWithAnswerFn answers P=true)
    (secret : BitVec 256) :
    Pr[fun value=>value=false | (simulateQ SphincsSecurity.romImpl (realize secret P)).run' ∅]≤1/(2:ENNReal)^128 := by
  refine (failure_le P secret).trans ?_
  refine (add_le_add (checked_failure_small P hPh hP secret) (fullCheck_failure_small secret)).trans ?_
  have hk : ∀ k : Nat, ENNReal.ofReal (1/(2:ℝ)^k)=1/(2:ENNReal)^k := by
    intro k
    rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_one,ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_ofNat]
  rw [←hk 138,←hk 128,←ENNReal.ofReal_add (by positivity) (by positivity),
    ←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

#print axioms fullCheck_bad_moment
#print axioms fullCheck_failure_small
#print axioms failure_small
#print axioms checked_failure_small
end OuterCompletenessProbability
