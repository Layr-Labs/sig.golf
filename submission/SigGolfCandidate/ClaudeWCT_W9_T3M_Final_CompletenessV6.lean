import SigGolfCandidate.ClaudeWCT_W9_T3M_Final_Pending
import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_TopCapBad

/-! # img-v6 source completeness with the 5,239-byte codec (r3-lean-topbytes)

`expand` normalizes the top path, so an honest signature expands only if every keygen top node passed its zero test
(`TopTreeOK`). The check `topCheck` runs first (it does not change the distribution of `everyMessageProgram`,
`evalDist_presample_computation`); then

`Pr[everyMessageProgram = false] ≤ Pr[checkedOK = false] + Pr[topCheck = false] ≤ 2^-138 + 2^-135 ≤ 2^-128`,

where `checkedOK = (!topCheck || everyMessageProgram)` is handled by the presampled-table argument (as before) and
`topCheck` by the cap-exhaustion bound `TopMoment.Ev_buildTopTree_bad`. -/

namespace ClaudeWCT.W9.T3.Completeness.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SourceReplay
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.QuerySpace
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler
noncomputable local instance : SampleableType NonceSampling.NonceOutputs := NonceSampling.nonceSampler

open Classical in
/-- Did every keygen top node pass its zero test? -/
noncomputable def topCheck : M Bool := do
  let levels ← buildTopTree
  pure (decide (ClaudeWCT.W9.T3.TopMoment.TopLevelsOK levels))

noncomputable def checkedProgram : M (Bool × Bool) := do
  let g ← topCheck
  let b ← everyMessageProgram
  pure (g, b)

noncomputable def checkedOK : M Bool := (fun p : Bool × Bool => !p.1 || p.2) <$> checkedProgram

theorem hashOnly_topCheck : HashOnly topCheck :=
  hashOnly_bind hashOnly_buildTopTree fun _ => hashOnly_pure _

theorem hashOnly_checkedOK : HashOnly checkedOK :=
  hashOnly_map _ (hashOnly_bind hashOnly_topCheck fun _ =>
    hashOnly_bind hashOnly_everyMessageProgram fun _ => hashOnly_pure _)

open Classical in
theorem eval_topCheck (answers : Answers) :
    evalWithAnswerFn answers topCheck = decide (TopTreeOK answers) := by
  unfold topCheck
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_buildTopTree]
  rfl

theorem checkedOK_true_of_complete (answers : Answers)
    (hcomplete : SigningComplete answers (evalWithAnswerFn answers keygen).2) :
    evalWithAnswerFn answers checkedOK = true := by
  classical
  unfold checkedOK checkedProgram
  simp only [evalWithAnswerFn_map, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_topCheck]
  by_cases htree : TopTreeOK answers
  · simp [htree, everyMessageProgram_true_of_complete answers hcomplete htree]
  · simp [htree]

theorem checked_prepared_failure_zero (secret : BitVec 256)
    (nonces : NonceSampling.NonceOutputs) (outputs : NonceSampling.SearchOutputs)
    (hgood : TableGoodForNonces (fun message => (nonces message).extractLsb' 0 128) outputs) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret checkedOK)).run'
        (NonceSampling.preparedCache secret nonces outputs)]=0 := by
  refine SigGolfCandidate.T3.Completeness.failure_zero_of_fixed_replay secret checkedOK _ ?_
  intro hash hagree
  have hsearch : Budgets.SearchAgreement outputs (fixedAnswers secret hash) := by
    intro key
    change hash (searchQuery key)=outputs key
    exact hagree (NonceSampling.preparedCache_search secret nonces outputs key)
  have hnonce : ∀ message, evalWithAnswerFn (fixedAnswers secret hash) (privateNonce message)=
      (nonces message).extractLsb' 0 128 := by
    intro message
    have h := hagree (NonceSampling.preparedCache_nonce secret nonces outputs message)
    exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) h
  have hcomplete := tableGoodForNonces_signing outputs (fixedAnswers secret hash)
    (fun message => (nonces message).extractLsb' 0 128) hgood hsearch hnonce
  exact (fixed_replay secret hash _ hashOnly_checkedOK).trans
    (congrArg (pure : Bool → ProbComp Bool) (checkedOK_true_of_complete _ hcomplete))

theorem checked_failure_small (secret : BitVec 256) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret checkedOK)).run' ∅]≤
        1/(2:ENNReal)^138 := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value=false))
    (NonceSampling.presample_source secret checkedOK)
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_of_forall_le
  intro nonces _
  refine (probEvent_bind_le_probEvent
    (p:=fun outputs => ¬TableGoodForNonces (fun message => (nonces message).extractLsb' 0 128) outputs)
    (fun outputs _ hgood => checked_prepared_failure_zero secret nonces outputs (not_not.mp hgood))).trans ?_
  exact tableGoodForNonces_failure _

/-- The top check fails with probability at most `2^-135` (cap exhaustion). -/
theorem topCheck_failure_small (secret : BitVec 256) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret topCheck)).run' ∅] ≤ ENNReal.ofReal (1 / 2 ^ 135) := by
  classical
  refine le_trans (le_of_eq ?_) (ClaudeWCT.W9.T3.TopMoment.Ev_buildTopTree_bad secret)
  rw [StateT.run'_eq]
  change Pr[fun value => value = false | Prod.fst <$> Sampling.roRun secret topCheck ∅] = _
  unfold topCheck
  rw [Sampling.roRun_bind, map_bind, probEvent_bind_eq_tsum]
  unfold ClaudeWCT.W9.T3.TopMoment.Ev
  rw [expectedValue_def]
  refine tsum_congr fun r => ?_
  rw [Sampling.roRun_pure, map_pure, probEvent_pure]
  congr 1
  by_cases h : ClaudeWCT.W9.T3.TopMoment.TopLevelsOK r.1 <;> simp [h]

/-- Running the top check first does not change the law of `everyMessageProgram`; on the joint run a failure of
`everyMessageProgram` is a failure of `checkedOK` or of `topCheck`. -/
theorem everyMessage_failure_le (secret : BitVec 256) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] ≤
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret checkedOK)).run' ∅] +
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret topCheck)).run' ∅] := by
  classical
  -- the joint law
  set A := Sampling.roRun secret topCheck ∅ with hA
  set J : ProbComp (Bool × Bool) := A >>= fun r =>
    (fun b => (r.1, b)) <$> (Prod.fst <$> Sampling.roRun secret everyMessageProgram r.2) with hJ
  have hev : 𝒮[(simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] =
      𝒮[Prod.snd <$> J] := by
    rw [SphincsSecurity.Seeded.evalDist_presample_computation (realize secret everyMessageProgram)
      (realize secret topCheck) ∅]
    rw [hJ, map_bind]
    simp only [Functor.map_map]
    rfl
  have hck : (simulateQ SphincsSecurity.romImpl (realize secret checkedOK)).run' ∅ =
      (fun p : Bool × Bool => !p.1 || p.2) <$> J := by
    rw [StateT.run'_eq]
    change Prod.fst <$> Sampling.roRun secret checkedOK ∅ = _
    unfold checkedOK checkedProgram
    rw [Sampling.roRun_map, Sampling.roRun_bind, hJ]
    simp only [Sampling.roRun_pure, Sampling.roRun_map, map_bind, Functor.map_map,
      bind_pure_comp]
    rfl
  have htc : (simulateQ SphincsSecurity.romImpl (realize secret topCheck)).run' ∅ = Prod.fst <$> A := by
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

theorem everyMessage_failure_small (secret : BitVec 256) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] ≤
        1/(2:ENNReal)^128 := by
  refine (everyMessage_failure_le secret).trans ?_
  refine le_trans (add_le_add (checked_failure_small secret) (topCheck_failure_small secret)) ?_
  have h135 : ENNReal.ofReal (1 / 2 ^ 135) = 1 / (2 : ENNReal) ^ 135 := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [h135]
  have h1 : 1/(2:ENNReal)^138 ≤ 1/(2:ENNReal)^129 :=
    ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by norm_num)) _
  have h2 : 1/(2:ENNReal)^135 ≤ 1/(2:ENNReal)^129 :=
    ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by norm_num)) _
  have h3 : 1/(2:ENNReal)^129 + 1/(2:ENNReal)^129 = 1/(2:ENNReal)^128 := by
    rw [← two_mul, pow_succ, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
      ENNReal.mul_inv (by simp) (by simp), ← mul_assoc, ← mul_assoc,
      mul_comm (2 : ENNReal) ((2 : ENNReal) ^ 128)⁻¹, mul_assoc ((2 : ENNReal) ^ 128)⁻¹ 2 2⁻¹,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  exact (add_le_add h1 h2).trans (le_of_eq h3)

theorem source_completeness (secret : BitVec 256) :
    1-1/(2:ENNReal)^128≤
      Pr[=true | (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] := by
  have hf := everyMessage_failure_small secret
  rw [probEvent_eq_eq_probOutput] at hf
  rw [probOutput_true_eq_sub]
  simp only [probFailure_eq_zero,tsub_zero]
  exact tsub_le_tsub_left hf 1
#print axioms source_completeness
end ClaudeWCT.W9.T3.Completeness.Paired
