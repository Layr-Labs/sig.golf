import SigGolfCandidate.OuterExpansionCost
import SigGolfCandidate.OuterSigningCost
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterPayloadCost
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
attribute [local irreducible] SigGolfCandidate.T3.SearchCost.cost OuterForestMoment.forest
  OuterForestCorrectness.recoverForest OuterSigning.signFromOutput

theorem signPayload_cost_step (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
      digestAttemptLimit)=some (counter,output)) :
    cost answers (OuterSigning.signPayload cache message)=cost answers (privateNonce message)+
      cost answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message)) message 0 digestAttemptLimit)+
      cost answers (OuterSigning.signFromOutput cache (evalWithAnswerFn answers (privateNonce message)) counter output) := by
  simp only [OuterSigning.signPayload,cost_bind,hd]
  split <;> simp only [cost_pure,Nat.add_zero,Nat.add_assoc]
theorem expand_cost_le_payload_field (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hreg : cache.region = cacheRegion (maskedTop answers)) (message : Message) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (hs' : evalWithAnswerFn answers (OuterSigning.signPayload cache message) = some sig) (pk : Digest)
    (hpk : pk = treeValue (builtTree answers 0 0) 12 0) :
    cost answers (OuterExpand.expandN message pk sig) ≤ cost answers (OuterSigning.signPayload cache message) + 137288 +
        max (topField (treeValue (builtTree answers 0 0) 11 0)) (topField (treeValue (builtTree answers 0 0) 11 1)) := by
  unfold OuterSigning.signPayload at hs'
  simp only [evalWithAnswerFn_bind] at hs'
  let rho := evalWithAnswerFn answers (privateNonce message)
  cases hd : evalWithAnswerFn answers (sharedDigestSearch rho message 0 digestAttemptLimit) with
  | none =>
    dsimp only [rho] at hd
    simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at hs'
  | some found =>
    obtain ⟨counter, output⟩ := found
    dsimp only [rho] at hd
    simp only [hd, evalWithAnswerFn_bind] at hs'
    cases hso : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output) with
    | none =>
      dsimp only [rho] at hso
      simp only [hso, evalWithAnswerFn_pure, reduceCtorEq] at hs'
    | some original =>
      have hr := OuterSigningCost.signFromOutput_recovery_cost_le answers cache hreg rho counter output original hso
      have hh := OuterSourceRecovery.signFromOutput_recovery answers cache hreg rho counter output original hso
      have hsib := OuterSigningCost.signFromOutput_topSib answers cache hreg rho counter output original hso
      dsimp only [rho] at hso
      simp only [hso, evalWithAnswerFn_pure, Option.some.injEq] at hs'
      subst sig
      obtain ⟨hrho, result, hres, hroot, hval, _⟩ := hh
      have hd' : evalWithAnswerFn answers (sharedDigestSearch original.signature.rho message 0 digestAttemptLimit) =
          some (counter, output) := by rw [hrho]; exact hd
      have hx := OuterExpansionCost.expand_cost_le_recovery_field answers message pk original.signature counter output result hd'
        hres (hroot.trans hpk.symm)
      have hf := OuterRecoverBudget.forest_cost answers (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) original.signature.forest
      have hle := SigGolfCandidate.Research.SharedForest.topField_sib_le answers (digestIndex output)
      rw [← hsib] at hle
      rw [hrho] at hx
      dsimp only [rho] at hx hr
      rw [signPayload_cost_step answers cache message counter output hd]
      omega


theorem sign_cost_honest (answers : Answers) (message : Message) :
    cost answers (OuterSigning.sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message)=
      cost answers (privateMac (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.region)+
      cost answers (OuterSigning.signPayload (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) := by
  have hv:=keygen_cache_tag answers
  simp only [CacheTagCorrect] at hv
  simp only [OuterSigning.sign,cost_bind,←hv,ne_eq,not_true_eq_false,ite_false]

theorem expand_cost_le_sign_field (answers : Answers) (message : Message)
    (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (hs : evalWithAnswerFn answers (OuterSigning.sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message)=some sig) :
    cost answers (OuterExpand.expandN message (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).1 sig)≤
      cost answers (OuterSigning.sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message)+137288+
        max (topField (treeValue (builtTree answers 0 0) 11 0)) (topField (treeValue (builtTree answers 0 0) 11 1)) := by
  have hv:=keygen_cache_tag answers
  have hk:=SigGolfCandidate.T3.Correctness.keygen_correct answers
  have hp : evalWithAnswerFn answers (OuterSigning.signPayload (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message)=some sig := by
    simp only [CacheTagCorrect] at hv
    simpa only [OuterSigning.sign,evalWithAnswerFn_bind,←hv,ne_eq,not_true_eq_false,ite_false] using hs
  have he:=expand_cost_le_payload_field answers _ hk.2.1 message sig hp _ hk.1
  rw [sign_cost_honest]
  omega

#print axioms expand_cost_le_sign_field

#print axioms signPayload_cost_step
#print axioms expand_cost_le_payload_field
end OuterPayloadCost
