import SigGolfCandidate.OuterVerifySource
import SigGolfCandidate.OuterExpand
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterExpandVerified
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness SigGolfCandidate.Research.SharedForest
theorem verified (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (out : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns5 : List Nat)
    (he : evalWithAnswerFn answers (OuterExpand.expandN message pk sig) = some (out,w,ns5)) :
    evalWithAnswerFn answers (OuterVerifySource.verify message pk w ns5) = true := by
  unfold OuterExpand.expandN at he
  by_cases hh : sig.policyHints.toNat ≥ 12288
  · simp only [hh, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he
  simp only [hh, if_false, evalWithAnswerFn_bind] at he
  let sig0 := fillTopSignature sig 0
  cases hd : evalWithAnswerFn answers (sharedDigestSearch sig0.rho message 0 digestAttemptLimit) with
  | none =>
      dsimp only [sig0] at hd
      simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      have hdlim : 0 + digestAttemptLimit ≤ 2 ^ 32 := by simpa using digestAttemptLimit_le
      obtain ⟨_, _, haccept, houtput⟩ := sharedDigestSearch_some answers sig0.rho message
        digestAttemptLimit 0 counter output hdlim hd
      have ha := digestAccepted_implies_verify haccept
      dsimp only [sig0] at hd
      simp only [hd, evalWithAnswerFn_bind] at he
      let index := digestIndex output
      let forest := (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest index (forestSelectionFromOutput output)
        (forestWordsFromOutput output) sig0.forest)).1
      cases hr : evalWithAnswerFn answers (recoverHintedLayers sig0 index ((sig0.layers 0).path topJ)
        4 (.pair forest.1 forest.2)) with
      | none =>
          dsimp only [index, forest, sig0] at hr
          simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some result =>
          dsimp only [index, forest, sig0] at hr
          simp only [hr] at he
          cases hp : OuterSigning.policyHintsValid index sig0.policyHints result.digits result.lows with
          | false =>
              dsimp only [index, sig0] at hp
              simp only [hp, Bool.not_false, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he
          | true =>
              dsimp only [index, sig0] at hp
              simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at he
              by_cases hpk : result.root = pk
              · simp only [hpk, if_true, evalWithAnswerFn_pure, Option.some.injEq,Prod.mk.injEq] at he
                obtain ⟨rfl,rfl,rfl⟩ := he
                exact OuterVerifySource.from_recovered answers message pk sig0 counter output result houtput ha hr hpk
              · simp only [hpk, if_false, evalWithAnswerFn_bind] at he
                cases hs : evalWithAnswerFn answers
                  (searchTop index result.foldedTop ((sig0.layers 0).path topJ) pk searchFuel 1) with
                | none =>
                    dsimp only [index, sig0] at hs
                    simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
                | some c =>
                    dsimp only [index, sig0] at hs
                    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq,Prod.mk.injEq] at he
                    obtain ⟨rfl,rfl,rfl⟩ := he
                    have hc := (eval_searchTop answers index result.foldedTop ((sig0.layers 0).path topJ)
                      pk searchFuel 1 c hs).2.2
                    let completed : RecoveredLayers := {result with
                      root := evalWithAnswerFn answers
                        (topNode index result.foldedTop (((fillTopSignature sig0 c).layers 0).path topJ))}
                    have hcompleted : completed.root = pk := by
                      dsimp only [completed]
                      rw [topPath_fill_signature]
                      exact hc
                    have hr' : evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig0 c) index
                        (((fillTopSignature sig0 c).layers 0).path topJ) 4 (.pair forest.1 forest.2)) =
                        some completed := by
                      rw [recoverHintedLayers_fill _ _ _ _ _ le_rfl]
                      rw [eval_recoverHintedLayers_other answers sig0 index ((sig0.layers 0).path topJ)]
                      rw [hr]
                      rfl
                    exact OuterVerifySource.from_recovered answers message pk (fillTopSignature sig0 c)
                      counter output completed houtput ha hr' hcompleted

#print axioms verified
end OuterExpandVerified
