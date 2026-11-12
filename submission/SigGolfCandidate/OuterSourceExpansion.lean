import SigGolfCandidate.OuterSourceRecovery
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterSourceExpansion
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest

theorem expand_complete_of_recovered (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (counter : BitVec 32) (output : HashOutput) (result : RecoveredLayers)
    (hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) =
      some (counter, output))
    (hr : evalWithAnswerFn answers (recoverHintedLayers sig (digestIndex output)
      ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1.1
        (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1.2)) = some result)
    (hh : OuterSigning.policyHintsValid (digestIndex output) sig.policyHints result.digits result.lows = true) (hpk : result.root = pk)
    :
    ∃ w, evalWithAnswerFn answers (OuterExpand.expandN message pk sig) = some w := by
  have hhbound : sig.policyHints.toNat < 12288 := by
    simp only [OuterSigning.policyHintsValid, decide_eq_true_eq] at hh
    exact hh.1
  let index := digestIndex output
  let forest := (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) sig.forest)).1
  let sig0 := fillTopSignature sig 0
  let result0 : RecoveredLayers := {result with
    root := evalWithAnswerFn answers (topNode index result.foldedTop ((sig0.layers 0).path topJ))}
  have hr0 : evalWithAnswerFn answers (recoverHintedLayers sig0 index
      ((sig0.layers 0).path topJ) 4 (.pair forest.1 forest.2)) = some result0 := by
    dsimp only [sig0]
    rw [recoverHintedLayers_fill _ _ _ _ _ le_rfl,
      eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)]
    rw [hr]
    rfl
  have hroot : evalWithAnswerFn answers (topNode index result.foldedTop ((sig.layers 0).path topJ)) = pk := by
    have he := eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)
      ((sig.layers 0).path topJ) 4 (.pair forest.1 forest.2)
    rw [hr] at he
    simp only [Option.map_some, Option.some.injEq] at he
    have he' := congrArg RecoveredLayers.root he
    exact he'.symm.trans hpk
  unfold OuterExpand.expandN
  simp only [show ¬sig.policyHints.toNat ≥ 12288 by omega, if_false, evalWithAnswerFn_bind]
  simp only [nonce_retained, hd, evalWithAnswerFn_bind]
  dsimp only [sig0, index, forest] at hr0
  simp only [show (fillTopSignature sig 0).forest = sig.forest from rfl]
  rw [hr0]
  simp only [result0, sig0, hints_retained, hh, Bool.not_true, Bool.false_eq_true, if_false]
  by_cases hzero : result0.root = pk
  · dsimp only [result0, sig0] at hzero
    rw [if_pos hzero, evalWithAnswerFn_pure]
    exact ⟨_, rfl⟩
  · have hz : evalWithAnswerFn answers (topNode index result.foldedTop ((sig0.layers 0).path topJ)) ≠ pk := hzero
    have hcompletion : evalWithAnswerFn answers (topNode index result.foldedTop
        (setTop ((sig0.layers 0).path topJ) (((sig.layers 0).path topJ).toNat / 2 ^ 108))) = pk := by
      rw [topPath_fill_signature, setTop_setTop, setTop_self]
      exact hroot
    have hn : ((sig.layers 0).path topJ).toNat / 2 ^ 108 ≠ 0 := by
      intro he
      rw [he, topPath_fill_signature, setTop_setTop] at hcompletion
      exact hz hcompletion
    obtain ⟨c, hc⟩ := searchTop_complete answers index result.foldedTop ((sig0.layers 0).path topJ)
      pk searchFuel 1 (((sig.layers 0).path topJ).toNat / 2 ^ 108) (by omega)
      (by have ht := top_lt ((sig.layers 0).path topJ); unfold searchFuel; omega) hcompletion
    dsimp only [sig0] at hz
    dsimp only [sig0, index] at hc
    rw [if_neg hz, evalWithAnswerFn_bind, hc, evalWithAnswerFn_pure]
    exact ⟨_, rfl⟩


#print axioms expand_complete_of_recovered
end OuterSourceExpansion
