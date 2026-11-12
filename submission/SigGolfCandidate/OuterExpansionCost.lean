import SigGolfCandidate.OuterSourceExpansion
import SigGolfCandidate.OuterRecoverBudget
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterExpansionCost
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
open ClaudeWCT.W9.T3.ExpansionBudget (cost_bind_le)
attribute [local irreducible] OuterForestCorrectness.recoverForest
theorem expand_cost_le_recovery_field (answers : Answers) (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (counter : BitVec 32) (output : HashOutput) (result : RecoveredLayers)
    (hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) =
      some (counter, output))
    (hr : evalWithAnswerFn answers (recoverHintedLayers sig (digestIndex output) ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1.1
        (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1.2)) = some result)
    (hpk : result.root = pk) :
    cost answers (OuterExpand.expandN message pk sig) ≤
      cost answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) +
      cost answers (OuterForestCorrectness.recoverForest (digestIndex output) (forestSelectionFromOutput output)
        (forestWordsFromOutput output) sig.forest) +
      cost answers (recoverHintedLayers sig (digestIndex output) ((sig.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1.1
          (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
            (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1.2)) +
      topField ((sig.layers 0).path topJ) := by
  let index := digestIndex output
  let forest := evalWithAnswerFn answers (OuterForestCorrectness.recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) sig.forest)
  let sig0 := fillTopSignature sig 0
  have hroot : evalWithAnswerFn answers (topNode index result.foldedTop ((sig.layers 0).path topJ)) = pk := by
    have he := eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)
      ((sig.layers 0).path topJ) 4 (.pair forest.1.1 forest.1.2)
    rw [hr] at he
    simp only [Option.map_some, Option.some.injEq] at he
    exact (congrArg RecoveredLayers.root he).symm.trans hpk
  have hr0 : evalWithAnswerFn answers (recoverHintedLayers sig index ((sig0.layers 0).path topJ) 4
      (.pair forest.1.1 forest.1.2)) = some {result with
        root := evalWithAnswerFn answers (topNode index result.foldedTop ((sig0.layers 0).path topJ))} := by
    rw [eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)]
    rw [hr]
    rfl
  unfold OuterExpand.expandN
  split
  · simp only [cost_pure]; omega
  · simp only [cost_bind, nonce_retained, hd,
      show (fillTopSignature sig 0).forest = sig.forest from rfl]
    rw [recoverHintedLayers_fill _ _ _ _ _ le_rfl,
      cost_recoverHintedLayers_other answers sig (digestIndex output)
        (((fillTopSignature sig 0).layers 0).path topJ) ((sig.layers 0).path topJ)]
    simp only [Nat.add_assoc]
    apply Nat.add_le_add_left
    apply Nat.add_le_add_left
    apply Nat.add_le_add_left
    dsimp only [sig0, index, forest] at hr0
    rw [hr0]
    simp only
    split
    · simp only [cost_pure]; exact Nat.zero_le _
    · split
      · simp only [cost_pure]; exact Nat.zero_le _
      · rename_i hz
        refine le_trans (cost_bind_le answers _ _ 0 ?_) ?_
        · split <;> simp only [cost_pure, le_refl]
        · rw [Nat.add_zero]
          have hcompletion : evalWithAnswerFn answers (topNode (digestIndex output) result.foldedTop
              (setTop (((fillTopSignature sig 0).layers 0).path topJ) (topField ((sig.layers 0).path topJ)))) = pk := by
            rw [topPath_fill_signature, setTop_setTop]
            unfold topField
            rw [setTop_self]
            exact hroot
          have hn : topField ((sig.layers 0).path topJ) ≠ 0 := by
            intro he
            rw [he, topPath_fill_signature, setTop_setTop] at hcompletion
            exact hz hcompletion
          have ht := top_lt ((sig.layers 0).path topJ)
          have := cost_searchTop_le_hit answers (digestIndex output) result.foldedTop
            (((fillTopSignature sig 0).layers 0).path topJ) pk searchFuel 1 (topField ((sig.layers 0).path topJ))
            (by omega) (by unfold searchFuel topField at *; omega) hcompletion
          omega



#print axioms expand_cost_le_recovery_field
end OuterExpansionCost
