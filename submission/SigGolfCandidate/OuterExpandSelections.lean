import SigGolfCandidate.OuterExpand
import SigGolfCandidate.Merge097
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterExpandSelections
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.Paired
theorem selections (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (ns5 : List Nat)
    (he : evalWithAnswerFn answers (OuterExpand.expandN message pk sig) = some (output,w,ns5)) :
    sig.policyHints.toNat < 12288 ∧ ∃ counter result c,
      evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 WCT9.digestAttemptLimit) =
        some (counter, output) ∧
      evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig 0) (WCT9.digestIndex output)
        (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4
        (.pair (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1.1
          (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1.2)) = some result ∧
      OuterSigning.policyHintsValid (WCT9.digestIndex output) sig.policyHints result.digits result.lows = true ∧
      w.signature = fillTopSignature sig c ∧ w.digestCounter = counter ∧
      (∀ lay, w.counters lay = result.counters.getD lay.val 0) ∧ w.topHigh = !(result.lows.getD 0 true) := by
  unfold OuterExpand.expandN at he
  simp only [show (fillTopSignature sig 0).rho = sig.rho from rfl,
    show (fillTopSignature sig 0).forest = sig.forest from rfl,
    show (fillTopSignature sig 0).policyHints = sig.policyHints from rfl] at he
  by_cases hh : sig.policyHints.toNat ≥ 12288
  · simp only [hh, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he
  · simp only [hh, if_false, evalWithAnswerFn_bind] at he
    cases hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 WCT9.digestAttemptLimit) with
    | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
    | some found =>
        obtain ⟨counter, N⟩ := found
        simp only [hd, evalWithAnswerFn_bind] at he
        let forest := evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (WCT9.digestIndex N)
          (forestSelectionFromOutput N) (forestWordsFromOutput N) sig.forest)
        cases hr : evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig 0)
          (WCT9.digestIndex N) (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4
          (.pair forest.1.1 forest.1.2)) with
        | none =>
            dsimp only [forest] at hr
            simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
        | some result =>
            dsimp only [forest] at hr
            simp only [hr] at he
            by_cases hp : OuterSigning.policyHintsValid (WCT9.digestIndex N) sig.policyHints result.digits result.lows = true
            · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at he
              by_cases hk : result.root = pk
              · simp only [hk, if_true, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨rfl, rfl, rfl⟩ := he
                exact ⟨by omega, counter, result, 0, (by first | exact hd | rfl), (by first | exact hr | rfl), hp, rfl, rfl, fun _ => rfl, rfl⟩
              · simp only [hk, if_false, evalWithAnswerFn_bind] at he
                cases hc : evalWithAnswerFn answers (WCT9.searchTop (WCT9.digestIndex N) result.foldedTop
                  (((fillTopSignature sig 0).layers 0).path WCT9.topJ) pk WCT9.searchFuel 1) with
                | none => simp only [hc, evalWithAnswerFn_pure, reduceCtorEq] at he
                | some c =>
                    simp only [hc, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                    obtain ⟨rfl, rfl, rfl⟩ := he
                    exact ⟨by omega, counter, result, c, (by first | exact hd | rfl), (by first | exact hr | rfl), hp,
                      fillTopSignature_fillTopSignature sig 0 c, rfl, fun _ => rfl, rfl⟩
            · have hp0 := Bool.eq_false_of_not_eq_true hp
              simp only [hp0, Bool.not_false, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he

#print axioms selections
end OuterExpandSelections
