import SigGolfCandidate.OuterPreparedFacts
import SigGolfCandidate.OuterExpand
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option trace.profiler false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterSourceRecovery
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
attribute [local irreducible] sharedNodes OuterCoordinateCorrectness.nodes OuterForestMoment.forest OuterForestCorrectness.recoverForest

theorem signFromOutput_recovery (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output) = some w) :
    w.signature.rho = rho ∧ ∃ result : RecoveredLayers,
      evalWithAnswerFn answers (recoverHintedLayers w.signature (digestIndex output)
        ((w.signature.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1.1
          (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
            (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1.2)) = some result ∧
      result.root = treeValue (builtTree answers 0 0) 12 0 ∧
      OuterSigning.policyHintsValid (digestIndex output) w.signature.policyHints result.digits result.lows = true ∧
      w.topHigh = !(result.lows.getD 0 true) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (OuterForestMoment.forest index
    (forestSelectionFromOutput output) (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots index)
  unfold OuterSigning.signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (OuterSigning.searchPreparedLayers cache index prepared built.2) with
  | none =>
      dsimp only [index, prepared, built] at hs
      simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some layers =>
      have hf := OuterPreparedFacts.searchPreparedLayers_some answers cache index prepared built.2 layers hs
      dsimp only [index, prepared, built] at hs
      simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
      subst w
      let sig : SigGolfCandidate.Research.SharedForest.Signature := ⟨rho, layers.policyHints, built.1,
        fun lay => piecesSignature lay (layers.pieces.getD lay.val ([], []))⟩
      obtain ⟨folded, nonces, lowerNonces, hr⟩ :=
        OuterPreparedFacts.PreparedSearchFacts.recover_honest hf hcache (digestIndex_lt output) sig rfl (by intro lay; rfl)
      refine ⟨rfl, ⟨folded, _, layers.counters, layers.digits, layers.lows, nonces, lowerNonces⟩, ?_, rfl,
        OuterPreparedFacts.PreparedSearchFacts.hints_valid hf, rfl⟩
      change evalWithAnswerFn answers (recoverHintedLayers sig index ((sig.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1)).1.1
          (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest index (forestSelectionFromOutput output)
            (forestWordsFromOutput output) built.1)).1.2)) = _
      have hforest : (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1)).1 = built.2 :=
        OuterForestCorrectness.forest_honest answers index _ _
      rw [hforest]
      exact hr


#print axioms signFromOutput_recovery
end OuterSourceRecovery
