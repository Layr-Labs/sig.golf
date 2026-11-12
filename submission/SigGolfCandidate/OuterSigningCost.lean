import SigGolfCandidate.OuterPreparedCost
import SigGolfCandidate.OuterSourceRecovery
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterSigningCost
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
attribute [local irreducible] SigGolfCandidate.T3.SearchCost.cost OuterForestMoment.forest
  OuterForestCorrectness.recoverForest sharedNodes OuterCoordinateCorrectness.nodes
theorem signFromOutput_cost (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    cost answers (OuterSigning.signFromOutput cache rho counter output) =
      cost answers (OuterForestMoment.forest (digestIndex output) (forestSelectionFromOutput output) (forestWordsFromOutput output)) +
      cost answers (prepareRoots (digestIndex output)) +
      cost answers (OuterSigning.searchPreparedLayers cache (digestIndex output)
        (evalWithAnswerFn answers (prepareRoots (digestIndex output)))
        (evalWithAnswerFn answers (OuterForestMoment.forest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output))).2) := by
  simp only [OuterSigning.signFromOutput, cost_bind]
  split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]

theorem signFromOutput_recovery_cost_le (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output) = some w) :
    cost answers (recoverHintedLayers w.signature (digestIndex output) ((w.signature.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1.1
        (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1.2)) ≤
      cost answers (OuterSigning.signFromOutput cache rho counter output) + (13124 + 106485) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (OuterForestMoment.forest index (forestSelectionFromOutput output) (forestWordsFromOutput output))
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
    have hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
        (recoverLayerPair (mainSignature sig) index lay (layers.digits.getD lay.val [])) =
        builtPair answers lay (route index lay).2 := by
      intro lay hl
      apply recoverLayerPair_wotsPieces answers sig index lay hl _ (hf.validDigits lay)
      change piecesSignature lay (layers.pieces.getD lay.val ([], [])) = _
      rw [hf.honest_pieces hcache (digestIndex_lt output)]
    have hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 1
    have hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 2
    have hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 3
    have hc := OuterPreparedCost.recovery_cost_le hf sig ((sig.layers 0).path topJ) rfl hm0 hm1 hm2 hp
    have hforest : (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest index (forestSelectionFromOutput output)
      (forestWordsFromOutput output) built.1)).1 = built.2 := OuterForestCorrectness.forest_honest answers index _ _
    change cost answers (recoverHintedLayers sig index ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest index (forestSelectionFromOutput output)
        (forestWordsFromOutput output) built.1)).1.1
        (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1)).1.2)) ≤ _
    rw [hforest, signFromOutput_cost]
    dsimp only [index, prepared, built] at hc ⊢
    omega


theorem signFromOutput_topSib (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output) = some w) :
    (w.signature.layers 0).path topJ =
      treeValue (builtTree answers 0 0) 11 ((route (digestIndex output) 0).1 / 2 ^ 11 ^^^ 1) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (OuterForestMoment.forest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output))
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
    have hp := hf.honest_pieces hcache (digestIndex_lt output) 0
    change (piecesSignature 0 (layers.pieces.getD (0 : Layer).val ([], []))).path topJ = _
    rw [hp, SigGolfCandidate.Research.SharedForest.route_top_tree _ (digestIndex_lt output)]
    simp [piecesSignature, wotsPieces, topJ, wotsTree_top, height, index]

#print axioms signFromOutput_cost
#print axioms signFromOutput_recovery_cost_le
#print axioms signFromOutput_topSib
end OuterSigningCost
