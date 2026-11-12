import SigGolfCandidate.OuterPreparedFacts
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterSignaturePaths
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness SigGolfCandidate.Research.SharedForest
attribute [local irreducible] OuterForestMoment.forest sharedNodes OuterCoordinateCorrectness.nodes
theorem signFromOutput_path (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output) = some w) (j : Fin (height 0)) :
    (w.signature.layers 0).path j =
      treeValue (builtTree answers 0 0) j.val ((route (digestIndex output) 0).1 / 2 ^ j.val ^^^ 1) := by
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
    change (piecesSignature 0 (layers.pieces.getD (0 : Layer).val ([], []))).path j = _
    have hj : j.val < 12 := j.isLt
    rw [hp, route0_tree _ (digestIndex_lt output)]
    simp [piecesSignature, wotsPieces, wotsTree_top, height, index, hj]

theorem signFromOutput_topPathOK (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (htree : TopTreeOK answers) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output) = some w) :
    TopPathOK w.signature := by
  intro j hj
  have hj11 : j.val ≤ 11 := Nat.le_of_lt_succ j.isLt
  rw [signFromOutput_path answers cache hcache rho counter output w he j]
  exact htree j.val hj hj11 _ (sibling_lt _ _ (route0_leaf_lt _) hj11)


theorem signFromOutput_path_lower (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output) = some w) (lay : Layer)
    (j : Fin (height lay)) :
    (w.signature.layers lay).path j = treeValue (wotsTree answers lay (route (digestIndex output) lay).2) j.val
      ((route (digestIndex output) lay).1 / 2 ^ j.val ^^^ 1) := by
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
    have hp := hf.honest_pieces hcache (digestIndex_lt output) lay
    change (piecesSignature lay (layers.pieces.getD lay.val ([], []))).path j = _
    rw [hp]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, j.isLt, index]


theorem signFromOutput_lowerPathOK (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (hlower : LowerTreesOK answers) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output) = some w) :
    LowerPathOK w.signature := by
  intro lay hl j
  rw [signFromOutput_path_lower answers cache hcache rho counter output w he lay j]
  exact hlower.1 _ (digestIndex_lt output) lay hl j.val j.isLt _
    (sibling_lt_lower lay _ _ (route_leaf_bound _ lay) j.isLt)


#print axioms signFromOutput_topPathOK
#print axioms signFromOutput_lowerPathOK
end OuterSignaturePaths
