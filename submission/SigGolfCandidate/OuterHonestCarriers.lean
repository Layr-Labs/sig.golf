import SigGolfCandidate.OuterHybridGlobalCorrectness
import SigGolfCandidate.OuterCarrierSerialization
import SigGolfCandidate.OuterSigning
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterHonestCarriers
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete (ftsTreeOK)
open OuterHybridForestComplete OuterHybridForestCorrectness OuterHybridGlobalCorrectness
attribute [local irreducible] sharedNodes OuterCoordinateCorrectness.nodes

theorem forest_pairs (answers : Answers) (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (p : Fin 4) :
    (evalWithAnswerFn answers (OuterForestMoment.forest index selected words)).1.pairs p =
      OuterPairModel.expectedPairOpening answers index p.val (selected.pairs p) (words.first p) (words.second p)
        (OuterHybridForestCorrectness.forestPrev answers index p.val) := by
  have hfour : List.finRange 4 = [0, 1, 2, 3] := by decide
  simp only [OuterForestMoment.forest, hfour, List.foldlM_cons, List.foldlM_nil,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, OuterPairModel.build_result,
    OuterForestMoment.singleton,OuterForestBudget.buildCoord,Bool.false_eq_true,↓reduceIte,OuterCoordinateCorrectness.build_result]
  fin_cases p <;> rfl

theorem forest_singleton_path (answers : Answers) (index : Nat) (selected : ForestSelection)
    (words : ForestWords) (i : Fin 7) :
    (evalWithAnswerFn answers (OuterForestMoment.forest index selected words)).1.singleton.path i =
      authAt (OuterCoordinateCorrectness.nodes answers index 8 (fun _ => OuterHybridForestCorrectness.forestPrev answers index 4)) selected.singleton.val i.val := by
  have hfour : List.finRange 4 = [0, 1, 2, 3] := by decide
  simp only [OuterForestMoment.forest, hfour, List.foldlM_cons, List.foldlM_nil,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, OuterPairModel.build_result,
    OuterForestMoment.singleton,OuterForestBudget.buildCoord,Bool.false_eq_true,↓reduceIte,OuterCoordinateCorrectness.build_result]
  rfl


theorem outerOK_of_coordOKb {coord : Nat} {nodes : Array Digest} (h : coordOKb false coord nodes=true) :
    OuterHybridNodeComplete.outerOK coord nodes := by
  simpa [coordOKb,OuterHybridNodeComplete.outerOK] using (show
    ftsTreeOK coord nodes=true ∧ OuterGroundCore.zeroOk coord (nodes.getD 2 0)=true ∧
      OuterGroundCore.zeroOk coord (nodes.getD 3 0)=true from by simpa [coordOKb] using h).2

theorem forest_pair_zero (answers : Answers) (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (h : evalWithAnswerFn answers (forestCheck index)=true) (p : Fin 4) :
    OuterGroundCore.zeroOk (2*p.val+1) (((evalWithAnswerFn answers (OuterForestMoment.forest index selected words)).1.pairs p).secondPath 6)=true := by
  rw [forest_pairs]
  have hp:=outerOK_of_coordOKb ((eval_forestCheck_true answers index h).1 p.val p.isLt).2
  exact OuterCoordinateCorrectness.outer_path_zero answers index (2*p.val+1) (secondChild (selected.pairs p))
    (nodesPair (OuterPairModel.firstNodes answers index p.val (OuterHybridForestCorrectness.forestPrev answers index p.val))) hp.1 hp.2

theorem forest_singleton_zero (answers : Answers) (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (h : evalWithAnswerFn answers (forestCheck index)=true) :
    OuterGroundCore.zeroOk 8 ((evalWithAnswerFn answers (OuterForestMoment.forest index selected words)).1.singleton.path 6)=true := by
  rw [forest_singleton_path]
  have hp:=outerOK_of_coordOKb (eval_forestCheck_true answers index h).2
  exact OuterCoordinateCorrectness.outer_path_zero answers index 8 selected.singleton (fun _=>OuterHybridForestCorrectness.forestPrev answers index 4) hp.1 hp.2

theorem signFromOutput_forest (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers
      (OuterSigning.signFromOutput cache rho counter output) = some w) :
    w.signature.forest = (evalWithAnswerFn answers (OuterForestMoment.forest (ClaudeWCT.WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output))).1 := by
  let index := ClaudeWCT.WCT9.digestIndex output
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
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
    subst w
    rfl


theorem signFromOutput_roundtrip (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hall : ForestsOK answers)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output)=some w) :
    OuterSignatureCodec.expand (OuterSignatureCodec.compress (ClaudeWCT.W9.T3M.SharedCodec.sigBC w.signature))=
      ClaudeWCT.W9.T3M.SharedCodec.sigBC w.signature := by
  have hf:=signFromOutput_forest answers cache rho counter output w he
  have h:=hall (digestIndex output) (digestIndex_lt output)
  apply OuterCarrierSerialization.compressed_roundtrip
  all_goals rw [hf]
  · exact forest_pair_zero answers _ _ _ h 0
  · exact forest_pair_zero answers _ _ _ h 1
  · exact forest_pair_zero answers _ _ _ h 2
  · exact forest_pair_zero answers _ _ _ h 3
  · exact forest_singleton_zero answers _ _ _ h

#print axioms signFromOutput_roundtrip
#print axioms forest_pair_zero
#print axioms forest_singleton_zero
end OuterHonestCarriers
