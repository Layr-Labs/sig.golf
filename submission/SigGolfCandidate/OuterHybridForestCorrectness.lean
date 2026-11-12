import SigGolfCandidate.OuterHybridForestComplete
import SigGolfCandidate.OuterPairModel
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterHybridForestCorrectness
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete (child0 rank0)
open OuterHybridForestComplete OuterForestBudget OuterPairModel
attribute [local irreducible] sharedNodes OuterCoordinateCorrectness.nodes

def forestPrev (answers : Answers) (index : Nat) : Nat → PairRoot
  | 0=>ftsStart
  | p+1=>OuterPairModel.expectedPairRoot answers index p (forestPrev answers index p)

theorem eval_pairCheck (answers : Answers) (index pair : Nat) (b : Bool) (prev : PairRoot) :
    evalWithAnswerFn answers (pairCheck index pair (b, prev)) =
      (b && coordOKb true (2 * pair) (OuterPairModel.firstNodes answers index pair prev) &&
        coordOKb false (2 * pair + 1) (OuterPairModel.secondNodes answers index pair prev), OuterPairModel.expectedPairRoot answers index pair prev) := by
  simp only [pairCheck, evalWithAnswerFn_bind, buildCoord,Bool.false_eq_true,↓reduceIte,buildA_eq,buildSharedCoordinate_result,OuterCoordinateCorrectness.build_result, evalWithAnswerFn_pure]
  rfl

theorem eval_forestCheck_true (answers : Answers) (index : Nat)
    (h : evalWithAnswerFn answers (forestCheck index) = true) :
    (∀ pair, pair < 4 →
      coordOKb true (2 * pair) (OuterPairModel.firstNodes answers index pair (forestPrev answers index pair)) = true ∧
      coordOKb false (2 * pair + 1) (OuterPairModel.secondNodes answers index pair (forestPrev answers index pair)) = true) ∧
    coordOKb false 8 (OuterCoordinateCorrectness.nodes answers index 8 (fun _ => forestPrev answers index 4)) = true := by
  simp only [forestCheck, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_pairCheck,
    buildCoord,Bool.false_eq_true,↓reduceIte,buildA_eq,OuterCoordinateCorrectness.build_result, Bool.and_eq_true, Bool.true_and] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨fun pair hp => ?_, h8⟩
  interval_cases pair
  · exact ⟨h0, h1⟩
  · exact ⟨h2, h3⟩
  · exact ⟨h4, h5⟩
  · exact ⟨h6, h7⟩


#print axioms eval_forestCheck_true
end OuterHybridForestCorrectness
