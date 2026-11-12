import SigGolfCandidate.OuterHybridGlobalComplete
import SigGolfCandidate.OuterHybridForestCorrectness
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterHybridGlobalCorrectness
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete (ftsIndices mem_ftsIndices)
open OuterHybridForestComplete OuterHybridGlobalComplete OuterHybridForestCorrectness

theorem eval_checkFold_true (answers : Answers) :
    ∀ (L : List Nat) (acc : Bool), evalWithAnswerFn answers (L.foldlM checkStep acc) = true →
      acc = true ∧ ∀ index ∈ L, evalWithAnswerFn answers (forestCheck index) = true := by
  intro L
  induction L with
  | nil => intro acc h; simpa using h
  | cons index L ih =>
      intro acc h
      rw [List.foldlM_cons, evalWithAnswerFn_bind] at h
      unfold checkStep at h
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure] at h
      obtain ⟨h1, h2⟩ := ih _ h
      simp only [Bool.and_eq_true] at h1
      refine ⟨h1.1, fun i hi => ?_⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · exact h1.2
      · exact h2 i hi


def ForestsOK (answers : Answers) : Prop := ∀ index,index<2^31 →
  evalWithAnswerFn answers (forestCheck index)=true

theorem eval_check_true (answers : Answers) (h : evalWithAnswerFn answers check=true) : ForestsOK answers := by
  have hall:=(eval_checkFold_true answers ftsIndices true h).2
  intro index hi
  exact hall index (mem_ftsIndices.mpr hi)

#print axioms eval_check_true
end OuterHybridGlobalCorrectness
