import SigGolfCandidate.T3_Secc_WotsStructuralHonest

namespace SigGolfCandidate.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
theorem eval_query_bind {α : Type} (T : Answers) (input : T3.Spec.Domain) (next : T3.Spec.Range input → M α) :
    evalWithAnswerFn T (liftM (T3.Spec.query input) >>= next) = evalWithAnswerFn T (next (T input)) := by
  rw [evalWithAnswerFn_bind]
  rw [show evalWithAnswerFn T (liftM (T3.Spec.query input)) = T input from simulateQ_spec_query T input]
theorem congr_of_queried {α : Type} (T T' : Answers) (program : M α)
    (h : ∀ q ∈ SourceReplay.queried T program, T q = T' q) :
    evalWithAnswerFn T program = evalWithAnswerFn T' program ∧
      SourceReplay.queried T program = SourceReplay.queried T' program := by
  induction program using OracleComp.inductionOn with
  | pure x => exact ⟨rfl, rfl⟩
  | query_bind input next ih =>
      rw [SourceReplay.queried_query_bind] at h
      have h0 : T input = T' input := h input List.mem_cons_self
      have ih' := ih (T input) (fun q hq => h q (List.mem_cons_of_mem _ hq))
      refine ⟨?_, ?_⟩
      · rw [eval_query_bind, eval_query_bind, ← h0]
        exact ih'.1
      · rw [SourceReplay.queried_query_bind, SourceReplay.queried_query_bind, ← h0, ih'.2]
end SigGolfCandidate.T3.Security.Wots.Structural
