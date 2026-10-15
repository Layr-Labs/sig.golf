import SigGolfCandidate.T3.Secc.WotsStructuralHonest

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
structure Variant (labels : CanonGraph.Labels) (T T' : Answers) : Prop where
  agrees : CanonGraph.Agrees T labels
  coin : ∀ n, T (.inl (.inl n)) = T' (.inl (.inl n))
  priv : ∀ c, T (.inr c) = T' (.inr c)
  pub : ∀ x : HashInput, (∀ node : CanonGraph.Node, Extract.posOf x = some node.toPos →
    x = CanonGraph.cell (CanonGraph.secretsOf T) node labels) → T (.inl (.inr x)) = T' (.inl (.inr x))
theorem posOf_honestInput (T : Answers) (p : Extract.Pos) (hp : p.Bounded) :
    Extract.posOf (Extract.honestInput T p) = some p :=
  Extract.posOf_eq hp (Extract.hdrBlock_honestInput T p)
theorem Variant.honest {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') :
    ∀ q, HonestQuery T q → T q = T' q
  | .inl (.inl n), _ => hv.coin n
  | .inr c, _ => hv.priv c
  | .inl (.inr x), Or.inl hnone => hv.pub x (fun node h => by rw [hnone] at h; cases h)
  | .inl (.inr x), Or.inr ⟨p, hp, hx⟩ => hv.pub x (fun node h => by
      rw [hx, posOf_honestInput T p hp] at h
      cases h
      rw [hx]
      exact CanonGraph.honestInput_eq hv.agrees node)
theorem Variant.congr {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') {α : Type}
    {program : M α} (hp : QueriesSat T (HonestQuery T) program) :
    evalWithAnswerFn T program = evalWithAnswerFn T' program ∧
      SourceReplay.queried T program = SourceReplay.queried T' program :=
  congr_of_queried T T' program (fun q hq => hv.honest q (hp q hq))
end SigGolfCandidate.T3.Security.Wots.Structural
