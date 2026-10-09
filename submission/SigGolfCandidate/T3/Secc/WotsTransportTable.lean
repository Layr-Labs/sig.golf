import SigGolfCandidate.T3.Secc.WotsTransportR3
import SigGolfCandidate.T3.Secc.WotsTransportShort
import SigGolfCandidate.T3.Secc.WotsTransportCompletion

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload
def GameSplit (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × T3.Cache))
    (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
      (adversary generated.value.1 generated.value.2)) generated.state) ∧
  checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker generated.value.1 interaction.value)
      interaction.state) ∧
  result = ⟨checked.value, generated.events ++ (interaction.events ++ checked.events), checked.state⟩
def CaseABAt (adversary : AdversaryP) (result : FirstHit.Recorded Bool) (answers : Answers) : Prop :=
  ∀ generated interaction checked, GameSplit adversary result generated interaction checked →
    ∀ forgery, interaction.value.1 = some forgery → VerifierWots answers generated.value.1 forgery
namespace Ref
def Good (adversary : AdversaryP) (q : Nat) (result : FirstHit.Recorded Bool) (answers : Answers) : Prop :=
  result.value = true ∧ chargeSum result.events ≤ q ∧ CaseABAt adversary result answers
noncomputable def cut (state : LazyPrivate.State) (F : Answers) : Answers
  | .inl (.inl n) => F (.inl (.inl n))
  | .inl (.inr input) =>
      if input ∈ SeccLaw.publicUniverse ∨ (state.2 input).isSome then F (.inl (.inr input)) else (0 : HashOutput)
  | .inr coordinate => F (.inr coordinate)
theorem cut_shortAgree (state : LazyPrivate.State) (F : Answers) : ShortAgree (cut state F) F := by
  intro query hq
  rcases query with (n | x) | c
  · rfl
  · change (if x ∈ SeccLaw.publicUniverse ∨ (state.2 x).isSome then F (.inl (.inr x)) else (0 : HashOutput)) = _
    rw [if_pos (Or.inl (SeccLaw.mem_publicUniverse x hq))]
  · rfl
theorem cut_cached (state : LazyPrivate.State) (F : Answers) (query : T3.Spec.Domain)
    (h : ∀ x, query = .inl (.inr x) → (state.2 x).isSome) : cut state F query = F query := by
  rcases query with (n | x) | c
  · rfl
  · change (if x ∈ SeccLaw.publicUniverse ∨ (state.2 x).isSome then F (.inl (.inr x)) else (0 : HashOutput)) = _
    rw [if_pos (Or.inr (h x rfl))]
  · rfl
theorem eval_congr_queried {α : Type} (program : M α) (A T : Answers)
    (h : ∀ query ∈ SourceReplay.queried T program, A query = T query) :
    evalWithAnswerFn A program = evalWithAnswerFn T program ∧
      SourceReplay.queried A program = SourceReplay.queried T program := by
  induction program using OracleComp.inductionOn with
  | pure value => exact ⟨rfl, rfl⟩
  | query_bind input next ih =>
      rw [SourceReplay.queried_query_bind] at h
      have hi : A input = T input := h input List.mem_cons_self
      have hn := ih (T input) (fun query hq => h query (List.mem_cons_of_mem _ hq))
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_query, eval_query, hi, hn.1,
        SourceReplay.queried_query_bind, SourceReplay.queried_query_bind, hi, hn.2]
      exact ⟨rfl, rfl⟩
theorem entriesOf_congr (A T : Answers) (queries : List T3.Spec.Domain)
    (h : ∀ query ∈ queries, A query = T query) : entriesOf A queries = entriesOf T queries := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
      have hr := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      rcases query with (n | x) | c
      · simpa [entriesOf] using hr
      · simp only [entriesOf, List.filterMap_cons] at hr ⊢
        rw [h _ List.mem_cons_self, hr]
      · simpa [entriesOf] using hr
theorem calls_append {ι : Type} (selected : ι → Prop) [DecidablePred selected] (left right : List ι) :
    SphincsSecurity.QueryCap.calls selected (left ++ right) =
      SphincsSecurity.QueryCap.calls selected left + SphincsSecurity.QueryCap.calls selected right := by
  simp [SphincsSecurity.QueryCap.calls, List.countP_append]
end Ref
end SigGolfCandidate.T3.Security.Wots
