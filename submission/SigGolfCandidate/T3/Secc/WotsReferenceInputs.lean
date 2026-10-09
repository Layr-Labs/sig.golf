import SigGolfCandidate.T3.Secc.WotsTransportR3
import SigGolfCandidate.T3.Secc.WotsTransportCompletion

namespace SigGolfCandidate.T3.Security.Wots.Ref
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete (hashInputs)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SphincsSecurity.Concrete.hashInputs keygen verifyP expandB buildFts buildTree signPayload
def allQueries {ι α : Type} {spec : OracleSpec ι} (computation : OracleComp spec α) : Set ι :=
  OracleComp.construct (fun _ => (∅ : Set ι)) (fun input _ next => {input} ∪ ⋃ u, next u) computation
theorem allQueries_pure {ι α : Type} {spec : OracleSpec ι} (value : α) :
    allQueries (pure value : OracleComp spec α) = ∅ := rfl
theorem allQueries_query_bind {ι α : Type} {spec : OracleSpec ι} (input : ι)
    (next : spec.Range input → OracleComp spec α) :
    allQueries (liftM (spec.query input) >>= next) = {input} ∪ ⋃ u, allQueries (next u) := by
  simp only [allQueries, OracleComp.construct_query_bind]
theorem mem_allQueries_query_bind {ι α : Type} {spec : OracleSpec ι} {input : ι}
    {next : spec.Range input → OracleComp spec α} {query : ι}
    (h : query ∈ allQueries (liftM (spec.query input) >>= next)) :
    query = input ∨ ∃ u, query ∈ allQueries (next u) := by
  rw [allQueries_query_bind] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_iUnion.mp h)
theorem recorded_mem_allQueries {ι α : Type} {spec : OracleSpec ι} (impl : QueryImpl spec ProbComp)
    (computation : OracleComp spec α) (result : α × List ι)
    (hr : result ∈ support (simulateQ impl (SphincsSecurity.QueryCap.recorded computation))) :
    ∀ query ∈ result.2, query ∈ allQueries computation := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
      rw [SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure, mem_support_pure_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind] at hr
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, mem_support_bind_iff,
        mem_support_pure_iff] at hr
      obtain ⟨answer, -, tail, htail, rfl⟩ := hr
      intro query hq
      rw [allQueries_query_bind]
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inl rfl
      · exact Or.inr (Set.mem_iUnion.mpr ⟨answer, ih answer tail htail query hq⟩)
theorem allQueries_run_subset {ι α : Type} {spec : OracleSpec ι} (selected : ι → Prop) [DecidablePred selected]
    (computation : OracleComp spec α) (budget : Nat) :
    allQueries (SphincsSecurity.QueryCap.run selected computation budget) ⊆ allQueries computation := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value =>
      rw [SphincsSecurity.QueryCap.run_pure, allQueries_pure]
      exact Set.empty_subset _
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.run_query_bind, allQueries_query_bind]
      intro query hq
      by_cases hs : selected input
      · rw [if_pos hs] at hq
        cases budget with
        | zero => exact absurd hq (by rw [allQueries_pure]; exact id)
        | succ remaining =>
            rcases mem_allQueries_query_bind hq with rfl | ⟨u, hu⟩
            · exact Or.inl rfl
            · exact Or.inr (Set.mem_iUnion.mpr ⟨u, ih u remaining hu⟩)
      · rw [if_neg hs] at hq
        rcases mem_allQueries_query_bind hq with rfl | ⟨u, hu⟩
        · exact Or.inl rfl
        · exact Or.inr (Set.mem_iUnion.mpr ⟨u, ih u budget hu⟩)
theorem allQueries_bind {ι α β : Type} {spec : OracleSpec ι} (first : OracleComp spec α)
    (next : α → OracleComp spec β) (query : ι) (h : query ∈ allQueries (first >>= next)) :
    query ∈ allQueries first ∨ ∃ value ∈ support first, query ∈ allQueries (next value) := by
  induction first using OracleComp.inductionOn with
  | pure value =>
      rw [pure_bind] at h
      exact Or.inr ⟨value, by simp, h⟩
  | query_bind input rest ih =>
      rw [bind_assoc] at h
      rcases mem_allQueries_query_bind h with rfl | ⟨u, hu⟩
      · exact Or.inl (by rw [allQueries_query_bind]; exact Or.inl rfl)
      · rcases ih u hu with hl | ⟨value, hv, hq⟩
        · exact Or.inl (by rw [allQueries_query_bind]; exact Or.inr (Set.mem_iUnion.mpr ⟨u, hl⟩))
        · refine Or.inr ⟨value, ?_, hq⟩
          rw [mem_support_bind_iff]
          exact ⟨u, by simp, hv⟩
theorem allQueries_map {ι α β : Type} {spec : OracleSpec ι} (f : α → β) (computation : OracleComp spec α)
    (query : ι) (h : query ∈ allQueries (f <$> computation)) : query ∈ allQueries computation := by
  rw [map_eq_bind_pure_comp] at h
  rcases allQueries_bind _ _ query h with h | ⟨_, _, h⟩
  · exact h
  · exact absurd h (by simp [Function.comp_def, allQueries_pure])
theorem ticks_allQueries (n : Nat) (query : RefWorld.Domain) (h : query ∈ allQueries (ticks n)) :
    query = .inr () := by
  induction n with
  | zero => exact absurd h (by simp [ticks, allQueries_pure])
  | succ n ih =>
      rw [ticks_succ] at h
      rcases mem_allQueries_query_bind h with rfl | ⟨_, hu⟩
      · rfl
      · exact ih hu
theorem hashInputs_bind_left {α β : Type} (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) :
    hashInputs first ⊆ hashInputs (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input rest ih =>
      rw [bind_assoc, SphincsSecurity.Concrete.hashInputs_query_bind, SphincsSecurity.Concrete.hashInputs_query_bind]
      intro x hx
      rw [Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · left
        cases input <;> exact hx
      · right
        rw [Finset.mem_biUnion] at hx ⊢
        obtain ⟨u, -, hu⟩ := hx
        exact ⟨u, Finset.mem_univ _, ih u hu⟩
theorem hashInputs_bind_of_mem {α β : Type} (first : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (value : α) (hv : value ∈ support first) :
    hashInputs (next value) ⊆ hashInputs (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value' =>
      rw [mem_support_pure_iff] at hv
      subst hv
      rw [pure_bind]
  | query_bind input rest ih =>
      rw [mem_support_bind_iff] at hv
      obtain ⟨u, -, hu⟩ := hv
      rw [bind_assoc]
      exact (ih u hu).trans (SphincsSecurity.Concrete.hashInputs_next_subset input (fun x => rest x >>= next) u)
theorem tableRun_query_bind {α : Type} (t : FullGame.FullTable) (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) :
    Derivation.tableRun t ((liftM (T3.Spec.query input) >>= next : M α)) =
      (Derivation.tableHandler t input >>= fun answer => Derivation.tableRun t (next answer)) := by
  unfold Derivation.tableRun
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl
theorem tableRun_bind {α β : Type} (t : FullGame.FullTable) (first : M α) (next : α → M β) :
    Derivation.tableRun t (first >>= next) =
      (Derivation.tableRun t first >>= fun value => Derivation.tableRun t (next value)) := by
  unfold Derivation.tableRun
  rw [simulateQ_bind]
theorem hashInputs_tableRun_sourceRecord {α : Type} (t : FullGame.FullTable) (program : M α)
    (state : LazyPrivate.State) :
    hashInputs (Derivation.tableRun t (FirstHit.sourceRecord program state)) =
      hashInputs (Derivation.tableRun t program) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [FirstHit.sourceRecord_pure]
      unfold Derivation.tableRun
      simp only [simulateQ_pure, SphincsSecurity.Concrete.hashInputs_pure]
  | query_bind input next ih =>
      rw [tableRun_sourceRecord_query_bind, tableRun_query_bind]
      rcases input with input | c
      · rw [tableHandler_world, SphincsSecurity.Concrete.hashInputs_query_bind,
          SphincsSecurity.Concrete.hashInputs_query_bind]
        have h : ∀ u, hashInputs ((fun last => (⟨last.value, ⟨state, .inl input, u⟩ :: last.events, last.state⟩ :
            FirstHit.Recorded α)) <$>
            Derivation.tableRun t (FirstHit.sourceRecord (next u) (FirstHit.advance state (.inl input) u))) =
            hashInputs (Derivation.tableRun t (next u)) := fun u => by rw [hashInputs_map, ih]
        simp only [h]
        cases input <;> rfl
      · rw [tableHandler_private, pure_bind, pure_bind, hashInputs_map, ih]
theorem eval_mem_support_tableRun {α : Type} (T : Answers) (t : FullGame.FullTable) (ht : ∀ c, T (.inr c) = t c)
    (program : M α) (hp : SourceReplay.HashOnly program) :
    evalWithAnswerFn T program ∈ support (Derivation.tableRun t program) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [Derivation.tableRun]
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [tableRun_query_bind, evalWithAnswerFn_bind, eval_query]
      rcases input with (n | x) | c
      · exact False.elim hi
      · rw [tableHandler_world, mem_support_bind_iff]
        exact ⟨T (.inl (.inr x)), by simp, ih _ (hn _)⟩
      · rw [tableHandler_private, pure_bind, ht c]
        exact ht c ▸ ih _ (hn _)
theorem verdict_queries (t : FullGame.FullTable) {β : Type} (program : M β) (hp : PublicVerdict.Only program) :
    ∀ x, (.inl (.inr x) : RefWorld.Domain) ∈ allQueries (simulateQ verdictImpl program) →
      x ∈ hashInputs (Derivation.tableRun t program) := by
  induction program using OracleComp.inductionOn with
  | pure value => intro x hx; exact absurd hx (by simp [allQueries_pure])
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rcases input with (n | y) | c
      · exact False.elim hi
      · intro x hx
        rw [simulateQ_bind, simulateQ_spec_query] at hx
        change (.inl (.inr x) : RefWorld.Domain) ∈ allQueries
          (liftM (RefWorld.query (.inl (.inr y))) >>= fun answer => simulateQ verdictImpl (next answer)) at hx
        rw [tableRun_query_bind, tableHandler_world]
        rcases mem_allQueries_query_bind hx with heq | ⟨u, hu⟩
        · cases heq
          exact SphincsSecurity.Concrete.mem_hashInputs_hash_bind _ _
        · exact SphincsSecurity.Concrete.hashInputs_next_subset (.inr y) _ u (ih u (hn u) x hu)
      · exact False.elim hi
end SigGolfCandidate.T3.Security.Wots.Ref
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload
theorem traceOf_mem {T : Answers} {queries : List RefWorld.Domain} {entry : Entry}
    (h : entry ∈ traceOf T queries) : (.inl (.inr entry.1) : RefWorld.Domain) ∈ queries := by
  unfold traceOf at h
  obtain ⟨query, hq, he⟩ := List.mem_filterMap.mp h
  rcases query with (n | x) | u
  · cases he
  · simp only [Option.some.injEq] at he
    rw [← he]
    exact hq
  · cases he
end SigGolfCandidate.T3.Security.Wots
