import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge101

-- ==== merged from SphincsSecurity_Proof_Base_QueryPauseInvariant ====
section

namespace SphincsSecurity.QueryPause
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Index Memory Result : Type} {spec : OracleSpec Index}
  (stop : Memory → Prop) [DecidablePred stop]
  (step : (input : spec.Domain) → spec.Range input → Memory → Memory)
theorem run_invariant (invariant : Memory → Prop)
    (hstep : ∀ memory, invariant memory → ¬stop memory → ∀ input answer, invariant (step input answer memory))
    (computation : OracleComp spec Result) (memory : Memory) (hinitial : invariant memory)
    (result : Memory × OracleComp spec Result) (hresult : result ∈ support (run stop step computation memory)) :
    invariant result.1 := by
  induction computation using OracleComp.inductionOn generalizing memory result with
  | pure value =>
      rw [run_pure, mem_support_pure_iff] at hresult
      subst result
      exact hinitial
  | query_bind input next ih =>
      rw [run_query_bind] at hresult
      by_cases hs : stop memory
      · rw [if_pos hs, mem_support_pure_iff] at hresult
        subst result
        exact hinitial
      · rw [if_neg hs, mem_support_bind_iff] at hresult
        obtain ⟨answer, _, hresult⟩ := hresult
        exact ih answer (step input answer memory) (hstep memory hinitial hs input answer) result hresult
theorem run_stopped_or_finished (computation : OracleComp spec Result) (memory : Memory)
    (result : Memory × OracleComp spec Result) (hresult : result ∈ support (run stop step computation memory)) :
    stop result.1 ∨ ∃ value, result.2 = pure value := by
  induction computation using OracleComp.inductionOn generalizing memory result with
  | pure value =>
      rw [run_pure, mem_support_pure_iff] at hresult
      subst result
      exact Or.inr ⟨value, rfl⟩
  | query_bind input next ih =>
      rw [run_query_bind] at hresult
      by_cases hs : stop memory
      · rw [if_pos hs, mem_support_pure_iff] at hresult
        subst result
        exact Or.inl hs
      · rw [if_neg hs, mem_support_bind_iff] at hresult
        obtain ⟨answer, _, hresult⟩ := hresult
        exact ih answer (step input answer memory) result hresult
theorem run_simulation_invariant {State : Type} (impl : QueryImpl spec (StateT State PMF))
    (invariant : Memory → State → Prop)
    (hstep : ∀ memory state, invariant memory state → ¬stop memory → ∀ input,
      ∀ result ∈ ((impl input).run state).support, invariant (step input result.1 memory) result.2)
    (computation : OracleComp spec Result) (memory : Memory) (state : State) (hinitial : invariant memory state)
    (result : (Memory × OracleComp spec Result) × State)
    (hresult : result ∈ ((simulateQ impl (run stop step computation memory)).run state).support) :
    invariant result.1.1 result.2 := by
  induction computation using OracleComp.inductionOn generalizing memory state result with
  | pure value =>
      simp only [run_pure, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact hinitial
  | query_bind input next ih =>
      rw [run_query_bind] at hresult
      by_cases hs : stop memory
      · simp only [if_pos hs, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hresult
        subst result
        exact hinitial
      · simp only [if_neg hs, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hresult
        obtain ⟨middle, hmiddle, hresult⟩ := hresult
        exact ih middle.1 (step input middle.1 memory) middle.2
          (hstep memory state hinitial hs input middle hmiddle) result hresult
end SphincsSecurity.QueryPause
end
-- ==== merged from SphincsSecurity_Proof_Base_QueryPauseTrace ====
section

namespace SphincsSecurity.QueryPause
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Index Trace Result : Type} {spec : OracleSpec Index} [Monoid Trace]
  (observation : (input : spec.Domain) → spec.Range input → Trace)
noncomputable def traced (computation : OracleComp spec Result) : OracleComp spec (Result × Trace) :=
  (simulateQ ((QueryImpl.id' spec).withTrace observation) computation).run
theorem traced_pure (result : Result) : traced observation (pure result : OracleComp spec Result) = pure (result, 1) := by
  simp only [traced, simulateQ_pure, WriterT.run_pure]
theorem traced_forget (computation : OracleComp spec Result) : Prod.fst <$> traced observation computation = computation := by
  rw [traced, QueryImpl.fst_map_run_withTrace, simulateQ_id']
theorem traced_query_bind (input : spec.Domain) (next : spec.Range input → OracleComp spec Result) :
    traced observation (liftM (spec.query input) >>= next) =
      liftM (spec.query input) >>= fun answer => (fun tail => (tail.1, observation input answer * tail.2)) <$> traced observation (next answer) := by
  simp only [traced, simulateQ_bind, simulateQ_spec_query, QueryImpl.withTrace_apply,
    WriterT.run_bind, WriterT.run_tell, QueryImpl.id'_apply, WriterT.run_monadLift, bind_map_left, bind_assoc, pure_bind, one_mul, Functor.map_map]
theorem traced_counted (selected : Index → Prop) [DecidablePred selected] (cost : Trace → Nat)
    (hzero : cost 1 = 0)
    (hstep : ∀ input answer trace, cost (observation input answer * trace) = (if selected input then 1 else 0) + cost trace)
    (computation : OracleComp spec Result) :
    (fun result => (result.1, cost result.2)) <$> traced observation computation = QueryCap.counted selected computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [traced_pure, QueryCap.counted_pure, map_pure, hzero]
  | query_bind input next ih =>
      simp only [traced_query_bind, QueryCap.counted_query_bind, map_bind, Functor.map_map, hstep]
      congr 1
      funext answer
      rw [← ih answer]
      simp only [bind_pure_comp, Functor.map_map]
theorem trace_resume (stop : Trace → Prop) [DecidablePred stop]
    (computation : OracleComp spec Result) (history : Trace) :
    (do
      let paused ← run stop (fun input answer memory => memory * observation input answer) computation history
      let tail ← traced observation paused.2
      pure (tail.1, paused.1 * tail.2)) =
        (fun result => (result.1, history * result.2)) <$> traced observation computation := by
  induction computation using OracleComp.inductionOn generalizing history with
  | pure result => simp only [run_pure, traced_pure, pure_bind, map_pure, mul_one]
  | query_bind input next ih =>
      rw [run_query_bind]
      by_cases hs : stop history
      · simp only [if_pos hs, pure_bind, bind_pure_comp]
      · simp only [if_neg hs, bind_assoc, traced_query_bind, map_bind, Functor.map_map, ← mul_assoc]
        exact congrArg (fun continuation => liftM (spec.query input) >>= continuation)
          (funext fun answer => ih answer (history * observation input answer))
end SphincsSecurity.QueryPause
end
-- ==== merged from SphincsSecurity_Proof_Base_QueryTraceInvariant ====
section

namespace SphincsSecurity.QueryPause
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Index Trace Result : Type} {spec : OracleSpec Index} [Monoid Trace]
  (observation : (input : spec.Domain) → spec.Range input → Trace)
theorem traced_simulation_invariant {State : Type} (impl : QueryImpl spec (StateT State PMF))
    (invariant : Trace → State → Prop)
    (hstep : ∀ history state, invariant history state → ∀ input,
      ∀ result ∈ ((impl input).run state).support, invariant (history * observation input result.1) result.2)
    (computation : OracleComp spec Result) (history : Trace) (state : State) (hinitial : invariant history state)
    (result : (Result × Trace) × State)
    (hresult : result ∈ ((simulateQ impl (traced observation computation)).run state).support) :
    invariant (history * result.1.2) result.2 := by
  induction computation using OracleComp.inductionOn generalizing history state result with
  | pure value =>
      simp only [traced_pure, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      simpa only [mul_one] using hinitial
  | query_bind input next ih =>
      simp only [traced_query_bind, simulateQ_bind, simulateQ_map, simulateQ_spec_query, StateT.run_bind, StateT.run_map,
        PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hresult
      obtain ⟨middle, hmiddle, tail, htail, rfl⟩ := hresult
      simpa only [mul_assoc] using ih middle.1 (history * observation input middle.1) middle.2
        (hstep history state hinitial input middle hmiddle) tail htail
theorem traced_counted_forget (selected : Index → Prop) [DecidablePred selected] (computation : OracleComp spec Result) :
    (fun result => (result.1.1, result.2)) <$> QueryCap.counted selected (traced observation computation) =
      QueryCap.counted selected computation := by
  rw [← QueryCap.counted_map, traced_forget]
theorem traced_counted_le (selected : Index → Prop) [DecidablePred selected] (cost : Trace → Nat)
    (hcost : ∀ first second, cost (first * second) = cost first + cost second)
    (hstep : ∀ input answer, (if selected input then 1 else 0) ≤ cost (observation input answer))
    (computation : OracleComp spec Result) (result : (Result × Trace) × Nat)
    (hresult : result ∈ support (QueryCap.counted selected (traced observation computation))) : result.2 ≤ cost result.1.2 := by
  apply QueryCap.counted_writer_simulate_le selected cost hcost ((QueryImpl.id' spec).withTrace observation) _ computation result hresult
  intro input output houtput
  have hquery : (((QueryImpl.id' spec).withTrace observation) input).run =
      (fun answer => (answer, observation input answer)) <$> (liftM (spec.query input) : OracleComp spec _) := by
    simp [QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_tell]
  rw [hquery, QueryCap.counted_map, support_map] at houtput
  obtain ⟨counted, hcounted, rfl⟩ := houtput
  rw [QueryCap.counted_query, support_map] at hcounted
  obtain ⟨answer, _, rfl⟩ := hcounted
  exact hstep input answer
end SphincsSecurity.QueryPause
end
