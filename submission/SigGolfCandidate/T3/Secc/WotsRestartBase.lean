import SigGolfCandidate.T3.Secc.WotsContacts

section
namespace SphincsSecurity.QueryCap
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Index Memory Result : Type} {spec : OracleSpec Index}
  (selected : Index → Prop) [DecidablePred selected]
end SphincsSecurity.QueryCap
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result Memory : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) → result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
  (hsmall : budget < Fintype.card State)
include hcharge hreal hsmall
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
private theorem scaled_expectation_le {Result : Type} (law : PMF Result) (factor : ENNReal)
    (left right : Result → ENNReal) (h : ∀ result ∈ law.support, factor * left result ≤ right result) :
    factor * (∑' result, law result * left result) ≤ ∑' result, law result * right result := by
  rw [← expectation_scale]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ law.support
  · exact mul_le_mul' le_rfl (h result hr)
  · have hz : law result = 0 := not_not.mp hr
    simp only [hz, zero_mul, le_refl]
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Checkpoint Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
  (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
  (observed : Fin n → State → Option State)
  (marked : State → Checkpoint × (Fin n → State → Option State) → Prop)
theorem realCheckpointRun_mark_probability :
    Pr[fun result => marked result.1 result.2.1 | realCheckpointRun auxiliary before after observed] =
      Pr[fun result => marked result.1 result.2 | realRun auxiliary before observed] := by
  have h := congrArg (fun law : PMF (State × (Checkpoint × (Fin n → State → Option State))) =>
    Pr[fun result => marked result.1 result.2 | law]) (realCheckpointRun_before auxiliary before after observed)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h
theorem realCheckpointRun_contact_charge (budget : Nat)
    (hmarked : ∀ endpoint middle, marked endpoint middle → ¬Contact middle.2 endpoint)
    (hbudget : ∀ endpoint, ∀ middle ∈ (lazyRun (auxiliary endpoint) (before endpoint) observed).support,
      marked endpoint middle → ∀ result ∈ (lazyRun (auxiliary endpoint)
        (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2).support, queryCount result.2 ≤ budget) :
    (1 - (budget : ENNReal) / Fintype.card State) * ((Fintype.card State : ENNReal) *
      Pr[fun result => marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 |
        realCheckpointRun auxiliary before after observed]) ≤
      ∑' result, realCheckpointRun auxiliary before after observed result *
        (((queryCount result.2.1.2 + 2 * result.2.2.1.2 : Nat) : ENNReal) * if marked result.1 result.2.1 then 1 else 0) := by
  rw [show Pr[fun result => marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 |
      realCheckpointRun auxiliary before after observed] =
      (∑' result, realCheckpointRun auxiliary before after observed result *
        if marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 then 1 else 0) by
          simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]]
  rw [realCheckpointRun_density, realCheckpointRun_expectation, ← mul_assoc]
  apply scaled_expectation_le
  intro endpoint _
  apply scaled_expectation_le
  intro middle hmiddle
  by_cases hm : marked endpoint middle
  · simp only [hm, true_and, if_true, mul_one]
    simpa only [mul_assoc] using run_contact_charge_transfer (auxiliary endpoint) (after endpoint middle) middle.2 endpoint
      (hmarked endpoint middle hm) budget (hbudget endpoint middle hmiddle hm)
  · simp only [hm, false_and, if_false, mul_zero, tsum_zero, le_refl]
theorem realCheckpointRun_contact_le_mark (budget : Nat)
    (hmarked : ∀ endpoint middle, marked endpoint middle → ¬Contact middle.2 endpoint)
    (hbudget : ∀ endpoint, ∀ middle ∈ (lazyRun (auxiliary endpoint) (before endpoint) observed).support,
      marked endpoint middle → ∀ result ∈ (lazyRun (auxiliary endpoint)
        (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2).support, queryCount result.2 ≤ budget)
    (hcost : ∀ result ∈ (realCheckpointRun auxiliary before after observed).support,
      marked result.1 result.2.1 → queryCount result.2.1.2 + result.2.2.1.2 ≤ budget) :
    (1 - (budget : ENNReal) / Fintype.card State) * ((Fintype.card State : ENNReal) *
      Pr[fun result => marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 |
        realCheckpointRun auxiliary before after observed]) ≤
      (2 * budget : Nat) * Pr[fun result => marked result.1 result.2 | realRun auxiliary before observed] := by
  apply (realCheckpointRun_contact_charge auxiliary before after observed marked budget hmarked hbudget).trans
  calc
    _ ≤ ∑' result, realCheckpointRun auxiliary before after observed result *
        (((2 * budget : Nat) : ENNReal) * if marked result.1 result.2.1 then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ (realCheckpointRun auxiliary before after observed).support
      · apply mul_le_mul' le_rfl
        by_cases hm : marked result.1 result.2.1
        · simp only [if_pos hm, mul_one]
          have hc := hcost result hr hm
          exact_mod_cast (show queryCount result.2.1.2 + 2 * result.2.2.1.2 ≤ 2 * budget by omega)
        · simp only [if_neg hm, mul_zero, le_refl]
      · have hz : realCheckpointRun auxiliary before after observed result = 0 := not_not.mp hr
        simp only [hz, zero_mul, le_refl]
    _ = _ := by
      rw [expectation_scale, ← realCheckpointRun_mark_probability auxiliary before after observed marked]
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Checkpoint Result Output : Type}
omit [Fintype State] [Nonempty State] in
theorem observedRun_bind (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (before : OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : Checkpoint → OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (before >>= after) observed =
      (observedRun auxiliary tables before observed).bind (fun middle => observedRun auxiliary tables (after middle.1) middle.2) := by
  simp only [observedRun, simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind]
omit [Fintype State] [Nonempty State] in
theorem checkpointObservedRun_project (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (before : OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : Checkpoint → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (project : Checkpoint → Result → Output) :
    (checkpointObservedRun auxiliary tables before (fun middle => after middle.1) observed).map
      (fun result => (project result.1.1 result.2.1.1, result.2.2)) =
    observedRun auxiliary tables (do let middle ← before; let result ← after middle; pure (project middle result)) observed := by
  simp only [checkpointObservedRun, PMF.map_bind, PMF.map_comp, Function.comp_def,
    observedRun_bind, bind_pure_comp, observedRun_map]
  apply congrArg (observedRun auxiliary tables before observed).bind
  funext middle
  rw [← observedRun_map auxiliary tables (QueryCap.counted IsPrefixQuery (after middle.1))
    (fun result => project middle.1 result.1) middle.2]
  rw [← Functor.map_map, QueryCap.counted_forget, observedRun_map]
theorem realCheckpointRun_project (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (project : State → Checkpoint → Result → Output) :
    (realCheckpointRun auxiliary before (fun endpoint middle => after endpoint middle.1) observed).map
      (fun result => (result.1, project result.1 result.2.1.1 result.2.2.1.1, result.2.2.2)) =
    realRun auxiliary (fun endpoint => do
      let middle ← before endpoint
      let result ← after endpoint middle
      pure (project endpoint middle result)) observed := by
  simp only [realCheckpointRun, realRun, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg (EndpointPreimageDensity.real (completeTables observed) evaluate).bind
  funext pair
  have h := congrArg (fun law => law.map (fun result => (pair.2, result)))
    (checkpointObservedRun_project (auxiliary pair.2) pair.1 (before pair.2) (after pair.2) observed (project pair.2))
  simpa only [PMF.map_comp, Function.comp_def] using h
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl lazyImpl record realRun idealRun lazyRun TwoEdgeEvent Contact queryCount)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace PrefixGame
def entryOf : (query : RefWorld.Domain) → RefWorld.Range query → List Entry
  | .inl (.inr input), answer => [(input, (answer : HashOutput))]
  | .inl (.inl _), _ => []
  | .inr _, _ => []
def stepTrace (query : RefWorld.Domain) (answer : RefWorld.Range query) (memory : List Entry) : List Entry :=
  memory ++ entryOf query answer
def refAnswer (T : Answers) : (query : RefWorld.Domain) → RefWorld.Range query
  | .inl query => T (.inl query)
  | .inr _ => ()
theorem traceOf_cons (T : Answers) (query : RefWorld.Domain) (qs : List RefWorld.Domain) :
    traceOf T (query :: qs) = entryOf query (refAnswer T query) ++ traceOf T qs := by
  rcases query with (n | input) | u <;> rfl
theorem entryOf_refImpl (T : Answers) (query : RefWorld.Domain) (answer : RefWorld.Range query)
    (h : answer ∈ support (refImpl T query)) : entryOf query answer = entryOf query (refAnswer T query) := by
  rcases query with (n | input) | u
  · rfl
  · simp only [refImpl, mem_support_pure_iff] at h
    subst h
    rfl
  · rfl
theorem entryOf_length_le (query : RefWorld.Domain) (answer : RefWorld.Range query) :
    (entryOf query answer).length ≤ 1 := by
  rcases query with (n | input) | u <;> simp [entryOf]
variable {β : Type}
noncomputable def pausedFull (stop : List Entry → Prop) (G : OracleComp RefWorld β) (memory : List Entry) :
    OracleComp RefWorld (List Entry × (β × List RefWorld.Domain)) := do
  let paused ← SphincsSecurity.QueryPause.run stop stepTrace (SphincsSecurity.QueryCap.recorded G) memory
  let result ← paused.2
  pure (paused.1, result)
theorem pausedFull_snd (stop : List Entry → Prop) (G : OracleComp RefWorld β) (memory : List Entry) :
    Prod.snd <$> pausedFull stop G memory = SphincsSecurity.QueryCap.recorded G := by
  unfold pausedFull
  simp only [map_bind, map_pure]
  conv_rhs => rw [← SphincsSecurity.QueryPause.resume stop stepTrace (SphincsSecurity.QueryCap.recorded G) memory]
  congr 1
  funext paused
  simp only [bind_pure]
theorem run_map {Index Memory α γ : Type} {spec : OracleSpec Index} (stop : Memory → Prop) [DecidablePred stop]
    (step : (input : spec.Domain) → spec.Range input → Memory → Memory) (f : α → γ)
    (computation : OracleComp spec α) (memory : Memory) :
    SphincsSecurity.QueryPause.run stop step (f <$> computation) memory =
      (fun paused => (paused.1, f <$> paused.2)) <$> SphincsSecurity.QueryPause.run stop step computation memory := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure value =>
      simp only [map_pure, SphincsSecurity.QueryPause.run_pure]
  | query_bind input next ih =>
      rw [map_bind, SphincsSecurity.QueryPause.run_query_bind, SphincsSecurity.QueryPause.run_query_bind]
      by_cases hs : stop memory
      · simp only [if_pos hs, map_pure, map_bind]
      · simp only [if_neg hs, map_bind, ih]
theorem pausedFull_query_bind (stop : List Entry → Prop) (input : RefWorld.Domain)
    (next : RefWorld.Range input → OracleComp RefWorld β) (memory : List Entry) :
    pausedFull stop (liftM (RefWorld.query input) >>= next) memory =
      if stop memory then
        (fun result => (memory, result)) <$> SphincsSecurity.QueryCap.recorded (liftM (RefWorld.query input) >>= next)
      else liftM (RefWorld.query input) >>= fun answer =>
        (fun paused => (paused.1, (paused.2.1, input :: paused.2.2))) <$>
          pausedFull stop (next answer) (stepTrace input answer memory) := by
  unfold pausedFull
  rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryPause.run_query_bind]
  by_cases hs : stop memory
  · rw [if_pos hs, if_pos hs, pure_bind, ← SphincsSecurity.QueryCap.recorded_query_bind]
    simp only [bind_pure_comp]
  · rw [if_neg hs, if_neg hs, bind_assoc]
    congr 1
    funext answer
    have hmap : (SphincsSecurity.QueryCap.recorded (next answer) >>= fun result =>
        (pure (result.1, input :: result.2) : OracleComp RefWorld _)) =
        (fun result => (result.1, input :: result.2)) <$> SphincsSecurity.QueryCap.recorded (next answer) := by
      simp only [bind_pure_comp]
    rw [hmap, run_map]
    simp only [map_bind, bind_map_left, map_pure]
theorem paused_structure (T : Answers) (stop : List Entry → Prop) (G : OracleComp RefWorld β) :
    ∀ (memory : List Entry) (result : List Entry × (β × List RefWorld.Domain)),
      result ∈ support (simulateQ (refImpl T) (pausedFull stop G memory)) →
        memory.length ≤ result.1.length ∧
        result.1 = (memory ++ traceOf T result.2.2).take result.1.length ∧
        (∀ j, memory.length ≤ j → j < result.1.length → ¬stop ((memory ++ traceOf T result.2.2).take j)) ∧
        (stop result.1 ∨ result.1 = memory ++ traceOf T result.2.2) := by
  induction G using OracleComp.inductionOn with
  | pure value =>
      intro memory result hr
      simp only [pausedFull, SphincsSecurity.QueryCap.recorded_pure, SphincsSecurity.QueryPause.run_pure, pure_bind,
        simulateQ_pure, mem_support_pure_iff] at hr
      subst hr
      refine ⟨le_refl _, ?_, fun j h1 h2 => by simp only at h2; omega, Or.inr ?_⟩
      · simp
      · show memory = memory ++ traceOf T []
        rw [show traceOf T [] = [] from rfl, List.append_nil]
  | query_bind input next ih =>
      intro memory result hr
      rw [pausedFull_query_bind] at hr
      by_cases hs : stop memory
      · rw [if_pos hs] at hr
        rw [simulateQ_map, support_map] at hr
        obtain ⟨tail, -, rfl⟩ := hr
        refine ⟨le_refl _, ?_, fun j h1 h2 => by simp only at h2; omega, Or.inl hs⟩
        show memory = List.take memory.length (memory ++ _)
        rw [List.take_left' rfl]
      · rw [if_neg hs, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at hr
        obtain ⟨answer, hanswer, hr⟩ := hr
        rw [simulateQ_map, support_map] at hr
        obtain ⟨paused, hpaused, rfl⟩ := hr
        obtain ⟨h1, h2, h3, h4⟩ := ih answer (stepTrace input answer memory) paused hpaused
        have hentry := entryOf_refImpl T input answer hanswer
        have htrace : stepTrace input answer memory ++ traceOf T paused.2.2 =
            memory ++ traceOf T (input :: paused.2.2) := by
          rw [traceOf_cons, stepTrace, hentry, List.append_assoc]
        rw [htrace] at h2 h3 h4
        have hlen : (stepTrace input answer memory).length ≤ memory.length + 1 := by
          have := entryOf_length_le input answer
          simp only [stepTrace, List.length_append]
          omega
        have hlen' : memory.length ≤ (stepTrace input answer memory).length := by
          simp only [stepTrace, List.length_append]
          omega
        refine ⟨le_trans hlen' h1, h2, ?_, h4⟩
        intro j hj1 hj2
        by_cases hj : (stepTrace input answer memory).length ≤ j
        · exact h3 j hj hj2
        · have hjm : j = memory.length := by omega
          rw [hjm, List.take_left' rfl]
          exact hs
variable {adversary : AdversaryP}
theorem lazyRun_bind {d : Nat} {α γ : Type} (first : OracleComp (SeedSpec d) α) (next : α → OracleComp (SeedSpec d) γ)
    (observed : Fin d → Digest → Option Digest) :
    lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (first >>= next) observed =
      (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl first observed).bind fun r =>
        lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (next r.1) r.2 := by
  simp only [lazyRun, simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind]
def RowsInv (a : ChainAddr) {d : Nat} (memory : List Entry) (observed : Fin d → Digest → Option Digest) : Prop :=
  ∀ (i : Fin d) (v w : Digest), observed i v = some w ↔ ∃ answer, (chainRow a i v, answer) ∈ memory ∧ low answer = w
theorem rowsInv_nil (a : ChainAddr) (d : Nat) : RowsInv a (d := d) [] (fun _ _ => none) := by
  intro i v w
  simp
end PrefixGame
end SigGolfCandidate.T3.Security.Wots
end
