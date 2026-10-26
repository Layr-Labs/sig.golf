import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge042
import SigGolfCandidate.Merge050
import SigGolfCandidate.Merge054
import SigGolfCandidate.Merge055
import SigGolfCandidate.Merge066
import SigGolfCandidate.Merge067
import SigGolfCandidate.Merge068
import SigGolfCandidate.Merge070

-- ==== merged from T3_Secc_WotsStructural ====
section

section
namespace SigGolfCandidate.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete.UniformTableObservation (lazyImpl lazyRun fixedImpl TableSpec)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def refObs : (q : RefWorld.Domain) → RefWorld.Range q → FreeMonoid Entry
  | .inl (.inr x), answer => FreeMonoid.of (x, answer)
  | .inl (.inl _), _ => 1
  | .inr _, _ => 1
theorem traceOf_cons_hash (T : Answers) (x : HashInput) (rest : List RefWorld.Domain) :
    traceOf T ((.inl (.inr x) : RefWorld.Domain) :: rest) = (x, T (.inl (.inr x))) :: traceOf T rest := rfl
theorem traceOf_cons_coin (T : Answers) (n : Nat) (rest : List RefWorld.Domain) :
    traceOf T ((.inl (.inl n) : RefWorld.Domain) :: rest) = traceOf T rest := rfl
theorem traceOf_cons_tick (T : Answers) (u : Unit) (rest : List RefWorld.Domain) :
    traceOf T ((.inr u : RefWorld.Domain) :: rest) = traceOf T rest := rfl
theorem recorded_traced {α : Type} (T : Answers) (C : OracleComp RefWorld α) :
    (fun run => (run.1, traceOf T run.2)) <$> simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded C) =
      (fun result => (result.1, result.2.toList)) <$>
        simulateQ (refImpl T) (SphincsSecurity.QueryPause.traced refObs C) := by
  induction C using OracleComp.inductionOn with
  | pure x =>
      simp only [SphincsSecurity.QueryCap.recorded_pure, SphincsSecurity.QueryPause.traced_pure,
        simulateQ_pure, map_pure]
      rfl
  | query_bind q next ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryPause.traced_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_map, map_bind, simulateQ_pure]
      rcases q with (n | x) | u
      · refine bind_congr fun answer => ?_
        have h := ih answer
        simp only [map_pure, bind_pure_comp, Functor.map_map, traceOf_cons_coin, refObs, one_mul] at h ⊢
        exact h
      · simp only [refImpl, pure_bind]
        have h := congrArg (Functor.map (fun p : α × List Entry => (p.1, (x, T (.inl (.inr x))) :: p.2)))
          (ih (T (.inl (.inr x))))
        simp only [map_pure, bind_pure_comp, Functor.map_map, traceOf_cons_hash, refObs, FreeMonoid.toList_mul,
          FreeMonoid.toList_of, List.singleton_append] at h ⊢
        exact h
      · refine bind_congr fun answer => ?_
        have h := ih answer
        simp only [map_pure, bind_pure_comp, Functor.map_map, traceOf_cons_tick, refObs, one_mul] at h ⊢
        exact h
section Lazy
variable (Str : Finset HashInput)
abbrev LazySpec := RefWorld + TableSpec Str HashOutput
noncomputable def strTranslate : QueryImpl RefWorld (OracleComp (LazySpec Str))
  | .inl (.inl n) => liftM ((LazySpec Str).query (.inl (.inl (.inl n))))
  | .inl (.inr x) => if h : x ∈ Str then liftM ((LazySpec Str).query (.inr ⟨x, h⟩))
      else liftM ((LazySpec Str).query (.inl (.inl (.inr x))))
  | .inr u => liftM ((LazySpec Str).query (.inl (.inr u)))
noncomputable def lazyAux (T0 : Answers) : QueryImpl RefWorld SPMF := fun q => 𝒮[refImpl T0 q]
theorem uniform_complete :
    (liftM (PMF.uniformOfFintype (Str → HashOutput)) : SPMF (Str → HashOutput)) =
      complete (fun _ : Str => (Finset.univ : Finset HashOutput)) := by
  rw [complete_of_nonempty _ (fun _ => Finset.univ_nonempty), SphincsSecurity.Concrete.uniformTable_univ]
variable (T : (Str → HashOutput) → Answers)
  (hstr : ∀ ρ x (hx : x ∈ Str), T ρ (.inl (.inr x)) = ρ ⟨x, hx⟩)
  (hout : ∀ ρ x, x ∉ Str → T ρ (.inl (.inr x)) = T (fun _ => 0) (.inl (.inr x)))
include hstr hout
theorem fixed_translate (ρ : Str → HashOutput) (q : RefWorld.Domain) :
    simulateQ (fixedImpl (lazyAux (T (fun _ => 0))) ρ) (strTranslate Str q) = 𝒮[refImpl (T ρ) q] := by
  rcases q with (n | x) | u
  · simp only [strTranslate, simulateQ_spec_query, fixedImpl, lazyAux]
    rfl
  · by_cases hx : x ∈ Str
    · simp only [strTranslate, dif_pos hx, simulateQ_spec_query, fixedImpl, refImpl, evalSPMF_pure, hstr ρ x hx]
    · simp only [strTranslate, dif_neg hx, simulateQ_spec_query, fixedImpl, lazyAux, refImpl, evalSPMF_pure,
        hout ρ x hx]
  · simp only [strTranslate, simulateQ_spec_query, fixedImpl, lazyAux]
    rfl
theorem fixed_run {α : Type} (ρ : Str → HashOutput) (C : OracleComp RefWorld α) :
    simulateQ (fixedImpl (lazyAux (T (fun _ => 0))) ρ) (simulateQ (strTranslate Str) C) =
      𝒮[simulateQ (refImpl (T ρ)) C] := by
  induction C using OracleComp.inductionOn with
  | pure x => simp only [simulateQ_pure, evalSPMF_pure]
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalSPMF_bind, ih, fixed_translate Str T hstr hout]
theorem uniform_run {α : Type} (C : OracleComp RefWorld α) :
    ((liftM (PMF.uniformOfFintype (Str → HashOutput)) : SPMF (Str → HashOutput)) >>= fun ρ =>
        𝒮[simulateQ (refImpl (T ρ)) C]) =
      Prod.fst <$> lazyRun (lazyAux (T (fun _ => 0))) (simulateQ (strTranslate Str) C) (fun _ => Finset.univ) := by
  rw [uniform_complete Str]
  have h := SphincsSecurity.Concrete.UniformTableObservation.run_marginal (lazyAux (T (fun _ => 0)))
    (simulateQ (strTranslate Str) C) (fun _ : Str => (Finset.univ : Finset HashOutput)) (fun _ => Finset.univ_nonempty)
  simpa only [fixed_run Str T hstr hout] using h
end Lazy
section Potential
variable (Str : Finset HashInput) (T0 : Answers)
def TraceConsistent (trace : FreeMonoid Entry) (allowed : Str → Finset HashOutput) : Prop :=
  (∀ row : Str, ∀ answer, (row.val, answer) ∈ trace.toList → allowed row = {answer}) ∧
    ∀ row : Str, (∀ answer, (row.val, answer) ∉ trace.toList) → allowed row = Finset.univ
theorem traceConsistent_one : TraceConsistent Str 1 (fun _ => Finset.univ) := by
  constructor
  · intro row answer h
    simp at h
  · intro row _
    rfl
theorem TraceConsistent.outside {Str : Finset HashInput} {trace : FreeMonoid Entry}
    {allowed : Str → Finset HashOutput} (h : TraceConsistent Str trace allowed) (input : HashInput)
    (hi : input ∉ Str) (output : HashOutput) :
    TraceConsistent Str (trace * FreeMonoid.of (input, output)) allowed := by
  constructor
  · intro row answer hentry
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton,
      Prod.mk.injEq] at hentry
    rcases hentry with hentry | ⟨heq, _⟩
    · exact h.1 row answer hentry
    · exact False.elim (hi (heq ▸ row.property))
  · intro row hfresh
    apply h.2 row
    intro answer hentry
    exact hfresh answer (by
      simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append]
      exact Or.inl hentry)
theorem TraceConsistent.disclose {Str : Finset HashInput} {trace : FreeMonoid Entry}
    {allowed : Str → Finset HashOutput} (h : TraceConsistent Str trace allowed) (row : Str) (output : HashOutput)
    (houtput : output ∈ allowed row) :
    TraceConsistent Str (trace * FreeMonoid.of (row.val, output))
      (SphincsSecurity.Concrete.discloseTableValue allowed row output) := by
  constructor
  · intro other answer hentry
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton,
      Prod.mk.injEq] at hentry
    rcases hentry with hentry | ⟨heq, hans⟩
    · by_cases heq : other = row
      · subst other
        have heq : output = answer := Finset.mem_singleton.mp ((h.1 row answer hentry) ▸ houtput)
        simp only [SphincsSecurity.Concrete.discloseTableValue, Function.update_self, heq]
      · rw [SphincsSecurity.Concrete.discloseTableValue, Function.update_of_ne heq]
        exact h.1 other answer hentry
    · have heq : other = row := Subtype.ext heq
      subst other
      rw [hans]
      exact Function.update_self row {output} allowed
  · intro other hfresh
    have heq : other ≠ row := by
      intro heq
      subst other
      exact hfresh output (by simp)
    rw [SphincsSecurity.Concrete.discloseTableValue, Function.update_of_ne heq]
    apply h.2 other
    intro answer hentry
    exact hfresh answer (by
      simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append]
      exact Or.inl hentry)
theorem TraceConsistent.cached_reply {Str : Finset HashInput} {trace : FreeMonoid Entry}
    {allowed : Str → Finset HashOutput} (h : TraceConsistent Str trace allowed) (row : Str)
    (previous output : HashOutput) (hp : (row.val, previous) ∈ trace.toList) (ho : cell (allowed row) output ≠ 0) :
    output = previous := by
  rw [h.1 row previous hp, cell_apply] at ho
  by_contra hn
  simp only [Finset.mem_singleton, hn, if_false, ne_eq, not_true_eq_false] at ho
theorem TraceConsistent.new_reply_le {Str : Finset HashInput} {trace : FreeMonoid Entry}
    {allowed : Str → Finset HashOutput} (h : TraceConsistent Str trace allowed) (row : Str)
    (event : HashOutput → Prop) :
    Pr[fun output => event output ∧ (row.val, output) ∉ trace.toList | cell (allowed row)] ≤
      Pr[event | cell Finset.univ] := by
  by_cases hfresh : ∀ output, (row.val, output) ∉ trace.toList
  · rw [h.2 row hfresh]
    exact probEvent_mono (fun _ _ he => he.1)
  · obtain ⟨previous, hp⟩ := not_forall.mp hfresh
    have hp : (row.val, previous) ∈ trace.toList := not_not.mp hp
    have hz : Pr[fun output => event output ∧ (row.val, output) ∉ trace.toList | cell (allowed row)] = 0 := by
      apply probEvent_eq_zero
      intro output ho he
      have heq := h.cached_reply row previous output hp ((SPMF.mem_support_iff _ _).mp ho)
      exact he.2 (heq.symm ▸ hp)
    rw [hz]
    exact bot_le
noncomputable def lazyWorld : QueryImpl RefWorld (StateT (Str → Finset HashOutput) SPMF) :=
  (lazyImpl (lazyAux T0)) ∘ₛ (strTranslate Str)
theorem lazyRun_eq_simulate {α : Type} (C : OracleComp RefWorld α) (allowed : Str → Finset HashOutput) :
    lazyRun (lazyAux T0) (simulateQ (strTranslate Str) C) allowed = (simulateQ (lazyWorld Str T0) C).run allowed := by
  rw [lazyRun, lazyWorld, QueryImpl.simulateQ_compose]
theorem lazyWorld_hash_mem (x : HashInput) (hx : x ∈ Str) (allowed : Str → Finset HashOutput) :
    (lazyWorld Str T0 (.inl (.inr x))).run allowed =
      (fun answer => (answer, SphincsSecurity.Concrete.discloseTableValue allowed ⟨x, hx⟩ answer)) <$>
        cell (allowed ⟨x, hx⟩) := by
  simp only [lazyWorld, QueryImpl.apply_compose, strTranslate, dif_pos hx, simulateQ_spec_query, lazyImpl,
    StateT.run_mk]
  rfl
theorem lazyWorld_hash_out (x : HashInput) (hx : x ∉ Str) (allowed : Str → Finset HashOutput) :
    (lazyWorld Str T0 (.inl (.inr x))).run allowed =
      (fun answer => (answer, allowed)) <$> lazyAux T0 (.inl (.inr x)) := by
  simp only [lazyWorld, QueryImpl.apply_compose, strTranslate, dif_neg hx, simulateQ_spec_query, lazyImpl,
    StateT.run_mk]
  rfl
theorem lazyWorld_coin (n : Nat) (allowed : Str → Finset HashOutput) :
    (lazyWorld Str T0 (.inl (.inl n))).run allowed = (fun answer => (answer, allowed)) <$> lazyAux T0 (.inl (.inl n)) := by
  simp only [lazyWorld, QueryImpl.apply_compose, strTranslate, simulateQ_spec_query, lazyImpl, StateT.run_mk]
  rfl
theorem lazyWorld_tick (u : Unit) (allowed : Str → Finset HashOutput) :
    (lazyWorld Str T0 (.inr u)).run allowed = (fun answer => (answer, allowed)) <$> lazyAux T0 (.inr u) := by
  simp only [lazyWorld, QueryImpl.apply_compose, strTranslate, simulateQ_spec_query, lazyImpl, StateT.run_mk]
  rfl
theorem map_pair_nonzero {A B : Type} (p : SPMF A) (f : A → B) (r : A × B) (hr : ((fun a => (a, f a)) <$> p) r ≠ 0) :
    r.2 = f r.1 ∧ p r.1 ≠ 0 := by
  rw [← bind_pure_comp] at hr
  obtain ⟨a, ha, heq⟩ := (SphincsSecurity.Concrete.RetainedObservation.bind_nonzero _ _ _).mp hr
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
  subst r
  exact ⟨rfl, ha⟩
theorem lazyWorld_traceConsistent (allowed : Str → Finset HashOutput) (trace : FreeMonoid Entry)
    (h : TraceConsistent Str trace allowed) (q : RefWorld.Domain)
    (result : RefWorld.Range q × (Str → Finset HashOutput)) (hr : (lazyWorld Str T0 q).run allowed result ≠ 0) :
    TraceConsistent Str (trace * refObs q result.1) result.2 := by
  rcases q with (n | x) | u
  · rw [lazyWorld_coin] at hr
    obtain ⟨h2, -⟩ := map_pair_nonzero _ (fun _ => allowed) result hr
    rw [h2]
    simpa only [refObs, mul_one] using h
  · by_cases hx : x ∈ Str
    · rw [lazyWorld_hash_mem Str T0 x hx] at hr
      obtain ⟨h2, h1⟩ := map_pair_nonzero _ _ result hr
      rw [h2]
      have hin : result.1 ∈ allowed ⟨x, hx⟩ := by
        by_contra hn
        rw [cell_apply, if_neg hn] at h1
        exact h1 rfl
      exact h.disclose ⟨x, hx⟩ result.1 hin
    · rw [lazyWorld_hash_out Str T0 x hx] at hr
      obtain ⟨h2, -⟩ := map_pair_nonzero _ (fun _ => allowed) result hr
      rw [h2]
      exact h.outside x hx result.1
  · rw [lazyWorld_tick] at hr
    obtain ⟨h2, -⟩ := map_pair_nonzero _ (fun _ => allowed) result hr
    rw [h2]
    simpa only [refObs, mul_one] using h
variable (Hit : HashInput → HashOutput → Prop) (Charged : HashInput → Prop)
def Seen (trace : FreeMonoid Entry) : Prop := ∃ e ∈ trace.toList, Hit e.1 e.2
noncomputable def chargedCount (trace : FreeMonoid Entry) : Nat :=
  (trace.toList.filter fun e => decide (Charged e.1)).length
noncomputable def queryCharge : RefWorld.Domain → Nat
  | .inl (.inr x) => if Charged x then 1 else 0
  | _ => 0
theorem seen_one : ¬Seen Hit 1 := by simp [Seen]
theorem seen_mul_of (trace : FreeMonoid Entry) (e : Entry) :
    Seen Hit (trace * FreeMonoid.of e) ↔ Seen Hit trace ∨ Hit e.1 e.2 := by
  simp only [Seen, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton, or_and_right,
    exists_or, exists_eq_left]
theorem chargedCount_one : chargedCount Charged 1 = 0 := rfl
theorem chargedCount_step (q : RefWorld.Domain) (answer : RefWorld.Range q) (tail : FreeMonoid Entry) :
    chargedCount Charged (refObs q answer * tail) = queryCharge Charged q + chargedCount Charged tail := by
  rcases q with (n | x) | u
  · simp [refObs, queryCharge, chargedCount]
  · by_cases hc : Charged x
    · simp [refObs, queryCharge, chargedCount, hc, Nat.add_comm]
    · simp [refObs, queryCharge, chargedCount, hc]
  · simp [refObs, queryCharge, chargedCount]
variable (rate : ENNReal) (hhit : ∀ x a, Hit x a → x ∈ Str)
  (hkernel : ∀ x, x ∈ Str → Pr[Hit x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤
    rate * (if Charged x then 1 else 0 : ENNReal))
include hhit hkernel in
theorem lazy_step_le (history : FreeMonoid Entry) (allowed : Str → Finset HashOutput)
    (hc : TraceConsistent Str history allowed) (q : RefWorld.Domain) :
    (∑' result, Pr[= result | (lazyWorld Str T0 q).run allowed] *
      (if Seen Hit (history * refObs q result.1) then 1 else 0 : ENNReal)) ≤
      (if Seen Hit history then 1 else 0 : ENNReal) + rate * (queryCharge Charged q : ENNReal) := by
  by_cases hs : Seen Hit history
  · simp only [if_pos hs]
    refine le_add_right (le_trans (ENNReal.tsum_le_tsum fun result => mul_le_of_le_one_right' ?_) tsum_probOutput_le_one)
    split <;> simp
  · simp only [if_neg hs, zero_add, mul_ite, mul_one, mul_zero]
    rw [← probEvent_eq_tsum_ite]
    rcases q with (n | x) | u
    · have hz : Pr[fun result => Seen Hit (history * refObs (.inl (.inl n)) result.1) |
          (lazyWorld Str T0 (.inl (.inl n))).run allowed] = 0 :=
        probEvent_eq_zero fun result _ h => hs (by simpa only [refObs, mul_one] using h)
      rw [hz]
      exact bot_le
    · by_cases hx : x ∈ Str
      · rw [lazyWorld_hash_mem Str T0 x hx, probEvent_map]
        calc Pr[(fun result => Seen Hit (history * refObs (.inl (.inr x)) result.1)) ∘
              (fun answer => (answer, SphincsSecurity.Concrete.discloseTableValue allowed ⟨x, hx⟩ answer)) |
              cell (allowed ⟨x, hx⟩)]
            ≤ Pr[fun answer => Hit x answer ∧ ((⟨x, hx⟩ : Str).val, answer) ∉ history.toList |
              cell (allowed ⟨x, hx⟩)] := by
              apply probEvent_mono
              intro answer _ h
              change Seen Hit (history * FreeMonoid.of ((x, answer) : Entry)) at h
              rcases (seen_mul_of Hit history (x, answer)).mp h with h | h
              · exact absurd h hs
              · exact ⟨h, fun hmem => hs ⟨(x, answer), hmem, h⟩⟩
          _ ≤ Pr[Hit x | cell Finset.univ] := hc.new_reply_le ⟨x, hx⟩ (Hit x)
          _ ≤ rate * (queryCharge Charged (.inl (.inr x)) : ENNReal) := by
              have hk := hkernel x hx
              rw [cell, dif_pos Finset.univ_nonempty]
              change Pr[Hit x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤ _
              refine hk.trans (le_of_eq ?_)
              simp only [queryCharge]
              split <;> simp
      · have hz : Pr[fun result => Seen Hit (history * refObs (.inl (.inr x)) result.1) |
            (lazyWorld Str T0 (.inl (.inr x))).run allowed] = 0 := by
          apply probEvent_eq_zero
          intro result _ h
          change Seen Hit (history * FreeMonoid.of ((x, result.1) : Entry)) at h
          rcases (seen_mul_of Hit history (x, result.1)).mp h with h | h
          · exact hs h
          · exact hx (hhit x result.1 h)
        rw [hz]
        exact bot_le
    · have hz : Pr[fun result => Seen Hit (history * refObs (.inr u) result.1) |
          (lazyWorld Str T0 (.inr u)).run allowed] = 0 :=
        probEvent_eq_zero fun result _ h => hs (by simpa only [refObs, mul_one] using h)
      rw [hz]
      exact bot_le
end Potential
end SigGolfCandidate.T3.Security.Wots.Structural
namespace SigGolfCandidate.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableObservation (lazyImpl lazyRun fixedImpl TableSpec)
open SphincsSecurity.Concrete.UniformTableCompletion
attribute [local instance] Classical.propDecidable
theorem lazyAux_neverFail (T0 : Answers) (q : RefWorld.Domain) : NeverFail (lazyAux T0 q) :=
  ⟨probFailure_eq_zero (mx := refImpl T0 q)⟩
section Main
variable (Str : Finset HashInput) (T : (Str → HashOutput) → Answers)
  (hstr : ∀ ρ x (hx : x ∈ Str), T ρ (.inl (.inr x)) = ρ ⟨x, hx⟩)
  (hout : ∀ ρ x, x ∉ Str → T ρ (.inl (.inr x)) = T (fun _ => 0) (.inl (.inr x)))
  (Hit : HashInput → HashOutput → Prop) (Charged : HashInput → Prop) (rate : ENNReal)
  (hhit : ∀ x a, Hit x a → x ∈ Str)
  (hkernel : ∀ x, x ∈ Str → Pr[Hit x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤
    rate * (if Charged x then 1 else 0 : ENNReal))
include hstr hout hhit hkernel
theorem lazy_seen_le {α : Type} (C : OracleComp RefWorld α) :
    Pr[fun r => Seen Hit r.2 | (liftM (PMF.uniformOfFintype (Str → HashOutput)) : SPMF (Str → HashOutput)) >>= fun ρ =>
        𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs C)]] ≤
      rate * ∑' r, Pr[= r | (liftM (PMF.uniformOfFintype (Str → HashOutput)) : SPMF (Str → HashOutput)) >>= fun ρ =>
        𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs C)]] *
          (chargedCount Charged r.2 : ENNReal) := by
  rw [uniform_run Str T hstr hout, lazyRun_eq_simulate, probEvent_map, tsum_probOutput_map_mul]
  have hpot := SphincsSecurity.QueryPause.traced_spmf_potential_le refObs (lazyWorld Str (T fun _ => 0))
    (fun history allowed => TraceConsistent Str history allowed ∧ ∀ row, (allowed row).Nonempty)
    (fun history allowed hi q result hr =>
      ⟨lazyWorld_traceConsistent Str (T fun _ => 0) allowed history hi.1 q result hr,
        SphincsSecurity.Concrete.UniformTableObservation.lazyRun_nonempty (lazyAux (T fun _ => 0))
          (strTranslate Str q) allowed hi.2 result hr⟩)
    (fun computation history allowed hi => by
      rw [← lazyRun_eq_simulate]
      exact probFailure_eq_zero' (SphincsSecurity.Concrete.UniformTableObservation.lazyRun_neverFail
        (lazyAux (T fun _ => 0)) (lazyAux_neverFail _) _ allowed hi.2))
    (fun history _ => if Seen Hit history then 1 else 0) rate (chargedCount Charged) (queryCharge Charged)
    (chargedCount_one Charged) (chargedCount_step Charged)
    (fun history allowed hi q => lazy_step_le Str (T fun _ => 0) Hit Charged rate hhit hkernel history allowed hi.1 q)
    C 1 (fun _ => Finset.univ) ⟨traceConsistent_one Str, fun _ => Finset.univ_nonempty⟩
  simp only [one_mul, if_neg (seen_one Hit), zero_add] at hpot
  rw [probEvent_eq_tsum_ite]
  simpa only [Function.comp_apply, mul_ite, mul_one, mul_zero] using hpot
end Main
end SigGolfCandidate.T3.Security.Wots.Structural
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Structural
open CanonGraph (Node Labels Secrets OtherHalves cell programmed canonInputs privateEquiv)
section Fixed
variable (V : Finset HashInput) (hU : canonInputs ⊆ V) (s : Secrets) (o : OtherHalves) (labels : Labels)
theorem card_digest : (Fintype.card SphincsSecurity.Digest : ℝ≥0∞) = 2 ^ 128 := by
  simp [SphincsSecurity.digestBits]
  norm_num
theorem mem_traceOf {T : Answers} {qs : List RefWorld.Domain} {e : Entry} (he : e ∈ traceOf T qs) :
    e.2 = T (.inl (.inr e.1)) := by
  unfold traceOf at he
  obtain ⟨query, -, hq⟩ := List.mem_filterMap.mp he
  rcases query with (n | x) | u
  · simp at hq
  · simp only [Option.some.injEq] at hq
    rw [← hq]
  · simp at hq
end Fixed
theorem uniform_split_bind {Index Cell R : Type} [Fintype Index] [Fintype Cell] [DecidableEq Index]
    [DecidableEq Cell] (embed : Index → Cell) (hinj : Function.Injective embed) (g : (Cell → HashOutput) → SPMF R) :
    ((liftM (PMF.uniformOfFintype (Cell → HashOutput)) : SPMF (Cell → HashOutput)) >>= g) =
      ((liftM (PMF.uniformOfFintype (SphincsSecurity.Concrete.UniformTableSplit.Outside embed → HashOutput)) :
          SPMF _) >>= fun rest =>
        (liftM (PMF.uniformOfFintype (Index → HashOutput)) : SPMF (Index → HashOutput)) >>= fun ρ =>
          g (SphincsSecurity.Concrete.UniformTableSplit.join embed hinj ρ rest)) := by
  rw [SphincsSecurity.Concrete.UniformTableSplit.uniform_join embed hinj, ← PMF.monad_bind_eq_bind, liftM_bind]
  simp only [← PMF.monad_map_eq_map, liftM_map, bind_assoc, bind_map_left]
  exact SphincsSecurity.Concrete.RetainedObservation.bind_comm _ _ _
end Structural
theorem liftM_pmf_apply {α : Type} (p : ProbComp α) (x : α) : (liftM p : PMF α) x = Pr[= x | 𝒮[p]] := by
  rw [← PMF.probOutput_eq_apply]
  rfl
theorem probEvent_liftM_pmf {α : Type} (p : ProbComp α) (E : α → Prop) :
    Pr[E | (liftM p : PMF α)] = Pr[E | 𝒮[p]] := rfl
theorem probEvent_liftM_pmf' {α : Type} (p : ProbComp α) (E : α → Prop) :
    Pr[E | (liftM p : PMF α)] = Pr[E | p] := rfl
theorem mem_support_liftM_pmf {α : Type} (p : ProbComp α) (x : α) (hx : x ∈ support p) :
    x ∈ (liftM p : PMF α).support := by
  rw [PMF.mem_support_iff, ← PMF.probOutput_eq_apply]
  change Pr[= x | p] ≠ 0
  exact (mem_support_iff _ _).mp hx
end SigGolfCandidate.T3.Security.Wots
end
end
-- ==== merged from T3_Secc_WotsStructuralFinal ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsTransportCount ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB buildFts buildTree signPayload GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsTransportCount : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsTransportCount : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable def refCount (cls : Answers → T3.Spec.Domain → Prop) (sample : RefSample) : Nat :=
  (sample.trace.filter fun e => decide (cls sample.answers (.inl (.inr e.1)))).length
def ShortCongruent (cls : Answers → T3.Spec.Domain → Prop) : Prop :=
  ∀ A T, Ref.ShortAgree A T → ∀ input, cls A input ↔ cls T input
namespace Ref
noncomputable def cappedCount {ι : Type} (selected : ι → Prop) [DecidablePred selected] (cls : ι → Prop) :
    Nat → List ι → Nat
  | _, [] => 0
  | budget, input :: rest =>
      if selected input then
        match budget with
        | 0 => 0
        | remaining + 1 => (if cls input then 1 else 0) + cappedCount selected cls remaining rest
      else cappedCount selected cls budget rest
section Capped
variable {ι : Type} (selected : ι → Prop) [DecidablePred selected] (cls : ι → Prop)
theorem cappedCount_cons_def (budget : Nat) (input : ι) (rest : List ι) :
    cappedCount selected cls budget (input :: rest) =
      if selected input then
        (match budget with
        | 0 => 0
        | remaining + 1 => (if cls input then 1 else 0) + cappedCount selected cls remaining rest)
      else cappedCount selected cls budget rest := rfl
theorem cappedCount_zero (inputs : List ι) : cappedCount selected cls 0 inputs = 0 := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      rw [cappedCount_cons_def]
      by_cases hs : selected input
      · rw [if_pos hs]
      · rw [if_neg hs]
        exact ih
theorem cappedCount_cons (budget : Nat) (input : ι) (rest : List ι) :
    cappedCount selected cls budget (input :: rest) =
      (if selected input ∧ 0 < budget ∧ cls input then 1 else 0) +
        cappedCount selected cls (budget - if selected input then 1 else 0) rest := by
  rw [cappedCount_cons_def]
  by_cases hs : selected input
  · rw [if_pos hs, if_pos hs]
    cases budget with
    | zero =>
        rw [if_neg (show ¬(selected input ∧ 0 < 0 ∧ cls input) from fun h => absurd h.2.1 (Nat.lt_irrefl 0)),
          Nat.zero_sub, cappedCount_zero]
    | succ remaining =>
        show (if cls input then 1 else 0) + cappedCount selected cls remaining rest = _
        rw [Nat.add_sub_cancel]
        by_cases hc : cls input
        · rw [if_pos hc, if_pos (show selected input ∧ 0 < remaining + 1 ∧ cls input from ⟨hs, Nat.succ_pos _, hc⟩)]
        · rw [if_neg hc, if_neg (show ¬(selected input ∧ 0 < remaining + 1 ∧ cls input) from fun h => hc h.2.2)]
  · rw [if_neg hs, if_neg hs, if_neg (show ¬(selected input ∧ 0 < budget ∧ cls input) from fun h => hs h.1),
      Nat.sub_zero, Nat.zero_add]
theorem cappedCount_append (budget : Nat) (left right : List ι) :
    cappedCount selected cls budget (left ++ right) =
      cappedCount selected cls budget left +
        cappedCount selected cls (budget - SphincsSecurity.QueryCap.calls selected left) right := by
  induction left generalizing budget with
  | nil => simp [cappedCount, SphincsSecurity.QueryCap.calls_nil]
  | cons input rest ih =>
      rw [List.cons_append, cappedCount_cons, cappedCount_cons, ih, SphincsSecurity.QueryCap.calls_cons,
        Nat.sub_sub, Nat.add_assoc]
end Capped
theorem expectedValue_const_add {α : Type} (mx : ProbComp α) (c : ℝ≥0∞) (g : α → ℝ≥0∞) :
    expectedValue mx (fun x => c + g x) = c + expectedValue mx g := by
  rw [expectedValue_add, expectedValue_const probFailure_eq_zero]
theorem expectedValue_zero {α : Type} (mx : ProbComp α) : expectedValue mx (fun _ => (0 : ℝ≥0∞)) = 0 := by
  simp [expectedValue_def]
theorem cap_cappedCount {ι β : Type} {spec : OracleSpec ι} (selected : ι → Prop) [DecidablePred selected]
    (cls : ι → Prop) (impl : QueryImpl spec ProbComp) (computation : OracleComp spec β) (budget : Nat) :
    expectedValue (simulateQ impl (SphincsSecurity.QueryCap.recorded
        (SphincsSecurity.QueryCap.run selected computation budget)))
        (fun result => (cappedCount selected cls budget result.2 : ℝ≥0∞)) =
      expectedValue (simulateQ impl (SphincsSecurity.QueryCap.recorded computation))
        (fun result => (cappedCount selected cls budget result.2 : ℝ≥0∞)) := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value =>
      simp only [SphincsSecurity.QueryCap.run_pure, SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure,
        expectedValue_pure, cappedCount]
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.run_query_bind]
      by_cases hs : selected input
      · rw [if_pos hs]
        cases budget with
        | zero =>
            simp only [cappedCount_zero, Nat.cast_zero, expectedValue_zero]
        | succ remaining =>
            rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryCap.recorded_query_bind]
            simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, expectedValue_bind, expectedValue_pure]
            congr 1
            funext answer
            simp only [cappedCount_cons_def, if_pos hs, Nat.cast_add]
            rw [expectedValue_const_add, expectedValue_const_add, ih answer remaining]
      · rw [if_neg hs, SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryCap.recorded_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, expectedValue_bind, expectedValue_pure]
        congr 1
        funext answer
        simp only [cappedCount_cons_def, if_neg hs]
        exact ih answer budget
def RefClass (C : T3.Spec.Domain → Prop) : RefWorld.Domain → Prop
  | .inl (.inr input) => C (.inl (.inr input))
  | _ => False
noncomputable abbrev refCharge (C : T3.Spec.Domain → Prop) (budget : Nat) (queries : List RefWorld.Domain) : Nat :=
  cappedCount RefCharged (RefClass C) budget queries
section Steps
variable (C : T3.Spec.Domain → Prop)
theorem refCharge_coin (budget n : Nat) (rest : List RefWorld.Domain) :
    refCharge C budget (.inl (.inl n) :: rest) = refCharge C budget rest := by
  rw [refCharge, cappedCount_cons_def, if_neg (show ¬RefCharged (.inl (.inl n)) from id)]
theorem refCharge_hash (budget : Nat) (input : HashInput) (rest : List RefWorld.Domain) :
    refCharge C budget (.inl (.inr input) :: rest) =
      (if 0 < budget ∧ C (.inl (.inr input)) then 1 else 0) + refCharge C (budget - 1) rest := by
  rw [refCharge, cappedCount_cons, if_pos (show RefCharged (.inl (.inr input)) from trivial)]
  congr 1
  by_cases h : 0 < budget ∧ C (.inl (.inr input))
  · rw [if_pos h, if_pos (show RefCharged (.inl (.inr input)) ∧ 0 < budget ∧ RefClass C (.inl (.inr input)) from
      ⟨trivial, h⟩)]
  · rw [if_neg h, if_neg (show ¬(RefCharged (.inl (.inr input)) ∧ 0 < budget ∧ RefClass C (.inl (.inr input))) from
      fun h' => h h'.2)]
theorem refCharge_tick (budget : Nat) (rest : List RefWorld.Domain) :
    refCharge C budget (.inr () :: rest) = refCharge C (budget - 1) rest := by
  rw [refCharge, cappedCount_cons, if_pos (show RefCharged (.inr ()) from trivial),
    if_neg (show ¬(RefCharged (.inr ()) ∧ 0 < budget ∧ RefClass C (.inr ())) from fun h => h.2.2), Nat.zero_add]
theorem refCharge_replicate_tick (budget n : Nat) :
    refCharge C budget (List.replicate n (.inr () : RefWorld.Domain)) = 0 := by
  induction n generalizing budget with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, refCharge_tick, ih]
theorem refCharge_append (budget : Nat) (left right : List RefWorld.Domain) :
    refCharge C budget (left ++ right) =
      refCharge C budget left + refCharge C (budget - SphincsSecurity.QueryCap.calls RefCharged left) right :=
  cappedCount_append _ _ budget left right
theorem calls_coin (n : Nat) (rest : List RefWorld.Domain) :
    SphincsSecurity.QueryCap.calls RefCharged (.inl (.inl n) :: rest) =
      SphincsSecurity.QueryCap.calls RefCharged rest := by
  rw [SphincsSecurity.QueryCap.calls_cons, if_neg (show ¬RefCharged (.inl (.inl n)) from id), Nat.zero_add]
theorem calls_hash (input : HashInput) (rest : List RefWorld.Domain) :
    SphincsSecurity.QueryCap.calls RefCharged (.inl (.inr input) :: rest) =
      1 + SphincsSecurity.QueryCap.calls RefCharged rest := by
  rw [SphincsSecurity.QueryCap.calls_cons, if_pos (show RefCharged (.inl (.inr input)) from trivial)]
theorem calls_tick (rest : List RefWorld.Domain) :
    SphincsSecurity.QueryCap.calls RefCharged (.inr () :: rest) = 1 + SphincsSecurity.QueryCap.calls RefCharged rest := by
  rw [SphincsSecurity.QueryCap.calls_cons, if_pos (show RefCharged (.inr ()) from trivial)]
theorem queryCharge_coin (n : Nat) : FullGame.queryCharge (.inl (.inl n)) = 0 := by
  simp [FullGame.queryCharge, Derivation.charged]
theorem queryCharge_public (input : HashInput) : FullGame.queryCharge (.inl (.inr input)) = 1 := by
  simp [FullGame.queryCharge, Derivation.charged]
theorem queryCharge_private (coordinate : Coordinate) : FullGame.queryCharge (.inr coordinate) = 1 := by
  simp [FullGame.queryCharge, Derivation.charged]
theorem classCharge_zero (events : List FirstHit.QueryEvent) : SeccLaw.classCharge C 0 events = 0 := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      simp only [SeccLaw.classCharge]
      split_ifs with h1 h2
      · have h0 : FullGame.queryCharge event.input = 0 := by omega
        rw [h0, Nat.zero_sub, ih]
      · rw [Nat.zero_sub, ih]
      · rfl
theorem classCharge_cons (budget : Nat) (event : FirstHit.QueryEvent) (rest : List FirstHit.QueryEvent) :
    SeccLaw.classCharge C budget (event :: rest) =
      (if FullGame.queryCharge event.input ≤ budget ∧ C event.input then FullGame.queryCharge event.input else 0) +
        SeccLaw.classCharge C (budget - FullGame.queryCharge event.input) rest := by
  simp only [SeccLaw.classCharge]
  by_cases h1 : FullGame.queryCharge event.input ≤ budget
  · rw [if_pos h1]
    by_cases h2 : C event.input
    · rw [if_pos h2, if_pos ⟨h1, h2⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.2)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1), Nat.sub_eq_zero_of_le (by omega), classCharge_zero]
theorem classCharge_coin (budget n : Nat) (event : FirstHit.QueryEvent) (he : event.input = .inl (.inl n))
    (rest : List FirstHit.QueryEvent) :
    SeccLaw.classCharge C budget (event :: rest) = SeccLaw.classCharge C budget rest := by
  rw [classCharge_cons, he, queryCharge_coin, Nat.sub_zero]
  split_ifs <;> exact Nat.zero_add _
theorem classCharge_public (budget : Nat) (input : HashInput) (event : FirstHit.QueryEvent)
    (he : event.input = .inl (.inr input)) (rest : List FirstHit.QueryEvent) :
    SeccLaw.classCharge C budget (event :: rest) =
      (if 0 < budget ∧ C (.inl (.inr input)) then 1 else 0) + SeccLaw.classCharge C (budget - 1) rest := by
  rw [classCharge_cons, he, queryCharge_public]
  rfl
theorem classCharge_coin_mk (budget n : Nat) (before : LazyPrivate.State) (answer : T3.Spec.Range (.inl (.inl n)))
    (rest : List FirstHit.QueryEvent) :
    SeccLaw.classCharge C budget (⟨before, .inl (.inl n), answer⟩ :: rest) = SeccLaw.classCharge C budget rest :=
  classCharge_coin C budget n _ rfl rest
theorem classCharge_public_mk (budget : Nat) (input : HashInput) (before : LazyPrivate.State)
    (answer : T3.Spec.Range (.inl (.inr input))) (rest : List FirstHit.QueryEvent) :
    SeccLaw.classCharge C budget (⟨before, .inl (.inr input), answer⟩ :: rest) =
      (if 0 < budget ∧ C (.inl (.inr input)) then 1 else 0) + SeccLaw.classCharge C (budget - 1) rest :=
  classCharge_public C budget input _ rfl rest
theorem classCharge_append (budget : Nat) (left right : List FirstHit.QueryEvent) :
    SeccLaw.classCharge C budget (left ++ right) =
      SeccLaw.classCharge C budget left + SeccLaw.classCharge C (budget - chargeSum left) right := by
  induction left generalizing budget with
  | nil => simp [SeccLaw.classCharge]
  | cons event rest ih =>
      rw [List.cons_append, classCharge_cons, classCharge_cons, ih, chargeSum_cons, Nat.sub_sub, Nat.add_assoc]
theorem refCharge_embed_le (budget : Nat) (events : List FirstHit.QueryEvent) :
    refCharge C budget (events.map fun event => embed event.input) ≤ SeccLaw.classCharge C budget events := by
  induction events generalizing budget with
  | nil => exact le_rfl
  | cons event rest ih =>
      rw [List.map_cons]
      rcases hinput : event.input with (n | x) | c
      · rw [embed, refCharge_coin, classCharge_coin C budget n event hinput]
        exact ih budget
      · rw [embed, refCharge_hash, classCharge_public C budget x event hinput]
        exact Nat.add_le_add_left (ih _) _
      · rw [embed, refCharge_tick, classCharge_cons, hinput, queryCharge_private]
        exact le_add_left (ih _)
end Steps
theorem traceOf_coin (T : Answers) (n : Nat) (rest : List RefWorld.Domain) :
    traceOf T (.inl (.inl n) :: rest) = traceOf T rest := rfl
theorem traceOf_hash (T : Answers) (input : HashInput) (rest : List RefWorld.Domain) :
    traceOf T (.inl (.inr input) :: rest) = (input, T (.inl (.inr input))) :: traceOf T rest := rfl
theorem traceOf_tick (T : Answers) (rest : List RefWorld.Domain) : traceOf T (.inr () :: rest) = traceOf T rest := rfl
theorem traceOf_length_le (T : Answers) (queries : List RefWorld.Domain) :
    (traceOf T queries).length ≤ SphincsSecurity.QueryCap.calls RefCharged queries := by
  induction queries with
  | nil => exact le_rfl
  | cons query rest ih =>
      rcases query with (n | x) | ⟨⟩
      · rw [traceOf_coin, calls_coin]; exact ih
      · rw [traceOf_hash, calls_hash, List.length_cons]; omega
      · rw [traceOf_tick, calls_tick]; omega
theorem refCharge_eq_filter (T : Answers) (C : T3.Spec.Domain → Prop) (queries : List RefWorld.Domain)
    (budget : Nat) (h : SphincsSecurity.QueryCap.calls RefCharged queries ≤ budget) :
    refCharge C budget queries = ((traceOf T queries).filter fun e => decide (C (.inl (.inr e.1)))).length := by
  induction queries generalizing budget with
  | nil => rfl
  | cons query rest ih =>
      rcases query with (n | x) | ⟨⟩
      · rw [calls_coin] at h
        rw [refCharge_coin, traceOf_coin]
        exact ih budget h
      · rw [calls_hash] at h
        rw [refCharge_hash, traceOf_hash, List.filter_cons, ih (budget - 1) (by omega)]
        by_cases hc : C (.inl (.inr x))
        · rw [if_pos ⟨by omega, hc⟩, if_pos (decide_eq_true hc), List.length_cons]
          omega
        · rw [if_neg (fun h' => hc h'.2), if_neg (by simpa using hc), Nat.zero_add]
      · rw [calls_tick] at h
        rw [refCharge_tick, traceOf_tick]
        exact ih (budget - 1) (by omega)
end Ref
theorem pmf_tsum_eq_expectedValue {α : Type} (p : PMF α) (g : α → ℝ≥0∞) :
    ∑' x, p x * g x = expectedValue p g := by
  rw [expectedValue_def]
  congr 1
  funext x
  rw [PMF.probOutput_eq_apply]
theorem expectedValue_liftM {α : Type} (mx : ProbComp α) (g : α → ℝ≥0∞) :
    expectedValue (liftM mx : PMF α) g = expectedValue mx g := by
  rw [expectedValue_def, expectedValue_def]
  congr 1
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsStructuralFinal ====
section

section
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
/-! (r3-lean-nonsec) The legacy non-paired structural route that used to live here was removed: nothing outside this
file used it (FinalFam uses `PairedStructural`/`PairedReference`). Only the helpers below are still used. -/
/-- The two 128-bit halves of an output, swapped. -/
noncomputable def swapHalves : SphincsSecurity.HashOutput ≃ SphincsSecurity.HashOutput :=
  ((SphincsSecurity.splitHashOutputEquiv 128 (by decide)).trans (Equiv.prodComm _ _)).trans
    (SphincsSecurity.splitHashOutputEquiv 128 (by decide)).symm
theorem truncate_swapHalves (a : SphincsSecurity.HashOutput) : SphincsSecurity.truncateHash (swapHalves a) = a.extractLsb' 128 128 := by
  have h := Equiv.apply_symm_apply (SphincsSecurity.splitHashOutputEquiv 128 (by decide))
    ((Equiv.prodComm _ _) (SphincsSecurity.splitHashOutputEquiv 128 (by decide) a))
  exact congrArg Prod.fst h
/-- The high half of a uniform output is uniform (nested FTS r1-1: the top FTS values are high halves). -/
theorem prob_high_eq (target : SphincsSecurity.Digest) :
    Pr[fun answer : HashOutput => answer.extractLsb' 128 128 = target | PMF.uniformOfFintype HashOutput] =
      (Fintype.card SphincsSecurity.Digest : ℝ≥0∞)⁻¹ := by
  rw [← SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq target]
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, PMF.uniformOfFintype_apply]
  conv_rhs => rw [← swapHalves.tsum_eq]
  simp only [truncate_swapHalves]
  rfl
/-- The used half of a uniform output is uniform at every position. -/
theorem prob_proj_eq (p : Extract.Pos) (target : SphincsSecurity.Digest) :
    Pr[fun answer : HashOutput => p.proj answer = target | PMF.uniformOfFintype HashOutput] =
      (Fintype.card SphincsSecurity.Digest : ℝ≥0∞)⁻¹ := by
  rw [Extract.Pos.proj_eq]
  cases p.high
  · simp only [Bool.false_eq_true, ite_false]
    exact SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq target
  · simp only [ite_true]
    exact prob_high_eq target
def OtherInput (answers : Answers) (input : HashInput) : Prop :=
  ∃ position, Extract.posOf input = some position ∧ position.Bounded ∧ WotsExtract.PosSource position ∧
    StructuralClass answers input position
def OtherQuery (answers : Answers) : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inl (.inr input) => OtherInput answers input
  | _ => False
noncomputable def otherCount (sample : RefSample) : Nat :=
  (sample.trace.filter fun e => decide (OtherQuery sample.answers (.inl (.inr e.1)))).length
namespace Structural
open ClaudeWCT.W9.T3.Security.CanonGraph (Node)
theorem exists_node_of_posSource {p : Extract.Pos} (h : WotsExtract.PosSource p) : ∃ node : Node, node.toPos = p := by
  apply CanonGraph.exists_toPos
  cases p with
  | chain lay tree leaf i step =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      have hh : 2 ^ height lay ≤ 2 ^ 12 :=
        Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
      have hw : 2 ^ width lay i ≤ 2 ^ 3 :=
        Nat.pow_le_pow_right (by decide) (Extract.width_le lay i)
      have hc := Extract.chainCount_le lay
      exact ⟨Extract.tree_lt_of_treeBits h1, by omega, by omega, by omega⟩
  | leaf lay tree leaf => exact h
  | node lay tree level nd => exact h
  | forest index => exact h
  | wctChain index coord child t step => exact h
  | wctLeaf index coord child => exact h
  | wctNode index coord level nd => exact h
end Structural
end ClaudeWCT.W9.T3.Security.Wots
end
/-! Top-nonce layer (r3-lean-nonsec): selected representatives and rejected-trial hits. -/
namespace ClaudeWCT.W9.T3.Security.CanonGraph
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
theorem sel_base (labels : Labels) (m : Node) : m.base.sel labels = m.sel labels := by
  cases m <;> rfl
theorem sel_eq_of_toPos (labels : Labels) {m m' : Node} (h : m.toPos = m'.toPos) : m.sel labels = m'.sel labels := by
  rw [← sel_base labels m, ← sel_base labels m', toPos_injective_base h]
/-- A hit (equal used halves) between a non-selected, non-phantom node and the selected trial of its position is a
rejected active trial whose zero test failed while the selected one passed, impossible unless every trial of that
top position failed (`CapFail`). -/
theorem rejected_hit_capFail {labels : Labels} {m node : Node} (hpos : m.toPos = node.toPos)
    (hp : ¬ PhantomAt m labels) (hne : m ≠ node.sel labels)
    (heq : Extract.Paired.proj node.toPos (labels m) = Extract.Paired.proj node.toPos (labels (node.sel labels))) :
    CapFail labels := by
  have hsel := sel_eq_of_toPos labels hpos
  cases m with
  | node mn =>
      have ha : Active labels mn := by by_contra ha; exact hp ⟨mn, rfl, ha⟩
      rw [← hsel] at hne heq
      rw [← hpos] at heq
      change Extract.Paired.proj (Node.node mn).toPos (labels (.node mn)) =
        Extract.Paired.proj (Node.node mn).toPos (labels (.node (selNode labels mn))) at heq
      rw [Paired.pairedProj_node] at heq
      have hk : mn.1.nonce.val ≠ selNonce labels mn := by
        intro hk
        apply hne
        change Node.node mn = Node.node (withNonce mn (selNonce labels mn))
        rw [← hk, withNonce_self]
      have hspec := selNonce_spec labels mn
      have hS := selNonce_lt labels mn
      have hcapmax := trialCap_le mn.1.lay mn.1.level.val
      -- the selected trial fails exactly when trial `k = mn.nonce` does (equal used halves)
      have hfail_eq : trialFails labels mn (selNonce labels mn) ↔ trialFails labels mn mn.1.nonce.val := by
        unfold trialFails
        rw [withNonce_self]
        change _ ↔ topZeroOk _ ((Node.node mn).toPos.proj (labels (.node mn))) = false
        rw [heq]
        rfl
      rcases Nat.lt_or_gt_of_ne hk with hlt | hgt
      · have hfk : trialFails labels mn mn.1.nonce.val := hspec.1 _ hlt
        have hfS := hfail_eq.2 hfk
        rcases hspec.2 with hpass | hlast
        · exact absurd hfS hpass
        · have hcap2 : 1 < trialCap mn.1.lay mn.1.level.val := by omega
          have htop : mn.1.lay = 0 ∧ mn.1.level.val < 11 := by
            by_contra hn
            unfold trialCap at hcap2
            rw [if_neg hn] at hcap2
            omega
          refine ⟨withNonce mn 0, htop.1, htop.2, withNonce_nonce mn (by omega), fun j hj => ?_⟩
          change trialFails labels mn j
          rcases Nat.lt_or_ge j (selNonce labels mn) with hj' | hj'
          · exact hspec.1 j hj'
          · have : j = selNonce labels mn := by
              change j < trialCap mn.1.lay mn.1.level.val at hj
              omega
            rw [this]; exact hfS
      · have hfS : trialFails labels mn (selNonce labels mn) := ha.2 _ hgt
        rcases hspec.2 with hpass | hlast
        · exact absurd hfS hpass
        · exfalso
          have := ha.1
          omega
  | _ =>
      exfalso
      apply hne
      rw [← hsel]
      rfl
end ClaudeWCT.W9.T3.Security.CanonGraph

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000

theorem prob_proj_eq (position : Extract.Pos) (target : Digest) :
    Pr[fun answer : HashOutput=>Extract.Paired.proj position answer=target |
      PMF.uniformOfFintype HashOutput]=(Fintype.card Digest:ℝ≥0∞)⁻¹ := by
  cases position with
  | wctNode index coord level node=>
    by_cases h:Extract.Paired.highNodeAt coord level node
    · simp only [Extract.Paired.proj,if_pos h]
      exact prob_high_eq target
    · simp only [Extract.Paired.proj,if_neg h]
      exact SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq target
  | wctLeaf index coord child=>
    by_cases h:Extract.Paired.highLeafAt coord child
    · simp only [Extract.Paired.proj,if_pos h]
      exact prob_high_eq target
    · simp only [Extract.Paired.proj,if_neg h]
      exact SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq target
  -- C2/C3: the lower-tree positions use the legacy (#866) projection `Pos.proj`.
  | chain lay tree leaf i step=>
    rw [Extract.Paired.proj_chain]
    exact ClaudeWCT.W9.T3.Security.Wots.prob_proj_eq _ target
  | leaf lay tree leaf=>
    rw [Extract.Paired.proj_leaf]
    exact ClaudeWCT.W9.T3.Security.Wots.prob_proj_eq _ target
  | node lay tree level node=>
    rw [Extract.Paired.proj_node]
    exact ClaudeWCT.W9.T3.Security.Wots.prob_proj_eq _ target
  -- witness stack: FTS chains 1, 3 keep the high half on steps < 3
  | wctChain index coord child chain step=>
    by_cases h:WCT9.ftsChainHigh chain step
    · simp only [Extract.Paired.proj,if_pos h]
      exact prob_high_eq target
    · simp only [Extract.Paired.proj,if_neg h]
      exact SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq target
  | _=>exact SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq target
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

structure Variant (labels : CanonGraph.Labels) (T T' : Answers) : Prop where
  agrees : CanonGraph.Paired.Agrees T labels
  coin : ∀ n, T (.inl (.inl n)) = T' (.inl (.inl n))
  priv : ∀ c, T (.inr c) = T' (.inr c)
  pub : ∀ x : HashInput, (∀ node : CanonGraph.Node, Extract.posOf x = some node.toPos →
    ∃ m : CanonGraph.Node, x = CanonGraph.Paired.cell (CanonGraph.secretsOf T) m labels) →
    T (.inl (.inr x)) = T' (.inl (.inr x))

theorem posOf_honestInput (T : Answers) (p : Extract.Pos) (hp : Extract.Paired.Bounded p) :
    Extract.posOf (Extract.Paired.honestInput T p) = some p :=
  Extract.posOf_eq hp.legacy (Extract.Paired.honestInput_length T p) (Extract.Paired.hdrBlock_honestInput T p)


end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Top-nonce layer: under agreement, a rejected keygen trial is the cell of an active trial node. -/
theorem topTrial_cell {T : Answers} {labels : CanonGraph.Labels} (h : CanonGraph.Paired.Agrees T labels) {x : HashInput}
    (ht : TopTrial T x) : ∃ m : CanonGraph.Node, x = CanonGraph.Paired.cell (CanonGraph.secretsOf T) m labels := by
  obtain ⟨level, c, k, hl, hc, hk, rfl⟩ := ht
  have hlev : level < height (0 : Layer) := by simp [height]; omega
  have hh : height (0 : Layer) - level - 1 = 11 - level := by simp [height]; omega
  have hc' : c < 2 ^ (height (0 : Layer) - level - 1) := by rw [hh]; exact hc
  have hpow : 2 ^ (height (0 : Layer) - level) = 2 * 2 ^ (height (0 : Layer) - level - 1) := by
    rw [← pow_succ']; congr 1; omega
  obtain ⟨n, hn, hlay, htree, hlv, hidx⟩ :=
    CanonGraph.Paired.treeNodeAt_some 0 0 level c hlev hc' (by decide) (Or.inl rfl)
  have hL : Correctness.treeValue (WCT9.wotsTree T 0 0) level (2 * c) = CanonGraph.treeLabel labels 0 0 level (2 * c) :=
    CanonGraph.Paired.builtTree_eq h 0 0 level (2 * c) (by omega) (by omega) (by decide) (Or.inl rfl)
  have hR : Correctness.treeValue (WCT9.wotsTree T 0 0) level (2 * c + 1) = CanonGraph.treeLabel labels 0 0 level (2 * c + 1) :=
    CanonGraph.Paired.builtTree_eq h 0 0 level (2 * c + 1) (by omega) (by omega) (by decide) (Or.inl rfl)
  obtain ⟨hsel, -⟩ := CanonGraph.tree_step (fun m => h (.node m)) 0 0 level c n hn hL hR
  have hk' : k ≤ CanonGraph.selNonce labels n := by
    have : WCT9.honestNonce T 0 0 level c = CanonGraph.selNonce labels n := hsel
    omega
  have ha := CanonGraph.active_trial_of_le (labels := labels) (n := n) hk'
  have hcap := CanonGraph.trialCap_le n.1.lay n.1.level.val
  have hks := CanonGraph.selNonce_lt labels n
  refine ⟨.node (CanonGraph.withNonce n k), ?_⟩
  rw [CanonGraph.Paired.cell_node, CanonGraph.cell_node_active ha, CanonGraph.withNonce_nonce n (by omega)]
  simp only [CanonGraph.withNonce_lay, CanonGraph.withNonce_tree, CanonGraph.withNonce_level,
    CanonGraph.withNonce_idx]
  rw [hlay, htree, hlv, hidx, hL, hR, hh]
  rfl
theorem Variant.honest {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') :
    ∀ q, HonestQuery T q → T q = T' q
  | .inl (.inl n), _ => hv.coin n
  | .inr c, _ => hv.priv c
  | .inl (.inr x), Or.inl hnone => hv.pub x (fun node h => by rw [hnone] at h; cases h)
  | .inl (.inr x), Or.inr (Or.inl ⟨p, hp, hx⟩) => hv.pub x (fun node h => by
      rw [hx,posOf_honestInput T p hp] at h
      cases h
      rw [hx]
      exact ⟨_, CanonGraph.Paired.honestInput_eq T labels hv.agrees node hp⟩)
  | .inl (.inr x), Or.inr (Or.inr ht) => hv.pub x (fun _ _ => topTrial_cell hv.agrees ht)

theorem Variant.congr {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') {α : Type}
    {program : M α} (hp : QueriesSat T (HonestQuery T) program) :
    evalWithAnswerFn T program = evalWithAnswerFn T' program ∧
      SourceReplay.queried T program = SourceReplay.queried T' program :=
  congr_of_queried T T' program (fun q hq => hv.honest q (hp q hq))

theorem eval_keygen_variant {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') :
    evalWithAnswerFn T keygen = evalWithAnswerFn T' keygen :=
  (hv.congr (sat_keygen T)).1

theorem keygen_queries_variant {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') :
    SourceReplay.queried T keygen = SourceReplay.queried T' keygen :=
  (hv.congr (sat_keygen T)).2

end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Fixed
variable (V : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ V) (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (labels : CanonGraph.Labels)
/-- Top-nonce layer: the resampled rows are the inputs at a graph position that are no node's cell (with trial
nodes, a position may own several cells: its active trials). -/
noncomputable def strRows : Finset HashInput :=
  V.filter fun x => (∃ node : CanonGraph.Node, Extract.posOf x = some node.toPos) ∧
    ∀ node : CanonGraph.Node, x ≠ CanonGraph.Paired.cell s node labels
theorem mem_strRows (x : HashInput) :
    x ∈ strRows V s labels ↔ x ∈ V ∧ (∃ node : CanonGraph.Node, Extract.posOf x = some node.toPos) ∧
      ∀ node : CanonGraph.Node, x ≠ CanonGraph.Paired.cell s node labels := by
  unfold strRows
  rw [Finset.mem_filter]
theorem strRows_not_cell {x : HashInput} (hx : x ∈ strRows V s labels) (node : CanonGraph.Node) :
    x ≠ CanonGraph.Paired.cell s node labels :=
  ((mem_strRows V s labels x).mp hx).2.2 node
def strEmbed : strRows V s labels → V := fun x => ⟨x.val, ((mem_strRows V s labels x.val).mp x.property).1⟩
theorem strEmbed_injective : Function.Injective (strEmbed V s labels) := by
  intro a b h
  exact Subtype.ext (congrArg (fun y : V => y.val) h)
abbrev Rest := SphincsSecurity.Concrete.UniformTableSplit.Outside (strEmbed V s labels) → HashOutput
noncomputable def strTable (rest : Rest V s labels) (ρ : strRows V s labels → HashOutput) : Answers :=
  eagerAnswers V (CanonGraph.privateEquiv.symm (s, o))
    (CanonGraph.Paired.programmed V hU s labels
      (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest))
variable (rest : Rest V s labels)
theorem strTable_eq_canon (ρ : strRows V s labels → HashOutput) :
    strTable V hU s o labels rest ρ = CanonGraph.eagerAnswers (CanonGraph.privateEquiv.symm (s, o)) V
      (CanonGraph.Paired.programmed V hU s labels
        (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest)) := by
  funext query
  rcases query with (n | x) | c <;> rfl
theorem strTable_agrees (ρ : strRows V s labels → HashOutput) :
    CanonGraph.Paired.Agrees (strTable V hU s o labels rest ρ) labels := by
  rw [strTable_eq_canon]
  exact CanonGraph.Paired.eager_programmed_agrees V hU s o labels _
theorem secretsOf_strTable (ρ : strRows V s labels → HashOutput) :
    CanonGraph.secretsOf (strTable V hU s o labels rest ρ) = s := by
  rw [strTable_eq_canon, CanonGraph.secretsOf_eager, CanonGraph.privateSecrets_symm]
theorem strTable_public_mem (ρ : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∈ V) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) =
      CanonGraph.Paired.programmed V hU s labels
        (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest)
        ⟨x, hx⟩ :=
  SphincsSecurity.Concrete.finiteHashAnswer_none ∅ V _ x hx rfl
theorem strTable_str (ρ : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∈ strRows V s labels) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) = ρ ⟨x, hx⟩ := by
  have hV := ((mem_strRows V s labels x).mp hx).1
  rw [strTable_public_mem V hU s o labels rest ρ x hV,
    CanonGraph.Paired.programmed_other V hU s labels _ ⟨x, hV⟩ (strRows_not_cell V s labels hx)]
  exact SphincsSecurity.Concrete.UniformTableSplit.join_embed (strEmbed V s labels) (strEmbed_injective V s labels)
    ρ rest ⟨x, hx⟩
theorem strTable_out (ρ ρ' : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∉ strRows V s labels) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) = strTable V hU s o labels rest ρ' (.inl (.inr x)) := by
  by_cases hV : x ∈ V
  · rw [strTable_public_mem V hU s o labels rest ρ x hV, strTable_public_mem V hU s o labels rest ρ' x hV]
    by_cases hcell : ∃ node, x = CanonGraph.Paired.cell s node labels
    · obtain ⟨node, rfl⟩ := hcell
      have he : (⟨CanonGraph.Paired.cell s node labels, hV⟩ : V) = CanonGraph.Paired.cellIn V hU s node labels := rfl
      rw [he, CanonGraph.Paired.programmed_at, CanonGraph.Paired.programmed_at]
    · have hn : ∀ node, x ≠ CanonGraph.Paired.cell s node labels := fun node h => hcell ⟨node, h⟩
      rw [CanonGraph.Paired.programmed_other V hU s labels _ ⟨x, hV⟩ hn,
        CanonGraph.Paired.programmed_other V hU s labels _ ⟨x, hV⟩ hn]
      have hout : (⟨x, hV⟩ : V) ∉ Set.range (strEmbed V s labels) := by
        rintro ⟨y, hy⟩
        apply hx
        have : y.val = x := congrArg Subtype.val hy
        rw [← this]
        exact y.property
      exact (SphincsSecurity.Concrete.UniformTableSplit.join_outside _ _ ρ rest ⟨⟨x, hV⟩, hout⟩).trans
        (SphincsSecurity.Concrete.UniformTableSplit.join_outside _ _ ρ' rest ⟨⟨x, hV⟩, hout⟩).symm
  · change SphincsSecurity.Concrete.finiteHashAnswer ∅ V _ x = SphincsSecurity.Concrete.finiteHashAnswer ∅ V _ x
    simp only [SphincsSecurity.Concrete.finiteHashAnswer, dif_neg hV]

end Fixed

section Kernel
variable (V : Finset HashInput) (s : CanonGraph.Secrets) (labels : CanonGraph.Labels)
def strHit (Charged : HashInput → Prop) (x : HashInput) (a : HashOutput) : Prop :=
  x ∈ strRows V s labels ∧ Charged x ∧ ∃ node : CanonGraph.Node, Extract.posOf x = some node.toPos ∧
    Extract.Paired.proj node.toPos a = Extract.Paired.proj node.toPos (labels (node.sel labels))
theorem strHit_kernel (Charged : HashInput → Prop) (x : HashInput) (hx : x ∈ strRows V s labels) :
    Pr[strHit V s labels Charged x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * (if Charged x then 1 else 0 : ℝ≥0∞) := by
  by_cases hO : Charged x
  · rw [if_pos hO, mul_one]
    obtain ⟨-, ⟨node₀, hpos₀⟩, -⟩ := (mem_strRows V s labels x).mp hx
    calc Pr[strHit V s labels Charged x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)]
        ≤ Pr[fun a : HashOutput => Extract.Paired.proj node₀.toPos a =
              Extract.Paired.proj node₀.toPos (labels (node₀.sel labels)) |
            PMF.uniformOfFintype HashOutput] := by
          apply probEvent_mono
          rintro a - ⟨-, -, node, hpos, hlow⟩
          have ht : node.toPos = node₀.toPos := Option.some.inj (hpos.symm.trans hpos₀)
          rw [ht, CanonGraph.sel_eq_of_toPos labels ht] at hlow
          exact hlow
      _ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
          have h := prob_proj_eq node₀.toPos (Extract.Paired.proj node₀.toPos (labels (node₀.sel labels)))
          have hc : Fintype.card Digest = 2^128 := by simp
          simpa only [hc, Nat.cast_pow, Nat.cast_ofNat] using h
  · have hz : Pr[strHit V s labels Charged x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] = 0 :=
      probEvent_eq_zero fun _ _ h => hO h.2.1
    rw [hz]
    exact bot_le

end Kernel
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem fixed_seen_bound (V : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ V)
    (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (labels : CanonGraph.Labels) (rest : Rest V s labels)
    (Charged : HashInput → Prop) {α : Type} (program : OracleComp RefWorld α) :
    Pr[fun r => Seen (strHit V s labels Charged) r.2 |
      (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun rows =>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest rows))
          (SphincsSecurity.QueryPause.traced refObs program)]] ≤
      (2^128 : ℝ≥0∞)⁻¹ * ∑' r,
        Pr[=r | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun rows =>
          𝒮[simulateQ (refImpl (strTable V hU s o labels rest rows))
            (SphincsSecurity.QueryPause.traced refObs program)]] * (chargedCount Charged r.2 : ℝ≥0∞) := by
  exact lazy_seen_le (strRows V s labels) (strTable V hU s o labels rest)
    (fun rows x hx=>strTable_str V hU s o labels rest rows x hx)
    (fun rows x hx=>strTable_out V hU s o labels rest rows (fun _=>0) x hx)
    (strHit V s labels Charged) Charged (2^128 : ℝ≥0∞)⁻¹
    (fun _ _ h=>h.1) (fun x hx=>strHit_kernel V s labels Charged x hx) program

end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
attribute [local instance] Classical.propDecidable

def OtherInput (answers : Answers) (input : HashInput) : Prop :=
  ∃ position, Extract.posOf input = some position ∧ Extract.Paired.Bounded position ∧
    WotsExtract.PosSource position ∧ CanonicalRef.StructuralClass answers (CanonicalRef.sourceMessages answers) input position

def OtherQuery (answers : Answers) : Spec.Domain → Prop
  | .inl (.inr input) => OtherInput answers input
  | _ => False

noncomputable def otherCount (sample : RefSample) : Nat :=
  (sample.trace.filter fun entry => decide (OtherQuery sample.answers (.inl (.inr entry.1)))).length

def StructuralHitIn (inputs : Finset HashInput) (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ input ∈ inputs ∧
    Extract.posOf input = some position ∧ Extract.Paired.Bounded position ∧
    WotsExtract.PosSource position ∧
    CanonicalRef.StructuralClass answers (CanonicalRef.sourceMessages answers) input position ∧
    Extract.Paired.HashHitAt answers position (Extract.Paired.honestInput answers position) input
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem topLow_short (coord index heap : Nat) (left pad right : Digest) :
    ShortRespects (shortHash (WCT9.wctTopInput coord index heap left pad right)) := by
  apply ShortRespects.shortHash
  apply short_of_le
  rw [WCT9.wctTopInput_length]
  decide

theorem topHigh_short (coord index heap : Nat) (left pad right : Digest) :
    ShortRespects (WCT9.highHash (WCT9.wctTopInput coord index heap left pad right)) := by
  intro A T hAT
  unfold WCT9.highHash
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind]
  have hinput : (pad64 (WCT9.wctTopInput coord index heap left pad right)).length ≤ SeccLaw.maxInputLength :=
    short_of_le _ (by rw [WCT9.wctTopInput_length]; decide)
  have hh : evalWithAnswerFn A (publicHash (WCT9.wctTopInput coord index heap left pad right)) =
      evalWithAnswerFn T (publicHash (WCT9.wctTopInput coord index heap left pad right)) := by
    change A (.inl (.inr (pad64 _))) = T (.inl (.inr (pad64 _)))
    exact hAT.public _ hinput
  rw [hh]
  rfl

theorem sharedNode_short (first : Bool) (coord index heap : Nat)
    (pads : Nat → PairRoot) (left right : Digest) :
    ShortRespects (sharedNode first coord index heap pads left right) := by
  unfold sharedNode
  split
  · unfold sharedOuterHash
    split
    · exact topLow_short _ _ _ _ _ _
    · exact topHigh_short _ _ _ _ _ _
  · split
    · split
      · exact topHigh_short _ _ _ _ _ _
      · exact topLow_short _ _ _ _ _ _
    · change ShortRespects (WCT9.ftsHash heap (WCT9.wctTopInput coord index heap left 0 right))
      rw [WCT9.ftsHash_eq]
      split
      · exact topHigh_short _ _ _ _ _ _
      · exact topLow_short _ _ _ _ _ _

theorem sharedHeap_short (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) :
    ShortRespects (sharedHeap first index coord pads leaves) := by
  unfold sharedHeap
  exact ShortRespects.foldlM _ _ (fun _ _ _ =>
    ShortRespects.bind (sharedNode_short _ _ _ _ _ _ _) fun _ => ShortRespects.pure' _) _

theorem sharedLeaves_short {A T : Answers} (hAT : ShortAgree A T)
    (first : Bool) (index : Nat) (coord : Fin 9) (pads : Nat → PairRoot) :
    sharedLeaves A first index coord.val pads = sharedLeaves T first index coord.val pads := by
  unfold sharedLeaves
  apply congrArg List.ofFn
  funext physical
  have hraw : rawChild first physical.val < 128 := by
    have hp := physical.isLt
    cases first <;> simp only [rawChild, Bool.false_eq_true, ↓reduceIte] <;> omega
  exact WCT9.Wots.childRootH_congr (fun query hq => hAT query (WCT9.Wots.ftsQuery_short hq))
    (128 + physical.val) coord ⟨rawChild first physical.val, hraw⟩ _

theorem sharedNodes_short {A T : Answers} (hAT : ShortAgree A T)
    (first : Bool) (index : Nat) (coord : Fin 9) (pads : Nat → PairRoot) :
    sharedNodes A first index coord.val pads = sharedNodes T first index coord.val pads := by
  unfold sharedNodes
  rw [sharedLeaves_short hAT first index coord]
  exact sharedHeap_short first index coord.val pads _ A T hAT

theorem expectedPairRoot_short {A T : Answers} (hAT : ShortAgree A T)
    (index : Nat) (pair : Fin 4) (prev : PairRoot) :
    expectedPairRoot A index pair.val prev = expectedPairRoot T index pair.val prev := by
  have ha : firstNodes A index pair.val prev = firstNodes T index pair.val prev :=
    sharedNodes_short hAT true index ⟨2 * pair.val, by have := pair.isLt; omega⟩ _
  have hb : secondNodes A index pair.val prev = secondNodes T index pair.val prev := by
    unfold secondNodes
    rw [ha]
    exact sharedNodes_short hAT false index ⟨2 * pair.val + 1, by have := pair.isLt; omega⟩ _
  unfold expectedPairRoot
  rw [hb]

theorem forestCommitment_short {A T : Answers} (hAT : ShortAgree A T) (index : Nat) :
    forestCommitment A index = forestCommitment T index := by
  have hpair (pair : Nat) (hp : pair < 4) (prev : PairRoot) :=
    expectedPairRoot_short hAT index ⟨pair, hp⟩ prev
  dsimp only [forestCommitment, SigGolfCandidate.Research.SharedForest.forestCommitment]
  rw [hpair 0 (by decide), hpair 1 (by decide), hpair 2 (by decide), hpair 3 (by decide),
    sharedNodes_short hAT false index ⟨8, by decide⟩]

theorem sourceMessages_short {A T : Answers} (hAT : ShortAgree A T) (L : LeafAddr) :
    sourceMessages A L = sourceMessages T L := by
  unfold sourceMessages
  split
  · unfold ClaudeWCT.W9.T3M.Extract.honestPair
    rw [Ref.wotsTree_short hAT]
  · rw [forestCommitment_short hAT]

theorem layerCounterSearchAt_short (lay : Layer) (floor tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter fuel : Nat) : ShortRespects (WCT9.CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact ShortRespects.pure' _
  | succ fuel ih =>
      unfold WCT9.CanonicalPolicy.layerCounterSearchAt
      refine ShortRespects.bind (fun A T hAT => ?_) fun answer => ?_
      · exact hAT.public _ (by
          rw [← ClaudeWCT.W9.T3M.BC.pad64_layerEncodingInputP_zero, ClaudeWCT.W9.T3M.BC.layerEncodingRow_length]
          unfold SeccLaw.maxInputLength
          omega)
      · split
        · exact ih _
        · exact ShortRespects.pure' _

theorem searchOf_short {A T : Answers} (hAT : ShortAgree A T) (L : LeafAddr) (remaining : Nat) :
    searchOf A (sourceMessages A) L remaining = searchOf T (sourceMessages T) L remaining := by
  unfold searchOf
  rw [sourceMessages_short hAT L]
  exact layerCounterSearchAt_short _ _ _ _ _ _ _ A T hAT

theorem referenceContext_short {A T : Answers} (hAT : ShortAgree A T) (L : LeafAddr) :
    referenceContext A (sourceMessages A) L = referenceContext T (sourceMessages T) L := by
  exact congrFun (referenceContext_congr (answers := T) (answers' := A)
    (messages := sourceMessages T) (messages' := sourceMessages A)
    (fun K remaining _ => searchOf_short hAT K remaining)) L

theorem referenceSearch_short {A T : Answers} (hAT : ShortAgree A T) (L : LeafAddr) :
    referenceSearch A (sourceMessages A) L = referenceSearch T (sourceMessages T) L := by
  exact referenceSearch_congr (answers := T) (answers' := A)
    (messages := sourceMessages T) (messages' := sourceMessages A)
    (fun K remaining _ => searchOf_short hAT K remaining) L

theorem referenceDigits_short {A T : Answers} (hAT : ShortAgree A T) (L : LeafAddr) :
    referenceDigits A (sourceMessages A) L = referenceDigits T (sourceMessages T) L := by
  unfold referenceDigits
  rw [referenceSearch_short hAT L]

theorem depth_short {A T : Answers} (hAT : ShortAgree A T) (a : ChainAddr) :
    depth A (sourceMessages A) a = depth T (sourceMessages T) a := by
  unfold depth
  rw [referenceDigits_short hAT a.key]

theorem frontierValue_short {A T : Answers} (hAT : ShortAgree A T) (a : ChainAddr) :
    frontierValue A (sourceMessages A) a = frontierValue T (sourceMessages T) a := by
  unfold frontierValue
  rw [depth_short hAT, Ref.wotsSeed_short hAT]
  -- C3 (#866): the frontier is `honestChainValueW` (`Ref.honestChainValueW_short`).
  exact Ref.honestChainValueW_short hAT _ _ _ _ _ _

theorem referenceInput_short {A T : Answers} (hAT : ShortAgree A T) (L : LeafAddr) :
    referenceInput A (sourceMessages A) L = referenceInput T (sourceMessages T) L := by
  unfold referenceInput
  rw [referenceSearch_short hAT, sourceMessages_short hAT]
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem otherInput_short {A T : Answers} (hAT : ShortAgree A T) (x : HashInput) :
    OtherInput A x ↔ OtherInput T x := by
  have hd : CanonicalRef.depth A (CanonicalRef.sourceMessages A) =
      CanonicalRef.depth T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.depth_short hAT)
  have hc (p : Extract.Pos) : CanonicalRef.StructuralClass A (CanonicalRef.sourceMessages A) x p ↔
      CanonicalRef.StructuralClass T (CanonicalRef.sourceMessages T) x p := by
    cases p <;> simp only [CanonicalRef.StructuralClass, CanonicalRef.OtherChainRow, hd]
  constructor
  · rintro ⟨p,hpos,hb,hsource,hclass⟩
    exact ⟨p,hpos,hb,hsource,(hc p).mp hclass⟩
  · rintro ⟨p,hpos,hb,hsource,hclass⟩
    exact ⟨p,hpos,hb,hsource,(hc p).mpr hclass⟩

theorem otherQuery_short : SigGolfCandidate.T3.Security.Wots.ShortCongruent OtherQuery := by
  intro A T hAT query
  rcases query with (coin | input) | coordinate
  · exact Iff.rfl
  · exact otherInput_short hAT input
  · exact Iff.rfl
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem pairPrev_short {A T : Answers} (hAT : ShortAgree A T) (index pair : Nat) (hp : pair ≤ 4) :
    Extract.Paired.pairPrev A index pair = Extract.Paired.pairPrev T index pair := by
  induction pair with
  | zero => rfl
  | succ pair ih =>
      simp only [Extract.Paired.pairPrev]
      rw [ih (by omega)]
      exact CanonicalRef.expectedPairRoot_short hAT index ⟨pair,by omega⟩ _

theorem firstNodes_short {A T : Answers} (hAT : ShortAgree A T) (index pair : Nat)
    (hp : pair<4) (prev : PairRoot) : firstNodes A index pair prev = firstNodes T index pair prev :=
  CanonicalRef.sharedNodes_short hAT true index ⟨2*pair,by omega⟩ _

theorem secondNodes_short {A T : Answers} (hAT : ShortAgree A T) (index pair : Nat)
    (hp : pair<4) (prev : PairRoot) : secondNodes A index pair prev = secondNodes T index pair prev := by
  unfold secondNodes
  rw [firstNodes_short hAT index pair hp]
  exact CanonicalRef.sharedNodes_short hAT false index ⟨2*pair+1,by omega⟩ _

theorem pads_short {A T : Answers} (hAT : ShortAgree A T) (index coord branch : Nat) (hc : coord<9) :
    Extract.Paired.pads A index coord branch = Extract.Paired.pads T index coord branch := by
  unfold Extract.Paired.pads
  split
  · rw [pairPrev_short hAT index 4 (by omega)]
  · rename_i hn
    split
    · rw [pairPrev_short hAT index (coord/2) (by omega)]
    · rw [pairPrev_short hAT index (coord/2) (by omega),firstNodes_short hAT index (coord/2) (by omega)]

theorem nodes_short {A T : Answers} (hAT : ShortAgree A T) (index coord : Nat) (hc : coord<9) :
    Extract.Paired.nodes A index coord = Extract.Paired.nodes T index coord := by
  unfold Extract.Paired.nodes
  split
  · rw [pairPrev_short hAT index 4 (by omega)]
    exact CanonicalRef.sharedNodes_short hAT false index ⟨8,by decide⟩ _
  · rename_i hn
    split
    · rw [pairPrev_short hAT index (coord/2) (by omega),firstNodes_short hAT index (coord/2) (by omega)]
    · rw [pairPrev_short hAT index (coord/2) (by omega),secondNodes_short hAT index (coord/2) (by omega)]

theorem honestInput_short {A T : Answers} (hAT : ShortAgree A T)
    (position : Extract.Pos) (hb : Extract.Paired.Bounded position) :
    Extract.Paired.honestInput A position = Extract.Paired.honestInput T position := by
  cases position with
  | chain | leaf | node | wctChain => exact Ref.honestInput_short hAT _ hb.legacy
  | forest => exact hb.elim
  | wctLeaf index coord child =>
      obtain ⟨hi,hc,hch⟩ := hb
      simp only [Extract.Paired.honestInput]
      rw [pads_short hAT index coord _ hc,Ref.wctEnds_short hAT index coord child hc hch]
  | wctNode index coord level node =>
      have hc := hb.legacy.2.1
      simp only [Extract.Paired.honestInput]
      rw [nodes_short hAT index coord hc,pads_short hAT index coord _ hc]

theorem honestInput_length (T : Answers) (position : Extract.Pos) :
    (Extract.Paired.honestInput T position).length ≤ SeccLaw.maxInputLength := by
  cases position with
  | chain lay tree leaf i step => exact Ref.honestInput_length T (.chain lay tree leaf i step)
  | leaf lay tree leaf => exact Ref.honestInput_length T (.leaf lay tree leaf)
  | node lay tree level node => exact Ref.honestInput_length T (.node lay tree level node)
  | forest index => exact Ref.honestInput_length T (.forest index)
  | wctChain index coord child chain step => exact Ref.honestInput_length T (.wctChain index coord child chain step)
  | wctLeaf index coord child =>
      simp only [Extract.Paired.honestInput]
      apply short_of_le
      simp only [Extract.wctLeafInputP,Extract.listInput_length',List.length_cons,List.length_drop,
        Extract.wctEnds,List.length_ofFn]
      omega
  | wctNode index coord level node =>
      simp only [Extract.Paired.honestInput]
      exact short_of_le _ (by rw [WCT9.wctTopInput_length];decide)
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {labels : CanonGraph.Labels} {T T' : Answers}
theorem wotsTree_variant_top (hv : Variant labels T T') (tree : Nat) (ht : tree < 2 ^ Extract.treeBits 0) :
    WCT9.wotsTree T 0 tree = WCT9.wotsTree T' 0 tree := by
  obtain rfl : tree = 0 := Extract.tree_zero_of_treeBits ht rfl
  rw [WCT9.wotsTree_top, WCT9.wotsTree_top, ← Correctness.eval_buildTopTree, ← Correctness.eval_buildTopTree,
    (hv.congr (sat_buildTopTree T)).1]
theorem wotsTree_take_variant (hv : Variant labels T T') (lay : Layer) (tree : Nat)
    (ht : tree < 2 ^ Extract.treeBits lay) :
    (WCT9.wotsTree T lay tree).take (height lay) = (WCT9.wotsTree T' lay tree).take (height lay) := by
  have htree : tree < 2 ^ 40 := lt_trans (Extract.tree_lt_of_treeBits ht) (by norm_num)
  by_cases hl : lay = 0
  · subst hl
    rw [wotsTree_variant_top hv tree ht]
  · have h0 : 0 < 2 ^ height lay := by positivity
    have hc := (hv.congr (sat_buildTreeP T hl tree 0 [] (Cost.validDigits_nil lay) htree ht)).1
    rw [WCT9.eval_buildTreeP_result T hl tree 0 [] (Cost.validDigits_nil lay) h0,
      WCT9.eval_buildTreeP_result T' hl tree 0 [] (Cost.validDigits_nil lay) h0] at hc
    exact congrArg Prod.fst hc
theorem honestPair_variant (hv : Variant labels T T') (lay : Layer) (tree : Nat)
    (ht : tree < 2 ^ Extract.treeBits lay) :
    Extract.honestPair T lay tree = Extract.honestPair T' lay tree := by
  have hh : height lay - 1 < height lay := by have : 1 ≤ height lay := by fin_cases lay <;> decide
                                              omega
  have key : ∀ x, treeValue (WCT9.wotsTree T lay tree) (height lay - 1) x =
      treeValue (WCT9.wotsTree T' lay tree) (height lay - 1) x := fun x => by
    rw [← WCT9.treeValue_take _ hh, wotsTree_take_variant hv lay tree ht, WCT9.treeValue_take _ hh]
  unfold Extract.honestPair
  rw [key, key]

theorem forestCommitment_variant (hv : Variant labels T T') (index : Nat) (hi : index<2^31) :
    CanonicalRef.forestCommitment T index = CanonicalRef.forestCommitment T' index := by
  let selected := forestSelectionFromOutput 0
  let words := forestWordsFromOutput 0
  have he : evalWithAnswerFn T (buildForest index selected words) =
      evalWithAnswerFn T' (buildForest index selected words) :=
    (hv.congr (sat_buildForest T index hi selected words)).1
  have hp : (evalWithAnswerFn T (buildForest index selected words)).2 =
      (evalWithAnswerFn T' (buildForest index selected words)).2 :=
    congrArg (fun value : ForestOpening × SigGolfCandidate.Research.SharedForest.PairRoot => value.2) he
  exact (buildForest_commitment T index selected words).symm.trans
    (hp.trans (buildForest_commitment T' index selected words))

theorem sourceMessages_variant (hv : Variant labels T T') (L : LeafAddr)
    (hL : WotsExtract.SourceLeaf7 L) :
    CanonicalRef.sourceMessages T L = CanonicalRef.sourceMessages T' L := by
  unfold CanonicalRef.sourceMessages
  split
  · rename_i h3
    rw [honestPair_variant hv _ _ (Extract.routed_treeBits_succ h3 hL.1 hL.2)]
  · rw [forestCommitment_variant hv _ (Nat.mod_lt _ (by decide))]

theorem source_search_variant (hv : Variant labels T T') (L : LeafAddr)
    (hL : WotsExtract.SourceLeaf7 L) (remaining : Nat) :
    CanonicalRef.searchOf T (CanonicalRef.sourceMessages T) L remaining =
      CanonicalRef.searchOf T' (CanonicalRef.sourceMessages T') L remaining := by
  unfold CanonicalRef.searchOf
  rw [sourceMessages_variant hv L hL]
  exact (hv.congr (sat_canonical_search T _ _ _ _ _ _ _)).1

theorem referenceContext_variant (hv : Variant labels T T') (L : LeafAddr)
    (hL : WotsExtract.SourceLeaf7 L) :
    CanonicalRef.referenceContext T (CanonicalRef.sourceMessages T) L =
      CanonicalRef.referenceContext T' (CanonicalRef.sourceMessages T') L := by
  exact (CanonicalRef.context_congr_on
    (search := CanonicalRef.searchOf T (CanonicalRef.sourceMessages T))
    (search' := CanonicalRef.searchOf T' (CanonicalRef.sourceMessages T')) WCT9.CanonicalPolicy.credit WotsExtract.SourceLeaf7
    (fun _ h hp => CanonicalRef.source_parent h hp)
    (fun leaf hl remaining _ => (source_search_variant hv leaf hl remaining).symm) hL).symm

theorem referenceSearch_variant (hv : Variant labels T T') (L : LeafAddr)
    (hL : WotsExtract.SourceLeaf7 L) :
    CanonicalRef.referenceSearch T (CanonicalRef.sourceMessages T) L =
      CanonicalRef.referenceSearch T' (CanonicalRef.sourceMessages T') L := by
  change (CanonicalRef.referenceContext T (CanonicalRef.sourceMessages T) L).bind
      (CanonicalRef.searchOf T (CanonicalRef.sourceMessages T) L) =
    (CanonicalRef.referenceContext T' (CanonicalRef.sourceMessages T') L).bind
      (CanonicalRef.searchOf T' (CanonicalRef.sourceMessages T') L)
  exact congrArg₂ (@Option.bind Nat (BitVec 32 × List Nat × Bool))
    (referenceContext_variant hv L hL)
    (funext fun remaining => source_search_variant hv L hL remaining)


theorem referenceDigits_variant (hv : Variant labels T T') (L : LeafAddr)
    (hL : WotsExtract.SourceLeaf7 L) :
    CanonicalRef.referenceDigits T (CanonicalRef.sourceMessages T) L =
      CanonicalRef.referenceDigits T' (CanonicalRef.sourceMessages T') L := by
  unfold CanonicalRef.referenceDigits
  rw [referenceSearch_variant hv L hL]

theorem depth_variant (hv : Variant labels T T') (a : ChainAddr)
    (hL : WotsExtract.SourceLeaf7 a.key) :
    CanonicalRef.depth T (CanonicalRef.sourceMessages T) a =
      CanonicalRef.depth T' (CanonicalRef.sourceMessages T') a := by
  unfold CanonicalRef.depth
  rw [referenceDigits_variant hv a.key hL]

end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private def ClassDepth (D : ChainAddr → Nat) (x : HashInput) (p : Extract.Pos) : Prop :=
  match p with
  | .chain .. => ∃ (a : ChainAddr) (step : Nat), Extract.posOf x = some (.chain a.key.lay a.key.tree a.key.leaf a.chain step) ∧
      ((∀ value, x ≠ chainRowW a step value) ∨ D a ≤ step)
  | _ => True

private theorem structuralClass_congr_generic (D D' : ChainAddr → Nat)
    (hdepth : ∀ a : ChainAddr, WotsExtract.SourceLeaf7 a.key →
      D a = D' a)
    {x : HashInput} {p : Extract.Pos} (hpos : Extract.posOf x = some p) (hsrc : WotsExtract.PosSource p) :
    ClassDepth D x p ↔ ClassDepth D' x p := by
  cases p with
  | chain lay tree leaf i step =>
      obtain ⟨htree, hleaf, -, -⟩ := hsrc
      have key : ∀ (a : ChainAddr) (step' : Nat),
          Extract.posOf x = some (.chain a.key.lay a.key.tree a.key.leaf a.chain step') →
          D a = D' a := by
        intro a step' h
        rw [hpos] at h
        simp only [Option.some.injEq, Extract.Pos.chain.injEq] at h
        obtain ⟨hl, ht, hlf, -, -⟩ := h
        apply hdepth a
        constructor
        · rw [← ht, ← hl]; exact htree
        · rw [← hlf, ← hl]; exact hleaf
      constructor
      · rintro ⟨a, step', h, hc⟩
        exact ⟨a, step', h, hc.imp id (fun hd => (Nat.le_of_eq (key a step' h).symm).trans hd)⟩
      · rintro ⟨a, step', h, hc⟩
        exact ⟨a, step', h, hc.imp id (fun hd => (Nat.le_of_eq (key a step' h)).trans hd)⟩
  | leaf | node | forest | wctChain | wctLeaf | wctNode => exact Iff.rfl

theorem structuralClass_congr_of_depth {T T' : Answers}
    (hdepth : ∀ a : ChainAddr, WotsExtract.SourceLeaf7 a.key →
      CanonicalRef.depth T (CanonicalRef.sourceMessages T) a = CanonicalRef.depth T' (CanonicalRef.sourceMessages T') a)
    {x : HashInput} {p : Extract.Pos} (hpos : Extract.posOf x = some p) (hsrc : WotsExtract.PosSource p) :
    CanonicalRef.StructuralClass T (CanonicalRef.sourceMessages T) x p ↔
      CanonicalRef.StructuralClass T' (CanonicalRef.sourceMessages T') x p :=
  structuralClass_congr_generic (CanonicalRef.depth T (CanonicalRef.sourceMessages T))
    (CanonicalRef.depth T' (CanonicalRef.sourceMessages T')) hdepth hpos hsrc

theorem otherInput_congr_of_depth {T T' : Answers}
    (hdepth : ∀ a : ChainAddr, WotsExtract.SourceLeaf7 a.key →
      CanonicalRef.depth T (CanonicalRef.sourceMessages T) a = CanonicalRef.depth T' (CanonicalRef.sourceMessages T') a)
    (x : HashInput) : OtherInput T x ↔ OtherInput T' x := by
  constructor
  · rintro ⟨p, hpos, hb, hsrc, hc⟩
    exact ⟨p, hpos, hb, hsrc, (structuralClass_congr_of_depth (T := T) (T' := T') hdepth hpos hsrc).mp hc⟩
  · rintro ⟨p, hpos, hb, hsrc, hc⟩
    exact ⟨p, hpos, hb, hsrc, (structuralClass_congr_of_depth (T := T) (T' := T') hdepth hpos hsrc).mpr hc⟩
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)

theorem eval_sign_variant {labels : CanonGraph.Labels} {T T' : Answers}
    (hv : Variant labels T T') (published : SigGolfCandidate.T3.Cache) (request : Request) :
    evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) =
      evalWithAnswerFn T' (PairedOuter.FullGame.authenticatedSign published request) :=
  (hv.congr (sat_authenticatedSign T published request)).1

theorem sign_queries_variant {labels : CanonGraph.Labels} {T T' : Answers}
    (hv : Variant labels T T') (published : SigGolfCandidate.T3.Cache) (request : Request) :
    SourceReplay.queried T (PairedOuter.FullGame.authenticatedSign published request) =
      SourceReplay.queried T' (PairedOuter.FullGame.authenticatedSign published request) :=
  (hv.congr (sat_authenticatedSign T published request)).2

end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem referenceGame_variant {labels : CanonGraph.Labels} {T T' : Answers}
    (hv : Variant labels T T') (adversary : Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceGame T adversary q = PairedReference.referenceGame T' adversary q :=
  PairedReference.referenceGame_congr T T' (eval_keygen_variant hv)
    (congrArg List.length (keygen_queries_variant hv))
    (eval_sign_variant hv) (fun published request => congrArg List.length (sign_queries_variant hv published request))
    adversary q

theorem structuralClass_variant {labels : CanonGraph.Labels} {T T' : Answers}
    (hv : Variant labels T T') {x : HashInput} {p : Extract.Pos}
    (hpos : Extract.posOf x = some p) (hsrc : WotsExtract.PosSource p) :
    CanonicalRef.StructuralClass T (CanonicalRef.sourceMessages T) x p ↔
      CanonicalRef.StructuralClass T' (CanonicalRef.sourceMessages T') x p :=
  PairedReference.structuralClass_congr_of_depth (T:=T) (T':=T') (depth_variant hv) hpos hsrc

theorem otherInput_variant {labels : CanonGraph.Labels} {T T' : Answers}
    (hv : Variant labels T T') (x : HashInput) :
    PairedReference.OtherInput T x ↔ PairedReference.OtherInput T' x :=
  PairedReference.otherInput_congr_of_depth (T:=T) (T':=T') (depth_variant hv) x
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal OracleComp.EvalDist OracleComp.DeferredSampling
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (Node Labels Secrets OtherHalves privateEquiv)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Fixed
variable (V : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ V) (s : Secrets) (o : OtherHalves) (labels : Labels)
variable (rest : Rest V s labels)
theorem strTable_variant (ρ ρ' : strRows V s labels → HashOutput) :
    Variant labels (strTable V hU s o labels rest ρ) (strTable V hU s o labels rest ρ') where
  agrees := strTable_agrees V hU s o labels rest ρ
  coin := fun _ => rfl
  priv := fun _ => rfl
  pub := fun x hx => by
    apply strTable_out V hU s o labels rest ρ ρ' x
    intro hmem
    obtain ⟨-, ⟨node, hpos⟩, hall⟩ := (mem_strRows V s labels x).mp hmem
    obtain ⟨m, hm⟩ := hx node hpos
    rw [secretsOf_strTable] at hm
    exact hall m hm
theorem hit_bridge (ρ : strRows V s labels → HashOutput) (qs : List RefWorld.Domain)
    (h : PairedReference.StructuralHitIn V (strTable V hU s o labels rest ρ) (traceOf (strTable V hU s o labels rest ρ) qs)) :
    (∃ e ∈ traceOf (strTable V hU s o labels rest ρ) qs,
      strHit V s labels (PairedReference.OtherInput (strTable V hU s o labels rest (fun _ => 0))) e.1 e.2) ∨
      CanonGraph.CapFail labels := by
  by_cases hcf : CanonGraph.CapFail labels
  · exact Or.inr hcf
  left
  obtain ⟨p, x, a, hmem, hxV, hpos, hb, hsrc, hc, hne, hlow⟩ := h
  obtain ⟨node, rfl⟩ := Wots.Structural.exists_node_of_posSource hsrc
  have hag := strTable_agrees V hU s o labels rest ρ
  have ha : a = strTable V hU s o labels rest ρ (.inl (.inr x)) := mem_traceOf hmem
  rw [CanonGraph.Paired.honest_answer _ labels hag node hb] at hlow
  have hlow' : Extract.Paired.proj node.toPos a = Extract.Paired.proj node.toPos (labels (node.sel labels)) := by
    rw [ha]; exact hlow
  rw [CanonGraph.Paired.honestInput_eq _ labels hag node hb, secretsOf_strTable] at hne
  refine ⟨(x, a), hmem, ?_, ?_, node, hpos, hlow'⟩
  · refine (mem_strRows V s labels x).mpr ⟨hxV, ⟨node, hpos⟩, fun m hm => ?_⟩
    obtain ⟨hmpos, hmp⟩ := CanonGraph.Paired.cell_eq_of_posOf s labels hpos hm
    have hTm : strTable V hU s o labels rest ρ (.inl (.inr x)) = labels m := by
      have := hag m
      rw [secretsOf_strTable] at this
      rw [hm]
      exact this
    refine hcf (CanonGraph.rejected_hit_capFail hmpos hmp (fun e => hne (by rw [hm, e])) ?_)
    rw [← hTm, ← ha]
    exact hlow'
  · exact ⟨node.toPos, hpos, hb, hsrc, (structuralClass_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0))
      hpos hsrc).mp hc⟩
theorem count_bridge (ρ : strRows V s labels → HashOutput) (pk : Digest) (trace : List Entry) :
    PairedReference.otherCount ⟨strTable V hU s o labels rest ρ, pk, trace⟩ =
      (trace.filter fun e => decide (PairedReference.OtherInput (strTable V hU s o labels rest (fun _ => 0)) e.1)).length := by
  unfold PairedReference.otherCount
  congr 1
  apply List.filter_congr
  intro e _
  exact decide_eq_decide.mpr (otherInput_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0)) e.1)
end Fixed
noncomputable def sampleComp (adversary : Final.Paired.AdversaryP) (q : Nat) (T : Answers) : ProbComp RefSample :=
  (fun run => (⟨T, (evalWithAnswerFn T keygen).1, traceOf T run.2⟩ : RefSample)) <$> PairedReference.offlineRun T adversary q
section Bound
variable (adversary : Final.Paired.AdversaryP) (q : Nat) (V : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ V) (s : Secrets)
  (o : OtherHalves) (labels : Labels) (rest : Rest V s labels)
theorem sampleComp_recorded (ρ : strRows V s labels → HashOutput) :
    𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)] =
      (fun run => (⟨strTable V hU s o labels rest ρ, (evalWithAnswerFn (strTable V hU s o labels rest ρ) keygen).1,
          traceOf (strTable V hU s o labels rest ρ) run.2⟩ : RefSample)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] := by
  unfold sampleComp PairedReference.offlineRun
  rw [referenceGame_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0)), evalSPMF_map]
theorem recorded_pair (ρ : strRows V s labels → HashOutput) :
    (fun run => (run.1, traceOf (strTable V hU s o labels rest ρ) run.2)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] =
      (fun r => (r.1, r.2.toList)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryPause.traced refObs (PairedReference.referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] := by
  rw [← evalSPMF_map, ← evalSPMF_map, recorded_traced]
theorem fixed_bound :
    Pr[fun sample => PairedReference.StructuralHitIn V sample.answers sample.trace |
        (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)]] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample,
        Pr[= sample | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)]] * (PairedReference.otherCount sample : ℝ≥0∞) +
        (if CanonGraph.CapFail labels then 1 else 0) := by
  by_cases hcf : CanonGraph.CapFail labels
  · rw [if_pos hcf]
    exact le_trans probEvent_le_one (le_add_left le_rfl)
  rw [if_neg hcf, add_zero]
  set T := strTable V hU s o labels rest with hT
  set G0 := PairedReference.referenceGame (T fun _ => 0) adversary q with hG0
  set Hit := strHit V s labels (PairedReference.OtherInput (T fun _ => 0)) with hHit
  set Charged := PairedReference.OtherInput (T fun _ => 0) with hCharged
  have hlazy := fixed_seen_bound V hU s o labels rest Charged G0
  have hevent : Pr[fun sample => PairedReference.StructuralHitIn V sample.answers sample.trace |
        (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (T ρ)]] ≤
      Pr[fun r => Seen Hit r.2 | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] := by
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine ENNReal.tsum_le_tsum fun ρ => mul_le_mul' le_rfl ?_
    rw [sampleComp_recorded adversary q V hU s o labels rest ρ, probEvent_map]
    have hpair := recorded_pair adversary q V hU s o labels rest ρ
    have hseen : Pr[fun r => Seen Hit r.2 |
        𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] =
        Pr[fun z => ∃ e ∈ z.2, Hit e.1 e.2 | (fun run => (run.1, traceOf (T ρ) run.2)) <$>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryCap.recorded G0)]] := by
      rw [hpair, probEvent_map]
      rfl
    rw [hseen, probEvent_map]
    apply probEvent_mono
    intro run _ h
    exact (hit_bridge V hU s o labels rest ρ run.2 h).resolve_right hcf
  have hcount : (∑' sample,
        Pr[= sample | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (T ρ)]] * (PairedReference.otherCount sample : ℝ≥0∞)) =
      ∑' r, Pr[= r | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] *
            (chargedCount Charged r.2 : ℝ≥0∞) := by
    rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
    refine tsum_congr fun ρ => congrArg _ ?_
    rw [sampleComp_recorded adversary q V hU s o labels rest ρ, tsum_probOutput_map_mul]
    have hA : ∀ run : Option (Bool × Nat) × List RefWorld.Domain,
        (PairedReference.otherCount (⟨T ρ, (evalWithAnswerFn (T ρ) keygen).1, traceOf (T ρ) run.2⟩ : RefSample) : ℝ≥0∞) =
          (fun z : Option (Bool × Nat) × List Entry => ((z.2.filter fun e => decide (Charged e.1)).length : ℝ≥0∞))
            ((fun run => (run.1, traceOf (T ρ) run.2)) run) := by
      intro run
      rw [count_bridge V hU s o labels rest ρ]
    refine (tsum_congr fun run => congrArg _ (hA run)).trans ?_
    rw [← tsum_probOutput_map_mul _ (fun run : Option (Bool × Nat) × List RefWorld.Domain =>
        (run.1, traceOf (T ρ) run.2))
      (fun z : Option (Bool × Nat) × List Entry => ((z.2.filter fun e => decide (Charged e.1)).length : ℝ≥0∞)),
      recorded_pair adversary q V hU s o labels rest ρ, tsum_probOutput_map_mul]
    rfl
  rw [hcount]
  exact hevent.trans hlazy
end Bound
/-- Structural bound with an additive error `ε` (top-nonce layer: `ε` carries `Pr[CapFail]`). -/
def BoundOn (V : Finset HashInput) (ε : ℝ≥0∞) (p : SPMF RefSample) : Prop :=
  Pr[fun sample => PairedReference.StructuralHitIn V sample.answers sample.trace | p] ≤
    (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, Pr[= sample | p] * (PairedReference.otherCount sample : ℝ≥0∞) + ε
theorem boundOn_mono {V : Finset HashInput} {ε ε' : ℝ≥0∞} {p : SPMF RefSample} (h : BoundOn V ε p) (he : ε ≤ ε') :
    BoundOn V ε' p :=
  le_trans h (add_le_add le_rfl he)
theorem tsum_prob_mul_le {X : Type} (μ : SPMF X) (c : ℝ≥0∞) : ∑' x, Pr[= x | μ] * c ≤ c := by
  rw [ENNReal.tsum_mul_right]
  calc (∑' x, Pr[= x | μ]) * c ≤ 1 * c := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = c := one_mul c
theorem boundOn_bind {X : Type} (V : Finset HashInput) (μ : SPMF X) (K : X → SPMF RefSample) (ε : X → ℝ≥0∞)
    (h : ∀ x, BoundOn V (ε x) (K x)) : BoundOn V (∑' x, Pr[= x | μ] * ε x) (μ >>= K) := by
  unfold BoundOn
  rw [probEvent_bind_eq_tsum, tsum_probOutput_bind_mul]
  calc (∑' x, Pr[= x | μ] * Pr[fun sample => PairedReference.StructuralHitIn V sample.answers sample.trace | K x])
      ≤ ∑' x, Pr[= x | μ] * ((2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, Pr[= sample | K x] *
          (PairedReference.otherCount sample : ℝ≥0∞) + ε x) :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = _ := by simp only [mul_add, ENNReal.tsum_add, mul_left_comm _ (2 ^ 128 : ℝ≥0∞)⁻¹, ENNReal.tsum_mul_left]
section Assembly
noncomputable local instance instFintypeCoordinate_wotsStructural : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsStructural : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType Secrets := SampleableType.ofFintype _
noncomputable local instance : SampleableType OtherHalves := SampleableType.ofFintype _
noncomputable local instance : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance (U : Finset HashInput) : SampleableType (U → HashOutput) := SampleableType.ofFintype _
theorem referenceInputs_canon (adversary : Final.Paired.AdversaryP) : CanonGraph.Paired.canonInputs ⊆ PairedReference.referenceInputs adversary := by
  unfold PairedReference.referenceInputs
  exact CanonGraph.Paired.canonInputs_subset_publicUniverse.trans Finset.subset_union_left
theorem tables_bind {Result : Type} (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U)
    (next : FullGame.FullTable → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
      let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
      next privateTable publicTable] =
      𝒮[do
        let secrets ← ($ᵗ Secrets : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (privateEquiv.symm (secrets, other)) (CanonGraph.Paired.programmed U hU secrets labels residual)] := by
  refine (CanonGraph.private_bind (fun privateTable => do
    let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
    next privateTable publicTable)).trans ?_
  apply evalSPMF_bind_congr_left
  intro secrets
  apply evalSPMF_bind_congr_left
  intro other
  exact CanonGraph.Paired.uniform_bind_programmed U hU secrets (fun table => next (privateEquiv.symm (secrets, other)) table)
theorem tables_bind_spmf {R : Type} (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U)
    (next : FullGame.FullTable → (U → HashOutput) → ProbComp R) :
    ((liftM (PMF.uniformOfFintype FullGame.FullTable) : SPMF _) >>= fun pt =>
      (liftM (PMF.uniformOfFintype (U → HashOutput)) : SPMF _) >>= fun pub => 𝒮[next pt pub]) =
    ((liftM (PMF.uniformOfFintype Secrets) : SPMF _) >>= fun s =>
      (liftM (PMF.uniformOfFintype OtherHalves) : SPMF _) >>= fun o =>
      (liftM (PMF.uniformOfFintype Labels) : SPMF _) >>= fun labels =>
      (liftM (PMF.uniformOfFintype (U → HashOutput)) : SPMF _) >>= fun r =>
        𝒮[next (privateEquiv.symm (s, o)) (CanonGraph.Paired.programmed U hU s labels r)]) := by
  have h := tables_bind U hU next
  simp only [evalSPMF_bind, evalSPMF_uniformSample] at h
  exact h
theorem referenceComp_spmf (adversary : Final.Paired.AdversaryP) (q : Nat) :
    𝒮[PairedReference.referenceComp adversary q] =
      ((liftM (PMF.uniformOfFintype FullGame.FullTable) : SPMF _) >>= fun pt =>
        (liftM (PMF.uniformOfFintype (PairedReference.referenceInputs adversary → HashOutput)) : SPMF _) >>= fun pub =>
          𝒮[sampleComp adversary q (eagerAnswers (PairedReference.referenceInputs adversary) pt pub)]) := by
  unfold PairedReference.referenceComp
  simp only [evalSPMF_bind, evalSPMF_uniformSample]
  rfl
theorem capFail_tsum_le :
    ∑' l, Pr[= l | (liftM (PMF.uniformOfFintype Labels) : SPMF Labels)] *
      (if CanonGraph.CapFail l then 1 else 0) ≤ (2 ^ 142 : ℝ≥0∞)⁻¹ := by
  have h := CanonGraph.prob_capFail_le
  have e : (liftM (PMF.uniformOfFintype Labels) : SPMF Labels) = 𝒮[($ᵗ Labels : ProbComp Labels)] :=
    (evalSPMF_uniformSample Labels).symm
  rw [e]
  rw [probEvent_eq_tsum_ite] at h
  refine le_trans (le_of_eq (tsum_congr fun l => ?_)) h
  rw [mul_ite, mul_one, mul_zero, probOutput_evalSPMF]
theorem referenceComp_bound (adversary : Final.Paired.AdversaryP) (q : Nat) :
    BoundOn (PairedReference.referenceInputs adversary) ((2 ^ 142 : ℝ≥0∞)⁻¹)
      𝒮[PairedReference.referenceComp adversary q] := by
  rw [referenceComp_spmf, tables_bind_spmf _ (referenceInputs_canon adversary)]
  refine boundOn_mono (boundOn_bind _ _ _ (fun _ => (2 ^ 142 : ℝ≥0∞)⁻¹) fun s => ?_) (tsum_prob_mul_le _ _)
  refine boundOn_mono (boundOn_bind _ _ _ (fun _ => (2 ^ 142 : ℝ≥0∞)⁻¹) fun o => ?_) (tsum_prob_mul_le _ _)
  refine boundOn_mono (boundOn_bind _ _ _ (fun labels => if CanonGraph.CapFail labels then 1 else 0)
    fun labels => ?_) capFail_tsum_le
  rw [uniform_split_bind (strEmbed (PairedReference.referenceInputs adversary) s labels)
    (strEmbed_injective (PairedReference.referenceInputs adversary) s labels)]
  refine boundOn_mono (boundOn_bind _ _ _ (fun _ => if CanonGraph.CapFail labels then 1 else 0) fun rest => ?_)
    (tsum_prob_mul_le _ _)
  exact fixed_bound adversary q (PairedReference.referenceInputs adversary) (referenceInputs_canon adversary) s o labels rest
end Assembly
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
theorem referenceExperiment_eq (adversary : Final.Paired.AdversaryP) (q : Nat) :
    referenceExperiment adversary q = liftM (referenceComp adversary q) := rfl
theorem reference_structural_in_le (adversary : Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun sample => StructuralHitIn (referenceInputs adversary) sample.answers sample.trace |
        referenceExperiment adversary q] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, referenceExperiment adversary q sample * (otherCount sample : ℝ≥0∞) +
        (2 ^ 142 : ℝ≥0∞)⁻¹ := by
  have h := PairedStructural.referenceComp_bound adversary q
  unfold PairedStructural.BoundOn at h
  rw [referenceExperiment_eq, probEvent_liftM_pmf]
  simp only [liftM_pmf_apply]
  exact h

end ClaudeWCT.W9.T3.Security.Wots.PairedReference
end
-- ==== merged from SphincsSecurity_Proof_Chains_PartialChainLastRow ====
section

section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
def knownRun : {n : Nat} → (Fin n → State → Option State) → State → Option State
  | 0, _, start => some start
  | _ + 1, observed, start => (observed 0 start).bind (knownRun (Fin.tail observed))
noncomputable def knownCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : Nat :=
  ∑ start : State, if knownRun observed start = some endpoint then 1 else 0
noncomputable def knownMass {n : Nat} (prior : PMF State) (observed : Fin n → State → Option State) (endpoint : State) : ENNReal :=
  ∑' start, prior start * if knownRun observed start = some endpoint then 1 else 0
noncomputable def properSuffixCount : {n : Nat} → (Fin n → State → Option State) → State → Nat
  | 0, _, _ => 0
  | _ + 1, observed, endpoint => knownCount (Fin.tail observed) endpoint + properSuffixCount (Fin.tail observed) endpoint
omit [Nonempty State] in
theorem knownCount_empty (observed : Fin 0 → State → Option State) (endpoint : State) : knownCount observed endpoint = 1 := by
  simp [knownCount, knownRun]
omit [Nonempty State] in
theorem knownMass_empty (prior : PMF State) (observed : Fin 0 → State → Option State) (endpoint : State) :
    knownMass prior observed endpoint = prior endpoint := by
  simp [knownMass, knownRun]
omit [Fintype State] [Nonempty State] in
theorem knownMass_pure {n : Nat} (value : State) (observed : Fin n → State → Option State) (endpoint : State) :
    knownMass (PMF.pure value) observed endpoint = if knownRun observed value = some endpoint then 1 else 0 := by
  simpa only [knownMass, PMF.probOutput_eq_apply, PMF.monad_pure_eq_pure] using
    (tsum_probOutput_pure_mul (m := PMF) value (fun start => if knownRun observed start = some endpoint then 1 else 0))
theorem knownMass_uniform {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    knownMass (PMF.uniformOfFintype State) observed endpoint =
      (knownCount observed endpoint : ENNReal) / Fintype.card State := by
  rw [knownMass, tsum_fintype, knownCount, Nat.cast_sum]
  simp only [PMF.uniformOfFintype_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, div_eq_mul_inv,
    Finset.mul_sum, mul_comm]
theorem advance_knownMass_le {n : Nat} (prior : PMF State) (observed : Fin (n + 1) → State → Option State) (endpoint : State) :
    knownMass (prior.bind (fun input => rowLaw (observed 0 input))) (Fin.tail observed) endpoint ≤
      knownMass prior observed endpoint + (knownCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State := by
  rw [knownMass, expectation_bind]
  calc
    _ ≤ ∑' input, prior input *
        ((if knownRun observed input = some endpoint then 1 else 0) +
          (knownCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State) := by
      apply ENNReal.tsum_le_tsum
      intro input
      apply mul_le_mul' le_rfl
      change knownMass (rowLaw (observed 0 input)) (Fin.tail observed) endpoint ≤ _
      cases hrow : observed 0 input with
      | none => simp only [rowLaw, knownMass_uniform, knownRun, hrow, Option.bind_none, reduceCtorEq, if_false, zero_add, le_refl]
      | some value =>
          simp only [rowLaw, knownMass_pure, knownRun, hrow, Option.bind_some]
          exact _root_.le_add_of_nonneg_right bot_le
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, knownMass]
theorem kernel_le_knownMass {n : Nat} (prior : PMF State) (observed : Fin n → State → Option State) (endpoint : State) :
    prior.bind (kernel observed) endpoint ≤
      knownMass prior observed endpoint + (properSuffixCount observed endpoint : ENNReal) / Fintype.card State := by
  induction n generalizing prior with
  | zero => simp [kernel, knownMass_empty, properSuffixCount]
  | succ n ih =>
      have h := ih (prior.bind (fun input => rowLaw (observed 0 input))) (Fin.tail observed)
      have hstep := advance_knownMass_le prior observed endpoint
      calc
        _ ≤ knownMass (prior.bind (fun input => rowLaw (observed 0 input))) (Fin.tail observed) endpoint +
            (properSuffixCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State := by
          simpa only [kernel, PMF.bind_bind] using h
        _ ≤ (knownMass prior observed endpoint + (knownCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State) +
            (properSuffixCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State := _root_.add_le_add hstep le_rfl
        _ = _ := by rw [properSuffixCount, Nat.cast_add, ENNReal.add_div, add_assoc]
theorem meanPreimages_le_suffixCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    meanPreimages observed endpoint ≤ (knownCount observed endpoint + properSuffixCount observed endpoint : Nat) := by
  rw [meanPreimages_eq]
  have h := mul_le_mul' (le_refl (Fintype.card State : ENNReal)) (kernel_le_knownMass (PMF.uniformOfFintype State) observed endpoint)
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa only [knownMass_uniform, Nat.cast_add, div_eq_mul_inv, mul_add, mul_left_comm (Fintype.card State : ENNReal),
    ENNReal.mul_inv_cancel hcard (by finiteness), mul_one] using h
def Contact {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : Prop :=
  ∃ step : Fin n, step.val + 1 = n ∧ ∃ input, observed step input = some endpoint
omit [Fintype State] [DecidableEq State] [Nonempty State] in
theorem contact_tail {n : Nat} (observed : Fin (n + 1) → State → Option State) (endpoint : State)
    (h : Contact (Fin.tail observed) endpoint) : Contact observed endpoint := by
  obtain ⟨step, hstep, input, hinput⟩ := h
  exact ⟨step.succ, by simpa only [Fin.val_succ] using congrArg Nat.succ hstep, input, hinput⟩
omit [Fintype State] [DecidableEq State] [Nonempty State] in
theorem knownRun_contact {n : Nat} (observed : Fin (n + 1) → State → Option State) (start endpoint : State)
    (h : knownRun observed start = some endpoint) : Contact observed endpoint := by
  induction n generalizing start with
  | zero =>
      have hrow : observed 0 start = some endpoint := by
        cases hstart : observed 0 start <;> simpa only [knownRun, hstart, Option.bind_none, Option.bind_some] using h
      exact ⟨0, rfl, start, hrow⟩
  | succ n ih =>
      rw [knownRun, Option.bind_eq_some_iff] at h
      obtain ⟨value, _, hvalue⟩ := h
      exact contact_tail observed endpoint (ih (Fin.tail observed) value hvalue)
omit [Nonempty State] in
theorem knownCount_eq_zero_of_no_contact {n : Nat} (observed : Fin (n + 1) → State → Option State) (endpoint : State)
    (h : ¬Contact observed endpoint) : knownCount observed endpoint = 0 := by
  unfold knownCount
  apply Finset.sum_eq_zero
  intro start _
  exact if_neg (fun hrun => h (knownRun_contact observed start endpoint hrun))
omit [Nonempty State] in
theorem suffixCount_le_one_of_no_contact {n : Nat} (observed : Fin n → State → Option State) (endpoint : State)
    (h : ¬Contact observed endpoint) : knownCount observed endpoint + properSuffixCount observed endpoint ≤ 1 := by
  induction n with
  | zero => simp only [knownCount_empty, properSuffixCount, Nat.add_zero, le_refl]
  | succ n ih =>
      rw [knownCount_eq_zero_of_no_contact observed endpoint h, properSuffixCount, Nat.zero_add]
      exact ih (Fin.tail observed) (fun htail => h (contact_tail observed endpoint htail))
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
def Extends {n : Nat} (before after : Fin n → State → Option State) : Prop :=
  ∀ step input answer, before step input = some answer → after step input = some answer
omit [Fintype State] [DecidableEq State] in
theorem Extends.tail {n : Nat} {before after : Fin (n + 1) → State → Option State} (h : Extends before after) :
    Extends (Fin.tail before) (Fin.tail after) := fun step input answer => h step.succ input answer
omit [Fintype State] [DecidableEq State] in
theorem knownRun_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after)
    (start endpoint : State) (hknown : knownRun before start = some endpoint) : knownRun after start = some endpoint := by
  induction n generalizing start with
  | zero => exact hknown
  | succ n ih =>
      rw [knownRun, Option.bind_eq_some_iff] at hknown ⊢
      obtain ⟨value, hvalue, hknown⟩ := hknown
      exact ⟨value, h 0 start value hvalue, ih h.tail value hknown⟩
theorem knownCount_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after) (endpoint : State) :
    knownCount before endpoint ≤ knownCount after endpoint := by
  apply Finset.sum_le_sum
  intro start _
  by_cases hknown : knownRun before start = some endpoint
  · simp only [if_pos hknown, if_pos (knownRun_mono h start endpoint hknown), le_refl]
  · simp only [if_neg hknown, Nat.zero_le]
noncomputable def targetCount : {n : Nat} → (Fin n → State → Option State) → State → Nat
  | 0, _, _ => 0
  | _ + 1, observed, endpoint => knownCount observed endpoint + targetCount (Fin.tail observed) endpoint
noncomputable def completedCount {n : Nat} (observed : Fin n → State → Option State) : Nat :=
  ∑ endpoint : State, targetCount observed endpoint
noncomputable def pendingCount {n : Nat} (observed : Fin n → State → Option State) : Nat :=
  queryCount observed - completedCount observed
theorem suffixCount_eq_targetCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    knownCount observed endpoint + properSuffixCount observed endpoint = 1 + targetCount observed endpoint := by
  induction n with
  | zero => simp only [knownCount_empty, properSuffixCount, targetCount, Nat.add_zero]
  | succ n ih =>
      rw [properSuffixCount, targetCount, ih]
      omega
theorem targetCount_eq_zero_of_no_contact {n : Nat} (observed : Fin n → State → Option State) (endpoint : State)
    (h : ¬Contact observed endpoint) : targetCount observed endpoint = 0 := by
  have hbound := suffixCount_le_one_of_no_contact observed endpoint h
  rw [suffixCount_eq_targetCount] at hbound
  omega
theorem targetCount_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after) (endpoint : State) :
    targetCount before endpoint ≤ targetCount after endpoint := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact Nat.add_le_add (knownCount_mono h endpoint) (ih h.tail)
theorem completedCount_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after) :
    completedCount before ≤ completedCount after :=
  Finset.sum_le_sum fun endpoint _ => targetCount_mono h endpoint
omit [DecidableEq State] in
theorem queriedCount_eq_sum (observed : State → Option State) :
    queriedCount observed = ∑ input : State, if observed input = none then 0 else 1 := by
  rw [queriedCount, unqueried, Finset.card_filter]
  have hsplit : (∑ input : State, if observed input = none then 1 else 0) +
      (∑ input : State, if observed input = none then 0 else 1) = Fintype.card State := by
    rw [← Finset.sum_add_distrib]
    simp only [ite_add_ite, Nat.add_zero, Nat.zero_add, ite_self, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  omega
theorem knownCount_sum {n : Nat} (observed : Fin n → State → Option State) :
    (∑ endpoint : State, knownCount observed endpoint) = ∑ start : State, if (knownRun observed start).isSome then 1 else 0 := by
  simp only [knownCount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro start _
  cases knownRun observed start <;> simp
theorem knownCount_sum_le_queried {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    (∑ endpoint : State, knownCount observed endpoint) ≤ queriedCount (observed 0) := by
  rw [knownCount_sum, queriedCount_eq_sum]
  apply Finset.sum_le_sum
  intro start _
  cases hrow : observed 0 start with
  | none => simp [knownRun, hrow]
  | some value =>
      simp only [reduceCtorEq, if_false]
      split <;> omega
theorem completedCount_le_queryCount {n : Nat} (observed : Fin n → State → Option State) :
    completedCount observed ≤ queryCount observed := by
  induction n with
  | zero => simp [completedCount, targetCount, queryCount]
  | succ n ih =>
      simp only [completedCount, targetCount, Finset.sum_add_distrib, queryCount, Fin.sum_univ_succ]
      exact Nat.add_le_add (knownCount_sum_le_queried observed) (ih (Fin.tail observed))
theorem pendingCount_partition {n : Nat} (observed : Fin n → State → Option State) :
    pendingCount observed + completedCount observed = queryCount observed :=
  Nat.sub_add_cancel (completedCount_le_queryCount observed)
omit [Fintype State] in
theorem record_extends {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State) (answer : State)
    (hconsistent : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer) :
    Extends observed (record observed query answer) := by
  intro step input old hold
  by_cases hstep : step = query.1
  · subst step
    by_cases hinput : input = query.2
    · subst input
      have heq : old = answer := by rcases hconsistent with h | h <;> simp_all
      simp [record, heq]
    · simpa only [record, Function.update_self, Function.update_of_ne hinput] using hold
  · simpa only [record, Function.update_of_ne hstep] using hold
theorem pendingCount_record_le {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State) (answer : State)
    (hconsistent : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer) :
    pendingCount (record observed query answer) ≤ pendingCount observed + 1 := by
  have hbefore := pendingCount_partition observed
  have hafter := pendingCount_partition (record observed query answer)
  have htotal := queryCount_record_le observed query answer
  have hdone := completedCount_mono (record_extends observed query answer hconsistent)
  omega
theorem completedCount_add_target_le {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after)
    (endpoint : State) (hcontact : ¬Contact before endpoint) :
    completedCount before + targetCount after endpoint ≤ completedCount after := by
  have hzero := targetCount_eq_zero_of_no_contact before endpoint hcontact
  have hrest := Finset.sum_le_sum (s := Finset.univ.erase endpoint) fun other _ => targetCount_mono h other
  rw [completedCount, completedCount,
    ← Finset.add_sum_erase Finset.univ (fun other => targetCount before other) (Finset.mem_univ endpoint),
    ← Finset.add_sum_erase Finset.univ (fun other => targetCount after other) (Finset.mem_univ endpoint), hzero]
  omega
theorem first_contact_density_charge [Nonempty State] {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (answer endpoint : State) (hcontact : ¬Contact observed endpoint)
    (hconsistent : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer) :
    meanPreimages (record observed query answer) endpoint + (pendingCount (record observed query answer) : ENNReal) ≤
      (pendingCount observed + 2 : Nat) := by
  have hbefore := pendingCount_partition observed
  have hafter := pendingCount_partition (record observed query answer)
  have htotal := queryCount_record_le observed query answer
  have hdone := completedCount_add_target_le (record_extends observed query answer hconsistent) endpoint hcontact
  have hcount : 1 + targetCount (record observed query answer) endpoint + pendingCount (record observed query answer) ≤
      pendingCount observed + 2 := by omega
  have hdensity := meanPreimages_le_suffixCount (record observed query answer) endpoint
  rw [suffixCount_eq_targetCount] at hdensity
  exact (_root_.add_le_add hdensity le_rfl).trans (by exact_mod_cast hcount)
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
omit [Fintype State] [DecidableEq State] in
theorem knownRun_isSome_eq_of_last {n : Nat} (before after : Fin n → State → Option State)
    (hearly : ∀ step input, step.val + 1 ≠ n → before step input = after step input)
    (hlast : ∀ step input, step.val + 1 = n → (before step input).isSome = (after step input).isSome)
    (start : State) : (knownRun before start).isSome = (knownRun after start).isSome := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero =>
          simpa [knownRun] using hlast 0 start rfl
      | succ n =>
          have hhead := hearly 0 start (by simp)
          have htail := ih (Fin.tail before) (Fin.tail after)
            (fun step input h => hearly step.succ input (by simpa only [Fin.val_succ, Nat.succ_add, Nat.succ_ne_succ_iff] using h))
            (fun step input h => hlast step.succ input (by simpa only [Fin.val_succ, Nat.succ_add, Nat.succ.injEq] using h))
          simp only [knownRun, hhead]
          cases after 0 start with
          | none => rfl
          | some value => exact htail value
theorem completedCount_eq_of_last {n : Nat} (before after : Fin n → State → Option State)
    (hearly : ∀ step input, step.val + 1 ≠ n → before step input = after step input)
    (hlast : ∀ step input, step.val + 1 = n → (before step input).isSome = (after step input).isSome) :
    completedCount before = completedCount after := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (∑ endpoint : State, (knownCount before endpoint + targetCount (Fin.tail before) endpoint)) =
        ∑ endpoint : State, (knownCount after endpoint + targetCount (Fin.tail after) endpoint)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, knownCount_sum, knownCount_sum]
      congr 1
      · exact Finset.sum_congr rfl fun start _ => congrArg (fun b : Bool => if b then 1 else 0)
          (knownRun_isSome_eq_of_last before after hearly hlast start)
      · exact ih (Fin.tail before) (Fin.tail after)
          (fun step input h => hearly step.succ input (by simpa only [Fin.val_succ, Nat.succ_add, Nat.succ_ne_succ_iff] using h))
          (fun step input h => hlast step.succ input (by simpa only [Fin.val_succ, Nat.succ_add, Nat.succ.injEq] using h))
omit [Fintype State] in
theorem record_isSome_eq {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (first second : State) (step : Fin n) (input : State) :
    (record observed query first step input).isSome = (record observed query second step input).isSome := by
  by_cases hs : step = query.1
  · subst step
    by_cases hi : input = query.2
    · subst input; simp [record]
    · simp only [record, Function.update_self, Function.update_of_ne hi]
  · simp only [record, Function.update_of_ne hs]
theorem queryCount_record_answer_eq {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (first second : State) : queryCount (record observed query first) = queryCount (record observed query second) := by
  unfold queryCount
  apply Finset.sum_congr rfl
  intro step _
  rw [queriedCount_eq_sum, queriedCount_eq_sum]
  apply Finset.sum_congr rfl
  intro input _
  have h := record_isSome_eq observed query first second step input
  cases hfirst : record observed query first step input <;> cases hsecond : record observed query second step input <;> simp_all
theorem pendingCount_record_last_answer_eq {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (hlast : query.1.val + 1 = n) (first second : State) :
    pendingCount (record observed query first) = pendingCount (record observed query second) := by
  unfold pendingCount
  rw [queryCount_record_answer_eq observed query first second]
  congr 1
  apply completedCount_eq_of_last
  · intro step input hearly
    have hs : step ≠ query.1 := fun h => hearly (by simpa only [h] using hlast)
    simp only [record, Function.update_of_ne hs]
  · intro step input _
    exact record_isSome_eq observed query first second step input
omit [Fintype State] [DecidableEq State] in
theorem contact_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after)
    (endpoint : State) (hc : Contact before endpoint) : Contact after endpoint := by
  obtain ⟨step, hstep, input, hinput⟩ := hc
  exact ⟨step, hstep, input, h step input endpoint hinput⟩
omit [Fintype State] in
theorem contact_record_iff {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (answer endpoint : State) (hc : ¬Contact observed endpoint) :
    Contact (record observed query answer) endpoint ↔ query.1.val + 1 = n ∧ answer = endpoint := by
  constructor
  · rintro ⟨step, hstep, input, hinput⟩
    by_cases hs : step = query.1
    · subst step
      by_cases hi : input = query.2
      · subst input
        exact ⟨hstep, by simpa only [record, Function.update_self, Option.some.injEq] using hinput⟩
      · exact False.elim (hc ⟨query.1, hstep, input, by simpa only [record, Function.update_self, Function.update_of_ne hi] using hinput⟩)
    · exact False.elim (hc ⟨step, hstep, input, by simpa only [record, Function.update_of_ne hs] using hinput⟩)
  · rintro ⟨hlast, rfl⟩
    exact ⟨query.1, hlast, query.2, by simp only [record, Function.update_self]⟩
omit [Fintype State] in
theorem record_of_known {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (answer : State) (h : observed query.1 query.2 = some answer) : record observed query answer = observed := by
  simp only [record, ← h, Function.update_eq_self]
theorem meanPreimages_observe [Nonempty State] {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * meanPreimages (record observed query answer) endpoint) =
      meanPreimages observed endpoint := by
  simp only [meanPreimages, ← ENNReal.tsum_mul_left, ← mul_assoc, completeTables_observe_mass, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp
end SphincsSecurity.Concrete.PartialChainEndpoint
end
end
-- ==== merged from SphincsSecurity_Proof_Chains_AdaptiveChainPotential ====
section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
theorem expectation_pure {Result : Type} (result : Result) (payoff : Result → ENNReal) :
    (∑' output, PMF.pure result output * payoff output) = payoff result := by
  simpa only [PMF.probOutput_eq_apply, PMF.monad_pure_eq_pure] using
    tsum_probOutput_pure_mul (m := PMF) result payoff
theorem expectation_add {Result : Type} (law : PMF Result) (first second : Result → ENNReal) :
    (∑' result, law result * (first result + second result)) =
      (∑' result, law result * first result) + ∑' result, law result * second result := by
  simp only [mul_add, ENNReal.tsum_add]
theorem expectation_scale {Result : Type} (law : PMF Result) (factor : ENNReal) (payoff : Result → ENNReal) :
    (∑' result, law result * (factor * payoff result)) = factor * ∑' result, law result * payoff result := by
  simp only [mul_left_comm _ factor, ENNReal.tsum_mul_left]
theorem expectation_const {Result : Type} (law : PMF Result) (value : ENNReal) :
    (∑' result, law result * value) = value := by
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result Next : Type}
theorem lazyRun_map (auxiliary : QueryImpl auxSpec PMF) (computation : OracleComp (auxSpec + PrefixSpec n State) Result)
    (f : Result → Next) (observed : Fin n → State → Option State) :
    lazyRun auxiliary (f <$> computation) observed = (lazyRun auxiliary computation observed).map (fun result => (f result.1, result.2)) := by
  simp only [lazyRun, simulateQ_map, StateT.run_map, PMF.monad_map_eq_map]
theorem lazyRun_potential_le (auxiliary : QueryImpl auxSpec PMF)
    (potential : (Fin n → State → Option State) → ENNReal) (rate : ENNReal)
    (hstep : ∀ input observed,
      (∑' result, (lazyImpl auxiliary input).run observed result * potential result.2) ≤
        potential observed + rate * ((if IsPrefixQuery input then 1 else 0 : Nat) : ENNReal))
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * potential result.2) ≤
      potential observed + rate *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing observed with
  | pure result => simp only [QueryCap.counted_pure, lazyRun_pure, expectation_pure, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | query_bind input next ih =>
      simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
        expectation_bind, expectation_map, Nat.cast_add, expectation_add, expectation_const]
      calc
        _ ≤ ∑' output, (lazyImpl auxiliary input).run observed output *
            (potential output.2 + rate * ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery (next output.1)) output.2 result *
              (result.1.2 : ENNReal)) := ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl (ih output.1 output.2)
        _ = (∑' output, (lazyImpl auxiliary input).run observed output * potential output.2) +
            rate * ∑' output, (lazyImpl auxiliary input).run observed output *
              ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery (next output.1)) output.2 result * (result.1.2 : ENNReal) := by
          rw [expectation_add, expectation_scale]
        _ ≤ _ := by
          rw [mul_add, ← add_assoc]
          exact _root_.add_le_add (hstep input observed) le_rfl
end SphincsSecurity.Concrete.PartialChainEndpoint
end
-- ==== merged from SphincsSecurity_Proof_Chains_PartialChainContactCount ====
section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
noncomputable def contactCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : Nat :=
  ∑ query : Fin n × State, if query.1.val + 1 = n ∧ observed query.1 query.2 = some endpoint then 1 else 0
theorem contactCount_empty {n : Nat} (endpoint : State) : contactCount (n := n) (fun _ _ => none) endpoint = 0 := by
  simp [contactCount]
theorem contactCount_succ {n : Nat} (observed : Fin (n + 1) → State → Option State) (endpoint : State) :
    contactCount observed endpoint = ∑ input : State, if observed (Fin.last n) input = some endpoint then 1 else 0 := by
  rw [contactCount, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp only [Fin.val_last, true_and]
  · intro step _ hstep
    have hn : step.val + 1 ≠ n + 1 := by
      intro hn
      apply hstep
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    simp only [hn, false_and, if_false, Finset.sum_const_zero]
  · simp
theorem contactCount_tail {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State) :
    contactCount (Fin.tail observed) endpoint = contactCount observed endpoint := by
  simp only [contactCount_succ, Fin.tail, Fin.succ_last]
theorem contactCount_single (observed : Fin 1 → State → Option State) (endpoint : State) :
    contactCount observed endpoint = knownCount observed endpoint := by
  rw [contactCount_succ, knownCount]
  apply Finset.sum_congr rfl
  intro input _
  cases hrow : observed 0 input <;> simp [knownRun, hrow]
omit [Fintype State] in
theorem record_at_other {n : Nat} (observed : Fin n → State → Option State) (query other : Fin n × State)
    (answer : State) (h : other ≠ query) : record observed query answer other.1 other.2 = observed other.1 other.2 := by
  by_cases hs : other.1 = query.1
  · have hi : other.2 ≠ query.2 := fun heq => h (Prod.ext hs heq)
    simp only [record, hs, Function.update_self, Function.update_of_ne hi]
  · simp only [record, Function.update_of_ne hs]
theorem contactCount_record_fresh {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (answer endpoint : State) (hfresh : observed query.1 query.2 = none) :
    contactCount (record observed query answer) endpoint =
      contactCount observed endpoint + if query.1.val + 1 = n ∧ answer = endpoint then 1 else 0 := by
  have hfun : (fun other : Fin n × State =>
      if other.1.val + 1 = n ∧ record observed query answer other.1 other.2 = some endpoint then 1 else 0) =
      Function.update (fun other : Fin n × State => if other.1.val + 1 = n ∧ observed other.1 other.2 = some endpoint then 1 else 0)
        query (if query.1.val + 1 = n ∧ answer = endpoint then 1 else 0) := by
    funext other
    by_cases ho : other = query
    · subst other
      simp only [record, Function.update_self, Option.some.injEq]
    · simp only [record_at_other observed query other answer ho, Function.update_of_ne ho]
  rw [contactCount, hfun, Finset.sum_update_of_mem (Finset.mem_univ query), Finset.sdiff_singleton_eq_erase,
    contactCount, ← Finset.add_sum_erase Finset.univ
      (fun other : Fin n × State => if other.1.val + 1 = n ∧ observed other.1 other.2 = some endpoint then 1 else 0)
      (Finset.mem_univ query)]
  simp only [hfresh, reduceCtorEq, and_false, if_false, Nat.zero_add, Nat.add_comm]
theorem contactCount_observe_increment_le [Nonempty State] {n : Nat}
    (value increment : Nat → ENNReal) (hincrement : ∀ k, value (k + 1) = value k + increment k)
    (observed : Fin n → State → Option State) (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * value (contactCount (record observed query answer) endpoint)) ≤
      value (contactCount observed endpoint) + increment (contactCount observed endpoint) / Fintype.card State := by
  cases hrow : observed query.1 query.2 with
  | some answer =>
      simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow]
      exact _root_.le_add_of_nonneg_right bot_le
  | none =>
      simp only [rowLaw, contactCount_record_fresh observed query _ endpoint hrow]
      by_cases hlast : query.1.val + 1 = n
      · simp only [hlast, true_and]
        have hvalue (answer : State) : value (contactCount observed endpoint + if answer = endpoint then 1 else 0) =
            value (contactCount observed endpoint) + if answer = endpoint then increment (contactCount observed endpoint) else 0 := by
          by_cases heq : answer = endpoint <;> simp only [heq, if_true, if_false, hincrement, add_zero]
        simp only [hvalue, expectation_add, expectation_const]
        simp only [mul_ite, mul_zero, tsum_ite_eq, PMF.uniformOfFintype_apply]
        exact le_of_eq (by rw [div_eq_mul_inv, mul_comm])
      · simp only [hlast, false_and, if_false, Nat.add_zero, expectation_const]
        exact _root_.le_add_of_nonneg_right bot_le
theorem contactCount_observe_le [Nonempty State] {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * (contactCount (record observed query answer) endpoint : ENNReal)) ≤
      (contactCount observed endpoint : ENNReal) + 1 / Fintype.card State :=
  contactCount_observe_increment_le (fun k => k) (fun _ => 1) (fun k => by simp only [Nat.cast_add, Nat.cast_one]) observed query endpoint
def contactFactorial (k : Nat) : Nat := k * (k - 1)
theorem contactFactorial_succ (k : Nat) : contactFactorial (k + 1) = contactFactorial k + 2 * k := by
  cases k with
  | zero => rfl
  | succ k => simp only [contactFactorial, Nat.add_sub_cancel]; ring
theorem contactFactorial_observe_le [Nonempty State] {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * (contactFactorial (contactCount (record observed query answer) endpoint) : ENNReal)) ≤
      (contactFactorial (contactCount observed endpoint) : ENNReal) + (2 * contactCount observed endpoint : Nat) / (Fintype.card State : ENNReal) :=
  contactCount_observe_increment_le (fun k => contactFactorial k) (fun k => (2 * k : Nat))
    (fun k => by rw [contactFactorial_succ, Nat.cast_add]) observed query endpoint
end SphincsSecurity.Concrete.PartialChainEndpoint
end
-- ==== merged from SphincsSecurity_Proof_Chains_PartialChainTwoEdgeCompensation ====
section

section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
def TwoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State) : Prop :=
  ∃ start middle, observed (Fin.last n).castSucc start = some middle ∧ observed (Fin.last (n + 1)) middle = some endpoint
omit [Fintype State] [DecidableEq State] in
theorem twoEdge_mono {n : Nat} {before after : Fin (n + 2) → State → Option State} (hextends : Extends before after)
    (endpoint : State) (h : TwoEdge before endpoint) : TwoEdge after endpoint := by
  obtain ⟨start, middle, hfirst, hlast⟩ := h
  exact ⟨start, middle, hextends _ _ _ hfirst, hextends _ _ _ hlast⟩
omit [Fintype State] [DecidableEq State] in
theorem twoEdge_tail {n : Nat} (observed : Fin (n + 3) → State → Option State) (endpoint : State)
    (h : TwoEdge (Fin.tail observed) endpoint) : TwoEdge observed endpoint := by
  obtain ⟨start, middle, hfirst, hlast⟩ := h
  have hindex : (Fin.last n).castSucc.succ = (Fin.last (n + 1)).castSucc := by apply Fin.ext; rfl
  exact ⟨start, middle, by simpa only [Fin.tail, hindex] using hfirst, by simpa only [Fin.tail, Fin.succ_last] using hlast⟩
omit [Fintype State] [DecidableEq State] in
theorem knownRun_twoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (start endpoint : State)
    (h : knownRun observed start = some endpoint) : TwoEdge observed endpoint := by
  induction n generalizing start with
  | zero =>
      rw [knownRun, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hfirst, hlast⟩ := h
      change (observed 1 middle).bind (fun value => some value) = some endpoint at hlast
      have hrow : observed 1 middle = some endpoint := by
        cases hrow : observed 1 middle <;> simpa only [hrow, Option.bind_none, Option.bind_some] using hlast
      exact ⟨start, middle, hfirst, hrow⟩
  | succ n ih =>
      rw [knownRun, Option.bind_eq_some_iff] at h
      obtain ⟨middle, _, htail⟩ := h
      exact twoEdge_tail observed endpoint (ih (Fin.tail observed) middle htail)
theorem knownCount_eq_zero_of_no_twoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State)
    (h : ¬TwoEdge observed endpoint) : knownCount observed endpoint = 0 := by
  unfold knownCount
  apply Finset.sum_eq_zero
  intro start _
  exact if_neg (fun hrun => h (knownRun_twoEdge observed start endpoint hrun))
theorem targetCount_eq_contactCount_of_no_twoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State)
    (h : ¬TwoEdge observed endpoint) : targetCount observed endpoint = contactCount observed endpoint := by
  induction n with
  | zero =>
      rw [targetCount, knownCount_eq_zero_of_no_twoEdge observed endpoint h, Nat.zero_add, targetCount, targetCount, Nat.add_zero,
        ← contactCount_single, contactCount_tail]
  | succ n ih =>
      rw [targetCount, knownCount_eq_zero_of_no_twoEdge observed endpoint h, Nat.zero_add,
        ih (Fin.tail observed) (fun htail => h (twoEdge_tail observed endpoint htail)), contactCount_tail]
theorem meanPreimages_le_contactCount_of_no_twoEdge [Nonempty State] {n : Nat}
    (observed : Fin (n + 2) → State → Option State) (endpoint : State) (h : ¬TwoEdge observed endpoint) :
    meanPreimages observed endpoint ≤ (1 + contactCount observed endpoint : Nat) := by
  have hbound := meanPreimages_le_suffixCount observed endpoint
  rwa [suffixCount_eq_targetCount, targetCount_eq_contactCount_of_no_twoEdge observed endpoint h] at hbound
omit [Fintype State] in
theorem twoEdge_record_earlier {n : Nat} (observed : Fin (n + 2) → State → Option State) (query : Fin (n + 2) × State)
    (answer endpoint : State) (hfirst : (Fin.last n).castSucc ≠ query.1) (hlast : Fin.last (n + 1) ≠ query.1) :
    TwoEdge (record observed query answer) endpoint ↔ TwoEdge observed endpoint := by
  simp only [TwoEdge, record, Function.update_of_ne hfirst, Function.update_of_ne hlast]
omit [Fintype State] in
theorem twoEdge_record_last {n : Nat} (observed : Fin (n + 2) → State → Option State) (input answer endpoint : State)
    (h : ¬TwoEdge observed endpoint) :
    TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint ↔
      answer = endpoint ∧ ∃ start, observed (Fin.last n).castSucc start = some input := by
  have hindex : (Fin.last n).castSucc ≠ Fin.last (n + 1) := by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_castSucc, Fin.val_last] at hv; omega
  constructor
  · rintro ⟨start, middle, hfirst, hlast⟩
    have hfirst' : observed (Fin.last n).castSucc start = some middle := by
      simpa only [record, Function.update_of_ne hindex] using hfirst
    by_cases hm : middle = input
    · subst middle
      exact ⟨by simpa only [record, Function.update_self, Option.some.injEq] using hlast, start, hfirst'⟩
    · exact False.elim (h ⟨start, middle, hfirst', by simpa only [record, Function.update_self, Function.update_of_ne hm] using hlast⟩)
  · rintro ⟨rfl, start, hfirst⟩
    exact ⟨start, input, by simpa only [record, Function.update_of_ne hindex] using hfirst,
      by simp only [record, Function.update_self]⟩
omit [Fintype State] in
theorem twoEdge_record_penultimate {n : Nat} (observed : Fin (n + 2) → State → Option State) (input answer endpoint : State)
    (h : ¬TwoEdge observed endpoint) :
    TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint ↔ observed (Fin.last (n + 1)) answer = some endpoint := by
  have hindex : Fin.last (n + 1) ≠ (Fin.last n).castSucc := by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_castSucc, Fin.val_last] at hv; omega
  constructor
  · rintro ⟨start, middle, hfirst, hlast⟩
    have hlast' : observed (Fin.last (n + 1)) middle = some endpoint := by
      simpa only [record, Function.update_of_ne hindex] using hlast
    by_cases hs : start = input
    · subst start
      have hm : answer = middle := by simpa only [record, Function.update_self, Option.some.injEq] using hfirst
      simpa only [hm] using hlast'
    · exact False.elim (h ⟨start, middle, by simpa only [record, Function.update_self, Function.update_of_ne hs] using hfirst, hlast'⟩)
  · intro hlast
    exact ⟨input, answer, by simp only [record, Function.update_self], by simpa only [record, Function.update_of_ne hindex] using hlast⟩
theorem twoEdge_last_probability [Nonempty State] {n : Nat}
    (observed : Fin (n + 2) → State → Option State) (input endpoint : State)
    (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last (n + 1)) input = none) :
    Pr[fun answer => TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint |
      rowLaw (observed (Fin.last (n + 1)) input)] =
        if ∃ start, observed (Fin.last n).castSucc start = some input then 1 / (Fintype.card State : ENNReal) else 0 := by
  classical
  simp only [hfresh, rowLaw, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    twoEdge_record_last observed input _ endpoint h]
  by_cases hp : ∃ start, observed (Fin.last n).castSucc start = some input
  · simp only [hp, and_true, if_true, tsum_ite_eq, PMF.uniformOfFintype_apply, one_div]
  · simp only [hp, and_false, if_false, tsum_zero]
theorem twoEdge_penultimate_probability [Nonempty State] {n : Nat}
    (observed : Fin (n + 2) → State → Option State) (input endpoint : State)
    (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last n).castSucc input = none) :
    Pr[fun answer => TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint |
      rowLaw (observed (Fin.last n).castSucc input)] = (contactCount observed endpoint : ENNReal) / Fintype.card State := by
  classical
  simp only [hfresh, rowLaw, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    twoEdge_record_penultimate observed input _ endpoint h, PMF.uniformOfFintype_apply, tsum_fintype,
    contactCount_succ, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, div_eq_mul_inv,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
private theorem weighted_event_le_bound {Result : Type} (law : PMF Result) (weight : Result → ENNReal)
    (event : Result → Prop) [DecidablePred event] (bound : ENNReal) (hbound : ∀ result, weight result ≤ bound) :
    (∑' result, law result * (weight result * if event result then 1 else 0)) ≤ bound * Pr[event | law] := by
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hevent : event result
  · simpa only [hevent, if_true, mul_one, PMF.probOutput_eq_apply, mul_comm] using mul_le_mul' (hbound result) (le_refl (law result))
  · simp only [hevent, if_false, mul_zero, le_refl]
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
omit [DecidableEq State] in
theorem kernel_snoc {n : Nat} (before : Fin n → State → Option State) (last : State → Option State) :
    kernel (Fin.snoc before last) = fun start => (kernel before start).bind (fun input => rowLaw (last input)) := by
  induction n with
  | zero => funext start; simp [kernel, Fin.snoc_zero]
  | succ n ih =>
      funext start
      have hs : Fin.snoc before last = @Fin.cons (n + 1) (fun _ => State → Option State) (before 0) (Fin.snoc (Fin.tail before) last) := by
        rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
      rw [hs, kernel, Fin.cons_zero, Fin.tail_cons]
      rw [ih]
      simp only [kernel, PMF.bind_bind]
theorem row_update_charge (prior : PMF State) (observed : State → Option State) (next : State → PMF State)
    (input answer endpoint : State) :
    prior.bind (fun start => (rowLaw (Function.update observed input (some answer) start)).bind next) endpoint ≤
      prior.bind (fun start => (rowLaw (observed start)).bind next) endpoint + prior input := by
  rw [PMF.bind_apply]
  calc
    _ ≤ ∑' start, prior start * (((rowLaw (observed start)).bind next) endpoint + if start = input then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro start
      apply mul_le_mul' le_rfl
      by_cases hs : start = input
      · rw [if_pos hs]
        exact (PMF.coe_le_one _ endpoint).trans (_root_.le_add_of_nonneg_left bot_le)
      · simp only [Function.update_of_ne hs, if_neg hs, add_zero, le_refl]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, mul_ite, mul_one, mul_zero, tsum_ite_eq, PMF.bind_apply]
theorem meanPreimages_last_update_le {n : Nat} (before : Fin n → State → Option State) (last : State → Option State)
    (input answer endpoint : State) :
    meanPreimages (Fin.snoc before (Function.update last input (some answer))) endpoint ≤
      meanPreimages (Fin.snoc before last) endpoint + meanPreimages before input := by
  have h := row_update_charge ((PMF.uniformOfFintype State).bind (kernel before)) last PMF.pure input answer endpoint
  simp only [PMF.bind_pure] at h
  have hscaled := mul_le_mul' (le_refl (Fintype.card State : ENNReal)) h
  simpa only [meanPreimages_eq, kernel_snoc, PMF.bind_bind, mul_add] using hscaled
theorem meanPreimages_penultimate_update_le {n : Nat} (before : Fin n → State → Option State)
    (penultimate last : State → Option State) (input answer endpoint : State) :
    meanPreimages (Fin.snoc (Fin.snoc before (Function.update penultimate input (some answer))) last) endpoint ≤
      meanPreimages (Fin.snoc (Fin.snoc before penultimate) last) endpoint + meanPreimages before input := by
  have h := row_update_charge ((PMF.uniformOfFintype State).bind (kernel before)) penultimate
    (fun middle => rowLaw (last middle)) input answer endpoint
  have hscaled := mul_le_mul' (le_refl (Fintype.card State : ENNReal)) h
  simpa only [meanPreimages_eq, kernel_snoc, PMF.bind_bind, mul_add] using hscaled
theorem meanPreimages_record_last_le {n : Nat} (observed : Fin (n + 1) → State → Option State)
    (input answer endpoint : State) :
    meanPreimages (record observed (Fin.last n, input) answer) endpoint ≤
      meanPreimages observed endpoint + meanPreimages (Fin.init observed) input := by
  have h := meanPreimages_last_update_le (Fin.init observed) (observed (Fin.last n)) input answer endpoint
  rw [Fin.snoc_init_self] at h
  have hrecord : record observed (Fin.last n, input) answer =
      Fin.snoc (Fin.init observed) (Function.update (observed (Fin.last n)) input (some answer)) := by
    conv_lhs => rw [← Fin.snoc_init_self observed]
    simp only [record, Fin.snoc_last, Fin.update_snoc_last]
  simpa only [hrecord] using h
theorem meanPreimages_record_penultimate_le {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) :
    meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint ≤
      meanPreimages observed endpoint + meanPreimages (Fin.init (Fin.init observed)) input := by
  have h := meanPreimages_penultimate_update_le (Fin.init (Fin.init observed)) ((Fin.init observed) (Fin.last n))
    (observed (Fin.last (n + 1))) input answer endpoint
  rw [Fin.snoc_init_self, Fin.snoc_init_self] at h
  have hrecord : record observed ((Fin.last n).castSucc, input) answer =
      Fin.snoc (Fin.snoc (Fin.init (Fin.init observed))
        (Function.update ((Fin.init observed) (Fin.last n)) input (some answer))) (observed (Fin.last (n + 1))) := by
    conv_lhs => rw [← Fin.snoc_init_self observed, ← Fin.snoc_init_self (Fin.init observed)]
    simp only [record, Fin.snoc_castSucc, Fin.snoc_last, ← Fin.snoc_update, Fin.update_snoc_last]
  simpa only [hrecord] using h
theorem twoEdge_last_density_charge {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (h : ¬TwoEdge observed endpoint) :
    meanPreimages (record observed (Fin.last (n + 1), input) answer) endpoint ≤
      (2 + contactCount observed endpoint + targetCount (Fin.init observed) input : Nat) := by
  have hprefix := meanPreimages_le_suffixCount (Fin.init observed) input
  rw [suffixCount_eq_targetCount] at hprefix
  apply (meanPreimages_record_last_le observed input answer endpoint).trans
  have hsum := _root_.add_le_add (meanPreimages_le_contactCount_of_no_twoEdge observed endpoint h) hprefix
  convert hsum using 1
  push_cast
  ring
theorem twoEdge_penultimate_density_charge {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (h : ¬TwoEdge observed endpoint) :
    meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint ≤
      (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input : Nat) := by
  have hprefix := meanPreimages_le_suffixCount (Fin.init (Fin.init observed)) input
  rw [suffixCount_eq_targetCount] at hprefix
  apply (meanPreimages_record_penultimate_le observed input answer endpoint).trans
  have hsum := _root_.add_le_add (meanPreimages_le_contactCount_of_no_twoEdge observed endpoint h) hprefix
  convert hsum using 1
  push_cast
  ring
theorem twoEdge_last_weighted_risk {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input endpoint : State) (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last (n + 1)) input = none) :
    (∑' answer, rowLaw (observed (Fin.last (n + 1)) input) answer *
      (meanPreimages (record observed (Fin.last (n + 1), input) answer) endpoint *
        if TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint then 1 else 0)) ≤
      if ∃ start, observed (Fin.last n).castSucc start = some input then
        (2 + contactCount observed endpoint + targetCount (Fin.init observed) input : Nat) / (Fintype.card State : ENNReal) else 0 := by
  classical
  apply (weighted_event_le_bound (rowLaw (observed (Fin.last (n + 1)) input))
    (fun answer => meanPreimages (record observed (Fin.last (n + 1), input) answer) endpoint)
    (fun answer => TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint)
    (2 + contactCount observed endpoint + targetCount (Fin.init observed) input : Nat)
    (fun answer => twoEdge_last_density_charge observed input answer endpoint h)).trans_eq
  rw [twoEdge_last_probability observed input endpoint h hfresh]
  split <;> simp only [mul_zero, div_eq_mul_inv, one_mul]
theorem twoEdge_penultimate_weighted_risk {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input endpoint : State) (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last n).castSucc input = none) :
    (∑' answer, rowLaw (observed (Fin.last n).castSucc input) answer *
      (meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint *
        if TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint then 1 else 0)) ≤
      (contactCount observed endpoint * (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input) : Nat) /
        (Fintype.card State : ENNReal) := by
  classical
  apply (weighted_event_le_bound (rowLaw (observed (Fin.last n).castSucc input))
    (fun answer => meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint)
    (fun answer => TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint)
    (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input : Nat)
    (fun answer => twoEdge_penultimate_density_charge observed input answer endpoint h)).trans_eq
  rw [twoEdge_penultimate_probability observed input endpoint h hfresh]
  simp only [Nat.cast_mul, div_eq_mul_inv]
  ring
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
noncomputable def longCompleted : {n : Nat} → (Fin n → State → Option State) → Nat
  | 0, _ => 0
  | 1, _ => 0
  | _ + 2, observed => (∑ endpoint : State, knownCount observed endpoint) + longCompleted (Fin.tail observed)
omit [Fintype State] [DecidableEq State] in
theorem Extends.init {n : Nat} {before after : Fin (n + 1) → State → Option State} (h : Extends before after) :
    Extends (Fin.init before) (Fin.init after) := fun step input answer => h step.castSucc input answer
theorem longCompleted_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after) :
    longCompleted before ≤ longCompleted after := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      cases n with
      | zero => exact le_rfl
      | succ n =>
          exact Nat.add_le_add (Finset.sum_le_sum fun endpoint _ => knownCount_mono h endpoint) (ih h.tail)
theorem knownCount_sum_single (observed : Fin 1 → State → Option State) :
    (∑ endpoint : State, knownCount observed endpoint) = queriedCount (observed 0) := by
  rw [knownCount_sum, queriedCount_eq_sum]
  apply Finset.sum_congr rfl
  intro input _
  cases hrow : observed 0 input <;> simp [knownRun, hrow]
theorem completedCount_eq_longCompleted {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    completedCount observed = longCompleted observed + queriedCount (observed (Fin.last n)) := by
  induction n with
  | zero =>
      simp only [completedCount, targetCount, Nat.add_zero, longCompleted, Nat.zero_add]
      exact knownCount_sum_single observed
  | succ n ih =>
      change (∑ endpoint : State, (knownCount observed endpoint + targetCount (Fin.tail observed) endpoint)) = _
      rw [Finset.sum_add_distrib]
      change (∑ endpoint : State, knownCount observed endpoint) + completedCount (Fin.tail observed) = _
      rw [ih (Fin.tail observed)]
      simp only [longCompleted, Fin.tail, Fin.succ_last, Nat.add_assoc]
omit [DecidableEq State] in
theorem queryCount_split_last {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    queryCount observed = queryCount (Fin.init observed) + queriedCount (observed (Fin.last n)) := by
  simp only [queryCount, Fin.sum_univ_castSucc, Fin.init]
theorem longCompleted_le_prefix_queries {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    longCompleted observed ≤ queryCount (Fin.init observed) := by
  have h := completedCount_le_queryCount observed
  rw [completedCount_eq_longCompleted, queryCount_split_last] at h
  omega
theorem longCompleted_le_queryCount {n : Nat} (observed : Fin n → State → Option State) :
    longCompleted observed ≤ queryCount observed := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
      have h := longCompleted_le_prefix_queries observed
      rw [queryCount_split_last]
      omega
theorem longCompleted_empty {n : Nat} : longCompleted (fun (_ : Fin n) (_ : State) => none) = 0 := by
  have h := longCompleted_le_queryCount (fun (_ : Fin n) (_ : State) => none)
  rw [queryCount_empty] at h
  omega
omit [Fintype State] [DecidableEq State] in
theorem tail_snoc {n : Nat} (before : Fin (n + 1) → State → Option State) (last : State → Option State) :
    @Fin.tail (n + 1) (fun _ => State → Option State) (Fin.snoc before last) =
      (Fin.snoc (Fin.tail before) last : Fin (n + 1) → State → Option State) := by
  have hs : Fin.snoc before last = @Fin.cons (n + 1) (fun _ => State → Option State) (before 0) (Fin.snoc (Fin.tail before) last) := by
    rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
  rw [hs, Fin.tail_cons]
omit [Fintype State] [DecidableEq State] in
theorem knownRun_snoc {n : Nat} (before : Fin n → State → Option State) (last : State → Option State) :
    knownRun (Fin.snoc before last) = fun start => (knownRun before start).bind last := by
  induction n with
  | zero => funext start; simp [knownRun, Fin.snoc_zero]
  | succ n ih =>
      funext start
      have hs : Fin.snoc before last = @Fin.cons (n + 1) (fun _ => State → Option State) (before 0) (Fin.snoc (Fin.tail before) last) := by
        rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
      rw [hs, knownRun, Fin.cons_zero, Fin.tail_cons, ih]
      simp only [knownRun, Option.bind_assoc]
theorem knownCount_sum_last_fresh {n : Nat} (before : Fin n → State → Option State) (last : State → Option State)
    (input answer : State) (hfresh : last input = none) :
    (∑ endpoint : State, knownCount (Fin.snoc before (Function.update last input (some answer))) endpoint) =
      (∑ endpoint : State, knownCount (Fin.snoc before last) endpoint) + knownCount before input := by
  rw [knownCount_sum, knownCount_sum]
  simp only [knownCount, ← Finset.sum_add_distrib, knownRun_snoc]
  apply Finset.sum_congr rfl
  intro start _
  cases hrun : knownRun before start with
  | none => simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, if_false, reduceCtorEq, Nat.add_zero]
  | some value =>
      by_cases hv : value = input
      · subst value
        simp only [Option.bind_some, Function.update_self, hfresh, Option.isSome_some, Option.isSome_none,
          Bool.false_eq_true, if_true, if_false, Nat.zero_add]
      · simp only [Option.bind_some, Function.update_of_ne hv, Option.some.injEq, if_neg hv, Nat.add_zero]
theorem longCompleted_last_fresh {n : Nat} (before : Fin n → State → Option State) (last : State → Option State)
    (input answer : State) (hfresh : last input = none) :
    longCompleted (Fin.snoc before (Function.update last input (some answer))) =
      longCompleted (Fin.snoc before last) + targetCount before input := by
  induction n with
  | zero => simp only [longCompleted, targetCount, Nat.add_zero]
  | succ n ih =>
      rw [longCompleted, longCompleted, tail_snoc, tail_snoc, knownCount_sum_last_fresh before last input answer hfresh,
        ih (Fin.tail before), targetCount]
      omega
theorem longCompleted_record_last {n : Nat} (observed : Fin (n + 1) → State → Option State)
    (input answer : State) (hfresh : observed (Fin.last n) input = none) :
    longCompleted (record observed (Fin.last n, input) answer) =
      longCompleted observed + targetCount (Fin.init observed) input := by
  have h := longCompleted_last_fresh (Fin.init observed) (observed (Fin.last n)) input answer hfresh
  rw [Fin.snoc_init_self] at h
  have hrecord : record observed (Fin.last n, input) answer =
      Fin.snoc (Fin.init observed) (Function.update (observed (Fin.last n)) input (some answer)) := by
    conv_lhs => rw [← Fin.snoc_init_self observed]
    simp only [record, Fin.snoc_last, Fin.update_snoc_last]
  simpa only [hrecord] using h
omit [Fintype State] in
theorem init_record {n : Nat} (observed : Fin (n + 1) → State → Option State)
    (step : Fin n) (input answer : State) :
    Fin.init (record observed (step.castSucc, input) answer) = record (Fin.init observed) (step, input) answer := by
  simp only [record, Fin.init_update_castSucc, Fin.init]
theorem longCompleted_prefix_record_penultimate {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer : State) (hfresh : observed (Fin.last n).castSucc input = none) :
    longCompleted (Fin.init (record observed ((Fin.last n).castSucc, input) answer)) =
      longCompleted (Fin.init observed) + targetCount (Fin.init (Fin.init observed)) input := by
  rw [init_record]
  exact longCompleted_record_last (Fin.init observed) input answer hfresh
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
noncomputable def queriedInputs (row : State → Option State) : Finset State :=
  Finset.univ.filter fun input => row input ≠ none
noncomputable def rowImage (row : State → Option State) : Finset State :=
  Finset.univ.biUnion fun input => (row input).toFinset
omit [DecidableEq State] in
theorem mem_queriedInputs (row : State → Option State) (input : State) :
    input ∈ queriedInputs row ↔ row input ≠ none := by simp [queriedInputs]
omit [DecidableEq State] in
theorem queriedInputs_card (row : State → Option State) : (queriedInputs row).card = queriedCount row := by
  rw [queriedInputs, Finset.card_filter, queriedCount_eq_sum]
  apply Finset.sum_congr rfl
  intro input _
  cases row input <;> simp
theorem mem_rowImage (row : State → Option State) (output : State) :
    output ∈ rowImage row ↔ ∃ input, row input = some output := by
  simp only [rowImage, Finset.mem_biUnion, Finset.mem_univ, true_and, Option.mem_toFinset, Option.mem_def]
theorem rowImage_card_le (row : State → Option State) : (rowImage row).card ≤ queriedCount row := by
  apply Finset.card_biUnion_le.trans
  rw [queriedCount_eq_sum]
  apply Finset.sum_le_sum
  intro input _
  cases row input <;> simp
noncomputable def productiveInputs {n : Nat} (observed : Fin (n + 2) → State → Option State) : Finset State :=
  queriedInputs (observed (Fin.last (n + 1))) ∩ rowImage (observed (Fin.last n).castSucc)
noncomputable def preparationCount {n : Nat} (observed : Fin (n + 2) → State → Option State) : Nat :=
  (productiveInputs observed).card
theorem mem_productiveInputs {n : Nat} (observed : Fin (n + 2) → State → Option State) (input : State) :
    input ∈ productiveInputs observed ↔
      observed (Fin.last (n + 1)) input ≠ none ∧ ∃ start, observed (Fin.last n).castSucc start = some input := by
  simp only [productiveInputs, Finset.mem_inter, mem_queriedInputs, mem_rowImage]
theorem productiveInputs_mono {n : Nat} {before after : Fin (n + 2) → State → Option State} (h : Extends before after) :
    productiveInputs before ⊆ productiveInputs after := by
  intro input hi
  rw [mem_productiveInputs] at hi ⊢
  constructor
  · cases hr : before (Fin.last (n + 1)) input with
    | none => exact False.elim (hi.1 hr)
    | some answer => rw [h _ _ _ hr]; exact Option.some_ne_none answer
  · obtain ⟨start, hs⟩ := hi.2
    exact ⟨start, h _ _ _ hs⟩
theorem preparationCount_mono {n : Nat} {before after : Fin (n + 2) → State → Option State} (h : Extends before after) :
    preparationCount before ≤ preparationCount after := Finset.card_le_card (productiveInputs_mono h)
theorem preparationCount_le_last {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    preparationCount observed ≤ queriedCount (observed (Fin.last (n + 1))) := by
  exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (queriedInputs_card _)
theorem preparationCount_le_penultimate {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    preparationCount observed ≤ queriedCount (observed (Fin.last n).castSucc) := by
  exact (Finset.card_le_card Finset.inter_subset_right).trans (rowImage_card_le _)
theorem preparationCount_le_prefix {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    preparationCount observed ≤ queryCount (Fin.init observed) := by
  apply (preparationCount_le_penultimate observed).trans
  change queriedCount ((Fin.init observed) (Fin.last n)) ≤ ∑ step, queriedCount ((Fin.init observed) step)
  exact Finset.single_le_sum (f := fun step => queriedCount ((Fin.init observed) step))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (Fin.last n))
theorem preparationCount_empty {n : Nat} : preparationCount (n := n) (fun (_ : Fin (n + 2)) (_ : State) => none) = 0 := by
  simp [preparationCount, productiveInputs, queriedInputs]
theorem preparationCount_last_fresh {n : Nat} (observed : Fin (n + 2) → State → Option State) (input answer : State)
    (hfresh : observed (Fin.last (n + 1)) input = none)
    (hprepared : ∃ start, observed (Fin.last n).castSucc start = some input) :
    preparationCount observed + 1 ≤ preparationCount (record observed (Fin.last (n + 1), input) answer) := by
  have hnot : input ∉ productiveInputs observed := by simp only [mem_productiveInputs, hfresh, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
  have hmem : input ∈ productiveInputs (record observed (Fin.last (n + 1), input) answer) := by
    rw [mem_productiveInputs]
    constructor
    · simp only [record, Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true]
    · obtain ⟨start, hs⟩ := hprepared
      refine ⟨start, ?_⟩
      rw [record_at_other observed (Fin.last (n + 1), input) ((Fin.last n).castSucc, start) answer]
      · exact hs
      · intro heq
        have hv := congrArg (fun query => query.1.val) heq
        simp only [Fin.val_castSucc, Fin.val_last] at hv
        omega
  have hsub := productiveInputs_mono (record_extends observed (Fin.last (n + 1), input) answer (Or.inl hfresh))
  have hcard := Finset.card_le_card (Finset.insert_subset hmem hsub)
  rw [Finset.card_insert_of_notMem hnot] at hcard
  exact hcard
theorem preparation_charge_le_three_halves {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    2 * (longCompleted observed + 2 * preparationCount observed) ≤ 3 * queryCount observed := by
  have hd := longCompleted_le_prefix_queries observed
  have hp := preparationCount_le_prefix observed
  have hl := preparationCount_le_last observed
  rw [queryCount_split_last]
  omega
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
theorem contactCount_mono {n : Nat} {before after : Fin n → State → Option State}
    (h : Extends before after) (endpoint : State) : contactCount before endpoint ≤ contactCount after endpoint := by
  unfold contactCount
  apply Finset.sum_le_sum
  intro query _
  by_cases hk : query.1.val + 1 = n ∧ before query.1 query.2 = some endpoint
  · have hk' : query.1.val + 1 = n ∧ after query.1 query.2 = some endpoint := ⟨hk.1, h _ _ _ hk.2⟩
    simp only [if_pos hk, if_pos hk', le_refl]
  · simp only [if_neg hk, Nat.zero_le]
noncomputable def twoEdgeCharge {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State) (endpoint : State) : Nat :=
  longCompleted observed + 2 * preparationCount observed +
    spent * (contactCount observed endpoint * (contactCount observed endpoint + 2)) +
    contactCount observed endpoint * longCompleted (Fin.init observed)
theorem twoEdgeCharge_empty {n : Nat} (endpoint : State) :
    twoEdgeCharge 0 (n := n) (fun _ _ => none) endpoint = 0 := by
  simp only [twoEdgeCharge, longCompleted_empty, preparationCount_empty, contactCount_empty,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
theorem twoEdgeCharge_mono {n : Nat} {before after : Fin (n + 2) → State → Option State}
    {spent next : Nat} (hs : spent ≤ next) (h : Extends before after) (endpoint : State) :
    twoEdgeCharge spent before endpoint ≤ twoEdgeCharge next after endpoint := by
  unfold twoEdgeCharge
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (longCompleted_mono h) (Nat.mul_le_mul_left 2 (preparationCount_mono h)))
      (Nat.mul_le_mul hs (Nat.mul_le_mul (contactCount_mono h endpoint) (Nat.add_le_add_right (contactCount_mono h endpoint) 2))))
    (Nat.mul_le_mul (contactCount_mono h endpoint) (longCompleted_mono h.init))
private theorem charge_increment (d p r k d' p' r' k' spent dd dp dr : Nat)
    (hd : d + dd ≤ d') (hp : p + dp ≤ p') (hr : r + dr ≤ r') (hk : k ≤ k') :
    (d + 2 * p + spent * (k * (k + 2)) + k * r) + dd + 2 * dp + k * (k + 2) + k * dr ≤
      d' + 2 * p' + (spent + 1) * (k' * (k' + 2)) + k' * r' := by
  have hpoly := Nat.mul_le_mul (Nat.le_refl (spent + 1)) (Nat.mul_le_mul hk (Nat.add_le_add_right hk 2))
  have hprod := Nat.mul_le_mul hk hr
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hd (Nat.mul_le_mul_left 2 hp)) hpoly) hprod
  convert hsum using 1
  ring
theorem twoEdgeCharge_record_last {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (hfresh : observed (Fin.last (n + 1)) input = none)
    (hprepared : ∃ start, observed (Fin.last n).castSucc start = some input) :
    twoEdgeCharge spent observed endpoint + (2 + contactCount observed endpoint + targetCount (Fin.init observed) input) ≤
      twoEdgeCharge (spent + 1) (record observed (Fin.last (n + 1), input) answer) endpoint := by
  have hext := record_extends observed (Fin.last (n + 1), input) answer (Or.inl hfresh)
  have h := charge_increment _ _ _ _ _ _ _ _ spent (targetCount (Fin.init observed) input) 1 0
    (le_of_eq (longCompleted_record_last observed input answer hfresh).symm)
    (preparationCount_last_fresh observed input answer hfresh hprepared)
    (by simpa only [Nat.add_zero] using longCompleted_mono hext.init) (contactCount_mono hext endpoint)
  change twoEdgeCharge spent observed endpoint + _ + _ + _ + _ ≤ twoEdgeCharge (spent + 1) _ endpoint at h
  have hk : contactCount observed endpoint ≤ contactCount observed endpoint * (contactCount observed endpoint + 2) := by nlinarith
  omega
theorem twoEdgeCharge_record_penultimate {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (hfresh : observed (Fin.last n).castSucc input = none) :
    twoEdgeCharge spent observed endpoint +
      contactCount observed endpoint * (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input) ≤
      twoEdgeCharge (spent + 1) (record observed ((Fin.last n).castSucc, input) answer) endpoint := by
  have hext := record_extends observed ((Fin.last n).castSucc, input) answer (Or.inl hfresh)
  have h := charge_increment _ _ _ _ _ _ _ _ spent 0 0 (targetCount (Fin.init (Fin.init observed)) input)
    (by simpa only [Nat.add_zero] using longCompleted_mono hext)
    (by simpa only [Nat.add_zero] using preparationCount_mono hext)
    (le_of_eq (longCompleted_prefix_record_penultimate observed input answer hfresh).symm) (contactCount_mono hext endpoint)
  change twoEdgeCharge spent observed endpoint + _ + _ + _ + _ ≤ twoEdgeCharge (spent + 1) _ endpoint at h
  convert h using 1
  ring
theorem contact_correction_identity (k : Nat) : k * (k + 2) + k = contactFactorial k + 4 * k := by
  cases k with
  | zero => rfl
  | succ k => simp only [contactFactorial, Nat.add_sub_cancel]; ring
theorem twoEdgeCharge_le {n : Nat} (spent budget : Nat) (observed : Fin (n + 2) → State → Option State)
    (endpoint : State) (hs : spent ≤ budget) (hq : queryCount observed ≤ budget) :
    twoEdgeCharge spent observed endpoint ≤ longCompleted observed + 2 * preparationCount observed +
      budget * (contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint) := by
  have hr := longCompleted_le_queryCount (Fin.init observed)
  have hsplit := queryCount_split_last observed
  have hrq : longCompleted (Fin.init observed) ≤ budget := by omega
  have hprod := Nat.mul_le_mul_left (contactCount observed endpoint) hrq
  have hspent := Nat.mul_le_mul_right (contactCount observed endpoint * (contactCount observed endpoint + 2)) hs
  have hsum := Nat.add_le_add hspent hprod
  rw [Nat.mul_comm (contactCount observed endpoint) budget, ← Nat.mul_add, contact_correction_identity] at hsum
  unfold twoEdgeCharge
  omega
theorem twoEdgeCharge_twice_le {n : Nat} (spent budget : Nat) (observed : Fin (n + 2) → State → Option State)
    (endpoint : State) (hs : spent ≤ budget) (hq : queryCount observed ≤ budget) :
    2 * twoEdgeCharge spent observed endpoint ≤ 3 * queryCount observed +
      2 * budget * (contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint) := by
  have h := twoEdgeCharge_le spent budget observed endpoint hs hq
  have hbase := preparation_charge_le_three_halves observed
  nlinarith
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
noncomputable def twoEdgeWeight {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State) : ENNReal :=
  meanPreimages observed endpoint * if TwoEdge observed endpoint then 1 else 0
theorem twoEdgeWeight_empty {n : Nat} (endpoint : State) :
    twoEdgeWeight (n := n) (fun _ _ => none) endpoint = 0 := by
  simp [twoEdgeWeight, TwoEdge]
omit [DecidableEq State] [Nonempty State] in
private theorem expected_charge_cover (law : PMF State) (before increment : Nat) (after : State → Nat)
    (weight : State → ENNReal)
    (hrisk : (∑' answer, law answer * weight answer) ≤ (increment : ENNReal) / Fintype.card State)
    (hcharge : ∀ answer, before + increment ≤ after answer) :
    (before : ENNReal) / Fintype.card State + (∑' answer, law answer * weight answer) ≤
      ∑' answer, law answer * ((after answer : ENNReal) / Fintype.card State) := by
  calc
    _ ≤ (before : ENNReal) / Fintype.card State + (increment : ENNReal) / Fintype.card State := _root_.add_le_add le_rfl hrisk
    _ = ((before + increment : Nat) : ENNReal) / Fintype.card State := by simp only [Nat.cast_add, div_eq_mul_inv, add_mul]
    _ = ∑' answer, law answer * (((before + increment : Nat) : ENNReal) / Fintype.card State) := (expectation_const _ _).symm
    _ ≤ _ := ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (by gcongr; exact_mod_cast hcharge answer)
theorem twoEdgeCharge_observe_mono {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State ≤
      ∑' answer, rowLaw (observed query.1 query.2) answer *
        ((twoEdgeCharge (spent + 1) (record observed query answer) endpoint : ENNReal) / Fintype.card State) := by
  cases hrow : observed query.1 query.2 with
  | some answer =>
      simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow]
      gcongr
      exact twoEdgeCharge_mono (Nat.le_succ spent) (fun _ _ _ h => h) endpoint
  | none =>
      rw [← expectation_const (rowLaw (none : Option State)) ((twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State)]
      apply ENNReal.tsum_le_tsum
      intro answer
      apply mul_le_mul' le_rfl
      gcongr
      exact twoEdgeCharge_mono (Nat.le_succ spent) (record_extends observed query answer (Or.inl hrow)) endpoint
theorem twoEdgeWeight_observe_of_bad {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) (hbad : TwoEdge observed endpoint) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * twoEdgeWeight (record observed query answer) endpoint) =
      twoEdgeWeight observed endpoint := by
  cases hrow : observed query.1 query.2 with
  | some answer => simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow]
  | none =>
      have hafter (answer : State) : TwoEdge (record observed query answer) endpoint :=
        twoEdge_mono (record_extends observed query answer (Or.inl hrow)) endpoint hbad
      simp only [twoEdgeWeight, if_pos hbad, if_pos (hafter _), mul_one]
      simpa only [hrow] using meanPreimages_observe observed query endpoint
theorem twoEdge_first_compensation {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) (hbad : ¬TwoEdge observed endpoint)
    (hfresh : observed query.1 query.2 = none) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State +
      (∑' answer, rowLaw (observed query.1 query.2) answer * twoEdgeWeight (record observed query answer) endpoint) ≤
      ∑' answer, rowLaw (observed query.1 query.2) answer *
        ((twoEdgeCharge (spent + 1) (record observed query answer) endpoint : ENNReal) / Fintype.card State) := by
  rcases query with ⟨step, input⟩
  by_cases hlast : step = Fin.last (n + 1)
  · subst step
    by_cases hprepared : ∃ start, observed (Fin.last n).castSucc start = some input
    · apply expected_charge_cover _ _ (2 + contactCount observed endpoint + targetCount (Fin.init observed) input)
      · simpa only [twoEdgeWeight, if_pos hprepared] using twoEdge_last_weighted_risk observed input endpoint hbad hfresh
      · intro answer
        exact twoEdgeCharge_record_last spent observed input answer endpoint hfresh hprepared
    · apply expected_charge_cover _ _ 0
      · simpa only [twoEdgeWeight, if_neg hprepared, Nat.cast_zero, div_eq_mul_inv, zero_mul] using twoEdge_last_weighted_risk observed input endpoint hbad hfresh
      · intro answer
        simpa only [Nat.add_zero] using twoEdgeCharge_mono (Nat.le_succ spent)
          (record_extends observed (Fin.last (n + 1), input) answer (Or.inl hfresh)) endpoint
  · by_cases hpen : step = (Fin.last n).castSucc
    · subst step
      apply expected_charge_cover _ _ (contactCount observed endpoint * (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input))
      · exact twoEdge_penultimate_weighted_risk observed input endpoint hbad hfresh
      · intro answer
        exact twoEdgeCharge_record_penultimate spent observed input answer endpoint hfresh
    · have hafter (answer : State) : ¬TwoEdge (record observed (step, input) answer) endpoint := by
        rw [twoEdge_record_earlier observed (step, input) answer endpoint (Ne.symm hpen) (Ne.symm hlast)]
        exact hbad
      simp only [twoEdgeWeight, if_neg (hafter _), mul_zero, tsum_zero, add_zero]
      exact twoEdgeCharge_observe_mono spent observed (step, input) endpoint
theorem twoEdge_observe_compensation {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State +
      (∑' answer, rowLaw (observed query.1 query.2) answer * twoEdgeWeight (record observed query answer) endpoint) ≤
      twoEdgeWeight observed endpoint + ∑' answer, rowLaw (observed query.1 query.2) answer *
        ((twoEdgeCharge (spent + 1) (record observed query answer) endpoint : ENNReal) / Fintype.card State) := by
  by_cases hbad : TwoEdge observed endpoint
  · rw [twoEdgeWeight_observe_of_bad observed query endpoint hbad, add_comm]
    exact _root_.add_le_add le_rfl (twoEdgeCharge_observe_mono spent observed query endpoint)
  · have hzero : twoEdgeWeight observed endpoint = 0 := by simp only [twoEdgeWeight, if_neg hbad, mul_zero]
    rw [hzero, zero_add]
    cases hrow : observed query.1 query.2 with
    | none => simpa only [hrow] using twoEdge_first_compensation spent observed query endpoint hbad hrow
    | some answer =>
        simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow, hzero, add_zero]
        gcongr
        exact twoEdgeCharge_mono (Nat.le_succ spent) (fun _ _ _ h => h) endpoint
end SphincsSecurity.Concrete.PartialChainEndpoint
end
end
-- ==== merged from SphincsSecurity_Proof_Chains_AdaptiveChainContact ====
section

section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
noncomputable def contactPotential {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : ENNReal :=
  if Contact observed endpoint then meanPreimages observed endpoint else (pendingCount observed : ENNReal) / Fintype.card State
theorem contactPotential_dominates {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    meanPreimages observed endpoint * (if Contact observed endpoint then 1 else 0) ≤ contactPotential observed endpoint := by
  by_cases h : Contact observed endpoint <;> simp [contactPotential, h]
theorem contactPotential_empty {n : Nat} (endpoint : State) : contactPotential (n := n) (fun _ _ => none) endpoint = 0 := by
  simp [contactPotential, Contact, pendingCount, queryCount_empty]
theorem contactPotential_observe_of_contact {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (endpoint : State) (hc : Contact observed endpoint) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * contactPotential (record observed query answer) endpoint) =
      contactPotential observed endpoint := by
  rw [contactPotential, if_pos hc, ← meanPreimages_observe observed query endpoint]
  apply tsum_congr
  intro answer
  cases hrow : observed query.1 query.2 with
  | none =>
      rw [contactPotential, if_pos (contact_mono (record_extends observed query answer (Or.inl hrow)) endpoint hc)]
  | some value =>
      by_cases hanswer : answer = value
      · subst answer
        rw [contactPotential, if_pos (contact_mono (record_extends observed query value (Or.inr hrow)) endpoint hc)]
      · simp only [rowLaw, PMF.pure_apply, if_neg hanswer, zero_mul]
theorem contactPotential_observe_le {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * contactPotential (record observed query answer) endpoint) ≤
      contactPotential observed endpoint + 2 / Fintype.card State := by
  by_cases hc : Contact observed endpoint
  · rw [contactPotential_observe_of_contact observed query endpoint hc]
    exact _root_.le_add_of_nonneg_right bot_le
  cases hrow : observed query.1 query.2 with
  | some value =>
      simp only [rowLaw]
      have hpure := tsum_probOutput_pure_mul (m := PMF) value
        (fun answer => contactPotential (record observed query answer) endpoint)
      simp only [PMF.probOutput_eq_apply, PMF.monad_pure_eq_pure, record_of_known observed query value hrow] at hpure
      rw [hpure]
      exact _root_.le_add_of_nonneg_right bot_le
  | none =>
      by_cases hlast : query.1.val + 1 = n
      · calc
          _ ≤ ∑' answer, rowLaw none answer *
              ((if answer = endpoint then meanPreimages (record observed query endpoint) endpoint else 0) +
                (pendingCount (record observed query endpoint) : ENNReal) / Fintype.card State) := by
            apply ENNReal.tsum_le_tsum
            intro answer
            apply mul_le_mul' le_rfl
            by_cases heq : answer = endpoint
            · subst answer
              rw [contactPotential, if_pos ((contact_record_iff observed query endpoint endpoint hc).mpr ⟨hlast, rfl⟩), if_pos rfl]
              exact _root_.le_add_of_nonneg_right bot_le
            · rw [contactPotential, if_neg (by simpa only [contact_record_iff observed query answer endpoint hc, hlast, true_and] using heq), if_neg heq, zero_add]
              rw [pendingCount_record_last_answer_eq observed query hlast answer endpoint]
          _ = (meanPreimages (record observed query endpoint) endpoint +
                (pendingCount (record observed query endpoint) : ENNReal)) / Fintype.card State := by
            simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, mul_ite, mul_zero, tsum_ite_eq]
            simp only [rowLaw, PMF.uniformOfFintype_apply, div_eq_mul_inv, mul_comm, mul_add]
          _ ≤ (pendingCount observed + 2 : Nat) / (Fintype.card State : ENNReal) := by
            simpa only [div_eq_mul_inv] using mul_le_mul'
              (first_contact_density_charge observed query endpoint endpoint hc (Or.inl hrow))
              (le_refl (Fintype.card State : ENNReal)⁻¹)
          _ = _ := by simp only [contactPotential, if_neg hc, Nat.cast_add, Nat.cast_ofNat, ENNReal.add_div]
      · calc
          _ ≤ ∑' answer, rowLaw none answer * ((pendingCount observed + 2 : Nat) / (Fintype.card State : ENNReal)) := by
            apply ENNReal.tsum_le_tsum
            intro answer
            apply mul_le_mul' le_rfl
            rw [contactPotential, if_neg (by simp only [contact_record_iff observed query answer endpoint hc, hlast, false_and, not_false_eq_true])]
            have hp : pendingCount (record observed query answer) ≤ pendingCount observed + 2 :=
              (pendingCount_record_le observed query answer (Or.inl hrow)).trans (by omega)
            simpa only [div_eq_mul_inv] using mul_le_mul' (show (pendingCount (record observed query answer) : ENNReal) ≤ (pendingCount observed + 2 : Nat) by exact_mod_cast hp)
              (le_refl (Fintype.card State : ENNReal)⁻¹)
          _ = _ := by
            simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, contactPotential, if_neg hc, Nat.cast_add, Nat.cast_ofNat, ENNReal.add_div]
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem lazyRun_counted_expectation (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (payoff : Result × (Fin n → State → Option State) → ENNReal) :
    (∑' result, lazyRun auxiliary computation observed result * payoff result) =
      ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * payoff (result.1.1, result.2) := by
  have h := congrArg (fun law : PMF (Result × (Fin n → State → Option State)) => ∑' result, law result * payoff result)
    (lazyRun_map auxiliary (QueryCap.counted IsPrefixQuery computation) Prod.fst observed)
  simpa only [QueryCap.counted_forget, expectation_map] using h
theorem lazyRun_contactPotential_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) (endpoint : State) :
    (∑' result, lazyRun auxiliary computation observed result * contactPotential result.2 endpoint) ≤
      contactPotential observed endpoint + (2 / Fintype.card State) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  rw [lazyRun_counted_expectation]
  apply lazyRun_potential_le auxiliary (fun current => contactPotential current endpoint) (2 / Fintype.card State)
  intro input current
  cases input with
  | inl input => simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | inr query =>
      simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true, Nat.cast_one, mul_one]
      exact contactPotential_observe_le current query endpoint
theorem realRun_contact_le (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) :
    Pr[fun result => Contact result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (2 / Fintype.card State) * ∑' result, idealRun auxiliary
        (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  rw [show Pr[fun result => Contact result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] =
    (∑' result, realRun auxiliary computation (fun _ _ => none) result * (if Contact result.2.2 result.1 then 1 else 0)) by
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]]
  rw [realRun_expectation]
  calc
    _ ≤ ∑' result, idealRun auxiliary computation (fun _ _ => none) result * contactPotential result.2.2 result.1 :=
      ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (contactPotential_dominates result.2.2 result.1)
    _ ≤ _ := by
      simp only [idealRun, expectation_bind, expectation_map]
      rw [← expectation_scale]
      apply ENNReal.tsum_le_tsum
      intro endpoint
      apply mul_le_mul' le_rfl
      simpa only [contactPotential_empty, zero_add] using
        lazyRun_contactPotential_le (auxiliary endpoint) (computation endpoint) (fun _ _ => none) endpoint
end SphincsSecurity.Concrete.PartialChainEndpoint
end
end
-- ==== merged from SphincsSecurity_Proof_Base_QueryCapErasure ====
section

namespace SphincsSecurity.QueryCap
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
private theorem map_eq_on_support {Result Output : Type} (law : PMF Result) (first second : Result → Output)
    (h : ∀ result ∈ law.support, first result = second result) : law.map first = law.map second := by
  classical
  apply PMF.ext
  intro output
  rw [PMF.map, PMF.map, PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro result
  simp only [Function.comp_apply]
  by_cases hresult : result ∈ law.support
  · rw [h result hresult]
  · have hzero : law result = 0 := by simpa only [PMF.mem_support_iff, not_not] using hresult
    simp only [hzero, zero_mul]
variable {Index : Type} {spec : OracleSpec Index} {Result : Type}
  (selected : Index → Prop) [DecidablePred selected]
theorem counted_simulate_result_mem (impl : QueryImpl spec PMF) (computation : OracleComp spec Result)
    (result : Result × Nat) (hresult : result ∈ (simulateQ impl (counted selected computation)).support) :
    result.1 ∈ (simulateQ impl computation).support := by
  have hmap : (simulateQ impl (counted selected computation)).map Prod.fst = simulateQ impl computation := by
    rw [← PMF.monad_map_eq_map, ← simulateQ_map, counted_forget]
  rw [← hmap, PMF.mem_support_map_iff]
  exact ⟨result, hresult, rfl⟩
theorem run_eq_some_counted (impl : QueryImpl spec PMF) (computation : OracleComp spec Result) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ impl (counted selected computation)).support, result.2 ≤ budget) :
    simulateQ impl (run selected computation budget) =
      (simulateQ impl (counted selected computation)).map (fun result => some (result.1, budget - result.2)) := by
  rw [run_eq_counted]
  apply map_eq_on_support
  intro result hresult
  exact if_pos (hbound result hresult)
theorem run_erased (impl : QueryImpl spec PMF) (computation : OracleComp spec Result) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ impl (counted selected computation)).support, result.2 ≤ budget) :
    (simulateQ impl (run selected computation budget)).map (Option.map Prod.fst) =
      (simulateQ impl computation).map some := by
  rw [run_eq_some_counted selected impl computation budget hbound, PMF.map_comp]
  change (simulateQ impl (counted selected computation)).map (some ∘ Prod.fst) = _
  rw [← PMF.map_comp]
  apply congrArg (PMF.map some)
  rw [← PMF.monad_map_eq_map, ← simulateQ_map, counted_forget]
theorem run_recover_count (impl : QueryImpl spec PMF) (computation : OracleComp spec Result) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ impl (counted selected computation)).support, result.2 ≤ budget) :
    (simulateQ impl (run selected computation budget)).map (Option.map (fun result => (result.1, budget - result.2))) =
      (simulateQ impl (counted selected computation)).map some := by
  rw [run_eq_some_counted selected impl computation budget hbound, PMF.map_comp]
  apply map_eq_on_support
  intro result hresult
  simp only [Function.comp_apply, Option.map_some]
  congr 2
  exact Nat.sub_sub_self (hbound result hresult)
end SphincsSecurity.QueryCap
end
-- ==== merged from SphincsSecurity_Proof_Chains_AdaptiveChainCapCost ====
section

section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem realRun_empty_apply_lower (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (budget : Nat)
    (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget)
    (result : State × (Result × (Fin n → State → Option State))) :
    (1 - (budget : ENNReal) / Fintype.card State) * idealRun auxiliary computation (fun _ _ => none) result ≤
      realRun auxiliary computation (fun _ _ => none) result := by
  classical
  have h := realRun_empty_cost_lower auxiliary computation budget hbound (fun output => if output = result then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, tsum_ite_eq] using h
theorem idealRun_empty_support_subset (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (budget : Nat)
    (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget)
    (hsmall : budget < Fintype.card State) :
    (idealRun auxiliary computation (fun _ _ => none)).support ⊆
      (realRun auxiliary computation (fun _ _ => none)).support := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpositive : 0 < 1 - (budget : ENNReal) / Fintype.card State := by
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl hcard) (Or.inl (by finiteness)), one_mul]
    exact_mod_cast hsmall
  intro result hresult
  exact ne_of_gt (lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨hpositive, pos_iff_ne_zero.mpr hresult⟩)
    (realRun_empty_apply_lower auxiliary computation budget hbound result))
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
include hcharge hreal
theorem fixed_counted_le (tables : Fin n → State → State) (secret : State) (result : Result × Nat)
    (hresult : result ∈ (simulateQ (fixedImpl (auxiliary (evaluate tables secret)) tables)
      (QueryCap.counted IsPrefixQuery (computation (evaluate tables secret)))).support) : result.2 ≤ budget := by
  have hcount := hcharge (evaluate tables secret) result (QueryCap.simulate_mem_support _ _ result hresult)
  have houtput := QueryCap.counted_simulate_result_mem IsPrefixQuery _ _ result hresult
  have hsource := realRun_empty_result_mem auxiliary computation tables secret result.1 houtput
  rw [PMF.mem_support_map_iff] at hsource
  obtain ⟨source, hsource, hvalue⟩ := hsource
  exact hcount.trans (by simpa only [hvalue] using hreal source hsource)
theorem realRun_cap_erased :
    (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
      (fun result => Option.map Prod.fst result.2.1) =
      (realRun auxiliary computation (fun _ _ => none)).map (fun result => some result.2.1) := by
  change (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
    (Option.map Prod.fst ∘ (fun result => result.2.1)) =
    (realRun auxiliary computation (fun _ _ => none)).map (some ∘ (fun result => result.2.1))
  rw [← PMF.map_comp, ← PMF.map_comp, realRun_empty_forget, realRun_empty_forget]
  simp only [PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (Fin n → State → State)).bind
  funext tables
  apply congrArg (PMF.uniformOfFintype State).bind
  funext secret
  exact QueryCap.run_erased IsPrefixQuery _ _ budget
    (fixed_counted_le auxiliary computation cost budget hcharge hreal tables secret)
theorem realRun_cap_recover_count :
    (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
      (fun result => Option.map (fun finished => (finished.1, budget - finished.2)) result.2.1) =
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).map
        (fun result => some result.2.1) := by
  change (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
    (Option.map (fun finished => (finished.1, budget - finished.2)) ∘ (fun result => result.2.1)) =
    (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).map
      (some ∘ (fun result => result.2.1))
  rw [← PMF.map_comp, ← PMF.map_comp, realRun_empty_forget, realRun_empty_forget]
  simp only [PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (Fin n → State → State)).bind
  funext tables
  apply congrArg (PMF.uniformOfFintype State).bind
  funext secret
  exact QueryCap.run_recover_count IsPrefixQuery _ _ budget
    (fixed_counted_le auxiliary computation cost budget hcharge hreal tables secret)
theorem realRun_cap_valid (result : State × (Option (Result × Nat) × (Fin n → State → Option State)))
    (hresult : result ∈ (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
      (fun _ _ => none)).support) :
    ∃ finished, result.2.1 = some finished ∧ cost finished.1 ≤ budget := by
  have hmap : Option.map Prod.fst result.2.1 ∈
      ((realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
        (fun result => Option.map Prod.fst result.2.1)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  rw [realRun_cap_erased auxiliary computation cost budget hcharge hreal, PMF.mem_support_map_iff] at hmap
  obtain ⟨source, hsource, hvalue⟩ := hmap
  cases hfinished : result.2.1 with
  | none => simp only [hfinished, Option.map_none, Option.some_ne_none] at hvalue
  | some finished =>
      refine ⟨finished, rfl, ?_⟩
      have heq : source.2.1 = finished.1 := by simpa only [hfinished, Option.map_some, Option.some.injEq] using hvalue
      rw [← heq]
      exact hreal source hsource
theorem idealRun_cap_valid (hsmall : budget < Fintype.card State)
    (result : State × (Option (Result × Nat) × (Fin n → State → Option State)))
    (hresult : result ∈ (idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
      (fun _ _ => none)).support) :
    ∃ finished, result.2.1 = some finished ∧ cost finished.1 ≤ budget := by
  apply realRun_cap_valid auxiliary computation cost budget hcharge hreal result
  exact idealRun_empty_support_subset auxiliary _ budget
    (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget) hsmall hresult
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.QueryCap
open _root_.OracleComp OracleSpec ENNReal
def spent {Result : Type} (budget : Nat) (result : Option (Result × Nat)) : Nat :=
  result.elim 0 (fun finished => budget - finished.2)
theorem scaled_expectation_bind_le {Sample First Second : Type} (prior : SPMF Sample)
    (first : Sample → SPMF First) (second : Sample → SPMF Second)
    (firstCost : First → ENNReal) (secondCost : Second → ENNReal) (factor : ENNReal)
    (h : ∀ sample ∈ support prior,
      factor * (∑' result, Pr[= result | first sample] * firstCost result) ≤
        ∑' result, Pr[= result | second sample] * secondCost result) :
    factor * (∑' result, Pr[= result | prior >>= first] * firstCost result) ≤
      ∑' result, Pr[= result | prior >>= second] * secondCost result := by
  rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro sample
  by_cases hsample : sample ∈ support prior
  · rw [mul_left_comm factor]
    exact mul_le_mul' le_rfl (h sample hsample)
  · rw [probOutput_eq_zero_of_not_mem_support hsample, zero_mul, zero_mul, mul_zero]
end SphincsSecurity.QueryCap
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
include hcharge hreal
theorem realRun_cap_count_payoff (payoff : Result × Nat → ENNReal) :
    (∑' result, realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
        (fun _ _ => none) result * result.2.1.elim 0 (fun finished => payoff (finished.1, budget - finished.2))) =
      ∑' result, realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none) result * payoff result.2.1 := by
  have h := congrArg (fun law : PMF (Option (Result × Nat)) => ∑' result, law result * result.elim 0 payoff)
    (realRun_cap_recover_count auxiliary computation cost budget hcharge hreal)
  simpa only [expectation_map, Option.elim_map, Option.elim_some, Function.comp_def] using h
theorem idealRun_cap_spent_lower :
    (1 - (budget : ENNReal) / Fintype.card State) *
        (∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
          (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal)) ≤
      ∑' result, realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  apply (realRun_empty_cost_lower auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
    budget (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget)
    (fun result => (QueryCap.spent budget result.2.1 : ENNReal))).trans_eq
  have h := realRun_cap_count_payoff auxiliary computation cost budget hcharge hreal (fun result => (result.2 : ENNReal))
  convert h using 1
  apply tsum_congr
  intro result
  congr 1
  cases result.2.1 <;> simp only [QueryCap.spent, Option.elim_none, Option.elim_some, Nat.cast_zero]
end SphincsSecurity.Concrete.PartialChainEndpoint
end
end
-- ==== merged from SphincsSecurity_Proof_Chains_AdaptiveChainCapContact ====
section

section
namespace SphincsSecurity.QueryCap
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Index : Type} {spec : OracleSpec Index} {Result : Type}
  (selected : Index → Prop) [DecidablePred selected]
theorem counted_run_balance (computation : OracleComp spec Result) (budget : Nat)
    (result : Option (Result × Nat) × Nat) (hresult : result ∈ support (counted selected (run selected computation budget))) :
    result.2 + result.1.elim 0 Prod.snd = budget := by
  induction computation using OracleComp.inductionOn generalizing budget result with
  | pure value =>
      simp only [run_pure, counted_pure, mem_support_pure_iff] at hresult
      subst result
      simp only [Option.elim_some, Nat.zero_add]
  | query_bind input next ih =>
      rw [run_query_bind] at hresult
      by_cases hs : selected input
      · rw [if_pos hs] at hresult
        cases budget with
        | zero =>
            rw [counted_pure, mem_support_pure_iff] at hresult
            subst result
            rfl
        | succ budget =>
            rw [counted_query_bind, mem_support_bind_iff] at hresult
            obtain ⟨answer, _, hresult⟩ := hresult
            rw [mem_support_bind_iff] at hresult
            obtain ⟨tail, htail, hresult⟩ := hresult
            rw [mem_support_pure_iff] at hresult
            subst result
            have h := ih answer budget tail htail
            simp only [if_pos hs]
            omega
      · rw [if_neg hs, counted_query_bind, mem_support_bind_iff] at hresult
        obtain ⟨answer, _, hresult⟩ := hresult
        rw [mem_support_bind_iff] at hresult
        obtain ⟨tail, htail, hresult⟩ := hresult
        rw [mem_support_pure_iff] at hresult
        subst result
        simpa only [if_neg hs, Nat.zero_add] using ih answer budget tail htail
theorem counted_next_bound (impl : QueryImpl spec PMF) (input : spec.Domain)
    (next : spec.Range input → OracleComp spec Result) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ impl (counted selected (liftM (spec.query input) >>= next))).support, result.2 ≤ budget)
    (answer : spec.Range input) (hanswer : answer ∈ (impl input).support)
    (tail : Result × Nat) (htail : tail ∈ (simulateQ impl (counted selected (next answer))).support) :
    (if selected input then 1 else 0) + tail.2 ≤ budget := by
  apply hbound (tail.1, (if selected input then 1 else 0) + tail.2)
  simp only [counted_query_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  exact ⟨answer, hanswer, tail, htail, rfl⟩
end SphincsSecurity.QueryCap
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result Next : Type}
theorem lazyRun_result_mem (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (result : Result × (Fin n → State → Option State)) (hresult : result ∈ (lazyRun auxiliary computation observed).support) :
    result.1 ∈ support computation := by
  induction computation using OracleComp.inductionOn generalizing observed with
  | pure value =>
      rw [lazyRun_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact (mem_support_pure_iff _ _).mpr rfl
  | query_bind input next ih =>
      rw [lazyRun_query_bind, PMF.mem_support_bind_iff] at hresult
      obtain ⟨middle, _, hresult⟩ := hresult
      rw [mem_support_bind_iff]
      exact ⟨middle.1, by simp only [support_query, Set.mem_univ], ih middle.1 middle.2 hresult⟩
theorem idealRun_result_mem (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (result : State × (Result × (Fin n → State → Option State))) (hresult : result ∈ (idealRun auxiliary computation observed).support) :
    result.2.1 ∈ support (computation result.1) := by
  rw [idealRun, PMF.mem_support_bind_iff] at hresult
  obtain ⟨endpoint, _, hresult⟩ := hresult
  rw [PMF.mem_support_map_iff] at hresult
  obtain ⟨output, houtput, rfl⟩ := hresult
  exact lazyRun_result_mem (auxiliary endpoint) (computation endpoint) observed output houtput
theorem idealRun_map (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (f : State → Result → Next)
    (observed : Fin n → State → Option State) :
    idealRun auxiliary (fun endpoint => f endpoint <$> computation endpoint) observed =
      (idealRun auxiliary computation observed).map (fun result => (result.1, f result.1 result.2.1, result.2.2)) := by
  simp only [idealRun, lazyRun_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
theorem idealRun_counted_forget (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    (idealRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) observed).map
      (fun result => (result.1, result.2.1.1, result.2.2)) = idealRun auxiliary computation observed := by
  simpa only [QueryCap.counted_forget] using
    (idealRun_map auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ => Prod.fst) observed).symm
variable (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
  (hsmall : budget < Fintype.card State)
include hcharge hreal hsmall
theorem idealRun_counted_cap_spent
    (result : State × ((Option (Result × Nat) × Nat) × (Fin n → State → Option State)))
    (hresult : result ∈ (idealRun auxiliary
      (fun endpoint => QueryCap.counted IsPrefixQuery (QueryCap.run IsPrefixQuery (computation endpoint) budget)) (fun _ _ => none)).support) :
    result.2.1.2 = QueryCap.spent budget result.2.1.1 := by
  have hforget : (result.1, result.2.1.1, result.2.2) ∈
      (idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).support := by
    rw [← idealRun_counted_forget auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none),
      PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  obtain ⟨finished, hfinished, _⟩ := idealRun_cap_valid auxiliary computation cost budget hcharge hreal hsmall _ hforget
  change result.2.1.1 = some finished at hfinished
  have hbalance := QueryCap.counted_run_balance IsPrefixQuery (computation result.1) budget result.2.1
    (idealRun_result_mem auxiliary _ (fun _ _ => none) result hresult)
  simp only [hfinished, Option.elim_some] at hbalance
  simp only [QueryCap.spent, hfinished, Option.elim_some]
  omega
theorem idealRun_cap_count_expectation :
    (∑' result, idealRun auxiliary
        (fun endpoint => QueryCap.counted IsPrefixQuery (QueryCap.run IsPrefixQuery (computation endpoint) budget)) (fun _ _ => none) result *
          (result.2.1.2 : ENNReal)) =
      ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) result *
        (QueryCap.spent budget result.2.1 : ENNReal) := by
  rw [← idealRun_counted_forget auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none), expectation_map]
  apply tsum_congr
  intro result
  by_cases hresult : result ∈ (idealRun auxiliary
      (fun endpoint => QueryCap.counted IsPrefixQuery (QueryCap.run IsPrefixQuery (computation endpoint) budget)) (fun _ _ => none)).support
  · rw [idealRun_counted_cap_spent auxiliary computation cost budget hcharge hreal hsmall result hresult]
  · have hzero : idealRun auxiliary
        (fun endpoint => QueryCap.counted IsPrefixQuery (QueryCap.run IsPrefixQuery (computation endpoint) budget)) (fun _ _ => none) result = 0 :=
      not_not.mp hresult
    simp only [hzero, zero_mul]
theorem realRun_cap_contact_le :
    Pr[fun result => Contact result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)] ≤
        (2 / Fintype.card State) * ∑' result,
          idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) result *
            (QueryCap.spent budget result.2.1 : ENNReal) := by
  have h := realRun_contact_le auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
  rwa [idealRun_cap_count_expectation auxiliary computation cost budget hcharge hreal hsmall] at h
end SphincsSecurity.Concrete.PartialChainEndpoint
end
end
-- ==== merged from SphincsSecurity_Proof_Chains_AdaptiveChainCountedRows ====
section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem lazyRun_counted_queryCount_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (result : (Result × Nat) × (Fin n → State → Option State))
    (hresult : result ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed).support) :
    queryCount result.2 ≤ queryCount observed + result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing observed result with
  | pure value =>
      rw [QueryCap.counted_pure, lazyRun_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact le_rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
            lazyImpl, StateT.run_mk, PMF.bind_map, Function.comp_def, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hresult
          obtain ⟨answer, _, tail, htail, rfl⟩ := hresult
          simpa only [IsPrefixQuery, if_false, Nat.zero_add] using ih answer observed tail htail
      | inr query =>
          simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
            lazyImpl, StateT.run_mk, PMF.bind_map, Function.comp_def, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hresult
          obtain ⟨answer, _, tail, htail, rfl⟩ := hresult
          have ht := ih answer (record observed query answer) tail htail
          have hr := queryCount_record_le observed query answer
          simp only [IsPrefixQuery, if_true]
          omega
theorem lazyRun_counted_budget_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget)
    (result : (Result × Nat) × (Fin n → State → Option State))
    (hresult : result ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed).support) :
    result.1.2 ≤ budget :=
  QueryCap.counted_le_of_queryBound IsPrefixQuery computation budget hbound result.1
    (lazyRun_result_mem auxiliary (QueryCap.counted IsPrefixQuery computation) observed result hresult)
end SphincsSecurity.Concrete.PartialChainEndpoint
end
-- ==== merged from SphincsSecurity_Proof_Chains_AdaptiveChainCapObservation ====
section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
private theorem pmf_bind_eq_on_support {First Second : Type} (prior : PMF First) (first second : First → PMF Second)
    (h : ∀ input ∈ prior.support, first input = second input) : prior.bind first = prior.bind second := by
  apply PMF.ext
  intro result
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro input
  by_cases hi : input ∈ prior.support
  · rw [h input hi]
  · have hz : prior input = 0 := not_not.mp hi
    simp only [hz, zero_mul]
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result Next : Type}
omit [Fintype State] [Nonempty State] in
theorem observedRun_map (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (f : Result → Next)
    (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (f <$> computation) observed =
      (observedRun auxiliary tables computation observed).map (fun result => (f result.1, result.2)) := by
  simp only [observedRun, simulateQ_map, StateT.run_map, PMF.monad_map_eq_map]
omit [Fintype State] [Nonempty State] in
theorem observedRun_cap_eq_counted (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ (fixedImpl auxiliary tables) (QueryCap.counted IsPrefixQuery computation)).support,
      result.2 ≤ budget) :
    observedRun auxiliary tables (QueryCap.run IsPrefixQuery computation budget) observed =
      (observedRun auxiliary tables (QueryCap.counted IsPrefixQuery computation) observed).map
        (fun result => (some (result.1.1, budget - result.1.2), result.2)) := by
  induction computation using OracleComp.inductionOn generalizing observed budget with
  | pure value =>
      simp only [QueryCap.run_pure, QueryCap.counted_pure, observedRun_pure, PMF.map, PMF.pure_bind, Function.comp_def, Nat.sub_zero]
  | query_bind input next ih =>
      rw [QueryCap.run_query_bind, QueryCap.counted_query_bind]
      simp only [bind_pure_comp, observedRun_query_bind, observedRun_map]
      cases input with
      | inl input =>
          simp only [IsPrefixQuery, if_false, observedRun_query_bind, observedImpl, StateT.run_mk,
            PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def, Nat.zero_add]
          apply pmf_bind_eq_on_support
          intro answer hanswer
          apply ih answer observed budget
          intro tail htail
          have h := QueryCap.counted_next_bound IsPrefixQuery (fixedImpl auxiliary tables) (.inl input) next budget hbound answer hanswer tail htail
          simpa only [IsPrefixQuery, if_false, Nat.zero_add] using h
      | inr query =>
          simp only [IsPrefixQuery, if_true]
          have hnext := fun tail htail => QueryCap.counted_next_bound IsPrefixQuery (fixedImpl auxiliary tables)
            (.inr query) next budget hbound (tables query.1 query.2) (by simp [fixedImpl]) tail htail
          cases budget with
          | zero =>
              obtain ⟨tail, htail⟩ := (simulateQ (fixedImpl auxiliary tables)
                (QueryCap.counted IsPrefixQuery (next (tables query.1 query.2)))).support_nonempty
              have h := hnext tail htail
              simp only [IsPrefixQuery, if_true] at h
              omega
          | succ budget =>
              simp only [observedRun_query_bind, observedImpl, StateT.run_mk, PMF.pure_bind,
                PMF.map_comp, Function.comp_def, Nat.add_comm 1, Nat.add_sub_add_right]
              apply ih (tables query.1 query.2) (record observed query (tables query.1 query.2)) budget
              intro tail htail
              have h := hnext tail htail
              simp only [IsPrefixQuery, if_true] at h
              omega
theorem realRun_map (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (f : State → Result → Next)
    (observed : Fin n → State → Option State) :
    realRun auxiliary (fun endpoint => f endpoint <$> computation endpoint) observed =
      (realRun auxiliary computation observed).map (fun result => (result.1, f result.1 result.2.1, result.2.2)) := by
  simp only [realRun, observedRun_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
theorem realRun_counted_forget (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) observed).map
      (fun result => (result.1, result.2.1.1, result.2.2)) = realRun auxiliary computation observed := by
  simpa only [QueryCap.counted_forget] using
    (realRun_map auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ => Prod.fst) observed).symm
variable (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
include hcharge hreal
theorem realRun_cap_eq_counted_observed :
    realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) =
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).map
        (fun result => (result.1, some (result.2.1.1, budget - result.2.1.2), result.2.2)) := by
  simp only [realRun, completeTables_empty, EndpointPreimageDensity.real, PMF.map_bind, PMF.bind_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def]
  apply congrArg (PMF.uniformOfFintype (Fin n → State → State)).bind
  funext tables
  apply congrArg (PMF.uniformOfFintype State).bind
  funext secret
  rw [observedRun_cap_eq_counted (auxiliary (evaluate tables secret)) tables (computation (evaluate tables secret))
    (fun _ _ => none) budget (fixed_counted_le auxiliary computation cost budget hcharge hreal tables secret), PMF.map_comp]
  simp only [Function.comp_def]
theorem realRun_cap_erased_observed :
    (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
      (fun result => (result.1, Option.map Prod.fst result.2.1, result.2.2)) =
      (realRun auxiliary computation (fun _ _ => none)).map (fun result => (result.1, some result.2.1, result.2.2)) := by
  rw [realRun_cap_eq_counted_observed auxiliary computation cost budget hcharge hreal, PMF.map_comp]
  have h := congrArg (PMF.map (fun result : State × (Result × (Fin n → State → Option State)) =>
    (result.1, some result.2.1, result.2.2))) (realRun_counted_forget auxiliary computation (fun _ _ => none))
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some] using h
theorem realRun_cap_contact_eq :
    Pr[fun result => Contact result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)] =
        Pr[fun result => Contact result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] := by
  have h := congrArg (fun law : PMF (State × (Option Result × (Fin n → State → Option State))) =>
    Pr[fun result => Contact result.2.2 result.1 | law])
    (realRun_cap_erased_observed auxiliary computation cost budget hcharge hreal)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h
theorem realRun_contact_le_cap_cost (hsmall : budget < Fintype.card State) :
    Pr[fun result => Contact result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (2 / Fintype.card State) * ∑' result,
        idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) result *
          (QueryCap.spent budget result.2.1 : ENNReal) := by
  rw [← realRun_cap_contact_eq auxiliary computation cost budget hcharge hreal]
  exact realRun_cap_contact_le auxiliary computation cost budget hcharge hreal hsmall
end SphincsSecurity.Concrete.PartialChainEndpoint
end
-- ==== merged from SphincsSecurity_Proof_Chains_AdaptiveChainCapTwoEdge ====
section

section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem lazyRun_budget_potential_le (auxiliary : QueryImpl auxSpec PMF)
    (potential : Nat → (Fin n → State → Option State) → ENNReal)
    (terminal : (Fin n → State → Option State) → ENNReal) (rate : ENNReal) (limit : Nat)
    (hterminal : ∀ budget observed, terminal observed ≤ potential budget observed)
    (hstep : ∀ input observed budget, budget ≤ limit → (¬IsPrefixQuery input ∨ 0 < budget) →
      (∑' result, (lazyImpl auxiliary input).run observed result *
        potential (if IsPrefixQuery input then budget - 1 else budget) result.2) ≤
          potential budget observed + rate * ((if IsPrefixQuery input then 1 else 0 : Nat) : ENNReal))
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (budget : Nat) (hbudget : budget ≤ limit) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * terminal result.2) ≤
      potential budget observed + rate *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing observed budget with
  | pure result =>
      simp only [QueryCap.counted_pure, lazyRun_pure, expectation_pure, Nat.cast_zero, mul_zero, add_zero]
      exact hterminal budget observed
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      have hremaining : (if IsPrefixQuery input then budget - 1 else budget) ≤ limit := by split <;> omega
      simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
        expectation_bind, expectation_map, Nat.cast_add, expectation_add, expectation_const]
      calc
        _ ≤ ∑' output, (lazyImpl auxiliary input).run observed output *
            (potential (if IsPrefixQuery input then budget - 1 else budget) output.2 + rate *
              ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery (next output.1)) output.2 result * (result.1.2 : ENNReal)) :=
          ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl
            (ih output.1 output.2 _ hremaining (hbound.2 output.1))
        _ = (∑' output, (lazyImpl auxiliary input).run observed output *
              potential (if IsPrefixQuery input then budget - 1 else budget) output.2) +
            rate * ∑' output, (lazyImpl auxiliary input).run observed output *
              ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery (next output.1)) output.2 result * (result.1.2 : ENNReal) := by
          rw [expectation_add, expectation_scale]
        _ ≤ _ := by
          rw [mul_add, ← add_assoc]
          exact _root_.add_le_add (hstep input observed budget hbudget hbound.1) le_rfl
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
noncomputable def contactMomentPotential (remaining : Nat) (observed : Fin n → State → Option State) (endpoint : State) : ENNReal :=
  (contactFactorial (contactCount observed endpoint) : ENNReal) +
    (2 * remaining : Nat) / (Fintype.card State : ENNReal) * (contactCount observed endpoint : ENNReal)
theorem contactMomentPotential_observe_le (observed : Fin n → State → Option State) (query : Fin n × State)
    (endpoint : State) (remaining limit : Nat) (hremaining : remaining ≤ limit) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * contactMomentPotential remaining (record observed query answer) endpoint) ≤
      contactMomentPotential (remaining + 1) observed endpoint + (2 * limit : Nat) / (Fintype.card State : ENNReal)^2 := by
  simp only [contactMomentPotential, expectation_add, expectation_scale]
  calc
    _ ≤ ((contactFactorial (contactCount observed endpoint) : ENNReal) +
          (2 * contactCount observed endpoint : Nat) / (Fintype.card State : ENNReal)) +
        ((2 * remaining : Nat) / (Fintype.card State : ENNReal)) *
          ((contactCount observed endpoint : ENNReal) + 1 / Fintype.card State) :=
      _root_.add_le_add (contactFactorial_observe_le observed query endpoint)
        (mul_le_mul' le_rfl (contactCount_observe_le observed query endpoint))
    _ = (contactFactorial (contactCount observed endpoint) : ENNReal) +
          (2 * (remaining + 1) : Nat) / (Fintype.card State : ENNReal) * (contactCount observed endpoint : ENNReal) +
          (2 * remaining : Nat) / (Fintype.card State : ENNReal)^2 := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv, ENNReal.inv_pow]
      ring
    _ ≤ _ := by
      apply _root_.add_le_add le_rfl
      have h : (2 * remaining : Nat) ≤ 2 * limit := Nat.mul_le_mul_left 2 hremaining
      simpa only [div_eq_mul_inv] using mul_le_mul'
        (show ((2 * remaining : Nat) : ENNReal) ≤ (2 * limit : Nat) by exact_mod_cast h)
        (le_refl ((Fintype.card State : ENNReal)^2)⁻¹)
theorem lazyRun_contactCount_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) (endpoint : State) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (contactCount result.2 endpoint : ENNReal)) ≤
      (contactCount observed endpoint : ENNReal) + (1 / Fintype.card State) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  apply lazyRun_potential_le auxiliary (fun current => (contactCount current endpoint : ENNReal)) (1 / Fintype.card State)
  intro input current
  cases input with
  | inl input => simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | inr query =>
      simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true, Nat.cast_one, mul_one]
      exact contactCount_observe_le current query endpoint
theorem lazyRun_contactFactorial_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (endpoint : State) (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      (contactFactorial (contactCount result.2 endpoint) : ENNReal)) ≤
      contactMomentPotential budget observed endpoint + ((2 * budget : Nat) / (Fintype.card State : ENNReal)^2) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  apply lazyRun_budget_potential_le auxiliary (fun remaining current => contactMomentPotential remaining current endpoint)
    (fun current => (contactFactorial (contactCount current endpoint) : ENNReal))
    ((2 * budget : Nat) / (Fintype.card State : ENNReal)^2) budget
    (fun _ _ => _root_.le_add_of_nonneg_right bot_le) ?_ computation observed budget le_rfl hbound
  intro input current remaining hremaining hpositive
  cases input with
  | inl input => simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | inr query =>
      have hpos : 0 < remaining := by simpa only [IsPrefixQuery, not_true_eq_false, false_or] using hpositive
      cases remaining with
      | zero => omega
      | succ remaining =>
          simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true, Nat.cast_one, mul_one, Nat.add_sub_cancel]
          exact contactMomentPotential_observe_le current query endpoint remaining budget (by omega)
theorem lazyRun_empty_contactCount_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (endpoint : State) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
      (contactCount result.2 endpoint : ENNReal)) ≤
      (1 / Fintype.card State) * ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
        (result.1.2 : ENNReal) := by
  simpa only [contactCount_empty, Nat.cast_zero, zero_add] using lazyRun_contactCount_le auxiliary computation (fun _ _ => none) endpoint
theorem lazyRun_empty_contactFactorial_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (endpoint : State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
      (contactFactorial (contactCount result.2 endpoint) : ENNReal)) ≤
      ((2 * budget : Nat) / (Fintype.card State : ENNReal)^2) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal) := by
  simpa only [contactMomentPotential, contactCount_empty, contactFactorial, Nat.zero_mul, Nat.cast_zero, mul_zero, zero_add] using
    lazyRun_contactFactorial_le auxiliary computation (fun _ _ => none) endpoint budget hbound
theorem lazyRun_empty_contact_correction (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (endpoint : State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    ((budget : ENNReal) / Fintype.card State) *
      (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
        ((contactFactorial (contactCount result.2 endpoint) + 4 * contactCount result.2 endpoint : Nat) : ENNReal)) ≤
      ((4 * ((budget : ENNReal) / Fintype.card State) + 2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal) := by
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, expectation_add, expectation_scale]
  have h := mul_le_mul' (le_refl ((budget : ENNReal) / Fintype.card State))
    (_root_.add_le_add (lazyRun_empty_contactFactorial_le auxiliary computation endpoint budget hbound)
      (mul_le_mul' (le_refl (4 : ENNReal)) (lazyRun_empty_contactCount_le auxiliary computation endpoint)))
  apply h.trans_eq
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, ENNReal.inv_pow]
  ring
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
private theorem compensation_compose {a b c d e f : ENNReal} (hc : c ≠ ⊤)
    (hstep : a + d ≤ b + c) (htail : c + e ≤ d + f) : a + e ≤ b + f := by
  apply (ENNReal.add_le_add_iff_left hc).mp
  calc
    c + (a + e) = a + (c + e) := by ac_rfl
    _ ≤ a + (d + f) := _root_.add_le_add le_rfl htail
    _ = (a + d) + f := by rw [add_assoc]
    _ ≤ (b + c) + f := _root_.add_le_add hstep le_rfl
    _ = c + (b + f) := by ac_rfl
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem lazyRun_compensation (auxiliary : QueryImpl auxSpec PMF)
    (charge weight : Nat → (Fin n → State → Option State) → ENNReal)
    (hfinite : ∀ input observed spent,
      (∑' output, (lazyImpl auxiliary input).run observed output *
        charge (spent + if IsPrefixQuery input then 1 else 0) output.2) ≠ ⊤)
    (hstep : ∀ input observed spent,
      charge spent observed + (∑' output, (lazyImpl auxiliary input).run observed output *
        weight (spent + if IsPrefixQuery input then 1 else 0) output.2) ≤
      weight spent observed + ∑' output, (lazyImpl auxiliary input).run observed output *
        charge (spent + if IsPrefixQuery input then 1 else 0) output.2)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (spent : Nat) :
    charge spent observed + (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      weight (spent + result.1.2) result.2) ≤
    weight spent observed + ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      charge (spent + result.1.2) result.2 := by
  induction computation using OracleComp.inductionOn generalizing observed spent with
  | pure result =>
      simp only [QueryCap.counted_pure, lazyRun_pure, expectation_pure, Nat.add_zero]
      exact le_of_eq (add_comm _ _)
  | query_bind input next ih =>
      simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
        expectation_bind, expectation_map, ← Nat.add_assoc]
      apply compensation_compose (hfinite input observed spent) (hstep input observed spent)
      have h := ENNReal.tsum_le_tsum fun output => mul_le_mul' (le_refl ((lazyImpl auxiliary input).run observed output))
        (ih output.1 output.2 (spent + if IsPrefixQuery input then 1 else 0))
      simpa only [expectation_add] using h
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem lazyRun_twoEdge_compensation (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (observed : Fin (n + 2) → State → Option State) (spent : Nat) (endpoint : State) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State +
      (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * twoEdgeWeight result.2 endpoint) ≤
      twoEdgeWeight observed endpoint + ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
        ((twoEdgeCharge (spent + result.1.2) result.2 endpoint : ENNReal) / Fintype.card State) := by
  apply lazyRun_compensation auxiliary (fun used current => (twoEdgeCharge used current endpoint : ENNReal) / Fintype.card State)
    (fun _ current => twoEdgeWeight current endpoint) ?_ ?_ computation observed spent
  · intro input current used
    have hn : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    cases input with
    | inl input =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.add_zero]
        exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hn
    | inr query =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true]
        change (∑' answer : State, rowLaw (current query.1 query.2) answer *
          ((twoEdgeCharge (used + 1) (record current query answer) endpoint : ENNReal) / Fintype.card State)) ≠ ⊤
        rw [tsum_fintype]
        apply ENNReal.sum_ne_top.mpr
        intro answer _
        exact ENNReal.mul_ne_top (ne_top_of_le_ne_top (by norm_num : (1 : ENNReal) ≠ ⊤) (PMF.coe_le_one _ _))
          (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hn)
  · intro input current used
    cases input with
    | inl input =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.add_zero]
        exact le_of_eq (add_comm _ _)
    | inr query =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true]
        exact twoEdge_observe_compensation used current query endpoint
omit [Nonempty State] in
theorem twoEdgeCharge_div_le (spent budget : Nat) (observed : Fin (n + 2) → State → Option State)
    (endpoint : State) (hs : spent ≤ budget) (hq : queryCount observed ≤ spent) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State ≤
      ((3 / 2 : ENNReal) / Fintype.card State) * (spent : ENNReal) +
        ((budget : ENNReal) / Fintype.card State) *
          ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by
  have hdouble : 2 * (twoEdgeCharge spent observed endpoint : ENNReal) ≤ 3 * (spent : ENNReal) +
      2 * (budget : ENNReal) * ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by
    exact_mod_cast (twoEdgeCharge_twice_le spent budget observed endpoint hs (hq.trans hs)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hq) _)
  have hcast : (twoEdgeCharge spent observed endpoint : ENNReal) ≤ (3 / 2 : ENNReal) * (spent : ENNReal) +
      (budget : ENNReal) * ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by
    apply (ENNReal.mul_le_mul_iff_left (c := 2) (by norm_num) (by norm_num)).mp
    have ht : (3 / 2 : ENNReal) * 2 = 3 := by
      rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
    calc
      _ = 2 * (twoEdgeCharge spent observed endpoint : ENNReal) := mul_comm _ _
      _ ≤ _ := hdouble
      _ = (3 / 2 * 2) * (spent : ENNReal) + 2 * (budget : ENNReal) *
          ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by rw [ht]
      _ = _ := by ring
  have h := mul_le_mul' hcast (le_refl (Fintype.card State : ENNReal)⁻¹)
  simpa only [div_eq_mul_inv, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using h
theorem lazyRun_empty_twoEdge_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec (n + 2) State) Result) (endpoint : State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary computation (fun _ _ => none) result * twoEdgeWeight result.2 endpoint) ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal) := by
  rw [lazyRun_counted_expectation]
  have hc := lazyRun_twoEdge_compensation auxiliary computation (fun _ _ => none) 0 endpoint
  simp only [twoEdgeCharge_empty, Nat.cast_zero, div_eq_mul_inv, zero_mul, twoEdgeWeight_empty, zero_add] at hc
  apply hc.trans
  calc
    _ ≤ ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
        (((3 / 2 : ENNReal) / Fintype.card State) * (result.1.2 : ENNReal) +
          ((budget : ENNReal) / Fintype.card State) *
            ((contactFactorial (contactCount result.2 endpoint) + 4 * contactCount result.2 endpoint : Nat) : ENNReal)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none)).support
      · apply mul_le_mul' le_rfl
        have hq := lazyRun_counted_queryCount_le auxiliary computation (fun _ _ => none) result hr
        simp only [queryCount_empty, Nat.zero_add] at hq
        exact twoEdgeCharge_div_le result.1.2 budget result.2 endpoint (lazyRun_counted_budget_le auxiliary computation _ budget hbound result hr) hq
      · have hz : lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result = 0 := not_not.mp hr
        simp only [hz, zero_mul, le_refl]
    _ = _ := by rw [expectation_add, expectation_scale, expectation_scale]
    _ ≤ _ := by
      have h := _root_.add_le_add
        (le_refl (((3 / 2 : ENNReal) / Fintype.card State) *
          ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal)))
        (lazyRun_empty_contact_correction auxiliary computation endpoint budget hbound)
      apply h.trans_eq
      simp only [div_eq_mul_inv]
      ring
theorem realRun_twoEdge_le (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (budget : Nat) (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget) :
    Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
            (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  rw [show Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] =
      (∑' result, realRun auxiliary computation (fun _ _ => none) result * (if TwoEdge result.2.2 result.1 then 1 else 0)) by
        simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]]
  rw [realRun_expectation]
  simp only [idealRun, expectation_bind, expectation_map]
  rw [← expectation_scale]
  apply ENNReal.tsum_le_tsum
  intro endpoint
  apply mul_le_mul' le_rfl
  exact lazyRun_empty_twoEdge_le (auxiliary endpoint) (computation endpoint) endpoint budget (hbound endpoint)
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
include hcharge hreal
theorem realRun_cap_twoEdge_eq :
    Pr[fun result => TwoEdge result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)] =
        Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] := by
  have h := congrArg (fun law : PMF (State × (Option Result × (Fin (n + 2) → State → Option State))) =>
    Pr[fun result => TwoEdge result.2.2 result.1 | law])
    (realRun_cap_erased_observed auxiliary computation cost budget hcharge hreal)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h
theorem realRun_twoEdge_le_cap_cost (hsmall : budget < Fintype.card State) :
    Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
            (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal) := by
  rw [← realRun_cap_twoEdge_eq auxiliary computation cost budget hcharge hreal]
  have h := realRun_twoEdge_le auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
    budget (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget)
  rw [idealRun_cap_count_expectation auxiliary computation cost budget hcharge hreal hsmall] at h
  exact h
omit hcharge hreal in
def TwoEdgeEvent : {depth : Nat} → (Fin depth → State → Option State) → State → Prop
  | 0, _, _ => False
  | 1, _, _ => False
  | _ + 2, observed, endpoint => TwoEdge observed endpoint
omit hcharge hreal in
theorem realRun_twoEdgeEvent_le_cap_cost {depth : Nat} (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec depth State) Result)
    (cost : Result → Nat) (budget : Nat)
    (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
      result.2 ≤ cost result.1)
    (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
    (hsmall : budget < Fintype.card State) :
    Pr[fun result => TwoEdgeEvent result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
            (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal) := by
  cases depth with
  | zero => simp only [TwoEdgeEvent, probEvent_eq_tsum_ite, if_false, tsum_zero]; exact bot_le
  | succ depth =>
      cases depth with
      | zero => simp only [TwoEdgeEvent, probEvent_eq_tsum_ite, if_false, tsum_zero]; exact bot_le
      | succ depth => exact realRun_twoEdge_le_cap_cost auxiliary computation cost budget hcharge hreal hsmall
end SphincsSecurity.Concrete.PartialChainEndpoint
end
end
-- ==== merged from T3_Secc_WotsMaskRest ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace Mask
variable (a : ChainAddr)
theorem lay_eq_of_header {lay : Layer} {t t' tree pos leaf tree' pos' leaf' : Nat}
    (h : header t lay.val tree pos leaf = header t' a.key.lay.val tree' pos' leaf') : lay = a.key.lay := by
  have hl := (header_fields h).2.1
  apply Fin.ext
  rw [Nat.mod_eq_of_lt (lt_trans lay.isLt (by decide)),
    Nat.mod_eq_of_lt (lt_trans a.key.lay.isLt (by decide))] at hl
  exact hl
theorem untouched_chainInput_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i s : Nat) (v : Digest) :
    Untouched a (.inl (.inr (pad64 (chainInput lay tree leaf i s v)))) := by
  intro step value _
  rw [pad64_chainInput]
  constructor
  · intro heq
    exact hl (chainHeader_fields (chainInput_fields heq).1).1
  · intro heq
    have hb := congrArg Extract.hdrBlock heq
    rw [chainRowG_header, show Extract.hdrBlock (chainInput lay tree leaf i s v) =
      bytesLE 16 (chainHeader lay tree leaf i s) from chainInput_header _ _ _ _ _ _] at hb
    exact hl (chainHeader_fields (bytesLE_injective hb)).1
theorem respects_chain_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i start count : Nat) (v : Digest) :
    Respects (Untouched a) (chain lay tree leaf i start count v) := by
  unfold chain
  exact Respects.foldlM _ _ (fun step _ value => Respects.shortHash _ (untouched_chainInput_of_lay a hl _ _ _ _ _))
    _
variable {T T' : Answers} (hT : ∀ q, Untouched a q → T q = T' q)
include hT
end Mask
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsPrefixGameBase ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_wotsPrefixGameBase : Fintype Coordinate := coordinateFintype
open Mask
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
namespace PrefixGame
theorem uniform_resample {Ω : Type} [Fintype Ω] [Nonempty Ω] {X : ℕ → Type} [∀ k, Fintype (X k)]
    [∀ k, Nonempty (X k)] (d : Ω → ℕ) (ov : ∀ k, Ω → X k → Ω) (rd : ∀ k, Ω → X k)
    (h1 : ∀ ω x, rd (d ω) (ov (d ω) ω x) = x) (h2 : ∀ ω x, ov (d ω) (ov (d ω) ω x) (rd (d ω) ω) = ω)
    (h3 : ∀ ω x, d (ov (d ω) ω x) = d ω) :
    (PMF.uniformOfFintype Ω).bind (fun ω => (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω)) =
      PMF.uniformOfFintype Ω := by
  classical
  let _ : DecidableEq Ω := Classical.decEq Ω
  apply PMF.ext
  intro ω₀
  obtain ⟨k₀, hk₀⟩ : ∃ k, k = d ω₀ := ⟨_, rfl⟩
  let σ : Ω × X k₀ → Ω × X k₀ := fun p =>
    if h : d p.1 = k₀ then (ov k₀ p.1 p.2, rd k₀ p.1) else p
  have hov : ∀ ω (h : d ω = k₀) (x : X k₀), d (ov k₀ ω x) = k₀ := by
    intro ω h x
    subst h
    exact h3 ω x
  have hσ : Function.Involutive σ := by
    rintro ⟨ω, x⟩
    by_cases h : d ω = k₀
    · have h' := hov ω h x
      simp only [σ, dif_pos h, dif_pos h']
      subst h
      rw [h2 ω x, h1 ω x]
    · simp only [σ, dif_neg h]
  have hinner : ∀ ω, (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω) ω₀ =
      if d ω = k₀ then ∑' x : X k₀, PMF.uniformOfFintype (X k₀) x * (if (σ (ω, x)).1 = ω₀ then 1 else 0)
      else 0 := by
    intro ω
    by_cases h : d ω = k₀
    · rw [if_pos h]
      have hgen : ∀ k (hk : d ω = k), (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω) ω₀ =
          (PMF.uniformOfFintype (X k)).map (ov k ω) ω₀ := by
        rintro k rfl; rfl
      rw [hgen k₀ h, PMF.map_apply]
      apply tsum_congr
      intro x
      simp only [σ, dif_pos h]
      by_cases he : ω₀ = ov k₀ ω x
      · rw [if_pos he, if_pos he.symm, mul_one]
      · rw [if_neg he, if_neg (fun h' => he h'.symm), mul_zero]
    · rw [if_neg h, PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      rw [if_neg]
      intro he
      apply h
      rw [hk₀, he, h3 ω x]
  rw [PMF.bind_apply]
  simp only [hinner]
  have hconst : ∀ (ω : Ω) (x : X k₀), PMF.uniformOfFintype Ω ω * PMF.uniformOfFintype (X k₀) x =
      PMF.uniformOfFintype (Ω × X k₀) (ω, x) := by
    intro ω x
    simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
    rw [ENNReal.mul_inv (by simp) (by simp)]
  have hfiber : ∀ ω, PMF.uniformOfFintype Ω ω *
      (if d ω = k₀ then ∑' x : X k₀, PMF.uniformOfFintype (X k₀) x * (if (σ (ω, x)).1 = ω₀ then 1 else 0)
        else 0) =
      ∑' x : X k₀, PMF.uniformOfFintype (Ω × X k₀) (ω, x) * (if (σ (ω, x)).1 = ω₀ then 1 else 0) := by
    intro ω
    by_cases h : d ω = k₀
    · rw [if_pos h, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro x
      rw [← mul_assoc, hconst]
    · rw [if_neg h, mul_zero]
      symm
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      have : (σ (ω, x)).1 = ω := by simp only [σ, dif_neg h]
      rw [this, if_neg (fun he => h (by rw [he, hk₀])), mul_zero]
  simp only [hfiber]
  rw [← ENNReal.tsum_prod (f := fun ω x => PMF.uniformOfFintype (Ω × X k₀) (ω, x) *
    (if (σ (ω, x)).1 = ω₀ then 1 else 0))]
  have hc : ∀ p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) p = PMF.uniformOfFintype (Ω × X k₀) (σ p) := by
    intro p
    simp only [PMF.uniformOfFintype_apply]
  calc (∑' p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) (p.1, p.2) * (if (σ (p.1, p.2)).1 = ω₀ then 1 else 0))
      = ∑' p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) (σ p) * (if (σ p).1 = ω₀ then 1 else 0) := by
        apply tsum_congr
        intro p
        rw [← hc p]
    _ = ∑' p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) p * (if p.1 = ω₀ then 1 else 0) :=
        (hσ.toPerm σ).tsum_eq (fun p => PMF.uniformOfFintype (Ω × X k₀) p * (if p.1 = ω₀ then 1 else 0))
    _ = ∑' x : X k₀, PMF.uniformOfFintype (Ω × X k₀) (ω₀, x) := by
        rw [ENNReal.tsum_prod']
        rw [tsum_eq_single ω₀]
        · simp only [if_true, mul_one]
        · intro ω hω
          apply ENNReal.tsum_eq_zero.mpr
          intro x
          rw [if_neg hω, mul_zero]
    _ = PMF.uniformOfFintype Ω ω₀ := by
        simp only [← hconst, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
end PrefixGame
abbrev RefTables (adversary : AdversaryP) := FullGame.FullTable × (referenceInputs adversary → HashOutput)
noncomputable instance instFintypeRefTables (adversary : AdversaryP) : Fintype (RefTables adversary) := by
  unfold RefTables FullGame.FullTable
  infer_instance
instance instNonemptyRefTables (adversary : AdversaryP) : Nonempty (RefTables adversary) := ⟨(fun _ => 0, fun _ => 0)⟩
noncomputable def restTable {adversary : AdversaryP} (R : RefTables adversary) : Answers :=
  eagerAnswers (referenceInputs adversary) R.1 R.2
@[irreducible] noncomputable def restDepth {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary) : Nat :=
  depth (restTable R) a
namespace PrefixGame
variable {adversary : AdversaryP}
def high (output : HashOutput) : Digest := output.extractLsb' 128 128
def seedHalf (a : ChainAddr) (output : HashOutput) : Digest :=
  if a.chain % 2 = 0 then output.extractLsb' 0 128 else output.extractLsb' 128 128
noncomputable def setSeed (a : ChainAddr) (output : HashOutput) (seed : Digest) : HashOutput :=
  if a.chain % 2 = 0 then ChainGraph.joinOutput seed (output.extractLsb' 128 128)
  else ChainGraph.joinOutput (output.extractLsb' 0 128) seed
theorem seedHalf_setSeed (a : ChainAddr) (output : HashOutput) (seed : Digest) :
    seedHalf a (setSeed a output seed) = seed := by
  unfold seedHalf setSeed
  by_cases h : a.chain % 2 = 0
  · rw [if_pos h, if_pos h, ChainGraph.joinOutput_low]
  · rw [if_neg h, if_neg h, ChainGraph.joinOutput_high]
theorem setSeed_seedHalf (a : ChainAddr) (output : HashOutput) : setSeed a output (seedHalf a output) = output := by
  unfold seedHalf setSeed
  by_cases h : a.chain % 2 = 0
  · rw [if_pos h, if_pos h, ChainGraph.joinOutput_parts]
  · rw [if_neg h, if_neg h, ChainGraph.joinOutput_parts]
theorem setSeed_setSeed (a : ChainAddr) (output : HashOutput) (seed seed' : Digest) :
    setSeed a (setSeed a output seed) seed' = setSeed a output seed' := by
  unfold setSeed
  by_cases h : a.chain % 2 = 0
  · rw [if_pos h, if_pos h, if_pos h, ChainGraph.joinOutput_high]
  · rw [if_neg h, if_neg h, if_neg h, ChainGraph.joinOutput_low]
theorem siblingHalf_setSeed (a : ChainAddr) (output : HashOutput) (seed : Digest) :
    siblingHalf a (setSeed a output seed) = siblingHalf a output := by
  unfold siblingHalf setSeed
  by_cases h : a.chain % 2 = 0
  · rw [if_pos h, if_pos h, if_pos h, ChainGraph.joinOutput_high]
  · rw [if_neg h, if_neg h, if_neg h, ChainGraph.joinOutput_low]
noncomputable def rowOf (a : ChainAddr) (d : Nat) (input : HashInput) : Option (Fin d × Digest) :=
  if h : ∃ p : Fin d × Digest, input = chainRow a p.1 p.2 then some (Classical.choose h) else none
theorem rowOf_some {a : ChainAddr} {d : Nat} {input : HashInput} {p : Fin d × Digest}
    (h : rowOf a d input = some p) : input = chainRow a p.1 p.2 := by
  unfold rowOf at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h
theorem rowOf_none {a : ChainAddr} {d : Nat} {input : HashInput} (h : rowOf a d input = none) (p : Fin d × Digest) :
    input ≠ chainRow a p.1 p.2 := by
  intro he
  unfold rowOf at h
  rw [dif_pos ⟨p, he⟩] at h
  cases h
theorem rowOf_chainRow (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (i : Fin d) (v : Digest) :
    rowOf a d (chainRow a i v) = some (i, v) := by
  cases h : rowOf a d (chainRow a i v) with
  | none => exact absurd rfl (rowOf_none h (i, v))
  | some p =>
      have he := rowOf_some h
      obtain ⟨hs, hv⟩ := chainRow_inj (by omega) (by have := p.1.isLt; omega) he
      rw [show p = (i, v) from Prod.ext (Fin.ext hs.symm) hv.symm]
theorem rowOf_none_iff (a : ChainAddr) {d : Nat} (input : HashInput) :
    rowOf a d input = none ↔ ¬∃ step value, step < d ∧ input = chainRow a step value := by
  constructor
  · rintro h ⟨step, value, hs, rfl⟩
    exact rowOf_none h (⟨step, hs⟩, value) rfl
  · intro h
    cases hp : rowOf a d input with
    | none => rfl
    | some p => exact absurd ⟨p.1.val, p.2, p.1.isLt, rowOf_some hp⟩ h
theorem chainRow_mem (a : ChainAddr) (step : Nat) (value : Digest) :
    chainRow a step value ∈ referenceInputs adversary := by
  unfold referenceInputs
  apply Finset.mem_union_left
  apply SeccLaw.mem_publicUniverse
  rw [chainRow_eq]
  have h : (chainInput a.key.lay a.key.tree a.key.leaf a.chain step value).length = 64 := by
    simp [chainInput, zero16, SphincsSecurity.bytesLE_length]
  rw [h]
  unfold SeccLaw.maxInputLength
  omega
abbrev Hidden (d : Nat) := (Fin d → Digest → Digest) × Digest
noncomputable def ovPub (a : ChainAddr) (d : Nat) (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) : referenceInputs adversary → HashOutput := fun x =>
  match rowOf a d x.val with
  | some p => ChainGraph.joinOutput (tables p.1 p.2) (high (pub x))
  | none => pub x
noncomputable def ovPriv (a : ChainAddr) (priv : FullGame.FullTable) (seed : Digest) : FullGame.FullTable :=
  Function.update priv (.inl (seedTweak a)) (setSeed a (priv (.inl (seedTweak a))) seed)
noncomputable def ov (a : ChainAddr) (d : Nat) (R : RefTables adversary) (x : Hidden d) : RefTables adversary :=
  (ovPriv a R.1 x.2, ovPub a d R.2 x.1)
noncomputable def rd (a : ChainAddr) (d : Nat) (R : RefTables adversary) : Hidden d :=
  (fun i v => low (R.2 ⟨chainRow a i v, chainRow_mem a i v⟩), seedHalf a (R.1 (.inl (seedTweak a))))
end PrefixGame
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from SphincsSecurity_Proof_Chains_AdaptiveChainCheckpoint ====
section

section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem lazyRun_contact_charge (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (endpoint : State) (hc : ¬Contact observed endpoint) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      (meanPreimages result.2 endpoint * (if Contact result.2 endpoint then 1 else 0))) ≤
      (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
        ((queryCount observed + 2 * result.1.2 : Nat) : ENNReal)) / Fintype.card State := by
  have h := lazyRun_contactPotential_le auxiliary computation observed endpoint
  rw [lazyRun_counted_expectation] at h
  have hinit : contactPotential observed endpoint ≤ (queryCount observed : ENNReal) / Fintype.card State := by
    rw [contactPotential, if_neg hc]
    have hp : pendingCount observed ≤ queryCount observed := Nat.sub_le _ _
    simpa only [div_eq_mul_inv] using mul_le_mul' (show (pendingCount observed : ENNReal) ≤ queryCount observed by exact_mod_cast hp)
      (le_refl (Fintype.card State : ENNReal)⁻¹)
  calc
    _ ≤ ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * contactPotential result.2 endpoint :=
      ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (contactPotential_dominates result.2 endpoint)
    _ ≤ (queryCount observed : ENNReal) / Fintype.card State + (2 / Fintype.card State) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) :=
      h.trans (_root_.add_le_add hinit le_rfl)
    _ = _ := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, expectation_add, expectation_const, expectation_scale, div_eq_mul_inv]
      ring
theorem run_contact_charge_transfer (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (endpoint : State) (hc : ¬Contact observed endpoint) (budget : Nat)
    (hbudget : ∀ result ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed).support,
      queryCount result.2 ≤ budget) :
    (1 - (budget : ENNReal) / Fintype.card State) * ((Fintype.card State : ENNReal) *
      ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
        (meanPreimages result.2 endpoint * (if Contact result.2 endpoint then 1 else 0))) ≤
      ∑' tables, completeTables observed tables * ∑' result,
        observedRun auxiliary tables (QueryCap.counted IsPrefixQuery computation) observed result *
          ((EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) *
            ((queryCount observed + 2 * result.1.2 : Nat) : ENNReal)) := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcharge := mul_le_mul' (le_refl (Fintype.card State : ENNReal))
    (lazyRun_contact_charge auxiliary computation observed endpoint hc)
  simp only [div_eq_mul_inv, mul_left_comm (Fintype.card State : ENNReal),
    ENNReal.mul_inv_cancel hcard (by finiteness), mul_one] at hcharge
  apply (mul_le_mul' (le_refl (1 - (budget : ENNReal) / Fintype.card State)) hcharge).trans
  exact run_allocated_cost_lower auxiliary (QueryCap.counted IsPrefixQuery computation) observed endpoint
    (fun result => ((queryCount observed + 2 * result.1.2 : Nat) : ENNReal)) budget hbudget
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Checkpoint Result : Type}
theorem run_posterior_payoff (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (payoff : (Fin n → State → State) → Result × (Fin n → State → Option State) → ENNReal) :
    (∑' tables, completeTables observed tables *
      ∑' result, observedRun auxiliary tables computation observed result * payoff tables result) =
    ∑' result, lazyRun auxiliary computation observed result *
      ∑' tables, completeTables result.2 tables * payoff tables result := by
  have h := congrArg (fun law : PMF ((Fin n → State → State) × (Result × (Fin n → State → Option State))) =>
    ∑' result, law result * payoff result.1 result.2) (run_posterior auxiliary computation observed)
  simpa only [expectation_bind, expectation_map] using h
theorem observedRun_supported_completion (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (tables : Fin n → State → State) (htables : tables ∈ (completeTables observed).support)
    (result : Result × (Fin n → State → Option State)) (hresult : result ∈ (observedRun auxiliary tables computation observed).support) :
    result ∈ (lazyRun auxiliary computation observed).support ∧ tables ∈ (completeTables result.2).support := by
  have hpair : (tables, result) ∈ ((completeTables observed).bind fun tables =>
      (observedRun auxiliary tables computation observed).map fun result => (tables, result)).support := by
    rw [PMF.mem_support_bind_iff]
    refine ⟨tables, htables, ?_⟩
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  rw [run_posterior, PMF.mem_support_bind_iff] at hpair
  obtain ⟨middle, hmiddle, hpair⟩ := hpair
  rw [PMF.mem_support_map_iff] at hpair
  obtain ⟨completed, hcompleted, heq⟩ := hpair
  simp only [Prod.mk.injEq] at heq
  rcases heq with ⟨rfl, rfl⟩
  exact ⟨hmiddle, hcompleted⟩
theorem realRun_support_lazy (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (result : State × (Result × (Fin n → State → Option State)))
    (hr : result ∈ (realRun auxiliary computation observed).support) :
    result.2 ∈ (lazyRun (auxiliary result.1) (computation result.1) observed).support := by
  rw [realRun, PMF.mem_support_bind_iff] at hr
  obtain ⟨⟨tables, endpoint⟩, hsource, hr⟩ := hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨output, ho, rfl⟩ := hr
  have ht : tables ∈ (completeTables observed).support := by
    intro hz
    apply hsource
    simp only [EndpointPreimageDensity.real_apply, hz, zero_mul]
  exact (observedRun_supported_completion (auxiliary endpoint) (computation endpoint) observed tables ht output ho).1
noncomputable def checkpointObservedRun (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (before : OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    PMF ((Checkpoint × (Fin n → State → Option State)) × ((Result × Nat) × (Fin n → State → Option State))) :=
  (observedRun auxiliary tables before observed).bind fun middle =>
    (observedRun auxiliary tables (QueryCap.counted IsPrefixQuery (after middle)) middle.2).map fun result => (middle, result)
noncomputable def realCheckpointRun (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    PMF (State × (Checkpoint × (Fin n → State → Option State)) × ((Result × Nat) × (Fin n → State → Option State))) :=
  (EndpointPreimageDensity.real (completeTables observed) evaluate).bind fun pair =>
    (checkpointObservedRun (auxiliary pair.2) pair.1 (before pair.2) (after pair.2) observed).map fun result => (pair.2, result)
theorem realCheckpointRun_support (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State)
    (result : State × (Checkpoint × (Fin n → State → Option State)) × ((Result × Nat) × (Fin n → State → Option State)))
    (hresult : result ∈ (realCheckpointRun auxiliary before after observed).support) :
    result.2.1 ∈ (lazyRun (auxiliary result.1) (before result.1) observed).support ∧
      result.2.2 ∈ (lazyRun (auxiliary result.1) (QueryCap.counted IsPrefixQuery (after result.1 result.2.1)) result.2.1.2).support := by
  classical
  rw [realCheckpointRun, PMF.mem_support_bind_iff] at hresult
  obtain ⟨⟨tables, endpoint⟩, hsource, hresult⟩ := hresult
  rw [PMF.mem_support_map_iff] at hresult
  obtain ⟨pair, hpair, rfl⟩ := hresult
  rw [checkpointObservedRun, PMF.mem_support_bind_iff] at hpair
  obtain ⟨middle, hmiddle, hpair⟩ := hpair
  rw [PMF.mem_support_map_iff] at hpair
  obtain ⟨final, hfinal, rfl⟩ := hpair
  have ht : tables ∈ (completeTables observed).support := by
    intro hz
    apply hsource
    simp only [EndpointPreimageDensity.real_apply, hz, zero_mul]
  have hm := observedRun_supported_completion (auxiliary endpoint) (before endpoint) observed tables ht middle hmiddle
  exact ⟨hm.1, (observedRun_supported_completion (auxiliary endpoint) (QueryCap.counted IsPrefixQuery (after endpoint middle))
    middle.2 tables hm.2 final hfinal).1⟩
theorem realCheckpointRun_before (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    (realCheckpointRun auxiliary before after observed).map (fun result => (result.1, result.2.1)) =
      realRun auxiliary before observed := by
  simp only [realCheckpointRun, checkpointObservedRun, realRun, PMF.map_bind, PMF.map_comp, Function.comp_def]
  simp only [PMF.map, Function.comp_def, PMF.bind_const]
theorem realCheckpointRun_expectation (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State)
    (payoff : State × (Checkpoint × (Fin n → State → Option State)) × ((Result × Nat) × (Fin n → State → Option State)) → ENNReal) :
    (∑' result, realCheckpointRun auxiliary before after observed result * payoff result) =
    ∑' endpoint, PMF.uniformOfFintype State endpoint * ∑' middle, lazyRun (auxiliary endpoint) (before endpoint) observed middle *
      ∑' tables, completeTables middle.2 tables *
        ∑' result, observedRun (auxiliary endpoint) tables (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2 result *
          ((EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) * payoff (endpoint, middle, result)) := by
  classical
  simp only [realCheckpointRun, expectation_bind, expectation_map]
  rw [EndpointPreimageDensity.real_payoff, ENNReal.tsum_prod', ENNReal.tsum_comm]
  simp only [EndpointPreimageDensity.ideal_apply, div_eq_mul_inv, PMF.uniformOfFintype_apply,
    checkpointObservedRun, expectation_bind, expectation_map]
  apply tsum_congr
  intro endpoint
  rw [← run_posterior_payoff (auxiliary endpoint) (before endpoint) observed
    (fun tables middle => ∑' result,
      observedRun (auxiliary endpoint) tables (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2 result *
        ((EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) * payoff (endpoint, middle, result)))]
  simp only [expectation_scale]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro tables
  ring
theorem realCheckpointRun_density (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State)
    (payoff : State × (Checkpoint × (Fin n → State → Option State)) × ((Result × Nat) × (Fin n → State → Option State)) → ENNReal) :
    (∑' result, realCheckpointRun auxiliary before after observed result * payoff result) =
    ∑' endpoint, PMF.uniformOfFintype State endpoint * ∑' middle, lazyRun (auxiliary endpoint) (before endpoint) observed middle *
      ∑' result, lazyRun (auxiliary endpoint) (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2 result *
        (meanPreimages result.2 endpoint * payoff (endpoint, middle, result)) := by
  rw [realCheckpointRun_expectation]
  apply tsum_congr
  intro endpoint
  congr 1
  apply tsum_congr
  intro middle
  congr 1
  exact run_weighted_payoff (auxiliary endpoint) (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2 endpoint
    (fun result => payoff (endpoint, middle, result))
end SphincsSecurity.Concrete.PartialChainEndpoint
end
end
-- ==== merged from T3_Secc_WotsPrefixGameSim ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl record realRun lazyRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
noncomputable local instance instFintypeCoordinate_wotsPrefixGameSim : Fintype Coordinate := coordinateFintype
open Mask
abbrev SeedResult := Option (Bool × Nat) × List RefWorld.Domain
namespace PrefixGame
variable {adversary : AdversaryP}
abbrev SeedSpec (d : Nat) := unifSpec + PrefixSpec d Digest
theorem evaluate_const : ∀ (n : Nat) (value : Digest),
    evaluate (fun (_ : Fin n) (_ : Digest) => value) value = value
  | 0, _ => rfl
  | n + 1, value => by
      simp only [evaluate]
      exact evaluate_const n value
end PrefixGame
namespace PrefixGame
variable {adversary : AdversaryP}
def PrefixQuery (a : ChainAddr) (d : Nat) (query : RefWorld.Domain) : Prop :=
  ∃ (i : Fin d) (v : Digest), query = .inl (.inr (chainRow a i v))
theorem observedRun_bind {d : Nat} {α β : Type} (tables : Fin d → Digest → Digest)
    (first : OracleComp (SeedSpec d) α) (next : α → OracleComp (SeedSpec d) β)
    (observed : Fin d → Digest → Option Digest) :
    observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables (first >>= next) observed =
      (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables first observed).bind fun r =>
        observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables (next r.1) r.2 := by
  simp only [observedRun, simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind]
end PrefixGame
namespace PrefixGame
theorem lazyRun_mem_support {d : Nat} {β : Type} (computation : OracleComp (SeedSpec d) β) :
    ∀ (observed : Fin d → Digest → Option Digest) (result : β × (Fin d → Digest → Option Digest)),
      result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl computation observed).support →
        result.1 ∈ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro observed result hr
      rw [SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff] at hr
      subst hr
      exact (mem_support_pure_iff _ _).mpr rfl
  | query_bind input next ih =>
      intro observed result hr
      rw [SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_query_bind] at hr
      rw [mem_support_bind_iff]
      cases input with
      | inl input =>
          simp only [SphincsSecurity.Concrete.PartialChainEndpoint.lazyImpl, StateT.run_mk, PMF.bind_map,
            PMF.mem_support_bind_iff] at hr
          obtain ⟨answer, _, hr⟩ := hr
          exact ⟨answer, by simp only [support_query, Set.mem_univ], ih answer observed result hr⟩
      | inr query =>
          simp only [SphincsSecurity.Concrete.PartialChainEndpoint.lazyImpl, StateT.run_mk, PMF.bind_map,
            PMF.mem_support_bind_iff] at hr
          obtain ⟨answer, _, hr⟩ := hr
          exact ⟨answer, by simp only [support_query, Set.mem_univ], ih answer _ result hr⟩
end PrefixGame
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsPrefixGame ====
section

section
namespace SphincsSecurity.Concrete.OtsContactTrace
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] contacts
variable (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
end SphincsSecurity.Concrete.OtsContactTrace
end
section
namespace SphincsSecurity.Concrete.OtsContactTrace
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] contacts
end SphincsSecurity.Concrete.OtsContactTrace
end
section
namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end SphincsSecurity.Concrete.OtsPrefix
end
section
namespace SphincsSecurity.Concrete.OtsContactTrace
open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def SeenRow (segment : OtsPrefix) (query : segment.Query) (answer : Digest) (trace : Trace) : Prop :=
  ∃ entry ∈ trace.toList, segment.parse entry.1 = some query ∧ truncateHash entry.2 = answer
end SphincsSecurity.Concrete.OtsContactTrace
namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec PartialChainEndpoint OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end SphincsSecurity.Concrete.OtsPrefix
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
theorem twoEdgeEvent_iff_rows {State : Type} {depth : Nat} (observed : Fin depth → State → Option State) (endpoint : State) :
    TwoEdgeEvent observed endpoint ↔ ∃ first last : Fin depth × State,
      first.1.val + 2 = depth ∧ last.1.val + 1 = depth ∧
        observed first.1 first.2 = some last.2 ∧ observed last.1 last.2 = some endpoint := by
  cases depth with
  | zero => simp only [TwoEdgeEvent, Prod.exists, Fin.exists_fin_zero]
  | succ depth =>
      cases depth with
      | zero =>
          constructor
          · exact False.elim
          · rintro ⟨first, _, hf, _⟩
            omega
      | succ depth =>
          constructor
          · rintro ⟨start, middle, hf, hl⟩
            exact ⟨⟨(Fin.last depth).castSucc, start⟩, ⟨Fin.last (depth + 1), middle⟩, rfl, rfl, hf, hl⟩
          · rintro ⟨⟨first, start⟩, ⟨last, middle⟩, hf, hl, hfirst, hlast⟩
            change first.val + 2 = depth + 2 at hf
            change last.val + 1 = depth + 2 at hl
            have hfi : first = (Fin.last depth).castSucc := by
              apply Fin.ext
              simp only [Fin.val_castSucc, Fin.val_last]
              omega
            have hla : last = Fin.last (depth + 1) := by
              apply Fin.ext
              simp only [Fin.val_last]
              omega
            subst first last
            exact ⟨start, middle, hfirst, hlast⟩
end SphincsSecurity.Concrete.PartialChainEndpoint
namespace SphincsSecurity.Concrete.OtsContactTrace
set_option backward.isDefEq.respectTransparency false
end SphincsSecurity.Concrete.OtsContactTrace
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl record realRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
noncomputable local instance instFintypeCoordinate_wotsPrefixGame : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsPrefixGame : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_wotsPrefixGame (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype _
namespace PrefixGame
theorem liftM_bind {α β : Type} (c : ProbComp α) (f : α → ProbComp β) :
    (liftM (c >>= f) : PMF β) = (liftM c : PMF α).bind (fun x => (liftM (f x) : PMF β)) := by
  show simulateQ _ (c >>= f) = _
  rw [simulateQ_bind]
  rfl
theorem liftM_map {α β : Type} (c : ProbComp α) (f : α → β) :
    (liftM (f <$> c) : PMF β) = (liftM c : PMF α).map f := by
  show simulateQ _ (f <$> c) = _
  rw [simulateQ_map]
  rfl
theorem liftM_apply {α : Type} (c : ProbComp α) (x : α) : (liftM c : PMF α) x = Pr[= x | c] := by
  rw [← PMF.probOutput_eq_apply]
  have h1 : 𝒮[(liftM c : PMF α)] = 𝒮[c] := by
    rw [evalSPMF_eq_simulateQ, PMF.evalSPMF_eq]
    rfl
  unfold probOutput
  rw [h1]
theorem liftM_uniform (α : Type) [Fintype α] [Nonempty α] [SampleableType α] :
    (liftM ($ᵗ α : ProbComp α) : PMF α) = PMF.uniformOfFintype α := by
  apply PMF.ext
  intro x
  rw [liftM_apply, probOutput_uniformSample, PMF.uniformOfFintype_apply]
theorem map_congr_support {α β : Type} (p : PMF α) (f g : α → β) (h : ∀ x ∈ p.support, f x = g x) :
    p.map f = p.map g := by
  apply PMF.ext
  intro y
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ p.support
  · rw [h x hx]
  · rw [PMF.apply_eq_zero_iff p x |>.mpr hx]
    simp only [ite_self]
theorem uniform_prod (α β : Type) [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    PMF.uniformOfFintype (α × β) =
      (PMF.uniformOfFintype α).bind (fun x => (PMF.uniformOfFintype β).map (fun y => (x, y))) :=
  SphincsSecurity.Concrete.UniformTableSplit.uniform_product
end PrefixGame
noncomputable def mkSample (T : Answers) (run : SeedResult) : RefSample :=
  ⟨T, (evalWithAnswerFn T keygen).1, traceOf T run.2⟩
theorem mem_traceOf (T : Answers) (qs : List RefWorld.Domain) (input : HashInput) (answer : HashOutput) :
    (input, answer) ∈ traceOf T qs ↔
      (.inl (.inr input) : RefWorld.Domain) ∈ qs ∧ answer = T (.inl (.inr input)) := by
  unfold traceOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨query, hq, he⟩
    rcases query with (n | x) | u
    · cases he
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨hq, rfl⟩
    · cases he
  · rintro ⟨hq, rfl⟩
    exact ⟨_, hq, rfl⟩
theorem traceOf_find (T : Answers) (x : HashInput) :
    ∀ qs : List RefWorld.Domain, (traceOf T qs).find? (fun e => decide (e.1 = x)) =
      if (.inl (.inr x) : RefWorld.Domain) ∈ qs then some (x, T (.inl (.inr x))) else none
  | [] => by simp [traceOf]
  | query :: qs => by
      rcases query with (n | input) | u
      · have h : traceOf T (.inl (.inl n) :: qs) = traceOf T qs := rfl
        rw [h, traceOf_find T x qs]
        simp
      · have h : traceOf T (.inl (.inr input) :: qs) = (input, T (.inl (.inr input))) :: traceOf T qs := rfl
        rw [h, List.find?_cons]
        by_cases hx : input = x
        · subst hx
          simp only [decide_true, List.mem_cons, true_or, if_true]
        · rw [show decide ((input, T (.inl (.inr input))).1 = x) = false from decide_eq_false hx]
          simp only
          rw [traceOf_find T x qs]
          have hne : (.inl (.inr x) : RefWorld.Domain) ≠ .inl (.inr input) := fun he => hx (by cases he; rfl)
          simp only [List.mem_cons, hne, false_or]
      · have h : traceOf T (.inr u :: qs) = traceOf T qs := rfl
        rw [h, traceOf_find T x qs]
        simp
theorem traceOf_filter_length (T : Answers) (P : HashInput → Prop) :
    ∀ qs : List RefWorld.Domain, ((traceOf T qs).filter fun e => decide (P e.1)).length =
      SphincsSecurity.QueryCap.calls (fun query : RefWorld.Domain => ∃ x, query = .inl (.inr x) ∧ P x) qs
  | [] => rfl
  | query :: qs => by
      rw [SphincsSecurity.QueryCap.calls_cons, ← traceOf_filter_length T P qs]
      rcases query with (n | input) | u
      · have h : traceOf T (.inl (.inl n) :: qs) = traceOf T qs := rfl
        rw [h, if_neg]
        · simp only [Nat.zero_add]
        · rintro ⟨x, hx, -⟩
          cases hx
      · have h : traceOf T (.inl (.inr input) :: qs) = (input, T (.inl (.inr input))) :: traceOf T qs := rfl
        rw [h, List.filter_cons]
        by_cases hp : P input
        · rw [if_pos (decide_eq_true hp), if_pos ⟨input, rfl, hp⟩, List.length_cons]
          omega
        · rw [if_neg (by simpa using hp), if_neg]
          · simp only [Nat.zero_add]
          · rintro ⟨x, hx, hpx⟩
            cases hx
            exact hp hpx
      · have h : traceOf T (.inr u :: qs) = traceOf T qs := rfl
        rw [h, if_neg]
        · simp only [Nat.zero_add]
        · rintro ⟨x, hx, -⟩
          cases hx
def PrefixRowAt (answers : Answers) (a : ChainAddr) (input : HashInput) : Prop :=
  ∃ step value, step < depth answers a ∧ input = chainRow a step value
structure PrefixView where
  depth : Nat
  frontier : Digest
  rows : Nat → Digest → Option Digest
  count : Nat
noncomputable def prefixCount (a : ChainAddr) (s : RefSample) : Nat :=
  (s.trace.filter fun e => decide (PrefixRowAt s.answers a e.1)).length
def PrefixView.TwoEdge (v : PrefixView) : Prop :=
  2 ≤ v.depth ∧ ∃ start middle, v.rows (v.depth - 2) start = some middle ∧ v.rows (v.depth - 1) middle = some v.frontier
def PrefixView.Contact (v : PrefixView) : Prop :=
  1 ≤ v.depth ∧ ∃ value, v.rows (v.depth - 1) value = some v.frontier
theorem pmf_probEvent_congr {α : Type} (p : PMF α) (E F : α → Prop) (h : ∀ x ∈ p.support, E x ↔ F x) :
    Pr[E | p] = Pr[F | p] := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ p.support
  · by_cases he : E x
    · rw [if_pos he, if_pos ((h x hx).mp he)]
    · rw [if_neg he, if_neg (fun hf => he ((h x hx).mpr hf))]
  · rw [PMF.probOutput_eq_apply, (PMF.apply_eq_zero_iff p x).mpr hx]
    simp only [ite_self]
theorem pmf_probEvent_mono {α : Type} (p : PMF α) (E F : α → Prop) (h : ∀ x ∈ p.support, E x → F x) :
    Pr[E | p] ≤ Pr[F | p] := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases he : E x
  · by_cases hx : x ∈ p.support
    · rw [if_pos he, if_pos (h x hx he)]
    · rw [if_pos he, PMF.probOutput_eq_apply, (PMF.apply_eq_zero_iff p x).mpr hx]
      exact bot_le
  · rw [if_neg he]
    exact bot_le
end SigGolfCandidate.T3.Security.Wots
end
end
-- ==== merged from T3_Secc_WotsEncodingMatch ====
section

section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
namespace Enc.Lazy
section World
variable {ι : Type} (cellInput : ι → HashInput) (F : Set ι)
abbrev World := RefWorld + UniformTableObservation.TableSpec F HashOutput
def IsCell (input : HashInput) : Prop := ∃ e, e ∈ F ∧ cellInput e = input
noncomputable def cellOf (input : HashInput) (h : IsCell cellInput F input) : F :=
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩
theorem cellOf_input (input : HashInput) (h : IsCell cellInput F input) :
    cellInput (cellOf cellInput F input h).val = input := (Classical.choose_spec h).2
noncomputable def translate : QueryImpl RefWorld (OracleComp (World F))
  | .inl (.inl n) => liftM ((World F).query (.inl (.inl (.inl n))))
  | .inl (.inr input) =>
      if h : IsCell cellInput F input then liftM ((World F).query (.inr (cellOf cellInput F input h)))
      else liftM ((World F).query (.inl (.inl (.inr input))))
  | .inr u => liftM ((World F).query (.inl (.inr u)))
noncomputable def aux (T : Answers) : QueryImpl RefWorld SPMF := fun q => 𝒮[refImpl T q]
noncomputable def overwrite (T : Answers) (y : F → HashOutput) : Answers
  | .inl (.inl n) => T (.inl (.inl n))
  | .inl (.inr input) => if h : IsCell cellInput F input then y (cellOf cellInput F input h) else T (.inl (.inr input))
  | .inr c => T (.inr c)
theorem fixed_translate (T : Answers) (y : F → HashOutput) (q : RefWorld.Domain) :
    simulateQ (UniformTableObservation.fixedImpl (aux T) y) (translate cellInput F q) =
      𝒮[refImpl (overwrite cellInput F T y) q] := by
  rcases q with (n | input) | u
  · simp only [translate, simulateQ_spec_query, UniformTableObservation.fixedImpl, aux, refImpl]
  · by_cases h : IsCell cellInput F input
    · simp only [translate, dif_pos h, simulateQ_spec_query, UniformTableObservation.fixedImpl, refImpl,
        overwrite, evalSPMF_pure]
    · simp only [translate, dif_neg h, simulateQ_spec_query, UniformTableObservation.fixedImpl, aux, refImpl,
        overwrite, evalSPMF_pure]
  · simp only [translate, simulateQ_spec_query, UniformTableObservation.fixedImpl, aux, refImpl]
theorem fixed_run {β : Type} (T : Answers) (y : F → HashOutput) (C : OracleComp RefWorld β) :
    simulateQ (UniformTableObservation.fixedImpl (aux T) y) (simulateQ (translate cellInput F) C) =
      𝒮[simulateQ (refImpl (overwrite cellInput F T y)) C] := by
  induction C using OracleComp.inductionOn with
  | pure result => simp only [simulateQ_pure, evalSPMF_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalSPMF_bind, ih, fixed_translate]
variable [Fintype F] [DecidableEq F]
theorem eager_lazy {β : Type} (T : Answers) (C : OracleComp RefWorld β) :
    (complete (fun _ : F => (Finset.univ : Finset HashOutput)) >>= fun y =>
      𝒮[simulateQ (refImpl (overwrite cellInput F T y)) C]) =
      Prod.fst <$> UniformTableObservation.lazyRun (aux T) (simulateQ (translate cellInput F) C)
        (fun _ => Finset.univ) := by
  rw [← UniformTableObservation.run_marginal (aux T) (simulateQ (translate cellInput F) C) _
    (fun _ => Finset.univ_nonempty)]
  simp only [fixed_run]
theorem eager_lazy_init {β : Type} (T : Answers) (C : OracleComp RefWorld β) (init : F → Finset HashOutput)
    (hinit : ∀ e, (init e).Nonempty) :
    (complete init >>= fun y => 𝒮[simulateQ (refImpl (overwrite cellInput F T y)) C]) =
      Prod.fst <$> UniformTableObservation.lazyRun (aux T) (simulateQ (translate cellInput F) C) init := by
  rw [← UniformTableObservation.run_marginal (aux T) (simulateQ (translate cellInput F) C) _ hinit]
  simp only [fixed_run]
noncomputable def lazyImpl (T : Answers) : QueryImpl RefWorld (StateT (F → Finset HashOutput) SPMF) :=
  (UniformTableObservation.lazyImpl (aux T)).compose (translate cellInput F)
theorem lazyRun_eq_simulate {β : Type} (T : Answers) (C : OracleComp RefWorld β) (allowed : F → Finset HashOutput) :
    UniformTableObservation.lazyRun (aux T) (simulateQ (translate cellInput F) C) allowed =
      (simulateQ (lazyImpl cellInput F T) C).run allowed := by
  rw [UniformTableObservation.lazyRun, lazyImpl, QueryImpl.simulateQ_compose]
end World
def obs : (q : RefWorld.Domain) → RefWorld.Range q → FreeMonoid Entry
  | .inl (.inl _), _ => 1
  | .inl (.inr input), answer => FreeMonoid.of (input, answer)
  | .inr _, _ => 1
theorem recorded_traced {α : Type} (T : Answers) (C : OracleComp RefWorld α) :
    (fun r => (r.1, traceOf T r.2)) <$> simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded C) =
      (fun r => (r.1, FreeMonoid.toList r.2)) <$> simulateQ (refImpl T) (SphincsSecurity.QueryPause.traced obs C) := by
  induction C using OracleComp.inductionOn with
  | pure result =>
      simp only [SphincsSecurity.QueryCap.recorded_pure, SphincsSecurity.QueryPause.traced_pure, simulateQ_pure,
        map_pure]
      rfl
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryPause.traced_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_map, simulateQ_pure, map_bind]
      rcases input with (n | x) | u
      · congr 1
        funext answer
        have h := congrArg (fun c => (fun r : α × List Entry => (r.1, (obs (.inl (.inl n)) answer).toList ++ r.2)) <$> c)
          (ih answer)
        simp only [Functor.map_map] at h
        simpa [obs, traceOf, bind_pure_comp] using h
      · have h := congrArg (fun c => (fun r : α × List Entry =>
          (r.1, (obs (.inl (.inr x)) (T (.inl (.inr x)))).toList ++ r.2)) <$> c) (ih (T (.inl (.inr x))))
        simp only [Functor.map_map] at h
        simp only [refImpl, pure_bind]
        simpa [obs, traceOf, bind_pure_comp] using h
      · congr 1
        funext answer
        have h := congrArg (fun c => (fun r : α × List Entry => (r.1, (obs (.inr u) answer).toList ++ r.2)) <$> c)
          (ih answer)
        simp only [Functor.map_map] at h
        simpa [obs, traceOf, bind_pure_comp] using h
section Potential
variable {ι : Type} (cellInput : ι → HashInput) (F : Set ι) [Fintype F] [DecidableEq F]
def Consistent (init : F → Finset HashOutput) (h : FreeMonoid Entry) (allowed : F → Finset HashOutput) : Prop :=
  (∀ e : F, ∀ ans, (cellInput e.val, ans) ∈ h.toList → allowed e = {ans}) ∧
    ∀ e : F, (∀ ans, (cellInput e.val, ans) ∉ h.toList) → allowed e = init e
theorem consistent_one (init : F → Finset HashOutput) : Consistent cellInput F init 1 init := by
  constructor
  · intro e ans h
    simp at h
  · intro e _
    rfl
theorem Consistent.nonempty {init : F → Finset HashOutput} {h : FreeMonoid Entry} {allowed : F → Finset HashOutput}
    (hc : Consistent cellInput F init h allowed) (hinit : ∀ e, (init e).Nonempty) : ∀ e, (allowed e).Nonempty := by
  intro e
  by_cases hq : ∃ ans, (cellInput e.val, ans) ∈ h.toList
  · obtain ⟨ans, hans⟩ := hq
    rw [hc.1 e ans hans]
    exact Finset.singleton_nonempty ans
  · rw [hc.2 e (fun ans hans => hq ⟨ans, hans⟩)]
    exact hinit e
noncomputable def marks {A : Type} [Fintype A] (M : A → Entry → Prop) (l : List Entry) : Nat :=
  (Finset.univ.filter fun a => ∃ entry ∈ l, M a entry).card
noncomputable def cellCount (l : List Entry) : Nat :=
  (l.filter fun entry => decide (IsCell cellInput F entry.1)).length
noncomputable def charge : RefWorld.Domain → Nat
  | .inl (.inr input) => if IsCell cellInput F input then 1 else 0
  | _ => 0
theorem marks_append_le {A : Type} [Fintype A] [DecidableEq A] (M : A → Entry → Prop) (l : List Entry)
    (x : Entry) : marks M (l ++ [x]) ≤ marks M l + (Finset.univ.filter fun a => M a x).card := by
  unfold marks
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_append, List.mem_singleton] at ha
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨entry, hmem, hm⟩ := ha
  rcases hmem with hmem | rfl
  · exact Or.inl ⟨entry, hmem, hm⟩
  · exact Or.inr hm
theorem marks_append_of_mem {A : Type} [Fintype A] (M : A → Entry → Prop) (l : List Entry) (x : Entry)
    (hx : x ∈ l) : marks M (l ++ [x]) = marks M l := by
  unfold marks
  congr 1
  apply Finset.filter_congr
  intro a _
  constructor
  · rintro ⟨entry, hmem, hm⟩
    rw [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact ⟨entry, hmem, hm⟩
    · exact ⟨_, hx, hm⟩
  · rintro ⟨entry, hmem, hm⟩
    exact ⟨entry, List.mem_append_left _ hmem, hm⟩
theorem marks_append_of_none {A : Type} [Fintype A] (M : A → Entry → Prop) (l : List Entry) (x : Entry)
    (hx : ∀ a, ¬ M a x) : marks M (l ++ [x]) = marks M l := by
  unfold marks
  congr 1
  apply Finset.filter_congr
  intro a _
  constructor
  · rintro ⟨entry, hmem, hm⟩
    rw [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact ⟨entry, hmem, hm⟩
    · exact absurd hm (hx a)
  · rintro ⟨entry, hmem, hm⟩
    exact ⟨entry, List.mem_append_left _ hmem, hm⟩
theorem cellCount_step (input : RefWorld.Domain) (answer : RefWorld.Range input) (tail : FreeMonoid Entry) :
    cellCount cellInput F (obs input answer * tail).toList =
      charge cellInput F input + cellCount cellInput F tail.toList := by
  rcases input with (n | x) | u
  · simp [obs, charge, cellCount]
  · by_cases hx : IsCell cellInput F x
    · simp [obs, charge, cellCount, hx, Nat.add_comm]
    · simp [obs, charge, cellCount, hx]
  · simp [obs, charge, cellCount]
theorem lazyImpl_coin (T : Answers) (n : Nat) (allowed : F → Finset HashOutput) :
    (lazyImpl cellInput F T (.inl (.inl n))).run allowed =
      (fun answer => (answer, allowed)) <$> aux T (.inl (.inl n)) := by
  simp only [lazyImpl, QueryImpl.compose, translate, simulateQ_spec_query, UniformTableObservation.lazyImpl,
    StateT.run_mk]
  rfl
theorem lazyImpl_tick (T : Answers) (u : Unit) (allowed : F → Finset HashOutput) :
    (lazyImpl cellInput F T (.inr u)).run allowed =
      (fun answer => (answer, allowed)) <$> aux T (.inr u) := by
  simp only [lazyImpl, QueryImpl.compose, translate, simulateQ_spec_query, UniformTableObservation.lazyImpl,
    StateT.run_mk]
  rfl
theorem lazyImpl_cell (T : Answers) (x : HashInput) (hx : IsCell cellInput F x) (allowed : F → Finset HashOutput) :
    (lazyImpl cellInput F T (.inl (.inr x))).run allowed =
      (fun answer => (answer, discloseTableValue allowed (cellOf cellInput F x hx) answer)) <$>
        cell (allowed (cellOf cellInput F x hx)) := by
  simp only [lazyImpl, QueryImpl.compose, translate, dif_pos hx, simulateQ_spec_query,
    UniformTableObservation.lazyImpl, StateT.run_mk]
  rfl
theorem lazyImpl_other (T : Answers) (x : HashInput) (hx : ¬ IsCell cellInput F x) (allowed : F → Finset HashOutput) :
    (lazyImpl cellInput F T (.inl (.inr x))).run allowed = pure (T (.inl (.inr x)), allowed) := by
  simp only [lazyImpl, QueryImpl.compose, translate, dif_neg hx, simulateQ_spec_query,
    UniformTableObservation.lazyImpl, StateT.run_mk, aux, refImpl, evalSPMF_pure, map_pure]
theorem map_nonzero {α β : Type} (μ : SPMF α) (f : α → β) (result : β) (h : (f <$> μ) result ≠ 0) :
    ∃ a, μ a ≠ 0 ∧ result = f a := by
  rw [← bind_pure_comp] at h
  obtain ⟨a, ha, heq⟩ := (SphincsSecurity.Concrete.RetainedObservation.bind_nonzero _ _ _).mp h
  refine ⟨a, ha, ?_⟩
  simpa only [Function.comp_apply, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using heq
theorem cell_nonzero_mem {allowed : Finset HashOutput} {answer : HashOutput} (h : cell allowed answer ≠ 0) :
    answer ∈ allowed := by
  rw [cell_apply] at h
  by_contra hn
  exact h (if_neg hn)
theorem consistent_step (hinj : Function.Injective cellInput) (T : Answers) (init : F → Finset HashOutput)
    (h : FreeMonoid Entry)
    (allowed : F → Finset HashOutput) (hc : Consistent cellInput F init h allowed) (input : RefWorld.Domain)
    (result : RefWorld.Range input × (F → Finset HashOutput))
    (hr : (lazyImpl cellInput F T input).run allowed result ≠ 0) :
    Consistent cellInput F init (h * obs input result.1) result.2 := by
  rcases input with (n | x) | u
  · rw [lazyImpl_coin] at hr
    obtain ⟨answer, _, rfl⟩ := map_nonzero _ _ _ hr
    simpa only [obs, mul_one] using hc
  · by_cases hx : IsCell cellInput F x
    · rw [lazyImpl_cell cellInput F T x hx] at hr
      obtain ⟨answer, ha, rfl⟩ := map_nonzero _ _ _ hr
      have hmem := cell_nonzero_mem ha
      set e₀ := cellOf cellInput F x hx with he₀
      have hx₀ : cellInput e₀.val = x := cellOf_input cellInput F x hx
      have hne : ∀ e : F, e ≠ e₀ → cellInput e.val ≠ x := by
        intro e he heq
        exact he (Subtype.ext (hinj (heq.trans hx₀.symm)))
      constructor
      · intro e ans hans
        simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton,
          Prod.mk.injEq] at hans
        by_cases he : e = e₀
        · subst he
          simp only [discloseTableValue, Function.update_self]
          rcases hans with hans | ⟨-, rfl⟩
          · have h1 := hc.1 _ ans hans
            rw [h1, Finset.mem_singleton] at hmem
            rw [hmem]
          · rfl
        · simp only [discloseTableValue, Function.update_of_ne he]
          rcases hans with hans | ⟨heq, -⟩
          · exact hc.1 e ans hans
          · exact absurd heq (hne e he)
      · intro e hfresh
        have he : e ≠ e₀ := by
          intro he
          apply hfresh answer
          simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton]
          right
          rw [he, hx₀]
        simp only [discloseTableValue, Function.update_of_ne he]
        apply hc.2 e
        intro ans hans
        apply hfresh ans
        simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append]
        exact Or.inl hans
    · rw [lazyImpl_other cellInput F T x hx] at hr
      have hres : result = (T (.inl (.inr x)), allowed) := by
        by_contra hn
        exact hr (by rw [SPMF.pure_apply_eq_zero_iff]; exact hn)
      subst hres
      have hnot : ∀ e : F, cellInput e.val ≠ x := fun e heq => hx ⟨e.val, e.property, heq⟩
      constructor
      · intro e ans hans
        simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton,
          Prod.mk.injEq] at hans
        rcases hans with hans | ⟨heq, -⟩
        · exact hc.1 e ans hans
        · exact absurd heq (hnot e)
      · intro e hfresh
        apply hc.2 e
        intro ans hans
        apply hfresh ans
        simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append]
        exact Or.inl hans
  · rw [lazyImpl_tick] at hr
    obtain ⟨answer, _, rfl⟩ := map_nonzero _ _ _ hr
    simpa only [obs, mul_one] using hc
theorem probEvent_cell_univ (p : HashOutput → Prop) :
    Pr[p | cell (Finset.univ : Finset HashOutput)] = Pr[p | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  refine tsum_congr fun ans => ?_
  split_ifs
  · rw [SPMF.probOutput_eq_apply, cell_apply, if_pos (Finset.mem_univ _), probOutput_uniformSample, Finset.card_univ]
  · rfl
theorem tsum_probOutput_mul_le_self {α : Type} (μ : SPMF α) (c : ENNReal) :
    ∑' a, Pr[= a | μ] * c ≤ c := by
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one
theorem tsum_filter_card {A : Type} [Fintype A] (μ : SPMF HashOutput) (M : A → HashOutput → Prop) :
    ∑' ans, Pr[= ans | μ] * ((Finset.univ.filter fun a => M a ans).card : ENNReal) = ∑ a, Pr[M a | μ] := by
  classical
  have h : ∀ ans, ((Finset.univ.filter fun a => M a ans).card : ENNReal) = ∑ a, if M a ans then 1 else 0 := by
    intro ans
    rw [Finset.card_filter]
    push_cast
    rfl
  simp only [h, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [probEvent_eq_tsum_ite]
  refine tsum_congr fun ans => ?_
  split_ifs <;> simp
theorem lazy_step {A : Type} [Fintype A] [DecidableEq A] (hinj : Function.Injective cellInput) (T : Answers)
    (M : A → Entry → Prop) (rate : ENNReal) (init : F → Finset HashOutput)
    (hcell : ∀ e : F, ∑ a, Pr[fun ans => M a (cellInput e.val, ans) | cell (init e)] ≤ rate)
    (hother : ∀ x, ¬ IsCell cellInput F x → ∀ a, ¬ M a (x, T (.inl (.inr x))))
    (h : FreeMonoid Entry) (allowed : F → Finset HashOutput) (hc : Consistent cellInput F init h allowed)
    (input : RefWorld.Domain) :
    ∑' result, Pr[= result | (lazyImpl cellInput F T input).run allowed] *
        (marks M (h * obs input result.1).toList : ENNReal) ≤
      (marks M h.toList : ENNReal) + rate * (charge cellInput F input : ENNReal) := by
  rcases input with (n | x) | u
  · rw [lazyImpl_coin, tsum_probOutput_map_mul]
    simp only [obs, mul_one]
    exact (tsum_probOutput_mul_le_self _ _).trans le_self_add
  · by_cases hx : IsCell cellInput F x
    · rw [lazyImpl_cell cellInput F T x hx, tsum_probOutput_map_mul]
      simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, charge, if_pos hx, Nat.cast_one, mul_one]
      set e₀ := cellOf cellInput F x hx with he₀
      have hx₀ : cellInput e₀.val = x := cellOf_input cellInput F x hx
      by_cases hq : ∃ ans₀, (cellInput e₀.val, ans₀) ∈ h.toList
      · obtain ⟨ans₀, hans₀⟩ := hq
        rw [hc.1 e₀ ans₀ hans₀]
        have hsupp : ∀ ans, ans ≠ ans₀ → Pr[= ans | cell ({ans₀} : Finset HashOutput)] = 0 := by
          intro ans hne
          rw [SPMF.probOutput_eq_apply, cell_apply, if_neg (by simpa using hne)]
        calc _ = ∑' ans, Pr[= ans | cell ({ans₀} : Finset HashOutput)] * (marks M h.toList : ENNReal) := by
              refine tsum_congr fun ans => ?_
              by_cases hne : ans = ans₀
              · rw [hne, ← hx₀, marks_append_of_mem M _ _ hans₀]
              · rw [hsupp ans hne, zero_mul, zero_mul]
          _ ≤ _ := (tsum_probOutput_mul_le_self _ _).trans le_self_add
      · rw [hc.2 e₀ (fun ans hans => hq ⟨ans, hans⟩)]
        calc _ ≤ ∑' ans, Pr[= ans | cell (init e₀)] *
              ((marks M h.toList : ENNReal) + ((Finset.univ.filter fun a => M a (x, ans)).card : ENNReal)) := by
              refine ENNReal.tsum_le_tsum fun ans => mul_le_mul' le_rfl ?_
              exact_mod_cast marks_append_le M _ _
          _ = ∑' ans, Pr[= ans | cell (init e₀)] * (marks M h.toList : ENNReal) +
              ∑' ans, Pr[= ans | cell (init e₀)] *
                ((Finset.univ.filter fun a => M a (x, ans)).card : ENNReal) := by
              rw [← ENNReal.tsum_add]
              exact tsum_congr fun ans => mul_add _ _ _
          _ ≤ _ := by
              refine add_le_add (tsum_probOutput_mul_le_self _ _) ?_
              rw [tsum_filter_card (cell (init e₀)) (fun a ans => M a (x, ans))]
              rw [← hx₀]
              exact hcell e₀
    · rw [lazyImpl_other cellInput F T x hx, tsum_probOutput_pure_mul]
      simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, charge, if_neg hx]
      rw [marks_append_of_none M _ _ (hother x hx)]
      exact le_self_add
  · rw [lazyImpl_tick, tsum_probOutput_map_mul]
    simp only [obs, mul_one]
    exact (tsum_probOutput_mul_le_self _ _).trans le_self_add
theorem aux_neverFail (T : Answers) (input : RefWorld.Domain) : NeverFail (aux T input) :=
  ⟨probFailure_eq_zero (mx := refImpl T input)⟩
theorem lazy_marks_init_le {α A : Type} [Fintype A] [DecidableEq A] (hinj : Function.Injective cellInput)
    (T : Answers) (M : A → Entry → Prop) (rate : ENNReal) (init : F → Finset HashOutput)
    (hinit : ∀ e, (init e).Nonempty)
    (hcell : ∀ e : F, ∑ a, Pr[fun ans => M a (cellInput e.val, ans) | cell (init e)] ≤ rate)
    (hother : ∀ x, ¬ IsCell cellInput F x → ∀ a, ¬ M a (x, T (.inl (.inr x))))
    (C : OracleComp RefWorld α) :
    ∑' r, Pr[= r | (simulateQ (lazyImpl cellInput F T) (SphincsSecurity.QueryPause.traced obs C)).run init] *
        (marks M r.1.2.toList : ENNReal) ≤
      rate * ∑' r, Pr[= r | (simulateQ (lazyImpl cellInput F T) (SphincsSecurity.QueryPause.traced obs C)).run
        init] * (cellCount cellInput F r.1.2.toList : ENNReal) := by
  have key := SphincsSecurity.QueryPause.traced_spmf_potential_le obs (lazyImpl cellInput F T)
    (fun h st => Consistent cellInput F init h st)
    (fun h st hc input result hr => consistent_step cellInput F hinj T init h st hc input result hr)
    (fun C' h st hc => by
      rw [← lazyRun_eq_simulate]
      exact probFailure_eq_zero' (UniformTableObservation.lazyRun_neverFail (aux T) (aux_neverFail T) _ st
        (hc.nonempty cellInput F hinit)))
    (fun h _ => (marks M h.toList : ENNReal)) rate (fun h => cellCount cellInput F h.toList) (charge cellInput F)
    (by simp [cellCount]) (fun input answer tail => cellCount_step cellInput F input answer tail)
    (fun h st hc input => lazy_step cellInput F hinj T M rate init hcell hother h st hc input)
    C 1 init (consistent_one cellInput F init)
  simp only [one_mul] at key
  have h0 : marks M (1 : FreeMonoid Entry).toList = 0 := by
    simp [marks]
  rw [h0, Nat.cast_zero, zero_add] at key
  exact key
theorem lazy_marks_le {α A : Type} [Fintype A] [DecidableEq A] (hinj : Function.Injective cellInput)
    (T : Answers) (M : A → Entry → Prop) (rate : ENNReal)
    (hcell : ∀ e : F, ∑ a, Pr[fun ans => M a (cellInput e.val, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate)
    (hother : ∀ x, ¬ IsCell cellInput F x → ∀ a, ¬ M a (x, T (.inl (.inr x))))
    (C : OracleComp RefWorld α) :
    ∑' r, Pr[= r | (simulateQ (lazyImpl cellInput F T) (SphincsSecurity.QueryPause.traced obs C)).run
        (fun _ => Finset.univ)] * (marks M r.1.2.toList : ENNReal) ≤
      rate * ∑' r, Pr[= r | (simulateQ (lazyImpl cellInput F T) (SphincsSecurity.QueryPause.traced obs C)).run
        (fun _ => Finset.univ)] * (cellCount cellInput F r.1.2.toList : ENNReal) :=
  lazy_marks_init_le cellInput F hinj T M rate (fun _ => Finset.univ) (fun _ => Finset.univ_nonempty)
    (fun e => by simp only [probEvent_cell_univ]; exact hcell e) hother C
end Potential
end Enc.Lazy
end SigGolfCandidate.T3.Security.Wots
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
section Table
variable (adversary : AdversaryP) (q : Nat)
theorem probOutput_complete_univ' {ι : Type} [Fintype ι] [DecidableEq ι] (y : ι → HashOutput) :
    Pr[= y | complete (fun _ : ι => (Finset.univ : Finset HashOutput))] = PMF.uniformOfFintype (ι → HashOutput) y := by
  rw [complete_of_nonempty _ (fun _ => Finset.univ_nonempty), SPMF.probOutput_eq_apply, SPMF.liftM_apply,
    SphincsSecurity.Concrete.uniformTable_univ]
theorem uniformOfFintype_inst {α : Type} [Nonempty α] (i1 i2 : Fintype α) (y : α) :
    @PMF.uniformOfFintype α i1 _ y = @PMF.uniformOfFintype α i2 _ y := by
  rw [Subsingleton.elim i1 i2]
theorem probOutput_complete_univ {ι : Type} [Fintype ι] [DecidableEq ι] (iX : Fintype (ι → HashOutput))
    (y : ι → HashOutput) :
    Pr[= y | complete (fun _ : ι => (Finset.univ : Finset HashOutput))] =
      @PMF.uniformOfFintype (ι → HashOutput) iX _ y :=
  (probOutput_complete_univ' y).trans (uniformOfFintype_inst _ iX y)
theorem probOutput_complete_init {ι : Type} [Fintype ι] [DecidableEq ι] (init : ι → Finset HashOutput)
    (hinit : ∀ e, (init e).Nonempty) (y : ι → HashOutput) :
    Pr[= y | complete init] =
      PMF.uniformOfFinset (Fintype.piFinset init) (Fintype.piFinset_nonempty.mpr hinit) y := by
  rw [complete_of_nonempty _ hinit, SPMF.probOutput_eq_apply, SPMF.liftM_apply]
  rfl
theorem marks_unit (P : Entry → Prop) (tr : List Entry) :
    (Lazy.marks (fun (_ : Unit) => P) tr : ENNReal) = if ∃ entry ∈ tr, P entry then 1 else 0 := by
  unfold Lazy.marks
  by_cases h : ∃ entry ∈ tr, P entry
  · rw [if_pos h, Finset.filter_true_of_mem (fun _ _ => h)]
    simp
  · rw [if_neg h, Finset.filter_false_of_mem (fun _ _ => h)]
    simp
end Table
end Enc
end SigGolfCandidate.T3.Security.Wots
end
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsMaskRest ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
variable (a : ChainAddr)
theorem slotAddr_lay : (slotAddr a).key.lay = a.key.lay := by
  unfold slotAddr; split_ifs <;> rfl
theorem untouchedP_chainInputW_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i s : Nat) (v : Digest) :
    UntouchedP a (.inl (.inr (pad64 (WCT9.chainInputW lay tree leaf i s v)))) := by
  intro step value _ heq
  rw [pad64_chainInputW] at heq
  exact hl (chainHeader_fields (chainInputW_fields heq).1).1
theorem respectsP_chain_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i start count : Nat) (v : Digest) :
    Respects (UntouchedP a) (WCT9.chainW lay tree leaf i start count v) :=
  respects_chainW' _ _ _ _ _ _ _ fun step value _ _ => untouchedP_chainInputW_of_lay a hl _ _ _ _ _
variable {T T' : Answers} (hT : ∀ q, UntouchedP a q → T q = T' q)
include hT
theorem wotsSeed_congr_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i : Nat) :
    WCT9.wotsSeed T lay tree leaf i = WCT9.wotsSeed T' lay tree leaf i := by
  apply wotsSeed_congr_cells
  intro p
  apply hT (.inr (.inl _))
  intro h
  apply hl
  unfold seedTweakP seedTweak WCT9.lowerSeedHeader at h
  split_ifs at h <;> exact lay_eq_of_header a h
theorem wotsEnd_congr_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i : Nat) :
    WCT9.wotsEnd T lay tree leaf i = WCT9.wotsEnd T' lay tree leaf i := by
  unfold WCT9.wotsEnd
  rw [wotsSeed_congr_of_lay a hT hl]
  exact (respectsP_chain_of_lay a hl _ _ _ _ _ _).eval_eq hT
theorem wotsRoot_congr_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf : Nat) :
    WCT9.wotsRoot T lay tree leaf = WCT9.wotsRoot T' lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i _ => wotsEnd_congr_of_lay a hT hl tree leaf i)]
  exact (respectsP_lowerLeafHash a _ _ _ _ (by
    simp only [List.length_map, List.length_range]; exact SigGolfCandidate.T3.Security.Wots.Enc.chainCount_ge4 _)).eval_eq hT
theorem wotsTree_congr_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree : Nat) :
    WCT9.wotsTree T lay tree = WCT9.wotsTree T' lay tree := by
  unfold WCT9.wotsTree
  have hr : WCT9.wotsRoot T lay tree = WCT9.wotsRoot T' lay tree :=
    funext (wotsRoot_congr_of_lay a hT hl tree)
  rw [hr]
  split_ifs
  · exact (respectsP_buildTopLevels a _).eval_eq hT
  · exact (respectsP_lowerLevels a _ _ _ (by fin_cases lay <;> decide) _
      (by simp only [List.length_map, List.length_range]; exact le_rfl)).eval_eq hT
theorem honestTop_congr (index : Nat) : Extract.honestTop T index = Extract.honestTop T' index := by
  rw [Extract.honestTop_eq_wct9, Extract.honestTop_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestTop_congr (fun _ hq => hT _ (ftsQuery_untouchedP a hq))
theorem leafMsg_congr : leafMsg T a.key = leafMsg T' a.key := by
  unfold leafMsg
  split
  · rename_i h
    unfold Extract.honestPair
    rw [wotsTree_congr_of_lay a hT (fun he => by
      have := congrArg Fin.val he
      simp only at this
      omega)]
  · rw [honestTop_congr a hT _]
theorem referenceSearch_congr : referenceSearch T a.key = referenceSearch T' a.key := by
  unfold referenceSearch
  rw [leafMsg_congr a hT]
  exact (respectsP_layerCounterSearch a _ _ _ _ _ _).eval_eq hT
end Mask
theorem depth_congr (a : ChainAddr) (T T' : Answers) (hT : ∀ q, UntouchedP a q → T q = T' q) :
    depth T a = depth T' a := by
  unfold depth referenceDigits
  rw [Mask.referenceSearch_congr a hT]
end ClaudeWCT.W9.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsPrefixGameBase ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_wotsPrefixGameBase : Fintype Coordinate := coordinateFintype
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
end PrefixGame
abbrev RefTables (adversary : AdversaryP) := FullGame.FullTable × (referenceInputs adversary → HashOutput)
noncomputable instance instFintypeRefTables (adversary : AdversaryP) : Fintype (RefTables adversary) := by
  unfold RefTables FullGame.FullTable
  infer_instance
instance instNonemptyRefTables (adversary : AdversaryP) : Nonempty (RefTables adversary) := ⟨(fun _ => 0, fun _ => 0)⟩
noncomputable def restLaw (adversary : AdversaryP) : PMF (RefTables adversary) := PMF.uniformOfFintype _
noncomputable def restTable {adversary : AdversaryP} (R : RefTables adversary) : Answers :=
  eagerAnswers (referenceInputs adversary) R.1 R.2
@[irreducible] noncomputable def restDepth {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary) : Nat :=
  depth (restTable R) a
theorem restDepth_eq {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary) :
    restDepth a R = depth (restTable R) a := by
  unfold restDepth; rfl
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
theorem chainRowW_mem (a : ChainAddr) (step : Nat) (value : Digest) :
    chainRowW a step value ∈ referenceInputs adversary := by
  unfold referenceInputs
  apply Finset.mem_union_left
  apply SeccLaw.mem_publicUniverse
  rw [chainRowW_eq]
  have h : (WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain step value).length = 64 := by
    simp [WCT9.chainInputW_length]
  rw [h]
  unfold SeccLaw.maxInputLength
  omega
theorem restTable_mem (R : RefTables adversary) (input : HashInput) (h : input ∈ referenceInputs adversary) :
    restTable R (.inl (.inr input)) = R.2 ⟨input, h⟩ := by
  show SphincsSecurity.Concrete.finiteHashAnswer ∅ (referenceInputs adversary) R.2 input = R.2 ⟨input, h⟩
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  rw [dif_pos h]
  rfl
theorem restTable_nonmem (R : RefTables adversary) (input : HashInput) (h : input ∉ referenceInputs adversary) :
    restTable R (.inl (.inr input)) = (0 : HashOutput) := by
  show SphincsSecurity.Concrete.finiteHashAnswer ∅ (referenceInputs adversary) R.2 input = (0 : HashOutput)
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  rw [dif_neg h]
  rfl
theorem restTable_private (R : RefTables adversary) (coordinate : Coordinate) :
    restTable R (.inr coordinate) = R.1 coordinate := rfl
/-- Pairing stage 1: the prefix row of chain `a` (current-scheme row `chainRowW`) that `input` is, if any. -/
noncomputable def rowOf (a : ChainAddr) (d : Nat) (input : HashInput) : Option (Fin d × Digest) :=
  if h : ∃ p : Fin d × Digest, input = chainRowW a p.1 p.2 then some (Classical.choose h) else none
theorem rowOf_some {a : ChainAddr} {d : Nat} {input : HashInput} {p : Fin d × Digest}
    (h : PrefixGame.rowOf a d input = some p) : input = chainRowW a p.1 p.2 := by
  unfold PrefixGame.rowOf at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h
theorem rowOf_none {a : ChainAddr} {d : Nat} {input : HashInput} (h : rowOf a d input = none) (p : Fin d × Digest) :
    input ≠ chainRowW a p.1 p.2 := by
  intro he
  unfold PrefixGame.rowOf at h
  rw [dif_pos ⟨p, he⟩] at h
  cases h
theorem rowOf_chainRow (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (i : Fin d) (v : Digest) :
    PrefixGame.rowOf a d (chainRowW a i v) = some (i, v) := by
  cases h : PrefixGame.rowOf a d (chainRowW a i v) with
  | none => exact absurd rfl (PrefixGame.rowOf_none h (i, v))
  | some p =>
      have he := PrefixGame.rowOf_some h
      obtain ⟨hs, hv⟩ := chainRowW_inj (by omega) (by have := p.1.isLt; omega) he
      rw [show p = (i, v) from Prod.ext (Fin.ext hs.symm) hv.symm]
theorem rowOf_none_iff (a : ChainAddr) {d : Nat} (input : HashInput) :
    PrefixGame.rowOf a d input = none ↔ ¬∃ step value, step < d ∧ input = chainRowW a step value := by
  constructor
  · rintro h ⟨step, value, hs, rfl⟩
    exact PrefixGame.rowOf_none h (⟨step, hs⟩, value) rfl
  · intro h
    cases hp : PrefixGame.rowOf a d input with
    | none => rfl
    | some p => exact absurd ⟨p.1.val, p.2, p.1.isLt, PrefixGame.rowOf_some hp⟩ h
noncomputable def ovPub (a : ChainAddr) (d : Nat) (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) : referenceInputs adversary → HashOutput := fun x =>
  match PrefixGame.rowOf a d x.val with
  | some p => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) (tables p.1 p.2)
      (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (pub x))
  | none => pub x
/-- The seed of chain `a` in `ov a d R x`: its leaf-family evaluation (every layer: campaign X1 stage B, top leaves
since campaign T8D), unchanged by `ov`; the seed component of `Hidden` is a dummy. -/
noncomputable def ovSeed (a : ChainAddr) (R : RefTables adversary) (_seed : Digest) : Digest :=
  WCT9.wotsSeed (restTable R) a.key.lay a.key.tree a.key.leaf a.chain
/-- Override of chain `a`'s prefix rows (the private table is unchanged). -/
noncomputable def ov (a : ChainAddr) (d : Nat) (R : RefTables adversary) (x : Hidden d) : RefTables adversary :=
  (R.1, ovPub a d R.2 x.1)
noncomputable def rd (a : ChainAddr) (d : Nat) (R : RefTables adversary) : Hidden d :=
  (fun i v => WCT9.halfOf (WCT9.chainHigh a.key.lay a.chain i.val) (R.2 ⟨chainRowW a i v, chainRowW_mem a i v⟩), 0)
theorem ovPub_row (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) (i : Fin d) (v : Digest) :
    ovPub a d pub tables ⟨chainRowW a i v, chainRowW_mem a i v⟩ =
      joinHalf (WCT9.chainHigh a.key.lay a.chain i.val) (tables i v)
        (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain i.val) (pub ⟨chainRowW a i v, chainRowW_mem a i v⟩)) := by
  unfold ovPub
  rw [PrefixGame.rowOf_chainRow a hd i v]
theorem ovPub_none (a : ChainAddr) {d : Nat} (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) (x : referenceInputs adversary) (h : PrefixGame.rowOf a d x.val = none) :
    ovPub a d pub tables x = pub x := by
  unfold ovPub
  rw [h]
theorem rd_ov_rows (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    (rd a d (ov a d R x)).1 = x.1 := by
  obtain ⟨tables, seed⟩ := x
  unfold rd ov
  funext i v
  simp only
  rw [ovPub_row a hd, halfOf_joinHalf]
/-- `ov` ignores the seed component. -/
theorem ov_seed_irrel (a : ChainAddr) {d : Nat} (R : RefTables adversary)
    (t : Fin d → Digest → Digest) (s s' : Digest) : ov a d R (t, s) = ov a d R (t, s') := rfl
theorem ov_ov_rd (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    ov a d (ov a d R x) (rd a d R) = R := by
  obtain ⟨priv, pub⟩ := R
  obtain ⟨tables, seed⟩ := x
  unfold ov rd
  simp only
  refine Prod.ext rfl ?_
  · funext y
    unfold ovPub
    cases hp : PrefixGame.rowOf a d y.val with
    | none => simp only [hp]
    | some p =>
        simp only [hp]
        have hy : y = ⟨chainRowW a p.1 p.2, chainRowW_mem a p.1 p.2⟩ := Subtype.ext (PrefixGame.rowOf_some hp)
        subst hy
        rw [halfOf_not_joinHalf, joinHalf_halfOf]
theorem restTable_ov_untouched (a : ChainAddr) {d : Nat} (hd : d ≤ 7) (R : RefTables adversary) (x : Hidden d)
    (query : T3.Spec.Domain) (hq : UntouchedP a query) : restTable (ov a d R x) query = restTable R query := by
  rcases query with (n | input) | (tweak | other)
  · rfl
  · by_cases h : input ∈ referenceInputs adversary
    · rw [restTable_mem _ _ h, restTable_mem _ _ h]
      unfold ov
      simp only
      rw [ovPub_none]
      cases hp : PrefixGame.rowOf a d input with
      | none => rfl
      | some p => exact absurd (PrefixGame.rowOf_some hp) (hq p.1 p.2 (by have := p.1.isLt; omega))
    · rw [restTable_nonmem _ _ h, restTable_nonmem _ _ h]
  · rfl
  · rfl
theorem restTable_ov_prefix (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d)
    (i : Fin d) (v : Digest) :
    restTable (ov a d R x) (.inl (.inr (chainRowW a i v))) =
      joinHalf (WCT9.chainHigh a.key.lay a.chain i.val) (x.1 i v)
        (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain i.val) (restTable R (.inl (.inr (chainRowW a i v))))) := by
  rw [restTable_mem _ _ (chainRowW_mem a i v), restTable_mem _ _ (chainRowW_mem a i v)]
  exact ovPub_row a hd R.2 x.1 i v
theorem restTable_ov_nonprefix (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d)
    (input : HashInput) (h : PrefixGame.rowOf a d input = none) :
    restTable (ov a d R x) (.inl (.inr input)) = restTable R (.inl (.inr input)) := by
  by_cases hm : input ∈ referenceInputs adversary
  · rw [restTable_mem _ _ hm, restTable_mem _ _ hm]
    exact ovPub_none a R.2 x.1 _ h
  · rw [restTable_nonmem _ _ hm, restTable_nonmem _ _ hm]
/-- `ov` leaves the private table alone. -/
theorem restTable_ov_private (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d)
    (coordinate : Coordinate) : restTable (ov a d R x) (.inr coordinate) = restTable R (.inr coordinate) := rfl
theorem depth_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 7) (R : RefTables adversary) (x : Hidden d) (b : ChainAddr)
    (hb : b = a) : depth (restTable (ov a d R x)) b = depth (restTable R) b := by
  subst hb
  exact depth_congr b _ _ (restTable_ov_untouched b hd R x)
theorem restDepth_le (a : ChainAddr) (R : RefTables adversary) : restDepth a R ≤ 7 := by
  rw [restDepth_eq]; exact Mask.depth_le_seven _ a
theorem restDepth_ov (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    restDepth a (ov a (restDepth a R) R x) = restDepth a R := by
  have hd : restDepth a R ≤ 7 := restDepth_le a R
  calc restDepth a (ov a (restDepth a R) R x) = depth (restTable (ov a (restDepth a R) R x)) a := restDepth_eq _ _
    _ = depth (restTable R) a := depth_ov a hd R x a rfl
    _ = restDepth a R := (restDepth_eq a R).symm
theorem wotsSeed_ov (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d) :
    WCT9.wotsSeed (restTable (ov a d R x)) a.key.lay a.key.tree a.key.leaf a.chain = ovSeed a R x.2 :=
  Mask.wotsSeed_congr_private (fun c => restTable_ov_private a R x c) _ _ _ _
theorem eval_chain_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    ∀ (n s : Nat) (hn : s + n ≤ d) (v : Digest),
      evalWithAnswerFn (restTable (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s n v) =
        SphincsSecurity.Concrete.PartialChainEndpoint.evaluate
          (fun (i : Fin n) => x.1 ⟨s + i.val, by omega⟩) v := by
  intro n
  induction n with
  | zero =>
      intro s hn v
      simp [WCT9.chainW, SphincsSecurity.Concrete.PartialChainEndpoint.evaluate]
  | succ n ih =>
      intro s hn v
      have hsplit : evalWithAnswerFn (restTable (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s (n + 1) v) =
          evalWithAnswerFn (restTable (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain (s + 1) n
            (evalWithAnswerFn (restTable (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s 1 v))) := by
        rw [show n + 1 = 1 + n by omega]
        exact eval_chainW_add' _ _ _ _ _ _ _ _ _
      rw [hsplit, eval_chainW_one', pad64_chainInputW]
      have hrow : WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain s v = chainRowW a (⟨s, by omega⟩ : Fin d) v := rfl
      rw [hrow, restTable_ov_prefix a hd R x]
      rw [show (⟨s, by omega⟩ : Fin d).val = s from rfl, halfOf_joinHalf, ih (s + 1) (by omega)]
      simp only [SphincsSecurity.Concrete.PartialChainEndpoint.evaluate]
      congr 1
      · funext i w
        unfold Fin.tail
        exact congrArg (fun j : Fin d => x.1 j w) (Fin.ext (by simp only [Fin.val_succ]; omega))
theorem frontierValue_ov (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    frontierValue (restTable (ov a (restDepth a R) R x)) a =
      SphincsSecurity.Concrete.PartialChainEndpoint.evaluate x.1 (ovSeed a R x.2) := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  have hdepth : depth (restTable (ov a (restDepth a R) R x)) a = restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R x)).symm.trans (restDepth_ov a R x)
  unfold frontierValue honestChainValueW
  rw [hdepth, wotsSeed_ov]
  rw [eval_chain_ov a hd R x (restDepth a R) 0 (by omega)]
  congr 1
  funext i
  exact congrArg x.1 (Fin.ext (by simp only [Nat.zero_add]))
end PrefixGame
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
namespace RawPrefix
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
include hU in
theorem chainRowW_mem (a : ChainAddr) (step : Nat) (value : Digest) :
    chainRowW a step value ∈ U := by
  apply hU
  apply SeccLaw.mem_publicUniverse
  rw [chainRowW_eq]
  have h : (WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain step value).length = 64 := by
    simp [WCT9.chainInputW_length]
  rw [h]
  unfold SeccLaw.maxInputLength
  omega
theorem raw_mem (R : Tables U) (input : HashInput) (h : input ∈ U) :
    raw R (.inl (.inr input)) = R.2 ⟨input, h⟩ := by
  show SphincsSecurity.Concrete.finiteHashAnswer ∅ U R.2 input = R.2 ⟨input, h⟩
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  rw [dif_pos h]
  rfl
theorem raw_nonmem (R : Tables U) (input : HashInput) (h : input ∉ U) :
    raw R (.inl (.inr input)) = (0 : HashOutput) := by
  show SphincsSecurity.Concrete.finiteHashAnswer ∅ U R.2 input = (0 : HashOutput)
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  rw [dif_neg h]
  rfl
theorem raw_private (R : Tables U) (coordinate : Coordinate) :
    raw R (.inr coordinate) = R.1 coordinate := rfl
noncomputable def ovPub (a : ChainAddr) (d : Nat) (pub : U → HashOutput)
    (tables : Fin d → Digest → Digest) : U → HashOutput := fun x =>
  match PrefixGame.rowOf a d x.val with
  | some p => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) (tables p.1 p.2)
      (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (pub x))
  | none => pub x
/-- The seed of chain `a` in `ov a d R x`: its leaf-family evaluation (every layer: campaign X1 stage B, top leaves
since campaign T8D), unchanged by `ov`; the seed component of `Hidden` is a dummy. -/
noncomputable def ovSeed (a : ChainAddr) (R : Tables U) (_seed : Digest) : Digest :=
  WCT9.wotsSeed (raw R) a.key.lay a.key.tree a.key.leaf a.chain
/-- Override of chain `a`'s prefix rows (the private table is unchanged). -/
noncomputable def ov (a : ChainAddr) (d : Nat) (R : Tables U) (x : Hidden d) : Tables U :=
  (R.1, ovPub a d R.2 x.1)
noncomputable def rd (a : ChainAddr) (d : Nat) (R : Tables U) : Hidden d :=
  (fun i v => WCT9.halfOf (WCT9.chainHigh a.key.lay a.chain i.val) (R.2 ⟨chainRowW a i v, chainRowW_mem hU a i v⟩), 0)
theorem ovPub_row (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (pub : U → HashOutput)
    (tables : Fin d → Digest → Digest) (i : Fin d) (v : Digest) :
    ovPub a d pub tables ⟨chainRowW a i v, chainRowW_mem hU a i v⟩ =
      joinHalf (WCT9.chainHigh a.key.lay a.chain i.val) (tables i v)
        (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain i.val) (pub ⟨chainRowW a i v, chainRowW_mem hU a i v⟩)) := by
  unfold ovPub
  rw [PrefixGame.rowOf_chainRow a hd i v]
theorem ovPub_none (a : ChainAddr) {d : Nat} (pub : U → HashOutput)
    (tables : Fin d → Digest → Digest) (x : U) (h : PrefixGame.rowOf a d x.val = none) :
    ovPub a d pub tables x = pub x := by
  unfold ovPub
  rw [h]
theorem rd_ov_rows (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : Tables U) (x : Hidden d) :
    (rd hU a d (ov a d R x)).1 = x.1 := by
  obtain ⟨tables, seed⟩ := x
  unfold rd ov
  funext i v
  simp only
  rw [ovPub_row hU a hd, halfOf_joinHalf]
/-- `ov` ignores the seed component. -/
theorem ov_seed_irrel (a : ChainAddr) {d : Nat} (R : Tables U)
    (t : Fin d → Digest → Digest) (s s' : Digest) : ov a d R (t, s) = ov a d R (t, s') := rfl
theorem ov_ov_rd (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : Tables U) (x : Hidden d) :
    ov a d (ov a d R x) (rd hU a d R) = R := by
  obtain ⟨priv, pub⟩ := R
  obtain ⟨tables, seed⟩ := x
  unfold ov rd
  simp only
  refine Prod.ext rfl ?_
  · funext y
    unfold ovPub
    cases hp : PrefixGame.rowOf a d y.val with
    | none => simp only [hp]
    | some p =>
        simp only [hp]
        have hy : y = ⟨chainRowW a p.1 p.2, chainRowW_mem hU a p.1 p.2⟩ := Subtype.ext (PrefixGame.rowOf_some hp)
        subst hy
        rw [halfOf_not_joinHalf, joinHalf_halfOf]
theorem raw_ov_untouched (a : ChainAddr) {d : Nat} (hd : d ≤ 7) (R : Tables U) (x : Hidden d)
    (query : T3.Spec.Domain) (hq : UntouchedP a query) : raw (ov a d R x) query = raw R query := by
  rcases query with (n | input) | (tweak | other)
  · rfl
  · by_cases h : input ∈ U
    · rw [raw_mem _ _ h, raw_mem _ _ h]
      unfold ov
      simp only
      rw [ovPub_none]
      cases hp : PrefixGame.rowOf a d input with
      | none => rfl
      | some p => exact absurd (PrefixGame.rowOf_some hp) (hq p.1 p.2 (by have := p.1.isLt; omega))
    · rw [raw_nonmem _ _ h, raw_nonmem _ _ h]
  · rfl
  · rfl
include hU in
theorem raw_ov_prefix (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : Tables U) (x : Hidden d)
    (i : Fin d) (v : Digest) :
    raw (ov a d R x) (.inl (.inr (chainRowW a i v))) =
      joinHalf (WCT9.chainHigh a.key.lay a.chain i.val) (x.1 i v)
        (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain i.val) (raw R (.inl (.inr (chainRowW a i v))))) := by
  rw [raw_mem _ _ (chainRowW_mem hU a i v), raw_mem _ _ (chainRowW_mem hU a i v)]
  exact ovPub_row hU a hd R.2 x.1 i v
theorem raw_ov_nonprefix (a : ChainAddr) {d : Nat} (R : Tables U) (x : Hidden d)
    (input : HashInput) (h : PrefixGame.rowOf a d input = none) :
    raw (ov a d R x) (.inl (.inr input)) = raw R (.inl (.inr input)) := by
  by_cases hm : input ∈ U
  · rw [raw_mem _ _ hm, raw_mem _ _ hm]
    exact ovPub_none a R.2 x.1 _ h
  · rw [raw_nonmem _ _ hm, raw_nonmem _ _ hm]
/-- `ov` leaves the private table alone. -/
theorem raw_ov_private (a : ChainAddr) {d : Nat} (R : Tables U) (x : Hidden d)
    (coordinate : Coordinate) : raw (ov a d R x) (.inr coordinate) = raw R (.inr coordinate) := rfl

theorem search_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 7) (R : Tables U) (x : Hidden d)
    (L : LeafAddr) (remaining : Nat) :
    searchOf (raw (ov a d R x)) zeroMessages L remaining=searchOf (raw R) zeroMessages L remaining := by
  unfold searchOf
  exact ((CanonicalRef.Mask.respectsP_layerCounterSearchAt a _ _ _ _ _ _ _)
    _ _ (raw_ov_untouched a hd R x)).1

theorem referenceSearch_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 7) (R : Tables U) (x : Hidden d)
    (L : LeafAddr) :
    referenceSearch (raw (ov a d R x)) zeroMessages L=referenceSearch (raw R) zeroMessages L :=
  CanonicalRef.referenceSearch_congr (fun L remaining _ => search_ov a hd R x L remaining) L

theorem depth_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 7) (R : Tables U) (x : Hidden d) (b : ChainAddr) :
    CanonicalRef.depth (raw (ov a d R x)) zeroMessages b=CanonicalRef.depth (raw R) zeroMessages b := by
  unfold CanonicalRef.depth CanonicalRef.referenceDigits
  rw [referenceSearch_ov a hd R x]

end RawPrefix
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawPrefix
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
@[irreducible] noncomputable def restDepth (a : ChainAddr) (R : Tables U) : Nat :=
  CanonicalRef.depth (raw R) zeroMessages a

theorem restDepth_eq (a : ChainAddr) (R : Tables U) :
    restDepth a R=CanonicalRef.depth (raw R) zeroMessages a := by unfold restDepth; rfl

theorem restDepth_le (a : ChainAddr) (R : Tables U) : restDepth a R≤7 := by
  rw [restDepth_eq]
  exact CanonicalRef.Mask.depth_le_seven _ _ _

theorem restDepth_ov (a : ChainAddr) (R : Tables U) (x : Hidden (restDepth a R)) :
    restDepth a (ov a (restDepth a R) R x)=restDepth a R := by
  rw [restDepth_eq,depth_ov a (by have := restDepth_le a R;omega),←restDepth_eq]

theorem wotsSeed_ov (a : ChainAddr) {d : Nat} (R : Tables U) (x : Hidden d) :
    WCT9.wotsSeed (raw (ov a d R x)) a.key.lay a.key.tree a.key.leaf a.chain = ovSeed a R x.2 :=
  Wots.Mask.wotsSeed_congr_private (fun c => raw_ov_private a R x c) _ _ _ _
include hU in
theorem eval_chain_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : Tables U) (x : Hidden d) :
    ∀ (n s : Nat) (hn : s + n ≤ d) (v : Digest),
      evalWithAnswerFn (raw (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s n v) =
        SphincsSecurity.Concrete.PartialChainEndpoint.evaluate
          (fun (i : Fin n) => x.1 ⟨s + i.val, by omega⟩) v := by
  intro n
  induction n with
  | zero =>
      intro s hn v
      simp [WCT9.chainW, SphincsSecurity.Concrete.PartialChainEndpoint.evaluate]
  | succ n ih =>
      intro s hn v
      have hsplit : evalWithAnswerFn (raw (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s (n + 1) v) =
          evalWithAnswerFn (raw (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain (s + 1) n
            (evalWithAnswerFn (raw (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s 1 v))) := by
        rw [show n + 1 = 1 + n by omega]
        exact eval_chainW_add' _ _ _ _ _ _ _ _ _
      rw [hsplit, eval_chainW_one', pad64_chainInputW]
      have hrow : WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain s v = chainRowW a (⟨s, by omega⟩ : Fin d) v := rfl
      rw [hrow, raw_ov_prefix hU a hd R x]
      rw [show (⟨s, by omega⟩ : Fin d).val = s from rfl, halfOf_joinHalf, ih (s + 1) (by omega)]
      simp only [SphincsSecurity.Concrete.PartialChainEndpoint.evaluate]
      congr 1
      · funext i w
        unfold Fin.tail
        exact congrArg (fun j : Fin d => x.1 j w) (Fin.ext (by simp only [Fin.val_succ]; omega))
include hU in
theorem frontierValue_ov (a : ChainAddr) (R : Tables U) (x : Hidden (restDepth a R)) :
    CanonicalRef.frontierValue (raw (ov a (restDepth a R) R x)) zeroMessages a =
      SphincsSecurity.Concrete.PartialChainEndpoint.evaluate x.1 (ovSeed a R x.2) := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  have hdepth : CanonicalRef.depth (raw (ov a (restDepth a R) R x)) zeroMessages a = restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R x)).symm.trans (restDepth_ov a R x)
  unfold CanonicalRef.frontierValue honestChainValueW
  rw [hdepth, wotsSeed_ov]
  rw [eval_chain_ov hU a hd R x (restDepth a R) 0 (by omega)]
  congr 1
  funext i
  exact congrArg x.1 (Fin.ext (by simp only [Nat.zero_add]))

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawPrefix
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsPrefixGameSim ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl record realRun lazyRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
noncomputable local instance instFintypeCoordinate_wotsPrefixGameSim : Fintype Coordinate := coordinateFintype
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
namespace PrefixGame
/-- Pairing stage 1: a query of a prefix row of chain `a` (current-scheme row `chainRowW`). -/
def PrefixQuery (a : ChainAddr) (d : Nat) (query : RefWorld.Domain) : Prop :=
  ∃ (i : Fin d) (v : Digest), query = .inl (.inr (chainRowW a i v))
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
noncomputable def routeImpl (a : ChainAddr) (d : Nat) (R : RefTables adversary) :
    QueryImpl RefWorld (OracleComp (SeedSpec d))
  | .inl (.inl n) => liftM ((SeedSpec d).query (.inl n))
  | .inl (.inr input) =>
      match PrefixGame.rowOf a d input with
      | some p => (fun w => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
            (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (restTable R (.inl (.inr input))))) <$>
          liftM ((SeedSpec d).query (.inr p))
      | none => pure (restTable R (.inl (.inr input)))
  | .inr _ => pure ()
noncomputable def fillTable (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest) : Answers :=
  restTable (ov a (restDepth a R) R (fun _ _ => endpoint, endpoint))
theorem prefixStep_none {T : Answers} {a : ChainAddr} {input : HashInput} (h : prefixStep T a input = none) :
    ¬∃ step value, step < depth T a ∧ input = chainRowW a step value := by
  unfold prefixStep at h
  split at h
  · cases h
  · assumption
theorem evaluate_const_succ (n : Nat) (value start : Digest) :
    evaluate (fun (_ : Fin (n + 1)) (_ : Digest) => value) start = value := by
  simp only [evaluate]
  exact evaluate_const n value
theorem evaluate_fill (n : Nat) (tables : Fin n → Digest → Digest) (start : Digest) :
    evaluate (fun (_ : Fin n) (_ : Digest) => evaluate tables start) start = evaluate tables start := by
  cases n with
  | zero => rfl
  | succ n => exact evaluate_const_succ n _ start
theorem maskAt_ov_fill (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    maskAt (restTable (ov a (restDepth a R) R x)) a =
      maskAt (fillTable a R (evaluate x.1 (ovSeed a R x.2))) a := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  set e := evaluate x.1 (ovSeed a R x.2) with he
  have hdx : depth (restTable (ov a (restDepth a R) R x)) a = restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R x)).symm.trans (restDepth_ov a R x)
  have hdf : depth (fillTable a R e) a = restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R _)).symm.trans (restDepth_ov a R _)
  apply maskAt_congr
  · intro input hp
    have hnone : PrefixGame.rowOf a (restDepth a R) input = none := by
      rw [PrefixGame.rowOf_none_iff]
      have := prefixStep_none hp
      rw [hdx] at this
      exact this
    unfold fillTable
    rw [restTable_ov_nonprefix a R x input hnone, restTable_ov_nonprefix a R _ input hnone]
  · intro coin
    have hg : ∀ (d : Nat) (y z : Hidden d),
        restTable (ov a d R y) (.inl (.inl coin)) = restTable (ov a d R z) (.inl (.inl coin)) :=
      fun _ _ _ => rfl
    exact hg _ _ _
  · intro coordinate
    have hg : ∀ (d : Nat) (y z : Hidden d),
        restTable (ov a d R y) (.inr coordinate) = restTable (ov a d R z) (.inr coordinate) :=
      fun _ _ _ => rfl
    exact hg _ _ _
  · rw [hdx, hdf]
  · rw [frontierValue_ov]
    unfold fillTable
    rw [frontierValue_ov]
    have h1 : ∀ v, ovSeed a R v = ovSeed a R x.2 := fun v => rfl
    rw [h1 e, he]
    exact (evaluate_fill _ _ _).symm
theorem referenceGame_fill (a : ChainAddr) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 24)
    (R : RefTables adversary) (x : Hidden (restDepth a R)) (q : Nat) :
    referenceGame (restTable (ov a (restDepth a R) R x)) adversary q =
      referenceGame (fillTable a R (evaluate x.1 (ovSeed a R x.2))) adversary q := by
  rw [← referenceGame_maskAt _ a htree hleaf, maskAt_ov_fill a R x, referenceGame_maskAt _ a htree hleaf]
end PrefixGame
open PrefixGame in
noncomputable def seedGame (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (endpoint : Digest) : OracleComp (SeedSpec (restDepth a R)) SeedResult :=
  simulateQ (PrefixGame.routeImpl a (restDepth a R) R)
    (SphincsSecurity.QueryCap.recorded (referenceGame (PrefixGame.fillTable a R endpoint) adversary q))
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
theorem fixed_route (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    ((fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1) ∘ₛ routeImpl a d R) =
      (SphincsSecurity.Concrete.OtsPrefix.uniformImpl ∘ₛ refImpl (restTable (ov a d R x))) := by
  funext query
  rcases query with (n | input) | u
  · simp only [QueryImpl.apply_compose, routeImpl, refImpl, simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose, routeImpl, refImpl]
    cases hp : PrefixGame.rowOf a d input with
    | none =>
        simp only [simulateQ_pure]
        rw [restTable_ov_nonprefix a R x input hp]
    | some p =>
        have hin := PrefixGame.rowOf_some hp
        simp only [simulateQ_map, simulateQ_spec_query, simulateQ_pure]
        simp only [fixedImpl, QueryImpl.add_apply_inr]
        rw [hin, restTable_ov_prefix a hd R x p.1 p.2, ← PMF.monad_pure_eq_pure, map_pure]
  · simp only [QueryImpl.apply_compose, routeImpl, refImpl, simulateQ_pure]
theorem fixed_seedGame (q : Nat) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 24)
    (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    simulateQ (fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1)
        (seedGame adversary q a R (evaluate x.1 (ovSeed a R x.2))) =
      (liftM (offlineRun (restTable (ov a (restDepth a R) R x)) adversary q) : PMF SeedResult) := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  unfold seedGame
  rw [← QueryImpl.simulateQ_compose, fixed_route a hd R x, ← referenceGame_fill a htree hleaf R x q,
    QueryImpl.simulateQ_compose]
  rfl
theorem route_step_observed (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary)
    (tables : Fin d → Digest → Digest) (input : RefWorld.Domain) (observed : Fin d → Digest → Option Digest)
    (result : RefWorld.Range input × (Fin d → Digest → Option Digest))
    (hr : result ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables (routeImpl a d R input)
      observed).support) (i : Fin d) (v : Digest) :
    result.2 i v = if input = .inl (.inr (chainRowW a i v)) then some (tables i v) else observed i v := by
  rcases input with (n | input) | u
  · simp only [routeImpl] at hr
    rw [show (liftM ((SeedSpec d).query (.inl n)) : OracleComp (SeedSpec d) _) =
        liftM ((SeedSpec d).query (.inl n)) >>= pure from (bind_pure _).symm,
      SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_query_bind] at hr
    simp only [observedImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff,
      SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff,
      Function.comp_def] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    simp
  · cases hp : PrefixGame.rowOf a d input with
    | none =>
        simp only [routeImpl, hp, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr
        rw [if_neg]
        intro he
        exact PrefixGame.rowOf_none hp (i, v) (Sum.inr.inj (Sum.inl.inj he))
    | some p =>
        simp only [routeImpl, hp] at hr
        rw [map_eq_bind_pure_comp, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_query_bind] at hr
        simp only [observedImpl, StateT.run_mk, PMF.pure_bind, Function.comp_def,
          SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff] at hr
        subst hr
        have hin := PrefixGame.rowOf_some hp
        simp only [record]
        by_cases hpi : p = (i, v)
        · subst hpi
          simp only [Function.update_self, hin, if_true]
        · have hne : input ≠ chainRowW a i v := by
            rw [hin]
            intro he
            obtain ⟨hs, hv⟩ := chainRowW_inj (by have := p.1.isLt; omega) (by have := i.isLt; omega) he
            exact hpi (Prod.ext (Fin.ext hs) hv)
          rw [if_neg (fun he => hne (Sum.inr.inj (Sum.inl.inj he)))]
          by_cases h1 : i = p.1
          · subst h1
            have h2 : v ≠ p.2 := fun h2 => hpi (Prod.ext rfl h2.symm)
            simp only [Function.update_self, Function.update_of_ne h2]
          · simp only [Function.update_of_ne h1]
  · simp only [routeImpl, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
      PMF.mem_support_pure_iff] at hr
    subst hr
    simp
theorem observed_rows (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary)
    (tables : Fin d → Digest → Digest) {β : Type} (computation : OracleComp RefWorld β) :
    ∀ (observed : Fin d → Digest → Option Digest) (result : (β × List RefWorld.Domain) × (Fin d → Digest → Option Digest)),
      result ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables
        (simulateQ (routeImpl a d R) (SphincsSecurity.QueryCap.recorded computation)) observed).support →
      ∀ (i : Fin d) (v : Digest), result.2 i v =
        if (.inl (.inr (chainRowW a i v)) : RefWorld.Domain) ∈ result.1.2 then some (tables i v) else observed i v := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro observed result hr i v
      simp only [SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure,
        SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff] at hr
      subst hr
      simp only [List.not_mem_nil, if_false]
  | query_bind input next ih =>
      intro observed result hr i v
      rw [SphincsSecurity.QueryCap.recorded_query_bind, simulateQ_bind, simulateQ_spec_query, observedRun_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      rw [simulateQ_bind, observedRun_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨tail, htail, hr⟩ := hr
      simp only [simulateQ_pure, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
        PMF.mem_support_pure_iff] at hr
      subst hr
      have hstep := route_step_observed a hd R tables input observed middle hmiddle i v
      have htl := ih middle.1 middle.2 tail htail i v
      simp only [List.mem_cons]
      rw [htl, hstep]
      by_cases h1 : (.inl (.inr (chainRowW a i v)) : RefWorld.Domain) ∈ tail.1.2
      · simp only [h1, or_true, if_true]
      · simp only [h1, if_false, or_false]
        by_cases h2 : input = .inl (.inr (chainRowW a i v))
        · simp only [h2, if_true]
        · simp only [h2, if_false]
          rw [if_neg (fun he => h2 he.symm)]
theorem route_step_count (a : ChainAddr) {d : Nat} (R : RefTables adversary) (input : RefWorld.Domain)
    (first : RefWorld.Range input × Nat)
    (hfirst : first ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery (routeImpl a d R input))) :
    first.2 = if PrefixGame.PrefixQuery a d input then 1 else 0 := by
  rcases input with (n | input) | u
  · simp only [routeImpl, SphincsSecurity.QueryCap.counted_query, support_map, Set.mem_image] at hfirst
    obtain ⟨answer, -, rfl⟩ := hfirst
    rw [if_neg, if_neg]
    · rintro ⟨i, v, he⟩
      cases he
    · exact fun h => h
  · cases hp : PrefixGame.rowOf a d input with
    | none =>
        simp only [routeImpl, hp, SphincsSecurity.QueryCap.counted_pure, mem_support_pure_iff] at hfirst
        subst hfirst
        rw [if_neg]
        rintro ⟨i, v, he⟩
        exact PrefixGame.rowOf_none hp (i, v) (Sum.inr.inj (Sum.inl.inj he))
    | some p =>
        simp only [routeImpl, hp, SphincsSecurity.QueryCap.counted_map, SphincsSecurity.QueryCap.counted_query,
          support_map, Set.mem_image] at hfirst
        obtain ⟨⟨answer, count⟩, hcount, rfl⟩ := hfirst
        obtain ⟨w, -, hw⟩ := hcount
        simp only [Prod.mk.injEq] at hw
        dsimp only
        rw [← hw.2, if_pos (show (IsPrefixQuery (Sum.inr p : (SeedSpec d).Domain) : Prop) from trivial),
          if_pos ⟨p.1, p.2, by rw [PrefixGame.rowOf_some hp]⟩]
  · simp only [routeImpl, SphincsSecurity.QueryCap.counted_pure, mem_support_pure_iff] at hfirst
    subst hfirst
    rw [if_neg]
    rintro ⟨i, v, he⟩
    cases he
theorem counted_rows (a : ChainAddr) {d : Nat} (R : RefTables adversary) {β : Type}
    (computation : OracleComp RefWorld β) :
    ∀ result ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery
        (simulateQ (routeImpl a d R) (SphincsSecurity.QueryCap.recorded computation))),
      result.2 = SphincsSecurity.QueryCap.calls (PrefixGame.PrefixQuery a d) result.1.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro result hr
      simp only [SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure, SphincsSecurity.QueryCap.counted_pure,
        mem_support_pure_iff] at hr
      subst hr
      rfl
  | query_bind input next ih =>
      intro result hr
      rw [SphincsSecurity.QueryCap.recorded_query_bind, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.QueryCap.counted_bind, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨second, hsecond, hr⟩ := hr
      rw [mem_support_pure_iff] at hr
      subst hr
      rw [simulateQ_bind, SphincsSecurity.QueryCap.counted_bind, mem_support_bind_iff] at hsecond
      obtain ⟨tail, htail, hsecond⟩ := hsecond
      simp only [simulateQ_pure, SphincsSecurity.QueryCap.counted_pure, pure_bind, mem_support_pure_iff] at hsecond
      subst hsecond
      have hstep := route_step_count a R input first hfirst
      have htl := ih first.1 tail htail
      simp only [SphincsSecurity.QueryCap.calls_cons, hstep, htl, Nat.add_zero]
end PrefixGame
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
end PrefixGame
open PrefixGame in
noncomputable def seedCost {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary) (result : SeedResult) :
    Nat :=
  SphincsSecurity.QueryCap.calls (PrefixGame.PrefixQuery a (restDepth a R)) result.2
open PrefixGame in
theorem seedGame_charge (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (endpoint : Digest) (result : SeedResult × Nat)
    (h : result ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint))) :
    result.2 = seedCost a R result.1 := by
  unfold seedGame at h
  revert h
  exact PrefixGame.counted_rows (d := restDepth a R) a R (referenceGame (PrefixGame.fillTable a R endpoint) adversary q) result
theorem referenceGame_queryBound (T : Answers) (adversary : AdversaryP) (q : Nat) :
    (referenceGame T adversary q).IsQueryBoundP RefCharged q := by
  unfold referenceGame
  exact SphincsSecurity.QueryCap.run_queryBound RefCharged (offlineGame T adversary) q
open PrefixGame in
theorem seedGame_real_cost (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (result : Digest × (SeedResult × (Fin (restDepth a R) → Digest → Option Digest)))
    (h : result ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
      (fun _ _ => none)).support) :
    seedCost a R result.2.1 ≤ q := by
  have hlazy := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_support_lazy
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R) (fun _ _ => none) result h
  have hseed : result.2.1 ∈ support (seedGame adversary q a R result.1) := by
    revert hlazy
    exact lazyRun_mem_support (seedGame adversary q a R result.1) (fun _ _ => none) result.2
  have hrec : result.2.1 ∈ support (SphincsSecurity.QueryCap.recorded
      (referenceGame (PrefixGame.fillTable a R result.1) adversary q)) := by
    unfold seedGame at hseed
    revert hseed
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (PrefixGame.routeImpl a (restDepth a R) R)
      (SphincsSecurity.QueryCap.recorded (referenceGame (PrefixGame.fillTable a R result.1) adversary q)) result.2.1
  have hcount : (result.2.1.1, SphincsSecurity.QueryCap.calls RefCharged result.2.1.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged
        (referenceGame (PrefixGame.fillTable a R result.1) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨result.2.1, hrec, rfl⟩
  have hbound := referenceGame_queryBound (PrefixGame.fillTable a R result.1) adversary q
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q hbound _ hcount
  refine le_trans ?_ hle
  unfold seedCost SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨i, v, rfl⟩ := hq
  trivial
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem maskAt_congr (answers answers' : Answers) (messages messages' : LeafAddr → WCT9.LayerMsg) (a : ChainAddr)
    (hrows : ∀ input, prefixStep answers messages a input = none →
      answers (.inl (.inr input)) = answers' (.inl (.inr input)))
    (hcoins : ∀ coin, answers (.inl (.inl coin)) = answers' (.inl (.inl coin)))
    (hprivate : ∀ coordinate, answers (.inr coordinate) = answers' (.inr coordinate))
    (hdepth : depth answers messages a = depth answers' messages' a)
    (hfrontier : frontierValue answers messages a = frontierValue answers' messages' a) :
    maskAt answers messages a = maskAt answers' messages' a := by
  have hstep : prefixStep answers messages a = prefixStep answers' messages' a := by
    funext input
    exact congrArg (fun d : Nat =>
      if h : ∃ step value, step<d ∧ input=chainRowW a step value then some (Classical.choose h) else none) hdepth
  funext q
  rcases q with (coin | input) | c
  · exact hcoins coin
  · rw [Mask.maskAt_public, Mask.maskAt_public, ← hstep, hdepth, hfrontier]
    cases hp : prefixStep answers messages a input with
    | none => exact hrows input hp
    | some step => rfl
  · exact hprivate c

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawPrefix
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
noncomputable def fill (a : ChainAddr) (R : Tables U) (endpoint : Digest) : Tables U :=
  ov a (restDepth a R) R (fun _ _ => endpoint, endpoint)

theorem prefixStep_none {T : Answers} {messages : LeafAddr → WCT9.LayerMsg} {a : ChainAddr} {input : HashInput}
    (h : CanonicalRef.prefixStep T messages a input=none) :
    ¬∃step value, step<CanonicalRef.depth T messages a ∧ input=chainRowW a step value := by
  unfold CanonicalRef.prefixStep at h
  split at h
  · cases h
  · assumption

include hU in
theorem maskAt_ov_fill (a : ChainAddr) (R : Tables U) (x : Hidden (restDepth a R)) :
    CanonicalRef.maskAt (raw (ov a (restDepth a R) R x)) zeroMessages a=
      CanonicalRef.maskAt (raw (fill a R (evaluate x.1 (ovSeed a R x.2)))) zeroMessages a := by
  set e := evaluate x.1 (ovSeed a R x.2) with he
  have hdx : CanonicalRef.depth (raw (ov a (restDepth a R) R x)) zeroMessages a=restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R x)).symm.trans (restDepth_ov a R x)
  have hdf : CanonicalRef.depth (raw (fill a R e)) zeroMessages a=restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R _)).symm.trans (restDepth_ov a R _)
  apply CanonicalRef.maskAt_congr
  · intro input hp
    have hn : PrefixGame.rowOf a (restDepth a R) input=none := by
      rw [PrefixGame.rowOf_none_iff]
      have hh := prefixStep_none hp
      rw [hdx] at hh
      exact hh
    unfold fill
    rw [raw_ov_nonprefix a R x input hn,raw_ov_nonprefix a R _ input hn]
  · intro _; rfl
  · intro _; rfl
  · rw [hdx,hdf]
  · rw [frontierValue_ov hU]
    unfold fill
    rw [frontierValue_ov hU]
    exact (Wots.PrefixGame.evaluate_fill _ _ _).symm

include hU in
theorem messages_ov_fill (a : ChainAddr) (hleaf : a.key.leaf<2^24)
    (R : Tables U) (x : Hidden (restDepth a R)) :
    sourceMessages (raw (ov a (restDepth a R) R x))=
      sourceMessages (raw (fill a R (evaluate x.1 (ovSeed a R x.2)))) := by
  rw [←sourceMessages_maskAt (raw (ov a (restDepth a R) R x)) zeroMessages a hleaf,
    maskAt_ov_fill hU a R x,sourceMessages_maskAt _ zeroMessages a hleaf]
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawPrefix

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
theorem depth_eq (R : Tables U) (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key) :
    CanonicalRef.depth (answers hU R) (sourceMessages (answers hU R)) a=
      CanonicalRef.depth (raw R) zeroMessages a := by
  unfold CanonicalRef.depth CanonicalRef.referenceDigits
  rw [referenceSearch_eq hU R a.key ha]

theorem wotsSeed_eq (R : Tables U) (lay : Layer) (tree leaf chain : Nat) :
    WCT9.wotsSeed (answers hU R) lay tree leaf chain=WCT9.wotsSeed (raw R) lay tree leaf chain :=
  Wots.Mask.wotsSeed_congr_private (fun _ => rfl) _ _ _ _

theorem chain_eq (R : Tables U) (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    evalWithAnswerFn (answers hU R) (chain lay tree leaf i start count v)=
      evalWithAnswerFn (raw R) (chain lay tree leaf i start count v) :=
  ((SigGolfCandidate.T3.Security.Wots.Enc.respects_chain lay tree leaf i start count v)
    _ _ (nonEnc hU R)).1

/-- C3 (#866): `chain_eq` for the chain of the current scheme. -/
theorem chainW_eq (R : Tables U) (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    evalWithAnswerFn (answers hU R) (WCT9.chainW lay tree leaf i start count v)=
      evalWithAnswerFn (raw R) (WCT9.chainW lay tree leaf i start count v) :=
  ((ClaudeWCT.W9.T3.Security.Wots.Enc.respects_chainW lay tree leaf i start count v)
    _ _ (nonEnc hU R)).1

theorem frontier_eq (R : Tables U) (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key) :
    CanonicalRef.frontierValue (answers hU R) (sourceMessages (answers hU R)) a=
      CanonicalRef.frontierValue (raw R) zeroMessages a := by
  unfold CanonicalRef.frontierValue ClaudeWCT.W9.T3.Security.Wots.honestChainValueW
  rw [depth_eq hU R a ha,wotsSeed_eq,chainW_eq]
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots.PrefixGame
open OracleComp OracleSpec
open RawPrefix
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

theorem nonEnc_chainRow (a : ChainAddr) (step : Nat) (v : Digest) :
    SigGolfCandidate.T3.Security.Wots.Enc.NonEnc (.inl (.inr (chainRowW a step v))) := by
  change SigGolfCandidate.T3.Security.Wots.Enc.NonEnc (.inl (.inr (WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain step v)))
  have hn := SigGolfCandidate.T3.Security.Wots.Enc.nonEnc_of_hdr _
    (chainHeader a.key.lay a.key.tree a.key.leaf a.chain step)
    (WCT9.chainInputW_header a.key.lay a.key.tree a.key.leaf a.chain step v)
    (SigGolfCandidate.T3.Security.Wots.Enc.notHyper_of_marker (by
      unfold tweakMarker; have := chainHeader_firstByte a.key.lay a.key.tree a.key.leaf a.chain step; omega))
  exact hn

theorem rowOf_encInput (a : ChainAddr) (d : Nat) (e : Wots.Enc.EncIndex) :
    PrefixGame.rowOf a d (Wots.Enc.encInput e)=none := by
  cases hh : PrefixGame.rowOf a d (Wots.Enc.encInput e) with
  | none => rfl
  | some p =>
    have he := PrefixGame.rowOf_some hh
    have hn := nonEnc_chainRow a p.1 p.2
    apply False.elim
    apply hn
    have hc := Wots.Enc.encInput_encHeader e
    rw [he] at hc
    exact hc

theorem answers_chainRow (R : Tables U) (a : ChainAddr) (step : Nat) (v : Digest) :
    answers hU R (.inl (.inr (chainRowW a step v)))=raw R (.inl (.inr (chainRowW a step v))) :=
  nonEnc hU R _ (nonEnc_chainRow a step v)

theorem answers_ov_prefix (a : ChainAddr) {d : Nat} (hd : d≤256) (R : Tables U) (x : Hidden d)
    (i : Fin d) (v : Digest) :
    answers hU (RawPrefix.ov a d R x) (.inl (.inr (chainRowW a i v)))=
      joinHalf (WCT9.chainHigh a.key.lay a.chain i.val) (x.1 i v)
        (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain i.val) (answers hU R (.inl (.inr (chainRowW a i v))))) := by
  rw [answers_chainRow,answers_chainRow,RawPrefix.raw_ov_prefix hU a hd R x]

theorem answers_ov_fill_nonprefix (a : ChainAddr) (hleaf : a.key.leaf<2^24)
    (R : Tables U) (x : Hidden (RawPrefix.restDepth a R)) (input : HashInput)
    (hn : PrefixGame.rowOf a (RawPrefix.restDepth a R) input=none) :
    answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x) (.inl (.inr input))=
      answers hU (RawPrefix.fill a R (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate x.1 (RawPrefix.ovSeed a R x.2)))
        (.inl (.inr input)) := by
  let F := RawPrefix.fill a R (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate x.1 (RawPrefix.ovSeed a R x.2))
  have hm : sourceMessages (raw (RawPrefix.ov a (RawPrefix.restDepth a R) R x))=sourceMessages (raw F) :=
    RawPrefix.messages_ov_fill hU a hleaf R x
  have ht : MessageSwap.table zeroMessages (sourceMessages (raw (RawPrefix.ov a (RawPrefix.restDepth a R) R x)))
      zeroMessages_fit (sourceMessages_fit _) hU=
      MessageSwap.table zeroMessages (sourceMessages (raw F)) zeroMessages_fit (sourceMessages_fit _) hU := by
    congr 1
  change eagerAnswers U R.1 (MessageSwap.table zeroMessages
      (sourceMessages (raw (RawPrefix.ov a (RawPrefix.restDepth a R) R x))) zeroMessages_fit (sourceMessages_fit _) hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x).2)
        (.inl (.inr input))=
    eagerAnswers U R.1 (MessageSwap.table zeroMessages (sourceMessages (raw F)) zeroMessages_fit
      (sourceMessages_fit _) hU F.2) (.inl (.inr input))
  rw [ht]
  by_cases hu : input∈U
  · rw [SigGolfCandidate.T3.Security.Wots.Enc.eagerAnswers_public_mem U R.1 _ ⟨input,hu⟩,
      SigGolfCandidate.T3.Security.Wots.Enc.eagerAnswers_public_mem U R.1 _ ⟨input,hu⟩]
    by_cases he : ∃e,Wots.Enc.encInput e=input
    · obtain ⟨e,he⟩:=he
      have hh : (⟨input,hu⟩ : U)=⟨Wots.Enc.encInput e,hU (Wots.Enc.encInput_short e)⟩ := Subtype.ext he.symm
      rw [hh,MessageSwap.table_at,MessageSwap.table_at]
      change RawPrefix.ovPub a (RawPrefix.restDepth a R) R.2 x.1 _=RawPrefix.ovPub a (RawPrefix.restDepth a R) R.2 _ _
      rw [RawPrefix.ovPub_none _ _ _ _ (rowOf_encInput _ _ _),RawPrefix.ovPub_none _ _ _ _ (rowOf_encInput _ _ _)]
    · push_neg at he
      rw [MessageSwap.table_other _ _ _ _ _ _ _ he,MessageSwap.table_other _ _ _ _ _ _ _ he]
      change RawPrefix.ovPub a (RawPrefix.restDepth a R) R.2 x.1 ⟨input,hu⟩=RawPrefix.ovPub a (RawPrefix.restDepth a R) R.2 _ ⟨input,hu⟩
      rw [RawPrefix.ovPub_none _ _ _ _ hn,RawPrefix.ovPub_none _ _ _ _ hn]
  · rw [SigGolfCandidate.T3.Security.Wots.Enc.eagerAnswers_public_not_mem U R.1 _ input hu,
      SigGolfCandidate.T3.Security.Wots.Enc.eagerAnswers_public_not_mem U R.1 _ input hu]
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

theorem maskAt_ov_fill (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key)
    (hleaf : a.key.leaf<2^24) (R : Tables U) (x : Hidden (RawPrefix.restDepth a R)) :
    CanonicalRef.maskAt (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
      (sourceMessages (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x))) a=
    CanonicalRef.maskAt (answers hU (RawPrefix.fill a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))))
      (sourceMessages (answers hU (RawPrefix.fill a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))))) a := by
  let F := RawPrefix.fill a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))
  have hdx : CanonicalRef.depth (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
      (sourceMessages (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x))) a=RawPrefix.restDepth a R := by
    rw [depth_eq hU _ a ha,←RawPrefix.restDepth_eq,RawPrefix.restDepth_ov]
  have hdf : CanonicalRef.depth (answers hU F) (sourceMessages (answers hU F)) a=RawPrefix.restDepth a R := by
    rw [depth_eq hU F a ha,←RawPrefix.restDepth_eq]
    exact RawPrefix.restDepth_ov a R _
  apply CanonicalRef.maskAt_congr
  · intro input hp
    apply answers_ov_fill_nonprefix hU a hleaf R x input
    rw [PrefixGame.rowOf_none_iff]
    have hh := RawPrefix.prefixStep_none hp
    rw [hdx] at hh
    exact hh
  · intro coin
    rw [nonEnc hU _ _ (by trivial),nonEnc hU _ _ (by trivial)]
    rfl
  · intro coordinate
    rw [nonEnc hU _ _ (by trivial),nonEnc hU _ _ (by trivial)]
    rfl
  · exact hdx.trans hdf.symm
  · rw [frontier_eq hU _ a ha,frontier_eq hU _ a ha,
      RawPrefix.frontierValue_ov hU]
    unfold RawPrefix.fill
    rw [RawPrefix.frontierValue_ov hU]
    exact (Wots.PrefixGame.evaluate_fill _ _ _).symm

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Route
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl record realRun lazyRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_wotsPrefixGameSim : Fintype Coordinate := coordinateFintype
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame
noncomputable def routeImpl (a : ChainAddr) (d : Nat) (prefixBase otherBase : Answers) :
    QueryImpl RefWorld (OracleComp (SeedSpec d))
  | .inl (.inl n) => liftM ((SeedSpec d).query (.inl n))
  | .inl (.inr input) =>
      match PrefixGame.rowOf a d input with
      | some p => (fun w => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
            (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (prefixBase (.inl (.inr input))))) <$>
          liftM ((SeedSpec d).query (.inr p))
      | none => pure (otherBase (.inl (.inr input)))
  | .inr _ => pure ()
theorem route_step_observed (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (prefixBase otherBase : Answers)
    (tables : Fin d → Digest → Digest) (input : RefWorld.Domain) (observed : Fin d → Digest → Option Digest)
    (result : RefWorld.Range input × (Fin d → Digest → Option Digest))
    (hr : result ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables (routeImpl a d prefixBase otherBase input)
      observed).support) (i : Fin d) (v : Digest) :
    result.2 i v = if input = .inl (.inr (chainRowW a i v)) then some (tables i v) else observed i v := by
  rcases input with (n | input) | u
  · simp only [routeImpl] at hr
    rw [show (liftM ((SeedSpec d).query (.inl n)) : OracleComp (SeedSpec d) _) =
        liftM ((SeedSpec d).query (.inl n)) >>= pure from (bind_pure _).symm,
      SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_query_bind] at hr
    simp only [observedImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff,
      SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff,
      Function.comp_def] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    simp
  · cases hp : PrefixGame.rowOf a d input with
    | none =>
        simp only [routeImpl, hp, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr
        rw [if_neg]
        intro he
        exact PrefixGame.rowOf_none hp (i, v) (Sum.inr.inj (Sum.inl.inj he))
    | some p =>
        simp only [routeImpl, hp] at hr
        rw [map_eq_bind_pure_comp, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_query_bind] at hr
        simp only [observedImpl, StateT.run_mk, PMF.pure_bind, Function.comp_def,
          SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff] at hr
        subst hr
        have hin := PrefixGame.rowOf_some hp
        simp only [record]
        by_cases hpi : p = (i, v)
        · subst hpi
          simp only [Function.update_self, hin, if_true]
        · have hne : input ≠ chainRowW a i v := by
            rw [hin]
            intro he
            obtain ⟨hs, hv⟩ := chainRowW_inj (by have := p.1.isLt; omega) (by have := i.isLt; omega) he
            exact hpi (Prod.ext (Fin.ext hs) hv)
          rw [if_neg (fun he => hne (Sum.inr.inj (Sum.inl.inj he)))]
          by_cases h1 : i = p.1
          · subst h1
            have h2 : v ≠ p.2 := fun h2 => hpi (Prod.ext rfl h2.symm)
            simp only [Function.update_self, Function.update_of_ne h2]
          · simp only [Function.update_of_ne h1]
  · simp only [routeImpl, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
      PMF.mem_support_pure_iff] at hr
    subst hr
    simp
theorem observed_rows (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (prefixBase otherBase : Answers)
    (tables : Fin d → Digest → Digest) {β : Type} (computation : OracleComp RefWorld β) :
    ∀ (observed : Fin d → Digest → Option Digest) (result : (β × List RefWorld.Domain) × (Fin d → Digest → Option Digest)),
      result ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables
        (simulateQ (routeImpl a d prefixBase otherBase) (SphincsSecurity.QueryCap.recorded computation)) observed).support →
      ∀ (i : Fin d) (v : Digest), result.2 i v =
        if (.inl (.inr (chainRowW a i v)) : RefWorld.Domain) ∈ result.1.2 then some (tables i v) else observed i v := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro observed result hr i v
      simp only [SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure,
        SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff] at hr
      subst hr
      simp only [List.not_mem_nil, if_false]
  | query_bind input next ih =>
      intro observed result hr i v
      rw [SphincsSecurity.QueryCap.recorded_query_bind, simulateQ_bind, simulateQ_spec_query, observedRun_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      rw [simulateQ_bind, observedRun_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨tail, htail, hr⟩ := hr
      simp only [simulateQ_pure, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
        PMF.mem_support_pure_iff] at hr
      subst hr
      have hstep := route_step_observed a hd prefixBase otherBase tables input observed middle hmiddle i v
      have htl := ih middle.1 middle.2 tail htail i v
      simp only [List.mem_cons]
      rw [htl, hstep]
      by_cases h1 : (.inl (.inr (chainRowW a i v)) : RefWorld.Domain) ∈ tail.1.2
      · simp only [h1, or_true, if_true]
      · simp only [h1, if_false, or_false]
        by_cases h2 : input = .inl (.inr (chainRowW a i v))
        · simp only [h2, if_true]
        · simp only [h2, if_false]
          rw [if_neg (fun he => h2 he.symm)]
theorem route_step_count (a : ChainAddr) {d : Nat} (prefixBase otherBase : Answers) (input : RefWorld.Domain)
    (first : RefWorld.Range input × Nat)
    (hfirst : first ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery (routeImpl a d prefixBase otherBase input))) :
    first.2 = if PrefixGame.PrefixQuery a d input then 1 else 0 := by
  rcases input with (n | input) | u
  · simp only [routeImpl, SphincsSecurity.QueryCap.counted_query, support_map, Set.mem_image] at hfirst
    obtain ⟨answer, -, rfl⟩ := hfirst
    rw [if_neg, if_neg]
    · rintro ⟨i, v, he⟩
      cases he
    · exact fun h => h
  · cases hp : PrefixGame.rowOf a d input with
    | none =>
        simp only [routeImpl, hp, SphincsSecurity.QueryCap.counted_pure, mem_support_pure_iff] at hfirst
        subst hfirst
        rw [if_neg]
        rintro ⟨i, v, he⟩
        exact PrefixGame.rowOf_none hp (i, v) (Sum.inr.inj (Sum.inl.inj he))
    | some p =>
        simp only [routeImpl, hp, SphincsSecurity.QueryCap.counted_map, SphincsSecurity.QueryCap.counted_query,
          support_map, Set.mem_image] at hfirst
        obtain ⟨⟨answer, count⟩, hcount, rfl⟩ := hfirst
        obtain ⟨w, -, hw⟩ := hcount
        simp only [Prod.mk.injEq] at hw
        dsimp only
        rw [← hw.2, if_pos (show (IsPrefixQuery (Sum.inr p : (SeedSpec d).Domain) : Prop) from trivial),
          if_pos ⟨p.1, p.2, by rw [PrefixGame.rowOf_some hp]⟩]
  · simp only [routeImpl, SphincsSecurity.QueryCap.counted_pure, mem_support_pure_iff] at hfirst
    subst hfirst
    rw [if_neg]
    rintro ⟨i, v, he⟩
    cases he
theorem counted_rows (a : ChainAddr) {d : Nat} (prefixBase otherBase : Answers) {β : Type}
    (computation : OracleComp RefWorld β) :
    ∀ result ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery
        (simulateQ (routeImpl a d prefixBase otherBase) (SphincsSecurity.QueryCap.recorded computation))),
      result.2 = SphincsSecurity.QueryCap.calls (PrefixGame.PrefixQuery a d) result.1.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro result hr
      simp only [SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure, SphincsSecurity.QueryCap.counted_pure,
        mem_support_pure_iff] at hr
      subst hr
      rfl
  | query_bind input next ih =>
      intro result hr
      rw [SphincsSecurity.QueryCap.recorded_query_bind, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.QueryCap.counted_bind, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨second, hsecond, hr⟩ := hr
      rw [mem_support_pure_iff] at hr
      subst hr
      rw [simulateQ_bind, SphincsSecurity.QueryCap.counted_bind, mem_support_bind_iff] at hsecond
      obtain ⟨tail, htail, hsecond⟩ := hsecond
      simp only [simulateQ_pure, SphincsSecurity.QueryCap.counted_pure, pure_bind, mem_support_pure_iff] at hsecond
      subst hsecond
      have hstep := route_step_count a prefixBase otherBase input first hfirst
      have htl := ih first.1 tail htail
      simp only [SphincsSecurity.QueryCap.calls_cons, hstep, htl, Nat.add_zero]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Route

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame
open SphincsSecurity.Concrete.PartialChainEndpoint (fixedImpl evaluate observedRun IsPrefixQuery realRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

theorem referenceGame_fill (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key)
    (htree : a.key.tree<2^40) (hleaf : a.key.leaf<2^24)
    (R : Tables U) (x : Hidden (RawPrefix.restDepth a R))
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceGame (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) adversary q=
    PairedReference.referenceGame (answers hU (RawPrefix.fill a R (evaluate x.1 (RawPrefix.ovSeed a R x.2)))) adversary q := by
  rw [←CanonicalRef.referenceGame_maskAt _ a htree hleaf,maskAt_ov_fill hU a ha hleaf R x,
    CanonicalRef.referenceGame_maskAt _ a htree hleaf]

noncomputable def seedGame (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (a : ChainAddr) (R : Tables U) (endpoint : Digest) : OracleComp (SeedSpec (RawPrefix.restDepth a R)) SeedResult :=
  simulateQ (Route.routeImpl a (RawPrefix.restDepth a R) (answers hU R) (answers hU (RawPrefix.fill a R endpoint)))
    (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (answers hU (RawPrefix.fill a R endpoint)) adversary q))

theorem fixed_route (a : ChainAddr) (hleaf : a.key.leaf<2^24)
    (R : Tables U) (x : Hidden (RawPrefix.restDepth a R)) :
    ((fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1) ∘ₛ
      Route.routeImpl a (RawPrefix.restDepth a R) (answers hU R)
        (answers hU (RawPrefix.fill a R (evaluate x.1 (RawPrefix.ovSeed a R x.2)))))=
    (SphincsSecurity.Concrete.OtsPrefix.uniformImpl ∘ₛ
      refImpl (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x))) := by
  have hd : RawPrefix.restDepth a R≤256 := by have := RawPrefix.restDepth_le a R;omega
  funext query
  rcases query with (n | input) | u
  · simp only [QueryImpl.apply_compose,Route.routeImpl,refImpl,simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose,Route.routeImpl,refImpl]
    cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
    | none =>
      simp only [simulateQ_pure]
      rw [answers_ov_fill_nonprefix hU a hleaf R x input hp]
    | some p =>
      have hin := PrefixGame.rowOf_some hp
      simp only [simulateQ_map,simulateQ_spec_query,simulateQ_pure]
      simp only [fixedImpl,QueryImpl.add_apply_inr]
      rw [hin,answers_ov_prefix hU a hd R x p.1 p.2,←PMF.monad_pure_eq_pure,map_pure]
  · simp only [QueryImpl.apply_compose,Route.routeImpl,refImpl,simulateQ_pure]

theorem fixed_seedGame (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key)
    (htree : a.key.tree<2^40) (hleaf : a.key.leaf<2^24)
    (R : Tables U) (x : Hidden (RawPrefix.restDepth a R))
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) :
    simulateQ (fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1)
      (seedGame hU adversary q a R (evaluate x.1 (RawPrefix.ovSeed a R x.2)))=
      (liftM (PairedReference.offlineRun (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) adversary q) : PMF SeedResult) := by
  unfold seedGame
  rw [←QueryImpl.simulateQ_compose,fixed_route hU a hleaf R x,
    ←referenceGame_fill hU a ha htree hleaf R x adversary q,QueryImpl.simulateQ_compose]
  rfl

noncomputable def seedCost (a : ChainAddr) (R : Tables U) (result : SeedResult) : Nat :=
  SphincsSecurity.QueryCap.calls (PrefixGame.PrefixQuery a (RawPrefix.restDepth a R)) result.2

theorem seedGame_charge (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (a : ChainAddr) (R : Tables U) (endpoint : Digest) (result : SeedResult×Nat)
    (h : result∈support (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame hU adversary q a R endpoint))) :
    result.2=seedCost a R result.1 := by
  unfold seedGame at h
  change result.2=SphincsSecurity.QueryCap.calls (PrefixGame.PrefixQuery a (RawPrefix.restDepth a R)) result.1.2
  exact Route.counted_rows a (answers hU R) (answers hU (RawPrefix.fill a R endpoint))
    (PairedReference.referenceGame (answers hU (RawPrefix.fill a R endpoint)) adversary q) result h
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame
open SphincsSecurity.Concrete.PartialChainEndpoint (fixedImpl evaluate observedRun IsPrefixQuery realRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

theorem referenceGame_queryBound (T : Answers) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    (PairedReference.referenceGame T adversary q).IsQueryBoundP RefCharged q := by
  unfold PairedReference.referenceGame
  exact SphincsSecurity.QueryCap.run_queryBound RefCharged (PairedReference.offlineGame T adversary) q
theorem seedGame_real_cost (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr) (R : Tables U)
    (result : Digest × (SeedResult × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)))
    (h : result ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame hU adversary q a R)
      (fun _ _ => none)).support) :
    seedCost a R result.2.1 ≤ q := by
  have hlazy := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_support_lazy
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame hU adversary q a R) (fun _ _ => none) result h
  have hseed : result.2.1 ∈ support (seedGame hU adversary q a R result.1) := by
    revert hlazy
    exact lazyRun_mem_support (seedGame hU adversary q a R result.1) (fun _ _ => none) result.2
  have hrec : result.2.1 ∈ support (SphincsSecurity.QueryCap.recorded
      (PairedReference.referenceGame (answers hU (RawPrefix.fill a R result.1)) adversary q)) := by
    unfold seedGame at hseed
    revert hseed
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (Route.routeImpl a (RawPrefix.restDepth a R) (answers hU R) (answers hU (RawPrefix.fill a R result.1)))
      (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (answers hU (RawPrefix.fill a R result.1)) adversary q)) result.2.1
  have hcount : (result.2.1.1, SphincsSecurity.QueryCap.calls RefCharged result.2.1.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged
        (PairedReference.referenceGame (answers hU (RawPrefix.fill a R result.1)) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨result.2.1, hrec, rfl⟩
  have hbound := referenceGame_queryBound (answers hU (RawPrefix.fill a R result.1)) adversary q
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q hbound _ hcount
  refine le_trans ?_ hle
  unfold seedCost SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨i, v, rfl⟩ := hq
  trivial

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsPrefixGame ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl record realRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
noncomputable local instance instFintypeCoordinate_wotsPrefixGame : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsPrefixGame : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_wotsPrefixGame (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype _
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
end PrefixGame
theorem restLaw_eq_prod (adversary : AdversaryP) :
    restLaw adversary = (PMF.uniformOfFintype FullGame.FullTable).bind
      (fun priv => (PMF.uniformOfFintype (referenceInputs adversary → HashOutput)).map (fun pub => (priv, pub))) := by
  unfold restLaw
  rw [← PrefixGame.uniform_prod]
open PrefixGame in
theorem reference_eq_bind (adversary : AdversaryP) (q : Nat) :
    referenceExperiment adversary q = (restLaw adversary).bind
      (fun R => (liftM (offlineRun (restTable R) adversary q) : PMF SeedResult).map (mkSample (restTable R))) := by
  unfold referenceExperiment referenceComp
  rw [liftM_bind, liftM_uniform]
  simp only [liftM_bind, liftM_uniform, liftM_map]
  rw [restLaw_eq_prod, PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype FullGame.FullTable).bind
  funext priv
  rw [PMF.bind_map]
  rfl
open PrefixGame in
/-- Resampling chain `a`'s prefix rows preserves the rest-table law (the seed is a family evaluation at every layer,
so the seed component of `Hidden` is a dummy). -/
theorem restLaw_resample (adversary : AdversaryP) (a : ChainAddr) {β : Type} (F : RefTables adversary → PMF β) :
    (restLaw adversary).bind F = (restLaw adversary).bind (fun R =>
      (PMF.uniformOfFintype (Hidden (restDepth a R))).bind (fun x => F (PrefixGame.ov a (restDepth a R) R x))) := by
  have h := uniform_resample (Ω := RefTables adversary) (X := fun k => Fin k → Digest → Digest) (restDepth a)
    (fun k R t => PrefixGame.ov a k R (t, 0)) (fun k R => (PrefixGame.rd a k R).1)
    (fun R t => PrefixGame.rd_ov_rows a (by have := PrefixGame.restDepth_le a R; omega) R (t, 0))
    (fun R t => by
      have e := PrefixGame.ov_seed_irrel a (PrefixGame.ov a (restDepth a R) R (t, 0))
        (PrefixGame.rd a (restDepth a R) R).1 0 (PrefixGame.rd a (restDepth a R) R).2
      rw [e]
      exact PrefixGame.ov_ov_rd a (by have := PrefixGame.restDepth_le a R; omega) R (t, 0))
    (fun R t => PrefixGame.restDepth_ov a R (t, 0))
  unfold restLaw
  conv_lhs => rw [← h]
  rw [PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype (RefTables adversary)).bind
  funext R
  rw [PMF.bind_map, show PMF.uniformOfFintype (Hidden (restDepth a R)) =
    PMF.uniformOfFintype ((Fin (restDepth a R) → Digest → Digest) × Digest) from rfl, uniform_prod, PMF.bind_bind]
  simp only [PMF.bind_map]
  apply congrArg (PMF.uniformOfFintype (Fin (restDepth a R) → Digest → Digest)).bind
  funext t
  change F (PrefixGame.ov a (restDepth a R) R (t, 0)) =
    (PMF.uniformOfFintype Digest).bind (fun s => F (PrefixGame.ov a (restDepth a R) R (t, s)))
  simp only [fun s => PrefixGame.ov_seed_irrel a R t s 0]
  exact (PMF.bind_const _ _).symm
open PrefixGame in
/-- The reference experiment as a mixture over the rest tables and chain `a`'s prefix rows, with the chain's seed
frozen at `ovSeed` (its leaf-family evaluation). -/
theorem reference_map_eq_frozen (adversary : AdversaryP) (q : Nat) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) {β : Type} (f : RefSample → β)
    (g : (R : RefTables adversary) → Digest × (SeedResult × (Fin (restDepth a R) → Digest → Option Digest)) → β)
    (hfg : ∀ (R : RefTables adversary) (x : Hidden (restDepth a R))
      (res : SeedResult × (Fin (restDepth a R) → Digest → Option Digest)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
        (seedGame adversary q a R (evaluate x.1 (ovSeed a R x.2))) (fun _ _ => none)).support →
      f (mkSample (restTable (PrefixGame.ov a (restDepth a R) R x)) res.1) =
        g R (evaluate x.1 (ovSeed a R x.2), res)) :
    (referenceExperiment adversary q).map f =
      (restLaw adversary).bind (fun R => (PMF.uniformOfFintype (Hidden (restDepth a R))).bind (fun x =>
        (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
          (seedGame adversary q a R (evaluate x.1 (ovSeed a R x.2))) (fun _ _ => none)).map
          (fun res => g R (evaluate x.1 (ovSeed a R x.2), res)))) := by
  have htree : a.key.tree < 2 ^ 40 := by have := ha.1.1; omega
  have hleaf : a.key.leaf < 2 ^ 24 := by
    have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      generalize a.key.lay = l; unfold height; fin_cases l <;> decide)
    omega
  rw [reference_eq_bind, PMF.map_bind, restLaw_resample adversary a]
  apply congrArg (restLaw adversary).bind
  funext R
  apply congrArg (PMF.uniformOfFintype (Hidden (restDepth a R))).bind
  funext x
  have hfix := PrefixGame.fixed_seedGame (adversary := adversary) q a htree hleaf R x
  rw [← hfix, ← SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_forget _ _ _ (fun _ _ => none),
    PMF.map_comp, PMF.map_comp]
  exact map_congr_support _ _ _ fun res hres => hfg R x res hres
def PrefixRowAt (answers : Answers) (a : ChainAddr) (input : HashInput) : Prop :=
  ∃ step value, step < depth answers a ∧ input = chainRowW a step value
noncomputable def sampleRows (a : ChainAddr) (s : RefSample) (step : Nat) (value : Digest) : Option Digest :=
  if step < depth s.answers a then
    (s.trace.find? fun e => decide (e.1 = chainRowW a step value)).map fun e => rowHalf a step e.2
  else none
noncomputable def prefixCount (a : ChainAddr) (s : RefSample) : Nat :=
  (s.trace.filter fun e => decide (PrefixRowAt s.answers a e.1)).length
noncomputable def sampleView (a : ChainAddr) (s : RefSample) : PrefixView :=
  ⟨depth s.answers a, frontierValue s.answers a, sampleRows a s, prefixCount a s⟩
noncomputable def runView {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary)
    (r : Digest × (SeedResult × (Fin (restDepth a R) → Digest → Option Digest))) : PrefixView :=
  ⟨restDepth a R, r.1, fun step value => if h : step < restDepth a R then r.2.2 ⟨step, h⟩ value else none,
    seedCost a R r.2.1⟩
open PrefixGame in
theorem sampleView_coupled (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (x : Hidden (restDepth a R)) (res : SeedResult × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (seedGame adversary q a R (evaluate x.1 (ovSeed a R x.2))) (fun _ _ => none)).support) :
    sampleView a (mkSample (restTable (PrefixGame.ov a (restDepth a R) R x)) res.1) =
      runView a R (evaluate x.1 (ovSeed a R x.2), res) := by
  have hd : restDepth a R ≤ 256 := by have := PrefixGame.restDepth_le a R; omega
  have hdepth : depth (restTable (PrefixGame.ov a (restDepth a R) R x)) a = restDepth a R :=
    (restDepth_eq a (PrefixGame.ov a (restDepth a R) R x)).symm.trans (PrefixGame.restDepth_ov a R x)
  have hrows : ∀ (i : Fin (restDepth a R)) (v : Digest), res.2 i v =
      if (.inl (.inr (chainRowW a i v)) : RefWorld.Domain) ∈ res.1.2 then some (x.1 i v) else none := by
    unfold seedGame at hres
    revert hres
    intro hres i v
    exact PrefixGame.observed_rows a hd R x.1 _ (fun _ _ => none) res hres i v
  unfold sampleView runView mkSample
  simp only
  rw [PrefixView.mk.injEq]
  refine ⟨hdepth, PrefixGame.frontierValue_ov a R x, ?_, ?_⟩
  · funext step value
    unfold sampleRows
    simp only
    rw [hdepth]
    by_cases hs : step < restDepth a R
    · rw [if_pos hs, dif_pos hs, traceOf_find, hrows ⟨step, hs⟩ value]
      by_cases hm : (.inl (.inr (chainRowW a step value)) : RefWorld.Domain) ∈ res.1.2
      · rw [if_pos hm, if_pos hm]
        simp only [Option.map_some]
        rw [rowHalf, PrefixGame.restTable_ov_prefix a hd R x ⟨step, hs⟩ value]
        exact congrArg some (halfOf_joinHalf _ _ _)
      · rw [if_neg hm, if_neg hm]
        rfl
    · rw [if_neg hs, dif_neg hs]
  · unfold prefixCount seedCost
    simp only
    rw [traceOf_filter_length]
    congr 1
    funext query
    apply propext
    constructor
    · rintro ⟨y, rfl, step, value, hs, rfl⟩
      rw [hdepth] at hs
      exact ⟨⟨step, hs⟩, value, rfl⟩
    · rintro ⟨i, v, rfl⟩
      exact ⟨_, rfl, i, v, by rw [hdepth]; exact i.isLt, rfl⟩
theorem reference_support_trace (adversary : AdversaryP) (q : Nat) (s : RefSample)
    (hs : s ∈ (referenceExperiment adversary q).support) : ∃ qs, s.trace = traceOf s.answers qs := by
  rw [reference_eq_bind, PMF.mem_support_bind_iff] at hs
  obtain ⟨R, -, hs⟩ := hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨run, -, rfl⟩ := hs
  exact ⟨run.2, rfl⟩
theorem sampleRows_eq_some (a : ChainAddr) (s : RefSample) (qs : List RefWorld.Domain)
    (hs : s.trace = traceOf s.answers qs) (step : Nat) (value out : Digest) :
    sampleRows a s step value = some out ↔ step < depth s.answers a ∧ SeenRowW s.trace a step value out := by
  unfold sampleRows SeenRowW
  rw [hs, traceOf_find]
  by_cases hstep : step < depth s.answers a
  · rw [if_pos hstep]
    by_cases hm : (.inl (.inr (chainRowW a step value)) : RefWorld.Domain) ∈ qs
    · rw [if_pos hm]
      simp only [Option.map_some, Option.some.injEq, hstep, true_and]
      constructor
      · rintro rfl
        exact ⟨_, (mem_traceOf _ _ _ _).mpr ⟨hm, rfl⟩, rfl⟩
      · rintro ⟨answer, hmem, rfl⟩
        rw [((mem_traceOf _ _ _ _).mp hmem).2]
    · rw [if_neg hm]
      simp only [Option.map_none, reduceCtorEq, false_iff, not_and, not_exists]
      intro _ answer hmem
      exact absurd ((mem_traceOf _ _ _ _).mp hmem).1 hm
  · rw [if_neg hstep]
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h => absurd h hstep
theorem twoEdgeAt_iff_view (a : ChainAddr) (s : RefSample) (qs : List RefWorld.Domain)
    (hs : s.trace = traceOf s.answers qs) :
    TwoEdgeAt s.answers s.trace a ↔ (sampleView a s).TwoEdge := by
  unfold TwoEdgeAt PrefixView.TwoEdge sampleView
  simp only [sampleRows_eq_some a s qs hs]
  constructor
  · rintro ⟨hd, start, middle, h1, h2⟩
    exact ⟨hd, start, middle, ⟨by omega, h1⟩, ⟨by omega, h2⟩⟩
  · rintro ⟨hd, start, middle, ⟨-, h1⟩, ⟨-, h2⟩⟩
    exact ⟨hd, start, middle, h1, h2⟩
theorem contactAt_iff_view (a : ChainAddr) (s : RefSample) (qs : List RefWorld.Domain)
    (hs : s.trace = traceOf s.answers qs) :
    ContactAt s.answers s.trace a ↔ (sampleView a s).Contact := by
  unfold ContactAt PrefixView.Contact sampleView
  simp only [sampleRows_eq_some a s qs hs]
  constructor
  · rintro ⟨hd, value, h⟩
    exact ⟨hd, value, ⟨by omega, h⟩⟩
  · rintro ⟨hd, value, ⟨-, h⟩⟩
    exact ⟨hd, value, h⟩
theorem runView_twoEdge {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary)
    (r : Digest × (SeedResult × (Fin (restDepth a R) → Digest → Option Digest))) :
    (runView a R r).TwoEdge ↔ TwoEdgeEvent r.2.2 r.1 := by
  rw [SphincsSecurity.Concrete.PartialChainEndpoint.twoEdgeEvent_iff_rows]
  unfold PrefixView.TwoEdge runView
  simp only
  constructor
  · rintro ⟨hd, start, middle, h1, h2⟩
    rw [dif_pos (by omega)] at h1 h2
    exact ⟨(⟨restDepth a R - 2, by omega⟩, start), (⟨restDepth a R - 1, by omega⟩, middle),
      by simp only; omega, by simp only; omega, h1, h2⟩
  · rintro ⟨⟨i, start⟩, ⟨j, middle⟩, hi, hj, h1, h2⟩
    simp only at hi hj h1 h2
    refine ⟨by omega, start, middle, ?_, ?_⟩
    · rw [dif_pos (by omega)]
      have : (⟨restDepth a R - 2, by omega⟩ : Fin (restDepth a R)) = i := Fin.ext (by simp only; omega)
      rw [this]; exact h1
    · rw [dif_pos (by omega)]
      have : (⟨restDepth a R - 1, by omega⟩ : Fin (restDepth a R)) = j := Fin.ext (by simp only; omega)
      rw [this]; exact h2
theorem runView_contact {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary)
    (r : Digest × (SeedResult × (Fin (restDepth a R) → Digest → Option Digest))) :
    (runView a R r).Contact ↔ Contact r.2.2 r.1 := by
  unfold PrefixView.Contact runView Contact
  simp only
  constructor
  · rintro ⟨hd, value, h⟩
    rw [dif_pos (by omega)] at h
    exact ⟨⟨restDepth a R - 1, by omega⟩, by simp only; omega, value, h⟩
  · rintro ⟨i, hi, value, h⟩
    refine ⟨by omega, value, ?_⟩
    rw [dif_pos (by omega)]
    have : (⟨restDepth a R - 1, by omega⟩ : Fin (restDepth a R)) = i := Fin.ext (by simp only; omega)
    rw [this]; exact h
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame
open SphincsSecurity.Concrete.PartialChainEndpoint (fixedImpl evaluate observedRun IsPrefixQuery realRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame PairedReference.offlineRun
attribute [local irreducible] raw normalize answers mkSample
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) := SampleableType.ofFintype _
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

include hU in
theorem uniform_resample_prefix (a : ChainAddr) {β : Type} (F : Tables U → PMF β) :
    (PMF.uniformOfFintype (Tables U)).bind F =
    (PMF.uniformOfFintype (Tables U)).bind (fun R =>
      (PMF.uniformOfFintype (Hidden (RawPrefix.restDepth a R))).bind
        (fun x => F (RawPrefix.ov a (RawPrefix.restDepth a R) R x))) := by
  have h := uniform_resample (Ω := Tables U) (X := fun k => Fin k → Digest → Digest) (RawPrefix.restDepth a)
    (fun k R t => RawPrefix.ov a k R (t,0)) (fun k R => (RawPrefix.rd hU a k R).1)
    (fun R t => RawPrefix.rd_ov_rows hU a (by have := RawPrefix.restDepth_le a R;omega) R (t,0))
    (fun R t => by
      have e := RawPrefix.ov_seed_irrel a (RawPrefix.ov a (RawPrefix.restDepth a R) R (t,0))
        (RawPrefix.rd hU a (RawPrefix.restDepth a R) R).1 0 (RawPrefix.rd hU a (RawPrefix.restDepth a R) R).2
      rw [e]
      exact RawPrefix.ov_ov_rd hU a (by have := RawPrefix.restDepth_le a R;omega) R (t,0))
    (fun R t => RawPrefix.restDepth_ov a R (t,0))
  conv_lhs => rw [←h]
  rw [PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype (Tables U)).bind
  funext R
  rw [PMF.bind_map,show PMF.uniformOfFintype (Hidden (RawPrefix.restDepth a R))=
    PMF.uniformOfFintype ((Fin (RawPrefix.restDepth a R) → Digest → Digest)×Digest) from rfl,
    uniform_prod,PMF.bind_bind]
  simp only [PMF.bind_map]
  apply congrArg (PMF.uniformOfFintype (Fin (RawPrefix.restDepth a R) → Digest → Digest)).bind
  funext t
  change F (RawPrefix.ov a (RawPrefix.restDepth a R) R (t,0))=
    (PMF.uniformOfFintype Digest).bind (fun s=>F (RawPrefix.ov a (RawPrefix.restDepth a R) R (t,s)))
  simp only [fun s=>RawPrefix.ov_seed_irrel a R t s 0]
  exact (PMF.bind_const _ _).symm

theorem referenceInputs_subset (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) :
    SeccLaw.publicUniverse⊆PairedReference.referenceInputs adversary := Finset.subset_union_left

theorem reference_eq_raw (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceExperiment adversary q=
    (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind
      (fun R => (liftM (PairedReference.offlineRun (raw R) adversary q) : PMF SeedResult).map (mkSample (raw R))) := by
  unfold PairedReference.referenceExperiment PairedReference.referenceComp
  rw [liftM_bind,liftM_uniform]
  simp only [liftM_bind,liftM_uniform,liftM_map]
  rw [uniform_prod,PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype FullGame.FullTable).bind
  funext priv
  rw [PMF.bind_map]
  unfold raw mkSample
  rfl

theorem reference_eq_normalized (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceExperiment adversary q=
    (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind
      (fun R => (liftM (PairedReference.offlineRun (answers (referenceInputs_subset adversary) R) adversary q) : PMF SeedResult).map
        (mkSample (answers (referenceInputs_subset adversary) R))) := by
  rw [reference_eq_raw]
  have h := congrArg (fun law : PMF (Tables (PairedReference.referenceInputs adversary)) =>
    law.bind (fun R => (liftM (PairedReference.offlineRun (raw R) adversary q) : PMF SeedResult).map (mkSample (raw R))))
    (uniform_normalize (referenceInputs_subset adversary))
  rw [PMF.bind_map] at h
  simpa only [answers,Function.comp_def] using h.symm
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame
open SphincsSecurity.Concrete.PartialChainEndpoint (fixedImpl evaluate observedRun IsPrefixQuery realRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame PairedReference.offlineRun
attribute [local irreducible] raw normalize answers
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) := SampleableType.ofFintype _
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

def PrefixRowAt (answers : Answers) (a : ChainAddr) (input : HashInput) : Prop :=
  ∃ step value, step < CanonicalRef.depth answers (sourceMessages answers) a ∧ input = chainRowW a step value
noncomputable def sampleRows (a : ChainAddr) (s : RefSample) (step : Nat) (value : Digest) : Option Digest :=
  if step < CanonicalRef.depth s.answers (sourceMessages s.answers) a then
    (s.trace.find? fun e => decide (e.1 = chainRowW a step value)).map fun e => rowHalf a step e.2
  else none
noncomputable def prefixCount (a : ChainAddr) (s : RefSample) : Nat :=
  (s.trace.filter fun e => decide (PrefixRowAt s.answers a e.1)).length
noncomputable def sampleView (a : ChainAddr) (s : RefSample) : PrefixView :=
  ⟨CanonicalRef.depth s.answers (sourceMessages s.answers) a, CanonicalRef.frontierValue s.answers (sourceMessages s.answers) a, sampleRows a s, prefixCount a s⟩
noncomputable def runView {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP} (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (r : Digest × (SeedResult × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))) : PrefixView :=
  ⟨RawPrefix.restDepth a R, r.1, fun step value => if h : step < RawPrefix.restDepth a R then r.2.2 ⟨step, h⟩ value else none,
    seedCost a R r.2.1⟩
theorem sampleView_coupled (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (ha : WotsExtract.SourceLeaf7 a.key)
    (x : Hidden (RawPrefix.restDepth a R)) (res : SeedResult × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (seedGame (referenceInputs_subset adversary) adversary q a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support) :
    sampleView a (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1) =
      runView a R (evaluate x.1 (RawPrefix.ovSeed a R x.2), res) := by
  have hd : RawPrefix.restDepth a R ≤ 256 := by have := RawPrefix.restDepth_le a R; omega
  have hdepth : CanonicalRef.depth (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) (sourceMessages (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x))) a = RawPrefix.restDepth a R :=
    (depth_eq (referenceInputs_subset adversary) _ a ha).trans
      ((RawPrefix.restDepth_eq a (RawPrefix.ov a (RawPrefix.restDepth a R) R x)).symm.trans (RawPrefix.restDepth_ov a R x))
  have hrows : ∀ (i : Fin (RawPrefix.restDepth a R)) (v : Digest), res.2 i v =
      if (.inl (.inr (chainRowW a i v)) : RefWorld.Domain) ∈ res.1.2 then some (x.1 i v) else none := by
    unfold seedGame at hres
    revert hres
    intro hres i v
    exact Route.observed_rows a hd (answers (referenceInputs_subset adversary) R)
      (answers (referenceInputs_subset adversary) (RawPrefix.fill a R (evaluate x.1 (RawPrefix.ovSeed a R x.2)))) x.1 _ (fun _ _ => none) res hres i v
  unfold sampleView runView mkSample
  simp only
  rw [PrefixView.mk.injEq]
  refine ⟨hdepth, (frontier_eq (referenceInputs_subset adversary) _ a ha).trans (RawPrefix.frontierValue_ov (referenceInputs_subset adversary) a R x), ?_, ?_⟩
  · funext step value
    unfold sampleRows
    simp only
    rw [hdepth]
    by_cases hs : step < RawPrefix.restDepth a R
    · rw [if_pos hs, dif_pos hs, traceOf_find, hrows ⟨step, hs⟩ value]
      by_cases hm : (.inl (.inr (chainRowW a step value)) : RefWorld.Domain) ∈ res.1.2
      · rw [if_pos hm, if_pos hm]
        simp only [Option.map_some]
        -- C3 (#866): a row is read through the half its step keeps.
        rw [rowHalf, answers_ov_prefix (referenceInputs_subset adversary) a hd R x ⟨step, hs⟩ value]
        exact congrArg some (halfOf_joinHalf _ _ _)
      · rw [if_neg hm, if_neg hm]
        rfl
    · rw [if_neg hs, dif_neg hs]
  · unfold prefixCount seedCost
    simp only
    rw [traceOf_filter_length]
    congr 1
    funext query
    apply propext
    constructor
    · rintro ⟨y, rfl, step, value, hs, rfl⟩
      rw [hdepth] at hs
      exact ⟨⟨step, hs⟩, value, rfl⟩
    · rintro ⟨i, v, rfl⟩
      exact ⟨_, rfl, i, v, by rw [hdepth]; exact i.isLt, rfl⟩
theorem reference_support_trace (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (s : RefSample)
    (hs : s ∈ (PairedReference.referenceExperiment adversary q).support) : ∃ qs, s.trace = traceOf s.answers qs := by
  rw [reference_eq_normalized, PMF.mem_support_bind_iff] at hs
  obtain ⟨R, -, hs⟩ := hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨run, -, rfl⟩ := hs
  exact ⟨run.2, rfl⟩
theorem sampleRows_eq_some (a : ChainAddr) (s : RefSample) (qs : List RefWorld.Domain)
    (hs : s.trace = traceOf s.answers qs) (step : Nat) (value out : Digest) :
    sampleRows a s step value = some out ↔ step < CanonicalRef.depth s.answers (sourceMessages s.answers) a ∧ SeenRowW s.trace a step value out := by
  unfold sampleRows SeenRowW
  rw [hs, traceOf_find]
  by_cases hstep : step < CanonicalRef.depth s.answers (sourceMessages s.answers) a
  · rw [if_pos hstep]
    by_cases hm : (.inl (.inr (chainRowW a step value)) : RefWorld.Domain) ∈ qs
    · rw [if_pos hm]
      simp only [Option.map_some, Option.some.injEq, hstep, true_and]
      constructor
      · rintro rfl
        exact ⟨_, (mem_traceOf _ _ _ _).mpr ⟨hm, rfl⟩, rfl⟩
      · rintro ⟨answer, hmem, rfl⟩
        rw [((mem_traceOf _ _ _ _).mp hmem).2]
    · rw [if_neg hm]
      simp only [Option.map_none, reduceCtorEq, false_iff, not_and, not_exists]
      intro _ answer hmem
      exact absurd ((mem_traceOf _ _ _ _).mp hmem).1 hm
  · rw [if_neg hstep]
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h => absurd h hstep
theorem twoEdgeAt_iff_view (a : ChainAddr) (s : RefSample) (qs : List RefWorld.Domain)
    (hs : s.trace = traceOf s.answers qs) :
    CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a ↔ (sampleView a s).TwoEdge := by
  unfold CanonicalRef.TwoEdgeAt PrefixView.TwoEdge sampleView
  simp only [sampleRows_eq_some a s qs hs]
  constructor
  · rintro ⟨hd, start, middle, h1, h2⟩
    exact ⟨hd, start, middle, ⟨by omega, h1⟩, ⟨by omega, h2⟩⟩
  · rintro ⟨hd, start, middle, ⟨-, h1⟩, ⟨-, h2⟩⟩
    exact ⟨hd, start, middle, h1, h2⟩
theorem contactAt_iff_view (a : ChainAddr) (s : RefSample) (qs : List RefWorld.Domain)
    (hs : s.trace = traceOf s.answers qs) :
    CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a ↔ (sampleView a s).Contact := by
  unfold CanonicalRef.ContactAt PrefixView.Contact sampleView
  simp only [sampleRows_eq_some a s qs hs]
  constructor
  · rintro ⟨hd, value, h⟩
    exact ⟨hd, value, ⟨by omega, h⟩⟩
  · rintro ⟨hd, value, ⟨-, h⟩⟩
    exact ⟨hd, value, h⟩
theorem runView_twoEdge {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP} (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (r : Digest × (SeedResult × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))) :
    (runView a R r).TwoEdge ↔ TwoEdgeEvent r.2.2 r.1 := by
  rw [SphincsSecurity.Concrete.PartialChainEndpoint.twoEdgeEvent_iff_rows]
  unfold PrefixView.TwoEdge runView
  simp only
  constructor
  · rintro ⟨hd, start, middle, h1, h2⟩
    rw [dif_pos (by omega)] at h1 h2
    exact ⟨(⟨RawPrefix.restDepth a R - 2, by omega⟩, start), (⟨RawPrefix.restDepth a R - 1, by omega⟩, middle),
      by simp only; omega, by simp only; omega, h1, h2⟩
  · rintro ⟨⟨i, start⟩, ⟨j, middle⟩, hi, hj, h1, h2⟩
    simp only at hi hj h1 h2
    refine ⟨by omega, start, middle, ?_, ?_⟩
    · rw [dif_pos (by omega)]
      have : (⟨RawPrefix.restDepth a R - 2, by omega⟩ : Fin (RawPrefix.restDepth a R)) = i := Fin.ext (by simp only; omega)
      rw [this]; exact h1
    · rw [dif_pos (by omega)]
      have : (⟨RawPrefix.restDepth a R - 1, by omega⟩ : Fin (RawPrefix.restDepth a R)) = j := Fin.ext (by simp only; omega)
      rw [this]; exact h2
theorem runView_contact {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP} (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (r : Digest × (SeedResult × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))) :
    (runView a R r).Contact ↔ Contact r.2.2 r.1 := by
  unfold PrefixView.Contact runView Contact
  simp only
  constructor
  · rintro ⟨hd, value, h⟩
    rw [dif_pos (by omega)] at h
    exact ⟨⟨RawPrefix.restDepth a R - 1, by omega⟩, by simp only; omega, value, h⟩
  · rintro ⟨i, hi, value, h⟩
    refine ⟨by omega, value, ?_⟩
    rw [dif_pos (by omega)]
    have : (⟨RawPrefix.restDepth a R - 1, by omega⟩ : Fin (RawPrefix.restDepth a R)) = i := Fin.ext (by simp only; omega)
    rw [this]; exact h

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame
open SphincsSecurity.Concrete.PartialChainEndpoint (fixedImpl evaluate observedRun IsPrefixQuery realRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame PairedReference.offlineRun
attribute [local irreducible] raw normalize answers
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) := SampleableType.ofFintype _
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

theorem reference_map_eq_frozen (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr)
    (ha : WotsExtract.SourceChain7 a) {β : Type} (f : RefSample → β)
    (g : (R : Tables (PairedReference.referenceInputs adversary)) → Digest × (SeedResult × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)) → β)
    (hfg : ∀ (R : Tables (PairedReference.referenceInputs adversary)) (x : Hidden (RawPrefix.restDepth a R))
      (res : SeedResult × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
        (seedGame (referenceInputs_subset adversary) adversary q a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support →
      f (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1) =
        g R (evaluate x.1 (RawPrefix.ovSeed a R x.2), res)) :
    (PairedReference.referenceExperiment adversary q).map f =
      (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind (fun R => (PMF.uniformOfFintype (Hidden (RawPrefix.restDepth a R))).bind (fun x =>
        (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
          (seedGame (referenceInputs_subset adversary) adversary q a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).map
          (fun res => g R (evaluate x.1 (RawPrefix.ovSeed a R x.2), res)))) := by
  have htree : a.key.tree < 2 ^ 40 := by have := ha.1.tree_lt; omega
  have hleaf : a.key.leaf < 2 ^ 24 := by
    have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      generalize a.key.lay = l; unfold height; fin_cases l <;> decide)
    omega
  rw [reference_eq_normalized, PMF.map_bind, uniform_resample_prefix (referenceInputs_subset adversary) a]
  apply congrArg (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind
  funext R
  apply congrArg (PMF.uniformOfFintype (Hidden (RawPrefix.restDepth a R))).bind
  funext x
  have hfix := fixed_seedGame (referenceInputs_subset adversary) q a ha.1 htree hleaf R x adversary
  rw [← hfix, ← SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_forget _ _ _ (fun _ _ => none),
    PMF.map_comp, PMF.map_comp]
  exact map_congr_support _ _ _ fun res hres => hfg R x res hres

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsEncodingMatch ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
def EncodingInput (input : HashInput) : Prop :=
  ∃ (L : LeafAddr) (message : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad),
    Extract.msgFits L.lay message ∧ input = encRow L message counter pad
def EncodingRow : Answers → SigGolfCandidate.T3.Spec.Domain → Prop
  | _, .inl (.inr input) => EncodingInput input
  | _, _ => False
noncomputable def encodingCount (s : RefSample) : Nat :=
  (s.trace.filter fun e => decide (EncodingRow s.answers (.inl (.inr e.1)))).length
theorem encodingCount_mkSample (T : Answers) (r : SeedResult) :
    (encodingCount (mkSample T r) : ENNReal) =
      (((traceOf T r.2).filter fun e => decide (EncodingInput e.1)).length : ENNReal) := rfl
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
theorem layerCounterSearch_first (T : Answers) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) :
    ∀ fuel start k digits, k < fuel →
      (∀ i < k, WCT9.producerDecode lay (WCT9.encodingAnswer lay (T (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf msg
        (BitVec.ofNat 32 (start + i)))))))) = none) →
      WCT9.producerDecode lay (WCT9.encodingAnswer lay (T (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf msg
        (BitVec.ofNat 32 (start + k)))))))) = some digits →
      evalWithAnswerFn T (WCT9.layerCounterSearch lay tree leaf msg start fuel) =
        some (BitVec.ofNat 32 (start + k), digits) := by
  intro fuel
  induction fuel with
  | zero => intro _ k _ hk; omega
  | succ fuel ih =>
      intro start k digits hk hprev hvalid
      simp only [WCT9.layerCounterSearch, evalWithAnswerFn_bind, WCT9.eval_encodingHash]
      rcases k with _ | k
      · simp only [Nat.add_zero] at hvalid ⊢
        rw [hvalid]
        rfl
      · have h0 := hprev 0 (by omega)
        simp only [Nat.add_zero] at h0
        rw [h0]
        have := ih (start + 1) k digits (by omega)
          (fun i hi => by rw [show start + 1 + i = start + (i + 1) by omega]; exact hprev (i + 1) (by omega))
          (by rw [show start + 1 + k = start + (k + 1) by omega]; exact hvalid)
        rw [show start + (k + 1) = start + 1 + k by omega]
        exact this
theorem reached_valid_reference {T : Answers} {L : LeafAddr} {input : HashInput} (hr : Reached T L input)
    {w : List Nat} (hw : WCT9.producerDecode L.lay (WCT9.encodingAnswer L.lay (T (.inl (.inr input)))) = some w) :
    referenceInput T L = some input := by
  obtain ⟨c, hc, rfl, hprev⟩ := hr
  have hs : referenceSearch T L = some (BitVec.ofNat 32 c, w) := by
    unfold referenceSearch
    have := layerCounterSearch_first T L.lay L.tree L.leaf (leafMsg T L) (WCT9.searchLimit L.lay) 0 c w hc
      (fun i hi => by rw [Nat.zero_add, ← encRow_zero]; exact hprev i hi)
      (by rw [Nat.zero_add, ← encRow_zero]; exact hw)
    rw [Nat.zero_add] at this
    exact this
  unfold referenceInput
  rw [hs]
  rfl
def MatchEntry (T : Answers) (entry : Entry) : Prop :=
  ∃ (L : CanonGraph.LeafPos) (message : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad), L.Source ∧
    Extract.msgFits L.lay message ∧ entry.1 = encRow (leafOf L) message counter pad ∧
      referenceInput T (leafOf L) ≠ some (encRow (leafOf L) message counter pad) ∧
      decode L.lay (WCT9.encodingAnswer L.lay entry.2) = some (referenceDigits T (leafOf L))
theorem matchAt_iff (T : Answers) (trace : List Entry) :
    (∃ L : CanonGraph.LeafPos, L.Source ∧ EncodingMatchAt T trace (leafOf L)) ↔
      ∃ entry ∈ trace, MatchEntry T entry := by
  constructor
  · rintro ⟨L, hs, message, counter, pad, answer, hfit, hmem, hne, hdec⟩
    exact ⟨_, hmem, L, message, counter, pad, hs, hfit, rfl, hne, hdec⟩
  · rintro ⟨⟨input, answer⟩, hmem, L, message, counter, pad, hs, hfit, rfl, hne, hdec⟩
    exact ⟨L, hs, message, counter, pad, answer, hfit, hmem, hne, hdec⟩
theorem encInput_leaf {e : EncIndex} {L : CanonGraph.LeafPos} {message : WCT9.LayerMsg} {counter : BitVec 32}
    {pad : RowPad} (hL : L.Source) (he : encInput e = encRow (leafOf L) message counter pad) : e.1.1 = L := by
  obtain ⟨⟨⟨lay, tree, leaf⟩, m, c, p⟩, hs, hok⟩ := e
  obtain ⟨lay', tree', leaf'⟩ := L
  obtain ⟨h1, h2, h3, -⟩ := ClaudeWCT.W9.T3M.BC.layerEncodingRow_coords hs.routed.1 hs.routed.2 hL.routed.1
    hL.routed.2 he
  subst h1
  have e2 : tree = tree' := Fin.ext h2
  have e3 : leaf = leaf' := Fin.ext h3
  subst e2 e3
  rfl
theorem matchEntry_cell_le (T : Answers) (e : EncIndex) :
    Pr[fun ans => MatchEntry T (encInput e, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ (7 / ((4 : ENNReal) * 2^128)) := by
  classical
  let targets : Finset Digest :=
    Finset.univ.filter fun d => decode e.1.1.lay d = some (referenceDigits T (leafOf e.1.1))
  have hcard : targets.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact decode_some_injective (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  calc _ ≤ Pr[fun output => WCT9.encodingAnswer e.1.1.lay output ∈ targets |
        ($ᵗ HashOutput : ProbComp HashOutput)] := by
        apply probEvent_mono
        rintro ans - ⟨L, message, counter, pad, hLs, -, he, -, hdec⟩
        have hL : e.1.1 = L := encInput_leaf hLs he
        subst hL
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdec⟩
    _ ≤ 7 / ((4 : ENNReal) * 2^128) := by
      by_cases hl : e.1.1.lay = 0
      · rw [hl]
        refine le_trans (probEvent_mono ?_) ((WCT9.probability_top_verification_exists_le targets).trans ?_)
        · intro output _ h
          exact ⟨WCT9.encodingHigh 0 output, by rw [WCT9.verificationAnswer_honest]; exact h⟩
        · have hc : (targets.card : ENNReal) ≤ 1 := by exact_mod_cast hcard
          simpa only [one_mul] using mul_le_mul' hc (le_refl (7 / ((4 : ENNReal) * 2^128)))
      · have hp : ∀ d, d ∈ targets → lowerSpare d := fun d hd =>
          decode_lowerSpare hl (Finset.mem_filter.mp hd).2
        have hprob := WCT9.probability_lower_encoding (fun d => d ∈ targets) hp
        simp only [Function.comp_def, Finset.filter_mem_eq_inter, Finset.univ_inter] at hprob
        simp only [WCT9.encodingAnswer, if_neg hl]
        rw [hprob]
        have hc : (targets.card : ENNReal) ≤ 1 := by exact_mod_cast hcard
        simpa only [one_mul] using mul_le_mul' hc
          (le_refl (7 / ((4 : ENNReal) * 2^128)))

theorem matchEntry_other (U : Finset HashInput) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (x : HashInput) (hx : ¬ Lazy.IsCell encInput (freeSet (eagerAnswers U privateTable pub)) x) :
    ¬ MatchEntry (eagerAnswers U privateTable pub) (x, eagerAnswers U privateTable pub (.inl (.inr x))) := by
  rintro ⟨L, message, counter, pad, hLs, hfit, he, hne, hdec⟩
  have hreached : Reached (eagerAnswers U privateTable pub) (leafOf L) x := by
    by_contra hfree
    have hx' : encInput (encIdx L hLs message counter pad hfit) = x :=
      (encInput_encIdx L hLs message counter pad hfit).trans he.symm
    exact hx ⟨encIdx L hLs message counter pad hfit, by
      change ¬ Reached _ _ (encInput (encIdx L hLs message counter pad hfit))
      rw [hx']
      exact hfree, hx'⟩
  have href := reached_valid_reference hreached (ClaudeWCT.W9.T3.Security.WotsExtract.producerDecode_of_reference _ _ hdec)
  exact hne (he ▸ href)
section Table
variable (adversary : AdversaryP) (q : Nat)
theorem publicUniverse_sub (adversary : AdversaryP) : SeccLaw.publicUniverse ⊆ referenceInputs adversary :=
  Finset.subset_union_left
theorem eager_ov_eq (U : Finset HashInput) (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) (y : freeSet (eagerAnswers U privateTable pub) → HashOutput) :
    eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y) =
      Lazy.overwrite encInput (freeSet (eagerAnswers U privateTable pub)) (eagerAnswers U privateTable pub) y := by
  funext query
  rcases query with (n | x) | c
  · simp only [eagerAnswers, Lazy.overwrite]
  · by_cases hx : Lazy.IsCell encInput (freeSet (eagerAnswers U privateTable pub)) x
    · have hxU : x ∈ U := by
        obtain ⟨e, -, rfl⟩ := hx
        exact hU (encInput_short e)
      rw [eagerAnswers_public_mem U privateTable _ ⟨x, hxU⟩]
      simp only [Lazy.overwrite, dif_pos hx]
      unfold ov
      have hx' : ∃ e, e ∈ freeSet (eagerAnswers U privateTable pub) ∧ encInput e = (⟨x, hxU⟩ : U).val := hx
      rw [dif_pos hx']
      rfl
    · simp only [Lazy.overwrite, dif_neg hx]
      by_cases hxU : x ∈ U
      · rw [eagerAnswers_public_mem U privateTable _ ⟨x, hxU⟩, eagerAnswers_public_mem U privateTable _ ⟨x, hxU⟩]
        exact ov_other _ _ _ _ (fun e he heq => hx ⟨e, he, heq⟩)
      · rw [eagerAnswers_public_not_mem U _ _ x hxU, eagerAnswers_public_not_mem U _ _ x hxU]
  · simp only [eagerAnswers, Lazy.overwrite]
theorem free_transfer [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) (U : Finset HashInput) (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) (h : RefSample → ENNReal) (φ : List Entry → ENNReal)
    (hφ : ∀ y r, h (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) =
      φ (traceOf (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r.2)) :
    ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          h (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) =
      ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl encInput (freeSet (eagerAnswers U privateTable pub))
          (eagerAnswers U privateTable pub))
          (SphincsSecurity.QueryPause.traced Lazy.obs (referenceGame (eagerAnswers U privateTable pub) adversary q))).run
          (fun _ => Finset.univ)] * φ z.1.2.toList := by
  have hinner : ∀ y : freeSet (eagerAnswers U privateTable pub) → HashOutput,
      ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          h (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) =
        ∑' r, Pr[= r | 𝒮[simulateQ (refImpl (Lazy.overwrite encInput (freeSet (eagerAnswers U privateTable pub))
          (eagerAnswers U privateTable pub) y))
          (SphincsSecurity.QueryPause.traced Lazy.obs (referenceGame (eagerAnswers U privateTable pub) adversary q))]] *
            φ r.2.toList := by
    intro y
    have hgame : referenceGame (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
        adversary q = referenceGame (eagerAnswers U privateTable pub) adversary q :=
      referenceGame_congr_honest (AgreeOn.of_eq (honest_ov U privateTable pub y)) adversary q
    simp only [PrefixGame.liftM_apply, hφ, probOutput_evalSPMF]
    unfold offlineRun
    rw [hgame, ← eager_ov_eq U hU privateTable pub y]
    have hmap := Lazy.recorded_traced (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
      (referenceGame (eagerAnswers U privateTable pub) adversary q)
    rw [← tsum_probOutput_map_mul _ (fun r : SeedResult => (r.1, traceOf (eagerAnswers U privateTable
      (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r.2)) (fun z : Option (Bool × Nat) × List Entry => φ z.2),
      hmap, tsum_probOutput_map_mul]
  simp only [hinner]
  rw [← Lazy.lazyRun_eq_simulate,
    ← tsum_probOutput_map_mul _ Prod.fst (fun r : Option (Bool × Nat) × FreeMonoid Entry => φ r.2.toList),
    ← Lazy.eager_lazy, tsum_probOutput_bind_mul]
  simp only [probOutput_complete_univ (iX (freeSet (eagerAnswers U privateTable pub)))]
theorem eager_ovk_eq (U : Finset HashInput) (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) (k : Set EncIndex) (y : k → HashOutput) :
    eagerAnswers U privateTable (ov k pub y) = Lazy.overwrite encInput k (eagerAnswers U privateTable pub) y := by
  funext query
  rcases query with (n | x) | c
  · simp only [eagerAnswers, Lazy.overwrite]
  · by_cases hx : Lazy.IsCell encInput k x
    · have hxU : x ∈ U := by
        obtain ⟨e, -, rfl⟩ := hx
        exact hU (encInput_short e)
      rw [eagerAnswers_public_mem U privateTable _ ⟨x, hxU⟩]
      simp only [Lazy.overwrite, dif_pos hx]
      unfold ov
      have hx' : ∃ e, e ∈ k ∧ encInput e = (⟨x, hxU⟩ : U).val := hx
      rw [dif_pos hx']
      rfl
    · simp only [Lazy.overwrite, dif_neg hx]
      by_cases hxU : x ∈ U
      · rw [eagerAnswers_public_mem U privateTable _ ⟨x, hxU⟩, eagerAnswers_public_mem U privateTable _ ⟨x, hxU⟩]
        exact ov_other _ _ _ _ (fun e he heq => hx ⟨e, he, heq⟩)
      · rw [eagerAnswers_public_not_mem U _ _ x hxU, eagerAnswers_public_not_mem U _ _ x hxU]
  · simp only [eagerAnswers, Lazy.overwrite]
theorem cell_transfer [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (U : Finset HashInput) (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) (h : RefSample → ENNReal) (φ : List Entry → ENNReal)
    (hφ : ∀ y, (∀ e, y e ∈ cellInit (cellKey (eagerAnswers U privateTable pub)) e) → ∀ r,
      h (mkSample (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) r) = φ (traceOf (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) r.2)) :
    ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) adversary q) : PMF SeedResult) r *
          h (mkSample (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) r) =
      ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl encInput (cellKey (eagerAnswers U privateTable pub)).1 (eagerAnswers U privateTable pub))
          (SphincsSecurity.QueryPause.traced Lazy.obs (referenceGame (eagerAnswers U privateTable pub) adversary q))).run
          (cellInit (cellKey (eagerAnswers U privateTable pub)))] * φ z.1.2.toList := by
  have hinner : ∀ y : (cellKey (eagerAnswers U privateTable pub)).1 → HashOutput, (∀ e, y e ∈ cellInit (cellKey (eagerAnswers U privateTable pub)) e) →
      ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) adversary q) : PMF SeedResult) r *
          h (mkSample (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) r) =
        ∑' r, Pr[= r | 𝒮[simulateQ (refImpl (Lazy.overwrite encInput (cellKey (eagerAnswers U privateTable pub)).1 (eagerAnswers U privateTable pub) y))
          (SphincsSecurity.QueryPause.traced Lazy.obs (referenceGame (eagerAnswers U privateTable pub) adversary q))]] *
            φ r.2.toList := by
    intro y hy
    have hgame : referenceGame (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) adversary q = referenceGame (eagerAnswers U privateTable pub) adversary q :=
      referenceGame_congr_honest (agree_ovc U hU privateTable pub y hy) adversary q
    simp only [PrefixGame.liftM_apply, hφ y hy, probOutput_evalSPMF]
    unfold offlineRun
    rw [hgame, ← eager_ovk_eq U hU privateTable pub _ y]
    have hmap := Lazy.recorded_traced (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) (referenceGame (eagerAnswers U privateTable pub) adversary q)
    rw [← tsum_probOutput_map_mul _ (fun r : SeedResult => (r.1, traceOf (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) r.2))
      (fun z : Option (Bool × Nat) × List Entry => φ z.2), hmap, tsum_probOutput_map_mul]
  refine Eq.trans (tsum_congr (g := fun y : (cellKey (eagerAnswers U privateTable pub)).1 → HashOutput =>
      PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, Pr[= r | 𝒮[simulateQ (refImpl (Lazy.overwrite encInput (cellKey (eagerAnswers U privateTable pub)).1 (eagerAnswers U privateTable pub) y))
          (SphincsSecurity.QueryPause.traced Lazy.obs (referenceGame (eagerAnswers U privateTable pub) adversary q))]] *
            φ r.2.toList) fun y => ?_) ?_
  · by_cases hy : ∀ e, y e ∈ cellInit (cellKey (eagerAnswers U privateTable pub)) e
    · rw [hinner y hy]
    · rw [PMF.uniformOfFinset_apply, if_neg (fun hm => hy (Fintype.mem_piFinset.mp hm)), zero_mul, zero_mul]
  · rw [← Lazy.lazyRun_eq_simulate,
      ← tsum_probOutput_map_mul _ Prod.fst (fun r : Option (Bool × Nat) × FreeMonoid Entry => φ r.2.toList),
      ← Lazy.eager_lazy_init (hinit := cellInit_nonempty _), tsum_probOutput_bind_mul]
    simp only [probOutput_complete_init _ (cellInit_nonempty _)]
noncomputable def matchInd (s : RefSample) : ENNReal :=
  if ∃ L : CanonGraph.LeafPos, L.Source ∧ EncodingMatchAt s.answers s.trace (leafOf L) then 1 else 0
theorem encodingMatchAt_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (trace : List Entry)
    {L : CanonGraph.LeafPos} (hs : L.Source) :
    EncodingMatchAt T' trace (leafOf L) ↔ EncodingMatchAt T trace (leafOf L) := by
  unfold EncodingMatchAt
  rw [referenceInput_congr_honest h hs, referenceDigits_congr_honest h hs]
theorem matchAt_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (trace : List Entry) :
    (∃ L : CanonGraph.LeafPos, L.Source ∧ EncodingMatchAt T' trace (leafOf L)) ↔
      ∃ L : CanonGraph.LeafPos, L.Source ∧ EncodingMatchAt T trace (leafOf L) :=
  exists_congr fun _ => ⟨fun ⟨hs, hm⟩ => ⟨hs, (encodingMatchAt_congr h trace hs).mp hm⟩,
    fun ⟨hs, hm⟩ => ⟨hs, (encodingMatchAt_congr h trace hs).mpr hm⟩⟩
theorem cellCount_le_encoding (F : Set EncIndex) (tr : List Entry) :
    Lazy.cellCount encInput F tr ≤ (tr.filter fun e => decide (EncodingInput e.1)).length := by
  unfold Lazy.cellCount
  apply List.Sublist.length_le
  apply List.monotone_filter_right
  intro e he
  simp only [decide_eq_true_eq] at he ⊢
  obtain ⟨x, -, hx⟩ := he
  exact ⟨_, _, _, _, x.2.2.1, hx.symm⟩
theorem free_match_le [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) (U : Finset HashInput) (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) :
    ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          matchInd (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) ≤
      (7 / ((4 : ENNReal) * 2^128)) * ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          (encodingCount (mkSample (eagerAnswers U privateTable
            (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) : ENNReal) := by
  rw [free_transfer adversary q iX U hU privateTable pub matchInd
      (fun tr => (Lazy.marks (fun (_ : Unit) => MatchEntry (eagerAnswers U privateTable pub)) tr : ENNReal))
      (fun y r => by
        unfold matchInd mkSample
        rw [marks_unit]
        dsimp only
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd ((matchAt_iff _ _).mp
            ((matchAt_congr (AgreeOn.of_eq (honest_ov U privateTable pub y)) _).mp h1)) h2
        · exact absurd ((matchAt_congr (AgreeOn.of_eq (honest_ov U privateTable pub y)) _).mpr
            ((matchAt_iff _ _).mpr h2)) h1
        · rfl),
    free_transfer adversary q iX U hU privateTable pub (fun s => (encodingCount s : ENNReal))
      (fun tr => (((tr.filter fun e => decide (EncodingInput e.1)).length : Nat) : ENNReal))
      (fun y r => encodingCount_mkSample _ r)]
  refine (Lazy.lazy_marks_le encInput (freeSet (eagerAnswers U privateTable pub)) encInput_injective
    (eagerAnswers U privateTable pub) (fun (_ : Unit) => MatchEntry (eagerAnswers U privateTable pub)) _
    (fun e => by simpa only [Finset.univ_unique, Finset.sum_singleton] using
      matchEntry_cell_le (eagerAnswers U privateTable pub) e.val)
    (fun x hx _ => matchEntry_other U privateTable pub x hx) _).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_)
  exact_mod_cast cellCount_le_encoding _ _
end Table
end Enc
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Enc
open ClaudeWCT.W9.T3.Security.Wots.Enc
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
theorem cell_transfer (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) [∀ k : Set Enc.EncIndex, Fintype k] [∀ k : Set Enc.EncIndex, DecidableEq k]
    (U : Finset HashInput) (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) (h : RefSample → ENNReal) (φ : List Entry → ENNReal)
    (hφ : ∀ y, (∀ e, y e ∈ cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))) e) → ∀ r,
      h (mkSample (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) = φ (traceOf (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r.2)) :
    ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          h (mkSample (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) =
      ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl Enc.encInput (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells (eagerAnswers U privateTable pub))
          (SphincsSecurity.QueryPause.traced Lazy.obs (PairedReference.referenceGame (eagerAnswers U privateTable pub) adversary q))).run
          (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))))] * φ z.1.2.toList := by
  have hinner : ∀ y : (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells → HashOutput, (∀ e, y e ∈ cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))) e) →
      ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          h (mkSample (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) =
        ∑' r, Pr[= r | 𝒮[simulateQ (refImpl (Lazy.overwrite Enc.encInput (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells (eagerAnswers U privateTable pub) y))
          (SphincsSecurity.QueryPause.traced Lazy.obs (PairedReference.referenceGame (eagerAnswers U privateTable pub) adversary q))]] *
            φ r.2.toList := by
    intro y hy
    have hgame : PairedReference.referenceGame (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q = PairedReference.referenceGame (eagerAnswers U privateTable pub) adversary q :=
      referenceGame_overwrite hU privateTable pub y hy adversary q
    simp only [PrefixGame.liftM_apply, hφ y hy, probOutput_evalSPMF]
    unfold PairedReference.offlineRun
    rw [hgame, ← Enc.eager_ovk_eq U hU privateTable pub _ y]
    have hmap := Lazy.recorded_traced (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) (PairedReference.referenceGame (eagerAnswers U privateTable pub) adversary q)
    rw [← tsum_probOutput_map_mul _ (fun r : SeedResult => (r.1, traceOf (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r.2))
      (fun z : Option (Bool × Nat) × List Entry => φ z.2), hmap, tsum_probOutput_map_mul]
  refine Eq.trans (tsum_congr (g := fun y : (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells → HashOutput =>
      PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, Pr[= r | 𝒮[simulateQ (refImpl (Lazy.overwrite Enc.encInput (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells (eagerAnswers U privateTable pub) y))
          (SphincsSecurity.QueryPause.traced Lazy.obs (PairedReference.referenceGame (eagerAnswers U privateTable pub) adversary q))]] *
            φ r.2.toList) fun y => ?_) ?_
  · by_cases hy : ∀ e, y e ∈ cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))) e
    · rw [hinner y hy]
    · rw [PMF.uniformOfFinset_apply, if_neg (fun hm => hy (Fintype.mem_piFinset.mp hm)), zero_mul, zero_mul]
  · rw [← Lazy.lazyRun_eq_simulate,
      ← tsum_probOutput_map_mul _ Prod.fst (fun r : Option (Bool × Nat) × FreeMonoid Entry => φ r.2.toList),
      ← Lazy.eager_lazy_init (hinit := cellInit_nonempty _), tsum_probOutput_bind_mul]
    simp only [probOutput_complete_init _ (cellInit_nonempty _)]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsTransportCount ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinateF GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsTransportCount : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsTransportCount : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace Ref
open SigGolfCandidate.T3.Security.Wots.Ref
theorem interaction_count_le (T : Answers) (published : T3.Cache) (C : T3.Spec.Domain → Prop) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) (state : LazyPrivate.State) (budget : Nat)
    (weight : α × QueryLog Requests → Nat → ℝ≥0∞) :
    expectedValue (simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (offlineInteraction T published program)))
        (fun run => (refCharge C budget run.2 : ℝ≥0∞) +
          weight run.1 (budget - SphincsSecurity.QueryCap.calls RefCharged run.2)) ≤
      expectedValue (fixedRecord T (FullGame.loggedWith (FullGame.authenticatedSign published) program) state)
        (fun result => (SeccLaw.classCharge C budget result.events : ℝ≥0∞) +
          weight result.value (budget - chargeSum result.events)) := by
  induction program using OracleComp.inductionOn generalizing state budget weight with
  | pure value =>
      rw [offlineInteraction_pure, FullGame.loggedWith_pure, fixedRecord_pure, SphincsSecurity.QueryCap.recorded_pure,
        simulateQ_pure, expectedValue_pure, expectedValue_pure]
      simp [SeccLaw.classCharge, cappedCount, SphincsSecurity.QueryCap.calls_nil]
  | query_bind input next ih =>
      rcases input with input | request
      · rw [FullGame.loggedWith_world, offlineInteraction_world]
        change expectedValue (simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded
            (liftM (RefWorld.query (.inl input)) >>= fun answer => offlineInteraction T published (next answer)))) _ ≤
          expectedValue (fixedRecord T (liftM (T3.Spec.query (.inl input)) >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer)) state) _
        rw [SphincsSecurity.QueryCap.recorded_query_bind, fixedRecord_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, expectedValue_bind, expectedValue_pure,
          expectedValue_map]
        rcases input with n | x
        · change expectedValue (liftM (unifSpec.query n) : ProbComp _) _ ≤
            expectedValue (liftM (unifSpec.query n) : ProbComp _) _
          apply expectedValue_mono
          intro answer
          simp only [refCharge_coin, calls_coin, classCharge_coin_mk, chargeSum_cons, queryCharge_coin,
            Nat.zero_add]
          exact ih answer _ budget weight
        · change expectedValue (pure (T (.inl (.inr x))) : ProbComp _) _ ≤
            expectedValue (pure (T (.inl (.inr x))) : ProbComp _) _
          rw [expectedValue_pure, expectedValue_pure]
          simp only [refCharge_hash, calls_hash, classCharge_public_mk, chargeSum_cons, queryCharge_public,
            Nat.cast_add, ← Nat.sub_sub, add_assoc]
          try simp only [expectedValue_const_add]
          exact add_le_add le_rfl (ih _ _ (budget - 1) weight)
      · rw [FullGame.loggedWith_request, offlineInteraction_request]
        unfold offlineSign
        rw [bind_assoc]
        simp only [pure_bind]
        rw [recorded_bind, simulateQ_bind, ticks_recorded, pure_bind, recorded_map, fixedRecord_bind,
          fixedRecord_hashOnly T _ (authenticatedSign_hashOnly published request), pure_bind]
        simp only [simulateQ_bind, simulateQ_map, simulateQ_pure, expectedValue_bind, expectedValue_pure,
          expectedValue_map, fixedRecord_map]
        rw [pureRecord_value]
        have hcharge : chargeSum (pureRecord T (FullGame.authenticatedSign published request) state).events =
            signCharge T published request :=
          pureRecord_charge T _ (authenticatedSign_hashOnly published request) state
        refine le_trans (le_of_eq ?_) (le_trans (ih (evalWithAnswerFn T (FullGame.authenticatedSign published request))
          (pureRecord T (FullGame.authenticatedSign published request) state).state
          (budget - signCharge T published request)
          (fun value rest => weight (value.1, ⟨request, evalWithAnswerFn T (FullGame.authenticatedSign published request)⟩ ::
            value.2) rest)) ?_)
        · congr 1
          funext run
          rw [refCharge_append, calls_replicate_tick, refCharge_replicate_tick, calls_append, calls_replicate_tick,
            Nat.zero_add, Nat.sub_sub]
        · apply expectedValue_mono
          intro result
          rw [classCharge_append, chargeSum_append, hcharge, Nat.sub_sub]
          gcongr
          exact le_add_left le_rfl
theorem offlineRun_calls_le (T : Answers) (adversary : AdversaryP) (q : Nat)
    (run : Option (Bool × Nat) × List RefWorld.Domain) (hrun : run ∈ support (offlineRun T adversary q)) :
    SphincsSecurity.QueryCap.calls RefCharged run.2 ≤ q := by
  have hmem := SphincsSecurity.QueryCap.simulate_oracle_mem_support (refImpl T) _ run hrun
  exact SphincsSecurity.QueryCap.recorded_calls_le RefCharged _ (fun _ => q)
    (fun result hresult => SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q
      (SphincsSecurity.QueryCap.run_queryBound RefCharged _ q) result hresult) run hmem
theorem table_count_le (adversary : AdversaryP) (q : Nat) (T : Answers) (C : T3.Spec.Domain → Prop) :
    expectedValue (offlineRun T adversary q) (fun run => (refCharge C q run.2 : ℝ≥0∞)) ≤
      expectedValue (fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅))
        (fun result => (SeccLaw.classCharge C q result.events : ℝ≥0∞)) := by
  unfold offlineRun referenceGame
  rw [cap_cappedCount RefCharged (RefClass C) (refImpl T) (offlineGame T adversary) q]
  unfold offlineGame
  rw [recorded_bind, simulateQ_bind, ticks_recorded, pure_bind, recorded_bind, simulateQ_bind]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc]
  simp only [verdict_recorded_fixed T _ (PaddedGame.verdict_public _ _), pure_bind]
  rw [expectedValue_bind]
  simp only [expectedValue_pure]
  rw [fixed_game_eq, expectedValue_map]
  unfold fixedInteraction
  refine le_trans (le_of_eq ?_) (le_trans (interaction_count_le T (evalWithAnswerFn T keygen).2 C
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) (pureRecord T keygen (∅, ∅)).state
    (q - keygenCharge T) (fun value rest => (refCharge C rest ((SourceReplay.queried T
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 value)).map embed) : ℝ≥0∞))) ?_)
  · congr 1
    funext run
    show (refCharge C q (List.replicate (keygenCharge T) (.inr ()) ++ (run.2 ++ List.map embed
      (SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 run.1)))) : ℝ≥0∞) = _
    rw [refCharge_append, refCharge_replicate_tick, calls_replicate_tick, refCharge_append, Nat.zero_add,
      Nat.cast_add]
  · apply expectedValue_mono
    intro interaction
    have hk : chargeSum (pureRecord T keygen (∅, ∅)).events = keygenCharge T :=
      pureRecord_charge T keygen SourceReplay.keygen_hashOnly (∅, ∅)
    have hinputs : (verdictRecord T interaction).events.map FirstHit.QueryEvent.input =
        SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1
          interaction.value) :=
      pureRecord_inputs T _ interaction.state
    have hv := refCharge_embed_le C (q - keygenCharge T - chargeSum interaction.events)
      (verdictRecord T interaction).events
    have hmap : (verdictRecord T interaction).events.map (fun event => embed event.input) =
        (SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1
          interaction.value)).map embed := by
      rw [← hinputs, List.map_map]
      rfl
    rw [hmap] at hv
    change (SeccLaw.classCharge C (q - keygenCharge T) interaction.events : ℝ≥0∞) +
        (refCharge C (q - keygenCharge T - chargeSum interaction.events) ((SourceReplay.queried T
          (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value)).map embed) : ℝ≥0∞) ≤
      (SeccLaw.classCharge C q ((pureRecord T keygen (∅, ∅)).events ++
        (interaction.events ++ (verdictRecord T interaction).events)) : ℝ≥0∞)
    rw [classCharge_append, classCharge_append, hk]
    exact_mod_cast (show _ ≤ _ by omega)
end Ref
theorem reference_trace_length (adversary : AdversaryP) (q : Nat) (sample : RefSample)
    (hs : sample ∈ (referenceExperiment adversary q).support) : sample.trace.length ≤ q := by
  unfold referenceExperiment at hs
  rw [MonitoredPrivate.pmf_support] at hs
  unfold referenceComp at hs
  rw [mem_support_bind_iff] at hs
  obtain ⟨privateTable, -, hs⟩ := hs
  rw [mem_support_bind_iff] at hs
  obtain ⟨publicTable, -, hs⟩ := hs
  rw [support_map] at hs
  obtain ⟨run, hrun, hsample⟩ := hs
  have htrace : sample.trace = traceOf (eagerAnswers (referenceInputs adversary) privateTable publicTable) run.2 := by
    rw [← hsample]
  rw [htrace]
  exact (Ref.traceOf_length_le _ run.2).trans (Ref.offlineRun_calls_le _ adversary q run hrun)
theorem completed_eager_map (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq =
      (fun x => (x.1, Ref.cut x.1.state x.2)) <$> eagerRecorded adversary := by
  apply PMF.ext
  intro y
  rw [← PMF.probOutput_eq_apply, ← PMF.probOutput_eq_apply, ← probEvent_eq_eq_probOutput,
    ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
  exact completed_eager_cut adversary q hq (fun rec A => (rec, A) = y)
theorem reference_count_le (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (cls : Answers → T3.Spec.Domain → Prop) (hcls : ShortCongruent cls) :
    ∑' s, referenceExperiment adversary q s * (refCount cls s : ENNReal) ≤
      SeccLaw.expectedCharge adversary q hq (fun z input => cls z.2 input) := by
  unfold SeccLaw.expectedCharge SeccLaw.sampleCharge
  rw [pmf_tsum_eq_expectedValue, pmf_tsum_eq_expectedValue]
  have hR : expectedValue (SeccLaw.completedExperiment adversary q hq)
      (fun z => (SeccLaw.classCharge (fun input => cls z.2 input) q (QueryRecorded.recordedTrace z.1).events : ℝ≥0∞)) =
      expectedValue (eagerRecorded adversary) (fun x => (SeccLaw.classCharge (cls x.2) q x.1.events : ℝ≥0∞)) := by
    have h1 := congrArg (fun p => expectedValue p (fun y : FirstHit.Recorded Bool × Answers =>
      (SeccLaw.classCharge (cls y.2) q y.1.events : ℝ≥0∞))) (completed_eager_map adversary q hq)
    simp only [expectedValue_map] at h1
    rw [h1]
    congr 1
    funext x
    have hc : cls (Ref.cut x.1.state x.2) = cls x.2 :=
      funext fun input => propext (hcls _ _ (Ref.cut_shortAgree _ _) input)
    rw [hc]
  rw [hR]
  unfold referenceExperiment eagerRecorded
  rw [expectedValue_liftM, expectedValue_liftM]
  unfold referenceComp
  simp only [expectedValue_bind, expectedValue_map]
  apply expectedValue_mono
  intro privateTable
  apply expectedValue_mono
  intro publicTable
  refine le_trans (le_of_eq (expectedValue_congr_of_support ?_)) (Ref.table_count_le adversary q _ (cls _))
  intro run hrun
  rw [Ref.refCharge_eq_filter _ _ _ _ (Ref.offlineRun_calls_le _ _ _ run hrun)]
  rfl
theorem reference_shared_budget (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (A B C : Answers → T3.Spec.Domain → Prop) (D : SeccLaw.SampleClass)
    (hA : ShortCongruent A) (hB : ShortCongruent B) (hC : ShortCongruent C)
    (hAB : ∀ T input, ¬(A T input ∧ B T input)) (hAC : ∀ T input, ¬(A T input ∧ C T input))
    (hBC : ∀ T input, ¬(B T input ∧ C T input))
    (hAD : ∀ z input, ¬(A z.2 input ∧ D z input)) (hBD : ∀ z input, ¬(B z.2 input ∧ D z input))
    (hCD : ∀ z input, ¬(C z.2 input ∧ D z input)) :
    ∑' s, referenceExperiment adversary q s * (refCount A s : ENNReal) +
      ∑' s, referenceExperiment adversary q s * (refCount B s : ENNReal) +
      ∑' s, referenceExperiment adversary q s * (refCount C s : ENNReal) +
      SeccLaw.expectedCharge adversary q hq D ≤ q :=
  le_trans (add_le_add (add_le_add (add_le_add (reference_count_le adversary q hq A hA)
      (reference_count_le adversary q hq B hB)) (reference_count_le adversary q hq C hC)) le_rfl)
    (SeccLaw.expectedCharge_four_le adversary q hq _ _ _ D (fun z input => hAB z.2 input)
      (fun z input => hAC z.2 input) hAD (fun z input => hBC z.2 input) hBD hCD)
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinateF PairedOuter.GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsTransportCount : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsTransportCount : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace Ref
open SigGolfCandidate.T3.Security.Wots.Ref
theorem interaction_count_le (T : Answers) (published : T3.Cache) (C : T3.Spec.Domain → Prop) {α : Type}
    (program : OracleComp PairedOuter.LazyPrivate.Interaction α) (state : LazyPrivate.State) (budget : Nat)
    (weight : α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests → Nat → ℝ≥0∞) :
    expectedValue (simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (offlineInteraction T published program)))
        (fun run => (refCharge C budget run.2 : ℝ≥0∞) +
          weight run.1 (budget - SphincsSecurity.QueryCap.calls RefCharged run.2)) ≤
      expectedValue (fixedRecord T (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) program) state)
        (fun result => (SeccLaw.classCharge C budget result.events : ℝ≥0∞) +
          weight result.value (budget - chargeSum result.events)) := by
  induction program using OracleComp.inductionOn generalizing state budget weight with
  | pure value =>
      rw [offlineInteraction_pure, PairedOuter.FullGame.loggedWith_pure, fixedRecord_pure, SphincsSecurity.QueryCap.recorded_pure,
        simulateQ_pure, expectedValue_pure, expectedValue_pure]
      simp [SeccLaw.classCharge, cappedCount, SphincsSecurity.QueryCap.calls_nil]
  | query_bind input next ih =>
      rcases input with input | request
      · rw [PairedOuter.FullGame.loggedWith_world, offlineInteraction_world]
        change expectedValue (simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded
            (liftM (RefWorld.query (.inl input)) >>= fun answer => offlineInteraction T published (next answer)))) _ ≤
          expectedValue (fixedRecord T (liftM (T3.Spec.query (.inl input)) >>= fun answer =>
            PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) (next answer)) state) _
        rw [SphincsSecurity.QueryCap.recorded_query_bind, fixedRecord_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, expectedValue_bind, expectedValue_pure,
          expectedValue_map]
        rcases input with n | x
        · change expectedValue (liftM (unifSpec.query n) : ProbComp _) _ ≤
            expectedValue (liftM (unifSpec.query n) : ProbComp _) _
          apply expectedValue_mono
          intro answer
          simp only [refCharge_coin, calls_coin, classCharge_coin_mk, chargeSum_cons, queryCharge_coin,
            Nat.zero_add]
          exact ih answer _ budget weight
        · change expectedValue (pure (T (.inl (.inr x))) : ProbComp _) _ ≤
            expectedValue (pure (T (.inl (.inr x))) : ProbComp _) _
          rw [expectedValue_pure, expectedValue_pure]
          simp only [refCharge_hash, calls_hash, classCharge_public_mk, chargeSum_cons, queryCharge_public,
            Nat.cast_add, ← Nat.sub_sub, add_assoc]
          try simp only [expectedValue_const_add]
          exact add_le_add le_rfl (ih _ _ (budget - 1) weight)
      · rw [PairedOuter.FullGame.loggedWith_request, offlineInteraction_request]
        unfold offlineSign
        rw [bind_assoc]
        simp only [pure_bind]
        rw [recorded_bind, simulateQ_bind, ticks_recorded, pure_bind, recorded_map, fixedRecord_bind,
          fixedRecord_hashOnly T _ (authenticatedSign_hashOnly published request), pure_bind]
        simp only [simulateQ_bind, simulateQ_map, simulateQ_pure, expectedValue_bind, expectedValue_pure,
          expectedValue_map, fixedRecord_map]
        rw [pureRecord_value]
        have hcharge : chargeSum (pureRecord T (PairedOuter.FullGame.authenticatedSign published request) state).events =
            signCharge T published request :=
          pureRecord_charge T _ (authenticatedSign_hashOnly published request) state
        refine le_trans (le_of_eq ?_) (le_trans (ih (evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request))
          (pureRecord T (PairedOuter.FullGame.authenticatedSign published request) state).state
          (budget - signCharge T published request)
          (fun value rest => weight (value.1, ⟨request, evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request)⟩ ::
            value.2) rest)) ?_)
        · congr 1
          funext run
          rw [refCharge_append, calls_replicate_tick, refCharge_replicate_tick, calls_append, calls_replicate_tick,
            Nat.zero_add, Nat.sub_sub]
        · apply expectedValue_mono
          intro result
          rw [classCharge_append, chargeSum_append, hcharge, Nat.sub_sub]
          gcongr
          exact le_add_left le_rfl
theorem offlineRun_calls_le (T : Answers) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (run : Option (Bool × Nat) × List RefWorld.Domain) (hrun : run ∈ support (offlineRun T adversary q)) :
    SphincsSecurity.QueryCap.calls RefCharged run.2 ≤ q := by
  have hmem := SphincsSecurity.QueryCap.simulate_oracle_mem_support (refImpl T) _ run hrun
  exact SphincsSecurity.QueryCap.recorded_calls_le RefCharged _ (fun _ => q)
    (fun result hresult => SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q
      (SphincsSecurity.QueryCap.run_queryBound RefCharged _ q) result hresult) run hmem
theorem table_count_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (T : Answers) (C : T3.Spec.Domain → Prop) :
    expectedValue (offlineRun T adversary q) (fun run => (refCharge C q run.2 : ℝ≥0∞)) ≤
      expectedValue (fixedRecord T (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅))
        (fun result => (SeccLaw.classCharge C q result.events : ℝ≥0∞)) := by
  unfold offlineRun referenceGame
  rw [cap_cappedCount RefCharged (RefClass C) (refImpl T) (offlineGame T adversary) q]
  unfold offlineGame
  rw [recorded_bind, simulateQ_bind, ticks_recorded, pure_bind, recorded_bind, simulateQ_bind]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc]
  simp only [verdict_recorded_fixed T _ (PairedOuter.PaddedGame.verdict_public _ _), pure_bind]
  rw [expectedValue_bind]
  simp only [expectedValue_pure]
  rw [fixed_game_eq, expectedValue_map]
  unfold fixedInteraction
  refine le_trans (le_of_eq ?_) (le_trans (interaction_count_le T (evalWithAnswerFn T keygen).2 C
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) (pureRecord T keygen (∅, ∅)).state
    (q - keygenCharge T) (fun value rest => (refCharge C rest ((SourceReplay.queried T
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 value)).map embed) : ℝ≥0∞))) ?_)
  · congr 1
    funext run
    show (refCharge C q (List.replicate (keygenCharge T) (.inr ()) ++ (run.2 ++ List.map embed
      (SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 run.1)))) : ℝ≥0∞) = _
    rw [refCharge_append, refCharge_replicate_tick, calls_replicate_tick, refCharge_append, Nat.zero_add,
      Nat.cast_add]
  · apply expectedValue_mono
    intro interaction
    have hk : chargeSum (pureRecord T keygen (∅, ∅)).events = keygenCharge T :=
      pureRecord_charge T keygen SourceReplay.keygen_hashOnly (∅, ∅)
    have hinputs : (verdictRecord T interaction).events.map FirstHit.QueryEvent.input =
        SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1
          interaction.value) :=
      pureRecord_inputs T _ interaction.state
    have hv := refCharge_embed_le C (q - keygenCharge T - chargeSum interaction.events)
      (verdictRecord T interaction).events
    have hmap : (verdictRecord T interaction).events.map (fun event => embed event.input) =
        (SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1
          interaction.value)).map embed := by
      rw [← hinputs, List.map_map]
      rfl
    rw [hmap] at hv
    change (SeccLaw.classCharge C (q - keygenCharge T) interaction.events : ℝ≥0∞) +
        (refCharge C (q - keygenCharge T - chargeSum interaction.events) ((SourceReplay.queried T
          (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value)).map embed) : ℝ≥0∞) ≤
      (SeccLaw.classCharge C q ((pureRecord T keygen (∅, ∅)).events ++
        (interaction.events ++ (verdictRecord T interaction).events)) : ℝ≥0∞)
    rw [classCharge_append, classCharge_append, hk]
    exact_mod_cast (show _ ≤ _ by omega)
end Ref
theorem reference_trace_length (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (sample : RefSample)
    (hs : sample ∈ (referenceExperiment adversary q).support) : sample.trace.length ≤ q := by
  unfold referenceExperiment at hs
  rw [MonitoredPrivate.pmf_support] at hs
  unfold referenceComp at hs
  rw [mem_support_bind_iff] at hs
  obtain ⟨privateTable, -, hs⟩ := hs
  rw [mem_support_bind_iff] at hs
  obtain ⟨publicTable, -, hs⟩ := hs
  rw [support_map] at hs
  obtain ⟨run, hrun, hsample⟩ := hs
  have htrace : sample.trace = traceOf (eagerAnswers (referenceInputs adversary) privateTable publicTable) run.2 := by
    rw [← hsample]
  rw [htrace]
  exact (Ref.traceOf_length_le _ run.2).trans (Ref.offlineRun_calls_le _ adversary q run hrun)
theorem completed_eager_map (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> PairedSeccLaw.completedExperiment adversary q hq =
      (fun x => (x.1, Ref.cut x.1.state x.2)) <$> eagerRecorded adversary := by
  apply PMF.ext
  intro y
  rw [← PMF.probOutput_eq_apply, ← PMF.probOutput_eq_apply, ← probEvent_eq_eq_probOutput,
    ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
  exact completed_eager_cut adversary q hq (fun rec A => (rec, A) = y)
theorem reference_count_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (cls : Answers → T3.Spec.Domain → Prop) (hcls : ShortCongruent cls) :
    ∑' s, referenceExperiment adversary q s * (refCount cls s : ENNReal) ≤
      PairedSeccLaw.expectedCharge adversary q hq (fun z input => cls z.2 input) := by
  unfold PairedSeccLaw.expectedCharge PairedSeccLaw.sampleCharge
  rw [pmf_tsum_eq_expectedValue, pmf_tsum_eq_expectedValue]
  have hR : expectedValue (PairedSeccLaw.completedExperiment adversary q hq)
      (fun z => (SeccLaw.classCharge (fun input => cls z.2 input) q (QueryRecorded.recordedTrace z.1).events : ℝ≥0∞)) =
      expectedValue (eagerRecorded adversary) (fun x => (SeccLaw.classCharge (cls x.2) q x.1.events : ℝ≥0∞)) := by
    have h1 := congrArg (fun p => expectedValue p (fun y : FirstHit.Recorded Bool × Answers =>
      (SeccLaw.classCharge (cls y.2) q y.1.events : ℝ≥0∞))) (completed_eager_map adversary q hq)
    simp only [expectedValue_map] at h1
    rw [h1]
    congr 1
    funext x
    have hc : cls (Ref.cut x.1.state x.2) = cls x.2 :=
      funext fun input => propext (hcls _ _ (Ref.cut_shortAgree _ _) input)
    rw [hc]
  rw [hR]
  unfold referenceExperiment eagerRecorded
  rw [expectedValue_liftM, expectedValue_liftM]
  unfold referenceComp
  simp only [expectedValue_bind, expectedValue_map]
  apply expectedValue_mono
  intro privateTable
  apply expectedValue_mono
  intro publicTable
  refine le_trans (le_of_eq (expectedValue_congr_of_support ?_)) (Ref.table_count_le adversary q _ (cls _))
  intro run hrun
  rw [Ref.refCharge_eq_filter _ _ _ _ (Ref.offlineRun_calls_le _ _ _ run hrun)]
  rfl
theorem reference_shared_budget (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (A B C : Answers → T3.Spec.Domain → Prop) (D : PairedSeccLaw.SampleClass)
    (hA : ShortCongruent A) (hB : ShortCongruent B) (hC : ShortCongruent C)
    (hAB : ∀ T input, ¬(A T input ∧ B T input)) (hAC : ∀ T input, ¬(A T input ∧ C T input))
    (hBC : ∀ T input, ¬(B T input ∧ C T input))
    (hAD : ∀ z input, ¬(A z.2 input ∧ D z input)) (hBD : ∀ z input, ¬(B z.2 input ∧ D z input))
    (hCD : ∀ z input, ¬(C z.2 input ∧ D z input)) :
    ∑' s, referenceExperiment adversary q s * (refCount A s : ENNReal) +
      ∑' s, referenceExperiment adversary q s * (refCount B s : ENNReal) +
      ∑' s, referenceExperiment adversary q s * (refCount C s : ENNReal) +
      PairedSeccLaw.expectedCharge adversary q hq D ≤ q :=
  le_trans (add_le_add (add_le_add (add_le_add (reference_count_le adversary q hq A hA)
      (reference_count_le adversary q hq B hB)) (reference_count_le adversary q hq C hC)) le_rfl)
    (PairedSeccLaw.expectedCharge_four_le adversary q hq _ _ _ D (fun z input => hAB z.2 input)
      (fun z input => hAC z.2 input) hAD (fun z input => hBC z.2 input) hBD hCD)
end ClaudeWCT.W9.T3.Security.Wots.PairedReference
end
-- ==== merged from T3_Secc_WotsTwoEdge ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
def PrefixRow (answers : Answers) : T3.Spec.Domain → Prop
  | .inl (.inr input) => ∃ a, WotsExtract.SourceChain a ∧ PrefixRowAt answers a input
  | _ => False
@[irreducible] noncomputable def sourceChains : Finset ChainAddr :=
  (Finset.univ : Finset Layer).biUnion fun lay => (Finset.range (2 ^ 31)).biUnion fun tree =>
    (Finset.range (2 ^ height lay)).biUnion fun leaf =>
      (Finset.range (chainCount lay)).image fun chain => (⟨⟨lay, tree, leaf⟩, chain⟩ : ChainAddr)
theorem height_le (lay : Layer) : height lay ≤ 12 := by
  fin_cases lay <;> decide
theorem mem_sourceChains (a : ChainAddr) : a ∈ sourceChains ↔ WotsExtract.SourceChain a := by
  unfold sourceChains
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨lay, tree, htree, leaf, hleaf, chain, hchain, rfl⟩
    exact ⟨⟨htree, hleaf⟩, hchain⟩
  · intro ha
    exact ⟨a.key.lay, a.key.tree, ha.1.1, a.key.leaf, ha.1.2, a.chain, ha.2, rfl⟩
noncomputable def twoEdgeRate (q : Nat) : ENNReal :=
  ((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) + 2 * ((q : ENNReal) / 2 ^ 128) ^ 2) / 2 ^ 128
theorem card_digest : ((Fintype.card Digest : ℕ) : ENNReal) = 2 ^ 128 := by
  rw [Fintype.card_bitVec]
  norm_num
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsClasses ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallA
theorem hdrBlock_chainRow (a : ChainAddr) (s : Nat) (v : Digest) :
    Extract.hdrBlock (chainRow a s v) =
      bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) :=
  chainInput_header _ _ _ _ _ _
theorem hdrBlock_digest (rho : Digest) (m : Message) (c : BitVec 32) :
    Extract.hdrBlock (pad64 (digestInput rho m c)) = bytesLE 16 (digestHeader c) := by
  unfold digestInput
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), Extract.hdrBlock_prefix]
theorem chainRow_ne_digest (a : ChainAddr) (s : Nat) (v : Digest) (rho : Digest) (m : Message) (c : BitVec 32) :
    chainRow a s v ≠ pad64 (digestInput rho m c) := by
  intro h
  have hb := congrArg Extract.hdrBlock h
  rw [hdrBlock_chainRow, hdrBlock_digest] at hb
  exact chainHeader_ne_digestHeader _ _ _ _ _ _ (bytesLE_injective hb)
theorem sourceChain_bounds {a : ChainAddr} (ha : WotsExtract.SourceChain a) :
    a.key.tree < 2 ^ 31 ∧ a.key.leaf < 4096 ∧ a.chain < 64 := by
  obtain ⟨⟨ht, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 2 ^ 12 :=
    Nat.pow_le_pow_right (by norm_num) (by have := height_le a.key.lay; omega)
  have hcc := Mask.chainCount_le a.key.lay
  refine ⟨by omega, by omega, by omega⟩
end SmallA
open SmallA
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_LargeCouplingQuery ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingQuery : DecidableEq T3.Cache := Classical.decEq _
noncomputable def routerLabels (vals : Coord → Digest) (a : AuxData) : Labels :=
  joinLabels (fun N => vals (.inl N)) a.high
def HonestPrefix (vals : Coord → Digest) (a : AuxData) (X : HashInput) : Prop :=
  ∃ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr ∧ PrefixRow a L ctr
structure Coherent (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) : Prop where
  agrees : Agrees T (routerLabels vals a)
  secrets : secretsOf T = fun s => vals (.inr s)
  residual : ∀ (X : HashInput) (hX : X ∈ U), (∀ N : CanonGraph.Node, X ≠ cell (secretsOf T) N (routerLabels vals a)) →
    ¬HonestPrefix vals a X → T (.inl (.inr X)) = τ ⟨X, hX⟩
  prefixRow : ∀ (L : EncLeaf) (ctr : BitVec 32), PrefixRow a L ctr →
    T (.inl (.inr (Wots.encodingRow L.toWots (vals (msgCoord L)) ctr))) = prefixValue a L ctr
  search : ∀ L : EncLeaf, Wots.referenceSearch T L.toWots =
    (a.sel L).bind fun r => (decode L.1.lay r.2).map fun d => (BitVec.ofNat 32 r.1.val, d)
  priv : ∀ c : Coordinate, (∀ i : Fin 2, (c, i) ∉ Set.range secretCoordinate) → (∀ m : Message, c ≠ .inr (.inl m)) →
    T (.inr c) = a.priv c
  outside : ∀ X, X ∉ U → T (.inl (.inr X)) = (0 : HashOutput)
  nonce : ∀ m : Message, (T (.inr (.inr (.inl m)))).extractLsb' 0 128 = nv m
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
end Coherent
theorem low_eq (y : HashOutput) : low y = y.extractLsb' 0 128 := rfl
theorem dummyDigest_decode' (lay : Layer) : decode lay (dummyDigest lay) = some (Wots.dummyDigits lay) :=
  Classical.choose_spec (Wots.dummyDigits_valid lay)
section Reference
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
theorem Coherent.referenceDigits (h : Coherent U T vals nv τ a) (L : EncLeaf) :
    Wots.referenceDigits T L.toWots = ((a.sel L).bind fun r => decode L.1.lay r.2).getD (Wots.dummyDigits L.1.lay) := by
  unfold Wots.referenceDigits
  rw [h.search]
  cases hs : a.sel L with
  | none => rfl
  | some r =>
      simp only [Option.bind_some]
      cases decode L.1.lay r.2 <;> rfl
end Reference
section Relation
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
end Relation
section Query
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem keep_guess_label {C : Type} (vals : C → Digest) (c p : C) (m : Digest) (y : HashOutput) :
    (⟨some (c, m), .label p⟩ : Probe C).keep vals y ↔ vals c ≠ m ∧ vals p ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]
theorem keep_label {C : Type} (vals : C → Digest) (p : C) (y : HashOutput) :
    (⟨none, .label p⟩ : Probe C).keep vals y ↔ vals p ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]
theorem keep_target {C : Type} (vals : C → Digest) (t : Digest) (y : HashOutput) :
    (⟨none, .target t⟩ : Probe C).keep vals y ↔ t ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]
theorem keep_guess_target {C : Type} (vals : C → Digest) (c : C) (m t : Digest) (y : HashOutput) :
    (⟨some (c, m), .target t⟩ : Probe C).keep vals y ↔ vals c ≠ m ∧ t ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]
end Query
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem lookupVal_map (f : Coord → Digest) (cs : List Coord) (c : Coord) (hc : c ∈ cs) :
    lookupVal (cs.map fun c => (c, f c)) c = f c := by
  induction cs with
  | nil => cases hc
  | cons d rest ih =>
      unfold lookupVal
      simp only [List.map_cons, List.find?_cons]
      by_cases hd : d = c
      · subst hd
        simp
      · simp only [hd, decide_false]
        exact ih ((List.mem_cons.mp hc).resolve_left (Ne.symm hd))
end Cases
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeCouplingQuery ====
section

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue IsDigestRow dummyDigest State Probe Hit Charge Cell
  readState probeState stoppedState tickState disclosedState runWith_map mem_restrict card_restrict_ge low)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure effF_self adm_of_plain Adm famKnown famSeeds
  mem_famSeeds mem_famKnown)
open SigGolfCandidate.T3.Security.LargeCoupling (low_eq keep_guess_label keep_label keep_target
  keep_guess_target dummyDigest_decode')
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingQuery : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
/-- Local copy of `Wots.SmallA.encRow_ne_digest` (WotsClasses), so the large route does not import the small
route's `WotsTwoEdge`. -/
theorem encRow_ne_digest' (L : Wots.LeafAddr) (m : WCT9.LayerMsg) (c : BitVec 32) (pad : Wots.RowPad) (rho : Digest)
    (m' : Message) (c' : BitVec 32) : Wots.encRow L m c pad ≠ pad64 (digestInput rho m' c') := by
  intro h
  have hb := congrArg ClaudeWCT.W9.T3M.Extract.hdrBlock h
  have h2 : ClaudeWCT.W9.T3M.Extract.hdrBlock (pad64 (digestInput rho m' c')) =
      bytesLE 16 (digestHeader c') :=
    SigGolfCandidate.T3.Security.Wots.SmallA.hdrBlock_digest rho m' c'
  rw [h2, show Wots.encRow L m c pad = pad64 (layerEncodingInputP L.lay L.tree L.leaf m c pad.1 pad.2.1 (pad.2.2 ^^^ 1)) from rfl,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP] at hb
  have hm := congrArg tweakMarker (bytesLE_injective hb)
  unfold WCT9.rowTweakW at hm
  rw [append64_marker, hyperWord_marker, digestHeader_marker] at hm
  exact absurd hm (by decide)
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
end Coherent
theorem encodingRow_parsed_none (L : Wots.LeafAddr) (m : WCT9.LayerMsg) (c : BitVec 32) (pad : Wots.RowPad) :
    Extract.posOf (Wots.encRow L m c pad) = none :=
  Wots.Structural.posOf_layerEncodingP _ _ _ _ _ _ _ _
theorem digestRow_parsed_none {X : HashInput} (h : IsDigestRow X) : Extract.posOf X = none := by
  obtain ⟨rho, m, c, rfl⟩ := h
  exact Wots.Structural.posOf_digest _ _ _
theorem not_parsed_of_digest {X : HashInput} (h : IsDigestRow X) : ¬Parsed X := by
  rintro ⟨N, hN⟩
  rw [digestRow_parsed_none h] at hN
  cases hN
theorem not_parsed_of_encRow {X : HashInput} (h : EncRow X) : ¬Parsed X := by
  rintro ⟨N, hN⟩
  obtain ⟨L, m, c, pad, -, rfl⟩ := h
  rw [encodingRow_parsed_none] at hN
  cases hN
theorem encRow_encLeaf {L L' : EncLeaf} {m m' : WCT9.LayerMsg} {c c' : BitVec 32} {pad pad' : Wots.RowPad}
    (h : Wots.encRow L.toWots m c pad = Wots.encRow L'.toWots m' c' pad') : L = L' ∧ c = c' := by
  obtain ⟨⟨lay, tree, leaf⟩, hs⟩ := L
  obtain ⟨⟨lay', tree', leaf'⟩, hs'⟩ := L'
  obtain ⟨h1, h2, h3, h4⟩ := ClaudeWCT.W9.T3M.BC.layerEncodingRow_coords hs.routed.1 hs.routed.2
    hs'.routed.1 hs'.routed.2 h
  refine ⟨?_, h4⟩
  subst h1
  have e2 : tree = tree' := Fin.ext h2
  have e3 : leaf = leaf' := Fin.ext h3
  subst e2 e3
  rfl
theorem msgFits_msgVals (v : Coord → Digest) (L : EncLeaf) : Extract.msgFits L.1.lay (msgVals v L) := by
  unfold msgVals
  split_ifs <;> trivial
theorem msgVals_congr (v w : Coord → Digest) (L : EncLeaf) (h : ∀ cs ∈ msgSlots L, v cs.1 = w cs.1) :
    msgVals v L = msgVals w L := by
  unfold msgVals
  unfold msgSlots at h
  split_ifs with hl
  · rw [dif_pos hl] at h
    rw [h _ List.mem_cons_self, h _ (List.mem_cons_of_mem _ List.mem_cons_self)]
  · rw [dif_neg hl] at h
    rw [h _ List.mem_cons_self, h _ (List.mem_cons_of_mem _ List.mem_cons_self)]
section Reference
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
end Reference
section Relation
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
end Relation
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.RouterState.next_of_not (U : Finset HashInput) (st : RouterState) (X : HashInput) (y : HashOutput)
    (h : ¬(X ∈ U ∧ IsDigestRow X)) : st.next U X y = st.after X := by
  unfold RouterState.next
  rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]
section Query
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
end Query
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.RouterState.next_disclosed (U : Finset HashInput)
    (st : RouterState) (X : HashInput) (y : HashOutput) : (st.next U X y).disclosed = st.disclosed := by
  unfold RouterState.next RouterState.after
  split_ifs <;> rfl
theorem encRow_not_digest (L : EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32) (pad : Wots.RowPad) :
    ¬IsDigestRow (Wots.encRow L.toWots m ctr pad) := by
  rintro ⟨rho, m', c, h⟩
  exact encRow_ne_digest' _ _ _ _ _ _ _ h
end Cases
end ClaudeWCT.W9.T3.Security.LargeCoupling

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def routerLabels (vals : Coord → Digest) (a : AuxData) : Labels :=
  CanonGraph.Paired.joinLabels (fun N => vals (.inl N)) a.high

def HonestPrefix (vals : Coord → Digest) (a : AuxData) (X : HashInput) : Prop :=
  ∃(L : CanonEncoding.EncLeaf)(ctr : BitVec 32),X=Wots.encRow L.toWots (msgVals vals L) ctr 0 ∧ PrefixRow a L ctr

structure Coherent (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) : Prop where
  agrees : CanonGraph.Paired.Filtered.Agrees T (routerLabels vals a)
  secrets : seedView (secretsOf T)=fun s => vals (.inr s)
  residual : ∀(X : HashInput)(hX : X∈U),
    (∀N : CanonGraph.Node,CanonGraph.Paired.Filtered.Used N → X≠CanonGraph.Paired.cell (secretsOf T) N (routerLabels vals a)) →
    ¬HonestPrefix vals a X → T (.inl (.inr X))=rowPresent X (τ ⟨X,hX⟩)
  prefixRow : ∀(L : CanonEncoding.EncLeaf)(ctr : BitVec 32),PrefixRow a L ctr →
    T (.inl (.inr (Wots.encRow L.toWots (msgVals vals L) ctr 0)))=prefixValue a L ctr
  search : ∀L : CanonEncoding.EncLeaf,
    Wots.CanonicalRef.referenceSearch T (Wots.CanonicalRef.sourceMessages T) L.toWots =
      (a.sel L).bind fun r => (WCT9.CanonicalPolicy.decode L.1.lay r.2).map fun d =>
        (BitVec.ofNat 32 r.1.val,d,WCT9.lowSelected L.1.lay (a.rows L r.1))
  priv : ∀c : Coordinate,(∀i : Fin 2,(c,i)∉Set.range secretCoordinate) → (∀m : Message,c≠.inr (.inl m)) →
    T (.inr c)=a.priv c
  outside : ∀X,X∉U → T (.inl (.inr X))=(0 : HashOutput)
  nonce : ∀m : Message,(T (.inr (.inr (.inl m)))).extractLsb' 0 128=nv m
  selected : a.sel=CanonEncoding.Paired.selectionsOfRows a.rows
  /-- Top-nonce layer: no top position exhausted its trial cap (`CapFail`, probability ≤ 2^-142). -/
  capOk : ¬ CanonGraph.CapFail (routerLabels vals a)

/-! ### Top-nonce layer helpers (r3-lean-nonsec, Subagent L) -/
theorem presentEquiv_base (M : CanonGraph.Node) :
    CanonGraph.Paired.presentEquiv M.base = CanonGraph.Paired.presentEquiv M := by
  cases M <;> rfl
theorem presentEquiv_toPos {M N : CanonGraph.Node} (h : M.toPos = N.toPos) :
    CanonGraph.Paired.presentEquiv M = CanonGraph.Paired.presentEquiv N := by
  rw [← presentEquiv_base M, ← presentEquiv_base N, CanonGraph.toPos_injective_base h]
/-- The node is not an over-cap tree node (`nonce ≥ trialCap`, a structural phantom with no slots). -/
def NoOver (M : CanonGraph.Node) : Prop := ∀ m, M = .node m → m.1.nonce.val < trialCap m.1.lay m.1.level.val
theorem noOver_of_not_phantom {L : Labels} {M : CanonGraph.Node} (h : ¬ PhantomAt M L) : NoOver M := by
  intro m hm
  subst hm
  by_contra hc
  exact h ⟨m, rfl, fun ha => hc ha.1⟩
theorem noOver_base (M : CanonGraph.Node) : NoOver M.base := by
  intro m hm
  cases M with
  | node n =>
    cases hm
    have := trialCap_pos n.1.lay n.1.level.val
    simp only [withNonce_lay, withNonce_level]
    rw [withNonce_nonce n (by norm_num)]
    exact this
  | _ => cases hm
theorem childSlots_base_of {M : CanonGraph.Node} (hM : NoOver M) : childSlots M.base = childSlots M := by
  cases M with
  | node m =>
    have h1 := hM m rfl
    have h0 := trialCap_pos m.1.lay m.1.level.val
    show LargeResidual.childSlots (.node (withNonce m 0)) = LargeResidual.childSlots (.node m)
    simp only [LargeResidual.childSlots]
    rw [if_neg (by simp only [withNonce_lay, withNonce_level]; rw [withNonce_nonce m (by norm_num)]; omega),
      if_neg (by omega)]
    rfl
  | _ => rfl
theorem childSlots_sub_base (M : CanonGraph.Node) : ∀ cs ∈ childSlots M, cs ∈ childSlots M.base := by
  intro cs hcs
  by_cases hM : NoOver M
  · rw [childSlots_base_of hM]; exact hcs
  · cases M with
    | node m =>
      have h1 : trialCap m.1.lay m.1.level.val ≤ m.1.nonce.val := by
        by_contra h; exact hM (fun m' hm' => by cases hm'; omega)
      change cs ∈ LargeResidual.childSlots (.node m) at hcs
      simp only [LargeResidual.childSlots] at hcs
      rw [if_pos h1] at hcs
      cases hcs
    | _ => exact hcs
theorem childSlots_eq_of {M N : CanonGraph.Node} (h : M.toPos = N.toPos) (hM : NoOver M) (hN : NoOver N) :
    childSlots M = childSlots N := by
  rw [← childSlots_base_of hM, ← childSlots_base_of hN, CanonGraph.toPos_injective_base h]
theorem cellDepsP_sub_base (M : CanonGraph.Node) : ∀ c ∈ cellDepsP M, c ∈ cellDepsP M.base := by
  intro c hc
  cases M with
  | node m =>
    change c ∈ LargeResidual.cellDeps (.node m) at hc
    change c ∈ LargeResidual.cellDeps (.node (withNonce m 0))
    unfold LargeResidual.cellDeps at hc ⊢
    simp only [List.mem_append] at hc ⊢
    rcases hc with ((hc | hc) | hc) | hc
    · obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc
      exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨cs, childSlots_sub_base (.node m) cs hcs, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr hc))
    · exact Or.inl (Or.inr hc)
    · exact Or.inr hc
  | _ => exact hc
theorem cellDepsP_sub {M N : CanonGraph.Node} (h : M.toPos = N.toPos) (hN : N.base = N) :
    ∀ c ∈ cellDepsP M, c ∈ cellDepsP N := by
  intro c hc
  have := cellDepsP_sub_base M c hc
  rwa [CanonGraph.toPos_injective_base h, hN] at this
theorem used_base {M : CanonGraph.Node} (hu : CanonGraph.Paired.Filtered.Used M) :
    CanonGraph.Paired.Filtered.Used M.base := by
  cases M <;> exact hu
theorem lay_zero_of_cap {lay : Layer} {level : Nat} (h : trialCap lay level ≠ 1) : lay = 0 := by
  unfold trialCap at h
  split_ifs at h with h'
  · exact h'.1
  · exact absurd rfl h
theorem treeNodeAt_spec {lay : Layer} {tree : Fin (2^31)} {level c : Nat} {m : TreeNode}
    (h : treeNodeAt lay tree level c = some m) :
    m.1.lay = lay ∧ m.1.tree = tree ∧ m.1.level.val = level ∧ m.1.idx.val = c ∧ m.1.nonce.val = 0 := by
  unfold treeNodeAt at h
  split_ifs at h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩
/-- A tree-node child coordinate of a slot list belongs to a tree node of the same layer and has nonce 0. -/
theorem childSlots_node_child {N : CanonGraph.Node} {cs : Coord × Nat} (hc : cs ∈ childSlots N) {m : TreeNode}
    (hm : cs.1 = .inl (.node m)) :
    ∃ n, N = .node n ∧ m.1.lay = n.1.lay ∧ m.1.level.val + 1 = n.1.level.val ∧ m.1.nonce.val = 0 := by
  obtain ⟨c, b⟩ := cs
  simp only at hm
  subst hm
  cases N with
  | node n =>
    refine ⟨n, rfl, ?_⟩
    simp only [childSlots, LargeResidual.childSlots] at hc
    split_ifs at hc
    · cases hc
    simp only [List.mem_append, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hc
    rcases hc with ⟨x, hx, hxe, -⟩ | ⟨x, hx, hxe, -⟩ <;> subst hxe <;>
    · unfold treeChild at hx
      split_ifs at hx with h0
      · simp at hx
      · simp only [Option.map_eq_some_iff, Sum.inl.injEq, CanonGraph.Node.node.injEq] at hx
        obtain ⟨m', hm', rfl⟩ := hx
        obtain ⟨h1, -, h3, -, h5⟩ := treeNodeAt_spec hm'
        exact ⟨h1, by omega, h5⟩
  | chain p =>
    simp only [childSlots, LargeResidual.childSlots, List.mem_singleton, Prod.mk.injEq] at hc
    unfold chainChild at hc
    split_ifs at hc <;> simp at hc
  | leaf L =>
    simp only [childSlots, LargeResidual.childSlots, List.mem_map, Prod.mk.injEq] at hc
    obtain ⟨i, -, h, -⟩ := hc
    simp at h
  | wctChain p =>
    simp only [childSlots, LargeResidual.childSlots, List.mem_singleton, Prod.mk.injEq] at hc
    have := hc.1
    unfold wctItem at this
    split_ifs at this <;> simp at this
  | wctLeaf L =>
    simp only [childSlots, List.mem_append, List.mem_ofFn, Option.mem_toList, Option.map_eq_some_iff,
      Prod.mk.injEq] at hc
    rcases hc with ⟨t, ht⟩ | ⟨x, hx, hxe, -⟩
    · have := ht.1
      unfold wctItem at this
      split_ifs at this <;> simp at this
    · subst hxe
      unfold padCoord ftsChild at hx
      split_ifs at hx <;> simp at hx
  | wctNode n =>
    simp only [childSlots, List.mem_append, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hc
    rcases hc with (⟨x, hx, hxe, -⟩ | ⟨x, hx, hxe, -⟩) | hc
    · subst hxe; unfold ftsChild at hx; split_ifs at hx <;> simp at hx
    · subst hxe; unfold ftsChild at hx; split_ifs at hx <;> simp at hx
    · split_ifs at hc
      · simp only [Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hc
        obtain ⟨x, hx, hxe, -⟩ := hc
        subst hxe; unfold padCoord ftsChild at hx; split_ifs at hx <;> simp at hx
      · simp at hc
  | forest index =>
    simp only [childSlots, LargeResidual.childSlots, List.mem_flatMap, List.mem_cons, List.mem_range,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hc
    obtain ⟨i, -, h | h⟩ := hc <;> simp at h
theorem selCoordV_self_of {v : Coord → Digest} {c : Coord}
    (h : ∀ m : TreeNode, c = .inl (.node m) → trialCap m.1.lay m.1.level.val = 1 ∧ m.1.nonce.val = 0) :
    selCoordV v c = c := by
  rcases c with (_ | _ | m | _ | _ | _ | _) | s
  all_goals try rfl
  obtain ⟨h1, h0⟩ := h m rfl
  show Sum.inl (CanonGraph.Node.node (withNonce m (selNonceV v m))) = _
  rw [selNonceV_cap_one h1]
  have hw := withNonce_self m
  rw [h0] at hw
  rw [hw]
/-- Off the top tree, child slots are their own selected trials. -/
theorem selCoordV_child {v : Coord → Digest} {N : CanonGraph.Node}
    (hN : ∀ n, N = .node n → n.1.lay ≠ 0) {cs : Coord × Nat} (hc : cs ∈ childSlots N) :
    selCoordV v cs.1 = cs.1 := by
  apply selCoordV_self_of
  intro m hm
  obtain ⟨n, rfl, hl, -, h0⟩ := childSlots_node_child hc hm
  exact ⟨trialCap_lower (hl ▸ hN n rfl) _, h0⟩
/-- A node of a single-trial position equal to its base representative is its position's selected trial. -/
theorem sel_of_single {L : Labels} {N : CanonGraph.Node} (hb : N.base = N)
    (hN : ∀ n, N = .node n → trialCap n.1.lay n.1.level.val = 1) : N.sel L = N := by
  cases N with
  | node n =>
    have h0 : n.1.nonce.val = 0 := by
      have := congrArg (fun M => match M with | CanonGraph.Node.node m => m.1.nonce.val | _ => 0) hb
      simpa [CanonGraph.Node.base, withNonce] using this.symm
    exact congrArg CanonGraph.Node.node (selNode_of_cap_one (hN n rfl) h0)
  | _ => rfl
/-- Two non-phantom nodes of one single-trial position coincide (with the base representative). -/
theorem eq_of_single {L : Labels} {M N : CanonGraph.Node} (hb : N.base = N)
    (hN : ∀ n, N = .node n → trialCap n.1.lay n.1.level.val = 1) (hM : M.toPos = N.toPos)
    (hnp : ¬ PhantomAt M L) : M = N := by
  have hbase := CanonGraph.toPos_injective_base hM
  rw [hb] at hbase
  cases M with
  | node m =>
    subst hbase
    have ha : Active L m := by by_contra ha; exact hnp ⟨m, rfl, ha⟩
    have hcap := hN _ rfl
    have h0 : m.1.nonce.val = 0 := by
      have := ha.1
      simp only [CanonGraph.Node.base, withNonce_lay, withNonce_level] at hcap
      omega
    show CanonGraph.Node.node m = CanonGraph.Node.node (withNonce m 0)
    have hw := withNonce_self m
    rw [h0] at hw
    rw [hw]
  | _ => exact hbase
/-- Top-tree child slots are keygen coordinates. -/
theorem top_childSlots_keygen {n : TreeNode} (hl : n.1.lay = 0) {cs : Coord × Nat}
    (hc : cs ∈ childSlots (.node n)) : cs.1 ∈ keygenDisclosed := by
  have hv : n.1.level.val < height n.1.lay ∧ n.1.idx.val < 2 ^ (height n.1.lay - n.1.level.val - 1) ∧
      n.1.tree.val < 2 ^ treeBits n.1.lay ∧ (n.1.lay = 0 ∨ n.1.level.val + 1 < height n.1.lay) := n.2
  rw [hl] at hv
  have ht : n.1.tree = 0 := Fin.ext (by simpa [treeBits] using hv.2.2.1)
  have hh : height 0 = 12 := rfl
  rw [hh] at hv
  obtain ⟨c, b⟩ := cs
  simp only [childSlots, LargeResidual.childSlots] at hc
  split_ifs at hc
  · cases hc
  simp only [List.mem_append, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hc
  have key : ∀ k, k < 2 ^ (12 - n.1.level.val) → ∀ x, treeChild 0 0 n.1.level.val k = some x →
      x ∈ keygenDisclosed := by
    intro k hk x hx
    apply List.mem_append_left
    apply List.mem_append_left
    unfold keygenCacheDisclosed
    simp only [List.mem_flatMap, List.mem_range'_1, List.mem_filterMap, List.mem_range]
    exact ⟨n.1.level.val, ⟨by omega, by omega⟩, k, hk, hx⟩
  have hpow : 2 ^ (12 - n.1.level.val) = 2 * 2 ^ (12 - n.1.level.val - 1) := by
    rw [← pow_succ']; congr 1; omega
  rcases hc with ⟨x, hx, rfl, -⟩ | ⟨x, hx, rfl, -⟩
  · rw [hl, ht] at hx; exact key _ (by omega) x hx
  · rw [hl, ht] at hx; exact key _ (by omega) x hx
theorem nonce_zero_of_base {n : TreeNode} (h : (CanonGraph.Node.node n).base = .node n) : n.1.nonce.val = 0 := by
  have := congrArg (fun M => match M with | CanonGraph.Node.node m => m.1.nonce.val | _ => 0) h
  simp only [CanonGraph.Node.base] at this
  rw [← this, withNonce_nonce n (by norm_num)]
theorem base_base (M : CanonGraph.Node) : M.base.base = M.base := by
  cases M <;> rfl
theorem trialDeps_keygen {n : TreeNode} {c : Coord} (hc : c ∈ trialDeps n) : c ∈ keygenDisclosed := by
  unfold trialDeps at hc
  split_ifs at hc with h1
  · simp at hc
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    exact trialCoord_mem_keygen (lay_zero_of_cap h1) h1 (List.mem_range.mp hj)
theorem childTrialDeps_keygen {lay : Layer} {tree : Fin (2^31)} {level k : Nat} {c : Coord}
    (hc : c ∈ childTrialDeps lay tree level k) : c ∈ keygenDisclosed := by
  unfold childTrialDeps at hc
  split at hc
  · exact trialDeps_keygen hc
  · simp at hc
theorem cellDepsP_known (st : RouterState) {N : CanonGraph.Node}
    (hall : ∀ cs ∈ childSlots N, RouterState.known st cs.1) : ∀ c ∈ cellDepsP N, RouterState.known st c := by
  intro c hc
  cases N with
  | node n =>
    simp only [cellDepsP, LargeResidual.cellDeps, List.mem_append] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc; exact hall cs hcs
    · exact Known.base (Or.inl (trialDeps_keygen hc))
    · exact Known.base (Or.inl (childTrialDeps_keygen hc))
    · exact Known.base (Or.inl (childTrialDeps_keygen hc))
  | _ => obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc; exact hall cs hcs
theorem ne_phantom_of_length {X : HashInput} (h : X.length = 64) : ∀ n, X ≠ phantom n := by
  intro n hX
  have := phantom_length n
  rw [← hX, h] at this
  exact absurd this (by decide)

theorem rowPresent_parsed {X : HashInput} {N : CanonGraph.Node}
    (hu : CanonGraph.Paired.Filtered.Used N) (hN : Extract.posOf X=some N.toPos) :
    rowPresent X=CanonGraph.Paired.presentEquiv N := by
  have hp : Parsed X := ⟨N,hu,hN⟩
  unfold rowPresent
  rw [dif_pos hp]
  have hc := (Classical.choose_spec hp).2
  exact presentEquiv_toPos (Option.some.inj (hc.symm.trans hN))

theorem proj_rowPresent {X : HashInput} {N : CanonGraph.Node}
    (hu : CanonGraph.Paired.Filtered.Used N) (hN : Extract.posOf X=some N.toPos) (y : HashOutput) :
    Extract.Paired.proj N.toPos (rowPresent X y)=y.extractLsb' 0 128 := by
  rw [rowPresent_parsed hu hN]
  exact CanonGraph.Paired.proj_presentEquiv N y

theorem rowPresent_unparsed {X : HashInput} (hp : ¬Parsed X) (y : HashOutput) : rowPresent X y=y := by
  unfold rowPresent
  rw [dif_neg hp]
  rfl

section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}

theorem Coherent.coordVal (h : Coherent U T vals nv τ a) : coordVal (secretsOf T) (routerLabels vals a)=vals := by
  funext c
  cases c with
  | inl N => exact CanonGraph.Paired.joinLabels_val _ _ N
  | inr s => exact congrFun h.secrets s

theorem selCoordV_coordVal_sel (s : Secrets) (L : Labels) (N : CanonGraph.Node) :
    selCoordV (coordVal s L) (.inl N) = .inl (N.sel L) := by
  cases N with
  | node n =>
    show Sum.inl (CanonGraph.Node.node (withNonce n (selNonceV (coordVal s L) n))) = _
    rw [selNonceV_coordVal]
    rfl
  | _ => rfl

theorem Coherent.selCoord (h : Coherent U T vals nv τ a) (N : CanonGraph.Node) :
    selCoordV vals (.inl N) = .inl (N.sel (routerLabels vals a)) := by
  have := selCoordV_coordVal_sel (secretsOf T) (routerLabels vals a) N
  rwa [h.coordVal] at this

/-- Top-nonce layer: the honest input of a position is the cell of its selected trial. -/
theorem Coherent.honestInput (h : Coherent U T vals nv τ a) (N : CanonGraph.Node)
    (hu : CanonGraph.Paired.Filtered.Used N) :
    Extract.Paired.honestInput T N.toPos=cellValues (N.sel (routerLabels vals a)) vals := by
  have hb := (CanonGraph.Paired.Filtered.used_iff_bounded N).1 hu
  rw [CanonGraph.Paired.Filtered.honestInput_eq T (routerLabels vals a) h.agrees N hb,
    cell_eq_cellValues _ _ _ (CanonGraph.Paired.Filtered.used_sel _ N hb),h.coordVal]

theorem Coherent.honestValue_sel (h : Coherent U T vals nv τ a) (N : CanonGraph.Node)
    (hu : CanonGraph.Paired.Filtered.Used N) :
    honestValue T (.inl N)=Extract.Paired.proj N.toPos (routerLabels vals a (N.sel (routerLabels vals a))) := by
  change Extract.Paired.proj N.toPos (T (.inl (.inr (Extract.Paired.honestInput T N.toPos))))=_
  rw [CanonGraph.Paired.Filtered.honest_answer T (routerLabels vals a) h.agrees N
    ((CanonGraph.Paired.Filtered.used_iff_bounded N).1 hu)]

/-- Top-nonce layer: the honest value of a position is the value of its selected trial. -/
theorem Coherent.honestValue_node (h : Coherent U T vals nv τ a) (N : CanonGraph.Node)
    (hu : CanonGraph.Paired.Filtered.Used N) : honestValue T (.inl N)=vals (selCoordV vals (.inl N)) := by
  rw [h.honestValue_sel N hu, h.selCoord N, ← CanonGraph.toPos_sel (routerLabels vals a) N]
  exact CanonGraph.Paired.joinLabels_val _ _ _

theorem Coherent.honestValue_seed (h : Coherent U T vals nv τ a) (s : SeedIndex) :
    honestValue T (.inr s)=vals (.inr s) := congrFun h.secrets s
end Coherent
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (slotValue)
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem treeChild_ne_self (n : TreeNode) (c : Nat) :
    treeChild n.1.lay n.1.tree n.1.level.val c ≠ some (.inl (.node n)) := by
  intro h
  unfold treeChild at h
  split_ifs at h with h0
  · simp at h
  · simp only [Option.map_eq_some_iff, Sum.inl.injEq, CanonGraph.Node.node.injEq] at h
    obtain ⟨m, hm, rfl⟩ := h
    have := (treeNodeAt_spec hm).2.2.1
    omega

theorem childSlots_used (N : CanonGraph.Node) (hu : CanonGraph.Paired.Filtered.Used N)
    (cs : Coord×Nat) (hc : cs∈childSlots N) : UsedCoord cs.1 := by
  by_cases hnode : ∃ n, N = .node n
  · obtain ⟨n, rfl⟩ := hnode
    obtain ⟨c,b⟩ := cs
    simp only [childSlots, LargeResidual.childSlots] at hc
    split_ifs at hc
    · cases hc
    simp only [List.mem_append, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hc
    rcases hc with ⟨x, hx, rfl, -⟩ | ⟨x, hx, rfl, -⟩ <;>
    · unfold treeChild at hx
      split_ifs at hx
      · obtain ⟨L, -, rfl⟩ := Option.map_eq_some_iff.mp hx; trivial
      · obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.mp hx; trivial
  obtain ⟨c,b⟩ := cs
  cases c with
  | inr s => trivial
  | inl n =>
    change CanonGraph.Paired.Filtered.Used n
    by_contra hn
    let secrets : Secrets := fun _ => 0
    let left : Labels := fun _ => 0
    let value := CanonGraph.Paired.presentEquiv n (ChainGraph.joinOutput 1 0)
    let right : Labels := Function.update left n value
    have heq : CanonGraph.Paired.cell secrets N left=CanonGraph.Paired.cell secrets N right := by
      apply CanonGraph.Paired.Filtered.cell_congr secrets N hu
      intro other ho _
      have hne : other≠n := by intro h; subst other; exact hn ho
      exact (Function.update_of_ne hne value left).symm
    rw [cell_eq_cellValues secrets left N hu,cell_eq_cellValues secrets right N hu] at heq
    have hs := congrArg (fun input => slotValue input b) heq
    have hnn : ∀ m, N = .node m → False := fun m hm => hnode ⟨m, hm⟩
    rw [slot_cellValues N (coordVal secrets left) (fun m hm => (hnn m hm).elim) (Sum.inl n,b) hc,
      slot_cellValues N (coordVal secrets right) (fun m hm => (hnn m hm).elim) (Sum.inl n,b) hc] at hs
    change Extract.Paired.proj n.toPos 0=Extract.Paired.proj n.toPos (right n) at hs
    rw [show right n=value from Function.update_self ..,
      CanonGraph.Paired.proj_presentEquiv,ChainGraph.joinOutput_low] at hs
    have hz : Extract.Paired.proj n.toPos (0 : HashOutput)=0 := by
      cases n <;> simp only [CanonGraph.Node.toPos,Extract.Paired.proj,ite_apply]
      all_goals first | rfl | split_ifs <;> rfl
    rw [hz] at hs
    exact (by decide : (0 : Digest)≠1) hs

theorem Coherent.honestValue_used {U : Finset HashInput} {T : Answers} {vals : Coord→Digest}
    {nv : Message→Digest} {τ : SigGolfCandidate.T3.Security.LargeResidual.Cell U→HashOutput} {a : AuxData}
    (h : Coherent U T vals nv τ a) (c : Coord) (hc : UsedCoord c) : honestValue T c=vals (selCoordV vals c) := by
  cases c with
  | inl n => exact h.honestValue_node n hc
  | inr s => exact h.honestValue_seed s
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (Cell routeAddr)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem ftsLabel_top (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) :
    CanonGraph.Paired.ftsLabel labels index coord 6 b.val =
      Extract.Paired.proj (CanonGraph.Node.wctNode (ftsTopNode index coord b)).toPos
        (labels (.wctNode (ftsTopNode index coord b))) := by
  unfold CanonGraph.Paired.ftsLabel
  rw [if_neg (by decide)]
  unfold ftsNodeAt
  rw [dif_pos (show 6-1<6 ∧ b.val<2^(7-(6-1)-1) by have:=b.isLt;omega)]
  rfl

section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord→Digest} {nv : Message→Digest}
  {τ : Cell U→HashOutput} {a : AuxData}

theorem Coherent.cell (h : Coherent U T vals nv τ a) (N : CanonGraph.Node)
    (hu : CanonGraph.Paired.Filtered.Used N) :
    CanonGraph.Paired.cell (secretsOf T) N (routerLabels vals a)=cellValues N vals := by
  rw [cell_eq_cellValues _ _ N hu,h.coordVal]

theorem Coherent.honest_answer (h : Coherent U T vals nv τ a) (N : CanonGraph.Node)
    (hu : CanonGraph.Paired.Filtered.Used N) :
    T (.inl (.inr (cellValues N vals)))=routerLabels vals a N := by
  rw [←h.cell N hu]
  exact h.agrees N hu

theorem Coherent.leafMsg (h : Coherent U T vals nv τ a) (L : CanonEncoding.EncLeaf) :
    Wots.CanonicalRef.sourceMessages T L.toWots=msgVals vals L := by
  rw [CanonEncoding.Paired.sourceMessages_eq_filtered h.agrees L]
  unfold CanonEncoding.Paired.msgLabel msgVals
  by_cases hl : L.1.lay.val<3
  · rw [dif_pos hl,dif_pos hl]
    congr 1
    · refine (treeLabel_top _ _ _ (childIndex_treeBits L hl) 0).trans ?_
      rw [selNode_of_cap_one (trialCap_lower (fun h => absurd (congrArg Fin.val h) (by simp [topNode])) _) rfl]
      exact CanonGraph.Paired.joinLabels_node _ _ _
    · refine (treeLabel_top _ _ _ (childIndex_treeBits L hl) 1).trans ?_
      rw [selNode_of_cap_one (trialCap_lower (fun h => absurd (congrArg Fin.val h) (by simp [topNode])) _) rfl]
      exact CanonGraph.Paired.joinLabels_node _ _ _
  · rw [dif_neg hl,dif_neg hl]
    congr 1
    · exact (ftsLabel_top _ _ _ 0).trans (CanonGraph.Paired.joinLabels_val _ _ _)
    · exact (ftsLabel_top _ _ _ 1).trans (CanonGraph.Paired.joinLabels_val _ _ _)

theorem Coherent.referenceDigits (h : Coherent U T vals nv τ a) (L : CanonEncoding.EncLeaf) :
    Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) L.toWots =
      ((a.sel L).bind fun r => WCT9.CanonicalPolicy.decode L.1.lay r.2).getD
        (Wots.dummyDigits (WCT9.CanonicalPolicy.normalLayer L.1.lay)) := by
  unfold Wots.CanonicalRef.referenceDigits
  rw [h.search]
  cases hs : a.sel L with
  | none => rfl
  | some r =>
      simp only [Option.bind_some]
      cases WCT9.CanonicalPolicy.decode L.1.lay r.2 <;> rfl

theorem Coherent.routerDigits_eq (h : Coherent U T vals nv τ a) (L : Wots.LeafAddr)
    (hL : ∃L' : CanonEncoding.EncLeaf,L'.toWots=L) :
    routerDigits a L=Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) L := by
  unfold routerDigits
  rw [dif_pos hL]
  have hs := Classical.choose_spec hL
  have hlay : (Classical.choose hL).1.lay=L.lay := congrArg Wots.LeafAddr.lay hs
  conv_rhs => rw [←hs]
  rw [h.referenceDigits,hlay]

theorem Coherent.routeOk_iff (h : Coherent U T vals nv τ a) (index : Nat) (hindex : index<2^31) :
    RouteOkR a index ↔ RouteOk T index := by
  constructor
  · intro hok lay
    obtain ⟨L,r,hL,hs,hd⟩ := hok lay
    rw [←hL,h.search L,hs]
    have hlay : L.1.lay=lay := congrArg Wots.LeafAddr.lay hL
    simp only [Option.bind_some]
    rw [hlay]
    cases hdec : WCT9.CanonicalPolicy.decode lay r.2 with
    | none => rw [hdec] at hd; cases hd
    | some ds => rfl
  · intro hok lay
    obtain ⟨L,hL⟩ := route_source index hindex lay
    change L.toWots = routeAddr index lay at hL
    have h1 := hok lay
    rw [←hL,h.search L] at h1
    have hlay : L.1.lay=lay := congrArg Wots.LeafAddr.lay hL
    cases hs : a.sel L with
    | none => rw [hs] at h1; cases h1
    | some r =>
      rw [hs] at h1
      refine ⟨L,r,hL,hs,?_⟩
      rw [←hlay]
      simp only [Option.bind_some] at h1
      cases hdec : WCT9.CanonicalPolicy.decode L.1.lay r.2 with
      | none => rw [hdec] at h1; cases h1
      | some ds => rfl
end Coherent
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SphincsSecurity.Concrete
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord→Digest} {nv : Message→Digest}
  {τ : Cell U→HashOutput} {a : AuxData}

theorem Coherent.sel_context (h : Coherent U T vals nv τ a) (L : EncLeaf)
    {r : Fin (2^22)×Digest} (hs : a.sel L=some r) :
    ∃remaining,CanonEncoding.Paired.rowsContext a.rows L.toWots=some remaining ∧
      CanonEncoding.Paired.selectionAt a.rows L remaining=some r := by
  rw [h.selected] at hs
  exact Option.bind_eq_some_iff.mp hs

theorem Coherent.sel_valid (h : Coherent U T vals nv τ a) (L : EncLeaf)
    {r : Fin (2^22)×Digest} (hs : a.sel L=some r) :
    ∃ds,WCT9.CanonicalPolicy.decode L.1.lay r.2=some ds := by
  obtain ⟨remaining,_,hr⟩ := h.sel_context L hs
  obtain ⟨hv,⟨ds,low⟩,hd⟩ := CanonEncoding.Paired.selectionAt_producer hr
  have hdec := (WCT9.CanonicalPolicy.producerDecodeAt_spec (WCT9.CanonicalPolicy.producerDecodeOut_spec hd).2).1
  rw [hv] at hdec
  exact ⟨ds,hdec⟩

theorem Coherent.referenceLow (h : Coherent U T vals nv τ a) (L : CanonEncoding.EncLeaf) :
    Wots.CanonicalRef.referenceLow T (Wots.CanonicalRef.sourceMessages T) L.toWots =
      ((a.sel L).bind fun r => (WCT9.CanonicalPolicy.decode L.1.lay r.2).map fun _ =>
        WCT9.lowSelected L.1.lay (a.rows L r.1)).getD true := by
  unfold Wots.CanonicalRef.referenceLow
  rw [h.search]
  cases hs : a.sel L with
  | none => rfl
  | some r =>
      simp only [Option.bind_some]
      cases WCT9.CanonicalPolicy.decode L.1.lay r.2 <;> rfl

theorem Coherent.routerLows_eq (h : Coherent U T vals nv τ a) (L : Wots.LeafAddr)
    (hL : ∃L' : CanonEncoding.EncLeaf,L'.toWots=L) :
    routerLows a L=Wots.CanonicalRef.referenceLow T (Wots.CanonicalRef.sourceMessages T) L := by
  unfold routerLows
  rw [dif_pos hL]
  have hs := Classical.choose_spec hL
  have hlay : (Classical.choose hL).1.lay=L.lay := congrArg Wots.LeafAddr.lay hs
  conv_rhs => rw [←hs]
  rw [h.referenceLow,hlay]
  cases hsel : a.sel (Classical.choose hL) with
  | none => rfl
  | some r =>
      obtain ⟨ds,hd⟩ := h.sel_valid _ hsel
      have hd' : WCT9.CanonicalPolicy.decode L.lay r.2 = some ds := by rw [← hlay]; exact hd
      simp only [Option.map_some, Option.bind_some, hd, hd', Option.getD_some]

theorem Coherent.search_isSome (h : Coherent U T vals nv τ a) (L : EncLeaf) :
    (Wots.CanonicalRef.referenceSearch T (Wots.CanonicalRef.sourceMessages T) L.toWots).isSome =
      (a.sel L).isSome := by
  rw [h.search]
  cases hs : a.sel L with
  | none => rfl
  | some r =>
      obtain ⟨ds,hd⟩ := h.sel_valid L hs
      simp only [Option.bind_some,hd,Option.map_some,Option.isSome_some]

theorem Coherent.referenceInput (h : Coherent U T vals nv τ a) (L : EncLeaf) (X : HashInput)
    (hX : Wots.CanonicalRef.referenceInput T (Wots.CanonicalRef.sourceMessages T) L.toWots=some X) :
    ∃r,a.sel L=some r ∧ X=Wots.encRow L.toWots (msgVals vals L) (BitVec.ofNat 32 r.1.val) 0 := by
  unfold Wots.CanonicalRef.referenceInput at hX
  rw [h.search,h.leafMsg] at hX
  cases hs : a.sel L with
  | none => rw [hs] at hX;cases hX
  | some r =>
      rw [hs] at hX
      obtain ⟨ds,hd⟩ := h.sel_valid L hs
      simp only [Option.bind_some,hd,Option.map_some] at hX
      exact ⟨r,rfl,(Option.some.inj hX).symm⟩

theorem Coherent.decode_ref (h : Coherent U T vals nv τ a) (L : EncLeaf)
    (hs : (a.sel L).isSome) (d : Digest) :
    WCT9.CanonicalPolicy.decode L.1.lay d =
      some (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) L.toWots) ↔
      d=refDigest a L := by
  obtain ⟨r,hr⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨ds,hd⟩ := h.sel_valid L hr
  rw [h.referenceDigits]
  simp only [hr,Option.bind_some,hd,Option.getD_some]
  change WCT9.CanonicalPolicy.decode L.1.lay d=some ds ↔ d=refDigest a L
  have href : refDigest a L=r.2 := by simp only [refDigest,hr]
  rw [href]
  constructor
  · intro hd';exact decode_some_injective hd' hd
  · rintro rfl;exact hd

theorem Coherent.canDecode_ref (h : Coherent U T vals nv τ a) (L : EncLeaf)
    (hs : (a.sel L).isSome) (y : HashOutput) :
    WCT9.encodingCanDecode L.1.lay y
      (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) L.toWots) ↔
      WCT9.encodingTarget L.1.lay (refDigest a L) y = refDigest a L :=
  WCT9.encodingCanDecode_iff_target _ _ _ _ ((h.decode_ref L hs _).mpr rfl)

end Coherent
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue IsDigestRow dummyDigest State Probe Hit Charge Cell
  readState probeState stoppedState tickState disclosedState runWith_map mem_restrict card_restrict_ge low)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure effF_self adm_of_plain Adm famKnown famSeeds
  mem_famSeeds mem_famKnown)
open SigGolfCandidate.T3.Security.LargeCoupling (low_eq keep_guess_label keep_label keep_target
  keep_guess_target dummyDigest_decode')
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeResidual (WCoord Coord SeedIndex WFam wsplit_inr keygenDisclosed keygenCacheDisclosed encodingDisclosed_shape LowerLeaf msgVals msgSlots treeChild)
structure Rel (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) (q : Nat) (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) : Prop where
  disclosed : mon.disclosed = st.disclosed
  seen : mon.seen = st.seen
  calls : mon.calls = st.calls
  wcalls : ws.counters.calls = st.calls
  digests : mon.digests = ws.counters.mass
  contact : mon.contact = false
  probes : ws.counters.probes ≤ ws.counters.calls
  budget : st.calls ≤ q
  mem : ∀ c, Sum.elim vals nv c ∈ ws.candidates c
  hidden : ∀ c, ¬(LargeResidual.Paired.RouterState.known st) c → 2 ^ 128 - ws.counters.probes ≤ (ws.candidates (.inl c)).card
  rowsEq : ∀ row v, ws.rows row = some v → v = τ row
  rowsSeen : ∀ row v, ws.rows row = some v → row.val ∈ st.seen ∨ IsDigestRow row.val
  seenCells : ∀ X ∈ st.seen, X ∈ U → ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1
  seenEnc : ∀ X ∈ st.seen, X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32),
    X = Wots.encRow L.toWots (msgVals vals L) ctr 0 → ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1
section Relation
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
theorem Rel.known (h : Rel U T vals nv τ a q mon st ws) : mon.known = (LargeResidual.Paired.RouterState.known st) := by
  unfold Monitor.known LargeResidual.Paired.RouterState.known
  rw [h.disclosed]
theorem Rel.query (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (y : HashOutput) :
    mon.query U T q X y =
      if X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X y then
        ⟨mon.disclosed, X :: mon.seen, mon.calls + 1, mon.digests, true⟩
      else ⟨mon.disclosed, X :: mon.seen, mon.calls + 1,
        mon.digests + (if X ∈ U ∧ IsDigestRow X then 1 else 0), false⟩ := by
  have hc : mon.calls + 1 ≤ q := by rw [h.calls]; omega
  unfold Monitor.query
  rw [if_neg (by rw [h.contact]; decide), h.known, h.seen]
  by_cases ht : X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X y
  · rw [if_pos ⟨ht.1, ht.2.1, hc, ht.2.2⟩, if_pos ht]
  · rw [if_neg (fun h' => ht ⟨h'.1, h'.2.1, h'.2.2.2⟩), if_neg ht]
    by_cases hd : X ∈ U ∧ IsDigestRow X
    · rw [if_pos ⟨hd.1, hd.2, hc⟩, if_pos hd]
    · rw [if_neg (fun h' => hd ⟨h'.1, h'.2.1⟩), if_neg hd]
theorem Rel.two_le (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (c : Coord)
    (hc : ¬(LargeResidual.Paired.RouterState.known st) c) : 2 ≤ (ws.candidates (.inl c)).card := by
  have h1 := h.hidden c hc
  have h2 := h.probes
  have h3 := h.wcalls
  omega
theorem Rel.next (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (ws' : LargeResidual.State WCoord (Cell U)) (δ : Nat)
    (hcalls : ws'.counters.calls = st.calls + 1) (hmass : ws'.counters.mass = ws.counters.mass + δ)
    (hprobes : ws'.counters.probes ≤ ws'.counters.calls)
    (hmem : ∀ c, Sum.elim vals nv c ∈ ws'.candidates c)
    (hhidden : ∀ c, ¬(LargeResidual.Paired.RouterState.known st) c → 2 ^ 128 - ws'.counters.probes ≤ (ws'.candidates (.inl c)).card)
    (hrowsEq : ∀ row v, ws'.rows row = some v → v = τ row)
    (hrowsSeen : ∀ row v, ws'.rows row = some v → row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val)
    (hcell : X ∈ U → ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1)
    (st' : RouterState) (hd : st'.disclosed = st.disclosed) (hs : st'.seen = X :: st.seen)
    (hc : st'.calls = st.calls + 1) :
    Rel U T vals nv τ a q ⟨mon.disclosed, X :: mon.seen, mon.calls + 1, mon.digests + δ, false⟩ st' ws' := by
  have hk : (LargeResidual.Paired.RouterState.known st') = (LargeResidual.Paired.RouterState.known st) := by unfold LargeResidual.Paired.RouterState.known; rw [hd]
  refine ⟨by rw [hd]; exact h.disclosed, by rw [hs, h.seen], by rw [hc, h.calls], by rw [hcalls, hc], ?_, rfl,
    hprobes, (show st'.calls ≤ q by omega), hmem, ?_, hrowsEq, ?_, ?_, ?_⟩
  · simp only [hmass, h.digests]
  · rw [hk]; exact hhidden
  · intro row v hv
    rw [hs]
    rcases hrowsSeen row v hv with h1 | h1 | h1
    · exact Or.inl (by rw [h1]; exact List.mem_cons_self)
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    · exact Or.inr h1
  · intro Y hY hYU N hu hN cs hcs
    rw [hk]
    rw [hs] at hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact hcell hYU N hu hN cs hcs
    · exact h.seenCells Y hY hYU N hu hN cs hcs
  · intro Y hY hYU L ctr hL
    rw [hk]
    rw [hs] at hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact henc hYU L ctr hL
    · exact h.seenEnc Y hY hYU L ctr hL
end Relation
def QueryOutcome (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) (q : Nat) (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U))
    (X : HashInput) (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U))) : Prop :=
  ∃ ws' : LargeResidual.State WCoord (Cell U),
    ((mon.query U T q X (T (.inl (.inr X)))).contact = true ∧ out = pure (none, ws') ∧
        ws'.counters.mass = mon.digests ∧ ws'.counters.calls ≤ q) ∨
      ((mon.query U T q X (T (.inl (.inr X)))).contact = false ∧
        out = pure (some (T (.inl (.inr X)), st.next U X (T (.inl (.inr X)))), ws') ∧
        Rel U T vals nv τ a q (mon.query U T q X (T (.inl (.inr X)))) (st.next U X (T (.inl (.inr X)))) ws')
section Query
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem observed_map {β γ : Type} (f : β → γ) (c : OracleComp (RWorld U) β) (s : LargeResidual.State WCoord (Cell U)) :
    observedRun aux q (Sum.elim vals nv) τ (f <$> c) s = (fun r => (r.1.map f, r.2)) <$> observedRun aux q (Sum.elim vals nv) τ c s :=
  runWith_map _ f c s
theorem observed_testReq (st' : RouterState) (X : HashInput) (hX : X ∈ U) (test : Probe WCoord)
    (hfresh : X ∉ st.seen → ws.rows ⟨X, hX⟩ = none) :
    observedRun aux q (Sum.elim vals nv) τ ((fun y => (y, st')) <$> testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ test) ws =
      if X ∉ st.seen then
        (if (test.effF ws.candidates).keep (Sum.elim vals nv) (τ ⟨X, hX⟩) then
          pure (some (τ ⟨X, hX⟩, st'), probeState ws ⟨X, hX⟩ (test.effF ws.candidates) (τ ⟨X, hX⟩))
        else pure (none, stoppedState ws))
      else pure (some (τ ⟨X, hX⟩, st'), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call) := by
  rw [observed_map]
  by_cases hs : X ∈ st.seen
  · have hd : decide (X ∉ st.seen) = false := by simp [hs]
    rw [hd, if_neg (not_not.mpr hs)]
    simp only [testReq, Bool.false_eq_true, if_false]
    rw [← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
    rfl
  · have hd : decide (X ∉ st.seen) = true := by simp [hs]
    rw [hd, if_pos hs]
    simp only [testReq, if_true]
    rw [← bind_pure (probeReq U ⟨X, hX⟩ test), observed_probeReq_fresh U aux q (Sum.elim vals nv) τ _ _ _ _ (hfresh hs)]
    split_ifs
    · rw [observed_pure, map_pure]; rfl
    · rw [map_pure]; rfl
theorem observed_testReqP (g : HashOutput → HashOutput) (st' : RouterState) (X : HashInput) (hX : X ∈ U)
    (test : Probe WCoord) (hfresh : X ∉ st.seen → ws.rows ⟨X, hX⟩ = none) :
    observedRun aux q (Sum.elim vals nv) τ ((fun y => (g y, st')) <$> testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ test) ws =
      if X ∉ st.seen then
        (if (test.effF ws.candidates).keep (Sum.elim vals nv) (τ ⟨X, hX⟩) then
          pure (some (g (τ ⟨X, hX⟩), st'), probeState ws ⟨X, hX⟩ (test.effF ws.candidates) (τ ⟨X, hX⟩))
        else pure (none, stoppedState ws))
      else pure (some (g (τ ⟨X, hX⟩), st'), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call) := by
  rw [observed_map]
  by_cases hs : X ∈ st.seen
  · have hd : decide (X ∉ st.seen) = false := by simp [hs]
    rw [hd, if_neg (not_not.mpr hs)]
    simp only [testReq, Bool.false_eq_true, if_false]
    rw [← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
    rfl
  · have hd : decide (X ∉ st.seen) = true := by simp [hs]
    rw [hd, if_pos hs]
    simp only [testReq, if_true]
    rw [← bind_pure (probeReq U ⟨X, hX⟩ test), observed_probeReq_fresh U aux q (Sum.elim vals nv) τ _ _ _ _ (hfresh hs)]
    split_ifs
    · rw [observed_pure, map_pure]; rfl
    · rw [map_pure]; rfl
end Query
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem outcome_stop (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U)))
    (hc : X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X))))
    (hout : out = pure (none, stoppedState ws)) :
    QueryOutcome U T vals nv τ a q mon st ws X out := by
  refine ⟨stoppedState ws, Or.inl ⟨?_, hout, ?_, ?_⟩⟩
  · rw [hrel.query hlt, if_pos hc]
  · exact hrel.digests.symm
  · show ws.counters.calls + 1 ≤ q
    rw [hrel.wcalls]
    omega
theorem outcome_continue (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U)))
    (hc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))))
    (ws' : LargeResidual.State WCoord (Cell U))
    (hout : out = pure (some (T (.inl (.inr X)), st.next U X (T (.inl (.inr X)))), ws'))
    (hcalls : ws'.counters.calls = st.calls + 1)
    (hmass : ws'.counters.mass = ws.counters.mass + (if X ∈ U ∧ IsDigestRow X then 1 else 0))
    (hprobes : ws'.counters.probes ≤ ws'.counters.calls)
    (hmem : ∀ c, Sum.elim vals nv c ∈ ws'.candidates c)
    (hhidden : ∀ c, ¬(LargeResidual.Paired.RouterState.known st) c → 2 ^ 128 - ws'.counters.probes ≤ (ws'.candidates (.inl c)).card)
    (hrowsEq : ∀ row v, ws'.rows row = some v → v = τ row)
    (hrowsSeen : ∀ row v, ws'.rows row = some v → row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val)
    (hcell : X ∈ U → ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X out := by
  refine ⟨ws', Or.inr ⟨?_, hout, ?_⟩⟩
  · rw [hrel.query hlt, if_neg hc]
  · rw [hrel.query hlt, if_neg hc]
    refine hrel.next hlt X ws' _ hcalls hmass hprobes hmem hhidden hrowsEq hrowsSeen hcell henc _ ?_ ?_ ?_ <;>
    · unfold LargeResidual.RouterState.next
      split_ifs <;> rfl
theorem Rel.fresh (hrel : Rel U T vals nv τ a q mon st ws) (X : HashInput) (hX : X ∈ U) (hd : ¬IsDigestRow X)
    (hs : X ∉ st.seen) : ws.rows ⟨X, hX⟩ = none := by
  cases hr : ws.rows ⟨X, hX⟩ with
  | none => rfl
  | some v =>
      rcases hrel.rowsSeen _ v hr with h | h
      · exact absurd h hs
      · exact absurd h hd
theorem case_outside (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q)
    (X : HashInput) (hX : X ∉ U) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (tickReq U .call >>= fun _ =>
      pure ((0 : HashOutput), st.after X)) ws) := by
  rw [observed_tickReq, observed_pure]
  apply outcome_continue hrel hlt X _ (fun h => hX h.2.1) (tickState q ws .call)
  · rw [hcoh.outside X hX, LargeResidual.RouterState.next_of_not U st X _ (fun h' => hX h'.1)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hX h.1), Nat.add_zero]
  · show ws.counters.probes ≤ ws.counters.calls + 1
    have := hrel.probes; omega
  · exact hrel.mem
  · exact hrel.hidden
  · exact hrel.rowsEq
  · intro row v hv; exact Or.inr (hrel.rowsSeen row v hv)
  · intro h; exact absurd h hX
  · intro h; exact absurd h hX
theorem rows_update_eq (hrel : Rel U T vals nv τ a q mon st ws) (row0 : Cell U) :
    ∀ row v, Function.update ws.rows row0 (some (τ row0)) row = some v → v = τ row := by
  intro row v hv
  by_cases hr : row = row0
  · subst hr
    rw [Function.update_self] at hv
    exact (Option.some.inj hv).symm
  · rw [Function.update_of_ne hr] at hv
    exact hrel.rowsEq row v hv
theorem rows_update_seen (hrel : Rel U T vals nv τ a q mon st ws) (X : HashInput) (hX : X ∈ U) :
    ∀ row v, Function.update ws.rows ⟨X, hX⟩ (some (τ ⟨X, hX⟩)) row = some v →
      row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val := by
  intro row v hv
  by_cases hr : row = ⟨X, hX⟩
  · exact Or.inl (by rw [hr])
  · rw [Function.update_of_ne hr] at hv
    exact Or.inr (hrel.rowsSeen row v hv)
theorem continue_read (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U)
    (ch : Charge) (hch : (ch = .call ∧ ¬IsDigestRow X) ∨ (ch = .mass ∧ IsDigestRow X))
    (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.next U X (τ ⟨X, hX⟩)),
        readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) ch)) := by
  apply outcome_continue hrel hlt X _ hnc (readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) ch)
  · rw [hTX]
  · rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    · show ws.counters.calls + 1 = st.calls + 1
      rw [hrel.wcalls]
  · rcases hch with ⟨rfl, hd⟩ | ⟨rfl, hd⟩
    · show ws.counters.mass = ws.counters.mass + _
      rw [if_neg (fun h => hd h.2), Nat.add_zero]
    · show ws.counters.mass + (if ws.counters.calls + 1 ≤ q then 1 else 0) = ws.counters.mass + _
      rw [if_pos (show ws.counters.calls + 1 ≤ q by rw [hrel.wcalls]; omega),
        if_pos (show X ∈ U ∧ IsDigestRow X from ⟨hX, hd⟩)]
  · have := hrel.probes
    rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · show ws.counters.probes ≤ ws.counters.calls + 1
      omega
    · show ws.counters.probes ≤ ws.counters.calls + 1
      omega
  · exact hrel.mem
  · rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hrel.hidden
    · exact hrel.hidden
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
theorem continue_read_call (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (hX : X ∈ U) (hnd : ¬IsDigestRow X) (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.after X), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call)) := by
  have h := continue_read hrel hlt X hX .call (Or.inl ⟨rfl, hnd⟩) hTX hnc hcell henc
  rwa [LargeResidual.RouterState.next_of_not U st X _ (fun h' => hnd h'.2)] at h
theorem continue_probe (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U)
    (test : Probe WCoord) (hk : test.keep (Sum.elim vals nv) (τ ⟨X, hX⟩))
    (hadm : ∀ g ∈ test.guess, ∀ parent, test.hit = Hit.label parent → g.1 ≠ parent)
    (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩) (hnd : ¬IsDigestRow X)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.after X),
        probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))) := by
  apply outcome_continue hrel hlt X _ hnc (probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))
  · rw [hTX, LargeResidual.RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hnd h.2), Nat.add_zero]
  · show ws.counters.probes + 1 ≤ ws.counters.calls + 1
    have := hrel.probes; omega
  · exact (mem_restrict test ws.candidates (τ ⟨X, hX⟩) (Sum.elim vals nv)).mpr ⟨hrel.mem, hk.1, by
      rcases test with ⟨g, hit⟩
      cases hit with
      | label p => exact hk.2
      | target t => trivial
      | selectedTarget t pickLow => trivial⟩
  · intro c hc
    have h1 := hrel.hidden c hc
    have h2 := card_restrict_ge test ws.candidates (τ ⟨X, hX⟩) hadm (.inl c)
    show 2 ^ 128 - (ws.counters.probes + 1) ≤ (test.restrict ws.candidates (τ ⟨X, hX⟩) (.inl c)).card
    omega
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
theorem continue_read_callP (g : HashOutput → HashOutput) (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q)
    (X : HashInput) (hX : X ∈ U) (hnd : ¬IsDigestRow X) (hTX : T (.inl (.inr X)) = g (τ ⟨X, hX⟩))
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (g (τ ⟨X, hX⟩), st.after X), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call)) := by
  apply outcome_continue hrel hlt X _ hnc (readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call)
  · rw [hTX, LargeResidual.RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hnd h.2), Nat.add_zero]
  · have := hrel.probes
    show ws.counters.probes ≤ ws.counters.calls + 1
    omega
  · exact hrel.mem
  · exact hrel.hidden
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
theorem continue_probeP (g : HashOutput → HashOutput) (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q)
    (X : HashInput) (hX : X ∈ U)
    (test : Probe WCoord) (hk : test.keep (Sum.elim vals nv) (τ ⟨X, hX⟩))
    (hadm : ∀ g ∈ test.guess, ∀ parent, test.hit = Hit.label parent → g.1 ≠ parent)
    (hTX : T (.inl (.inr X)) = g (τ ⟨X, hX⟩)) (hnd : ¬IsDigestRow X)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (g (τ ⟨X, hX⟩), st.after X),
        probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))) := by
  apply outcome_continue hrel hlt X _ hnc (probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))
  · rw [hTX, LargeResidual.RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hnd h.2), Nat.add_zero]
  · show ws.counters.probes + 1 ≤ ws.counters.calls + 1
    have := hrel.probes; omega
  · exact (mem_restrict test ws.candidates (τ ⟨X, hX⟩) (Sum.elim vals nv)).mpr ⟨hrel.mem, hk.1, by
      rcases test with ⟨g, hit⟩
      cases hit with
      | label p => exact hk.2
      | target t => trivial
      | selectedTarget t pickLow => trivial⟩
  · intro c hc
    have h1 := hrel.hidden c hc
    have h2 := card_restrict_ge test ws.candidates (τ ⟨X, hX⟩) hadm (.inl c)
    show 2 ^ 128 - (ws.counters.probes + 1) ≤ (test.restrict ws.candidates (τ ⟨X, hX⟩) (.inl c)).card
    omega
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
/-- FTS seeds of family `f` disclosed by the router so far. -/
@[irreducible] noncomputable def DiscSeeds (st : RouterState) (f : Fin (2 ^ 31) × Fin 9) : Finset CanonGraph.WctAddr :=
  Finset.univ.filter fun w => (w.1, w.2.1) = f ∧ (.inr (.inr w) : Coord) ∈ st.disclosed
theorem mem_DiscSeeds (st : RouterState) (f : Fin (2 ^ 31) × Fin 9) (w : CanonGraph.WctAddr) :
    w ∈ DiscSeeds st f ↔ (w.1, w.2.1) = f ∧ (.inr (.inr w) : Coord) ∈ st.disclosed := by
  unfold DiscSeeds
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
/-- Lower WOTS seeds of leaf `L` disclosed by the router so far (stage B). -/
@[irreducible] noncomputable def DiscLower (st : RouterState) (L : LowerLeaf) : Finset ChainGraph.Address :=
  Finset.univ.filter fun a =>
    (a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf) = L.1 ∧ (.inr (.inl a) : Coord) ∈ st.disclosed
theorem mem_DiscLower (st : RouterState) (L : LowerLeaf) (a : ChainGraph.Address) :
    a ∈ DiscLower st L ↔
      (a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf) = L.1 ∧ (.inr (.inl a) : Coord) ∈ st.disclosed := by
  unfold DiscLower
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
/-- No seed family is determined by the router's disclosures: FTS families have at most 53 disclosed seeds, WOTS
leaf families at most `famCount − 1` (structurally at most `famCount − 3`: 14 lower, `lower_zero_count_le`; 21 top of
31 coefficients, `top_zero_count_le`, campaign T51). -/
def FamOK (st : RouterState) : Prop :=
  (∀ f, (DiscSeeds st f).card ≤ 53) ∧ ∀ L : LowerLeaf, (DiscLower st L).card ≤ WCT9.famSize L.1.1 L.1.2.2.val - 1
theorem DiscSeeds_mono {st st' : RouterState} (h : ∀ x ∈ st.disclosed, x ∈ st'.disclosed)
    (f : Fin (2 ^ 31) × Fin 9) : DiscSeeds st f ⊆ DiscSeeds st' f := by
  intro w hw
  rw [mem_DiscSeeds] at hw ⊢
  exact ⟨hw.1, h _ hw.2⟩
theorem DiscLower_mono {st st' : RouterState} (h : ∀ x ∈ st.disclosed, x ∈ st'.disclosed)
    (L : LowerLeaf) : DiscLower st L ⊆ DiscLower st' L := by
  intro w hw
  rw [mem_DiscLower] at hw ⊢
  exact ⟨hw.1, h _ hw.2⟩
theorem famOK_mono {st st' : RouterState} (h : ∀ x ∈ st.disclosed, x ∈ st'.disclosed) (hok : FamOK st') :
    FamOK st :=
  ⟨fun f => (Finset.card_le_card (DiscSeeds_mono h f)).trans (hok.1 f),
    fun L => (Finset.card_le_card (DiscLower_mono h L)).trans (hok.2 L)⟩
theorem famOK_of_disclosed {st st' : RouterState} (h : st'.disclosed = st.disclosed) (hok : FamOK st) :
    FamOK st' := famOK_mono (fun x hx => by rw [h] at hx; exact hx) hok
theorem router_next_disclosed (U : Finset HashInput)
    (st : RouterState) (X : HashInput) (y : HashOutput) : (st.next U X y).disclosed = st.disclosed := by
  unfold LargeResidual.RouterState.next LargeResidual.RouterState.after
  split_ifs <;> rfl
theorem known_seed_base {D : Coord → Prop} {s : SeedIndex} (h : Known D (.inr s)) : D (.inr s) := by
  cases h with
  | base h => exact h
theorem keygen_inl {c : Coord} (hc : c ∈ keygenDisclosed) : ∃ N, c = .inl N := by
  rcases LargeResidual.mem_keygenDisclosed.mp hc with hc | hc | hc
  rotate_left
  · rcases encodingDisclosed_shape hc with ⟨n, rfl⟩ | ⟨i, rfl⟩ <;> exact ⟨_, rfl⟩
  · obtain ⟨n, rfl⟩ := LargeResidual.topTrialsDisclosed_shape hc; exact ⟨_, rfl⟩
  · unfold keygenCacheDisclosed at hc
    simp only [List.mem_flatMap, List.mem_filterMap] at hc
    obtain ⟨level, _, node, _, h⟩ := hc
    unfold treeChild at h
    split_ifs at h
    · obtain ⟨L, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨_, rfl⟩
    · obtain ⟨n, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨_, rfl⟩
theorem known_seed_disc (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127)
    (s : SeedIndex) (hc1 : (ws.candidates (.inl (.inr s))).card = 1) : (.inr s : Coord) ∈ st.disclosed := by
  have hk : (LargeResidual.Paired.RouterState.known st) (.inr s) := by
    by_contra hn
    have := h.two_le hlt hq _ hn
    omega
  rcases known_seed_base hk with hkg | hd
  · obtain ⟨N, hN⟩ := keygen_inl hkg; cases hN
  · exact hd
theorem famKnown_le (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (hok : FamOK st)
    (f : WFam) : (famKnown ws.candidates f).card ≤ ClaudeWCT.W9.T3.Security.FamResidual.Seeds.deg (Coord := WCoord) f := by
  rcases f with L | f
  · let e : ChainGraph.Address ↪ WCoord := ⟨fun a => .inl (.inr (.inl a)), fun a a' h => by simpa using h⟩
    refine (Finset.card_le_card (t := (DiscLower st L).map e) ?_).trans
      (by rw [Finset.card_map]; exact hok.2 L)
    intro c hc
    have hm := (mem_famKnown ws.candidates (Sum.inl L : WFam) c).mp hc
    obtain ⟨pt, hpt⟩ := hm.1
    rcases wsplit_inr hpt with ⟨a, ha, rfl, hfp⟩ | ⟨w, rfl, hfp⟩
    · simp only [Prod.mk.injEq] at hfp
      refine Finset.mem_map.mpr ⟨a, (mem_DiscLower st L a).mpr ⟨?_, known_seed_disc h hlt hq _ hm.2⟩, rfl⟩
      rw [Sum.inl.inj hfp.1]
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hfp
  · let e : CanonGraph.WctAddr ↪ WCoord := ⟨fun w => .inl (.inr (.inr w)), fun w w' h => by simpa using h⟩
    refine (Finset.card_le_card (t := (DiscSeeds st f).map e) ?_).trans
      (by rw [Finset.card_map]; exact hok.1 f)
    intro c hc
    have hm := (mem_famKnown ws.candidates (Sum.inr f : WFam) c).mp hc
    obtain ⟨pt, hpt⟩ := hm.1
    rcases wsplit_inr hpt with ⟨a, ha, rfl, hfp⟩ | ⟨w, rfl, hfp⟩
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hfp
    · simp only [Prod.mk.injEq] at hfp
      exact Finset.mem_map.mpr ⟨w, (mem_DiscSeeds st f w).mpr ⟨(Sum.inr.inj hfp.1).symm,
        known_seed_disc h hlt hq _ hm.2⟩, rfl⟩
/-- Admissibility of a router guess on an unknown coordinate (the hit, if a label, is a node). -/
theorem Rel.adm (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (hok : FamOK st)
    (c : Coord) (hc : ¬(LargeResidual.Paired.RouterState.known st) c) (v : Digest) (hit : Hit WCoord)
    (hpar : ∀ parent, hit = Hit.label parent → (.inl c : WCoord) ≠ parent ∧ ∃ N, parent = .inl (.inl N)) :
    Adm ws.candidates hit ((.inl c : WCoord), v) := by
  refine ⟨h.two_le hlt hq c hc, fun parent hp => (hpar parent hp).1, fun fp _ => ⟨famKnown_le h hlt hq hok fp.1,
    fun parent hp fp' => ?_⟩⟩
  obtain ⟨N, rfl⟩ := (hpar parent hp).2
  intro hs
  cases hs

end Cases
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (Cell slotValue)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
open ClaudeWCT.W9.T3.Security.LargeResidual (msgVals msgSlots msgSlot_mem_keygen)
open ClaudeWCT.W9.T3.Security.LargeCoupling (encodingRow_parsed_none encRow_encLeaf)
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem childSlots_ne (N : CanonGraph.Node) (hu : CanonGraph.Paired.Filtered.Used N)
    (cs : Coord×Nat) (hc : cs∈childSlots N) : cs.1≠.inl N := by
  intro he
  by_cases hnode : ∃ n, N = .node n
  · obtain ⟨n, rfl⟩ := hnode
    obtain ⟨c,b⟩ := cs
    dsimp only at he
    subst c
    simp only [childSlots, LargeResidual.childSlots] at hc
    split_ifs at hc
    · cases hc
    simp only [List.mem_append, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hc
    rcases hc with ⟨x, hx, hxe, -⟩ | ⟨x, hx, hxe, -⟩ <;> subst hxe <;> exact treeChild_ne_self n _ hx
  obtain ⟨c,b⟩ := cs
  dsimp only at he
  subst c
  let secrets : Secrets := fun _ => 0
  let left : Labels := fun _ => 0
  let value := CanonGraph.Paired.presentEquiv N (ChainGraph.joinOutput 1 0)
  let right : Labels := Function.update left N value
  have heq : CanonGraph.Paired.cell secrets N left=CanonGraph.Paired.cell secrets N right := by
    apply CanonGraph.Paired.Filtered.cell_congr secrets N hu
    intro other _ hd
    have hne : other≠N := by intro he;subst other;exact (Nat.lt_irrefl _ hd)
    exact (Function.update_of_ne hne value left).symm
  rw [cell_eq_cellValues secrets left N hu,cell_eq_cellValues secrets right N hu] at heq
  have hs := congrArg (fun input => slotValue input b) heq
  have hnn : ∀ m, N = .node m → False := fun m hm => hnode ⟨m, hm⟩
  rw [slot_cellValues N (coordVal secrets left) (fun m hm => (hnn m hm).elim) (Sum.inl N,b) hc,
    slot_cellValues N (coordVal secrets right) (fun m hm => (hnn m hm).elim) (Sum.inl N,b) hc] at hs
  change Extract.Paired.proj N.toPos 0=Extract.Paired.proj N.toPos (right N) at hs
  rw [show right N=value from Function.update_self ..,
    CanonGraph.Paired.proj_presentEquiv,ChainGraph.joinOutput_low] at hs
  have hz : Extract.Paired.proj N.toPos (0 : HashOutput)=0 := by
    cases N <;> simp only [CanonGraph.Node.toPos,Extract.Paired.proj,ite_apply]
    all_goals first | rfl | split_ifs <;> rfl
  rw [hz] at hs
  exact (by decide : (0 : Digest)≠1) hs

theorem firstUnknown_some {K : Coord→Prop} {N : CanonGraph.Node} {cs : Coord×Nat}
    (h : firstUnknown K N=some cs) : cs∈childSlots N ∧ ¬K cs.1 := by
  unfold firstUnknown at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨hm,hp⟩
theorem firstUnknown_none {K : Coord→Prop} {N : CanonGraph.Node} (h : firstUnknown K N=none) :
    ∀cs∈childSlots N,K cs.1 := by
  intro cs hc
  have ht := List.find?_eq_none.mp h cs hc
  simpa using ht

theorem RouterState.msgSlot_known (st : RouterState) (L : EncLeaf) (cs : Coord×Nat) (hc : cs∈msgSlots L) :
    RouterState.known st cs.1 := Known.base (Or.inl (msgSlot_mem_keygen hc))

theorem contactTest_parsed {A : Answers} {K : Coord→Prop} {X : HashInput} {y : HashOutput} {N : CanonGraph.Node}
    (hu : CanonGraph.Paired.Filtered.Used N) (hN : Extract.posOf X=some N.toPos) (hN0 : NoOver N) :
    ContactTest A K X y ↔
      (∃cs,firstUnknown K N=some cs ∧ slotValue X cs.2=honestValue A cs.1) ∨
        (X≠Extract.Paired.honestInput A N.toPos ∧ Extract.Paired.proj N.toPos y=honestValue A (.inl N)) := by
  constructor
  · rintro (⟨N',_,hN',h⟩ | ⟨L,m,c,pad,_,hX,_⟩)
    · rw [hN] at hN'
      have he : N'.toPos = N.toPos := (Option.some.inj hN').symm
      have hv : honestValue A (.inl N') = honestValue A (.inl N) := by
        change Extract.Paired.proj N'.toPos _ = Extract.Paired.proj N.toPos _
        rw [he]
      by_cases hov : NoOver N'
      · have hfu : firstUnknown K N' = firstUnknown K N := by
          unfold firstUnknown; rw [childSlots_eq_of he hov hN0]
        rw [hfu, hv, he] at h
        exact h
      · have h0 : childSlots N' = [] := by
          cases N' with
          | node m =>
            have h1 : trialCap m.1.lay m.1.level.val ≤ m.1.nonce.val := by
              by_contra h2; exact hov (fun m' hm' => by cases hm'; omega)
            change LargeResidual.childSlots (.node m) = []
            simp only [LargeResidual.childSlots]; rw [if_pos h1]
          | _ => exact absurd (fun m' hm' => by cases hm') hov
        rcases h with ⟨cs, hcs, -⟩ | h
        · unfold firstUnknown at hcs; rw [h0] at hcs; cases hcs
        · rw [hv, he] at h; exact Or.inr h
    · rw [hX,encodingRow_parsed_none] at hN;cases hN
  · intro h
    exact Or.inl ⟨N,(CanonGraph.Paired.Filtered.used_iff_bounded N).1 hu,hN,h⟩

theorem contactTest_enc {A : Answers} {K : Coord→Prop} {y : HashOutput} {L : EncLeaf} {m : WCT9.LayerMsg}
    {c : BitVec 32} {pad : Wots.RowPad} (hfit : Extract.msgFits L.1.lay m) :
    ContactTest A K (Wots.encRow L.toWots m c pad) y ↔
      Wots.CanonicalRef.referenceSearch A (Wots.CanonicalRef.sourceMessages A) L.toWots≠none ∧
      Wots.CanonicalRef.referenceInput A (Wots.CanonicalRef.sourceMessages A) L.toWots≠some (Wots.encRow L.toWots m c pad) ∧
      Wots.CanonicalRef.NotSearched A (Wots.CanonicalRef.sourceMessages A) L.toWots (Wots.encRow L.toWots m c pad) ∧
      WCT9.encodingCanDecode L.1.lay y
        (Wots.CanonicalRef.referenceDigits A (Wots.CanonicalRef.sourceMessages A) L.toWots) := by
  constructor
  · rintro (⟨N',_,hN',_⟩ | ⟨L',m',c',pad',_,hX,h⟩)
    · rw [encodingRow_parsed_none] at hN';cases hN'
    · obtain ⟨rfl,_⟩ := encRow_encLeaf hX
      exact h
  · intro h;exact Or.inr ⟨L,m,c,pad,hfit,rfl,h⟩

theorem not_parsed_of_encRow {X : HashInput} (he : LargeResidual.EncRow X) : ¬Parsed X := by
  rintro ⟨N,_,hN⟩
  exact ClaudeWCT.W9.T3.Security.LargeCoupling.not_parsed_of_encRow he ⟨N,hN⟩
theorem not_parsed_of_digest {X : HashInput} (hd : SigGolfCandidate.T3.Security.LargeResidual.IsDigestRow X) :
    ¬Parsed X := by
  rintro ⟨N,_,hN⟩
  exact ClaudeWCT.W9.T3.Security.LargeCoupling.not_parsed_of_digest hd ⟨N,hN⟩
theorem contactTest_other {A : Answers} {K : Coord→Prop} {X : HashInput} {y : HashOutput}
    (hp : ¬Parsed X) (he : ¬LargeResidual.EncRow X) : ¬ContactTest A K X y := by
  rintro (⟨N,hu,hN,_⟩ | ⟨L,m,c,pad,hfit,hX,_⟩)
  · exact hp ⟨N,(CanonGraph.Paired.Filtered.used_iff_bounded N).2 hu,hN⟩
  · exact he ⟨L,m,c,pad,hfit,hX⟩

section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord→Digest} {nv : Message→Digest}
  {τ : Cell U→HashOutput} {a : AuxData}

/-- A cell decoding to the position of `N` is the cell of a non-phantom node of that position. -/
theorem Coherent.cell_pos (h : Coherent U T vals nv τ a) {X : HashInput} {N M : CanonGraph.Node}
    (hN : Extract.posOf X=some N.toPos) (hu : CanonGraph.Paired.Filtered.Used M) (heq : X=cellValues M vals) :
    M.toPos=N.toPos ∧ ¬PhantomAt M (routerLabels vals a) :=
  CanonGraph.Paired.cell_eq_of_posOf (secretsOf T) (routerLabels vals a) hN (heq.trans (h.cell M hu).symm)

theorem Coherent.not_cell_parsed (h : Coherent U T vals nv τ a) {X : HashInput} {N : CanonGraph.Node}
    (hN : Extract.posOf X=some N.toPos)
    (hne : ∀M,CanonGraph.Paired.Filtered.Used M → M.toPos=N.toPos → X≠cellValues M vals) :
    ∀N',CanonGraph.Paired.Filtered.Used N' → X≠cellValues N' vals := by
  intro N' hu heq
  exact hne N' hu (h.cell_pos hN hu heq).1 heq

theorem not_cell_unparsed (h : Coherent U T vals nv τ a) {X : HashInput} (hp : ¬Parsed X)
    (hph : ∀ n, X ≠ phantom n) :
    ∀N',CanonGraph.Paired.Filtered.Used N' → X≠cellValues N' vals := by
  intro N' hu heq
  have hc : X = CanonGraph.Paired.cell (secretsOf T) N' (routerLabels vals a) := heq.trans (h.cell N' hu).symm
  by_cases hphA : PhantomAt N' (routerLabels vals a)
  · obtain ⟨n, rfl, hn⟩ := hphA
    apply hph n
    rw [hc, CanonGraph.Paired.cell_node]
    exact cell_node_inactive hn
  · exact hp ⟨N',hu,by rw [hc]; exact CanonGraph.Paired.posOf_cell _ _ _ hphA⟩

theorem Coherent.activeV_iff (h : Coherent U T vals nv τ a) (n : TreeNode) :
    LargeResidual.ActiveV vals n ↔ Active (routerLabels vals a) n := by
  have := activeV_coordVal (secretsOf T) (routerLabels vals a) n
  rwa [h.coordVal] at this

/-- A phantom input is the cell of exactly its own (inactive) tree node. -/
theorem Coherent.cell_phantom (h : Coherent U T vals nv τ a) {N' : CanonGraph.Node} {n : TreeNode}
    (hu : CanonGraph.Paired.Filtered.Used N') (heq : phantom n = cellValues N' vals) :
    N' = .node n ∧ ¬ Active (routerLabels vals a) n := by
  have hc : phantom n = CanonGraph.Paired.cell (secretsOf T) N' (routerLabels vals a) := heq.trans (h.cell N' hu).symm
  by_cases hphA : PhantomAt N' (routerLabels vals a)
  · obtain ⟨m, rfl, hm⟩ := hphA
    rw [CanonGraph.Paired.cell_node, cell_node_inactive hm] at hc
    have := phantom_injective hc
    subst this
    exact ⟨rfl, hm⟩
  · have := CanonGraph.Paired.posOf_cell (secretsOf T) N' (routerLabels vals a) hphA
    rw [← hc, posOf_phantom] at this
    cases this

theorem not_prefix_parsed {X : HashInput} (hp : Parsed X) : ¬HonestPrefix vals a X := by
  rintro ⟨L,ctr,rfl,_⟩
  exact not_parsed_of_encRow ⟨L,_,ctr,0,LargeCoupling.msgFits_msgVals vals L,rfl⟩ hp
theorem not_prefix_enc {X : HashInput} (he : ¬LargeResidual.EncRow X) : ¬HonestPrefix vals a X := by
  rintro ⟨L,ctr,rfl,_⟩
  exact he ⟨L,_,ctr,0,LargeCoupling.msgFits_msgVals vals L,rfl⟩
theorem not_enc_parsed {X : HashInput} (hp : Parsed X) (L : EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32)
    (pad : Wots.RowPad) (hfit : Extract.msgFits L.1.lay m) : X≠Wots.encRow L.toWots m ctr pad := by
  rintro rfl
  exact not_parsed_of_encRow ⟨L,m,ctr,pad,hfit,rfl⟩ hp
end Coherent
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
open ClaudeWCT.W9.T3.Security.LargeResidual (msgVals)
open ClaudeWCT.W9.T3.Security.LargeCoupling (encRow_encLeaf)
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord→Digest} {nv : Message→Digest}
  {τ : Cell U→HashOutput} {a : AuxData}

theorem honestPrefix_iff {L : EncLeaf} {m : WCT9.LayerMsg} {ctr : BitVec 32} {pad : Wots.RowPad} :
    HonestPrefix vals a (Wots.encRow L.toWots m ctr pad) ↔
      Wots.encRow L.toWots m ctr pad=Wots.encRow L.toWots (msgVals vals L) ctr 0 ∧ PrefixRow a L ctr := by
  constructor
  · rintro ⟨L',ctr',hX,hp⟩
    obtain ⟨rfl,rfl⟩ := encRow_encLeaf hX
    exact ⟨hX,hp⟩
  · rintro ⟨hX,hp⟩;exact ⟨L,ctr,hX,hp⟩

theorem Coherent.referenceInput_eq (hcoh : Coherent U T vals nv τ a) {L : EncLeaf} {m : WCT9.LayerMsg}
    {ctr : BitVec 32} {pad : Wots.RowPad}
    (h : Wots.CanonicalRef.referenceInput T (Wots.CanonicalRef.sourceMessages T) L.toWots=
      some (Wots.encRow L.toWots m ctr pad)) :
    Wots.encRow L.toWots m ctr pad=Wots.encRow L.toWots (msgVals vals L) ctr 0 ∧ PrefixRow a L ctr := by
  obtain ⟨r,hr,hX⟩ := hcoh.referenceInput L _ h
  obtain ⟨_,hc⟩ := encRow_encLeaf hX
  obtain ⟨remaining,hctx,hsel⟩ := hcoh.sel_context L hr
  have hcap := (capSel_eq_some.mp hsel).2
  refine ⟨by rw [hX,←hc],?_,?_,?_⟩
  · rw [hctx];rfl
  · rw [hc,BitVec.toNat_ofNat]
    have hbound := r.1.isLt
    rw [Nat.mod_eq_of_lt (show r.1.val<2^32 by omega)]
    exact hcap
  · intro r' hr'
    rw [hr] at hr';cases hr'
    rw [hc,BitVec.toNat_ofNat]
    have hbound := r.1.isLt
    omega

theorem Coherent.residual_unparsed (h : Coherent U T vals nv τ a) (X : HashInput) (hX : X∈U)
    (hp : ¬Parsed X)
    (hc : ∀N,CanonGraph.Paired.Filtered.Used N → X≠CanonGraph.Paired.cell (secretsOf T) N (routerLabels vals a))
    (hn : ¬HonestPrefix vals a X) : T (.inl (.inr X))=τ ⟨X,hX⟩ := by
  exact (h.residual X hX hc hn).trans (rowPresent_unparsed hp _)
end Coherent
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue IsDigestRow dummyDigest State Probe Hit Charge Cell
  readState probeState stoppedState tickState disclosedState runWith_map mem_restrict card_restrict_ge low)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure effF_self adm_of_plain Adm famKnown famSeeds
  mem_famSeeds mem_famKnown)
open SigGolfCandidate.T3.Security.LargeCoupling (low_eq keep_guess_label keep_label keep_target
  keep_guess_target dummyDigest_decode')
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeResidual (WCoord Coord SeedIndex WFam wsplit_inr keygenDisclosed keygenCacheDisclosed encodingDisclosed_shape LowerLeaf msgVals msgSlots treeChild)
open ClaudeWCT.W9.T3.Security.LargeResidual (lookupVal)
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem case_unknownChild (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (hok : FamOK st) (X : HashInput) (hX : X ∈ U) (N : CanonGraph.Node) (hu : CanonGraph.Paired.Filtered.Used N)
    (hN : Extract.posOf X = some N.toPos) (hbN : N.base = N) (cs : Coord × Nat)
    (hfu : firstUnknown (LargeResidual.Paired.RouterState.known st) N = some cs) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (rowPresent X y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩) ws) := by
  obtain ⟨hcsm, hcsk⟩ := LargeResidual.Paired.firstUnknown_some hfu
  have hlow : ∀ n, N = .node n → n.1.lay ≠ 0 := by
    intro n hn hl
    subst hn
    exact hcsk (Known.base (Or.inl (LargeResidual.Paired.top_childSlots_keygen hl hcsm)))
  have hcap1 : ∀ n, N = .node n → trialCap n.1.lay n.1.level.val = 1 := fun n hn => trialCap_lower (hlow n hn) _
  have hsel : N.sel (routerLabels vals a) = N := LargeResidual.Paired.sel_of_single hbN hcap1
  have hvN : honestValue T (.inl N) = vals (.inl N) := by rw [hcoh.honestValue_node N hu, hcoh.selCoord N, hsel]
  have hiN : Extract.Paired.honestInput T N.toPos = cellValues N vals := by rw [hcoh.honestInput N hu, hsel]
  have hchild : ∀ cs ∈ childSlots N, honestValue T cs.1 = vals cs.1 := fun cs hc => by
    rw [hcoh.honestValue_used cs.1 (LargeResidual.Paired.childSlots_used N hu cs hc),
      LargeResidual.Paired.selCoordV_child hlow hc]
  have hne' : X ≠ cellValues N vals → ∀ M : CanonGraph.Node, CanonGraph.Paired.Filtered.Used M →
      M.toPos = N.toPos → X ≠ cellValues M vals := fun hXc M hMu hMpos heq =>
    hXc (by rw [LargeResidual.Paired.eq_of_single hbN hcap1 hMpos (hcoh.cell_pos hN hMu heq).2] at heq; exact heq)
  have hNact : ∀ n, N = .node n → LargeResidual.ActiveV vals n ∧ ∀ cs ∈ childSlots N, vals (LargeResidual.selCoordV vals cs.1) = vals cs.1 := by
    intro n hn
    refine ⟨⟨?_, fun j hj => ?_⟩, fun cs hc => by rw [LargeResidual.Paired.selCoordV_child hlow hc]⟩
    · rw [hcap1 n hn]; subst hn; rw [LargeResidual.Paired.nonce_zero_of_base hbN]; omega
    · subst hn; rw [LargeResidual.Paired.nonce_zero_of_base hbN] at hj; exact absurd hj (by omega)
  have hp : Parsed X := ⟨N,hu,hN⟩
  have hnd : ¬IsDigestRow X := fun hd => LargeResidual.Paired.not_parsed_of_digest hd hp
  have hadm : ∀ g ∈ (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).guess, ∀ parent,
      (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).hit = Hit.label parent → g.1 ≠ parent := by
    intro g hg parent hpar
    simp only [Option.mem_def, Option.some.injEq] at hg
    subst hg
    simp only [Hit.label.injEq] at hpar
    subst hpar
    exact fun h => LargeResidual.Paired.childSlots_ne N hu cs hcsm (Sum.inl.inj h)
  have heff : (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).effF ws.candidates =
      ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ := by
    refine effF_self _ _ ?_ (Or.inl rfl)
    intro g hg
    simp only [Option.mem_def, Option.some.injEq] at hg
    subst hg
    exact hrel.adm hlt hq hok cs.1 hcsk _ _ fun parent hpar =>
      ⟨hadm _ rfl parent hpar, ⟨N, by simp only [Hit.label.injEq] at hpar; exact hpar.symm⟩⟩
  have hcomp := observed_testReqP (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st) (ws := ws) aux
    (rowPresent X) (st.after X) X hX ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩
    (hrel.fresh X hX hnd)
  refine (congrArg (QueryOutcome U T vals nv τ a q mon st ws X) hcomp).mpr ?_
  rw [heff]
  have hct : ∀ y : HashOutput, ContactTest T (LargeResidual.Paired.RouterState.known st) X y ↔
      slotValue X cs.2 = vals cs.1 ∨ (X ≠ cellValues N vals ∧ Extract.Paired.proj N.toPos y = vals (.inl N)) := by
    intro y
    rw [LargeResidual.Paired.contactTest_parsed hu hN (hbN ▸ LargeResidual.Paired.noOver_base N), hvN, hiN]
    constructor
    · rintro (⟨cs', hcs', h⟩ | h)
      · rw [hfu] at hcs'
        cases hcs'
        exact Or.inl (by simpa only [hchild cs hcsm] using h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl ⟨cs,hfu,by simpa only [hchild cs hcsm] using h⟩
      · exact Or.inr h
  have hres : X ≠ cellValues N vals → T (.inl (.inr X)) = rowPresent X (τ ⟨X, hX⟩) := fun hXc =>
    hcoh.residual X hX (fun N' hu' => by rw [hcoh.cell N' hu']; exact hcoh.not_cell_parsed hN (hne' hXc) N' hu') (LargeResidual.Paired.not_prefix_parsed hp)
  have hcell : X ≠ cellValues N vals → ∀ N' : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N' → X = cellValues N' vals →
      ∀ cs ∈ childSlots N', (LargeResidual.Paired.RouterState.known st) cs.1 := fun hXc N' hu' hN' => absurd hN' (hcoh.not_cell_parsed hN (hne' hXc) N' hu')
  have henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1 := fun L ctr hL => absurd hL (LargeResidual.Paired.not_enc_parsed hp L _ ctr 0 (msgFits_msgVals vals L))
  by_cases hs : X ∈ st.seen
  · rw [if_neg (not_not.mpr hs)]
    have hXc : X ≠ cellValues N vals := fun heq => hcsk (hrel.seenCells X hs hX N hu heq cs hcsm)
    exact continue_read_callP (rowPresent X) hrel hlt X hX hnd (hres hXc) (fun h => h.1 hs) (hcell hXc) henc
  · rw [if_pos hs]
    by_cases hXc : X = cellValues N vals
    · have hslot : slotValue X cs.2 = vals cs.1 := by
        rw [hXc]
        exact slot_cellValues N vals hNact cs hcsm
      have hkeep : ¬(⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩) := by
        rw [keep_guess_label]
        intro h
        exact h.1 hslot.symm
      rw [if_neg hkeep]
      exact outcome_stop hrel hlt X _ ⟨hs, hX, (hct _).mpr (Or.inl hslot)⟩ rfl
    · have hTX := hres hXc
      by_cases hk : (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩)
      · rw [if_pos hk]
        have hk' := (keep_guess_label (Sum.elim vals nv) (.inl cs.1) (.inl (.inl N)) (slotValue X cs.2) _).mp hk
        have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) := by
          rintro ⟨-, -, hc⟩
          rw [hct, hTX, LargeResidual.Paired.proj_rowPresent hu hN] at hc
          rcases hc with h | h
          · exact hk'.1 h.symm
          · exact hk'.2 h.2.symm
        exact continue_probeP (rowPresent X) hrel hlt X hX _ hk hadm hTX hnd hnc (hcell hXc) henc
      · rw [if_neg hk]
        refine outcome_stop hrel hlt X _ ⟨hs, hX, (hct _).mpr ?_⟩ rfl
        rw [keep_guess_label, not_and_or, not_not, not_not] at hk
        rcases hk with h | h
        · exact Or.inl h.symm
        · exact Or.inr ⟨hXc, by rw [hTX, LargeResidual.Paired.proj_rowPresent hu hN]; exact h.symm⟩
theorem queryOutcome_congr {X : HashInput}
    {out out' : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U))} (h : out = out')
    (h' : QueryOutcome U T vals nv τ a q mon st ws X out') : QueryOutcome U T vals nv τ a q mon st ws X out := h ▸ h'
theorem lookupVal_map (f : Coord → Digest) (cs : List Coord) (c : Coord) (hc : c ∈ cs) :
    lookupVal (cs.map fun c => (c, f c)) c = f c := by
  induction cs with
  | nil => cases hc
  | cons d rest ih =>
      unfold lookupVal
      simp only [List.map_cons, List.find?_cons]
      by_cases hd : d = c
      · subst hd
        simp
      · simp only [hd, decide_false]
        exact ih ((List.mem_cons.mp hc).resolve_left (Ne.symm hd))
theorem discloseStates_counters (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) :
    (discloseStates U q (Sum.elim vals nv) s cs).counters = s.counters := by
  induction cs generalizing s with
  | nil => rfl
  | cons c rest ih => exact (ih _).trans rfl
theorem discloseStates_rows (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) :
    (discloseStates U q (Sum.elim vals nv) s cs).rows = s.rows := by
  induction cs generalizing s with
  | nil => rfl
  | cons c rest ih => exact (ih _).trans rfl
theorem discloseStates_candidates (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) (c : WCoord) :
    (discloseStates U q (Sum.elim vals nv) s cs).candidates c =
      if c ∈ cs.map Sum.inl then {Sum.elim vals nv c} else s.candidates c := by
  induction cs generalizing s with
  | nil => simp [discloseStates]
  | cons d rest ih =>
      change (discloseStates U q (Sum.elim vals nv)
        (disclosedState q s (.inl d) (Sum.elim vals nv (.inl d)) .none) rest).candidates c = _
      rw [ih]
      change (if c ∈ rest.map Sum.inl then {Sum.elim vals nv c}
        else Function.update s.candidates (.inl d) {Sum.elim vals nv (.inl d)} c) = _
      by_cases hr : c ∈ rest.map Sum.inl
      · rw [if_pos hr, if_pos (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hr)]
      · rw [if_neg hr]
        by_cases hd : c = .inl d
        · subst hd
          rw [Function.update_self, if_pos (by rw [List.map_cons]; exact List.mem_cons_self)]
        · rw [Function.update_of_ne hd, if_neg (by simp only [List.map_cons, List.mem_cons]; tauto)]
theorem Rel.discloseStates (hrel : Rel U T vals nv τ a q mon st ws) (cs : List Coord) (hk : ∀ c ∈ cs, (LargeResidual.Paired.RouterState.known st) c) :
    Rel U T vals nv τ a q mon st (discloseStates U q (Sum.elim vals nv) ws cs) := by
  have hc := discloseStates_counters (U := U) (q := q) (vals := vals) (nv := nv) cs ws
  have hr := discloseStates_rows (U := U) (q := q) (vals := vals) (nv := nv) cs ws
  refine ⟨hrel.disclosed, hrel.seen, hrel.calls, by rw [hc]; exact hrel.wcalls, by rw [hc]; exact hrel.digests,
    hrel.contact, by rw [hc]; exact hrel.probes, hrel.budget, ?_, ?_, by rw [hr]; exact hrel.rowsEq,
    by rw [hr]; exact hrel.rowsSeen, hrel.seenCells, hrel.seenEnc⟩
  · intro c
    rw [discloseStates_candidates]
    split_ifs
    · exact Finset.mem_singleton_self _
    · exact hrel.mem c
  · intro c hck
    rw [discloseStates_candidates, hc]
    rw [if_neg (fun hm => hck (by
      obtain ⟨d, hd, hdc⟩ := List.mem_map.mp hm
      have hdc' := Sum.inl.inj hdc
      subst hdc'
      exact hk _ hd))]
    exact hrel.hidden c hck
theorem case_knownChildren (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (N : CanonGraph.Node) (hu : CanonGraph.Paired.Filtered.Used N)
    (hN : Extract.posOf X = some N.toPos) (hbN : N.base = N)
    (hfu : firstUnknown (LargeResidual.Paired.RouterState.known st) N = none) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (do
      let pairs ← discloseAll U (cellDepsP N)
      if X = cellFrom (cellNode N (lookupVal pairs) X) (lookupVal pairs) then do
        let v ← discloseReq U (.inl (.inl (cellNode N (lookupVal pairs) X))) .call
        pure (CanonGraph.Paired.presentEquiv (cellNode N (lookupVal pairs) X)
          (ChainGraph.joinOutput v (a.high (cellNode N (lookupVal pairs) X))), st.after X)
      else (fun y => (rowPresent X y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨none, .label (.inl (LargeResidual.selCoordV (lookupVal pairs) (.inl N)))⟩) ws) := by
  have hall := LargeResidual.Paired.firstUnknown_none hfu
  have hp : Parsed X := ⟨N,hu,hN⟩
  have hnd : ¬IsDigestRow X := fun hd => LargeResidual.Paired.not_parsed_of_digest hd hp
  have hN0 : LargeResidual.Paired.NoOver N := hbN ▸ LargeResidual.Paired.noOver_base N
  have hkN : ∀ M : CanonGraph.Node, M.toPos = N.toPos → LargeResidual.Paired.NoOver M →
      (LargeResidual.Paired.RouterState.known st) (.inl M) :=
    fun M hM hM0 => Known.node (by rw [LargeResidual.Paired.childSlots_eq_of hM hM0 hN0]; exact hall)
  have hkc : ∀ c ∈ cellDepsP N, (LargeResidual.Paired.RouterState.known st) c :=
    LargeResidual.Paired.cellDepsP_known st hall
  have hrel1 := hrel.discloseStates _ hkc
  rw [observed_discloseAll]
  have hv0c : ∀ c ∈ cellDepsP N,
      lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c))) c = vals c :=
    fun c hc => lookupVal_map (fun c => Sum.elim vals nv (.inl c)) _ c hc
  have hcf : ∀ M : CanonGraph.Node, M.toPos = N.toPos →
      cellFrom M (lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c)))) = cellValues M vals := by
    intro M hM
    change cellValues M _ = cellValues M vals
    apply cellValues_congr
    intro c hc
    exact hv0c c (LargeResidual.Paired.cellDepsP_sub hM hbN c hc)
  have henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1 := fun L ctr hL => absurd hL (LargeResidual.Paired.not_enc_parsed hp L _ ctr 0 (msgFits_msgVals vals L))
  obtain hex | hex := Classical.em (∃ M : CanonGraph.Node, CanonGraph.Paired.Filtered.Used M ∧ M.toPos = N.toPos ∧
      X = cellFrom M (lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c)))))
  · have hM := Classical.choose_spec hex
    have hcn : cellNode N (lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c)))) X =
        Classical.choose hex := by
      unfold cellNode; exact @dif_pos _ _ hex _ _ _
    rw [hcn]
    obtain ⟨hMu, hMpos, hMX⟩ := hM
    rw [if_pos hMX, observed_discloseReq, observed_pure]
    have hXc : X = cellValues (Classical.choose hex) vals := hMX.trans (hcf _ hMpos)
    have hTX : T (.inl (.inr X)) = routerLabels vals a (Classical.choose hex) := by
      have h1 := hcoh.honest_answer _ hMu
      rwa [← hXc] at h1
    have hnp : ¬PhantomAt (Classical.choose hex) (routerLabels vals a) := (hcoh.cell_pos hN hMu hXc).2
    have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) := by
      rintro ⟨-, -, hc⟩
      rw [LargeResidual.Paired.contactTest_parsed hu hN hN0, hfu] at hc
      rcases hc with ⟨cs, hcs, -⟩ | ⟨hne, hval⟩
      · cases hcs
      · by_cases hMs : Classical.choose hex = N.sel (routerLabels vals a)
        · apply hne
          rw [hcoh.honestInput N hu, ← hMs, ← hXc]
        · apply hcoh.capOk
          refine CanonGraph.rejected_hit_capFail hMpos hnp hMs ?_
          rw [hTX, hcoh.honestValue_sel N hu] at hval
          exact hval
    apply outcome_continue hrel hlt X _ hnc
    · rw [LargeResidual.RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
      congr 3
      rw [hTX]
      rfl
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1 = st.calls + 1
      rw [discloseStates_counters, hrel.wcalls]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.mass = ws.counters.mass + _
      rw [discloseStates_counters, if_neg (fun h => hnd h.2), Nat.add_zero]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤ (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1
      rw [discloseStates_counters]
      have := hrel.probes; omega
    · intro c
      show Sum.elim vals nv c ∈ Function.update (discloseStates U q (Sum.elim vals nv) ws _).candidates
        (.inl (.inl (Classical.choose hex))) {Sum.elim vals nv (.inl (.inl (Classical.choose hex)))} c
      by_cases hc : c = .inl (.inl (Classical.choose hex))
      · subst hc
        rw [Function.update_self]
        exact Finset.mem_singleton_self _
      · rw [Function.update_of_ne hc]
        exact hrel1.mem c
    · intro c hck
      show 2 ^ 128 - (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤
        (Function.update (discloseStates U q (Sum.elim vals nv) ws _).candidates (.inl (.inl (Classical.choose hex)))
          {Sum.elim vals nv (.inl (.inl (Classical.choose hex)))} (.inl c)).card
      rw [Function.update_of_ne (fun h => hck (by rw [Sum.inl.inj h]; exact hkN _ hMpos (LargeResidual.Paired.noOver_of_not_phantom hnp)))]
      exact hrel1.hidden c hck
    · intro row v hv
      exact hrel1.rowsEq row v hv
    · intro row v hv
      exact Or.inr (hrel1.rowsSeen row v hv)
    · intro _ N' hu' hN'
      rw [LargeResidual.Paired.childSlots_eq_of (hcoh.cell_pos hN hu' hN').1
        (LargeResidual.Paired.noOver_of_not_phantom (hcoh.cell_pos hN hu' hN').2) hN0]
      exact hall
    · exact fun _ => henc
  · have hcn : cellNode N (lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c)))) X = N := by
      unfold cellNode; exact @dif_neg _ _ hex _ _ _
    rw [hcn]
    have hXN : ¬ X = cellFrom N (lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c)))) :=
      fun h => hex ⟨N, hu, rfl, h⟩
    rw [if_neg hXN]
    have hsc : LargeResidual.selCoordV (lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c)))) (.inl N) =
        .inl (N.sel (routerLabels vals a)) := by
      rw [← hcoh.selCoord N]
      apply LargeResidual.selCoordV_congr
      intro n hn h1 j hj
      have hN' : N = .node n := Sum.inl.inj hn
      subst hN'
      exact hv0c _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (LargeResidual.mem_trialDeps h1 hj))))
    rw [hsc]
    have hSu : CanonGraph.Paired.Filtered.Used (N.sel (routerLabels vals a)) :=
      (CanonGraph.Paired.Filtered.used_iff_bounded _).2 (by
        rw [CanonGraph.toPos_sel]; exact (CanonGraph.Paired.Filtered.used_iff_bounded N).1 hu)
    have hne' : ∀ M : CanonGraph.Node, CanonGraph.Paired.Filtered.Used M → M.toPos = N.toPos → X ≠ cellValues M vals :=
      fun M hMu hMpos h => hex ⟨M, hMu, hMpos, h.trans (hcf M hMpos).symm⟩
    have hTX : T (.inl (.inr X)) = rowPresent X (τ ⟨X, hX⟩) :=
      hcoh.residual X hX (fun N' hu' => by rw [hcoh.cell N' hu']; exact hcoh.not_cell_parsed hN hne' N' hu') (LargeResidual.Paired.not_prefix_parsed hp)
    have hct : ∀ y : HashOutput, ContactTest T (LargeResidual.Paired.RouterState.known st) X y ↔
        Extract.Paired.proj N.toPos y = vals (.inl (N.sel (routerLabels vals a))) := by
      intro y
      rw [LargeResidual.Paired.contactTest_parsed hu hN hN0, hcoh.honestValue_node N hu, hcoh.selCoord N, hfu]
      simp only [reduceCtorEq, false_and, exists_false, false_or]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rw [hcoh.honestInput N hu]
        exact hne' _ hSu (CanonGraph.toPos_sel _ N)
    have hcell : ∀ N' : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N' → X = cellValues N' vals → ∀ cs ∈ childSlots N', (LargeResidual.Paired.RouterState.known st) cs.1 :=
      fun N' hu' hN' => absurd hN' (hcoh.not_cell_parsed hN hne' N' hu')
    have hfresh : X ∉ st.seen → (discloseStates U q (Sum.elim vals nv) ws (cellDepsP N)).rows ⟨X, hX⟩ = none :=
      hrel1.fresh X hX hnd
    have hcomp := observed_testReqP (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st)
      (ws := discloseStates U q (Sum.elim vals nv) ws (cellDepsP N)) aux
      (rowPresent X) (st.after X) X hX ⟨none, .label (.inl (.inl (N.sel (routerLabels vals a))))⟩ hfresh
    refine queryOutcome_congr hcomp ?_
    rw [effF_self _ _ (by intro g hg; cases hg)]
    have hadm : ∀ g ∈ (⟨none, .label (.inl (.inl (N.sel (routerLabels vals a))))⟩ : Probe WCoord).guess, ∀ parent,
        (⟨none, .label (.inl (.inl (N.sel (routerLabels vals a))))⟩ : Probe WCoord).hit = Hit.label parent → g.1 ≠ parent := by
      intro g hg; cases hg
    by_cases hs : X ∈ st.seen
    · rw [if_neg (not_not.mpr hs)]
      exact continue_read_callP (rowPresent X) hrel1 hlt X hX hnd hTX (fun h => h.1 hs) hcell henc
    · rw [if_pos hs]
      by_cases hk : (⟨none, .label (.inl (.inl (N.sel (routerLabels vals a))))⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩)
      · rw [if_pos hk]
        have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) := by
          rintro ⟨-, -, hc⟩
          rw [hct, hTX, LargeResidual.Paired.proj_rowPresent hu hN] at hc
          exact ((keep_label (Sum.elim vals nv) _ _).mp hk) hc.symm
        exact continue_probeP (rowPresent X) hrel1 hlt X hX _ hk hadm hTX hnd hnc hcell henc
      · rw [if_neg hk]
        refine outcome_stop hrel1 hlt X _ ⟨hs, hX, (hct _).mpr ?_⟩ rfl
        rw [keep_label, not_not] at hk
        rw [hTX, LargeResidual.Paired.proj_rowPresent hu hN]
        exact hk.symm

end Cases
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue IsDigestRow dummyDigest State Probe Hit Charge Cell
  readState probeState stoppedState tickState disclosedState runWith_map mem_restrict card_restrict_ge low)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure effF_self adm_of_plain Adm famKnown famSeeds
  mem_famSeeds mem_famKnown)
open SigGolfCandidate.T3.Security.LargeCoupling (low_eq keep_guess_label keep_label keep_target
  keep_guess_target dummyDigest_decode')
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeResidual (WCoord Coord SeedIndex WFam wsplit_inr keygenDisclosed keygenCacheDisclosed encodingDisclosed_shape LowerLeaf msgVals msgSlots treeChild)
open ClaudeWCT.W9.T3.Security.LargeResidual (lookupVal encodingHit keep_encodingHit)
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem case_phantom (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (hnp : ¬Parsed X) (n : TreeNode) (hXn : X = phantom n) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (do
      let pairs ← discloseAll U (LargeResidual.trialDeps n)
      if LargeResidual.ActiveV (lookupVal pairs) n then (fun y => (y, st.after X)) <$> readReq U ⟨X, hX⟩ .call
      else do
        let v ← discloseReq U (.inl (.inl (.node n))) .call
        pure (CanonGraph.Paired.presentEquiv (.node n) (ChainGraph.joinOutput v (a.high (.node n))), st.after X)) ws) := by
  have hlen : X.length ≠ 64 := by rw [hXn, phantom_length]; decide
  have hne : ¬LargeResidual.EncRow X := by
    rintro ⟨L, m, ctr, pad, -, rfl⟩
    exact hlen (ClaudeWCT.W9.T3.Security.Wots.Enc.encRow_length _ _ _ _)
  have hnd : ¬IsDigestRow X := by
    rintro ⟨rho, m, c, hd⟩
    apply hlen
    rw [hd, Cost.pad64_length]
    simp [digestInput, SphincsSecurity.bytesLE_length]
  have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) :=
    fun h => LargeResidual.Paired.contactTest_other hnp hne h.2.2
  have hkc : ∀ c ∈ LargeResidual.trialDeps n, (LargeResidual.Paired.RouterState.known st) c :=
    fun c hc => Known.base (Or.inl (LargeResidual.Paired.trialDeps_keygen hc))
  have hrel1 := hrel.discloseStates _ hkc
  rw [observed_discloseAll]
  have hact : LargeResidual.ActiveV (lookupVal ((LargeResidual.trialDeps n).map fun c => (c, Sum.elim vals nv (.inl c)))) n ↔ LargeResidual.ActiveV vals n :=
    LargeResidual.activeV_congr (fun h1 j hj => lookupVal_map (fun c => Sum.elim vals nv (.inl c)) _ _ (LargeResidual.mem_trialDeps h1 hj))
  have henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1 :=
    fun L' ctr' hL' => absurd ⟨L', _, ctr', 0, msgFits_msgVals vals L', hL'⟩ hne
  by_cases ha : LargeResidual.ActiveV vals n
  · rw [if_pos (hact.mpr ha)]
    have hnot : ∀ N' : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N' → X ≠ cellValues N' vals := by
      intro N' hu' heq
      obtain ⟨rfl, hn⟩ := hcoh.cell_phantom hu' (hXn.symm.trans heq)
      exact hn ((hcoh.activeV_iff n).mp ha)
    have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
      hcoh.residual_unparsed X hX hnp (fun N' hu' => by rw [hcoh.cell N' hu']; exact hnot N' hu')
        (LargeResidual.Paired.not_prefix_enc hne)
    rw [observed_map, ← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
    exact continue_read_call hrel1 hlt X hX hnd hTX hnc (fun N' hu' hN' => absurd hN' (hnot N' hu')) henc
  · rw [if_neg (fun h => ha (hact.mp h)), observed_discloseReq, observed_pure]
    have hXc : X = cellValues (.node n) vals := by
      rw [hXn]
      show phantom n = LargeResidual.cellValues (.node n) vals
      simp only [LargeResidual.cellValues, if_neg ha]
    have hTX : T (.inl (.inr X)) = routerLabels vals a (.node n) := by
      rw [hXc]; exact hcoh.honest_answer _ trivial
    have hslots : ∀ cs ∈ childSlots (.node n), (LargeResidual.Paired.RouterState.known st) cs.1 := by
      intro cs hcs
      by_cases hov : trialCap n.1.lay n.1.level.val ≤ n.1.nonce.val
      · simp [childSlots, LargeResidual.childSlots, hov] at hcs
      · have h1 : trialCap n.1.lay n.1.level.val ≠ 1 := by
          intro h1
          apply ha
          refine ⟨by omega, fun j hj => ?_⟩
          rw [h1] at hov; exact absurd hj (by omega)
        exact Known.base (Or.inl (LargeResidual.Paired.top_childSlots_keygen (LargeResidual.Paired.lay_zero_of_cap h1) hcs))
    have hkN : (LargeResidual.Paired.RouterState.known st) (.inl (.node n)) := Known.node hslots
    apply outcome_continue hrel hlt X _ hnc
    · rw [LargeResidual.RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
      congr 3
      rw [hTX]
      rfl
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1 = st.calls + 1
      rw [discloseStates_counters, hrel.wcalls]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.mass = ws.counters.mass + _
      rw [discloseStates_counters, if_neg (fun h => hnd h.2), Nat.add_zero]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤ (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1
      rw [discloseStates_counters]
      have := hrel.probes; omega
    · intro c
      show Sum.elim vals nv c ∈ Function.update (discloseStates U q (Sum.elim vals nv) ws _).candidates
        (.inl (.inl (.node n))) {Sum.elim vals nv (.inl (.inl (.node n)))} c
      by_cases hc : c = .inl (.inl (.node n))
      · subst hc
        rw [Function.update_self]
        exact Finset.mem_singleton_self _
      · rw [Function.update_of_ne hc]
        exact hrel1.mem c
    · intro c hck
      show 2 ^ 128 - (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤
        (Function.update (discloseStates U q (Sum.elim vals nv) ws _).candidates (.inl (.inl (.node n)))
          {Sum.elim vals nv (.inl (.inl (.node n)))} (.inl c)).card
      rw [Function.update_of_ne (fun h => hck (by rw [Sum.inl.inj h]; exact hkN))]
      exact hrel1.hidden c hck
    · intro row v hv
      exact hrel1.rowsEq row v hv
    · intro row v hv
      exact Or.inr (hrel1.rowsSeen row v hv)
    · intro _ N' hu' hN'
      obtain ⟨rfl, -⟩ := hcoh.cell_phantom hu' (hXn.symm.trans hN')
      exact hslots
    · exact fun _ => henc

theorem case_enc_known (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (L : EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32)
    (pad : Wots.RowPad) (hfit : Extract.msgFits L.1.lay m) (hXe : X = Wots.encRow L.toWots m ctr pad)
    :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (do
      let pairs ← discloseAll U ((msgSlots L).map Prod.fst)
      if X = Wots.encRow L.toWots (msgVals (lookupVal pairs) L) ctr 0 ∧ PrefixRow a L ctr then do
        tickReq U .call
        pure (prefixValue a L ctr, st.after X)
      else if (a.sel L).isSome then
        (fun y => (y,st.after X)) <$> testReq U (decide (X ∉ st.seen)) ⟨X,hX⟩ ⟨none,encodingHit L.1.lay (refDigest a L)⟩
      else (fun y => (y,st.after X)) <$> readReq U ⟨X,hX⟩ .call) ws) := by
  have hph : ∀ n, X ≠ phantom n :=
    LargeResidual.Paired.ne_phantom_of_length (by rw [hXe]; exact ClaudeWCT.W9.T3.Security.Wots.Enc.encRow_length _ _ _ _)
  have hall : ∀cs∈msgSlots L,LargeResidual.Paired.RouterState.known st cs.1 :=
    LargeResidual.Paired.RouterState.msgSlot_known st L
  have hnp : ¬Parsed X := by rw [hXe]; exact LargeResidual.Paired.not_parsed_of_encRow ⟨L, m, ctr, pad, hfit, rfl⟩
  have hnd : ¬IsDigestRow X := by rw [hXe]; exact encRow_not_digest L m ctr pad
  have hnext : st.next U X (T (.inl (.inr X))) = st.after X := LargeResidual.RouterState.next_of_not U st X _ (fun h => hnd h.2)
  have hkc : ∀ c ∈ (msgSlots L).map Prod.fst, (LargeResidual.Paired.RouterState.known st) c := by
    intro c hc
    obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc
    exact hall cs hcs
  have hrel1 := hrel.discloseStates _ hkc
  rw [observed_discloseAll]
  have hmv : msgVals (lookupVal (((msgSlots L).map Prod.fst).map fun c => (c, Sum.elim vals nv (.inl c)))) L =
      msgVals vals L :=
    msgVals_congr _ _ L (fun cs hcs =>
      lookupVal_map (fun c => Sum.elim vals nv (.inl c)) _ cs.1 (List.mem_map.mpr ⟨cs, hcs, rfl⟩))
  rw [hmv]
  have hct : ∀y : HashOutput,ContactTest T (LargeResidual.Paired.RouterState.known st) X y ↔
      (a.sel L).isSome ∧
        Wots.CanonicalRef.referenceInput T (Wots.CanonicalRef.sourceMessages T) L.toWots≠some X ∧
        Wots.CanonicalRef.NotSearched T (Wots.CanonicalRef.sourceMessages T) L.toWots X ∧
        WCT9.encodingTarget L.1.lay (refDigest a L) y=refDigest a L := by
    intro y
    rw [hXe,LargeResidual.Paired.contactTest_enc hfit,←hXe]
    have hs : Wots.CanonicalRef.referenceSearch T (Wots.CanonicalRef.sourceMessages T) L.toWots≠none ↔
        (a.sel L).isSome := by
      rw [←Option.isSome_iff_ne_none,hcoh.search_isSome]
    rw [hs]
    constructor
    · rintro ⟨hsel,hi,hns,hd⟩
      exact ⟨hsel,hi,hns,(hcoh.canDecode_ref L hsel _).mp hd⟩
    · rintro ⟨hsel,hi,hns,hd⟩
      exact ⟨hsel,hi,hns,(hcoh.canDecode_ref L hsel _).mpr hd⟩
  have hcell : ∀ N' : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N' → X = cellValues N' vals → ∀ cs ∈ childSlots N', (LargeResidual.Paired.RouterState.known st) cs.1 :=
    fun N' hu' hN' => absurd hN' (LargeResidual.Paired.not_cell_unparsed hcoh hnp hph N' hu')
  have henc : ∀ (L' : EncLeaf) (ctr' : BitVec 32), X = Wots.encRow L'.toWots (msgVals vals L') ctr' 0 →
      ∀ cs ∈ msgSlots L', (LargeResidual.Paired.RouterState.known st) cs.1 := by
    intro L' ctr' hL'
    rw [hXe] at hL'
    obtain ⟨rfl, -⟩ := encRow_encLeaf hL'
    exact hall
  by_cases hpre : X = Wots.encRow L.toWots (msgVals vals L) ctr 0 ∧ PrefixRow a L ctr
  · rw [if_pos hpre, observed_tickReq, observed_pure]
    have hTX : T (.inl (.inr X)) = prefixValue a L ctr := by
      rw [hpre.1]
      exact hcoh.prefixRow L ctr hpre.2
    have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) := by
      -- A searched honest row is never an encoding contact (path-aware floors: see `NotSearched`).
      rintro ⟨-, -, hc⟩
      rw [hct] at hc
      obtain ⟨hsel, -, hns, -⟩ := hc
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsel
      obtain ⟨ds, hd⟩ := hcoh.sel_valid L hr
      have hfound : Wots.CanonicalRef.referenceSearch T (Wots.CanonicalRef.sourceMessages T) L.toWots =
          some (BitVec.ofNat 32 r.1.val, ds, WCT9.lowSelected L.1.lay (a.rows L r.1)) := by
        rw [hcoh.search, hr]
        simp only [Option.bind_some, hd, Option.map_some]
      have hle : ctr.toNat ≤ (BitVec.ofNat 32 r.1.val).toNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := r.1.isLt; omega)]
        exact hpre.2.2.2 r hr
      have hctr : BitVec.ofNat 32 ctr.toNat = ctr := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt ctr.isLt
      apply hns _ hfound ctr.toNat hle
      rw [hpre.1, hcoh.leafMsg L, hctr]
    apply outcome_continue hrel1 hlt X _ hnc
      (tickState q (discloseStates U q (Sum.elim vals nv) ws ((msgSlots L).map Prod.fst)) .call)
    · rw [hnext, hTX]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1 = st.calls + 1
      rw [discloseStates_counters, hrel.wcalls]
    · show (discloseStates U q (Sum.elim vals nv) ws ((msgSlots L).map Prod.fst)).counters.mass =
        (discloseStates U q (Sum.elim vals nv) ws ((msgSlots L).map Prod.fst)).counters.mass + _
      rw [if_neg (fun h => hnd h.2), Nat.add_zero]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤
        (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1
      rw [discloseStates_counters]
      have := hrel.probes; omega
    · exact hrel1.mem
    · exact hrel1.hidden
    · exact hrel1.rowsEq
    · intro row v hv; exact Or.inr (hrel1.rowsSeen row v hv)
    · exact fun _ => hcell
    · exact fun _ => henc
  · rw [if_neg hpre]
    have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
      hcoh.residual_unparsed X hX hnp (fun N' hu' => by rw [hcoh.cell N' hu']; exact LargeResidual.Paired.not_cell_unparsed hcoh hnp hph N' hu')
        (by rw [hXe, LargeResidual.Paired.honestPrefix_iff, ← hXe]; exact hpre)
    have hri : Wots.CanonicalRef.referenceInput T (Wots.CanonicalRef.sourceMessages T) L.toWots ≠ some X := by
      rw [hXe]
      intro h
      exact hpre (by rw [hXe]; exact hcoh.referenceInput_eq h)
    by_cases hsel : (a.sel L).isSome
    · rw [if_pos hsel]
      have hfresh := hrel1.fresh X hX hnd
      have hcomp := observed_testReq (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st)
        (ws := discloseStates U q (Sum.elim vals nv) ws ((msgSlots L).map Prod.fst)) aux
        (st.after X) X hX ⟨none, encodingHit L.1.lay (refDigest a L)⟩ hfresh
      refine queryOutcome_congr hcomp ?_
      rw [effF_self _ _ (by intro g hg; cases hg)]
      have hadm : ∀ g ∈ (⟨none, encodingHit L.1.lay (refDigest a L)⟩ : Probe WCoord).guess, ∀ parent,
          (⟨none, encodingHit L.1.lay (refDigest a L)⟩ : Probe WCoord).hit = Hit.label parent → g.1 ≠ parent := by
        intro g hg; cases hg
      by_cases hs : X ∈ st.seen
      · rw [if_neg (not_not.mpr hs)]
        exact continue_read_call hrel1 hlt X hX hnd hTX (fun h => h.1 hs) hcell henc
      · rw [if_pos hs]
        by_cases hk : (⟨none, encodingHit L.1.lay (refDigest a L)⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩)
        · rw [if_pos hk]
          have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) := by
            rintro ⟨-, -, hc⟩
            rw [hct, hTX] at hc
            exact ((keep_encodingHit (Sum.elim vals nv) _ _ _).mp hk) hc.2.2.2.symm
          exact continue_probe hrel1 hlt X hX _ hk hadm hTX hnd hnc hcell henc
        · rw [if_neg hk]
          have hns : Wots.CanonicalRef.NotSearched T (Wots.CanonicalRef.sourceMessages T) L.toWots X := by
            intro found hfound c hc heq
            apply hpre
            obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsel
            obtain ⟨ds, hd⟩ := hcoh.sel_valid L hr
            have hfound' : Wots.CanonicalRef.referenceSearch T (Wots.CanonicalRef.sourceMessages T) L.toWots =
                some (BitVec.ofNat 32 r.1.val, ds, WCT9.lowSelected L.1.lay (a.rows L r.1)) := by
              rw [hcoh.search, hr]
              simp only [Option.bind_some, hd, Option.map_some]
            rw [hfound'] at hfound
            cases hfound
            have hr1 : (BitVec.ofNat 32 r.1.val).toNat = r.1.val := by
              rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := r.1.isLt; omega)
            rw [hr1] at hc
            rw [hXe] at heq
            have hc' := (encRow_encLeaf heq).2
            obtain ⟨remaining, hctx, hselAt⟩ := hcoh.sel_context L hr
            have hcap := (capSel_eq_some.mp hselAt).2
            have hctrc : ctr.toNat = c := by
              rw [hc', BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := r.1.isLt; omega)
            refine ⟨?_, by rw [hctx]; rfl, by omega, fun r' hr' => ?_⟩
            · rw [hXe, heq, hcoh.leafMsg L, hc']
            · rw [hr] at hr'; cases hr'; omega
          refine outcome_stop hrel1 hlt X _ ⟨hs, hX, (hct _).mpr ⟨hsel,hri,hns,?_⟩⟩ rfl
          rw [keep_encodingHit, not_not] at hk
          rw [hTX]
          exact hk.symm
    · rw [if_neg hsel,observed_map]
      rw [←bind_pure (readReq U ⟨X,hX⟩ .call),observed_readReq,observed_pure,map_pure]
      exact continue_read_call hrel1 hlt X hX hnd hTX
        (fun hc => hsel ((hct _).mp hc.2.2).1) hcell henc

end Cases
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue IsDigestRow dummyDigest State Probe Hit Charge Cell
  readState probeState stoppedState tickState disclosedState runWith_map mem_restrict card_restrict_ge low)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure effF_self adm_of_plain Adm famKnown famSeeds
  mem_famSeeds mem_famKnown)
open SigGolfCandidate.T3.Security.LargeCoupling (low_eq keep_guess_label keep_label keep_target
  keep_guess_target dummyDigest_decode')
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeResidual (WCoord Coord SeedIndex WFam wsplit_inr keygenDisclosed keygenCacheDisclosed encodingDisclosed_shape LowerLeaf msgVals msgSlots treeChild)
open ClaudeWCT.W9.T3.Security.LargeResidual (lookupVal EncRow)
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem case_digest (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (hd : IsDigestRow X) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (y, if st.Fresh X then { st.after X with births := (X, y) :: st.births } else st.after X)) <$>
        readReq U ⟨X, hX⟩ .mass) ws) := by
  have hnp := LargeResidual.Paired.not_parsed_of_digest hd
  have hph : ∀ n, X ≠ phantom n := by
    obtain ⟨rho, m, c, hdX⟩ := hd
    exact LargeResidual.Paired.ne_phantom_of_length (by
      rw [hdX, Cost.pad64_length]; simp [digestInput, SphincsSecurity.bytesLE_length])
  have hne : ¬LargeResidual.EncRow X := by
    rintro ⟨L, m, ctr, pad, -, rfl⟩
    exact encRow_not_digest L m ctr pad hd
  have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
    hcoh.residual_unparsed X hX hnp (fun N' hu' => by rw [hcoh.cell N' hu']; exact LargeResidual.Paired.not_cell_unparsed hcoh hnp hph N' hu') (LargeResidual.Paired.not_prefix_enc hne)
  rw [observed_map, ← bind_pure (readReq U ⟨X, hX⟩ .mass), observed_readReq, observed_pure, map_pure]
  have h := continue_read hrel hlt X hX .mass (Or.inr ⟨rfl, hd⟩) hTX
    (fun h => LargeResidual.Paired.contactTest_other hnp hne h.2.2)
    (fun N' hu' hN' => absurd hN' (LargeResidual.Paired.not_cell_unparsed hcoh hnp hph N' hu'))
    (fun L' ctr' hL' => absurd ⟨L', _, ctr', 0, msgFits_msgVals vals L', hL'⟩ hne)
  have heq : (if st.Fresh X then { st.after X with births := (X, τ ⟨X, hX⟩) :: st.births } else st.after X) =
      st.next U X (τ ⟨X, hX⟩) := by
    unfold LargeResidual.RouterState.next
    by_cases hf : st.Fresh X
    · rw [if_pos hf, if_pos ⟨hX, hd, hf⟩]
    · rw [if_neg hf, if_neg (fun h' => hf h'.2.2)]
  rw [← heq] at h
  exact h
theorem case_other (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (hnp : ¬Parsed X) (hne : ¬LargeResidual.EncRow X) (hnd : ¬IsDigestRow X)
    (hph : ∀ n, X ≠ phantom n) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (y, st.after X)) <$> readReq U ⟨X, hX⟩ .call) ws) := by
  have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
    hcoh.residual_unparsed X hX hnp (fun N' hu' => by rw [hcoh.cell N' hu']; exact LargeResidual.Paired.not_cell_unparsed hcoh hnp hph N' hu') (LargeResidual.Paired.not_prefix_enc hne)
  rw [observed_map, ← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
  exact continue_read_call hrel hlt X hX hnd hTX (fun h => LargeResidual.Paired.contactTest_other hnp hne h.2.2)
    (fun N' hu' hN' => absurd hN' (LargeResidual.Paired.not_cell_unparsed hcoh hnp hph N' hu'))
    (fun L' ctr' hL' => absurd ⟨L', _, ctr', 0, msgFits_msgVals vals L', hL'⟩ hne)
theorem routeQuery_observed (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (hok : FamOK st) (X : HashInput) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (observedRun aux q (Sum.elim vals nv) τ (routeQuerySelected U a st X) ws) := by
  unfold routeQuerySelected
  dsimp only
  by_cases hX : X ∈ U
  · rw [dif_pos hX]
    by_cases hp : Parsed X
    · rw [dif_pos hp]
      have hN := Classical.choose_spec hp
      have hu : CanonGraph.Paired.Filtered.Used (Classical.choose hp).base := LargeResidual.Paired.used_base hN.1
      have hpos : Extract.posOf X = some (Classical.choose hp).base.toPos := by
        rw [CanonGraph.toPos_base]; exact hN.2
      split
      · rename_i cs hfu
        exact case_unknownChild aux hcoh hrel hlt hq hok X hX _ hu hpos (LargeResidual.Paired.base_base _) cs hfu
      · rename_i hfu
        exact case_knownChildren aux hcoh hrel hlt X hX _ hu hpos (LargeResidual.Paired.base_base _) hfu
    · rw [dif_neg hp]
      by_cases hph : ∃ n : TreeNode, X = phantom n
      · rw [dif_pos hph]
        exact case_phantom aux hcoh hrel hlt X hX hp _ (Classical.choose_spec hph)
      rw [dif_neg hph]
      by_cases he : LargeResidual.EncRow X
      · rw [dif_pos he]
        have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec he)))
        exact case_enc_known aux hcoh hrel hlt X hX _ _ _ _ hspec.1 hspec.2
      · rw [dif_neg he]
        by_cases hd : IsDigestRow X
        · rw [if_pos hd]
          exact case_digest aux hcoh hrel hlt X hX hd
        · rw [if_neg hd]
          exact case_other aux hcoh hrel hlt X hX hp he hd (fun n h => hph ⟨n, h⟩)
  · rw [dif_neg hX]
    exact case_outside aux hcoh hrel hlt X hX

end Cases
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

end
-- ==== merged from T3_Secc_LargeCouplingSigning ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingSigning : DecidableEq T3.Cache := Classical.decEq _
structure ReadsOnly {U : Finset HashInput} (τ : Cell U → HashOutput) (ws ws' : LargeResidual.State WCoord (Cell U)) :
    Prop where
  candidates : ws'.candidates = ws.candidates
  counters : ws'.counters = ws.counters
  rows : ∀ row v, ws'.rows row = some v → ws.rows row = some v ∨ (IsDigestRow row.val ∧ v = τ row)
theorem ReadsOnly.refl {U : Finset HashInput} (τ : Cell U → HashOutput) (ws : LargeResidual.State WCoord (Cell U)) :
    ReadsOnly τ ws ws :=
  ⟨rfl, rfl, fun _ _ h => Or.inl h⟩
theorem ReadsOnly.trans {U : Finset HashInput} {τ : Cell U → HashOutput} {ws ws' ws'' : LargeResidual.State WCoord (Cell U)}
    (h1 : ReadsOnly τ ws ws') (h2 : ReadsOnly τ ws' ws'') : ReadsOnly τ ws ws'' := by
  refine ⟨h2.candidates.trans h1.candidates, h2.counters.trans h1.counters, fun row v hv => ?_⟩
  rcases h2.rows row v hv with h | h
  · exact h1.rows row v h
  · exact Or.inr h
section Search
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (labels : WCoord → Digest) (τ : Cell U → HashOutput) (a : AuxData)
theorem digestRow_isDigest (rho : Digest) (m : Message) (c : BitVec 32) : IsDigestRow (pad64 (digestInput rho m c)) :=
  ⟨rho, m, c, rfl⟩
end Search
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
theorem digestRow_mem (hUpub : SeccLaw.publicUniverse ⊆ U) (rho : Digest) (m : Message) (c : BitVec 32) :
    pad64 (digestInput rho m c) ∈ U := by
  apply hUpub
  apply SeccLaw.mem_publicUniverse
  have h := Wots.Ref.pad64_length_le (digestInput rho m c)
  have hl : (digestInput rho m c).length = 64 := by
    simp only [digestInput, List.length_append, SphincsSecurity.bytesLE_length]
  unfold SeccLaw.maxInputLength
  omega
theorem Coherent.privateNonce (hcoh : Coherent U T vals nv τ a) (m : Message) :
    evalWithAnswerFn T (T3.privateNonce m) = nv m := by
  simp only [T3.privateNonce, privateHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact hcoh.nonce m
theorem Coherent.signDigest (hcoh : Coherent U T vals nv τ a) (m : Message) :
    LargeResidual.signDigest T m = evalWithAnswerFn T (digestSearch (nv m) m 0 attemptLimit) := by
  unfold LargeResidual.signDigest
  rw [hcoh.privateNonce]
end Coherent
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeCouplingVerdict ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingVerdict : DecidableEq T3.Cache := Classical.decEq _
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeCouplingInteraction ====
section

section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingInteraction : DecidableEq T3.Cache := Classical.decEq _
end SigGolfCandidate.T3.Security.LargeCoupling
end
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeCouplingInteraction ====
section

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (slotValue routeAddr IsDigestRow State Cell
  readState disclosedState runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (digestRow_isDigest digestRow_mem)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingSigning : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Search
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (labels : WCoord → Digest) (τ : Cell U → HashOutput) (a : AuxData)
end Search
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
end Coherent
section Sign
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} {mon : Monitor} {st : RouterState}
  {ws : LargeResidual.State WCoord (Cell U)} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
end Sign
section SignRel
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} {mon : Monitor} {st : RouterState}
  {ws : LargeResidual.State WCoord (Cell U)} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
end SignRel
section SignMain
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} {mon : Monitor} {st : RouterState}
  {ws : LargeResidual.State WCoord (Cell U)} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
end SignMain
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Fixed
variable {α : Type} (F : Answers) (published : SigGolfCandidate.T3.Cache)
end Fixed
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingVerdict : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Monitor
variable (U : Finset HashInput) (A : Answers) (q : Nat)
end Monitor
section Verdict
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
end Verdict
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingInteraction : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Steps
variable (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
end Steps
section Interaction
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} (initLaw : PMF AuxData)
end Interaction
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeResidual (slotValue routeAddr IsDigestRow State Cell
  readState disclosedState runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (digestRow_isDigest digestRow_mem)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingSigning : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
open ClaudeWCT.W9.T3.Security.LargeResidual (WCoord Coord msgVals msgSlots layerChains layerItems layerPath lookupVal)
structure ReadsOnly {U : Finset HashInput} (τ : Cell U → HashOutput) (ws ws' : LargeResidual.State WCoord (Cell U)) :
    Prop where
  candidates : ws'.candidates = ws.candidates
  counters : ws'.counters = ws.counters
  rows : ∀ row v, ws'.rows row = some v → ws.rows row = some v ∨ (IsDigestRow row.val ∧ v = τ row)
theorem ReadsOnly.refl {U : Finset HashInput} (τ : Cell U → HashOutput) (ws : LargeResidual.State WCoord (Cell U)) :
    ReadsOnly τ ws ws :=
  ⟨rfl, rfl, fun _ _ h => Or.inl h⟩
theorem ReadsOnly.trans {U : Finset HashInput} {τ : Cell U → HashOutput} {ws ws' ws'' : LargeResidual.State WCoord (Cell U)}
    (h1 : ReadsOnly τ ws ws') (h2 : ReadsOnly τ ws' ws'') : ReadsOnly τ ws ws'' := by
  refine ⟨h2.candidates.trans h1.candidates, h2.counters.trans h1.counters, fun row v hv => ?_⟩
  rcases h2.rows row v hv with h | h
  · exact h1.rows row v h
  · exact Or.inr h
section Search
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (labels : WCoord → Digest) (τ : Cell U → HashOutput) (a : AuxData)
theorem observed_search (T : Answers) (rho : Digest) (m : Message)
    (hU : ∀ c : BitVec 32, pad64 (digestInput rho m c) ∈ U)
    (hT : ∀ c : BitVec 32, T (.inl (.inr (pad64 (digestInput rho m c)))) = τ ⟨_, hU c⟩) :
    ∀ (fuel c : Nat) (ws : LargeResidual.State WCoord (Cell U)), ∃ ws',
      observedRun aux q labels τ (simulateQ (readImpl U a) (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m c fuel)) ws =
        pure (some (evalWithAnswerFn T (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m c fuel)), ws') ∧ ReadsOnly τ ws ws' := by
  intro fuel
  induction fuel with
  | zero =>
      intro c ws
      refine ⟨ws, ?_, ReadsOnly.refl τ ws⟩
      simp only [SigGolfCandidate.Research.SharedForest.sharedDigestSearch, simulateQ_pure, evalWithAnswerFn_pure]
      exact observed_pure aux q labels τ _ ws
  | succ fuel ih =>
      intro c ws
      rw [show SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m c (fuel + 1) = (digest rho m (BitVec.ofNat 32 c) >>= fun output =>
          if SigGolfCandidate.Research.SharedForest.digestAccepted output = true then pure (some (BitVec.ofNat 32 c, output))
          else SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m (c + 1) fuel) from rfl]
      simp only [digest, publicHash, simulateQ_bind, evalWithAnswerFn_bind]
      have hq : simulateQ (readImpl U a) (SigGolfCandidate.T3.Spec.query
          (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c))))) :
          M HashOutput) = readReq U ⟨_, hU (BitVec.ofNat 32 c)⟩ .none := by
        change simulateQ (readImpl U a) (liftM (SigGolfCandidate.T3.Spec.query _)) = _
        rw [simulateQ_spec_query]
        simp only [readImpl, dif_pos (hU (BitVec.ofNat 32 c))]
      rw [hq, observed_readReq]
      set X : Cell U := ⟨_, hU (BitVec.ofNat 32 c)⟩
      have hTX : (evalWithAnswerFn T (SigGolfCandidate.T3.Spec.query
          (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c))))) :
          M HashOutput) : HashOutput) = τ X := hT _
      have hrd : ReadsOnly τ ws (readState q ws X (τ X) .none) := by
        refine ⟨rfl, rfl, fun row v hv => ?_⟩
        by_cases hr : row = X
        · subst hr
          simp only [readState, Function.update_self] at hv
          exact Or.inr ⟨digestRow_isDigest _ _ _, (Option.some.inj hv).symm⟩
        · simp only [readState, Function.update_of_ne hr] at hv
          exact Or.inl hv
      rw [hTX]
      by_cases hadm : SigGolfCandidate.Research.SharedForest.digestAccepted (τ X) = true
      · simp only [hadm, if_true, simulateQ_pure, evalWithAnswerFn_pure]
        exact ⟨_, observed_pure aux q labels τ _ _, hrd⟩
      · simp only [hadm, Bool.false_eq_true, if_false]
        obtain ⟨ws', h1, h2⟩ := ih (c + 1) (readState q ws X (τ X) .none)
        exact ⟨ws', h1, hrd.trans h2⟩
end Search
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.digestRow (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hUpub : SeccLaw.publicUniverse ⊆ U) (rho : Digest)
    (m : Message) (c : BitVec 32) :
    T (.inl (.inr (pad64 (digestInput rho m c)))) = τ ⟨_, digestRow_mem hUpub rho m c⟩ := by
  have hd := digestRow_isDigest rho m c
  have hnp := LargeResidual.Paired.not_parsed_of_digest hd
  apply hcoh.residual_unparsed _ _ hnp (fun N' hu' => by rw [hcoh.cell N' hu']; exact LargeResidual.Paired.not_cell_unparsed hcoh hnp (LargeResidual.Paired.ne_phantom_of_length (by rw [Cost.pad64_length]; simp [digestInput, SphincsSecurity.bytesLE_length])) N' hu')
  rintro ⟨L, ctr, hX, -⟩
  exact encRow_not_digest L _ ctr 0 (hX ▸ hd)
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.privateNonce (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (m : Message) :
    evalWithAnswerFn T (SigGolfCandidate.T3.privateNonce m) = nv m := by
  simp only [SigGolfCandidate.T3.privateNonce, privateHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact hcoh.nonce m
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.signDigest (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (m : Message) :
    LargeResidual.Paired.signDigest T m =
      evalWithAnswerFn T (SigGolfCandidate.Research.SharedForest.sharedDigestSearch (nv m) m 0 WCT9.digestAttemptLimit) := by
  unfold LargeResidual.Paired.signDigest
  rw [hcoh.privateNonce]

end Coherent
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (Cell routeAddr)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord layerChains layerItems layerPath wctItem digestIndex)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord→Digest} {nv : Message→Digest}
  {τ : Cell U→HashOutput} {a : AuxData}

theorem layerChains_congr (d d' : Wots.LeafAddr→List Nat) (index : Fin (2^31)) (lay : Layer)
    (h : d (routeAddr index.val lay)=d' (routeAddr index.val lay)) :
    layerChains d index lay=layerChains d' index lay := by
  unfold layerChains
  split_ifs
  · rw [h]
  · rfl

theorem routeAddr_enc (index : Nat) (hi : index<2^31) (lay : Layer) :
    ∃L : EncLeaf,L.toWots=routeAddr index lay := route_source index hi lay

theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.layerChains_eq (h : LargeResidual.Paired.Coherent U T vals nv τ a)
    (index : Fin (2^31)) (lay : Layer) :
    layerChains (routerDigits a) index lay=
      layerChains (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T)) index lay :=
  layerChains_congr _ _ index lay (h.routerDigits_eq _ (routeAddr_enc index.val index.isLt lay))

theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.layerItems_eq (h : LargeResidual.Paired.Coherent U T vals nv τ a) (index : Fin (2^31)) :
    layerItems (routerDigits a) index=
      layerItems (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T)) index := by
  unfold layerItems
  apply List.flatMap_congr
  intro lay _
  rw [h.layerChains_eq]

theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.signItems_eq (h : LargeResidual.Paired.Coherent U T vals nv τ a) (output : HashOutput) :
    LargeResidual.Paired.signItemsWith (routerDigits a) output=LargeResidual.Paired.signItems T output := by
  unfold LargeResidual.Paired.signItems LargeResidual.Paired.signItemsWith
  rw [h.layerItems_eq]

theorem assembleSig_congr (rho : Digest) (output : HashOutput) (v v' : Coord→Digest)
    (d : Wots.LeafAddr→List Nat) (l : Wots.LeafAddr→Bool)
    (h : ∀c∈LargeResidual.Paired.signItemsWith d output,v c=v' c) :
    LargeResidual.Paired.assembleSig rho output v d l=LargeResidual.Paired.assembleSig rho output v' d l := by
  have hfts : ∀c∈LargeResidual.Paired.ftsItems (digestIndex output) output,v c=v' c :=
    fun c hc => h c (List.mem_append_left _ hc)
  have hlay : ∀c∈layerItems d (digestIndex output),v c=v' c :=
    fun c hc => h c (List.mem_append_right _ hc)
  have hopen : openingValues output v=openingValues output v' := by
    funext k t
    apply hfts
    have ho : wctItem (digestIndex output,k,SigGolfCandidate.Research.SharedForest.rawChildFromOutput output k,t)
        (4-WCT9.wordDigit (SigGolfCandidate.Research.SharedForest.forestRank output k.val) t) ∈
        LargeResidual.Paired.wctOpened (digestIndex output) k output := by
      unfold LargeResidual.Paired.wctOpened
      exact List.mem_ofFn.mpr ⟨t,rfl⟩
    exact List.mem_flatMap.mpr ⟨k,List.mem_finRange k,List.mem_append_left _ ho⟩
  have hpath : openingPath output v=openingPath output v' := by
    funext k l
    unfold openingPath
    congr 1
    apply List.map_congr_left
    intro c hc
    exact hfts c (List.mem_flatMap.mpr ⟨k,List.mem_finRange k,List.mem_append_right _ hc⟩)
  unfold LargeResidual.Paired.assembleSig assembleForest
  rw [hopen,hpath]
  congr 1
  funext lay
  congr 2
  · apply List.map_congr_left
    intro c hc
    exact hlay c (List.mem_flatMap.mpr ⟨lay,List.mem_finRange lay,List.mem_append_left _ hc⟩)
  · apply List.map_congr_left
    intro c hc
    exact hlay c (List.mem_flatMap.mpr ⟨lay,List.mem_finRange lay,List.mem_append_right _ hc⟩)

theorem assembleSig_digits (rho : Digest) (output : HashOutput) (v : Coord→Digest)
    (d d' : Wots.LeafAddr→List Nat) (l l' : Wots.LeafAddr→Bool)
    (h : ∀lay,d (routeAddr (digestIndex output).val lay)=d' (routeAddr (digestIndex output).val lay))
    (hl : ∀lay,l (routeAddr (digestIndex output).val lay)=l' (routeAddr (digestIndex output).val lay)) :
    LargeResidual.Paired.assembleSig rho output v d l=LargeResidual.Paired.assembleSig rho output v d' l' := by
  unfold LargeResidual.Paired.assembleSig
  congr 1
  · unfold hintsOf
    change ∀lay,d (routeAddr (WCT9.digestIndex output) lay)=d' (routeAddr (WCT9.digestIndex output) lay) at h
    change ∀lay,l (routeAddr (WCT9.digestIndex output) lay)=l' (routeAddr (WCT9.digestIndex output) lay) at hl
    rw [h 0,h 1,h 2,hl 0,hl 1,hl 2]
  · funext lay
    rw [layerChains_congr d d' _ lay (h lay)]
end Coherent
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeResidual (slotValue routeAddr IsDigestRow State Cell
  readState disclosedState runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (digestRow_isDigest digestRow_mem)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingSigning_states : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
open ClaudeWCT.W9.T3.Security.LargeResidual (WCoord Coord msgVals msgSlots layerChains layerItems layerPath lookupVal)
def MemoOk (T : Answers) (st : RouterState) : Prop :=
  ∀ m f, st.memo.lookup m = some f → f = LargeResidual.Paired.signDigest T m
noncomputable def signedState (T : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : Security.Request) : RouterState :=
  if request.cache = published then
    let st1 := if (st.memo.lookup request.message).isSome then st
      else LargeResidual.Paired.RouterState.signed st (nv request.message) request.message (LargeResidual.Paired.signDigest T request.message)
    match LargeResidual.Paired.signDigest T request.message with
    | some (_, N) => if RouteOk T (WCT9.digestIndex N) then
        { st1 with disclosed := st1.disclosed ++ LargeResidual.Paired.signItems T N } else st1
    | none => st1
  else st
noncomputable def finishState (T : Answers) (st1 : RouterState) (found : Option (BitVec 32 × HashOutput)) :
    RouterState :=
  match found with
  | some (_, N) => if RouteOk T (WCT9.digestIndex N) then
      { st1 with disclosed := st1.disclosed ++ LargeResidual.Paired.signItems T N } else st1
  | none => st1
noncomputable def startState (T : Answers) (nv : Message → Digest) (st : RouterState) (m : Message) : RouterState :=
  if (st.memo.lookup m).isSome then st else LargeResidual.Paired.RouterState.signed st (nv m) m (LargeResidual.Paired.signDigest T m)
theorem signedState_eq (T : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : Security.Request) :
    signedState T nv published st request = if request.cache = published then
      finishState T (startState T nv st request.message) (LargeResidual.Paired.signDigest T request.message) else st := rfl
theorem startState_fields (T : Answers) (nv : Message → Digest) (st : RouterState) (m : Message) :
    (startState T nv st m).disclosed = st.disclosed ∧ (startState T nv st m).seen = st.seen ∧
      (startState T nv st m).calls = st.calls ∧ (startState T nv st m).births = st.births := by
  unfold startState
  split_ifs
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨h1, h2, h3, h4, -⟩ := LargeResidual.Paired.RouterState.signed_fields st (nv m) m (LargeResidual.Paired.signDigest T m)
    exact ⟨h1, h2, h3, h4⟩
theorem finishState_fields (T : Answers) (st1 : RouterState) (found : Option (BitVec 32 × HashOutput)) :
    (finishState T st1 found).disclosed = st1.disclosed ++ (match found with
      | some (_, N) => if RouteOk T (WCT9.digestIndex N) then LargeResidual.Paired.signItems T N else []
      | none => []) ∧
    (finishState T st1 found).seen = st1.seen ∧ (finishState T st1 found).calls = st1.calls ∧
    (finishState T st1 found).births = st1.births ∧ (finishState T st1 found).memo = st1.memo := by
  unfold finishState
  cases found with
  | none => exact ⟨by simp, rfl, rfl, rfl, rfl⟩
  | some f =>
      obtain ⟨c, N⟩ := f
      dsimp only
      split_ifs
      · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨by simp, rfl, rfl, rfl, rfl⟩
theorem signedState_disclosed (T : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : Security.Request) :
    (signedState T nv published st request).disclosed = st.disclosed ++ signDisclosed T published request := by
  rw [signedState_eq]
  unfold signDisclosed
  split_ifs with hc
  · rw [(finishState_fields _ _ _).1, (startState_fields _ _ _ _).1]
    congr 1
  · simp
theorem signedState_seen (T : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : Security.Request) :
    (signedState T nv published st request).seen = st.seen ∧ (signedState T nv published st request).calls = st.calls := by
  rw [signedState_eq]
  split_ifs with hc
  · rw [(finishState_fields _ _ _).2.1, (finishState_fields _ _ _).2.2.1, (startState_fields _ _ _ _).2.1,
      (startState_fields _ _ _ _).2.2.1]
    exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
theorem signedState_memo (T : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : Security.Request) (hmemo : MemoOk T st) : MemoOk T (signedState T nv published st request) := by
  rw [signedState_eq]
  split_ifs with hc
  · intro m' f hf
    rw [(finishState_fields _ _ _).2.2.2.2] at hf
    unfold startState at hf
    split_ifs at hf with hm
    · exact hmemo m' f hf
    · simp only [(LargeResidual.Paired.RouterState.signed_fields _ _ _ _).2.2.2.2.2, List.lookup_cons] at hf
      by_cases hmm : m' = request.message
      · subst hmm
        simp only [beq_self_eq_true] at hf
        exact (Option.some.inj hf).symm
      · have hne : (m' == request.message) = false := by simpa using hmm
        rw [hne] at hf
        exact hmemo m' f hf
  · exact hmemo
theorem eval_authenticatedSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Security.Request) :
    evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) =
      if request.cache = published then evalWithAnswerFn T (SigGolfCandidate.Research.SharedForest.signPayload published request.message) else none := by
  unfold PairedOuter.FullGame.authenticatedSign
  simp only [evalWithAnswerFn_bind]
  split_ifs with h1
  · rw [h1]
  · rfl
section Sign
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} {mon : Monitor} {st : RouterState}
  {ws : LargeResidual.State WCoord (Cell U)} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
noncomputable def finishOut (T : Answers) (vals : Coord → Digest) (rho : Digest) (found : Option (BitVec 32 × HashOutput)) :
    Option SigGolfCandidate.Research.SharedForest.Signature :=
  match found with
  | some (_, N) => if RouteOk T (WCT9.digestIndex N) then
      some (assembleSig rho N (ClaudeWCT.W9.T3.Security.LargeResidual.selVals vals) (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T))
        (Wots.CanonicalRef.referenceLow T (Wots.CanonicalRef.sourceMessages T))) else none
  | none => none
noncomputable def finishWorld (T : Answers) (U : Finset HashInput) (q : Nat) (labels : WCoord → Digest)
    (ws : LargeResidual.State WCoord (Cell U)) (found : Option (BitVec 32 × HashOutput)) :
    LargeResidual.State WCoord (Cell U) :=
  match found with
  | some (_, N) => if RouteOk T (WCT9.digestIndex N) then
      discloseStates U q labels ws (LargeResidual.Paired.signItems T N ++ ClaudeWCT.W9.T3.Security.LargeResidual.topTrialsDisclosed)
      else ws
  | none => ws

theorem signItems_node_nonce (T : Answers) (N : HashOutput) :
    ∀ c ∈ LargeResidual.Paired.signItems T N, ∀ m : CanonGraph.TreeNode, c = .inl (.node m) → m.1.nonce.val = 0 := by
  intro c hc m hm
  subst hm
  rcases List.mem_append.mp hc with hc | hc
  · unfold LargeResidual.Paired.ftsItems at hc
    obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hc
    rcases List.mem_append.mp hk with hk | hk
    · unfold LargeResidual.Paired.wctOpened at hk
      obtain ⟨t, ht⟩ := List.mem_ofFn.mp hk
      exact absurd ht (LargeResidual.Paired.wctItem_not_node _ _ m)
    · unfold LargeResidual.Paired.wctPath at hk
      obtain ⟨l, -, hl⟩ := List.mem_filterMap.mp hk
      exact absurd rfl (LargeResidual.Paired.ftsChild_not_node hl m)
  · unfold ClaudeWCT.W9.T3.Security.LargeResidual.layerItems at hc
    obtain ⟨lay, -, hl⟩ := List.mem_flatMap.mp hc
    rcases List.mem_append.mp hl with hl | hl
    · unfold ClaudeWCT.W9.T3.Security.LargeResidual.layerChains at hl
      split_ifs at hl
      · obtain ⟨i, -, hi⟩ := List.mem_map.mp hl
        exact absurd hi (LargeResidual.Paired.chainItem_not_node _ _ _ m)
      · simp at hl
    · unfold ClaudeWCT.W9.T3.Security.LargeResidual.layerPath at hl
      split_ifs at hl
      · obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp hl
        unfold ClaudeWCT.W9.T3.Security.LargeResidual.treeChild at hj
        split_ifs at hj
        · simp at hj
        · obtain ⟨m', hm', he⟩ := Option.map_eq_some_iff.mp hj
          cases he
          exact (LargeResidual.Paired.treeNodeAt_spec hm').2.2.2.2
      · simp at hl
theorem selVals_lookup_sign (vals : Coord → Digest) (nv : Message → Digest) (items : List Coord)
    (hitems : ∀ c ∈ items, ∀ m : CanonGraph.TreeNode, c = .inl (.node m) → m.1.nonce.val = 0)
    (c : Coord) (hc : c ∈ items) :
    ClaudeWCT.W9.T3.Security.LargeResidual.selVals (lookupVal ((items ++ ClaudeWCT.W9.T3.Security.LargeResidual.topTrialsDisclosed).map
      (fun c => (c, Sum.elim vals nv (.inl c))))) c = ClaudeWCT.W9.T3.Security.LargeResidual.selVals vals c := by
  have hv0 : ∀ x ∈ items ++ ClaudeWCT.W9.T3.Security.LargeResidual.topTrialsDisclosed,
      lookupVal ((items ++ ClaudeWCT.W9.T3.Security.LargeResidual.topTrialsDisclosed).map (fun c => (c, Sum.elim vals nv (.inl c)))) x = vals x :=
    fun x hx => lookupVal_map (fun c => Sum.elim vals nv (.inl c)) _ x hx
  have htr : ∀ n : CanonGraph.TreeNode, CanonGraph.trialCap n.1.lay n.1.level.val ≠ 1 →
      ∀ j < CanonGraph.trialCap n.1.lay n.1.level.val, ClaudeWCT.W9.T3.Security.LargeResidual.trialCoord n j ∈ items ++ ClaudeWCT.W9.T3.Security.LargeResidual.topTrialsDisclosed :=
    fun n h1 j hj => List.mem_append_right _
      (ClaudeWCT.W9.T3.Security.LargeResidual.trialCoord_mem_topTrials (LargeResidual.Paired.lay_zero_of_cap h1) h1 hj)
  unfold ClaudeWCT.W9.T3.Security.LargeResidual.selVals
  rw [ClaudeWCT.W9.T3.Security.LargeResidual.selCoordV_congr c (fun n _ h1 j hj => hv0 _ (htr n h1 j hj))]
  apply hv0
  rcases c with (_ | _ | m | _ | _ | _ | _) | s
  all_goals first | exact List.mem_append_left _ hc | skip
  show ClaudeWCT.W9.T3.Security.LargeResidual.trialCoord m (ClaudeWCT.W9.T3.Security.LargeResidual.selNonceV vals m) ∈ _
  by_cases h1 : CanonGraph.trialCap m.1.lay m.1.level.val = 1
  · rw [ClaudeWCT.W9.T3.Security.LargeResidual.selNonceV_cap_one h1]
    have hw := CanonGraph.withNonce_self m
    rw [hitems _ hc m rfl] at hw
    show Sum.inl (CanonGraph.Node.node (CanonGraph.withNonce m 0)) ∈ _
    rw [hw]
    exact List.mem_append_left _ hc
  · exact htr m h1 _ (ClaudeWCT.W9.T3.Security.LargeResidual.selNonceV_lt vals m)
theorem observed_signFinish (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (st1 : RouterState) (rho : Digest)
    (found : Option (BitVec 32 × HashOutput)) (ws1 : LargeResidual.State WCoord (Cell U)) :
    observedRun aux q (Sum.elim vals nv) τ (signFinish U a st1 rho found) ws1 =
      pure (some (finishOut T vals rho found, finishState T st1 found),
        finishWorld T U q (Sum.elim vals nv) ws1 found) := by
  cases found with
  | none => exact observed_pure aux q _ τ _ ws1
  | some f =>
      obtain ⟨c, N⟩ := f
      have hidx : WCT9.digestIndex N < 2 ^ 31 := Nat.mod_lt _ (by positivity)
      unfold signFinish finishOut finishState finishWorld
      dsimp only
      by_cases hok : RouteOk T (WCT9.digestIndex N)
      · rw [if_pos ((hcoh.routeOk_iff _ hidx).mpr hok), if_pos hok, if_pos hok, if_pos hok]
        rw [observed_discloseAll, observed_pure, hcoh.signItems_eq]
        have hs : assembleSig rho N
            (ClaudeWCT.W9.T3.Security.LargeResidual.selVals (lookupVal ((LargeResidual.Paired.signItems T N ++ ClaudeWCT.W9.T3.Security.LargeResidual.topTrialsDisclosed).map
              (fun c => (c, Sum.elim vals nv (.inl c))))))
            (routerDigits a) (routerLows a) =
            assembleSig rho N (ClaudeWCT.W9.T3.Security.LargeResidual.selVals vals) (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T))
              (Wots.CanonicalRef.referenceLow T (Wots.CanonicalRef.sourceMessages T)) := by
          rw [assembleSig_digits rho N _ _ (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T))
            _ (Wots.CanonicalRef.referenceLow T (Wots.CanonicalRef.sourceMessages T)) (fun lay =>
            hcoh.routerDigits_eq _ (routeAddr_enc _ (LargeResidual.digestIndex N).isLt lay)) (fun lay =>
            hcoh.routerLows_eq _ (routeAddr_enc _ (LargeResidual.digestIndex N).isLt lay))]
          apply assembleSig_congr
          intro c' hc'
          exact selVals_lookup_sign vals nv _ (signItems_node_nonce T N) c' hc'
        rw [hs]
      · rw [if_neg (fun h => hok ((hcoh.routeOk_iff _ hidx).mp h)), if_neg hok, if_neg hok, if_neg hok]
        exact observed_pure aux q _ τ _ ws1
end Sign
section SignRel
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} {mon : Monitor} {st : RouterState}
  {ws : LargeResidual.State WCoord (Cell U)} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem known_signed (published : SigGolfCandidate.T3.Cache) (request : Security.Request) (c : Coord) (hc : (LargeResidual.Paired.RouterState.known st) c) :
    LargeResidual.Paired.RouterState.known (signedState T nv published st request) c := by
  unfold LargeResidual.Paired.RouterState.known at hc ⊢
  refine LargeResidual.Paired.Known.mono (fun d hd => ?_) hc
  rcases hd with hd | hd
  · exact Or.inl hd
  · right
    rw [signedState_disclosed]
    exact List.mem_append_left _ hd
theorem known_signed_new (published : SigGolfCandidate.T3.Cache) (request : Security.Request) (c : Coord)
    (hc : c ∈ signDisclosed T published request) : LargeResidual.Paired.RouterState.known (signedState T nv published st request) c := by
  apply LargeResidual.Paired.Known.base
  right
  rw [signedState_disclosed]
  exact List.mem_append_right _ hc
theorem Rel.afterSign (hrel : Rel U T vals nv τ a q mon st ws) (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (wsF : LargeResidual.State WCoord (Cell U))
    (hcand : ∀ c : Coord, c ∉ signDisclosed T published request → c ∉ ClaudeWCT.W9.T3.Security.LargeResidual.keygenDisclosed →
      wsF.candidates (.inl c) = ws.candidates (.inl c))
    (hmemF : ∀ c, Sum.elim vals nv c ∈ wsF.candidates c) (hcnt : wsF.counters = ws.counters)
    (hrows : ∀ row v, wsF.rows row = some v → ws.rows row = some v ∨ (IsDigestRow row.val ∧ v = τ row)) :
    Rel U T vals nv τ a q (mon.sign T published request) (signedState T nv published st request) wsF := by
  have hms : mon.sign T published request =
      ⟨mon.disclosed ++ signDisclosed T published request, mon.seen, mon.calls, mon.digests, false⟩ := by
    unfold Monitor.sign
    rw [if_neg (by rw [hrel.contact]; decide)]
  obtain ⟨hseen, hcalls⟩ := signedState_seen T nv published st request
  rw [hms]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, hmemF, ?_, ?_, ?_, ?_, ?_⟩
  · rw [signedState_disclosed, hrel.disclosed]
  · rw [hseen, hrel.seen]
  · rw [hcalls, hrel.calls]
  · rw [hcnt, hcalls, hrel.wcalls]
  · rw [hcnt, hrel.digests]
  · rw [hcnt]; exact hrel.probes
  · rw [hcalls]; exact hrel.budget
  · intro c hck
    have hc1 : c ∉ signDisclosed T published request := fun h => hck (known_signed_new published request c h)
    have hc2 : ¬(LargeResidual.Paired.RouterState.known st) c := fun h => hck (known_signed published request c h)
    rw [hcand c hc1 (fun h => hc2 (ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Known.base (Or.inl h))), hcnt]
    exact hrel.hidden c hc2
  · intro row v hv
    rcases hrows row v hv with h | h
    · exact hrel.rowsEq row v h
    · exact h.2
  · intro row v hv
    rw [hseen]
    rcases hrows row v hv with h | h
    · exact hrel.rowsSeen row v h
    · exact Or.inr h.1
  · intro X hX hXU N hu hN cs hcs
    rw [hseen] at hX
    exact known_signed published request _ (hrel.seenCells X hX hXU N hu hN cs hcs)
  · intro X hX hXU L ctr hL cs hcs
    rw [hseen] at hX
    exact known_signed published request _ (hrel.seenEnc X hX hXU L ctr hL cs hcs)
theorem disclosedState_props (s : LargeResidual.State WCoord (Cell U)) (c : WCoord) (v : Digest) :
    (disclosedState q s c v .none).candidates = Function.update s.candidates c {v} ∧
      (disclosedState q s c v .none).counters = s.counters ∧ (disclosedState q s c v .none).rows = s.rows :=
  ⟨rfl, rfl, rfl⟩
theorem finishWorld_props (s : LargeResidual.State WCoord (Cell U)) (found : Option (BitVec 32 × HashOutput)) :
    (finishWorld T U q (Sum.elim vals nv) s found).counters = s.counters ∧
    (finishWorld T U q (Sum.elim vals nv) s found).rows = s.rows ∧
    (∀ c, (finishWorld T U q (Sum.elim vals nv) s found).candidates c = s.candidates c ∨
      (finishWorld T U q (Sum.elim vals nv) s found).candidates c = {Sum.elim vals nv c}) ∧
    (∀ c : Coord, c ∉ (match found with
        | some (_, N) => if RouteOk T (WCT9.digestIndex N) then LargeResidual.Paired.signItems T N else []
        | none => []) → c ∉ ClaudeWCT.W9.T3.Security.LargeResidual.topTrialsDisclosed →
      (finishWorld T U q (Sum.elim vals nv) s found).candidates (.inl c) = s.candidates (.inl c)) := by
  unfold finishWorld
  cases found with
  | none => exact ⟨rfl, rfl, fun c => Or.inl rfl, fun c _ _ => rfl⟩
  | some f =>
      obtain ⟨c0, N⟩ := f
      dsimp only
      split_ifs with hok
      · refine ⟨discloseStates_counters _ _, discloseStates_rows _ _, fun c => ?_, fun c hc hc' => ?_⟩
        · rw [discloseStates_candidates]
          split_ifs
          · exact Or.inr rfl
          · exact Or.inl rfl
        · rw [discloseStates_candidates, if_neg]
          intro hm
          obtain ⟨d, hd, hdc⟩ := List.mem_map.mp hm
          rw [Sum.inl.inj hdc] at hd
          rcases List.mem_append.mp hd with hd | hd
          · exact hc hd
          · exact hc' hd
      · exact ⟨rfl, rfl, fun c => Or.inl rfl, fun c _ _ => rfl⟩
end SignRel

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeResidual (slotValue routeAddr IsDigestRow State Cell
  readState disclosedState runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (digestRow_isDigest digestRow_mem)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingSigning_sign : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
open ClaudeWCT.W9.T3.Security.LargeResidual (WCoord Coord msgVals msgSlots layerChains layerItems layerPath lookupVal)
section SignMain
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} {mon : Monitor} {st : RouterState}
  {ws : LargeResidual.State WCoord (Cell U)} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem routeSign_observed (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hUpub : SeccLaw.publicUniverse ⊆ U)
    (published : SigGolfCandidate.T3.Cache)
    (hsource : ∀request : Security.Request,request.cache=published →
      evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request)=
        finishOut T vals (nv request.message) (LargeResidual.Paired.signDigest T request.message))
    (hrel : Rel U T vals nv τ a q mon st ws) (hmemo : MemoOk T st) (request : Security.Request) :
    ∃ wsF, observedRun aux q (Sum.elim vals nv) τ (routeSign U a published st request) ws =
        pure (some (evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request),
          signedState T nv published st request), wsF) ∧
      Rel U T vals nv τ a q (mon.sign T published request) (signedState T nv published st request) wsF := by
  unfold routeSign
  by_cases hc : request.cache = published
  · rw [if_pos hc, observed_discloseReq]
    simp only [Sum.elim_inr]
    have hreal := hsource request hc
    have hsd : signDisclosed T published request = match LargeResidual.Paired.signDigest T request.message with
        | some (_, N) => if RouteOk T (WCT9.digestIndex N) then LargeResidual.Paired.signItems T N else []
        | none => [] := by
      unfold signDisclosed
      rw [if_pos hc]
      congr 1
    set ws1 := disclosedState q ws (.inr request.message) (nv request.message) .none with hws1
    have hws1c := (disclosedState_props (q := q) ws (.inr request.message) (nv request.message)).1
    have hws1n := (disclosedState_props (q := q) ws (.inr request.message) (nv request.message)).2.1
    have hws1r := (disclosedState_props (q := q) ws (.inr request.message) (nv request.message)).2.2
    have hmem1 : ∀ c, Sum.elim vals nv c ∈ ws1.candidates c := by
      intro c
      rw [hws1c]
      by_cases hcm : c = .inr request.message
      · subst hcm
        rw [Function.update_self]
        exact Finset.mem_singleton_self _
      · rw [Function.update_of_ne hcm]
        exact hrel.mem c
    have hfinal : ∀ ws2 : LargeResidual.State WCoord (Cell U), ReadsOnly τ ws1 ws2 →
        Rel U T vals nv τ a q (mon.sign T published request) (signedState T nv published st request)
          (finishWorld T U q (Sum.elim vals nv) ws2 (LargeResidual.Paired.signDigest T request.message)) := by
      intro ws2 hro
      obtain ⟨hfc, hfr, hfcand, hfold⟩ := finishWorld_props (T := T) (q := q) (vals := vals) (nv := nv) ws2
        (LargeResidual.Paired.signDigest T request.message)
      apply hrel.afterSign published request
      · intro c hcn hkg
        rw [hsd] at hcn
        rw [hfold c hcn (fun h => hkg (List.mem_append_right _ h)), hro.candidates, hws1c,
          Function.update_of_ne (by simp)]
      · intro c
        rcases hfcand c with h | h
        · rw [h, hro.candidates]; exact hmem1 c
        · rw [h]; exact Finset.mem_singleton_self _
      · rw [hfc, hro.counters, hws1n]
      · intro row v hv
        rw [hfr] at hv
        rcases hro.rows row v hv with h | h
        · rw [hws1r] at h; exact Or.inl h
        · exact Or.inr h
    cases hm : st.memo.lookup request.message with
    | some f =>
        have hf := hmemo _ f hm
        simp only
        rw [observed_signFinish aux hcoh st (nv request.message) f ws1, hf]
        refine ⟨_, ?_, hfinal ws1 (ReadsOnly.refl τ ws1)⟩
        rw [hreal, signedState_eq, if_pos hc]
        unfold startState
        rw [hm]
        rfl
    | none =>
        simp only
        obtain ⟨ws2, hs, hro⟩ := observed_search aux q (Sum.elim vals nv) τ a T (nv request.message)
          request.message (digestRow_mem hUpub _ _) (hcoh.digestRow hUpub _ _) WCT9.digestAttemptLimit 0 ws1
        rw [observedRun, runWith_bind, ← observedRun, hs, pure_bind]
        simp only [Option.elim_some]
        rw [← observedRun, ← hcoh.signDigest, observed_signFinish aux hcoh _ (nv request.message) _ ws2]
        refine ⟨_, ?_, hfinal ws2 hro⟩
        rw [hreal, signedState_eq, if_pos hc]
        unfold startState
        rw [hm]
        rfl
  · rw [if_neg hc]
    have hnone : evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) = none := by
      rw [eval_authenticatedSign, if_neg hc]
    have hst : signedState T nv published st request = st := by rw [signedState_eq, if_neg hc]
    refine ⟨ws, ?_, ?_⟩
    · rw [hnone, hst]
      exact observed_pure aux q _ τ _ ws
    · exact hrel.afterSign published request ws (fun c _ _ => rfl) hrel.mem rfl (fun row v hv => Or.inl hv)

end SignMain
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingVerdict : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Monitor
variable (U : Finset HashInput) (A : Answers) (q : Nat)
theorem query_frozen (mon : Monitor) (h : mon.contact = true) (X : HashInput) (y : HashOutput) :
    mon.query U A q X y = mon := by
  unfold Monitor.query; rw [if_pos h]
theorem event_frozen (mon : Monitor) (h : mon.contact = true) (e : FirstHit.QueryEvent) :
    mon.event U A q e = mon := by
  rcases e with ⟨before, (n | X) | c, answer⟩
  · rfl
  · exact query_frozen U A q mon h X answer
  · rfl
theorem events_frozen (mon : Monitor) (h : mon.contact = true) (events : List FirstHit.QueryEvent) :
    events.foldl (Monitor.event U A q) mon = mon := by
  induction events with
  | nil => rfl
  | cons e rest ih => rw [List.foldl_cons, event_frozen U A q mon h e, ih]
theorem query_over (mon : Monitor) (hc : mon.contact = false) (hq : q ≤ mon.calls) (X : HashInput)
    (y : HashOutput) : (mon.query U A q X y).contact = false ∧ q < (mon.query U A q X y).calls := by
  unfold Monitor.query
  rw [if_neg (by rw [hc]; decide), if_neg (fun h => by omega)]
  exact ⟨rfl, show q < mon.calls + 1 by omega⟩
theorem event_over (mon : Monitor) (hc : mon.contact = false) (hq : q < mon.calls) (e : FirstHit.QueryEvent) :
    (mon.event U A q e).contact = false ∧ q < (mon.event U A q e).calls := by
  rcases e with ⟨before, (n | X) | c, answer⟩
  · exact ⟨hc, hq⟩
  · exact query_over U A q mon hc (by omega) X answer
  · exact ⟨hc, hq⟩
theorem events_over (mon : Monitor) (hc : mon.contact = false) (hq : q < mon.calls) (events : List FirstHit.QueryEvent) :
    (events.foldl (Monitor.event U A q) mon).contact = false ∧ q < (events.foldl (Monitor.event U A q) mon).calls := by
  induction events generalizing mon with
  | nil => exact ⟨hc, hq⟩
  | cons e rest ih =>
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := event_over U A q mon hc hq e
      exact ih _ h1 h2
end Monitor
noncomputable def routerEvent (U : Finset HashInput) (st : RouterState) (e : FirstHit.QueryEvent) : RouterState :=
  match e with
  | ⟨_, .inl (.inr X), y⟩ => st.next U X y
  | _ => st
def PhaseOutcome (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) (q : Nat) {β : Type} (monF : Monitor) (value : β) (stF : RouterState)
    (out : Option (Option (β × RouterState))) (ws' : LargeResidual.State WCoord (Cell U)) : Prop :=
  (out = none ∧ monF.contact = true ∧ ws'.counters.calls ≤ q) ∨
    (out = some none ∧ monF.contact = false ∧ q < monF.calls) ∨
    (out = some (some (value, stF)) ∧ Rel U T vals nv τ a q monF stF ws')
section Verdict
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem routeVerdict_pure {β : Type} (v : β) (st : RouterState) :
    routeVerdict U a q (pure v : M β) st = pure (some (v, st)) := rfl
theorem routeVerdict_public {β : Type} (X : HashInput) (next : HashOutput → M β) (st : RouterState) :
    routeVerdict U a q (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr X))) >>= next) st =
      if q ≤ st.calls then pure none else (routeQuerySelected U a st X >>= fun r => routeVerdict U a q (next r.1) r.2) := rfl
theorem routeVerdict_observed (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hq : q ≤ 2 ^ 127) {β : Type} (V : M β)
    (hV : PublicVerdict.Only V) :
    ∀ (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) (state : LazyPrivate.State),
      Rel U T vals nv τ a q mon st ws → FamOK st →
      ∃ out ws', observedRun aux q (Sum.elim vals nv) τ (routeVerdict U a q V st) ws = pure (out, ws') ∧
        PhaseOutcome U T vals nv τ a q ((Wots.Ref.pureRecord T V state).events.foldl (Monitor.event U T q) mon)
          (evalWithAnswerFn T V) ((Wots.Ref.pureRecord T V state).events.foldl (routerEvent U) st) out ws' := by
  induction V using OracleComp.inductionOn with
  | pure v =>
      intro mon st ws state hrel _
      refine ⟨some (some (v, st)), ws, ?_, Or.inr (Or.inr ⟨rfl, hrel⟩)⟩
      rw [routeVerdict_pure]
      exact observed_pure aux q _ τ _ ws
  | query_bind input next ih =>
      intro mon st ws state hrel hok
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hV
      rcases input with (n | X) | c
      · exact False.elim hi
      · rw [Wots.Ref.pureRecord_query_bind]
        simp only [List.foldl_cons]
        rw [routeVerdict_public]
        by_cases hb : q ≤ st.calls
        · rw [if_pos hb]
          refine ⟨some none, ws, observed_pure aux q _ τ _ ws, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
          have h1 := query_over U T q mon hrel.contact (by rw [hrel.calls]; exact hb) X (T (.inl (.inr X)))
          exact events_over U T q _ h1.1 h1.2 _
        · rw [if_neg hb]
          have hlt : st.calls < q := by omega
          obtain ⟨ws1, hout⟩ := routeQuery_observed aux hcoh hrel hlt hq hok X
          rcases hout with ⟨hc, hrun, -, hcalls⟩ | ⟨hc, hrun, hrel1⟩
          · refine ⟨none, ws1, ?_, Or.inl ⟨rfl, ?_, hcalls⟩⟩
            · rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
              rfl
            · change (List.foldl (Monitor.event U T q) (mon.query U T q X (T (.inl (.inr X)))) _).contact = true
              rw [events_frozen U T q _ hc]
              exact hc
          · obtain ⟨out, ws2, hrun2, hph⟩ := ih (T (.inl (.inr X))) (hn _) _ _ ws1 _ hrel1
              (famOK_of_disclosed (st.next_disclosed U X _) hok)
            refine ⟨out, ws2, ?_, hph⟩
            rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            exact hrun2
      · exact False.elim hi
end Verdict
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingInteraction : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def routerStep (U : Finset HashInput) (T : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache)
    (st : RouterState) : TaggedStep → RouterState
  | .world e => routerEvent U st e
  | .sign request _ _ => signedState T nv published st request
section Steps
variable (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
theorem steps_over (mon : Monitor) (hc : mon.contact = false) (hq : q < mon.calls) (steps : List TaggedStep) :
    (steps.foldl (Monitor.step U A q published) mon).contact = false ∧
      q < (steps.foldl (Monitor.step U A q published) mon).calls := by
  induction steps generalizing mon with
  | nil => exact ⟨hc, hq⟩
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      · cases s with
        | world e => exact (event_over U A q mon hc hq e).1
        | sign request out events =>
            simp only [Monitor.step, Monitor.sign, hc]
            rfl
      · cases s with
        | world e => exact (event_over U A q mon hc hq e).2
        | sign request out events =>
            simp only [Monitor.step, Monitor.sign, hc]
            exact hq
theorem steps_frozen (mon : Monitor) (hc : mon.contact = true) (steps : List TaggedStep) :
    steps.foldl (Monitor.step U A q published) mon = mon := by
  induction steps with
  | nil => rfl
  | cons s rest ih =>
      rw [List.foldl_cons]
      have h1 : Monitor.step U A q published mon s = mon := by
        cases s with
        | world e => exact event_frozen U A q mon hc e
        | sign request out events => simp only [Monitor.step, Monitor.sign, hc, if_true]
      rw [h1, ih]
end Steps
theorem routerStep_disclosed_mono (U : Finset HashInput) (T : Answers) (nv : Message → Digest)
    (published : SigGolfCandidate.T3.Cache) (st : RouterState) (s : TaggedStep) :
    ∀ x ∈ st.disclosed, x ∈ (routerStep U T nv published st s).disclosed := by
  intro x hx
  cases s with
  | world e =>
      have he : (routerEvent U st e).disclosed = st.disclosed := by
        rcases e with ⟨before, (n | X) | c, y⟩
        · rfl
        · exact LargeResidual.RouterState.next_disclosed U st X y
        · rfl
      change x ∈ (routerEvent U st e).disclosed
      rw [he]; exact hx
  | sign request out events =>
      change x ∈ (signedState T nv published st request).disclosed
      rw [signedState_disclosed]
      exact List.mem_append_left _ hx
theorem steps_disclosed_mono (U : Finset HashInput) (T : Answers) (nv : Message → Digest)
    (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) (st : RouterState) :
    ∀ x ∈ st.disclosed, x ∈ (steps.foldl (routerStep U T nv published) st).disclosed := by
  induction steps generalizing st with
  | nil => exact fun x hx => hx
  | cons s rest ih =>
      intro x hx
      rw [List.foldl_cons]
      exact ih _ x (routerStep_disclosed_mono U T nv published st s x hx)
section Interaction
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} (initLaw : PMF AuxData)
theorem routeInteraction_pure {α : Type} (published : SigGolfCandidate.T3.Cache) (v : α) (st : RouterState) :
    routeInteraction U a published q (pure v : OracleComp PairedOuter.LazyPrivate.Interaction α) st = pure (some ((v, []), st)) :=
  rfl
theorem routeInteraction_coin {α : Type} (published : SigGolfCandidate.T3.Cache) (n : Nat)
    (next : Fin (n + 1) → OracleComp PairedOuter.LazyPrivate.Interaction α) (st : RouterState) :
    routeInteraction U a published q (liftM (PairedOuter.LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) st =
      (coinReq U n >>= fun c => routeInteraction U a published q (next c) st) := rfl
theorem routeInteraction_hash {α : Type} (published : SigGolfCandidate.T3.Cache) (X : HashInput)
    (next : HashOutput → OracleComp PairedOuter.LazyPrivate.Interaction α) (st : RouterState) :
    routeInteraction U a published q (liftM (PairedOuter.LazyPrivate.Interaction.query (.inl (.inr X))) >>= next) st =
      if q ≤ st.calls then pure none else
        (routeQuerySelected U a st X >>= fun r => routeInteraction U a published q (next r.1) r.2) := rfl
theorem routeInteraction_request {α : Type} (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp PairedOuter.LazyPrivate.Interaction α) (st : RouterState) :
    routeInteraction U a published q (liftM (PairedOuter.LazyPrivate.Interaction.query (.inr request)) >>= next) st =
      (routeSign U a published st request >>= fun s =>
        routeInteraction U a published q (next s.1) s.2 >>= fun rest =>
          pure (rest.map fun res => ((res.1.1, ⟨request, s.1⟩ :: res.1.2), res.2))) := rfl
theorem interaction_le (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hq : q ≤ 2 ^ 127) (hUpub : SeccLaw.publicUniverse ⊆ U)
    (published : SigGolfCandidate.T3.Cache) (hsource : ∀request : Security.Request,request.cache=published →
      evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request)=
        finishOut T vals (nv request.message) (LargeResidual.Paired.signDigest T request.message))
    {α : Type} (program : OracleComp PairedOuter.LazyPrivate.Interaction α) :
    ∀ {β : Type} (Final : Monitor → RouterState → (α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) → LazyPrivate.State → Prop)
      (K : Option ((α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) × RouterState) → OracleComp (RWorld U) β)
      (F : Option β × LargeResidual.State WCoord (Cell U) → Prop),
      (∀ mon st ws state v log, Rel U T vals nv τ a q mon st ws → MemoOk T st → Final mon st (v, log) state →
        1 ≤ Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (K (some ((v, log), st))) ws]) →
      (∀ m s v σ, Final m s v σ → m.contact = true ∨ m.calls ≤ q) →
      (∀ ws' : LargeResidual.State WCoord (Cell U), ws'.counters.calls ≤ q → F (none, ws')) →
      (∀ m s v σ, Final m s v σ → FamOK s) →
      ∀ (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) (state : LazyPrivate.State),
        Rel U T vals nv τ a q mon st ws → MemoOk T st →
        Pr[fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
              (t.steps.foldl (routerStep U T nv published) st) t.value t.state |
            taggedFixed T published program state] ≤
          Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
            (routeInteraction U a published q program st >>= K) ws] := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro β Final K F hleaf habort hstop hfin mon st ws state hrel hmemo
      rw [taggedFixed_pure, routeInteraction_pure, pure_bind, probEvent_pure]
      split_ifs with hf
      · exact hleaf mon st ws state v [] hrel hmemo hf
      · exact zero_le
  | query_bind input next ih =>
      intro β Final K F hleaf habort hstop hfin mon st ws state hrel hmemo
      rcases input with (n | X) | request
      ·
        rw [taggedFixed_world, routeInteraction_coin, bind_assoc, observed_coinReq]
        rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro c
        have hc : Pr[= c | Wots.Ref.fixedWorld T (.inl (.inl n))] =
            Pr[= c | (liftM (auxLaw initLaw (.coin n)) : SPMF (Fin (n + 1)))] := by
          change Pr[= c | (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))] = _
          simp [auxLaw, SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
        rw [hc]
        gcongr
        rw [probEvent_map]
        exact ih c Final K F hleaf habort hstop hfin mon st ws _ hrel hmemo
      ·
        rw [taggedFixed_world, Wots.Ref.fixedWorld_public, pure_bind, probEvent_map, routeInteraction_hash]
        by_cases hb : q ≤ st.calls
        ·
          rw [if_pos hb]
          have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
              (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                last.state⟩ : Tagged α)) |
              taggedFixed T published (next (T (.inl (.inr X))))
                (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
            have h1 := query_over U T q mon hrel.contact (by rw [hrel.calls]; exact hb) X (T (.inl (.inr X)))
            refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
            intro t ht
            simp only [Function.comp_apply, List.foldl_cons] at ht
            have h2 := steps_over U T q published _ h1.1 h1.2 t.steps
            rcases habort _ _ _ _ ht with h | h
            · change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).contact
                = true at h
              rw [h2.1] at h
              cases h
            · change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).calls
                ≤ q at h
              omega
          rw [hzero]
          exact zero_le
        · by_cases hok : FamOK st
          swap
          · have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                  (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
                (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                  last.state⟩ : Tagged α)) |
                taggedFixed T published (next (T (.inl (.inr X))))
                  (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
              refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
              intro t ht
              exact hok (famOK_mono (steps_disclosed_mono U T nv published _ _) (hfin _ _ _ _ ht))
            rw [hzero]
            exact zero_le
          rw [if_neg hb, bind_assoc]
          have hlt : st.calls < q := by omega
          obtain ⟨ws1, hout⟩ := routeQuery_observed (auxLaw initLaw) hcoh hrel hlt hq hok X
          rcases hout with ⟨hc, hrun, -, hcalls⟩ | ⟨hc, hrun, hrel1⟩
          ·
            rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_none]
            rw [probEvent_pure, if_pos (hstop ws1 hcalls)]
            exact probEvent_le_one
          · rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_some]
            have hmemo1 : MemoOk T (st.next U X (T (.inl (.inr X)))) := by
              intro m f hf
              apply hmemo m f
              unfold LargeResidual.RouterState.next at hf
              split_ifs at hf <;> exact hf
            exact ih (T (.inl (.inr X))) Final K F hleaf habort hstop hfin _ _ ws1 _ hrel1 hmemo1
      ·
        rw [taggedFixed_request, Wots.Ref.fixedRecord_hashOnly T _ (Wots.PairedReference.Ref.authenticatedSign_hashOnly _ _),
          pure_bind, probEvent_map, routeInteraction_request, bind_assoc]
        obtain ⟨wsF, hrun, hrelF⟩ := routeSign_observed (auxLaw initLaw) hcoh hUpub published hsource hrel hmemo request
        rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
        simp only [Option.elim_some, bind_assoc, pure_bind]
        have hval : (Wots.Ref.pureRecord T (PairedOuter.FullGame.authenticatedSign published request) state).value =
            evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) := Wots.Ref.pureRecord_value _ _ _
        rw [hval]
        set out := evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) with hout
        let Final' : Monitor → RouterState → (α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) → LazyPrivate.State → Prop :=
          fun m s v σ => Final m s (v.1, ⟨request, out⟩ :: v.2) σ
        let K' : Option ((α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) × RouterState) → OracleComp (RWorld U) β :=
          fun rest => K (rest.map fun res => ((res.1.1, ⟨request, out⟩ :: res.1.2), res.2))
        have hleaf' : ∀ mon st ws state v log, Rel U T vals nv τ a q mon st ws → MemoOk T st →
            Final' mon st (v, log) state →
            1 ≤ Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (K' (some ((v, log), st))) ws] :=
          fun mon st ws state v log hrel hmemo hf => hleaf mon st ws state v (⟨request, out⟩ :: log) hrel hmemo hf
        have habort' : ∀ m s v σ, Final' m s v σ → m.contact = true ∨ m.calls ≤ q :=
          fun m s v σ hf => habort _ _ _ _ hf
        exact ih out Final' K' F hleaf' habort' hstop (fun m s v σ hf => hfin _ _ _ _ hf) _ _ wsF _ hrelF
          (signedState_memo T nv published st request hmemo)
end Interaction
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.source
    {U : Finset HashInput} {T : Answers} {vals : Coord→Digest} {nv : Message→Digest}
    {τ : Cell U→HashOutput} {a : AuxData} (h : LargeResidual.Paired.Coherent U T vals nv τ a)
    (published : SigGolfCandidate.T3.Cache)
    (hpub : published.region=Correctness.cacheRegion (Correctness.maskedTop T))
    (request : Security.Request) (hc : request.cache=published) :
    evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request)=
      finishOut T vals (nv request.message) (LargeResidual.Paired.signDigest T request.message) := by
  rw [authenticatedSign_disclosed h.agrees published hpub request,if_pos hc,h.privateNonce]
  unfold finishOut
  cases LargeResidual.Paired.signDigest T request.message with
  | none => rfl
  | some found =>
    rcases found with ⟨ctr,N⟩
    dsimp only
    split_ifs
    · apply congrArg some
      apply assembleSig_congr
      intro c hc
      exact h.honestValue_used c (signItems_used T N c hc)
    · rfl
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
-- ==== merged from T3_Secc_LargeCouplingCertDefs ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def honestNonce (A : Answers) (m : Message) : Digest := evalWithAnswerFn A (privateNonce m)
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeCouplingCertDefs ====
section

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
end ClaudeWCT.W9.T3.Security.LargeCoupling

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord trialRows)
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCertFold_fold : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def routerFold (U : Finset HashInput) (A : Answers) (published : SigGolfCandidate.T3.Cache)
    (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) : RouterState :=
  verdict.foldl (routerEvent U) (steps.foldl (routerStep U A (honestNonce A) published) LargeResidual.RouterState.initial)
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open ClaudeWCT.W9.T3.Security.LargeResidual (WCoord)

def CertGhost (st : LargeResidual.Paired.RouterState) : Prop :=
  st.exposures.length ≤ CaseC.horizon ∧
    (st.reused = true ∨ ∃ p ∈ st.births,
      ClaudeWCT.Bank.Paired.lawSpec.admissible p.2 = true ∧
      ClaudeWCT.Bank.Paired.Covered st.exposures p.2)

def CertOut {U : Finset HashInput}
    (r : Option (Option (Bool × LargeResidual.Paired.RouterState)) ×
      SigGolfCandidate.T3.Security.LargeResidual.State WCoord (Cell U)) : Prop :=
  ∃ st, r.1 = some (some (true, st)) ∧ CertGhost st
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord trialRows)
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCertFold_certR : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
def CertR (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (rec : FirstHit.Recorded Bool) (A : Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary rec generated tagged checked →
    checked.value = true ∧
    (monitorRun (Wots.PairedReference.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).contact = false ∧
    (monitorRun (Wots.PairedReference.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).calls ≤ q ∧
    CertGhost (routerFold (Wots.PairedReference.referenceInputs adversary) A generated.value.2 tagged.steps checked.events)

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
end
-- ==== merged from T3_Secc_WotsExtractSplit ====
section

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityExtraction SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB
def recordedEntries (answers : Answers) (events : List FirstHit.QueryEvent) : List Entry :=
  entriesOf answers (events.map FirstHit.QueryEvent.input)
theorem entries_recorded {answers : Answers} {qs : List Spec.Domain} {events : List FirstHit.QueryEvent}
    (hrec : ∀ input, (.inl (.inr input) : Spec.Domain) ∈ qs →
      ∃ prior, (⟨prior, .inl (.inr input), answers (.inl (.inr input))⟩ : FirstHit.QueryEvent) ∈ events) :
    ∀ e ∈ entriesOf answers qs, e ∈ recordedEntries answers events := by
  rintro ⟨input, answer⟩ he
  obtain ⟨hq, ha⟩ := mem_entriesOf_iff.mp he
  obtain ⟨prior, hev⟩ := hrec input hq
  exact mem_entriesOf_iff.mpr ⟨List.mem_map.mpr ⟨_, hev, rfl⟩, ha⟩
end SigGolfCandidate.T3.Security.WotsExtract
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3.Security.WotsExtract
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsExtractSplit ====
section

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots (Entry entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (recordedEntries entries_recorded)
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB
theorem verdict_accepting (publicKey : Digest) (interaction : Option ForgeryP × QueryLog Requests)
    (before : LazyPrivate.State) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker publicKey interaction) before))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hwin : result.value = true) :
    interaction.2.length ≤ 2 ^ 32 ∧
    ∃ forgery, interaction.1 = some forgery ∧ PaddedExtraction.Fresh interaction.2 forgery ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
        evalWithAnswerFn answers (ClaudeWCT.W9.T3M.verifyP message publicKey witness) = true ∧
        ∀ input, (.inl (.inr input) : Spec.Domain) ∈ queried answers (ClaudeWCT.W9.T3M.verifyP message publicKey witness) →
          ∃ prior, (⟨prior, .inl (.inr input), answers (.inl (.inr input))⟩ : FirstHit.QueryEvent) ∈
            result.events := by
  cases hf : interaction.1 with
  | none =>
      simp only [GameWith.verdict, hf, FirstHit.record_pure, support_pure, Set.mem_singleton_iff] at hr
      subst result
      contradiction
  | some forgery =>
      simp only [GameWith.verdict, hf, PaddedGame.checker] at hr
      obtain ⟨checked, hchecked, last, hlast, hvalue, hevents, hstate⟩ :=
        FirstHit.record_bind_support _ _ before result hr
      rw [FirstHit.record_pure, support_pure, Set.mem_singleton_iff] at hlast
      subst last
      simp only [List.append_nil] at hevents
      have hand : (decide (interaction.2.length ≤ 2 ^ 32) && checked.value) = true := hvalue.symm.trans hwin
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hand
      obtain ⟨hlength, hcheckedWin⟩ := hand
      have hac : ∀ input answer, SourceReplay.known checked.state input = some answer → answers input = answer := by
        simpa only [hstate] using ha
      have hp := PaddedExtraction.check_hashOnly publicKey interaction.2 forgery
      have hw := (SourceReplay.resolves_of_run _ hp before (checked.value, checked.state)
        (FirstHit.recorded_support _ _ _ hchecked)).eval answers hac
      rw [hcheckedWin] at hw
      obtain ⟨hfresh, message, witness, hof, hv, hsub⟩ :=
        PaddedExtraction.check_accepting answers publicKey interaction.2 forgery hw
      refine ⟨hlength, forgery, rfl, hfresh, message, witness, hof, hv, fun input hq => ?_⟩
      obtain ⟨prior, hev⟩ := PaddedExtraction.public_occurrence _ hp before checked hchecked answers hac input
        (hsub _ hq)
      exact ⟨prior, hevents ▸ hev⟩
end ClaudeWCT.W9.T3.Security.WotsExtract
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.WotsExtract
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB
end ClaudeWCT.W9.T3.Security.Wots
end
-- ==== merged from T3_Secc_LargeContactChain ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeContactChain : DecidableEq T3.Cache := Classical.decEq _
def wotsAddr (a : ChainGraph.Address) : Wots.ChainAddr := ⟨⟨a.layer, a.tree.val, a.leaf.val⟩, a.chain.val⟩
def Disclosed (A : Answers) (published : T3.Cache) (c : Coord) : Prop :=
  c ∈ keygenDisclosed ∨ ∃ request, c ∈ signDisclosed A published request
end SigGolfCandidate.T3.Security.LargeCoupling
end
