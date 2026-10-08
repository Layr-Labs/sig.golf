import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessForced
import SigGolfCandidate.T3.Secc.PairGuessWorld

/-!
# Predicate observations and sampler-generic secret-guess engines (campaign X1, stage A)

* `restrictBy` / `discloseBy` / `trialBy`: observing a function `view` (or a Boolean test) of one coordinate of a
  uniform table restricted to `allowed`; `bind_discloseBy` / `bind_trialBy` are the conditioning identities. The
  equality-trial engine of `SecretGuessObservation` is the special case `view = fun value => decide (value = c)`.
* `Sampler`, `withImpl`, `withRun`: the lazy engine of `SecretGuessObservation` with an arbitrary law for trial
  outcomes and disclosed values (same `State`, same `afterTrial` / `afterDisclosure` bookkeeping). Used for the FTS
  seed families, whose seeds are evaluations of a hidden coefficient vector rather than independent cells.
* Bounds for `withRun` under an abstract hazard: a pair potential (`withRun_pair_le`) and the first-guess forcing
  machinery (`withRun_event_le_forced_slot`). A monotone `Bad` flag switches the hazard off (FTS overflow).
These live in a new module (not in `SecretGuessObservation.lean`) to avoid rebuilding its 80 dependents.
-/

section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal UniformTableCompletion
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Out : Type} [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

/-- Restrict coordinate `coordinate` to the values whose `view` is `out`. -/
noncomputable def restrictBy (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out) (out : Out) :
    Coordinate → Finset Value :=
  Function.update allowed coordinate ((allowed coordinate).filter fun value => out = view value)
/-- Law of `view (labels coordinate)` for `labels` uniform on the table `allowed`. -/
noncomputable def discloseBy (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out) :
    SPMF Out :=
  complete allowed >>= fun labels => pure (view (labels coordinate))
/-- A Boolean test of one coordinate: `discloseBy` with `Out = Bool`. -/
noncomputable abbrev trialBy (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (test : Value → Bool) :
    SPMF Bool :=
  discloseBy allowed coordinate test
theorem restrictBy_subset (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) (other : Coordinate) : restrictBy allowed coordinate view out other ⊆ allowed other := by
  by_cases heq : other = coordinate
  · subst other
    rw [restrictBy, Function.update_self]
    exact Finset.filter_subset _ _
  · simp only [restrictBy, Function.update_of_ne heq, Finset.Subset.refl]
theorem mem_restrictBy_self (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) (value : Value) :
    value ∈ restrictBy allowed coordinate view out coordinate ↔ value ∈ allowed coordinate ∧ out = view value := by
  rw [restrictBy, Function.update_self, Finset.mem_filter]
theorem restrictBy_other (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) {other : Coordinate} (h : other ≠ coordinate) :
    restrictBy allowed coordinate view out other = allowed other := by
  rw [restrictBy, Function.update_of_ne h]
theorem restrictBy_membership (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) (labels : Coordinate → Value) :
    (∀ other, labels other ∈ restrictBy allowed coordinate view out other) ↔
      (∀ other, labels other ∈ allowed other) ∧ out = view (labels coordinate) := by
  constructor
  · intro h
    refine ⟨fun other => restrictBy_subset allowed coordinate view out other (h other), ?_⟩
    have hc := h coordinate
    rw [restrictBy, Function.update_self, Finset.mem_filter] at hc
    exact hc.2
  · rintro ⟨h, hh⟩ other
    by_cases heq : other = coordinate
    · subst other
      rw [restrictBy, Function.update_self]
      exact Finset.mem_filter.mpr ⟨h coordinate, hh⟩
    · simpa only [restrictBy, Function.update_of_ne heq] using h other
theorem restrictBy_mass (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) (labels : Coordinate → Value) :
    (if out = view (labels coordinate) then complete allowed labels else 0) =
      restrictionWeight allowed (restrictBy allowed coordinate view out) *
        complete (restrictBy allowed coordinate view out) labels := by
  have h := restrict_guard allowed _ (restrictBy_subset allowed coordinate view out) _
    (restrictBy_membership allowed coordinate view out) labels
  by_cases hh : out = view (labels coordinate)
  · simpa only [if_pos hh] using h
  · simpa only [if_neg hh] using h
theorem discloseBy_apply (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) :
    discloseBy allowed coordinate view out = restrictionWeight allowed (restrictBy allowed coordinate view out) := by
  rw [discloseBy, SPMF.bind_apply_eq_tsum]
  simp only [SPMF.pure_apply, mul_ite, mul_one, mul_zero, restrictBy_mass, ENNReal.tsum_mul_left,
    weight_tsum_complete]
theorem discloseBy_mass (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) (labels : Coordinate → Value) :
    discloseBy allowed coordinate view out * complete (restrictBy allowed coordinate view out) labels =
      if out = view (labels coordinate) then complete allowed labels else 0 := by
  rw [discloseBy_apply, restrictBy_mass]
/-- Conditioning identity: observing `view` of one coordinate, then completing the restricted table, is the uniform
table. -/
theorem bind_discloseBy {Result : Type} (allowed : Coordinate → Finset Value) (coordinate : Coordinate)
    (view : Value → Out) (next : Out → (Coordinate → Value) → SPMF Result) :
    (complete allowed >>= fun labels => next (view (labels coordinate)) labels) =
      (discloseBy allowed coordinate view >>= fun out =>
        complete (restrictBy allowed coordinate view out) >>= next out) := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, ← ENNReal.tsum_mul_left, ← mul_assoc, discloseBy_mass, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro labels
  rw [tsum_eq_single (view (labels coordinate))]
  · simp only [if_true]
  · intro out hout
    rw [if_neg hout]
theorem bind_trialBy {Result : Type} (allowed : Coordinate → Finset Value) (coordinate : Coordinate)
    (test : Value → Bool) (next : Bool → (Coordinate → Value) → SPMF Result) :
    (complete allowed >>= fun labels => next (test (labels coordinate)) labels) =
      (trialBy allowed coordinate test >>= fun hit => complete (restrictBy allowed coordinate test hit) >>= next hit) :=
  bind_discloseBy allowed coordinate test next
theorem discloseBy_nonempty (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) (hout : discloseBy allowed coordinate view out ≠ 0) :
    ∀ other, (restrictBy allowed coordinate view out other).Nonempty := by
  by_contra hn
  rw [discloseBy_apply, weight_of_empty _ _ hn] at hout
  exact hout rfl
end SphincsSecurity.Concrete.SecretGuessObservation
end

section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- Laws of trial outcomes and disclosed values, as functions of the bookkeeping state. -/
structure Sampler (Coordinate Value Memory : Type) where
  trialLaw : State Coordinate Value Memory → Coordinate → Value → SPMF Bool
  discloseLaw : State Coordinate Value Memory → Coordinate → SPMF Value

variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

/-- The lazy engine with sampler `sampler`: auxiliary queries as in `lazyImpl`, secret queries from the sampler. -/
noncomputable def withImpl (environment : Environment auxSpec Coordinate Value Memory)
    (sampler : Sampler Coordinate Value Memory) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => lazyImpl environment (.inl input)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      (fun hit => (hit, afterTrial environment state coordinate candidate hit)) <$>
        sampler.trialLaw state coordinate candidate
  | .inr (.inr coordinate) => StateT.mk fun state =>
      (fun value => (value, afterDisclosure environment state coordinate value)) <$>
        sampler.discloseLaw state coordinate
noncomputable def withRun {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (sampler : Sampler Coordinate Value Memory) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) :=
  runWith (withImpl environment sampler) computation state
variable (environment : Environment auxSpec Coordinate Value Memory) (sampler : Sampler Coordinate Value Memory)
/-- Every step of `withImpl` lands on an `afterTrial` / `afterDisclosure` / auxiliary-memory successor. -/
theorem withImpl_cases (state : State Coordinate Value Memory) (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (withImpl environment sampler input).run state result ≠ 0) :
    (∃ memory, result.2 = { state with memory := memory }) ∨
      (∃ coordinate candidate hit, input = .inr (.inl (coordinate, candidate)) ∧
        sampler.trialLaw state coordinate candidate hit ≠ 0 ∧
        result.2 = afterTrial environment state coordinate candidate hit) ∨
      (∃ coordinate value, input = .inr (.inr coordinate) ∧ sampler.discloseLaw state coordinate value ≠ 0 ∧
        result.2 = afterDisclosure environment state coordinate value) := by
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · simp only [withImpl, lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
      Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    exact Or.inl ⟨answer.2, rfl⟩
  · simp only [withImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
      Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨hit, hh, rfl⟩ := hr
    exact Or.inr (Or.inl ⟨coordinate, candidate, hit, rfl, hh, rfl⟩)
  · simp only [withImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
      Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨value, hv, rfl⟩ := hr
    exact Or.inr (Or.inr ⟨coordinate, value, rfl, hv, rfl⟩)
theorem withImpl_probes (state : State Coordinate Value Memory) (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (withImpl environment sampler input).run state result ≠ 0) :
    result.2.probes = state.probes + probeStep input := by
  rcases withImpl_cases environment sampler state input result hr with ⟨memory, h⟩ | ⟨c, v, hit, hi, -, h⟩ |
    ⟨c, value, hi, -, h⟩
  · rw [h]
    rcases input with input | (⟨c, v⟩ | c)
    · rfl
    · simp only [withImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      obtain ⟨hit, -, he⟩ := hr
      have := congrArg (fun s : State Coordinate Value Memory => s.probes) (he ▸ h)
      simp only [afterTrial] at this
      omega
    · rfl
  · subst hi; rw [h]; rfl
  · subst hi; rw [h]; rfl
theorem withRun_preserves {Result : Type} (invariant : State Coordinate Value Memory → Prop)
    (hstep : ∀ state, invariant state → ∀ input result,
      (withImpl environment sampler input).run state result ≠ 0 → invariant result.2)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hinvariant : invariant state) (result : Result × State Coordinate Value Memory)
    (hr : withRun environment sampler computation state result ≠ 0) : invariant result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [withRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact hinvariant
  | query_bind input next ih =>
      rw [withRun, runWith_query_bind, RetainedObservation.bind_nonzero] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 middle.2 (hstep state hinvariant input middle hm) result hr
theorem withRun_probes_mono {Result : Type} (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (result : Result × State Coordinate Value Memory)
    (hr : withRun environment sampler computation state result ≠ 0) : state.probes ≤ result.2.probes := by
  apply withRun_preserves environment sampler (fun next => state.probes ≤ next.probes) _ computation state le_rfl
    result hr
  intro middle hm input next hn
  rw [withImpl_probes environment sampler middle input next hn]
  exact hm.trans (Nat.le_add_right _ _)
theorem afterTrial_guesses_sub (state : State Coordinate Value Memory) (hs : state.guesses ⊆ state.retired)
    (coordinate : Coordinate) (candidate : Value) (hit : Bool) :
    (afterTrial environment state coordinate candidate hit).guesses ⊆
      (afterTrial environment state coordinate candidate hit).retired := by
  simp only [afterTrial]
  split
  · rename_i hh
    rw [if_pos hh.1]
    exact Finset.insert_subset_insert coordinate hs
  · split
    · exact hs.trans (Finset.subset_insert _ _)
    · exact hs
/-- `guesses ⊆ retired` is preserved by every engine step. -/
theorem withImpl_guesses_sub (state : State Coordinate Value Memory) (hs : state.guesses ⊆ state.retired)
    (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (withImpl environment sampler input).run state result ≠ 0) : result.2.guesses ⊆ result.2.retired := by
  rcases withImpl_cases environment sampler state input result hr with ⟨memory, h⟩ | ⟨c, v, hit, -, -, h⟩ |
    ⟨c, value, -, -, h⟩
  · rw [h]; exact hs
  · rw [h]; exact afterTrial_guesses_sub environment state hs c v hit
  · rw [h]; exact hs.trans (Finset.subset_insert _ _)

/-! ### Abstract hazard and the pair bound -/

/-- Invariant `Inv` with a monotone failure flag `Bad`: steps preserve `Inv`, keep `Bad`, and keep `guesses ⊆ retired`;
while `¬Bad` and at most one guess was made, a trial at a non-retired coordinate hits with probability
`≤ (size - budget)⁻¹`. -/
structure Hazard (size budget : Nat) (Inv Bad : State Coordinate Value Memory → Prop) : Prop where
  step : ∀ state, Inv state → ∀ input result, (withImpl environment sampler input).run state result ≠ 0 →
    Inv result.2
  bad : ∀ state, Inv state → Bad state → ∀ input result, (withImpl environment sampler input).run state result ≠ 0 →
    Bad result.2
  guesses : ∀ state, Inv state → state.guesses ⊆ state.retired
  hazard : ∀ state, Inv state → ¬Bad state → state.guesses.card ≤ 1 → state.probes < budget →
    ∀ coordinate candidate, coordinate ∉ state.retired →
      sampler.trialLaw state coordinate candidate true ≤ ((size - budget : Nat) : ENNReal)⁻¹
variable {environment sampler}
private theorem expectation_const_le' {Result : Type} (law : SPMF Result) (value : ENNReal) :
    (∑' result, Pr[= result | law] * value) ≤ value := by
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left' tsum_probOutput_le_one
/-- The pair potential, switched off under `Bad`. -/
noncomputable def pairPotentialB (Bad : State Coordinate Value Memory → Prop) (size budget : Nat)
    (state : State Coordinate Value Memory) : ENNReal :=
  if Bad state then 0 else pairPotential size budget state
theorem tsum_le_of_support {Result : Type} (law : SPMF Result) (f : Result → ENNReal) (c : ENNReal)
    (h : ∀ result, law result ≠ 0 → f result ≤ c) : (∑' result, Pr[= result | law] * f result) ≤ c := by
  refine le_trans (ENNReal.tsum_le_tsum fun result => ?_) (expectation_const_le' law c)
  by_cases hz : law result = 0
  · simp only [SPMF.probOutput_eq_apply, hz, zero_mul, le_refl]
  · exact mul_le_mul' le_rfl (h result hz)
theorem pairPotential_afterTrial_with (size budget : Nat) (state : State Coordinate Value Memory)
    (hs : state.guesses ⊆ state.retired) (coordinate : Coordinate) (candidate : Value) (law : SPMF Bool)
    (hrate : state.guesses.card ≤ 1 → state.probes < budget → coordinate ∉ state.retired →
      law true ≤ ((size - budget : Nat) : ENNReal)⁻¹) :
    (∑' hit, Pr[= hit | law] * pairPotential size budget (afterTrial environment state coordinate candidate hit)) ≤
      pairPotential size budget state := by
  classical
  by_cases hroom : state.probes < budget
  · have hwithin : state.probes ≤ budget := Nat.le_of_lt hroom
    have hafter : state.probes + 1 ≤ budget := hroom
    have hremaining : budget - state.probes = (budget - (state.probes + 1)) + 1 := by omega
    have hp (hit : Bool) : (afterTrial environment state coordinate candidate hit).probes = state.probes + 1 := rfl
    simp only [pairPotential, hp, afterTrial_guesses_card environment state hs, if_pos hafter, if_pos hwithin]
    by_cases hc : coordinate ∈ state.retired
    · simp only [hc, not_true_eq_false, and_false, if_false, Nat.add_zero]
      exact (expectation_const_le' _ _).trans (pairValue_mono _ _ (Nat.sub_le_sub_left (by omega) _))
    · by_cases hg : state.guesses.card ≤ 1
      · simp only [hc, not_false_eq_true, and_true]
        rw [hremaining]
        exact pairValue_trial _ _ (hrate hg hroom hc) _ _
      · obtain ⟨k, hk⟩ : ∃ k, state.guesses.card = k + 2 := ⟨state.guesses.card - 2, by omega⟩
        have h1 : ∀ hit : Bool, pairValue ((size - budget : Nat) : ENNReal)⁻¹ (budget - (state.probes + 1))
            (state.guesses.card + if hit = true ∧ coordinate ∉ state.retired then 1 else 0) = 1 := by
          intro hit
          rw [hk, show k + 2 + (if hit = true ∧ coordinate ∉ state.retired then 1 else 0) =
            (k + if hit = true ∧ coordinate ∉ state.retired then 1 else 0) + 2 by omega]
          rfl
        have h2 : pairValue ((size - budget : Nat) : ENNReal)⁻¹ (budget - state.probes) state.guesses.card = 1 := by
          rw [hk]; rfl
        simp only [h1, h2]
        exact expectation_const_le' law 1
  · have hafter : ¬state.probes + 1 ≤ budget := by omega
    simp only [pairPotential, afterTrial, if_neg hafter, mul_zero, tsum_zero]
    exact bot_le
theorem withImpl_pairPotentialB {size budget : Nat} {Inv Bad : State Coordinate Value Memory → Prop}
    (H : Hazard environment sampler size budget Inv Bad) (state : State Coordinate Value Memory) (hs : Inv state)
    (input : (World auxSpec Coordinate Value).Domain) :
    (∑' result, Pr[= result | (withImpl environment sampler input).run state] *
      pairPotentialB Bad size budget result.2) ≤ pairPotentialB Bad size budget state := by
  by_cases hbad : Bad state
  · refine tsum_le_of_support _ _ _ fun result hz => ?_
    simp only [pairPotentialB, if_pos (H.bad state hs hbad input result hz)]
    exact bot_le
  · have hle : (∑' result, Pr[= result | (withImpl environment sampler input).run state] *
        pairPotentialB Bad size budget result.2) ≤
        ∑' result, Pr[= result | (withImpl environment sampler input).run state] *
          pairPotential size budget result.2 := by
      refine ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl ?_
      unfold pairPotentialB
      split
      · exact bot_le
      · exact le_rfl
    refine hle.trans ?_
    rw [pairPotentialB, if_neg hbad]
    rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
    · refine tsum_le_of_support _ _ _ fun result hz => ?_
      rcases withImpl_cases environment sampler state _ result hz with ⟨memory, h⟩ | ⟨c, v, hit, hi, -, -⟩ |
        ⟨c, value, hi, -, -⟩
      · rw [h]; exact le_rfl
      · cases hi
      · cases hi
    · simp only [withImpl, StateT.run_mk, tsum_probOutput_map_mul]
      exact pairPotential_afterTrial_with size budget state (H.guesses state hs) coordinate candidate _
        (fun hg hp hc => H.hazard state hs hbad hg hp coordinate candidate hc)
    · refine tsum_le_of_support _ _ _ fun result hz => ?_
      rcases withImpl_cases environment sampler state _ result hz with ⟨memory, h⟩ | ⟨c, v, hit, hi, -, -⟩ |
        ⟨c, value, hi, -, h⟩
      · rw [h]; exact le_rfl
      · cases hi
      · rw [h]; exact le_rfl
theorem withRun_pairPotentialB {Result : Type} {size budget : Nat} {Inv Bad : State Coordinate Value Memory → Prop}
    (H : Hazard environment sampler size budget Inv Bad) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Inv state) :
    (∑' result, Pr[= result | withRun environment sampler computation state] *
      pairPotentialB Bad size budget result.2) ≤ pairPotentialB Bad size budget state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [withRun, runWith_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [withRun, runWith_query_bind, tsum_probOutput_bind_mul]
      apply le_trans _ (withImpl_pairPotentialB H state hs input)
      apply ENNReal.tsum_le_tsum
      intro middle
      by_cases hm : (withImpl environment sampler input).run state middle = 0
      · simp only [SPMF.probOutput_eq_apply, hm, zero_mul, le_refl]
      · exact mul_le_mul' le_rfl (ih middle.1 middle.2 (H.step state hs input middle hm))
/-- Pair bound for any sampler with a hazard: two new guesses within the budget, without `Bad`, have probability at
most `C(budget, 2) · (size - budget)⁻²`. -/
theorem withRun_pair_le {Result : Type} {size budget : Nat} {Inv Bad : State Coordinate Value Memory → Prop}
    (H : Hazard environment sampler size budget Inv Bad) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Inv state) (hprobes : state.probes = 0)
    (hguesses : state.guesses = ∅) :
    Pr[fun result => 2 ≤ result.2.guesses.card ∧ result.2.probes ≤ budget ∧ ¬Bad result.2 |
      withRun environment sampler computation state] ≤
      (budget.choose 2 : ENNReal) * ((size - budget : Nat) : ENNReal)⁻¹ ^ 2 := by
  apply (probEvent_le_tsum_probOutput_mul_cost_of_mem_support _ _
    (fun result => pairPotentialB Bad size budget result.2) ?_).trans
  · refine (withRun_pairPotentialB H computation state hs).trans ?_
    unfold pairPotentialB
    split
    · exact bot_le
    · simp [pairPotential, hprobes, hguesses, pairValue]
  · intro result _ h
    rw [pairPotentialB, if_neg h.2.2]
    exact pairPotential_two _ _ result.2 h.2.1 h.1
end SphincsSecurity.Concrete.SecretGuessObservation
end

section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
variable (environment : Environment auxSpec Coordinate Value Memory) (sampler : Sampler Coordinate Value Memory)

/-! ### First-guess forcing -/

/-- Forcing at `slot` applies to the first new guess only: fresh coordinate, no earlier guess, positive hit mass. -/
def EligibleWith (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate) (candidate : Value) :
    Prop :=
  state.probes = slot ∧ coordinate ∉ state.retired ∧ state.guesses = ∅ ∧
    sampler.trialLaw state coordinate candidate true ≠ 0
noncomputable def forcedTrialWith (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate)
    (candidate : Value) : SPMF Bool :=
  if EligibleWith sampler slot state coordinate candidate then pure true else sampler.trialLaw state coordinate candidate
noncomputable def forcedWithImpl (slot : Nat) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => withImpl environment sampler (.inl input)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      (fun hit => (hit, afterTrial environment state coordinate candidate hit)) <$>
        forcedTrialWith sampler slot state coordinate candidate
  | .inr (.inr coordinate) => withImpl environment sampler (.inr (.inr coordinate))
noncomputable def forcedWithRun {Result : Type} (slot : Nat) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) :=
  runWith (forcedWithImpl environment sampler slot) computation state
theorem forcedTrialWith_nonzero (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate)
    (candidate : Value) (hit : Bool) (hhit : forcedTrialWith sampler slot state coordinate candidate hit ≠ 0) :
    sampler.trialLaw state coordinate candidate hit ≠ 0 := by
  by_cases he : EligibleWith sampler slot state coordinate candidate
  · simp only [forcedTrialWith, if_pos he, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hhit
    subst hit
    exact he.2.2.2
  · simpa only [forcedTrialWith, if_neg he] using hhit
theorem forcedWithImpl_nonzero (slot : Nat) (state : State Coordinate Value Memory)
    (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (forcedWithImpl environment sampler slot input).run state result ≠ 0) :
    (withImpl environment sampler input).run state result ≠ 0 := by
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · exact hr
  · simp only [forcedWithImpl, withImpl, StateT.run_mk, map_eq_bind_pure_comp,
      RetainedObservation.bind_nonzero] at hr ⊢
    obtain ⟨hit, hh, hr⟩ := hr
    exact ⟨hit, forcedTrialWith_nonzero sampler slot state coordinate candidate hit hh, hr⟩
  · exact hr
noncomputable def hitTrialWith (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate)
    (candidate : Value) : SPMF Bool :=
  if state.probes = slot then
    sampler.trialLaw state coordinate candidate >>= fun hit =>
      if hit = true ∧ coordinate ∉ state.retired ∧ state.guesses = ∅ then pure hit else failure
  else sampler.trialLaw state coordinate candidate
noncomputable def trialFactorWith (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate)
    (candidate : Value) : ENNReal :=
  if state.probes = slot then
    if coordinate ∉ state.retired ∧ state.guesses = ∅ then sampler.trialLaw state coordinate candidate true else 0
  else 1
theorem hitTrialWith_apply (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate)
    (candidate : Value) (hit : Bool) :
    hitTrialWith sampler slot state coordinate candidate hit =
      trialFactorWith sampler slot state coordinate candidate * forcedTrialWith sampler slot state coordinate candidate hit := by
  by_cases hs : state.probes = slot
  · by_cases hc : coordinate ∉ state.retired ∧ state.guesses = ∅
    · have hmass : hitTrialWith sampler slot state coordinate candidate hit =
          if hit = true then sampler.trialLaw state coordinate candidate true else 0 := by
        rw [hitTrialWith, if_pos hs, SPMF.bind_apply_eq_tsum]
        simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, false_and, if_false, true_and,
          hc, and_self, SPMF.failure_apply, mul_zero, add_zero]
        split <;> simp_all
      rw [hmass]
      by_cases hp : sampler.trialLaw state coordinate candidate true = 0
      · simp only [trialFactorWith, if_pos hs, if_pos hc, hp, zero_mul, ite_self]
      · have he : EligibleWith sampler slot state coordinate candidate := ⟨hs, hc.1, hc.2, hp⟩
        simp only [trialFactorWith, if_pos hs, if_pos hc, forcedTrialWith, if_pos he, SPMF.pure_apply,
          mul_ite, mul_one, mul_zero]
    · have hz : hitTrialWith sampler slot state coordinate candidate hit = 0 := by
        rw [hitTrialWith, if_pos hs, SPMF.bind_apply_eq_tsum]
        refine ENNReal.tsum_eq_zero.mpr fun h => ?_
        rw [if_neg (fun hh => hc ⟨hh.2.1, hh.2.2⟩), SPMF.failure_apply, mul_zero]
      simp only [hz, trialFactorWith, if_pos hs, if_neg hc, zero_mul]
  · have he : ¬EligibleWith sampler slot state coordinate candidate := fun h => hs h.1
    simp only [hitTrialWith, trialFactorWith, if_neg hs, forcedTrialWith, if_neg he, one_mul]
theorem hitTrialWith_bind_apply {Result : Type} (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) (next : Bool → SPMF Result) (result : Result) :
    (hitTrialWith sampler slot state coordinate candidate >>= next) result =
      trialFactorWith sampler slot state coordinate candidate *
        (forcedTrialWith sampler slot state coordinate candidate >>= next) result := by
  simp only [SPMF.bind_apply_eq_tsum, hitTrialWith_apply, mul_assoc, ENNReal.tsum_mul_left]
noncomputable def hitWithImpl (slot : Nat) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => withImpl environment sampler (.inl input)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      (fun hit => (hit, afterTrial environment state coordinate candidate hit)) <$>
        hitTrialWith sampler slot state coordinate candidate
  | .inr (.inr coordinate) => withImpl environment sampler (.inr (.inr coordinate))
noncomputable def forceFactorWith (slot : Nat) (state : State Coordinate Value Memory) :
    (World auxSpec Coordinate Value).Domain → ENNReal
  | .inr (.inl (coordinate, candidate)) => trialFactorWith sampler slot state coordinate candidate
  | _ => 1
theorem hitWithImpl_apply (slot : Nat) (state : State Coordinate Value Memory)
    (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory) :
    (hitWithImpl environment sampler slot input).run state result =
      forceFactorWith sampler slot state input * (forcedWithImpl environment sampler slot input).run state result := by
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · simp only [hitWithImpl, forcedWithImpl, forceFactorWith, one_mul]
  · simp only [hitWithImpl, forcedWithImpl, forceFactorWith, StateT.run_mk, map_eq_bind_pure_comp,
      Function.comp_def]
    exact hitTrialWith_bind_apply sampler slot state coordinate candidate
      (fun hit : Bool => pure (hit, afterTrial environment state coordinate candidate hit)) result
  · simp only [hitWithImpl, forcedWithImpl, forceFactorWith, one_mul]
noncomputable def hitWithRun {Result : Type} (slot : Nat) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) :=
  runWith (hitWithImpl environment sampler slot) computation state >>= fun result =>
    if slot < result.2.probes then pure result else (failure : SPMF _)
theorem hitWithRun_weighted_forced {Result : Type} (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | hitWithRun environment sampler slot computation state] * payoff result) =
      ∑' result, Pr[= result | WeightedQuery.run (forcedWithImpl environment sampler slot) (forceFactorWith sampler slot)
        computation (state, 1)] * (forceWeight slot result.2 * payoff (result.1, result.2.1)) := by
  have h := WeightedQuery.run_payoff (hitWithImpl environment sampler slot) (forcedWithImpl environment sampler slot)
    (forceFactorWith sampler slot) (hitWithImpl_apply environment sampler slot) computation state 1
    (fun result => if slot < result.2.probes then payoff result else 0)
  simp only [one_mul] at h
  rw [hitWithRun, tsum_probOutput_bind_mul]
  convert h using 1
  · apply tsum_congr
    intro result
    congr 1
    by_cases hp : slot < result.2.probes
    · simp only [if_pos hp, tsum_probOutput_pure_mul]
    · simp only [if_neg hp, SPMF.probOutput_eq_apply, SPMF.failure_apply, zero_mul, tsum_zero]
  · apply tsum_congr
    intro result
    congr 1
    simp only [forceWeight, mul_ite, ite_mul, mul_zero, zero_mul]
theorem forceFactorWith_le_one (slot : Nat) (state : State Coordinate Value Memory)
    (input : (World auxSpec Coordinate Value).Domain) : forceFactorWith sampler slot state input ≤ 1 := by
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · exact le_rfl
  · simp only [forceFactorWith, trialFactorWith]
    split
    · split
      · simpa only [SPMF.probOutput_eq_apply] using
          (show Pr[= true | sampler.trialLaw state coordinate candidate] ≤ 1 from probOutput_le_one)
      · exact bot_le
    · exact le_rfl
  · exact le_rfl
variable {environment sampler}
theorem forceFactorWith_weight_bound {size budget : Nat} {Inv Bad : State Coordinate Value Memory → Prop}
    (H : Hazard environment sampler size budget Inv Bad) (slot : Nat) (hslot : slot < budget)
    (state : State Coordinate Value Memory) (weight : ENNReal) (hs : Inv state) (hw : weight ≤ 1)
    (hlate : slot < state.probes → weight ≤ ((size - budget : Nat) : ENNReal)⁻¹ ∨ Bad state)
    (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (forcedWithImpl environment sampler slot input).run state result ≠ 0) :
    weight * forceFactorWith sampler slot state input ≤ 1 ∧
      (slot < result.2.probes →
        weight * forceFactorWith sampler slot state input ≤ ((size - budget : Nat) : ENNReal)⁻¹ ∨ Bad result.2) := by
  have hm : weight * forceFactorWith sampler slot state input ≤ weight :=
    mul_le_of_le_one_right' (forceFactorWith_le_one sampler slot state input)
  have hwith := forcedWithImpl_nonzero environment sampler slot state input result hr
  refine ⟨hm.trans hw, fun hafter => ?_⟩
  by_cases hb : slot < state.probes
  · rcases hlate hb with h | h
    · exact Or.inl (hm.trans h)
    · exact Or.inr (H.bad state hs h input result hwith)
  by_cases hbad : Bad state
  · exact Or.inr (H.bad state hs hbad input result hwith)
  left
  have hp := withImpl_probes environment sampler state input result hwith
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · simp only [probeStep, Nat.add_zero] at hp; omega
  · change result.2.probes = state.probes + 1 at hp
    have he : state.probes = slot := by omega
    simp only [forceFactorWith, trialFactorWith, if_pos he]
    split
    next hc =>
      have hg : state.guesses.card ≤ 1 := by rw [hc.2]; simp
      exact (mul_le_of_le_one_left' hw).trans
        (H.hazard state hs hbad hg (he ▸ hslot) coordinate candidate hc.1)
    next hc => simp only [mul_zero]; exact bot_le
  · simp only [probeStep, Nat.add_zero] at hp; omega
theorem weightedForcedWith_weight_bound {Result : Type} {size budget : Nat}
    {Inv Bad : State Coordinate Value Memory → Prop} (H : Hazard environment sampler size budget Inv Bad)
    (slot : Nat) (hslot : slot < budget) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Inv state) (hp : state.probes ≤ slot)
    (result : Result × State Coordinate Value Memory × ENNReal)
    (hr : WeightedQuery.run (forcedWithImpl environment sampler slot) (forceFactorWith sampler slot) computation
      (state, 1) result ≠ 0) :
    forceWeight slot result.2 ≤ ((size - budget : Nat) : ENNReal)⁻¹ ∨ Bad result.2.1 := by
  let valid (st : State Coordinate Value Memory × ENNReal) : Prop :=
    Inv st.1 ∧ st.2 ≤ 1 ∧ (slot < st.1.probes → st.2 ≤ ((size - budget : Nat) : ENNReal)⁻¹ ∨ Bad st.1)
  have hstep (st : State Coordinate Value Memory × ENNReal) (hv : valid st)
      (input : (World auxSpec Coordinate Value).Domain)
      (middle : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
      (hm : (forcedWithImpl environment sampler slot input).run st.1 middle ≠ 0) :
      valid (middle.2, st.2 * forceFactorWith sampler slot st.1 input) :=
    ⟨H.step st.1 hv.1 input middle (forcedWithImpl_nonzero environment sampler slot st.1 input middle hm),
      forceFactorWith_weight_bound H slot hslot st.1 st.2 hv.1 hv.2.1 hv.2.2 input middle hm⟩
  have hinitial : valid (state, 1) := ⟨hs, le_rfl, fun h => absurd (show slot < state.probes from h) (by omega)⟩
  have h := WeightedQuery.run_preserves (forcedWithImpl environment sampler slot) (forceFactorWith sampler slot)
    valid hstep computation (state, 1) hinitial result hr
  rw [forceWeight]
  split
  · exact h.2.2 ‹_›
  · exact Or.inl bot_le
theorem hitWithRun_payoff_le_forced {Result : Type} {size budget : Nat}
    {Inv Bad : State Coordinate Value Memory → Prop} (H : Hazard environment sampler size budget Inv Bad)
    (slot : Nat) (hslot : slot < budget) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Inv state) (hp : state.probes ≤ slot)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | hitWithRun environment sampler slot computation state] *
      (if Bad result.2 then 0 else payoff result)) ≤
      ((size - budget : Nat) : ENNReal)⁻¹ *
        (∑' result, Pr[= result | forcedWithRun environment sampler slot computation state] * payoff result) := by
  rw [hitWithRun_weighted_forced]
  have hforget := congrArg (fun law : SPMF (Result × State Coordinate Value Memory) =>
    ∑' result, Pr[= result | law] * payoff result)
    (WeightedQuery.run_forget (forcedWithImpl environment sampler slot) (forceFactorWith sampler slot) computation
      (state, 1))
  rw [tsum_probOutput_map_mul] at hforget
  rw [forcedWithRun, runWith, ← show (∑' result, Pr[= result | WeightedQuery.run (forcedWithImpl environment sampler slot)
      (forceFactorWith sampler slot) computation (state, 1)] * payoff (result.1, result.2.1)) =
      (∑' result, Pr[= result | (simulateQ (forcedWithImpl environment sampler slot) computation).run state] *
        payoff result) from hforget, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hz : WeightedQuery.run (forcedWithImpl environment sampler slot) (forceFactorWith sampler slot) computation
    (state, 1) result = 0
  · simp only [SPMF.probOutput_eq_apply, hz, zero_mul, mul_zero, le_refl]
  · rw [mul_left_comm (((size - budget : Nat) : ENNReal)⁻¹)]
    apply mul_le_mul' le_rfl
    dsimp only
    rcases weightedForcedWith_weight_bound H slot hslot computation state hs hp result hz with h | h
    · split
      · simp only [mul_zero]; exact bot_le
      · exact mul_le_mul' h le_rfl
    · rw [if_pos h, mul_zero]; exact bot_le
end SphincsSecurity.Concrete.SecretGuessObservation
end

section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
variable (environment : Environment auxSpec Coordinate Value Memory) (sampler : Sampler Coordinate Value Memory)

/-! ### First-guess decomposition -/

theorem hitWithImpl_eq_with (slot : Nat) (state : State Coordinate Value Memory) (hne : state.probes ≠ slot)
    (input : (World auxSpec Coordinate Value).Domain) :
    (hitWithImpl environment sampler slot input).run state = (withImpl environment sampler input).run state := by
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · rfl
  · simp only [hitWithImpl, withImpl, StateT.run_mk, hitTrialWith, if_neg hne]
  · rfl
theorem hitWithImplRun_after {Result : Type} (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hslot : slot < state.probes) :
    runWith (hitWithImpl environment sampler slot) computation state = withRun environment sampler computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [withRun, runWith_pure]
  | query_bind input next ih =>
      rw [runWith_query_bind, withRun, runWith_query_bind,
        hitWithImpl_eq_with environment sampler slot state (Nat.ne_of_gt hslot)]
      apply RetainedObservation.bind_congr
      intro middle hm
      have hp := withImpl_probes environment sampler state input middle hm
      apply ih middle.1 middle.2
      rw [hp]
      exact hslot.trans_le (Nat.le_add_right _ _)
theorem hitWithRun_apply {Result : Type} (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (result : Result × State Coordinate Value Memory) : hitWithRun environment sampler slot computation state result =
      if slot < result.2.probes then runWith (hitWithImpl environment sampler slot) computation state result else 0 := by
  rw [hitWithRun, SPMF.bind_apply_eq_tsum, tsum_eq_single result]
  · split <;> simp only [SPMF.pure_apply_self, SPMF.failure_apply, mul_one, mul_zero]
  · intro other hother
    split <;> simp only [SPMF.pure_apply, if_neg (Ne.symm hother), SPMF.failure_apply, mul_zero]
theorem hitWithRun_after {Result : Type} (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hslot : slot < state.probes) :
    hitWithRun environment sampler slot computation state = withRun environment sampler computation state := by
  apply SPMF.ext
  intro result
  rw [hitWithRun_apply, hitWithImplRun_after environment sampler slot computation state hslot]
  by_cases hp : slot < result.2.probes
  · exact if_pos hp
  · rw [if_neg hp]
    symm
    by_contra hr
    exact hp (hslot.trans_le (withRun_probes_mono environment sampler computation state result hr))
theorem hitWithRun_query_bind {Result : Type} (slot : Nat) (input : (World auxSpec Coordinate Value).Domain)
    (next : (World auxSpec Coordinate Value).Range input → OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) :
    hitWithRun environment sampler slot (liftM ((World auxSpec Coordinate Value).query input) >>= next) state =
      ((hitWithImpl environment sampler slot input).run state >>= fun middle =>
        hitWithRun environment sampler slot (next middle.1) middle.2) := by
  simp only [hitWithRun, runWith_query_bind, bind_assoc]
theorem hitWithRun_probe_at {Result : Type} (coordinate : Coordinate) (candidate : Value)
    (next : Bool → OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :
    hitWithRun environment sampler state.probes
      (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state =
      (sampler.trialLaw state coordinate candidate >>= fun hit =>
        if hit = true ∧ coordinate ∉ state.retired ∧ state.guesses = ∅ then
          withRun environment sampler (next hit) (afterTrial environment state coordinate candidate hit)
        else failure) := by
  rw [hitWithRun_query_bind]
  simp only [hitWithImpl, StateT.run_mk, bind_map_left, hitTrialWith, ite_true, bind_assoc]
  apply congrArg (sampler.trialLaw state coordinate candidate >>= ·)
  funext hit
  by_cases hh : hit = true ∧ coordinate ∉ state.retired ∧ state.guesses = ∅
  · rw [if_pos hh, pure_bind, hitWithRun_after environment sampler state.probes _ _ (Nat.lt_succ_self _)]
    rw [if_pos hh]
  · simp only [if_neg hh, failure_bind]
theorem hitWithRun_probe_other {Result : Type} (slot : Nat) (coordinate : Coordinate) (candidate : Value)
    (next : Bool → OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hne : state.probes ≠ slot) :
    hitWithRun environment sampler slot
      (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state =
      (sampler.trialLaw state coordinate candidate >>= fun hit =>
        hitWithRun environment sampler slot (next hit) (afterTrial environment state coordinate candidate hit)) := by
  rw [hitWithRun_query_bind, hitWithImpl_eq_with environment sampler slot state hne]
  simp only [withImpl, StateT.run_mk, bind_map_left]
  rfl
private theorem sum_bind_apply' {Index First Result : Type} (indices : Finset Index) (law : SPMF First)
    (next : Index → First → SPMF Result) (result : Result) :
    (∑ index ∈ indices, (law >>= next index) result) =
      ∑' first, law first * ∑ index ∈ indices, next index first result := by
  simp only [SPMF.bind_apply_eq_tsum]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp only [Finset.mul_sum]
theorem hitWithImpl_no_probe (slot : Nat) (input : (World auxSpec Coordinate Value).Domain) (hn : probeStep input = 0) :
    hitWithImpl environment sampler slot input = withImpl environment sampler input := by
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · rfl
  · cases hn
  · rfl
theorem withImpl_no_probe_guesses (input : (World auxSpec Coordinate Value).Domain) (hn : probeStep input = 0)
    (state : State Coordinate Value Memory)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (withImpl environment sampler input).run state result ≠ 0) : result.2.guesses = state.guesses := by
  rcases withImpl_cases environment sampler state input result hr with ⟨memory, h⟩ | ⟨c, v, hit, hi, -, -⟩ |
    ⟨c, value, -, -, h⟩
  · rw [h]
  · subst hi; cases hn
  · rw [h]; rfl
theorem hitWithRun_sum_no_probe {Result : Type} (slots : Finset Nat) (input : (World auxSpec Coordinate Value).Domain)
    (hn : probeStep input = 0)
    (next : (World auxSpec Coordinate Value).Range input → OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (result : Result × State Coordinate Value Memory) :
    (∑ slot ∈ slots, hitWithRun environment sampler slot
        (liftM ((World auxSpec Coordinate Value).query input) >>= next) state result) =
      ∑' middle, (withImpl environment sampler input).run state middle *
        ∑ slot ∈ slots, hitWithRun environment sampler slot (next middle.1) middle.2 result := by
  simp_rw [hitWithRun_query_bind, hitWithImpl_no_probe environment sampler _ input hn]
  exact sum_bind_apply' slots _ _ result
theorem hitWithRun_sum_probe {Result : Type} (budget : Nat) (coordinate : Coordinate) (candidate : Value)
    (next : Bool → OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (result : Result × State Coordinate Value Memory) (hbudget : state.probes < budget) :
    (∑ slot ∈ Finset.Ico state.probes budget, hitWithRun environment sampler slot
      (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state result) =
      ∑' hit, sampler.trialLaw state coordinate candidate hit *
        ((if hit = true ∧ coordinate ∉ state.retired ∧ state.guesses = ∅ then
            withRun environment sampler (next hit) (afterTrial environment state coordinate candidate hit) result
          else 0) +
          ∑ slot ∈ Finset.Ico (state.probes + 1) budget,
            hitWithRun environment sampler slot (next hit) (afterTrial environment state coordinate candidate hit)
              result) := by
  rw [Finset.sum_eq_sum_Ico_succ_bot hbudget, hitWithRun_probe_at, SPMF.bind_apply_eq_tsum]
  have htail :
      (∑ slot ∈ Finset.Ico (state.probes + 1) budget, hitWithRun environment sampler slot
        (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state result) =
      ∑' hit, sampler.trialLaw state coordinate candidate hit *
        ∑ slot ∈ Finset.Ico (state.probes + 1) budget,
          hitWithRun environment sampler slot (next hit) (afterTrial environment state coordinate candidate hit)
            result := by
    calc
      _ = ∑ slot ∈ Finset.Ico (state.probes + 1) budget,
          (sampler.trialLaw state coordinate candidate >>= fun hit =>
            hitWithRun environment sampler slot (next hit) (afterTrial environment state coordinate candidate hit))
              result := by
        apply Finset.sum_congr rfl
        intro slot hslot
        rw [hitWithRun_probe_other environment sampler slot coordinate candidate next state (by
          have h := (Finset.mem_Ico.mp hslot).1
          omega)]
      _ = _ := sum_bind_apply' _ _ _ result
  rw [htail, ← ENNReal.tsum_add]
  apply tsum_congr
  intro hit
  by_cases hh : hit = true ∧ coordinate ∉ state.retired ∧ state.guesses = ∅
  · simp only [if_pos hh, mul_add]
  · simp only [if_neg hh, SPMF.failure_apply, mul_zero, zero_add]
/-- A run that makes its first guess within the budget splits along the probe slot of that first guess. -/
theorem withRun_first_guess_le_sum {Result : Type} (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (result : Result × State Coordinate Value Memory) (budget : Nat)
    (hbudget : result.2.probes ≤ budget) (h0 : state.guesses = ∅) (hnew : result.2.guesses ≠ ∅) :
    withRun environment sampler computation state result ≤
      ∑ slot ∈ Finset.Ico state.probes budget, hitWithRun environment sampler slot computation state result := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      by_cases he : result = (value, state)
      · subst result
        exact False.elim (hnew h0)
      · simp only [withRun, runWith_pure, SPMF.pure_apply, if_neg he]
        exact bot_le
  | query_bind input next ih =>
      by_cases hn : probeStep input = 0
      · rw [hitWithRun_sum_no_probe environment sampler _ input hn, withRun, runWith_query_bind,
          SPMF.bind_apply_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro middle
        by_cases hm : (withImpl environment sampler input).run state middle = 0
        · simp only [hm, zero_mul, le_refl]
        · have hp := withImpl_probes environment sampler state input middle hm
          rw [hn, Nat.add_zero] at hp
          have hg := withImpl_no_probe_guesses environment sampler input hn state middle hm
          have h := ih middle.1 middle.2 (hg.trans h0)
          rw [hp] at h
          exact mul_le_mul' le_rfl h
      · rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
        · exact False.elim (hn rfl)
        · by_cases hz : withRun environment sampler
              (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state
              result = 0
          · rw [hz]
            exact bot_le
          have hpositive := hz
          rw [withRun, runWith_query_bind] at hpositive
          simp only [withImpl, StateT.run_mk, bind_map_left, RetainedObservation.bind_nonzero] at hpositive
          obtain ⟨hit, _, htail⟩ := hpositive
          have hp := withRun_probes_mono environment sampler (next hit)
            (afterTrial environment state coordinate candidate hit) result htail
          have hroom : state.probes < budget := by
            change state.probes + 1 ≤ result.2.probes at hp
            omega
          rw [hitWithRun_sum_probe environment sampler budget coordinate candidate next state result hroom]
          simp only [withRun, runWith_query_bind, withImpl, StateT.run_mk, bind_map_left, SPMF.bind_apply_eq_tsum]
          apply ENNReal.tsum_le_tsum
          intro hit
          apply mul_le_mul' le_rfl
          by_cases hh : hit = true ∧ coordinate ∉ state.retired ∧ state.guesses = ∅
          · rw [if_pos hh]
            exact le_add_right le_rfl
          · rw [if_neg hh, zero_add]
            have hh' : ¬(hit = true ∧ coordinate ∉ state.retired) := fun h => hh ⟨h.1, h.2, h0⟩
            apply ih hit (afterTrial environment state coordinate candidate hit)
            simpa only [afterTrial, if_neg hh'] using h0
        · exact False.elim (hn rfl)
variable {environment sampler}
/-- First-guess forcing bound: an event that forces a guess within the budget, without `Bad`, is bounded by the
hazard rate times the forced runs' payoffs, summed over the slot of the first guess. -/
theorem withRun_event_le_forced_slot {Result : Type} {size budget : Nat}
    {Inv Bad : State Coordinate Value Memory → Prop} (H : Hazard environment sampler size budget Inv Bad)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hs : Inv state) (hp0 : state.probes = 0) (hg0 : state.guesses = ∅)
    (event : Result × State Coordinate Value Memory → Prop)
    (payoff : Nat → Result × State Coordinate Value Memory → ENNReal)
    (hevent : ∀ result, withRun environment sampler computation state result ≠ 0 → event result →
      result.2.guesses.Nonempty ∧ result.2.probes ≤ budget ∧ ¬Bad result.2 ∧
        ∀ slot < result.2.probes, 1 ≤ payoff slot result) :
    Pr[event | withRun environment sampler computation state] ≤
      ((size - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, ∑' result,
          Pr[= result | forcedWithRun environment sampler slot computation state] * payoff slot result := by
  let cond : Result × State Coordinate Value Memory → Prop := fun result =>
    result.2.guesses.Nonempty ∧ result.2.probes ≤ budget ∧ ¬Bad result.2 ∧
      ∀ slot < result.2.probes, 1 ≤ payoff slot result
  have hstep : (∑' result, Pr[= result | withRun environment sampler computation state] *
      (if cond result then (1 : ENNReal) else 0)) ≤
      ∑ slot ∈ Finset.range budget, ∑' result,
        Pr[= result | hitWithRun environment sampler slot computation state] *
          (if Bad result.2 then 0 else payoff slot result) := by
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hg : cond result
    · rw [if_pos hg, mul_one, SPMF.probOutput_eq_apply]
      have h := withRun_first_guess_le_sum environment sampler computation state result budget hg.2.1 hg0
        hg.1.ne_empty
      rw [hp0, ← Finset.range_eq_Ico] at h
      refine h.trans (Finset.sum_le_sum fun slot hslot => ?_)
      rw [SPMF.probOutput_eq_apply, if_neg hg.2.2.1, hitWithRun_apply]
      split
      · next hlt => exact le_mul_of_one_le_right' (hg.2.2.2 slot hlt)
      · simp only [zero_mul, le_refl]
    · simp only [if_neg hg, mul_zero]
      exact bot_le
  apply (probEvent_le_tsum_probOutput_mul_cost_of_mem_support _ _
    (fun result => if cond result then (1 : ENNReal) else 0) ?_).trans
  · apply hstep.trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro slot hslot
    exact hitWithRun_payoff_le_forced H slot (Finset.mem_range.mp hslot) computation state hs (by omega)
      (payoff slot)
  · intro result hr he
    have h := hevent result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he
    rw [if_pos h]
end SphincsSecurity.Concrete.SecretGuessObservation
end
