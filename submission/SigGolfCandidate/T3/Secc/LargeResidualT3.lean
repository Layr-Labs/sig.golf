import SigGolfCandidate.T3.Secc.LargePotential
import SigGolfCandidate.T3.Secc.CanonEncoding

section
namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion RetainedObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
abbrev Digest := SphincsSecurity.Digest
abbrev HashOutput := SphincsSecurity.HashOutput
def low (answer : HashOutput) : Digest := SphincsSecurity.truncateHash answer
inductive Hit (Coord : Type) where
  | label (parent : Coord)
  | target (value : Digest)
structure Probe (Coord : Type) where
  guess : Option (Coord × Digest)
  hit : Hit Coord
section Defs
variable {Coord : Type}
def Hit.miss : Hit Coord → (Coord → Digest) → Digest → Prop
  | .label parent, labels, value => labels parent ≠ value
  | .target t, _, value => t ≠ value
def Hit.labelMiss : Hit Coord → (Coord → Digest) → Digest → Prop
  | .label parent, labels, value => labels parent ≠ value
  | .target _t, _, _ => True
def Hit.answerOk : Hit Coord → Digest → Prop
  | .label _p, _ => True
  | .target t, value => t ≠ value
theorem Hit.miss_iff (hit : Hit Coord) (labels : Coord → Digest) (value : Digest) :
    hit.miss labels value ↔ hit.labelMiss labels value ∧ hit.answerOk value := by
  cases hit <;> simp [Hit.miss, Hit.labelMiss, Hit.answerOk]
def Probe.guessMiss (probe : Probe Coord) (labels : Coord → Digest) : Prop :=
  ∀ g ∈ probe.guess, labels g.1 ≠ g.2
def Probe.keep (probe : Probe Coord) (labels : Coord → Digest) (answer : HashOutput) : Prop :=
  probe.guessMiss labels ∧ probe.hit.miss labels (low answer)
variable [DecidableEq Coord]
def Probe.guessRestrict (probe : Probe Coord) (allowed : Coord → Finset Digest) : Coord → Finset Digest :=
  match probe.guess with
  | none => allowed
  | some g => eraseTableValue allowed g.1 g.2
def Hit.restrict : Hit Coord → (Coord → Finset Digest) → Digest → Coord → Finset Digest
  | .label parent, allowed, value => eraseTableValue allowed parent value
  | .target _, allowed, _ => allowed
def Probe.restrict (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput) :
    Coord → Finset Digest :=
  probe.hit.restrict (probe.guessRestrict allowed) (low answer)
def Probe.Admissible (candidates : Coord → Finset Digest) (hit : Hit Coord) (g : Coord × Digest) : Prop :=
  2 ≤ (candidates g.1).card ∧ ∀ parent, hit = Hit.label parent → g.1 ≠ parent
noncomputable def Probe.effective (candidates : Coord → Finset Digest) (probe : Probe Coord) : Probe Coord :=
  ⟨probe.guess.filter (fun g => decide (Probe.Admissible candidates probe.hit g)), probe.hit⟩
end Defs
section Restrict
variable {Coord : Type} [DecidableEq Coord]
theorem mem_eraseTableValue (allowed : Coord → Finset Digest) (c0 : Coord) (v : Digest)
    (labels : Coord → Digest) (c : Coord) :
    labels c ∈ eraseTableValue allowed c0 v c ↔ labels c ∈ allowed c ∧ (c = c0 → labels c ≠ v) := by
  by_cases h : c = c0
  · subst h
    simp only [eraseTableValue, Function.update_self, Finset.mem_erase, true_implies]
    exact and_comm
  · simp only [eraseTableValue, Function.update_of_ne h, h, false_implies, and_true]
theorem eraseTableValue_subset (allowed : Coord → Finset Digest) (c0 : Coord) (v : Digest) (c : Coord) :
    eraseTableValue allowed c0 v c ⊆ allowed c := by
  by_cases h : c = c0
  · subst h
    simp only [eraseTableValue, Function.update_self]
    exact Finset.erase_subset _ _
  · simp only [eraseTableValue, Function.update_of_ne h, subset_refl]
theorem guessRestrict_subset (probe : Probe Coord) (allowed : Coord → Finset Digest) (c : Coord) :
    probe.guessRestrict allowed c ⊆ allowed c := by
  unfold Probe.guessRestrict
  cases probe.guess with
  | none => exact subset_refl _
  | some g => exact eraseTableValue_subset _ _ _ _
theorem Hit.restrict_subset (hit : Hit Coord) (allowed : Coord → Finset Digest) (value : Digest) (c : Coord) :
    hit.restrict allowed value c ⊆ allowed c := by
  cases hit with
  | label parent => exact eraseTableValue_subset _ _ _ _
  | target t => exact subset_refl _
theorem restrict_subset (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput) (c : Coord) :
    probe.restrict allowed answer c ⊆ allowed c :=
  (Hit.restrict_subset _ _ _ c).trans (guessRestrict_subset probe allowed c)
theorem mem_guessRestrict (probe : Probe Coord) (allowed : Coord → Finset Digest) (labels : Coord → Digest) :
    (∀ c, labels c ∈ probe.guessRestrict allowed c) ↔ (∀ c, labels c ∈ allowed c) ∧ probe.guessMiss labels := by
  unfold Probe.guessRestrict Probe.guessMiss
  cases hg : probe.guess with
  | none => simp
  | some g =>
      simp only [mem_eraseTableValue, Option.mem_def, Option.some.injEq, forall_eq']
      constructor
      · intro h
        exact ⟨fun c => (h c).1, (h g.1).2 rfl⟩
      · rintro ⟨h, hg'⟩ c
        exact ⟨h c, fun hc => hc ▸ hg'⟩
theorem mem_hitRestrict (hit : Hit Coord) (allowed : Coord → Finset Digest) (value : Digest)
    (labels : Coord → Digest) :
    (∀ c, labels c ∈ hit.restrict allowed value c) ↔ (∀ c, labels c ∈ allowed c) ∧ hit.labelMiss labels value := by
  cases hit with
  | label parent =>
      simp only [Hit.restrict, Hit.labelMiss, mem_eraseTableValue]
      constructor
      · intro h
        exact ⟨fun c => (h c).1, (h parent).2 rfl⟩
      · rintro ⟨h, hp⟩ c
        exact ⟨h c, fun hc => hc ▸ hp⟩
  | target t => simp [Hit.restrict, Hit.labelMiss]
theorem mem_restrict (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput)
    (labels : Coord → Digest) :
    (∀ c, labels c ∈ probe.restrict allowed answer c) ↔
      (∀ c, labels c ∈ allowed c) ∧ probe.guessMiss labels ∧ probe.hit.labelMiss labels (low answer) := by
  unfold Probe.restrict
  rw [mem_hitRestrict, mem_guessRestrict, and_assoc]
end Restrict
section Posterior
variable {Coord : Type} [Fintype Coord] [DecidableEq Coord]
noncomputable def response (labels : Coord → Digest) (probe : Probe Coord) : SPMF HashOutput := do
  let answer ← (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)
  if probe.keep labels answer then pure answer else failure
noncomputable def lazyResponse (allowed : Coord → Finset Digest) (probe : Probe Coord) : SPMF HashOutput :=
  complete allowed >>= fun labels => response labels probe
omit [Fintype Coord] [DecidableEq Coord] in
theorem response_apply (labels : Coord → Digest) (probe : Probe Coord) (answer : HashOutput) :
    response labels probe answer =
      if probe.keep labels answer then PMF.uniformOfFintype HashOutput answer else 0 := by
  rw [response, SPMF.bind_apply_eq_tsum]
  rw [tsum_eq_single answer]
  · by_cases h : probe.keep labels answer <;> simp only [h, if_true, if_false, SPMF.liftM_apply,
      SPMF.pure_apply_self, SPMF.failure_apply, mul_one, mul_zero]
  · intro other hother
    by_cases h : probe.keep labels other <;> simp only [h, if_true, if_false, SPMF.pure_apply,
      if_neg (Ne.symm hother), SPMF.failure_apply, mul_zero]
theorem Probe.mass (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput)
    (labels : Coord → Digest) :
    (if probe.keep labels answer then complete allowed labels else 0) =
      if probe.hit.answerOk (low answer) then
        restrictionWeight allowed (probe.restrict allowed answer) * complete (probe.restrict allowed answer) labels
      else 0 := by
  by_cases ha : probe.hit.answerOk (low answer)
  · rw [if_pos ha]
    have h := restrict_guard allowed (probe.restrict allowed answer) (restrict_subset probe allowed answer)
      (fun labels => probe.guessMiss labels ∧ probe.hit.labelMiss labels (low answer))
      (fun labels => mem_restrict probe allowed answer labels) labels
    have hkeep : probe.keep labels answer ↔ probe.guessMiss labels ∧ probe.hit.labelMiss labels (low answer) := by
      simp only [Probe.keep, Hit.miss_iff, ha, and_true]
    by_cases hc : probe.guessMiss labels ∧ probe.hit.labelMiss labels (low answer)
    · rw [if_pos (hkeep.mpr hc)]
      rw [if_pos hc] at h
      exact h
    · rw [if_neg (fun h' => hc (hkeep.mp h'))]
      rw [if_neg hc] at h
      exact h
  · have hk : ¬probe.keep labels answer := fun h => ha ((Hit.miss_iff _ _ _).mp h.2).2
    simp only [hk, ha, if_false]
end Posterior
section Hazard
variable {Coord : Type} [Fintype Coord] [DecidableEq Coord]
noncomputable def law (allowed : Coord → Finset Digest) (ha : ∀ c, (allowed c).Nonempty) :
    PMF ((Coord → Digest) × HashOutput) :=
  (uniformTable allowed ha).bind fun labels =>
    (PMF.uniformOfFintype HashOutput).map fun answer => (labels, answer)
omit [Fintype Coord] [DecidableEq Coord] in
theorem response_failure (labels : Coord → Digest) (probe : Probe Coord) :
    (response labels probe).toPMF none =
      Pr[fun answer => ¬probe.keep labels answer | PMF.uniformOfFintype HashOutput] := by
  rw [response, toPMF_bind_lift, PMF.bind_apply, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true, not_true_eq_false, if_false, SPMF.toPMF_pure, PMF.pure_apply,
      reduceCtorEq, mul_zero]
  · simp only [h, if_false, not_false_eq_true, if_true, SPMF.toPMF_failure, PMF.pure_apply,
      mul_one, PMF.probOutput_eq_apply]
omit [Fintype Coord] [DecidableEq Coord] in
theorem hit_miss_prob (hit : Hit Coord) (labels : Coord → Digest) :
    Pr[fun answer => hit.miss labels (low answer) | PMF.uniformOfFintype HashOutput] =
      1 - (Fintype.card Digest : ENNReal)⁻¹ := by
  cases hit with
  | label parent =>
      have he : (fun answer => Hit.miss (.label parent) labels (low answer)) =
          (fun answer => SphincsSecurity.truncateHash answer ≠ labels parent) := by
        funext answer
        simp only [Hit.miss, low, ne_eq, eq_comm]
      rw [he]
      exact HiddenLabelProbe.prob_truncate_ne (labels parent)
  | target t =>
      have he : (fun answer => Hit.miss (.target t) labels (low answer)) =
          (fun answer => SphincsSecurity.truncateHash answer ≠ t) := by
        funext answer
        simp only [Hit.miss, low, ne_eq, eq_comm]
      rw [he]
      exact HiddenLabelProbe.prob_truncate_ne t
end Hazard
end SigGolfCandidate.T3.Security.LargeResidual
end
section
namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
inductive Charge where
  | none
  | call
  | mass
  deriving DecidableEq
inductive Request (Coord Cell : Type) where
  | read (row : Cell) (charge : Charge)
  | probe (row : Cell) (test : Probe Coord)
  | disclose (coord : Coord) (charge : Charge)
  | tick (charge : Charge)
abbrev ResidualSpec (Coord Cell : Type) : OracleSpec (Request Coord Cell)
  | .read _ _ => HashOutput
  | .probe _ _ => HashOutput
  | .disclose _ _ => Digest
  | .tick _ => Unit
abbrev World {AuxIndex : Type} (auxSpec : OracleSpec AuxIndex) (Coord Cell : Type) :=
  auxSpec + ResidualSpec Coord Cell
structure Counters where
  calls : Nat
  probes : Nat
  mass : Nat
def Counters.charge (q : Nat) (counters : Counters) : Charge → Counters
  | .none => counters
  | .call => ⟨counters.calls + 1, counters.probes, counters.mass⟩
  | .mass => ⟨counters.calls + 1, counters.probes, counters.mass + (if counters.calls + 1 ≤ q then 1 else 0)⟩
def Counters.probe (counters : Counters) : Counters :=
  ⟨counters.calls + 1, counters.probes + 1, counters.mass⟩
structure State (Coord Cell : Type) where
  candidates : Coord → Finset Digest
  rows : ResidualTableCompletion.Cache Cell
  counters : Counters
section World
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
def readState (q : Nat) (state : State Coord Cell) (row : Cell) (answer : HashOutput) (charge : Charge) :
    State Coord Cell :=
  ⟨state.candidates, Function.update state.rows row (some answer), state.counters.charge q charge⟩
def probeState (state : State Coord Cell) (row : Cell) (test : Probe Coord) (answer : HashOutput) :
    State Coord Cell :=
  ⟨test.restrict state.candidates answer, Function.update state.rows row (some answer), state.counters.probe⟩
def stoppedState (state : State Coord Cell) : State Coord Cell :=
  ⟨state.candidates, state.rows, state.counters.probe⟩
def disclosedState (q : Nat) (state : State Coord Cell) (coord : Coord) (value : Digest) (charge : Charge) :
    State Coord Cell :=
  ⟨discloseTableValue state.candidates coord value, state.rows, state.counters.charge q charge⟩
def tickState (q : Nat) (state : State Coord Cell) (charge : Charge) : State Coord Cell :=
  ⟨state.candidates, state.rows, state.counters.charge q charge⟩
noncomputable def observedImpl (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (labels : Coord → Digest) (table : Cell → HashOutput) :
    QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (aux input) : SPMF _) >>= fun answer => pure (some answer, state)
  | .inr (.read row charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (table row), readState q state row (table row) charge)
  | .inr (.probe row test) => OptionT.mk <| StateT.mk fun state =>
      match state.rows row with
      | some answer => pure (some answer, readState q state row answer .call)
      | none => if (test.effective state.candidates).keep labels (table row) then
          pure (some (table row), probeState state row (test.effective state.candidates) (table row))
        else pure (none, stoppedState state)
  | .inr (.disclose coord charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (labels coord), disclosedState q state coord (labels coord) charge)
  | .inr (.tick charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (), tickState q state charge)
noncomputable def lazyImpl (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat) :
    QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (aux input) : SPMF _) >>= fun answer => pure (some answer, state)
  | .inr (.read row charge) => OptionT.mk <| StateT.mk fun state =>
      reply state.rows row >>= fun answer => pure (some answer, readState q state row answer charge)
  | .inr (.probe row test) => OptionT.mk <| StateT.mk fun state =>
      match state.rows row with
      | some answer => pure (some answer, readState q state row answer .call)
      | none => observe (lazyResponse state.candidates (test.effective state.candidates))
          (pure (none, stoppedState state))
          (fun answer => pure (some answer, probeState state row (test.effective state.candidates) answer))
  | .inr (.disclose coord charge) => OptionT.mk <| StateT.mk fun state =>
      cell (state.candidates coord) >>= fun value => pure (some value, disclosedState q state coord value charge)
  | .inr (.tick charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (), tickState q state charge)
noncomputable def runWith {Result : Type}
    (implementation : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :
    SPMF (Option Result × State Coord Cell) :=
  (OptionT.run (simulateQ implementation computation)).run state
omit [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell] in
theorem runWith_pure {Result : Type}
    (implementation : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (value : Result) (state : State Coord Cell) : runWith implementation (pure value) state = pure (some value, state) := by
  simp only [runWith, simulateQ_pure, OptionT.run_pure, StateT.run_pure]
omit [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell] in
theorem runWith_query_bind {Result : Type}
    (implementation : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (input : (World auxSpec Coord Cell).Domain)
    (next : (World auxSpec Coord Cell).Range input → OracleComp (World auxSpec Coord Cell) Result)
    (state : State Coord Cell) :
    runWith implementation (liftM ((World auxSpec Coord Cell).query input) >>= next) state =
      ((implementation input).run.run state >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun answer => runWith implementation (next answer) result.2)) := by
  simp only [runWith, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (fun continuation => (implementation input).run.run state >>= continuation)
  funext result
  rcases result with ⟨answer, state⟩
  cases answer <;> rfl
noncomputable def observedRun {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (labels : Coord → Digest) (table : Cell → HashOutput)
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :=
  runWith (observedImpl aux q labels table) computation state
noncomputable def lazyRun {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :=
  runWith (lazyImpl aux q) computation state
def retain {Result : Type} (labels : Coord → Digest) (table : Cell → HashOutput)
    (result : Option Result × State Coord Cell) :
    Option ((Coord → Digest) × (Cell → HashOutput) × Result) × State Coord Cell :=
  (result.1.map (fun value => (labels, table, value)), result.2)
end World
end SigGolfCandidate.T3.Security.LargeResidual
end
section
namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open LargePotential (Step Charges StepBound FreeStep MassStep ProbeStep hazard)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
section Bound
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
def charges : Charges (State Coord Cell) :=
  ⟨fun state => state.counters.calls, fun state => state.counters.probes, fun state => state.counters.mass⟩
def Inv (state : State Coord Cell) : Prop :=
  ∀ c, (state.candidates c).card = 1 ∨ 2 ^ 128 - state.counters.probes ≤ (state.candidates c).card
def initial : State Coord Cell := ⟨fun _ => Finset.univ, fun _ => none, ⟨0, 0, 0⟩⟩
theorem stop_zero_of_shape {X R : Type} (p : SPMF X) (g : X → R) (f : X → State Coord Cell) :
    Pr[fun result : Option R × State Coord Cell => result.1 = none | p >>= fun a => pure (some (g a), f a)] = 0 := by
  apply probEvent_eq_zero
  intro result hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨a, _, hr⟩ := hresult
  rw [mem_support_pure_iff] at hr
  subst hr
  simp
theorem support_of_shape {X R : Type} (p : SPMF X) (g : X → R) (f : X → State Coord Cell)
    (result : Option R × State Coord Cell) (hresult : result ∈ support (p >>= fun a => pure (some (g a), f a))) :
    ∃ a, result = (some (g a), f a) := by
  rw [mem_support_bind_iff] at hresult
  obtain ⟨a, _, hr⟩ := hresult
  rw [mem_support_pure_iff] at hr
  exact ⟨a, hr⟩
theorem stepBound_of_charge (q : Nat) {X : Type} (step : Step SPMF (World auxSpec Coord Cell) (State Coord Cell))
    (input : (World auxSpec Coord Cell).Domain) (state : State Coord Cell) (charge : Charge)
    (p : SPMF X) (g : X → (World auxSpec Coord Cell).Range input) (f : X → State Coord Cell)
    (hstep : step input state = p >>= fun a => pure (some (g a), f a))
    (hcounters : ∀ a, (f a).counters = state.counters.charge q charge) :
    StepBound step charges (2 ^ 128) q input state := by
  have hstop : Pr[fun result => result.1 = none | step input state] = 0 := by
    rw [hstep]; exact stop_zero_of_shape p g f
  cases charge with
  | none =>
      left
      refine ⟨fun result hresult => ?_, hstop⟩
      rw [hstep] at hresult
      obtain ⟨a, rfl⟩ := support_of_shape p g f result hresult
      simp only [charges, hcounters a, Counters.charge, le_refl, and_self]
  | call =>
      left
      refine ⟨fun result hresult => ?_, hstop⟩
      rw [hstep] at hresult
      obtain ⟨a, rfl⟩ := support_of_shape p g f result hresult
      simp only [charges, hcounters a, Counters.charge]
      omega
  | mass =>
      right; left
      refine ⟨fun result hresult => ?_, hstop⟩
      rw [hstep] at hresult
      obtain ⟨a, rfl⟩ := support_of_shape p g f result hresult
      simp only [charges, hcounters a, Counters.charge]
      omega
theorem observe_stop {S : Type} (response : SPMF HashOutput) (stopped : S) (continued : HashOutput → S) :
    Pr[fun result : Option HashOutput × S => result.1 = none |
        observe response (pure (none, stopped)) (fun answer => pure (some answer, continued answer))] =
      response.toPMF none := by
  rw [observe, probEvent_bind_eq_tsum, tsum_option _ ENNReal.summable]
  simp
theorem observe_support {S : Type} (response : SPMF HashOutput) (stopped : S) (continued : HashOutput → S)
    (result : Option HashOutput × S)
    (hresult : result ∈ support (observe response (pure (none, stopped))
      (fun answer => pure (some answer, continued answer)))) :
    result = (none, stopped) ∨ ∃ answer, response answer ≠ 0 ∧ result = (some answer, continued answer) := by
  rw [observe, mem_support_bind_iff] at hresult
  obtain ⟨o, ho, hr⟩ := hresult
  cases o with
  | none =>
      rw [mem_support_pure_iff] at hr
      exact Or.inl hr
  | some answer =>
      rw [mem_support_pure_iff] at hr
      refine Or.inr ⟨answer, ?_, hr⟩
      rw [SPMF.apply_eq_toPMF_some response answer]
      rw [mem_support_iff] at ho
      simpa using ho
@[simp] theorem Counters.charge_probes (q : Nat) (counters : Counters) (charge : Charge) :
    (counters.charge q charge).probes = counters.probes := by
  cases charge <;> rfl
omit [Fintype Coord] in
theorem card_erase_ge (allowed : Coord → Finset Digest) (c0 : Coord) (v : Digest) (c : Coord) :
    (allowed c).card - 1 ≤ (eraseTableValue allowed c0 v c).card := by
  by_cases h : c = c0
  · subst h
    simpa only [eraseTableValue, Function.update_self] using
      (Finset.pred_card_le_card_erase (s := allowed c) (a := v))
  · simp only [eraseTableValue, Function.update_of_ne h]
    omega
omit [Fintype Coord] in
theorem card_erase_of_ne (allowed : Coord → Finset Digest) (c0 : Coord) (v : Digest) (c : Coord) (h : c ≠ c0) :
    (eraseTableValue allowed c0 v c).card = (allowed c).card := by
  simp only [eraseTableValue, Function.update_of_ne h]
omit [Fintype Coord] in
theorem card_restrict_ge (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput)
    (hadm : ∀ g ∈ probe.guess, ∀ parent, probe.hit = Hit.label parent → g.1 ≠ parent) (c : Coord) :
    (allowed c).card - 1 ≤ (probe.restrict allowed answer c).card := by
  unfold Probe.restrict
  cases hhit : probe.hit with
  | target t =>
      simp only [Hit.restrict]
      unfold Probe.guessRestrict
      cases hg : probe.guess with
      | none => simp
      | some g => exact card_erase_ge _ _ _ _
  | label parent =>
      simp only [Hit.restrict]
      unfold Probe.guessRestrict
      cases hg : probe.guess with
      | none => exact card_erase_ge _ _ _ _
      | some g =>
          have hne : g.1 ≠ parent := hadm g (by rw [hg]; rfl) parent hhit
          by_cases hc : c = parent
          · subst hc
            have h1 := card_erase_ge (eraseTableValue allowed g.1 g.2) c (low answer) c
            rw [card_erase_of_ne allowed g.1 g.2 c (Ne.symm hne)] at h1
            exact h1
          · rw [card_erase_of_ne _ parent (low answer) c hc]
            exact card_erase_ge _ _ _ _
omit [Fintype Coord] in
theorem restrict_subset_card (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput) (c : Coord) :
    (probe.restrict allowed answer c).card ≤ (allowed c).card :=
  Finset.card_le_card (restrict_subset probe allowed answer c)
end Bound
end SigGolfCandidate.T3.Security.LargeResidual
end
section
namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeResidualT3 : DecidableEq T3.Cache := Classical.decEq _
abbrev Coord := CanonGraph.Node ⊕ CanonGraph.SecretIndex
def chainChild (p : ChainGraph.Point) : Coord :=
  if p.2.val = 0 then .inr (.inl p.1) else .inl (.chain (ChainGraph.predecessor p))
def treeChild (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Option Coord :=
  if level = 0 then (if h : c < 4096 then some (.inl (.leaf ⟨lay, tree, ⟨c, h⟩⟩)) else none)
  else (treeNodeAt lay tree (level - 1) c).map fun n => .inl (.node n)
def ftsChild (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) : Option Coord :=
  if level = 0 then (if h : c < 2048 then some (.inl (.ftsLeaf ⟨index, coord, ⟨c, h⟩⟩)) else none)
  else (ftsNodeAt index coord (level - 1) c).map fun n => .inl (.ftsNode n)
def endPoint (L : LeafPos) (i : Nat) : ChainGraph.Point :=
  (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(maxDigit L.lay i - 1) % 7, Nat.mod_lt _ (by decide)⟩)
def listBlock (i : Nat) : Nat := if i = 0 then 0 else i + 1
def childSlots : CanonGraph.Node → List (Coord × Nat)
  | .chain p => [(chainChild p, 3)]
  | .leaf L => (List.range (chainCount L.lay)).map fun i => (.inl (.chain (endPoint L i)), listBlock i)
  | .node n => ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList
  | .ftsLeaf f => [(.inr (.inr f), 2)]
  | .ftsNode n => ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList
  | .forest index => (List.range 7).map fun c => (.inl (.ftsNode (ftsRootNode index (fin7 c))), listBlock c)
def slotValue (input : HashInput) (block : Nat) : Digest := readDigest ((input.drop (16 * block)).take 16)
noncomputable def honestValue (A : Answers) : Coord → Digest
  | .inl N => (A (.inl (.inr (Extract.honestInput A N.toPos)))).extractLsb' 0 128
  | .inr s => secretsOf A s
inductive Known (D : Coord → Prop) : Coord → Prop
  | base {c : Coord} : D c → Known D c
  | node {N : CanonGraph.Node} : (∀ cs ∈ childSlots N, Known D cs.1) → Known D (.inl N)
noncomputable def firstUnknown (K : Coord → Prop) (N : CanonGraph.Node) : Option (Coord × Nat) :=
  (childSlots N).find? fun cs => decide (¬K cs.1)
def keygenDisclosed : List Coord :=
  (List.range' 0 13).flatMap fun level =>
    (List.range (2 ^ (12 - level))).filterMap fun node => treeChild 0 0 level node
def chainItem (L : LeafPos) (i d : Nat) : Coord :=
  if d = 0 then .inr (.inl ⟨L.lay, L.tree, L.leaf, fin58 i⟩)
  else .inl (.chain (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(d - 1) % 7, Nat.mod_lt _ (by decide)⟩))
def ftsOpened (index : Fin (2^31)) (coord : Nat) (sel : Selection) : List Coord :=
  (sel.leaves.map (fun s => sel.bucket * 128 + s)).filterMap fun leaf =>
    if h : leaf < 2048 then some (.inr (.inr ⟨index, fin7 coord, ⟨leaf, h⟩⟩)) else none
def ftsProof (index : Fin (2^31)) (coord : Nat) (sel : Selection) : List Coord :=
  ((frontier (sel.leaves.map (fun s => sel.bucket * 128 + s)) 7 sel.bucket).filterMap fun p =>
      ftsChild index (fin7 coord) p.1 p.2) ++
    ((List.range 4).filterMap fun j => ftsChild index (fin7 coord) (7 + j) (sel.bucket / 2 ^ j ^^^ 1))
def ftsItems (index : Fin (2^31)) (chosen : List Selection) : List Coord :=
  (List.range 7).flatMap fun coord =>
    ftsOpened index coord (chosen.getD coord ⟨0, []⟩) ++ ftsProof index coord (chosen.getD coord ⟨0, []⟩)
def routeAddr (index : Nat) (lay : Layer) : Wots.LeafAddr := ⟨lay, (route index lay).2, (route index lay).1⟩
def layerChains (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) (lay : Layer) : List Coord :=
  if h : (route index.val lay).2 < 2 ^ 31 ∧ (route index.val lay).1 < 4096 then
    (List.range (chainCount lay)).map fun i =>
      chainItem ⟨lay, ⟨(route index.val lay).2, h.1⟩, ⟨(route index.val lay).1, h.2⟩⟩ i
        ((digitsOf (routeAddr index.val lay)).getD i 0)
  else []
def layerPath (index : Fin (2^31)) (lay : Layer) : List Coord :=
  if h : (route index.val lay).2 < 2 ^ 31 then
    (List.range (height lay)).filterMap fun j =>
      treeChild lay ⟨(route index.val lay).2, h⟩ j ((route index.val lay).1 / 2 ^ j ^^^ 1)
  else []
def layerItems (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) : List Coord :=
  (List.finRange 4).flatMap fun lay => layerChains digitsOf index lay ++ layerPath index lay
def digestIndex (N : HashOutput) : Fin (2^31) := ⟨N.toNat % 2 ^ 31, Nat.mod_lt _ (by positivity)⟩
def signItemsWith (digitsOf : Wots.LeafAddr → List Nat) (N : HashOutput) : List Coord :=
  ftsItems (digestIndex N) (selections N) ++ layerItems digitsOf (digestIndex N)
noncomputable def signItems (A : Answers) (N : HashOutput) : List Coord :=
  signItemsWith (Wots.referenceDigits A) N
def RouteOk (A : Answers) (index : Nat) : Prop :=
  ∀ lay : Layer, lay ≠ 0 → (Wots.referenceSearch A (routeAddr index lay)).isSome
noncomputable def signDigest (A : Answers) (message : Message) : Option (BitVec 32 × HashOutput) :=
  evalWithAnswerFn A (digestSearch (evalWithAnswerFn A (privateNonce message)) message 0 attemptLimit)
noncomputable def signDisclosed (A : Answers) (published : T3.Cache) (request : SigGolfCandidate.T3.Security.Request) :
    List Coord :=
  if request.cache = published then
    match signDigest A request.message with
    | some (_, N) => if RouteOk A (N.toNat % 2 ^ 31) then signItems A N else []
    | none => []
  else []
def msgCoord (L : EncLeaf) : Coord :=
  if h : L.1.lay.val < 3 then .inl (.node (rootNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L)))
  else .inl (.forest (childIndex L))
def StructuralContact (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ N : CanonGraph.Node, Extract.posOf input = some N.toPos ∧
    ((∃ cs, firstUnknown K N = some cs ∧ slotValue input cs.2 = honestValue A cs.1) ∨
      (input ≠ Extract.honestInput A N.toPos ∧ answer.extractLsb' 0 128 = honestValue A (.inl N)))
def EncodingContact (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ (L : EncLeaf) (m : Digest) (ctr : BitVec 32), input = Wots.encodingRow L.toWots m ctr ∧
    ((¬K (msgCoord L) ∧ m = honestValue A (msgCoord L)) ∨
      (Wots.referenceInput A L.toWots ≠ some input ∧
        decode L.1.lay (answer.extractLsb' 0 128) = some (Wots.referenceDigits A L.toWots)))
def ContactTest (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  StructuralContact A K input answer ∨ EncodingContact A K input answer
def IsDigestRow (input : HashInput) : Prop :=
  ∃ (rho : Digest) (message : Message) (counter : BitVec 32), input = pad64 (digestInput rho message counter)
end SigGolfCandidate.T3.Security.LargeResidual
end
