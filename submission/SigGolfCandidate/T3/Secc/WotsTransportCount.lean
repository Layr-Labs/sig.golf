import SigGolfCandidate.T3.Secc.WotsTransport
import SigGolfCandidate.T3.Secc.WotsReferenceInputs

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload GameWith.idealGame
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
