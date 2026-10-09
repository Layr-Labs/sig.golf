import SigGolfCandidate.T3.BPORS

namespace SigGolfCandidate.T3.Security.SeccLaw
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def maxInputLength : Nat := 4096
noncomputable def publicUniverse : Finset HashInput :=
  (Finset.range (maxInputLength + 1)).biUnion fun k =>
    (Finset.univ : Finset (Fin k → UInt8)).image fun bytes => List.ofFn bytes
attribute [irreducible] publicUniverse
theorem mem_publicUniverse (input : HashInput) (h : input.length ≤ maxInputLength) : input ∈ publicUniverse := by
  rw [publicUniverse, Finset.mem_biUnion]
  refine ⟨input.length, Finset.mem_range.mpr (by omega), ?_⟩
  rw [Finset.mem_image]
  exact ⟨input.get, Finset.mem_univ _, List.ofFn_get input⟩
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_seccLaw : Fintype Coordinate := coordinateFintype
abbrev PublicTable := publicUniverse → HashOutput
abbrev CompletionTables := FullGame.FullTable × PublicTable
noncomputable instance instFintypeCompletionTables : Fintype CompletionTables := by
  unfold CompletionTables PublicTable FullGame.FullTable
  infer_instance
instance instNonemptyCompletionTables : Nonempty CompletionTables := ⟨(fun _ => 0, fun _ => 0)⟩
noncomputable def publicFill (table : PublicTable) (input : HashInput) : HashOutput :=
  if h : input ∈ publicUniverse then table ⟨input, h⟩ else 0
noncomputable def completeWith (state : LazyPrivate.State) (tables : CompletionTables) : Correctness.Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => (state.2 input).getD (publicFill tables.2 input)
  | .inr coordinate => (state.1 coordinate).getD (tables.1 coordinate)
theorem completeWith_agrees (state : LazyPrivate.State) (tables : CompletionTables)
    (input : T3.Spec.Domain) (answer : T3.Spec.Range input)
    (h : SourceReplay.known state input = some answer) : completeWith state tables input = answer := by
  cases input with
  | inl input =>
      cases input with
      | inl n => cases h
      | inr input =>
          change state.2 input = some answer at h
          simp only [completeWith, h, Option.getD_some]
  | inr coordinate =>
      change state.1 coordinate = some answer at h
      simp only [completeWith, h, Option.getD_some]
noncomputable def classCharge (cls : T3.Spec.Domain → Prop) : Nat → List FirstHit.QueryEvent → Nat
  | _, [] => 0
  | budget, event :: rest =>
      if FullGame.queryCharge event.input ≤ budget then
        (if cls event.input then FullGame.queryCharge event.input else 0) +
          classCharge cls (budget - FullGame.queryCharge event.input) rest
      else 0
theorem classCharge_or (P Q : T3.Spec.Domain → Prop) (hdisj : ∀ input, ¬(P input ∧ Q input))
    (budget : Nat) (events : List FirstHit.QueryEvent) :
    classCharge (fun input => P input ∨ Q input) budget events =
      classCharge P budget events + classCharge Q budget events := by
  induction events generalizing budget with
  | nil => simp [classCharge]
  | cons event rest ih =>
      simp only [classCharge]
      split_ifs with hc hpq hp hq hq' <;> first
        | omega
        | (rw [ih]; omega)
        | (exfalso; exact hdisj _ ⟨hp, hq⟩)
        | (simp_all)
theorem classCharge_le (cls : T3.Spec.Domain → Prop) (budget : Nat) (events : List FirstHit.QueryEvent) :
    classCharge cls budget events ≤ budget := by
  induction events generalizing budget with
  | nil => simp [classCharge]
  | cons event rest ih =>
      simp only [classCharge]
      split_ifs with hc hcls
      · have := ih (budget - FullGame.queryCharge event.input); omega
      · have := ih (budget - FullGame.queryCharge event.input); omega
      · omega
abbrev SampleClass := PaddedGame.TraceResult × Correctness.Answers → T3.Spec.Domain → Prop
end SigGolfCandidate.T3.Security.SeccLaw
