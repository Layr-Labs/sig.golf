import SigGolfCandidate.T3.Secc.PairGuessWorld
import SigGolfCandidate.T3.Secc.WotsTransportTable

section


namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Table
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
theorem splitEquiv_snd (t : ChainGraph.HalfTable) (h : ChainGraph.HalfCoordinate)
    (hh : h ∉ Set.range CanonGraph.secretCoordinate) : (CanonGraph.splitEquiv t).2 ⟨h, hh⟩ = t h := by
  simp [CanonGraph.splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.Set.sumCompl]
  rfl
theorem splitEquiv_symm_other (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (h : ChainGraph.HalfCoordinate)
    (hh : h ∉ Set.range CanonGraph.secretCoordinate) : CanonGraph.splitEquiv.symm (s, o) h = o ⟨h, hh⟩ := by
  have e := splitEquiv_snd (CanonGraph.splitEquiv.symm (s, o)) h hh
  rw [Equiv.apply_symm_apply] at e
  exact e.symm
theorem privateEquiv_symm_apply (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (c : Coordinate) :
    CanonGraph.privateEquiv.symm (s, o) c =
      ChainGraph.joinOutput (CanonGraph.splitEquiv.symm (s, o) (c, 0)) (CanonGraph.splitEquiv.symm (s, o) (c, 1)) :=
  rfl
end Table
def openedValues (fts : FtsCoord → Digest) (output : HashOutput) : List Digest := (openedPositions output).map fts
section Signer
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
noncomputable local instance instDecidableEqCache_pairGuessSigner : DecidableEq T3.Cache := Classical.decEq _
noncomputable def signerForest (output : HashOutput) : List Digest × List Digest × List Digest :=
  evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (Correctness.signForest (output.toNat % 2 ^ 31) (selections output))
noncomputable def signerLayers (request : Request) (output : HashOutput) : Option (List Pieces) :=
  evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (signLayers request.cache (output.toNat % 2 ^ 31) 4
    (evalWithAnswerFn (Omega.answers hU ω (fun _ => 0))
      (forestPk (output.toNat % 2 ^ 31) (signerForest hU ω output).2.2)))
end Signer
end SigGolfCandidate.T3.Security.BPair
end

section



section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Tracking
open SecretGuessObservation (runWith fixedRun fixedImpl afterTrial afterDisclosure)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
theorem disclosed_append_left (A : Answers) (l1 l2 : QueryLog Requests) (f : FtsCoord) (h : Disclosed A l1 f) :
    Disclosed A (l1 ++ l2) f := by
  obtain ⟨entry, he, rest⟩ := h
  exact ⟨entry, List.mem_append_left _ he, rest⟩
theorem disclosed_append_right (A : Answers) (l1 l2 : QueryLog Requests) (f : FtsCoord) (h : Disclosed A l2 f) :
    Disclosed A (l1 ++ l2) f := by
  obtain ⟨entry, he, rest⟩ := h
  exact ⟨entry, List.mem_append_right _ he, rest⟩
structure Tracks (fts : FtsCoord → Digest) (before after : WState) (log : QueryLog Requests)
    (entries : List Wots.Entry) : Prop where
  probes : after.probes ≤ before.probes + entries.length
  guesses : before.guesses ⊆ after.guesses
  retired : before.retired ⊆ after.retired
  origin : ∀ f ∈ after.retired, f ∈ before.retired ∨ f ∈ after.guesses ∨ Disclosed (Omega.answers hU ω fts) log f
  queried : ∀ f answer, (probeInput f (fts f), answer) ∈ entries → f ∈ after.retired
theorem Tracks.refl (fts : FtsCoord → Digest) (state : WState) : Tracks hU ω fts state state [] [] :=
  ⟨by simp, Finset.Subset.refl _, Finset.Subset.refl _, fun _ h => Or.inl h, fun _ _ h => by cases h⟩
theorem Tracks.trans {fts : FtsCoord → Digest} {s1 s2 s3 : WState} {l1 l2 : QueryLog Requests}
    {e1 e2 : List Wots.Entry} (first : Tracks hU ω fts s1 s2 l1 e1) (second : Tracks hU ω fts s2 s3 l2 e2) :
    Tracks hU ω fts s1 s3 (l1 ++ l2) (e1 ++ e2) := by
  refine ⟨?_, first.guesses.trans second.guesses, first.retired.trans second.retired, ?_, ?_⟩
  · have := first.probes
    have := second.probes
    simp only [List.length_append]
    omega
  · intro f hf
    rcases second.origin f hf with h | h | h
    · rcases first.origin f h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (second.guesses h))
      · exact Or.inr (Or.inr (disclosed_append_left _ _ _ _ h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (disclosed_append_right _ _ _ _ h))
  · intro f answer h
    rcases List.mem_append.mp h with h | h
    · exact second.retired (first.queried f answer h)
    · exact second.queried f answer h
end Tracking
end SigGolfCandidate.T3.Security.BPair
end
section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end SigGolfCandidate.T3.Security.BPair
end
section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
open OracleComp.DeferredSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload GameWith.idealGame
theorem probEvent_bind_mono' {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
    (p : β → Prop) (r : γ → Prop) (h : ∀ x, Pr[p | f x] ≤ Pr[r | g x]) :
    Pr[p | mx >>= f] ≤ Pr[r | mx >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
def publicEntries (events : List FirstHit.QueryEvent) : List Wots.Entry :=
  events.filterMap fun e => match e with
    | ⟨_, .inl (.inr input), answer⟩ => some (input, answer)
    | _ => none
theorem publicEntries_pureRecord (T : Answers) {β : Type} (program : M β) (state : LazyPrivate.State) :
    publicEntries (Wots.Ref.pureRecord T program state).events = Wots.entriesOf T (SourceReplay.queried T program) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [Wots.Ref.pureRecord_query_bind, SourceReplay.queried_query_bind]
      rcases input with (n | x) | c
      · exact ih _ _
      · change (x, T (.inl (.inr x))) :: publicEntries _ = (x, T (.inl (.inr x))) :: Wots.entriesOf T _
        rw [ih]
      · exact ih _ _
theorem entriesOf_length_le (T : Answers) (queries : List T3.Spec.Domain) :
    (Wots.entriesOf T queries).length ≤ queries.length := by
  unfold Wots.entriesOf
  exact List.length_filterMap_le _ _
section Law
noncomputable local instance instFintypeCoordinate_pairGuessEager : Fintype Coordinate := coordinateFintype
attribute [local instance] Wots.Ref.instSampleableTypeFullTable_wotsTransportCompletion
  FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
theorem pmf_probEvent_mono {α : Type} (p : PMF α) (A B : α → Prop) (h : ∀ x ∈ p.support, A x → B x) :
    Pr[A | p] ≤ Pr[B | p] := by
  simp only [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ p.support
  · split_ifs with ha hb
    · exact le_rfl
    · exact absurd (h x hx ha) hb
    · exact zero_le
    · exact le_rfl
  · have hz : p x = 0 := by simpa [PMF.mem_support_iff] using hx
    split_ifs <;> simp [PMF.probOutput_eq_apply, hz]
end Law
end SigGolfCandidate.T3.Security.BPair
end
end
