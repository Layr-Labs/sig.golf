import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsContactTrace
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryTraceInvariant
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCapTwoEdge
import SigGolfCandidate.T3.Secc.WotsPrefixGameSim

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
