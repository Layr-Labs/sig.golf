import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsLeafRef
set_option Elab.async false

/-! # Prefix views of lower chains (campaign X1 stage B, step B3)

The prefix-view consumers (`ContactAt`, `TwoEdgeAt`, `prefixCount`) for lower source chains: the reference
experiment and the `realRun` mixture agree up to `errC a` (probabilities, `view_prob_le` / `view_prob_ge`), and the
expected prefix count of the mixture exceeds the reference one by at most `q · errC a` (`view_count_le`). -/

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
noncomputable local instance instFintypeCoordinate_wotsLeafView : Fintype Coordinate := coordinateFintype
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun)
open SphincsSecurity.QueryCap (recorded counted calls)
variable {adversary : AdversaryP}

/-- The prefix view of a run at depth `d` (`runView` is the case `d = restDepth a R`). -/
noncomputable def runViewD (a : ChainAddr) (d : Nat) (r : Digest × (SeedResult × TObs d)) : PrefixView :=
  ⟨d, r.1, fun step value => if h : step < d then r.2.2 ⟨step, h⟩ value else none,
    calls (PrefixGame.PrefixQuery a d) r.2.1.2⟩

theorem runView_eq (a : ChainAddr) (R : RefTables adversary) (r : Digest × (SeedResult × TObs (restDepth a R))) :
    runView a R r = runViewD a (restDepth a R) r := rfl

theorem mixLaw_seed (q : ℕ) (a : ChainAddr) (R : RefTables adversary) :
    mixLaw a (restDepth a R) R (GDseed adversary q) =
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
        (fun _ _ => none) := by
  have h : seedGame adversary q a R = gameD a (restDepth a R) R (GDseed adversary q) :=
    funext (seedGame_eq_gameD q a R)
  unfold mixLaw
  rw [h]

section View
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain a)
  (E : PrefixView → Prop) (hE0 : ∀ z : Digest × (SeedResult × TObs 0), ¬E (runViewD a 0 z))
include ha hE0

end View

/-! ### Expected counts by layers -/

theorem nat_eq_sum_lt (n m : ℕ) (h : n ≤ m) :
    (n : ℝ≥0∞) = ∑ k ∈ Finset.range m, (if k < n then 1 else 0) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [show (Finset.range m).filter (fun k => k < n) = Finset.range n by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega, Finset.card_range]

theorem expectation_layers {α : Type} (P : PMF α) (X : α → ℕ) (m : ℕ) (hX : ∀ s ∈ P.support, X s ≤ m) :
    ∑' s, P s * (X s : ℝ≥0∞) = ∑ k ∈ Finset.range m, Pr[fun s => k < X s | P] := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun s => ?_
  by_cases hs : s ∈ P.support
  · rw [nat_eq_sum_lt (X s) m (hX s hs), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  · rw [(PMF.apply_eq_zero_iff P s).mpr hs]
    simp

theorem calls_prefixQuery_zero (a : ChainAddr) (qs : List RefWorld.Domain) :
    calls (PrefixGame.PrefixQuery a 0) qs = 0 := by
  unfold calls
  rw [List.countP_eq_zero]
  rintro x - hx
  simp only [decide_eq_true_eq] at hx
  obtain ⟨i, -, -⟩ := hx
  exact i.elim0

theorem prefixCount_le_length (a : ChainAddr) (s : RefSample) : prefixCount a s ≤ s.trace.length :=
  List.length_filter_le _ _

/-- Total seed-test error over the source chains. -/
noncomputable def errTot (adversary : AdversaryP) (q : ℕ) : ℝ≥0∞ :=
  ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, errC adversary q a

end Leaf
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.LeafView
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun)
open SphincsSecurity.QueryCap (recorded counted calls)
open Core
open ClaudeWCT.W9.T3.Security.Wots.Leaf (prob_pmf_map prob_bind)
set_option maxHeartbeats 100000
set_option Elab.async false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers PairedReference.referenceGame PairedReference.offlineGame
noncomputable local instance : Fintype Coordinate := coordinateFintype
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}

theorem runView_eq (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (r : Digest × (SeedResult × ClaudeWCT.W9.T3.Security.Wots.Leaf.TObs (RawPrefix.restDepth a R))) :
    runView a R r = ClaudeWCT.W9.T3.Security.Wots.Leaf.runViewD a (RawPrefix.restDepth a R) r := rfl

theorem reference_map_view (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) :
    (PairedReference.referenceExperiment adversary q).map (sampleView a) =
      (Core.restLaw (PairedReference.referenceInputs adversary)).bind (fun R =>
        (Core.frozenLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (Core.GDseed adversary q)).map
          (ClaudeWCT.W9.T3.Security.Wots.Leaf.runViewD a (RawPrefix.restDepth a R))) := by
  rw [reference_map_eq_frozen adversary q a ha (sampleView a) (fun R => ClaudeWCT.W9.T3.Security.Wots.Leaf.runViewD a (RawPrefix.restDepth a R))
    (fun R x res hres => (sampleView_coupled adversary q a R ha.1 x res hres).trans (runView_eq a R _))]
  change _ = (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind _
  apply congrArg (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind
  funext R
  unfold Core.frozenLaw
  rw [PMF.map_bind]
  congr 1
  funext x
  rw [PMF.map_comp, Core.seedGame_eq_gameD]
  rfl

theorem reference_prob_view (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) (E : PrefixView → Prop) :
    Pr[fun s => E (sampleView a s) | PairedReference.referenceExperiment adversary q] =
      ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        Pr[fun z => E (ClaudeWCT.W9.T3.Security.Wots.Leaf.runViewD a (RawPrefix.restDepth a R) z) |
          Core.frozenLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (Core.GDseed adversary q)] := by
  change Pr[E ∘ sampleView a | PairedReference.referenceExperiment adversary q] = _
  rw [← prob_pmf_map, reference_map_view q ha, prob_bind]
  simp only [prob_pmf_map, Function.comp_def]

theorem mixLaw_seed (q : ℕ) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) :
    Core.mixLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (Core.GDseed adversary q) =
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none) := by
  have h : seedGame (referenceInputs_subset adversary) adversary q a R =
      Core.gameD (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (Core.GDseed adversary q) :=
    funext (Core.seedGame_eq_gameD q a R)
  unfold Core.mixLaw
  rw [h]

section View
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  (E : PrefixView → Prop) (hE0 : ∀ z : Digest × (SeedResult × ClaudeWCT.W9.T3.Security.Wots.Leaf.TObs 0), ¬E (ClaudeWCT.W9.T3.Security.Wots.Leaf.runViewD a 0 z))
include ha hE0

end View

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.LeafView

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.LeafView
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun)
open SphincsSecurity.QueryCap (recorded counted calls)
open Core
open ClaudeWCT.W9.T3.Security.Wots.Leaf (runViewD)
set_option maxHeartbeats 100000
set_option Elab.async false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers PairedReference.referenceGame PairedReference.offlineGame
noncomputable local instance : Fintype Coordinate := coordinateFintype
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}

theorem prefixCount_le_length (a : ChainAddr) (s : RefSample) : prefixCount a s ≤ s.trace.length :=
  List.length_filter_le _ _

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.LeafView
