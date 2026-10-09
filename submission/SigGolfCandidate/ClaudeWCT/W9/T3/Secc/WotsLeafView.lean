import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsLeafRef

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
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain a) (hl : a.key.lay ≠ 0)
  (E : PrefixView → Prop) (hE0 : ∀ z : Digest × (SeedResult × TObs 0), ¬E (runViewD a 0 z))
include ha hl hE0

theorem view_hyps :
    (∀ T T', LeafCongr a.key T T' → GDseed adversary q T' = GDseed adversary q T) ∧
    (∀ (R : RefTables adversary) (x : Hidden (restDepth a R)) (res : SeedResult × TObs (restDepth a R)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
        (gameD a (restDepth a R) R (GDseed adversary q) (evaluate x.1 (PrefixGame.ovSeed a R x.2)))
          (fun _ _ => none)).support →
      (E (sampleView a (mkSample (restTable (PrefixGame.ov a (restDepth a R) R x)) (id res.1))) ↔
        E (runViewD a (restDepth a R) (evaluate x.1 (PrefixGame.ovSeed a R x.2), res)))) ∧
    (∀ (R : RefTables adversary) (z : Digest × (SeedResult × TObs 0)), ¬E (runViewD a 0 z)) := by
  have htree : a.key.tree < 2 ^ 40 := by have := ha.1.1; omega
  have hleaf := (ref_hyps q ha (GDseed adversary q) id (fun T => id_map _)).2
  refine ⟨fun T T' h => GDseed_leaf hl hleaf htree q T T' h, fun R x res hres => ?_, fun R z => hE0 z⟩
  rw [← seedGame_eq_gameD] at hres
  rw [id, sampleView_coupled adversary q a R x res hres, runView_eq]

/-- **View probabilities, reference ≤ mixture.** -/
theorem view_prob_le :
    Pr[fun s => E (sampleView a s) | referenceExperiment adversary q] ≤
      ∑' R, restLaw adversary R * Pr[fun r => E (runView a R r) |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)] + errC adversary q a := by
  obtain ⟨hG, hEF, hF0⟩ := view_hyps q ha hl E hE0
  have h := ref_le_mix q ha hl (GDseed adversary q) id (fun T => id_map _) (fun s => E (sampleView a s))
    (fun d _ z => E (runViewD a d z)) (fun _ _ _ _ _ => rfl) hF0 hG hEF
  simp only [mixLaw_seed] at h
  exact h

/-- **View probabilities, mixture ≤ reference.** -/
theorem view_prob_ge :
    ∑' R, restLaw adversary R * Pr[fun r => E (runView a R r) |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)] ≤
      Pr[fun s => E (sampleView a s) | referenceExperiment adversary q] + errC adversary q a := by
  obtain ⟨hG, hEF, hF0⟩ := view_hyps q ha hl E hE0
  have h := mix_le_ref q ha hl (GDseed adversary q) id (fun T => id_map _) (fun s => E (sampleView a s))
    (fun d _ z => E (runViewD a d z)) (fun _ _ _ _ _ => rfl) hF0 hG hEF
  simp only [mixLaw_seed] at h
  exact h
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

/-- **Expected prefix counts, mixture ≤ reference + q · error.** -/
theorem view_count_le (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain a) (hl : a.key.lay ≠ 0) :
    ∑' R, restLaw adversary R * ∑' r,
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞) ≤
      ∑' s, referenceExperiment adversary q s * (prefixCount a s : ℝ≥0∞) + q * errC adversary q a := by
  have hmix : ∀ R : RefTables adversary, ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞) =
      ∑ k ∈ Finset.range q, Pr[fun r => (fun v : PrefixView => k < v.count) (runView a R r) |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)] :=
    fun R => expectation_layers _ (fun r => seedCost a R r.2.1) q (fun r hr => seedGame_real_cost adversary q a R r hr)
  have href : ∑' s, referenceExperiment adversary q s * (prefixCount a s : ℝ≥0∞) =
      ∑ k ∈ Finset.range q, Pr[fun s => (fun v : PrefixView => k < v.count) (sampleView a s) |
        referenceExperiment adversary q] :=
    expectation_layers _ (prefixCount a) q (fun s hs =>
      (prefixCount_le_length a s).trans (ref_trace_length_le adversary q s hs))
  simp only [hmix, href]
  calc ∑' R, restLaw adversary R * ∑ k ∈ Finset.range q, Pr[fun r => k < (runView a R r).count |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)]
      = ∑ k ∈ Finset.range q, ∑' R, restLaw adversary R * Pr[fun r => k < (runView a R r).count |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)] := by
        simp only [Finset.mul_sum]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ k ∈ Finset.range q, (Pr[fun s => k < (sampleView a s).count | referenceExperiment adversary q] +
          errC adversary q a) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact view_prob_ge q ha hl (fun v => k < v.count) (fun z h => by
          simp only [runViewD, calls_prefixQuery_zero] at h
          omega)
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Total seed-test error over the source chains. -/
noncomputable def errTot (adversary : AdversaryP) (q : ℕ) : ℝ≥0∞ :=
  ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, errC adversary q a

end Leaf
end ClaudeWCT.W9.T3.Security.Wots
