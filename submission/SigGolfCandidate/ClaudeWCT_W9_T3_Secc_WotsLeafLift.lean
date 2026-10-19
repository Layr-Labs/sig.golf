import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsLeafCore

/-! # The seed-test reduction over the rest tables (campaign X1 stage B, step B3)

`frozen_le_mix` / `mix_le_frozen`: for a lower source chain `a`, the frozen mixture (the reference game) and the
`realRun` mixture (independent seed) give the same probability to every depth-uniform event that is blind to `a`'s
leaf data, up to `errA a`, the rest-table average of `errR`. -/

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
noncomputable local instance instFintypeCoordinate_wotsLeafLift : Fintype Coordinate := coordinateFintype
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.Arith.SideChannel (TSpec Free seedsR)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
variable {adversary : AdversaryP}

theorem prob_bind {α β : Type} (P : PMF α) (Q : α → PMF β) (E : β → Prop) :
    Pr[E | P.bind Q] = ∑' x, P x * Pr[E | Q x] := by
  rw [← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum]
  simp only [PMF.probOutput_eq_apply]

/-- The chain `a` as an unrevealed coordinate of its leaf (depth `≥ 1`). -/
def selfF {a : ChainAddr} (hac : a.chain < chainCount a.key.lay) (R : RefTables adversary)
    (hd1 : 1 ≤ restDepth a R) : Free (revSet a.key R) :=
  ⟨⟨a.chain, hac⟩, by
    unfold revSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [restDepth_eq] at hd1
    intro h
    rw [show (⟨a.key, (⟨a.chain, hac⟩ : Fin (chainCount a.key.lay)).val⟩ : ChainAddr) = a from rfl] at h
    omega⟩

/-- Per rest table error (zero at depth `0`). -/
noncomputable def errAR {Res : Type} (a : ChainAddr) (hac : a.chain < chainCount a.key.lay)
    (GD : Answers → OracleComp RefWorld Res) (q : ℕ) (R : RefTables adversary) : ℝ≥0∞ :=
  if hd1 : 1 ≤ restDepth a R then ENNReal.ofReal (errR (a := a) R GD (selfF hac R hd1) q) else 0

theorem restLaw_resampleL_tsum {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (Φ : RefTables adversary → ℝ≥0∞) :
    ∑' R, restLaw adversary R * Φ R =
      ∑' R, restLaw adversary R * ∑' y, PMF.uniformOfFintype (LeafData L) y * Φ (ovL L R y) := by
  have h := restLaw_resampleL (adversary := adversary) hL (fun R => PMF.pure R)
  simp only [PMF.bind_pure] at h
  conv_lhs => rw [h]
  rw [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind]
  congr 1
  funext R
  congr 1
  rw [show (PMF.uniformOfFintype (LeafData L)).bind (fun y => PMF.pure (ovL L R y)) =
    (PMF.uniformOfFintype (LeafData L)).map (ovL L R) from rfl,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]

section Lift
variable {a : ChainAddr} (hac : a.chain < chainCount a.key.lay) (hLleaf : a.key.leaf < 2 ^ 24)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res) (hG : ∀ T T', LeafCongr a.key T T' → GD T' = GD T)
  (q : ℕ) (hGq : ∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q)
  (F : (d : ℕ) → RefTables adversary → Digest × (Res × TObs d) → Prop)
  (hF : ∀ (R : RefTables adversary) (p : PData a.key (restDepth a R)) (K K' : Fin (WCT9.famCount a.key.lay) → Digest),
    seedsR (ptL a.key) (revSet a.key R) K = seedsR (ptL a.key) (revSet a.key R) K' →
      F (restDepth a R) (ovL a.key R (K, progF p.1.1 p.1.2 K)) =
        F (restDepth a R) (ovL a.key R (K', progF p.1.1 p.1.2 K')))
  (hF0 : ∀ R z, ¬F 0 R z)

theorem prob_zero_of_depth {R : RefTables adversary} (h0 : restDepth a R = 0) {Ω : Type}
    (G : Ω → Digest × (Res × TObs (restDepth a R)) → Prop)
    (hG0 : ∀ w : Ω × (Digest × (Res × TObs (restDepth a R))), ¬G w.1 w.2)
    (P : PMF (Ω × (Digest × (Res × TObs (restDepth a R))))) : Pr[fun w => G w.1 w.2 | P] = 0 := by
  rw [probEvent_eq_tsum_ite]
  exact ENNReal.tsum_eq_zero.mpr fun w => if_neg (hG0 w)

include hac hLleaf hG hGq hF hF0

end Lift

end Leaf
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable def restLaw (U : Finset HashInput) : PMF (Tables U) := PMF.uniformOfFintype (Tables U)
theorem sourceLeaf_leaf_lt {L : LeafAddr} (hL : WotsExtract.SourceLeaf7 L) : L.leaf<2^24 := by
  have hh : ∀lay:Layer,2^height lay≤2^24 := by intro lay;fin_cases lay<;>decide
  exact hL.2.trans_le (hh L.lay)
/-- The chain `a` as an unrevealed coordinate of its leaf (depth `≥ 1`). -/
def selfF {a : ChainAddr} (hac : a.chain < chainCount a.key.lay) (R : Tables U)
    (hd1 : 1 ≤ RawPrefix.restDepth a R) : Free (revSet a.key R) :=
  ⟨⟨a.chain, hac⟩, by
    unfold revSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [RawPrefix.restDepth_eq] at hd1
    intro h
    rw [show (⟨a.key, (⟨a.chain, hac⟩ : Fin (chainCount a.key.lay)).val⟩ : ChainAddr) = a from rfl] at h
    omega⟩

/-- Per rest table error (zero at depth `0`). -/
noncomputable def errAR {Res : Type} (a : ChainAddr) (hac : a.chain < chainCount a.key.lay)
    (GD : Answers → OracleComp RefWorld Res) (q : ℕ) (R : Tables U) : ℝ≥0∞ :=
  if hd1 : 1 ≤ RawPrefix.restDepth a R then ENNReal.ofReal (errR hU (a := a) R GD (selfF hac R hd1) q) else 0

include hU in
theorem restLaw_resampleL_tsum {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (Φ : Tables U → ℝ≥0∞) :
    ∑' R, restLaw U R * Φ R =
      ∑' R, restLaw U R * ∑' y, PMF.uniformOfFintype (LeafData L) y * Φ (RawLeaf.ovL L R y) := by
  unfold restLaw
  have h := RawLeaf.restLaw_resampleL hU hL (fun R => PMF.pure R)
  simp only [PMF.bind_pure] at h
  conv_lhs => rw [h]
  rw [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind]
  congr 1
  funext R
  congr 1
  rw [show (PMF.uniformOfFintype (LeafData L)).bind (fun y => PMF.pure (RawLeaf.ovL L R y)) =
    (PMF.uniformOfFintype (LeafData L)).map (RawLeaf.ovL L R) from rfl,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]

section Lift
variable {a : ChainAddr} (hac : a.chain < chainCount a.key.lay) (hL : WotsExtract.SourceLeaf7 a.key)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res) (hG : ∀ T T', CanonicalRef.Leaf.Congr (sourceMessages T) a.key T T' → GD T' = GD T)
  (q : ℕ) (hGq : ∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q)
  (F : (d : ℕ) → Tables U → Digest × (Res × TObs d) → Prop)
  (hF : ∀ (R : Tables U) (p : PData a.key (RawPrefix.restDepth a R)) (K K' : Fin (WCT9.famCount a.key.lay) → Digest),
    seedsR (ptL a.key) (revSet a.key R) K = seedsR (ptL a.key) (revSet a.key R) K' →
      F (RawPrefix.restDepth a R) (RawLeaf.ovL a.key R (K, progF p.1.1 p.1.2 K)) =
        F (RawPrefix.restDepth a R) (RawLeaf.ovL a.key R (K', progF p.1.1 p.1.2 K')))
  (hF0 : ∀ R z, ¬F 0 R z)

theorem prob_zero_of_depth {R : Tables U} (h0 : RawPrefix.restDepth a R = 0) {Ω : Type}
    (G : Ω → Digest × (Res × TObs (RawPrefix.restDepth a R)) → Prop)
    (hG0 : ∀ w : Ω × (Digest × (Res × TObs (RawPrefix.restDepth a R))), ¬G w.1 w.2)
    (P : PMF (Ω × (Digest × (Res × TObs (RawPrefix.restDepth a R))))) : Pr[fun w => G w.1 w.2 | P] = 0 := by
  rw [probEvent_eq_tsum_ite]
  exact ENNReal.tsum_eq_zero.mpr fun w => if_neg (hG0 w)

include hac hL hG hGq hF hF0

end Lift
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core
