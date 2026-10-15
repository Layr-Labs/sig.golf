import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsLeafCore

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

include hLleaf in
/-- Resampling the leaf data, the event and the law at the resampled table. -/
theorem resample_ind (Law : (d : ℕ) → RefTables adversary → PMF (Digest × (Res × TObs d))) :
    ∑' R, restLaw adversary R * Pr[F (restDepth a R) R | Law (restDepth a R) R] =
      ∑' R, restLaw adversary R * Pr[fun w => F (restDepth a R) (ovL a.key R w.1) w.2 |
        (PMF.uniformOfFintype (LeafData a.key)).bind
          (fun y => (Law (restDepth a R) (ovL a.key R y)).map (fun z => (y, z)))] := by
  rw [restLaw_resampleL_tsum hLleaf (fun R => Pr[F (restDepth a R) R | Law (restDepth a R) R])]
  refine tsum_congr fun R => ?_
  congr 1
  rw [prob_bind]
  refine tsum_congr fun y => ?_
  congr 1
  rw [prob_pmf_map, restDepth_ovL hLleaf a rfl R y]
  rfl

theorem prob_zero_of_depth {R : RefTables adversary} (h0 : restDepth a R = 0) {Ω : Type}
    (G : Ω → Digest × (Res × TObs (restDepth a R)) → Prop)
    (hG0 : ∀ w : Ω × (Digest × (Res × TObs (restDepth a R))), ¬G w.1 w.2)
    (P : PMF (Ω × (Digest × (Res × TObs (restDepth a R))))) : Pr[fun w => G w.1 w.2 | P] = 0 := by
  rw [probEvent_eq_tsum_ite]
  exact ENNReal.tsum_eq_zero.mpr fun w => if_neg (hG0 w)

include hac hLleaf hG hGq hF hF0

/-- **Frozen ≤ mixture + error.** -/
theorem frozen_le_mix :
    ∑' R, restLaw adversary R * Pr[F (restDepth a R) R | frozenLaw a (restDepth a R) R GD] ≤
      ∑' R, restLaw adversary R * Pr[F (restDepth a R) R | mixLaw a (restDepth a R) R GD] +
        ∑' R, restLaw adversary R * errAR a hac GD q R := by
  rw [resample_ind hLleaf F (fun d R => frozenLaw a d R GD),
    resample_ind hLleaf F (fun d R => mixLaw a d R GD), ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun R => ?_
  rw [← mul_add]
  refine mul_le_mul' le_rfl ?_
  by_cases hd1 : 1 ≤ restDepth a R
  · unfold errAR
    rw [dif_pos hd1]
    exact frozen_le_mix_R rfl hac hLleaf R hd1 GD hG (selfF hac R hd1) rfl q hGq
      (fun y z => F (restDepth a R) (ovL a.key R y) z) (fun p K K' h => hF R p K K' h)
  · have h0 : restDepth a R = 0 := by omega
    have hF0' : ∀ (d : ℕ), d = 0 → ∀ (R' : RefTables adversary) (z : Digest × (Res × TObs d)), ¬F d R' z := by
      intro d hd
      subst hd
      exact hF0
    rw [prob_zero_of_depth h0 (fun y z => F (restDepth a R) (ovL a.key R y) z) (fun w => hF0' _ h0 _ w.2)]
    exact bot_le

/-- **Mixture ≤ frozen + error.** -/
theorem mix_le_frozen :
    ∑' R, restLaw adversary R * Pr[F (restDepth a R) R | mixLaw a (restDepth a R) R GD] ≤
      ∑' R, restLaw adversary R * Pr[F (restDepth a R) R | frozenLaw a (restDepth a R) R GD] +
        ∑' R, restLaw adversary R * errAR a hac GD q R := by
  rw [resample_ind hLleaf F (fun d R => frozenLaw a d R GD),
    resample_ind hLleaf F (fun d R => mixLaw a d R GD), ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun R => ?_
  rw [← mul_add]
  refine mul_le_mul' le_rfl ?_
  by_cases hd1 : 1 ≤ restDepth a R
  · unfold errAR
    rw [dif_pos hd1]
    exact mix_le_frozen_R rfl hac hLleaf R hd1 GD hG (selfF hac R hd1) rfl q hGq
      (fun y z => F (restDepth a R) (ovL a.key R y) z) (fun p K K' h => hF R p K K' h)
  · have h0 : restDepth a R = 0 := by omega
    have hF0' : ∀ (d : ℕ), d = 0 → ∀ (R' : RefTables adversary) (z : Digest × (Res × TObs d)), ¬F d R' z := by
      intro d hd
      subst hd
      exact hF0
    rw [prob_zero_of_depth h0 (fun y z => F (restDepth a R) (ovL a.key R y) z) (fun w => hF0' _ h0 _ w.2)]
    exact bot_le
end Lift

end Leaf
end ClaudeWCT.W9.T3.Security.Wots
