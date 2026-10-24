import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamCore
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamSum1

/-! # Family restart, steps P4c/P5b: the lift over the rest tables and the seed-error charge (r3-lean-seedfam)

Family port of `WotsLeafLift` (normalized part: `selfF`, `errAR`, `restLaw_resampleL_tsum`, `resample_ind`,
`frozen_le_mix`, `mix_le_frozen`) and of the normalized charge of `WotsLeafSum` (`enT_testRun_rec`, `tcount`,
`errR_le_count`, `count_frozen`, `frozenCount`, `errAR_sum_le`, `reference_map_NL`, `frozenCount_eq`, `errC`,
`errC_le`, `errC_sum_le`). The leaf `L` becomes a family `F` of a scheme `S`, chain `a = chainOfF ca`, the leaf
resampling becomes `RawFam.restLaw_resampleF`, and the per-leaf allocation `54` becomes `Cmax ≥ grp · chainCount`.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf chainOfF FamData FamOkS)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW gptS)
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
noncomputable local instance : Fintype Coordinate := coordinateFintype

/-- The chain `a = chainOfF ca` as an unrevealed chain of its family (depth `≥ 1`). -/
def selfFF (S : FamScheme) {F : FamAddr} {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U)
    (hd1 : 1 ≤ RawPrefix.restDepth a R) : Free (RawFam.revSetF S F R) :=
  ⟨ca, by
    simp only [RawFam.revSetF, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro _ h
    rw [RawPrefix.restDepth_eq, haF] at hd1
    omega⟩

/-- Per rest table error of the family restart (zero at depth `0`). -/
noncomputable def errARF (S : FamScheme) {F : FamAddr} {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) {Res : Type}
    (GD : Answers → OracleComp RefWorld Res) (q : ℕ) (R : Tables U) : ℝ≥0∞ :=
  if hd1 : 1 ≤ RawPrefix.restDepth a R then
    ENNReal.ofReal (FamCore.errRF hU (a := a) R GD (selfFF S ca haF R hd1) q) else 0

include hU in
theorem restLaw_resampleF_tsum {g w b n : Nat} {F : FamAddr} (hF : RawFam.FamOk g w b n F)
    (Φ : Tables U → ℝ≥0∞) :
    ∑' R, Core.restLaw U R * Φ R =
      ∑' R, Core.restLaw U R * ∑' y, PMF.uniformOfFintype (FamData g w n) y * Φ (RawFam.ovF g w b n F R y) := by
  unfold Core.restLaw
  have h := RawFam.restLaw_resampleF hU hF (fun R => PMF.pure R)
  simp only [PMF.bind_pure] at h
  conv_lhs => rw [h]
  rw [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind]
  congr 1
  funext R
  congr 1
  rw [show (PMF.uniformOfFintype (FamData g w n)).bind (fun y => PMF.pure (RawFam.ovF g w b n F R y)) =
    (PMF.uniformOfFintype (FamData g w n)).map (RawFam.ovF g w b n F R) from rfl,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]

theorem revSetF_ovF (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) (R : Tables U)
    (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) :
    RawFam.revSetF S F (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) =
      RawFam.revSetF S F R := by
  unfold RawFam.revSetF
  congr 1
  funext c
  rw [RawFam.depth_ovF S hF R y]

section Lift
variable (S : FamScheme) {F : FamAddr} (hF : FamOkS S F)
  (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → GD T' = GD T)
  (q : ℕ) (hGq : ∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q)
  (C : FamCaps S) (hws : chainCount F.lay ≤ S.stride F.lay)
  (hb : (S.grp F.lay - 1) * S.stride F.lay + chainCount F.lay < 1024)
  (E : (d : ℕ) → Tables U → Digest × (Res × TObs d) → Prop)
  (hE : ∀ (R : Tables U) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))
      (K K' : Fin (S.size F.lay F.fam) → Digest),
    seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K = seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K' →
      E (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
          (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)) =
        E (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
          (K', RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K')))
  (hE0 : ∀ R z, ¬E 0 R z)

include hU hF in
/-- Resampling the family data, the event and the law at the resampled table. -/
theorem resample_indF (Law : (d : ℕ) → Tables U → PMF (Digest × (Res × TObs d))) :
    ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Law (RawPrefix.restDepth a R) R] =
      ∑' R, Core.restLaw U R * Pr[fun w => E (RawPrefix.restDepth a R)
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R w.1) w.2 |
        (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
          (fun y => (Law (RawPrefix.restDepth a R)
            (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)).map
              (fun z => (y, z)))] := by
  rw [restLaw_resampleF_tsum hU hF (fun R => Pr[E (RawPrefix.restDepth a R) R | Law (RawPrefix.restDepth a R) R])]
  refine tsum_congr fun R => ?_
  congr 1
  rw [prob_bind]
  refine tsum_congr fun y => ?_
  congr 1
  rw [prob_pmf_map, RawFam.restDepth_ovF S hF R y a]
  rfl

include hU hF htb haF hG hGq C hws hb hE hE0

/-- **Frozen ≤ mixture + error** (family version). -/
theorem frozen_le_mixF :
    ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Core.frozenLaw hU a (RawPrefix.restDepth a R) R GD] ≤
      ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Core.mixLaw hU a (RawPrefix.restDepth a R) R GD] +
        ∑' R, Core.restLaw U R * errARF hU S ca haF GD q R := by
  rw [resample_indF hU S hF (a := a) E (fun d R => Core.frozenLaw hU a d R GD),
    resample_indF hU S hF (a := a) E (fun d R => Core.mixLaw hU a d R GD), ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun R => ?_
  rw [← mul_add]
  refine mul_le_mul' le_rfl ?_
  by_cases hd1 : 1 ≤ RawPrefix.restDepth a R
  · unfold errARF
    rw [dif_pos hd1]
    exact FamCore.frozen_le_mix_RF hU hF htb ca haF R hd1 GD hG (selfFF S ca haF R hd1) rfl q hGq C hws hb
      (fun y z => E (RawPrefix.restDepth a R)
        (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) z)
      (fun p K K' h => hE R p K K' h)
  · have h0 : RawPrefix.restDepth a R = 0 := by omega
    have hF0' : ∀ (d : ℕ), d = 0 → ∀ (R' : Tables U) (z : Digest × (Res × TObs d)), ¬E d R' z := by
      intro d hd
      subst hd
      exact hE0
    rw [Core.prob_zero_of_depth h0 (fun y z => E (RawPrefix.restDepth a R)
      (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) z)
      (fun w => hF0' _ h0 _ w.2)]
    exact bot_le

/-- **Mixture ≤ frozen + error** (family version). -/
theorem mix_le_frozenF :
    ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Core.mixLaw hU a (RawPrefix.restDepth a R) R GD] ≤
      ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Core.frozenLaw hU a (RawPrefix.restDepth a R) R GD] +
        ∑' R, Core.restLaw U R * errARF hU S ca haF GD q R := by
  rw [resample_indF hU S hF (a := a) E (fun d R => Core.frozenLaw hU a d R GD),
    resample_indF hU S hF (a := a) E (fun d R => Core.mixLaw hU a d R GD), ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun R => ?_
  rw [← mul_add]
  refine mul_le_mul' le_rfl ?_
  by_cases hd1 : 1 ≤ RawPrefix.restDepth a R
  · unfold errARF
    rw [dif_pos hd1]
    exact FamCore.mix_le_frozen_RF hU hF htb ca haF R hd1 GD hG (selfFF S ca haF R hd1) rfl q hGq C hws hb
      (fun y z => E (RawPrefix.restDepth a R)
        (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) z)
      (fun p K K' h => hE R p K K' h)
  · have h0 : RawPrefix.restDepth a R = 0 := by omega
    have hF0' : ∀ (d : ℕ), d = 0 → ∀ (R' : Tables U) (z : Digest × (Res × TObs d)), ¬E d R' z := by
      intro d hd
      subst hd
      exact hE0
    rw [Core.prob_zero_of_depth h0 (fun y z => E (RawPrefix.restDepth a R)
      (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) z)
      (fun w => hF0' _ h0 _ w.2)]
    exact bot_le
end Lift

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf chainOfF FamData FamOkS)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW gptS)
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
noncomputable local instance : Fintype Coordinate := coordinateFintype
open ClaudeWCT.Arith.SideChannel (exT enT amLen tdepth)
open SphincsSecurity.QueryCap (recorded counted calls)

/-- Expected number of tests = expected number of test queries in the recorded list (family version). -/
theorem enT_testRun_recF {S : FamScheme} {F : FamAddr} {a : ChainAddr} {R : Tables U} {Res : Type}
    (G0 : Answers → OracleComp RefWorld Res) (aF : Free (RawFam.revSetF S F R))
    (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))
    (r : GChainW (S.grp F.lay) (chainCount F.lay) → Digest) (y : Free (RawFam.revSetF S F R) → Digest) :
    enT y (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p r) =
      exT y (fun out => (calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R)
          (RawFam.revSetF S F R)) out.1.2 : ℝ))
        (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p r) := by
  unfold FamCore.testRunF
  rw [enT_simulate y _ (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (RawFam.revSetF S F R))
      (fun q s => FamTest.enT_testImplF (F := F) (a := a) (FamCore.TstF hU S F a R p r) aF _ y q s),
    counted_recorded, simulateQ_map, StateT.run_map, exT_map']
  rfl

section ErrR
variable {S : FamScheme} {F : FamAddr} (hF : FamOkS S F)
  (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
  {Res : Type} (G0 : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → recorded (G0 T') = recorded (G0 T))
  (aF : Free (RawFam.revSetF S F R)) (haca : aF.1 = ca) (q : ℕ)
  (hGq : ∀ T, OracleComp.IsQueryBoundP (recorded (G0 T)) RefCharged q)
  (C : FamCaps S) (hws : chainCount F.lay ≤ S.stride F.lay)
  (hb : (S.grp F.lay - 1) * S.stride F.lay + chainCount F.lay < 1024)

/-- The family test-query count of a run. -/
noncomputable def tcountF (out : (Res × List RefWorld.Domain) × TObs (RawPrefix.restDepth a R)) : ℕ :=
  calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (RawFam.revSetF S F R)) out.1.2

include hGq C hws hb in
/-- **The family error is charged to the expected test count.** -/
theorem errR_le_countF :
    FamCore.errRF hU (a := a) R (fun T => recorded (G0 T)) aF q * (1 - (Fintype.card Digest : ℝ)⁻¹ * q) ≤
      2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q *
        ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), ∑ K : Fin (S.size F.lay F.fam) → Digest,
          (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ *
            ((Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ *
              exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
                (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
                (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p
                  (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) := by
  have hRev : (RawFam.revSetF S F R).card + 3 ≤ S.size F.lay F.fam := FamCore.revSetF_card_le C F R
  have hpt : Function.Injective (gptS (S.stride F.lay) (g := S.grp F.lay) (w := chainCount F.lay)) :=
    ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_injective hws
  have hsmall : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), gptS (S.stride F.lay) c < 1024 :=
    ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_lt hb
  set C' : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q with hC'
  set cK : ℝ := (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹
  set cp : ℝ := (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹
  have hC0 : 0 ≤ C' := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3))
    (Nat.cast_nonneg _)
  have hcK : 0 ≤ cK := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcp : 0 ≤ cp := inv_nonneg.mpr (Nat.cast_nonneg _)
  have e1 : FamCore.errRF hU (a := a) R (fun T => recorded (G0 T)) aF q =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (C' * cK * cp) *
        ∑ K : Fin (S.size F.lay F.fam) → Digest, amLen (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p
          (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) := by
    unfold FamCore.errRF
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by ring
  have e2 : ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R),
      ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * (cp *
        exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
          (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
          (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) *
        ∑ K : Fin (S.size F.lay F.fam) → Digest,
          enT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
            (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => ?_
    rw [enT_testRun_recF]
    unfold tcountF
    ring
  rw [e1, e2, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have hf := ClaudeWCT.Arith.SideChannel.family_amLen_le hpt hsmall hRev
    (fun r => FamCore.testRunF hU (fun T => recorded (G0 T)) aF p r) q
    (fun r => FamCore.tdepth_testRunF hU R (fun T => recorded (G0 T)) aF q hGq p r)
  calc C' * cK * cp * (∑ K : Fin (S.size F.lay F.fam) → Digest,
        amLen (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) *
        (1 - (Fintype.card Digest : ℝ)⁻¹ * q)
      = C' * cK * cp * ((∑ K : Fin (S.size F.lay F.fam) → Digest,
          amLen (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) *
          (1 - (Fintype.card Digest : ℝ)⁻¹ * q)) := by ring
    _ ≤ C' * cK * cp * ∑ K : Fin (S.size F.lay F.fam) → Digest,
          enT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
            (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) :=
        mul_le_mul_of_nonneg_left hf (mul_nonneg (mul_nonneg hC0 hcK) hcp)
    _ = C' * ((cK * cp) * ∑ K : Fin (S.size F.lay F.fam) → Digest,
          enT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
            (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) := by
        ring

include hF htb haF hd1 hG haca in
/-- The expected test count of the decomposed frozen law (family version). -/
theorem count_frozenF :
    ENNReal.ofReal (∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R),
        ∑ K : Fin (S.size F.lay F.fam) → Digest,
          (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ *
            ((Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ *
              exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
                (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
                (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p
                  (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)))) =
      ∑' z, ((PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => Core.frozenLaw hU a (RawPrefix.restDepth a R)
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)
          (fun T => recorded (G0 T)))) z *
          (tcountF (S := S) (F := F) (a := a) R z.2 : ℝ≥0∞) := by
  rw [FamCore.frozen_decompF hU S hF htb ca haF R hd1 (fun T => recorded (G0 T)) hG aF haca]
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  have hx : ∀ (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)),
      ∑' out, evalT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
        (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) out *
          (tcountF (S := S) (F := F) (a := a) R out : ℝ≥0∞) =
      ENNReal.ofReal (exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
        (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
        (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) := by
    intro K p
    rw [ClaudeWCT.Arith.SideChannel.ofReal_exT _ (fun _ => Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  simp only [hx, tsum_fintype, PMF.uniformOfFintype_apply]
  rw [Finset.sum_comm]
  have hnn : ∀ (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)),
      0 ≤ exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
        (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
        (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) :=
    fun K p => ClaudeWCT.Arith.SideChannel.exT_nonneg _ (fun _ => Nat.cast_nonneg _) _
  rw [ENNReal.ofReal_sum_of_nonneg (fun K _ => Finset.sum_nonneg fun p _ => mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _)) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hnn K p)))]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _)) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hnn K p))),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _)), ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _)),
    ← inv_card_eq_ofReal, ← inv_card_eq_ofReal]
end ErrR

section Charge
variable {S : FamScheme} {F : FamAddr} (hF : FamOkS S F)
  (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca)
  {Res : Type} (G0 : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → recorded (G0 T') = recorded (G0 T)) (q : ℕ)
  (hGq : ∀ T, OracleComp.IsQueryBoundP (recorded (G0 T)) RefCharged q)
  (C : FamCaps S) (hws : chainCount F.lay ≤ S.stride F.lay)
  (hb : (S.grp F.lay - 1) * S.stride F.lay + chainCount F.lay < 1024)
  (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1)

/-- The rest-table-averaged expected family test count of the frozen law. -/
noncomputable def frozenCountF (GD : Answers → OracleComp RefWorld (Res × List RefWorld.Domain)) : ℝ≥0∞ :=
  ∑' R, Core.restLaw U R * ∑' z, Core.frozenLaw hU a (RawPrefix.restDepth a R) R GD z *
    (calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (RawFam.revSetF S F R)) z.2.1.2 : ℝ≥0∞)

include hF htb haF hG hGq C hws hb hq in
theorem errAR_sum_leF :
    ∑' R, Core.restLaw U R * errARF hU S ca haF (fun T => recorded (G0 T)) q R ≤
      ENNReal.ofReal (2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q /
        (1 - (Fintype.card Digest : ℝ)⁻¹ * q)) *
        frozenCountF hU (S := S) (F := F) (a := a) (fun T => recorded (G0 T)) := by
  set C' : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q /
    (1 - (Fintype.card Digest : ℝ)⁻¹ * q) with hC'
  have hpos : 0 < 1 - (Fintype.card Digest : ℝ)⁻¹ * q := by linarith
  let Ψd : ℕ → Tables U → ℝ≥0∞ := fun d R' =>
    ∑' z, Core.frozenLaw hU a d R' (fun T => recorded (G0 T)) z *
      (calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a d (RawFam.revSetF S F R')) z.2.1.2 : ℝ≥0∞)
  have hres := restLaw_resampleF_tsum hU hF (fun R => Ψd (RawPrefix.restDepth a R) R)
  unfold frozenCountF
  change _ ≤ ENNReal.ofReal C' * ∑' R, Core.restLaw U R * Ψd (RawPrefix.restDepth a R) R
  rw [hres, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun R => ?_
  rw [mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  unfold errARF
  split_ifs with hd1
  · have hy : ∀ y, Ψd (RawPrefix.restDepth a
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y))
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) =
        ∑' z, Core.frozenLaw hU a (RawPrefix.restDepth a R)
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)
          (fun T => recorded (G0 T)) z * (tcountF (S := S) (F := F) (a := a) R z.2 : ℝ≥0∞) := by
      intro y
      rw [RawFam.restDepth_ovF S hF R y a]
      simp only [Ψd, revSetF_ovF S hF R y]
      rfl
    simp only [hy]
    rw [← SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind,
      ← count_frozenF hU hF htb ca haF R hd1 G0 hG (selfFF S ca haF R hd1) rfl]
    rw [← ENNReal.ofReal_mul (by
      rw [hC']; exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr
        (Nat.cast_nonneg _)) 3)) (Nat.cast_nonneg _)) hpos.le)]
    apply ENNReal.ofReal_le_ofReal
    have h := errR_le_countF hU (a := a) R G0 (selfFF S ca haF R hd1) q hGq C hws hb
    rw [hC', div_mul_eq_mul_div, le_div_iff₀ hpos]
    exact h
  · exact bot_le
end Charge

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf chainOfF FamData FamOkS)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW gptS)
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
noncomputable local instance : Fintype Coordinate := coordinateFintype
open SphincsSecurity.QueryCap (recorded counted calls)
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame

section Ref
variable (S : FamScheme) {F : FamAddr} (hF : FamOkS S F)
  (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (hreal : FamSum.RealM S F ca.1.val)

include hF htb haF hreal in
theorem reference_map_NLF (q : ℕ) (ha : WotsExtract.SourceChain7 a) :
    (PairedReference.referenceExperiment adversary q).map (FamSum.NLF S F) =
      (Core.restLaw (PairedReference.referenceInputs adversary)).bind (fun R =>
        (Core.frozenLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (Core.GDseed adversary q)).map
          (fun z => calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R)
            (RawFam.revSetF S F R)) z.2.1.2)) := by
  rw [reference_map_eq_frozen adversary q a ha (FamSum.NLF S F)
    (fun R z => calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R)
      (RawFam.revSetF S F R)) z.2.1.2)
    (fun R x res _ => FamSum.NL_mkSampleF S (referenceInputs_subset adversary) hF htb ca haF hreal R x res.1)]
  change _ = (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind _
  apply congrArg (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind
  funext R
  unfold Core.frozenLaw
  rw [PMF.map_bind]
  congr 1
  funext x
  rw [PMF.map_comp, Core.seedGame_eq_gameD]
  rfl

include hF htb haF hreal in
/-- **The frozen family count is the reference family count.** -/
theorem frozenCount_eqF (q : ℕ) (ha : WotsExtract.SourceChain7 a) :
    frozenCountF (referenceInputs_subset adversary) (S := S) (F := F) (a := a) (Core.GDseed adversary q) =
      ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLF S F s : ℝ≥0∞) := by
  have e1 : ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLF S F s : ℝ≥0∞) =
      ∑' n, ((PairedReference.referenceExperiment adversary q).map (FamSum.NLF S F)) n * (n : ℝ≥0∞) := by
    rw [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  rw [e1, reference_map_NLF S hF htb ca haF hreal q ha,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind]
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  rfl
end Ref

/-- Family chain coordinates of a chain `a` in its family `famOf S a.key`: member `leaf % grp`, chain `a.chain`. -/
def caOf (S : FamScheme) (a : ChainAddr) (hac : a.chain < chainCount a.key.lay) :
    GChainW (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay) :=
  (⟨a.key.leaf % S.grp a.key.lay, Nat.mod_lt _ (S.grp_pos _)⟩, ⟨a.chain, hac⟩)

theorem chainOf_caOf (S : FamScheme) (a : ChainAddr) (hac : a.chain < chainCount a.key.lay) :
    a = chainOfF (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay) (FamSum.famOf S a.key)
      (caOf S a hac) := by
  obtain ⟨⟨lay, tree, leaf⟩, c⟩ := a
  simp only [chainOfF, famLeaf, caOf, FamSum.famOf, Nat.div_add_mod]

theorem real_caOf (S : FamScheme) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) :
    FamSum.RealM S (FamSum.famOf S a.key) (caOf S a ha.2).1.val := by
  unfold FamSum.RealM
  show S.grp a.key.lay * (a.key.leaf / S.grp a.key.lay) + a.key.leaf % S.grp a.key.lay < 2 ^ height a.key.lay
  rw [Nat.div_add_mod]
  exact ha.1.2

/-- **Admissibility of the family of a source leaf** (group size at most `2^20`). -/
theorem famOk_of_source (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) {L : LeafAddr}
    (hL : WotsExtract.SourceLeaf7 L) : FamOkS S (FamSum.famOf S L) := by
  have hleaf : L.leaf < 2 ^ 12 := by
    have h1 := hL.2
    have h2 : 2 ^ height L.lay ≤ 2 ^ 12 :=
      Nat.pow_le_pow_right (by norm_num) (SigGolfCandidate.T3.Security.Wots.height_le L.lay)
    omega
  have hdiv : L.leaf / S.grp L.lay ≤ L.leaf := Nat.div_le_self _ _
  have hmd : S.grp L.lay * (L.leaf / S.grp L.lay) ≤ L.leaf := Nat.mul_div_le _ _
  have hg := hgrp L.lay
  have hcnt : S.cnt L.lay * (L.leaf / S.grp L.lay) ≤ 512 * 4096 :=
    Nat.mul_le_mul (S.cnt_le L.lay) (by omega)
  have hc := S.cnt_le L.lay
  refine ⟨S.grp_pos _, ?_, ?_, ?_, ?_, S.size_le _ _⟩
  · have := chainCount_le L.lay
    show chainCount L.lay < 2 ^ 24
    omega
  · show S.grp L.lay * (L.leaf / S.grp L.lay) + S.grp L.lay ≤ 2 ^ 24
    omega
  · show L.tree < 2 ^ 40
    have := hL.tree_lt
    omega
  · show S.cnt L.lay * (L.leaf / S.grp L.lay) + S.cnt L.lay ≤ 2 ^ 33
    omega

/-- The seed-game body is invariant under family congruence. -/
theorem GDseed_fam (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) (q : ℕ) (T T' : Answers)
    (h : FamGame.FamCongr S (sourceMessages T) F T T') : Core.GDseed adversary q T' = Core.GDseed adversary q T := by
  unfold Core.GDseed
  rw [FamGame.referenceGame_fam h hF.tree hF.leaf adversary q]

/-- **The per-chain seed-test error of the family restart** (every source chain, charged to its family). -/
noncomputable def errCF (S : FamScheme) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ)
    (a : ChainAddr) : ℝ≥0∞ :=
  if h : WotsExtract.SourceChain7 a then
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
      errARF (referenceInputs_subset adversary) S (F := FamSum.famOf S a.key) (caOf S a h.2) (chainOf_caOf S a h.2)
        (Core.GDseed adversary q) q R
  else 0

theorem errC_leF (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
    (hws : ∀ lay, chainCount lay ≤ S.stride lay)
    (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
    (q : ℕ) (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1) (a : ChainAddr) :
    errCF S adversary q a ≤ ENNReal.ofReal (Core.errConst q) *
      ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLaF S a s : ℝ≥0∞) := by
  unfold errCF
  split_ifs with h
  · have hF := famOk_of_source S hgrp h.1
    unfold FamSum.NLaF
    rw [← frozenCount_eqF S hF h.1.1 (caOf S a h.2) (chainOf_caOf S a h.2) (real_caOf S h) q h]
    exact errAR_sum_leF (referenceInputs_subset adversary) hF h.1.1 (caOf S a h.2) (chainOf_caOf S a h.2)
      (fun T => PairedReference.referenceGame T adversary q) (fun T T' h' => GDseed_fam S hF q T T' h') q
      (fun T => Core.GDseed_queryBound q T) C (hws _) (hb _) hq
  · exact bot_le

/-- **Total seed-test error of the family restart**: `Cmax ≥ grp · chainCount` on every layer. -/
theorem errC_sum_leF (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (Cmax : ℕ)
    (hC : ∀ lay, S.grp lay * chainCount lay ≤ Cmax) (C : FamCaps S)
    (hws : ∀ lay, chainCount lay ≤ S.stride lay)
    (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
    (q : ℕ) (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1) :
    ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, errCF S adversary q a ≤
      ENNReal.ofReal (Core.errConst q) * ((Cmax : ℝ≥0∞) * q) := by
  calc ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, errCF S adversary q a
      ≤ ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, ENNReal.ofReal (Core.errConst q) *
          ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLaF S a s : ℝ≥0∞) :=
        Finset.sum_le_sum fun a _ => errC_leF S hgrp C hws hb q hq a
    _ = ENNReal.ofReal (Core.errConst q) * ∑' s, PairedReference.referenceExperiment adversary q s *
          ((∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, FamSum.NLaF S a s : ℕ) : ℝ≥0∞) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine tsum_congr fun s => ?_
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ ENNReal.ofReal (Core.errConst q) * ((Cmax : ℝ≥0∞) * q) := by
        refine mul_le_mul' le_rfl ?_
        calc ∑' s, PairedReference.referenceExperiment adversary q s *
              ((∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, FamSum.NLaF S a s : ℕ) : ℝ≥0∞)
            ≤ ∑' s, PairedReference.referenceExperiment adversary q s * ((Cmax : ℝ≥0∞) * q) := by
              refine ENNReal.tsum_le_tsum fun s => ?_
              by_cases hs : s ∈ (PairedReference.referenceExperiment adversary q).support
              · refine mul_le_mul' le_rfl ?_
                have h1 := FamSum.sum_NL_leF S hgrp Cmax hC s
                have h2 := Core.ref_trace_length_le adversary q s hs
                have : ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, FamSum.NLaF S a s ≤ Cmax * q := by
                  calc _ ≤ Cmax * s.trace.length := h1
                    _ ≤ Cmax * q := Nat.mul_le_mul_left Cmax h2
                exact_mod_cast this
              · rw [(PMF.apply_eq_zero_iff _ s).mpr hs, zero_mul, zero_mul]
          _ = (Cmax : ℝ≥0∞) * q := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
