import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamLift
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_FinalG

/-! # Family restart, step P6a: the total family seed-test error (r3-lean-seedfam)

`errTotF S adversary q := ∑ over source chains of errCF` (family analogue of `Contacts.errTot`), bounded by the charge
`Cmax` (`errTotF_le`), in reals `errTotF ≤ 2·Cmax·y³/(1-y)` with the one-sided side-channel constant
(`errTotF_toReal`), hence the small-route seed-error hypothesis for `Cmax ≤ 305` (`seedErrorBoundF`; v6: `Cmax = 301`,
`errTotF ≤ 602 y³/(1-y)`). -/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Total family seed-test error over the source chains. -/
noncomputable def errTotF (S : FamScheme) (adversary : Final.Paired.AdversaryP) (q : Nat) : ℝ≥0∞ :=
  ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, FamLift.errCF S adversary q a

/-- Scheme-wide hypotheses of the family restart. -/
structure FamHyps (S : FamScheme) (Cmax : Nat) where
  caps : FamCaps S
  grp_le : ∀ lay, S.grp lay ≤ 2 ^ 20
  charge : ∀ lay, S.grp lay * chainCount lay ≤ Cmax
  width : ∀ lay, chainCount lay ≤ S.stride lay
  points : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024

theorem errTotF_le {S : FamScheme} {Cmax : Nat} (H : FamHyps S Cmax) (adversary : Final.Paired.AdversaryP) (q : Nat)
    (hq : q < 2 ^ 128) :
    errTotF S adversary q ≤ ENNReal.ofReal (Core.errConst q) * ((Cmax : ℝ≥0∞) * q) :=
  FamLift.errC_sum_leF S H.grp_le Cmax H.charge H.caps H.width H.points q
    (CanonicalWeighted.query_card_lt_one q hq)

theorem errTotF_toReal {S : FamScheme} {Cmax : Nat} (H : FamHyps S Cmax) (adversary : Final.Paired.AdversaryP)
    (q : Nat) (hq : q < 2 ^ 128) :
    (errTotF S adversary q).toReal ≤ 2 * Cmax * ((q : ℝ) / 2 ^ 128) ^ 3 / (1 - (q : ℝ) / 2 ^ 128) := by
  have h0 := CanonicalWeighted.errConst_nonneg q hq
  have hle := errTotF_le H adversary q hq
  have h := ENNReal.toReal_mono (by finiteness) hle
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal h0, ENNReal.toReal_natCast] at h
  have hd : 0 < 1 - (q : ℝ) / 2 ^ 128 := by
    have hq' : (q : ℝ) < 2 ^ 128 := by exact_mod_cast hq
    exact sub_pos.mpr ((div_lt_one (by positivity)).2 hq')
  have hn : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hk := CanonicalWeighted.kconst_le_sq q
  have hm : 0 ≤ (Cmax : ℝ) * (q : ℝ) := mul_nonneg (Nat.cast_nonneg _) hn
  have hc : 0 ≤ 2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) 128)) 3)
  unfold Core.errConst at h
  have hcard : (Fintype.card Digest : ℝ) = 2 ^ 128 := by rw [Fintype.card_bitVec]; norm_num
  rw [hcard] at h
  have hrat : ((2 : ℝ) ^ 128)⁻¹ * (q : ℝ) = (q : ℝ) / 2 ^ 128 := by ring
  rw [hrat] at h
  calc (errTotF S adversary q).toReal
      ≤ (2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 * (ClaudeWCT.Arith.SideChannel.kconst q : ℝ) / (1 - (q : ℝ) / 2 ^ 128)) *
          ((Cmax : ℝ) * q) := h
    _ ≤ (2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 * ((q : ℝ) ^ 2) / (1 - (q : ℝ) / 2 ^ 128)) * ((Cmax : ℝ) * q) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk hc) hd.le) hm
    _ = _ := by ring

/-- The family seed-error hypothesis of the small route (`errTotF ≤ (733/1000) y²` on `y ≤ 3/2500`) for `Cmax ≤ 305`. -/
theorem seedErrorBoundF {S : FamScheme} {Cmax : Nat} (H : FamHyps S Cmax) (hC : Cmax ≤ 305)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (hy : (q : ℝ) / 2 ^ 128 ≤ 3 / 2500) :
    (errTotF S adversary q).toReal ≤ (733 / 1000) * ((q : ℝ) / 2 ^ 128) ^ 2 :=
  (errTotF_toReal H adversary q hq).trans
    (grouped_seed_error Cmax _ (Nat.cast_nonneg _) (by exact_mod_cast hC) (by positivity) hy)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot
