import SigGolfCandidate.Merge054
import SigGolfCandidate.OuterGroundFresh
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace OuterGroundFactors
open ENNReal
open ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh
theorem facFH_ok_four (b : Nat) (hb1 : 1 ≤ b) (hb3 : b ≤ 5) :
    ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.FacFH SigGolfCandidate.T3.Budgets.signingZ b (mG b) := by
  unfold ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.FacFH
  set zr := SigGolfCandidate.T3.Budgets.signingZ.toReal with hzr
  have hz0 : 0 ≤ zr := ENNReal.toReal_nonneg
  have hzE : SigGolfCandidate.T3.Budgets.signingZ = ENNReal.ofReal zr := (ENNReal.ofReal_toReal signingZ_ne_top).symm
  have hk := ClaudeWCT.Numerics.TopZero.groundM_step b hb1 (by omega) zr signingZ_toReal_le
  have hq0 : (0 : ℝ) ≤ 1 / 2 ^ b := by positivity
  have hq1 : (1 : ℝ) / 2 ^ b ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hm0 : (0 : ℝ) ≤ (ClaudeWCT.Numerics.TopZero.groundM b : ℝ) / ClaudeWCT.Numerics.CanonicalCompression.scale := by
    positivity
  unfold mG
  rw [hzE, inv_two_pow_eq']
  refine ⟨?_, ENNReal.ofReal_le_ofReal hk.2⟩
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0, ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_add hq0 (by nlinarith), ← ENNReal.ofReal_mul hz0]
  exact ENNReal.ofReal_le_ofReal hk.1

theorem outer_fac (coord : Nat) :
    ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.FacFH SigGolfCandidate.T3.Budgets.signingZ
      (OuterGroundCore.width coord) (mG (OuterGroundCore.width coord)) :=
  facFH_ok_four _ (by have := OuterGroundCore.width_bounds coord;omega) (OuterGroundCore.width_bounds coord).2
#print axioms outer_fac
end OuterGroundFactors
