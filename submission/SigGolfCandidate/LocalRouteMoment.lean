import SigGolfCandidate.LocalRouteChecks
import SigGolfCandidate.TopRouteNumerics
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
namespace ClaudeWCT.Numerics.LocalRoute.Moment
open ClaudeWCT.Numerics.CanonicalCompression
open ClaudeWCT.Numerics.TopZero

def fixedCost : Nat := 112007
def fixedBound : Nat := ClaudeWCT.Numerics.LocalRoute.fixedBoundU16
theorem fixed_power_checked : ClaudeWCT.Numerics.CanonicalCompression.powerUp (ClaudeWCT.Numerics.CanonicalCompression.ceilDiv (ClaudeWCT.Numerics.CanonicalCompression.zNum*ClaudeWCT.Numerics.CanonicalCompression.scale) ClaudeWCT.Numerics.CanonicalCompression.zDen) fixedCost ≤ fixedBound := by decide +kernel
theorem fixed_ratio_bound : ((ClaudeWCT.Numerics.CanonicalCompression.zNum:ℝ)/ClaudeWCT.Numerics.CanonicalCompression.zDen)^fixedCost≤(fixedBound:ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale := by
  have hs : (0:ℝ)<ClaudeWCT.Numerics.CanonicalCompression.scale := by norm_num [ClaudeWCT.Numerics.CanonicalCompression.scale]
  have hceil := ceilDiv_ratio_le (ClaudeWCT.Numerics.CanonicalCompression.zNum*ClaudeWCT.Numerics.CanonicalCompression.scale) ClaudeWCT.Numerics.CanonicalCompression.zDen (by norm_num [ClaudeWCT.Numerics.CanonicalCompression.zDen])
  have hc : ((ClaudeWCT.Numerics.CanonicalCompression.zNum:ℝ)/ClaudeWCT.Numerics.CanonicalCompression.zDen)≤(ClaudeWCT.Numerics.CanonicalCompression.ceilDiv (ClaudeWCT.Numerics.CanonicalCompression.zNum*ClaudeWCT.Numerics.CanonicalCompression.scale) ClaudeWCT.Numerics.CanonicalCompression.zDen:ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale := by
    apply (le_div_iff₀ hs).mpr
    simpa only [Nat.cast_mul,mul_div_assoc,div_mul_eq_mul_div] using hceil
  have hp := powerUp_ratio_ge (ClaudeWCT.Numerics.CanonicalCompression.ceilDiv (ClaudeWCT.Numerics.CanonicalCompression.zNum*ClaudeWCT.Numerics.CanonicalCompression.scale) ClaudeWCT.Numerics.CanonicalCompression.zDen) fixedCost
  calc
    _ ≤ ((ClaudeWCT.Numerics.CanonicalCompression.ceilDiv (ClaudeWCT.Numerics.CanonicalCompression.zNum*ClaudeWCT.Numerics.CanonicalCompression.scale) ClaudeWCT.Numerics.CanonicalCompression.zDen:ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale)^fixedCost := by gcongr
    _ ≤ _ := hp.trans (div_le_div_of_nonneg_right (by exact_mod_cast fixed_power_checked) hs.le)


theorem full_moment_checked :
    ClaudeWCT.Numerics.CanonicalCompression.mulUp (ClaudeWCT.Numerics.CanonicalCompression.mulUp (ClaudeWCT.Numerics.CanonicalCompression.mulUp fixedBound ClaudeWCT.Numerics.TopZero.groundBound) ClaudeWCT.Numerics.CanonicalCompression.ftsBound) Tables.meanInitial * 100000 < 200000 * ClaudeWCT.Numerics.CanonicalCompression.scale := by
  decide +kernel

theorem envelope_ratio_le_two :
    (((fixedBound : ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale)*((ClaudeWCT.Numerics.TopZero.groundBound : ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale))*
      (((ClaudeWCT.Numerics.CanonicalCompression.ftsBound : ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale)*((Tables.meanInitial : ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale)) ≤ 2 := by
  have hm := mulUp_ratio_ge fixedBound ClaudeWCT.Numerics.TopZero.groundBound
  have he := ClaudeWCT.Numerics.TopRoute.envelope_from_integer
    (ClaudeWCT.Numerics.CanonicalCompression.mulUp fixedBound ClaudeWCT.Numerics.TopZero.groundBound) Tables.meanInitial 200000 (by norm_num) full_moment_checked
  have h0 : (0 : ℝ) ≤ ((ClaudeWCT.Numerics.CanonicalCompression.ftsBound : ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale)*((Tables.meanInitial : ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact (mul_le_mul_of_nonneg_right hm h0).trans he
#print axioms envelope_ratio_le_two
end ClaudeWCT.Numerics.LocalRoute.Moment
