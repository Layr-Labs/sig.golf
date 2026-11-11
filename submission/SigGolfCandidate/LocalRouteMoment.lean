import SigGolfCandidate.LocalRouteChecks
import SigGolfCandidate.TopRouteNumerics
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
namespace ClaudeWCT.Numerics.LocalRoute.Moment
open ClaudeWCT.Numerics.CanonicalCompression
open ClaudeWCT.Numerics.TopZero

theorem full_moment_checked :
    ClaudeWCT.Numerics.CanonicalCompression.mulUp (ClaudeWCT.Numerics.CanonicalCompression.mulUp (ClaudeWCT.Numerics.CanonicalCompression.mulUp ClaudeWCT.Numerics.TopZero.fixedBoundU16 ClaudeWCT.Numerics.TopZero.groundBound) ClaudeWCT.Numerics.CanonicalCompression.ftsBound) Tables.meanInitial * 100000 < 200000 * ClaudeWCT.Numerics.CanonicalCompression.scale := by
  decide +kernel

theorem envelope_ratio_le_two :
    (((ClaudeWCT.Numerics.TopZero.fixedBoundU16 : ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale)*((ClaudeWCT.Numerics.TopZero.groundBound : ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale))*
      (((ClaudeWCT.Numerics.CanonicalCompression.ftsBound : ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale)*((Tables.meanInitial : ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale)) ≤ 2 := by
  have hm := mulUp_ratio_ge ClaudeWCT.Numerics.TopZero.fixedBoundU16 ClaudeWCT.Numerics.TopZero.groundBound
  have he := ClaudeWCT.Numerics.TopRoute.envelope_from_integer
    (ClaudeWCT.Numerics.CanonicalCompression.mulUp ClaudeWCT.Numerics.TopZero.fixedBoundU16 ClaudeWCT.Numerics.TopZero.groundBound) Tables.meanInitial 200000 (by norm_num) full_moment_checked
  have h0 : (0 : ℝ) ≤ ((ClaudeWCT.Numerics.CanonicalCompression.ftsBound : ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale)*((Tables.meanInitial : ℝ)/ClaudeWCT.Numerics.CanonicalCompression.scale) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact (mul_le_mul_of_nonneg_right hm h0).trans he
#print axioms envelope_ratio_le_two
end ClaudeWCT.Numerics.LocalRoute.Moment
