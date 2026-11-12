import SigGolfCandidate.OuterGroundNumerics
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterEnvelope
open ClaudeWCT.Numerics.CanonicalCompression ClaudeWCT.Numerics.TopZero

theorem fixed_ratio_bound : ((zNum:ℝ)/zDen)^OuterGroundNumerics.fixedCost≤(OuterGroundNumerics.fixedBound:ℝ)/scale := by
  have hs : (0:ℝ)<scale := by norm_num [scale]
  have hceil:=ceilDiv_ratio_le (zNum*scale) zDen (by norm_num [zDen])
  have hc : ((zNum:ℝ)/zDen)≤(ceilDiv (zNum*scale) zDen:ℝ)/scale := by
    apply (le_div_iff₀ hs).mpr
    simpa only [Nat.cast_mul,mul_div_assoc,div_mul_eq_mul_div] using hceil
  have hp:=powerUp_ratio_ge (ceilDiv (zNum*scale) zDen) OuterGroundNumerics.fixedCost
  exact (pow_le_pow_left₀ (by positivity) hc _).trans hp

theorem outer_ratio_bound : ((groundM 3:ℝ)/scale)^8*((groundM 4:ℝ)/scale)^2≤
    (OuterGroundNumerics.outerBound:ℝ)/scale := by
  have h3:=powerUp_ratio_ge (groundM 3) 8
  have h4:=powerUp_ratio_ge (groundM 4) 2
  have nn (n : Nat) : (0:ℝ)≤(n:ℝ)/scale := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact (mul_le_mul h3 h4 (by positivity) (nn _)).trans (mulUp_ratio_ge _ _)
#print axioms fixed_ratio_bound
#print axioms outer_ratio_bound
end OuterEnvelope
