import SigGolfCandidate.LocalRouteMoment
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
namespace OuterGroundNumerics
open ClaudeWCT.Numerics.CanonicalCompression ClaudeWCT.Numerics.TopZero
def initial72_0 : Nat := ClaudeWCT.Numerics.LocalRoute.Tables.initial72_0
theorem check72_0 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 16 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_0 initial72_0=true := by decide +kernel
def initial72_1 : Nat := ClaudeWCT.Numerics.LocalRoute.Tables.initial72_1
theorem check72_1 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 16 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_1 initial72_1=true := by decide +kernel
def initial72_2 : Nat := ClaudeWCT.Numerics.LocalRoute.Tables.initial72_2
theorem check72_2 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 16 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_2 initial72_2=true := by decide +kernel
def initial72_3 : Nat := ClaudeWCT.Numerics.LocalRoute.Tables.initial72_3
theorem check72_3 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 16 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_3 initial72_3=true := by decide +kernel
def initial72_4 : Nat := ClaudeWCT.Numerics.LocalRoute.Tables.initial72_4
theorem check72_4 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 16 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_4 initial72_4=true := by decide +kernel
def initial72_5 : Nat := ClaudeWCT.Numerics.LocalRoute.Tables.initial72_5
theorem check72_5 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 16 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_5 initial72_5=true := by decide +kernel
def initial72_6 : Nat := ClaudeWCT.Numerics.LocalRoute.Tables.initial72_6
theorem check72_6 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 16 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_6 initial72_6=true := by decide +kernel
def initial72_7 : Nat := ClaudeWCT.Numerics.LocalRoute.Tables.initial72_7
theorem check72_7 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 16 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_7 initial72_7=true := by decide +kernel
def mean74 : Nat := ClaudeWCT.Numerics.LocalRoute.Tables.meanInitial
theorem mean_checked : ClaudeWCT.Numerics.LocalRoute.Tables.initial71_0 + 2*initial72_0 + ClaudeWCT.Numerics.LocalRoute.Tables.initial73_0 + ClaudeWCT.Numerics.LocalRoute.Tables.initial71_1 + 2*initial72_1 + ClaudeWCT.Numerics.LocalRoute.Tables.initial73_1 + ClaudeWCT.Numerics.LocalRoute.Tables.initial71_2 + 2*initial72_2 + ClaudeWCT.Numerics.LocalRoute.Tables.initial73_2 + ClaudeWCT.Numerics.LocalRoute.Tables.initial71_3 + 2*initial72_3 + ClaudeWCT.Numerics.LocalRoute.Tables.initial73_3 + ClaudeWCT.Numerics.LocalRoute.Tables.initial71_4 + 2*initial72_4 + ClaudeWCT.Numerics.LocalRoute.Tables.initial73_4 + ClaudeWCT.Numerics.LocalRoute.Tables.initial71_5 + 2*initial72_5 + ClaudeWCT.Numerics.LocalRoute.Tables.initial73_5 + ClaudeWCT.Numerics.LocalRoute.Tables.initial71_6 + 2*initial72_6 + ClaudeWCT.Numerics.LocalRoute.Tables.initial73_6 + ClaudeWCT.Numerics.LocalRoute.Tables.initial71_7 + 2*initial72_7 + ClaudeWCT.Numerics.LocalRoute.Tables.initial73_7 ≤ 32*mean74 := by decide +kernel
def fixedCost : Nat := 111997
def fixedBound : Nat := powerUp (ceilDiv (zNum*scale) zDen) fixedCost
def outerBound : Nat := mulUp (powerUp (groundM 5) 8) (powerUp (groundM 4) 2)
theorem outer_checked : outerBound=340801063000205250462000243590921102696 := by decide +kernel
theorem full_moment_checked : mulUp (mulUp (mulUp (mulUp fixedBound groundBound) ftsBound) outerBound) mean74<2*scale := by decide +kernel
theorem envelope_ratio_le_two :
    ((fixedBound:ℝ)/scale)*((groundBound:ℝ)/scale)*((ftsBound:ℝ)/scale)*
      ((outerBound:ℝ)/scale)*((mean74:ℝ)/scale)≤2 := by
  have hs : (0:ℝ)<scale := by norm_num [scale]
  have nn (n : Nat) : (0:ℝ)≤(n:ℝ)/scale := div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg scale)
  have h1:=mulUp_ratio_ge fixedBound groundBound
  have h2:=mulUp_ratio_ge (mulUp fixedBound groundBound) ftsBound
  have h3:=mulUp_ratio_ge (mulUp (mulUp fixedBound groundBound) ftsBound) outerBound
  have h4:=mulUp_ratio_ge (mulUp (mulUp (mulUp fixedBound groundBound) ftsBound) outerBound) mean74
  have hh : (mulUp (mulUp (mulUp (mulUp fixedBound groundBound) ftsBound) outerBound) mean74:ℝ)<2*(scale:ℝ) := by
    exact_mod_cast full_moment_checked
  calc
    _ ≤ ((mulUp fixedBound groundBound:ℝ)/scale)*((ftsBound:ℝ)/scale)*((outerBound:ℝ)/scale)*((mean74:ℝ)/scale) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (nn ftsBound)) (nn outerBound)) (nn mean74)
    _ ≤ ((mulUp (mulUp fixedBound groundBound) ftsBound:ℝ)/scale)*((outerBound:ℝ)/scale)*((mean74:ℝ)/scale) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (nn outerBound)) (nn mean74)
    _ ≤ ((mulUp (mulUp (mulUp fixedBound groundBound) ftsBound) outerBound:ℝ)/scale)*((mean74:ℝ)/scale) := mul_le_mul_of_nonneg_right h3 (nn mean74)
    _ ≤ (mulUp (mulUp (mulUp (mulUp fixedBound groundBound) ftsBound) outerBound) mean74:ℝ)/scale := h4
    _ ≤ 2 := (div_le_iff₀ hs).mpr hh.le
#print axioms envelope_ratio_le_two
#print axioms full_moment_checked
end OuterGroundNumerics
