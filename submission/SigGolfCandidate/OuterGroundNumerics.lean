import SigGolfCandidate.LocalRouteMoment
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
namespace OuterGroundNumerics
open ClaudeWCT.Numerics.CanonicalCompression ClaudeWCT.Numerics.TopZero
def initial72_0 : Nat := 366951251504075224751912023362707978338
theorem check72_0 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 18 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_0 initial72_0=true := by decide +kernel
def initial72_1 : Nat := 366728123593525518492926223643650145891
theorem check72_1 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 18 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_1 initial72_1=true := by decide +kernel
def initial72_2 : Nat := 366727632637969870185166323090096698620
theorem check72_2 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 18 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_2 initial72_2=true := by decide +kernel
def initial72_3 : Nat := 366547643706864023960383846543413861809
theorem check72_3 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 18 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_3 initial72_3=true := by decide +kernel
def initial72_4 : Nat := 366722958083101108281834699089371746485
theorem check72_4 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 18 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_4 initial72_4=true := by decide +kernel
def initial72_5 : Nat := 366536943957432662635026909489834939254
theorem check72_5 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 18 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_5 initial72_5=true := by decide +kernel
def initial72_6 : Nat := 366536606419227368398955940851689916118
theorem check72_6 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 18 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_6 initial72_6=true := by decide +kernel
def initial72_7 : Nat := 366387930847206515587762658713293379029
theorem check72_7 : recurrenceCheck topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 18 72 ClaudeWCT.Numerics.LocalRoute.Tables.row1_7 initial72_7=true := by decide +kernel
def mean74 : Nat := 366865161303095426883041867615347432304
theorem mean_checked : 1*initial72_0+1*initial72_1+1*initial72_2+1*initial72_3+1*initial72_4+1*initial72_5+1*initial72_6+1*initial72_7+2*ClaudeWCT.Numerics.LocalRoute.Tables.initial73_0+2*ClaudeWCT.Numerics.LocalRoute.Tables.initial73_1+2*ClaudeWCT.Numerics.LocalRoute.Tables.initial73_2+2*ClaudeWCT.Numerics.LocalRoute.Tables.initial73_3+2*ClaudeWCT.Numerics.LocalRoute.Tables.initial73_4+2*ClaudeWCT.Numerics.LocalRoute.Tables.initial73_5+2*ClaudeWCT.Numerics.LocalRoute.Tables.initial73_6+2*ClaudeWCT.Numerics.LocalRoute.Tables.initial73_7+1*ClaudeWCT.Numerics.LocalRoute.Tables.initial74_0+1*ClaudeWCT.Numerics.LocalRoute.Tables.initial74_1+1*ClaudeWCT.Numerics.LocalRoute.Tables.initial74_2+1*ClaudeWCT.Numerics.LocalRoute.Tables.initial74_3+1*ClaudeWCT.Numerics.LocalRoute.Tables.initial74_4+1*ClaudeWCT.Numerics.LocalRoute.Tables.initial74_5+1*ClaudeWCT.Numerics.LocalRoute.Tables.initial74_6+1*ClaudeWCT.Numerics.LocalRoute.Tables.initial74_7≤32*mean74 := by decide +kernel
def fixedCost : Nat := 111997
def fixedBound : Nat := powerUp (ceilDiv (zNum*scale) zDen) fixedCost
def outerBound : Nat := mulUp (powerUp (groundM 3) 8) (powerUp (groundM 4) 2)
theorem outer_checked : outerBound=340455168899374582504977570063757275322 := by decide +kernel
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
