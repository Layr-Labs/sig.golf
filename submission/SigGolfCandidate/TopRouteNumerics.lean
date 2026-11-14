import SigGolfCandidate.Merge044
set_option debug.skipKernelTC false
namespace ClaudeWCT.Numerics.TopRoute
open CanonicalCompression hiding topChoiceFree topHighW topCounts topAcceptedHistogram
open TopZero
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
set_option Elab.async false
def initial71 : Nat := 366715107545796050819992259851601894746
def initial72 : Nat := 366942643904593431787406997148413147551
def initial73 : Nat := 367292559183542624456206104990048416928
def initialFor (pool : Nat) : Nat := if pool = 71 then initial71 else if pool = 72 then initial72 else initial73
def topFloorFor (pool : Nat) : Nat := max 18 (pool - 54)
theorem initial_checked (pool : Nat) (hlo : 71 ≤ pool) (hhi : pool ≤ 73) :
    recurrenceCheck topDen topAcceptedHistogram (topFloorFor pool) pool rowOne (initialFor pool) = true := by
  interval_cases pool <;> decide +kernel
def meanInitial : Nat := 366973238634631384712753089784619151694
theorem mean_checked : initial71 + 2 * initial72 + initial73 ≤ 4 * meanInitial := by decide +kernel
theorem full_moment_checked :
    mulUp (mulUp (mulUp fixedBoundU16 groundBound) ftsBound) meanInitial * 100000 < 200000 * scale := by
  decide +kernel
theorem envelope_from_integer (F I X : Nat) (hX : X ≤ 200000)
    (hn : mulUp (mulUp F ftsBound) I * 100000 < X * scale) :
    ((F:ℝ)/scale)*(((ftsBound:ℝ)/scale)*((I:ℝ)/scale))≤2 := by
  have hs : (0:ℝ)<scale := by norm_num [scale]
  have hmul2 := mulUp_ratio_ge (mulUp F ftsBound) I
  have hnum : (mulUp (mulUp F ftsBound) I:ℝ)/scale<X/100000 := by
    have hreal : (mulUp (mulUp F ftsBound) I:ℝ)*100000<X*(scale:ℝ) := by exact_mod_cast hn
    apply (div_lt_iff₀ hs).mpr
    nlinarith
  have hX' : (X:ℝ)/100000 ≤ 2 := by
    have : (X:ℝ) ≤ 200000 := by exact_mod_cast hX
    rw [div_le_iff₀ (by norm_num)]
    linarith
  calc
    _ = (((F:ℝ)/scale)*((ftsBound:ℝ)/scale))*((I:ℝ)/scale) := by ring
    _ ≤ ((mulUp F ftsBound:ℝ)/scale)*((I:ℝ)/scale) := by
        gcongr
        exact mulUp_ratio_ge F ftsBound
    _ ≤ _ := hmul2
    _ ≤ 2 := hnum.le.trans hX'

theorem envelope_ratio_le_two :
    (((fixedBoundU16 : ℝ) / scale) * ((groundBound : ℝ) / scale)) *
      (((ftsBound : ℝ) / scale) * ((meanInitial : ℝ) / scale)) ≤ 2 := by
  have hm := mulUp_ratio_ge fixedBoundU16 groundBound
  have he := envelope_from_integer (mulUp fixedBoundU16 groundBound) meanInitial 200000 (by norm_num) full_moment_checked
  have h0 : (0 : ℝ) ≤ ((ftsBound : ℝ) / scale) * ((meanInitial : ℝ) / scale) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact (mul_le_mul_of_nonneg_right hm h0).trans he

end ClaudeWCT.Numerics.TopRoute
#print axioms ClaudeWCT.Numerics.TopRoute.initial_checked
#print axioms ClaudeWCT.Numerics.TopRoute.mean_checked
#print axioms ClaudeWCT.Numerics.TopRoute.full_moment_checked
#print axioms ClaudeWCT.Numerics.TopRoute.envelope_ratio_le_two
