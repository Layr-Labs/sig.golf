import SigGolfCandidate.Merge044
set_option debug.skipKernelTC false
namespace ClaudeWCT.Numerics.TopRoute
open CanonicalCompression hiding topChoiceFree topHighW topCounts topAcceptedHistogram
open TopZero
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
set_option Elab.async false
def initial72 : Nat := 367005657474986467815470743115839911649
def initial73 : Nat := 367318666652001138259236047368320093699
def initial74 : Nat := 367683102476305508059439482870983051730
def initialFor (pool : Nat) : Nat := if pool = 72 then initial72 else if pool = 73 then initial73 else initial74
def topFloorFor (pool : Nat) : Nat := max 16 (pool - 56)
theorem initial_checked (pool : Nat) (hlo : 72 ≤ pool) (hhi : pool ≤ 74) :
    recurrenceCheck topDen topAcceptedHistogram (topFloorFor pool) pool rowOne (initialFor pool) = true := by
  interval_cases pool <;> decide +kernel
def meanInitial : Nat := 367331523313823563098345580180865787695
theorem mean_checked : initial72 + 2 * initial73 + initial74 ≤ 4 * meanInitial := by decide +kernel
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

end ClaudeWCT.Numerics.TopRoute
#print axioms ClaudeWCT.Numerics.TopRoute.initial_checked
#print axioms ClaudeWCT.Numerics.TopRoute.mean_checked
