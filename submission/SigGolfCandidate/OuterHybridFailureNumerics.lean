import SigGolfCandidate.OuterHybridForestComplete
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace OuterHybridFailureNumerics
open ENNReal OuterHybridForestComplete
open ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete

theorem eps_eq : eps=ENNReal.ofReal (1/(2:ℝ)^186) := by
  unfold eps
  rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_one,ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat,one_div]
theorem cF_le_eps : cF≤eps := by
  rw [eps_eq]
  unfold cF
  apply ENNReal.ofReal_le_ofReal
  norm_num

theorem forestFailure_le : forestFailure≤226*eps := by
  unfold forestFailure
  calc
    216*cF+10*eps≤216*eps+10*eps := add_le_add (mul_le_mul' le_rfl cF_le_eps) le_rfl
    _=226*eps := by ring

theorem global_sum_le : ((2^31:Nat):ENNReal)*forestFailure≤ENNReal.ofReal (1/(2:ℝ)^146) := by
  refine (mul_le_mul' le_rfl forestFailure_le).trans ?_
  rw [eps_eq]
  have he : ((2^31:Nat):ENNReal)*(226*ENNReal.ofReal (1/(2:ℝ)^186))=
      ENNReal.ofReal (((2^31:Nat):ℝ)*(226*(1/(2:ℝ)^186))) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤226),
      ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  norm_num
#print axioms global_sum_le
end OuterHybridFailureNumerics
