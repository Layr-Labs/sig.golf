import SigGolfCandidate.Merge054
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterExpandSlack
open scoped ENNReal

theorem factor_real : (2:ℝ)^(3/224:ℝ)≤65/64 := by
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (by norm_num) _) (by norm_num) (by norm_num : (0:ℝ)<224)).mp
  rw [←Real.rpow_mul (by norm_num),show (3/224:ℝ)*224=3 from by norm_num]
  norm_num [←Real.rpow_natCast]

open ClaudeWCT.W9.T3.TopMoment SigGolfCandidate.Research.SharedExpansionV6

noncomputable def extraWeight (c : Nat) : ℝ≥0∞ :=
  (2:ℝ≥0∞)^((8/7:ℝ)*((SigGolfCandidate.Research.SharedForest.expandReplayExtra+12288+c:Nat):ℝ)/1048576)

theorem extraWeight_eq (c : Nat) : extraWeight c=(2:ℝ≥0∞)^(3/224:ℝ)*excessWeight c := by
  unfold extraWeight excessWeight
  rw [←ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
  congr 1
  push_cast
  ring

theorem factor_le : (2:ℝ≥0∞)^(3/224:ℝ)≤ENNReal.ofReal (65/64) := by
  rw [show (2:ℝ≥0∞)=ENNReal.ofReal (2:ℝ) from by norm_num,ENNReal.ofReal_rpow_of_pos (by norm_num)]
  exact ENNReal.ofReal_le_ofReal factor_real

theorem avgF_mul (c : ℝ≥0∞) (f : Nat→ℝ≥0∞) : avgF (fun n=>c*f n)=c*avgF f := by
  unfold avgF
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  change (2^20:ℝ≥0∞)⁻¹*(c*f n)=c*((2^20:ℝ≥0∞)⁻¹*f n)
  ac_rfl

theorem numeric_extra : avgF (fun c2=>avgF (fun c3=>extraWeight (max c2 c3)))≤ENNReal.ofReal (194/100) := by
  simp_rw [extraWeight_eq,avgF_mul]
  have hnum:=expandExcessNumeric19_holds
  unfold ExpandExcessNumeric19 at hnum
  calc
    _ ≤ ENNReal.ofReal (65/64)*ENNReal.ofReal (191/100) := mul_le_mul factor_le hnum bot_le bot_le
    _ ≤ ENNReal.ofReal (194/100) := by
      rw [←ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

#print axioms numeric_extra

#print axioms factor_real
end OuterExpandSlack
