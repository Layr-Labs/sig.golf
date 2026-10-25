import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_ExpandExcess
import SigGolfCandidate.ClaudeWCT_Numerics_V6Budgets

/-! # N2b wired (certificate by the r3k numerics porter, `ClaudeWCT.Numerics.V6Budgets.expand_excess_numeric`). -/

namespace ClaudeWCT.Numerics.V6Budgets
open CanonicalCompression Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! N2b with slack (r3-lean-topbytes copy of r3k's certificate proof, final constant 19/10; the kernel check
`expand_block_checked` gives < 1.81213). The slack absorbs the cap-exhaustion term of the expand excess. -/
theorem expand_excess_moment19 (w : ℝ) (hw1 : 1 ≤ w) (hw : w ≤ (expandWNum:ℝ)/expandWDen) :
    w^427665 * ((1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)) ≤ 19 / 10 := by
  have hwf := hw.trans expandW_fix
  have hw0 : 0 ≤ w := by linarith
  set v : ℝ := w^8192 with hv
  -- blocks: w^max a b ≤ v^(max (a/L) (b/L) + 1)
  have hpt : ∀ a b : ℕ, w^(max a b) ≤ v^(max (a/8192) (b/8192) + 1) := by
    intro a b
    rw [hv, ← pow_mul]
    exact pow_le_pow_right₀ hw1 (max_block_le a b 8192 (by norm_num))
  have hR : (2:ℕ)^19 = 64 * 8192 := by norm_num
  have hsum : ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b) ≤
      (8192:ℝ) * (8192 * ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)) := by
    calc ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)
        ≤ ∑ a ∈ range (64*8192), ∑ b ∈ range (64*8192), v^(max (a/8192) (b/8192) + 1) := by
          rw [hR]; exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
      _ = (8192:ℝ) * ∑ i ∈ range 64, ∑ b ∈ range (64*8192), v^(max i (b/8192) + 1) :=
          sum_range_mul_div (fun i => ∑ b ∈ range (64*8192), v^(max i (b/8192) + 1)) 64 8192 (by norm_num)
      _ = (8192:ℝ) * (8192 * ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)) := by
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ =>
            sum_range_mul_div (fun j => v^(max i j + 1)) 64 8192 (by norm_num)
  -- fixed point: v ≤ blockV/scale, v^k ≤ pw k/scale
  have hvb : v ≤ (blockV:ℝ)/scale := by
    rw [hv]
    rw [blockV_eq]
    exact (pow_le_pow_left₀ hw0 hwf 8192).trans (powerUp_ratio_ge _ _)
  have hv0 : 0 ≤ v := by positivity
  have hterm : ∀ i j : ℕ, v^(max i j + 1) ≤ (pw (max i j + 1):ℝ)/scale := fun i j =>
    (pow_le_pow_left₀ hv0 hvb _).trans (pw_ratio_ge _)
  have hblock : ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1) ≤ (blockSum:ℝ)/scale := by
    calc ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)
        ≤ ∑ i ∈ range 64, ∑ j ∈ range 64, (pw (max i j + 1):ℝ)/scale :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = (blockSum:ℝ)/scale := by
          simp only [blockSum, Nat.cast_sum, Finset.sum_div]
  have hK : w^427665 ≤ (powerUp expandWFix 427665:ℝ)/scale :=
    (pow_le_pow_left₀ hw0 hwf _).trans (powerUp_ratio_ge _ _)
  have hcheck : (mulUp (powerUp expandWFix 427665) blockSum:ℝ) * 100000 <
      181213 * (scale:ℝ) * 4096 := by exact_mod_cast expand_block_checked
  have hmul := mulUp_ratio_ge (powerUp expandWFix 427665) blockSum
  have hs : (0:ℝ) < scale := by norm_num [scale]
  have hS : (1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b) ≤
      ((blockSum:ℝ)/scale) / 4096 := by
    have h2 : (1:ℝ)/2^38 * ((8192:ℝ) * (8192 * ((blockSum:ℝ)/scale))) = ((blockSum:ℝ)/scale) / 4096 := by
      generalize ((blockSum:ℝ)/scale) = B
      norm_num; ring
    rw [← h2]
    have h3 : (8192:ℝ) * (8192 * ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)) ≤
        (8192:ℝ) * (8192 * ((blockSum:ℝ)/scale)) := by
      gcongr
    have h4 := hsum.trans h3
    have h5 : (0:ℝ) ≤ 1/2^38 := by positivity
    exact mul_le_mul_of_nonneg_left h4 h5
  have hB : w^427665 * ((1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)) ≤
      ((powerUp expandWFix 427665:ℝ)/scale) * (((blockSum:ℝ)/scale) / 4096) :=
    mul_le_mul hK hS
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => pow_nonneg hw0 _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hC : ((powerUp expandWFix 427665:ℝ)/scale) * (((blockSum:ℝ)/scale) / 4096) ≤
      ((mulUp (powerUp expandWFix 427665) blockSum:ℝ)/scale) / 4096 := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hmul (by norm_num)
  have hD : ((mulUp (powerUp expandWFix 427665) blockSum:ℝ)/scale) / 4096 ≤ 19 / 10 := by
    have hs0 : (0:ℝ) < scale := by norm_num [scale]
    generalize (mulUp (powerUp expandWFix 427665) blockSum:ℝ) = P at hcheck ⊢
    generalize (scale:ℝ) = S at hcheck hs0 ⊢
    rw [div_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith


theorem expand_excess_numeric19 :
    avgF19 (fun c2 => avgF19 (fun c3 => excessWeightV6 (max c2 c3))) ≤ ENNReal.ofReal (19 / 10) := by
  set w : ℝ := (2:ℝ)^(1/((917504:ℕ):ℝ)) with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow (by norm_num) (by positivity)
  have hw0 : 0 ≤ w := by linarith
  have hin : ∀ c2, avgF19 (fun c3 => excessWeightV6 (max c2 c3)) =
      ENNReal.ofReal (∑ c3 ∈ range (2^19), (1/2^19) * w^(427665 + max c2 c3)) := by
    intro c2
    simp_rw [excessWeightV6_eq]
    exact avgF19_ofReal (fun c3 => w^(427665 + max c2 c3)) (fun _ => pow_nonneg hw0 _)
  simp_rw [hin]
  rw [avgF19_ofReal _ (fun _ => Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (pow_nonneg hw0 _))]
  have hreal : ∑ c2 ∈ range (2^19), (1/2^19) * ∑ c3 ∈ range (2^19), (1/2^19) * w^(427665 + max c2 c3) =
      w^427665 * ((1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)) := by
    simp only [pow_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hreal]
  have h := expand_excess_moment19 w hw1 (by rw [hw]; exact expand_w_le)
  exact ENNReal.ofReal_le_ofReal h

end ClaudeWCT.Numerics.V6Budgets

namespace SigGolfCandidate.Research.SharedExpansionV6
open ClaudeWCT.W9.T3.TopMoment
open Finset

/-! Campaign T51: the brute-forced sibling field has 16 bits (`TopMoment.avgF` over `2^16`), so the expand excess
numeric is a monotone bound: every field value is at most `2^16 - 1`, and
`2^((8/7)(427665 + 65535)/2^20) ≤ 1.9` (kernel power check). -/
theorem avgF_le_of (φ : Nat → ENNReal) (B : ENNReal) (h : ∀ c, c < 2 ^ 16 → φ c ≤ B) : avgF φ ≤ B := by
  unfold avgF
  calc ∑ c ∈ range (2 ^ 16), ((2 : ENNReal) ^ 16)⁻¹ * φ c ≤ ∑ _c ∈ range (2 ^ 16), ((2 : ENNReal) ^ 16)⁻¹ * B :=
        Finset.sum_le_sum fun c hc => mul_le_mul' le_rfl (h c (mem_range.mp hc))
    _ = B := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul, ← mul_assoc, Nat.cast_pow, Nat.cast_ofNat,
          ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

theorem expand_field_power_checked :
    ClaudeWCT.Numerics.CanonicalCompression.powerUp ClaudeWCT.Numerics.V6Budgets.expandWFix (427665 + 65535) * 10 ≤
      19 * ClaudeWCT.Numerics.CanonicalCompression.scale := by
  decide +kernel

theorem excessWeight_field_max : excessWeight 65535 ≤ ENNReal.ofReal (19 / 10) := by
  have he : excessWeight 65535 = ClaudeWCT.Numerics.V6Budgets.excessWeightV6 65535 := by
    unfold excessWeight ClaudeWCT.Numerics.V6Budgets.excessWeightV6 SigGolfCandidate.Research.SharedForest.expandReplayExtra
    norm_num
  rw [he, ClaudeWCT.Numerics.V6Budgets.excessWeightV6_eq]
  apply ENNReal.ofReal_le_ofReal
  have hw := ClaudeWCT.Numerics.V6Budgets.expand_w_le.trans ClaudeWCT.Numerics.V6Budgets.expandW_fix
  have hw0 : (0 : ℝ) ≤ (2:ℝ)^(1/((917504:ℕ):ℝ)) := by positivity
  have hp := ClaudeWCT.Numerics.CanonicalCompression.powerUp_ratio_ge ClaudeWCT.Numerics.V6Budgets.expandWFix
    (427665 + 65535)
  have hc := expand_field_power_checked
  have hs0 : (0 : ℝ) < ClaudeWCT.Numerics.CanonicalCompression.scale := by
    norm_num [ClaudeWCT.Numerics.CanonicalCompression.scale]
  have hc' : (ClaudeWCT.Numerics.CanonicalCompression.powerUp ClaudeWCT.Numerics.V6Budgets.expandWFix
      (427665 + 65535) : ℝ) * 10 ≤ 19 * (ClaudeWCT.Numerics.CanonicalCompression.scale : ℝ) := by exact_mod_cast hc
  calc ((2:ℝ)^(1/((917504:ℕ):ℝ)))^(427665 + 65535)
      ≤ ((ClaudeWCT.Numerics.V6Budgets.expandWFix : ℝ) / ClaudeWCT.Numerics.CanonicalCompression.scale) ^
          (427665 + 65535) := pow_le_pow_left₀ hw0 hw _
    _ ≤ (ClaudeWCT.Numerics.CanonicalCompression.powerUp ClaudeWCT.Numerics.V6Budgets.expandWFix
          (427665 + 65535) : ℝ) / ClaudeWCT.Numerics.CanonicalCompression.scale := hp
    _ ≤ 19 / 10 := by
        rw [div_le_iff₀ hs0]; linarith

/-- N2b with slack: `E_{c₂,c₃}[2^((8/7)(K + max c₂ c₃)/2^20)] ≤ 1.9`. -/
def ExpandExcessNumeric19 : Prop :=
  avgF (fun c2 => avgF (fun c3 => excessWeight (max c2 c3))) ≤ ENNReal.ofReal (19 / 10)

theorem expandExcessNumeric19_holds : ExpandExcessNumeric19 := by
  unfold ExpandExcessNumeric19
  apply avgF_le_of; intro c2 hc2
  apply avgF_le_of; intro c3 hc3
  exact (excessWeight_mono (by omega : max c2 c3 ≤ 65535)).trans excessWeight_field_max

theorem expandExcessNumeric_holds : ExpandExcessNumeric :=
  expandExcessNumeric19_holds.trans (by
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num]
    exact ENNReal.ofReal_le_ofReal (by norm_num))

end SigGolfCandidate.Research.SharedExpansionV6
