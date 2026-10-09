import SigGolfCandidate.ClaudeR3.F2

namespace ClaudeR3.Final
open Finset ENNReal
open ClaudeWCT.Numerics.N600 (uniformOn priceN nearPriceN nearLoad priceScale priceScale_mul priceScale_sq_mul
  priceScale_ne_top priceN_ne_top card_index Q A theta_excess_le_square_v5 theta_excess_le_square_54 near_le_sub)
open ClaudeWCT.Numerics.Law (lawAvg marked lawAvg_mul_left lawAvg_sum law_marked_atIndex lawAvg_mono lawAvg_const
  lawAvg_add lawAvg_sum_square_le law_marked_negative_correlation marked_sum_one)
open ClaudeWCT.Numerics.Thinning (env env_le_one env_cons_le nearEnv nearEnv_le_one)
open SphincsSecurity.Concrete (binomialAverage binomialAverage_mul_left)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open ClaudeWCT.Numerics.PoissonReflect (rejection_window_sharp rate_le_one)
open ClaudeWCT.WCT9 (wordDigit Child Rank)
open ClaudeR3.Asm (J779)
open ClaudeR3.PoissonJ (poissonCheckJ poissonCheckJ_sound)

def nearJCheck : Bool := poissonCheckJ J779 13533529 100000000 2 1 fNear (54 * Q ^ 9) (54 * A) 1 259 1 80
def diagJCheck : Bool :=
  poissonCheckJ J779 13533529 100000000 2 1 fDiag (Q ^ 18) (A ^ 2) (2 ^ 31) 3417 1000000 80

theorem meanJ_ok : meanJCheck = true := by decide +kernel
theorem nearJ_ok : nearJCheck = true := by decide +kernel
theorem diagJ_ok : diagJCheck = true := by decide +kernel

theorem lam_window {T : ℕ} (hT2 : T ≤ 2 ^ 32) :
    (T : ENNReal) * (2 ^ 31 : ENNReal)⁻¹ * 1 ≤ ((2 : ℕ) : ENNReal) / ((1 : ℕ) : ENNReal) := by
  rw [mul_one, Nat.cast_one, div_one]
  calc (T : ENNReal) * (2 ^ 31 : ENNReal)⁻¹ ≤ (2 ^ 32 : ENNReal) * (2 ^ 31 : ENNReal)⁻¹ := by
        gcongr; exact_mod_cast hT2
    _ = 2 := by
        rw [show (2 ^ 32 : ENNReal) = 2 * 2 ^ 31 by norm_num, mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    _ = ((2 : ℕ) : ENNReal) := by norm_num

theorem honest_marked_sum_one : ∑ p, marked (α := Fin (2 ^ 31)) honest779 p = 1 :=
  marked_sum_one honest779 honest_sum_one

theorem diag_pay_one (r : ℕ) : lawAvg honest779 r (fun L => env (n := 9) (C := Child) wordDigit L ^ 2) ≤ 1 :=
  (lawAvg_mono honest779 r fun L => pow_le_one₀ zero_le (env_le_one wordDigit L)).trans_eq
    (lawAvg_const honest779 honest_sum_one r 1)

theorem near_pay_one (r : ℕ) : nearLoad wordDigit (vc := honest779) (C := Child) r ≤ 1 := by
  unfold nearLoad
  calc (54 : ENNReal)⁻¹ * ∑ k : Fin 9, ∑ t : Fin 6, lawAvg honest779 r (nearEnv (C := Child) wordDigit k t)
      ≤ (54 : ENNReal)⁻¹ * ∑ _k : Fin 9, ∑ _t : Fin 6, (1 : ENNReal) :=
        mul_le_mul' le_rfl (sum_le_sum fun k _ => sum_le_sum fun t _ =>
          (lawAvg_mono honest779 r (nearEnv_le_one wordDigit k t)).trans_eq (lawAvg_const honest779 honest_sum_one r 1))
    _ = 1 := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        rw [show ((9 : ℕ) : ENNReal) * (6 : ℕ) = 54 by norm_num, ENNReal.inv_mul_cancel (by simp) (by simp)]

section Window
variable [SampleableType Coords] {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32)
include hT1 hT2

theorem cap_mean_le : lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (priceN wordDigit) ≤ 602 / 1000 := by
  rw [price_mean_eq]
  have h := poissonCheckJ_sound (Dv := J779) (f := fMean) (dbase := Q ^ 9) (sn := A) (sd := 1) (Mn := 602) (Md := 1000)
    meanJ_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rate_le_one 1 le_rfl
    (lam_window hT2) (rejection_window_sharp T hT1) _ (fun r _ => mean_pay r) (fun r _ => mean_pay_one r)
  simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using h

theorem cap_diag_eq :
    priceScale ^ 2 * ∑ index : Fin (2 ^ 31), lawAvg (marked (α := Fin (2 ^ 31)) honest779) T
        (fun W => env (n := 9) (C := Child) wordDigit (atIndex index W) ^ 2) =
      (A : ENNReal) ^ 2 / 2 ^ 31 * binomialAverage (2 ^ 31 : ENNReal)⁻¹ T
        (fun r => lawAvg honest779 r (fun L => env (n := 9) (C := Child) wordDigit L ^ 2)) := by
  simp_rw [law_marked_atIndex honest779 honest_sum_one _ T (fun L => env (n := 9) (C := Child) wordDigit L ^ 2),
    card_index]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← priceScale_sq_mul]

theorem cap_second_le :
    lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (fun W => priceN wordDigit W ^ 2) ≤
      lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (priceN wordDigit) ^ 2 + 3417 / 1000000 := by
  set M := marked (α := Fin (2 ^ 31)) honest779
  have hsq := lawAvg_sum_square_le M T (fun index W => env (n := 9) (C := Child) wordDigit (atIndex index W))
    (fun first second hne => law_marked_negative_correlation honest779 honest_sum_one first second hne T _ _
      (env_cons_le wordDigit) (env_cons_le wordDigit))
  have hmean : lawAvg M T (priceN wordDigit) =
      priceScale * ∑ index : Fin (2 ^ 31), lawAvg M T (fun W => env (n := 9) (C := Child) wordDigit (atIndex index W)) := by
    unfold priceN; rw [lawAvg_mul_left, lawAvg_sum]
  have hcheck := poissonCheckJ_sound (Dv := J779) (f := fDiag) (dbase := Q ^ 18) (sn := A ^ 2) (sd := 2 ^ 31)
    (Mn := 3417) (Md := 1000000) diagJ_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rate_le_one 1 le_rfl (lam_window hT2) (rejection_window_sharp T hT1) _ (fun r _ => diag_pay r)
    (fun r _ => diag_pay_one r)
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hcheck
  calc lawAvg M T (fun W => priceN wordDigit W ^ 2)
      = priceScale ^ 2 * lawAvg M T (fun W => (∑ index : Fin (2 ^ 31),
          env (n := 9) (C := Child) wordDigit (atIndex index W)) ^ 2) := by
        unfold priceN; simp_rw [mul_pow]; rw [lawAvg_mul_left]
    _ ≤ priceScale ^ 2 * ((∑ index : Fin (2 ^ 31), lawAvg M T (fun W => env (n := 9) (C := Child) wordDigit
          (atIndex index W))) ^ 2 + ∑ index : Fin (2 ^ 31), lawAvg M T (fun W => env (n := 9) (C := Child) wordDigit
          (atIndex index W) ^ 2)) :=
        mul_le_mul' le_rfl hsq
    _ = lawAvg M T (priceN wordDigit) ^ 2 + priceScale ^ 2 *
          ∑ index : Fin (2 ^ 31), lawAvg M T (fun W => env (n := 9) (C := Child) wordDigit (atIndex index W) ^ 2) := by
        rw [hmean]; ring
    _ ≤ _ := by
        rw [cap_diag_eq hT1 hT2]
        exact add_le_add le_rfl hcheck

theorem cap_excess_le :
    lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (fun W => priceN wordDigit W - 1023 / 1024) ≤ 2933 / 1000000 := by
  set M := marked (α := Fin (2 ^ 31)) honest779
  have hmean := cap_mean_le hT1 hT2
  have hsecond := cap_second_le hT1 hT2
  set mean := lawAvg M T (priceN wordDigit)
  have h := lawAvg_mono M T (fun W : List (Fin (2 ^ 31) × Coords) =>
    theta_excess_le_square_v5 (priceN wordDigit W) mean (priceN_ne_top wordDigit W) hmean)
  rw [lawAvg_add, lawAvg_add, lawAvg_mul_left, lawAvg_mul_left, lawAvg_const M honest_marked_sum_one T] at h
  have hcancel : (1588 / 1000 : ENNReal) * lawAvg M T (fun W => priceN wordDigit W - 1023 / 1024) ≤ 3417 / 1000000 := by
    have hmt : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
    apply ENNReal.le_of_add_le_add_right (a := 2 * mean ^ 2) (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hmt))
    calc
      _ = (1588 / 1000 : ENNReal) * lawAvg M T (fun W => priceN wordDigit W - 1023 / 1024) + 2 * mean * mean := by ring
      _ ≤ lawAvg M T (fun W => priceN wordDigit W ^ 2) + mean ^ 2 := h
      _ ≤ (mean ^ 2 + 3417 / 1000000) + mean ^ 2 := add_le_add hsecond le_rfl
      _ = _ := by ring
  have hi : (1000 / 1588 : ENNReal) * (1588 / 1000) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  calc
    _ = (1000 / 1588 : ENNReal) * ((1588 / 1000) * lawAvg M T (fun W => priceN wordDigit W - 1023 / 1024)) := by
        rw [← mul_assoc, hi, one_mul]
    _ ≤ (1000 / 1588 : ENNReal) * (3417 / 1000000) := mul_le_mul' le_rfl hcancel
    _ ≤ _ := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

theorem cap_excess_le_54 :
    lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (fun W => priceN wordDigit W - 2031 / 1024) ≤ 6186 / 10000000 := by
  set M := marked (α := Fin (2 ^ 31)) honest779
  have hmean := cap_mean_le hT1 hT2
  have hsecond := cap_second_le hT1 hT2
  set mean := lawAvg M T (priceN wordDigit)
  have h := lawAvg_mono M T (fun W : List (Fin (2 ^ 31) × Coords) =>
    theta_excess_le_square_54 (priceN wordDigit W) mean (priceN_ne_top wordDigit W) hmean)
  rw [lawAvg_add, lawAvg_add, lawAvg_mul_left, lawAvg_mul_left, lawAvg_const M honest_marked_sum_one T] at h
  have hcancel : (5524 / 1000 : ENNReal) * lawAvg M T (fun W => priceN wordDigit W - 2031 / 1024) ≤ 3417 / 1000000 := by
    have hmt : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
    apply ENNReal.le_of_add_le_add_right (a := 2 * mean ^ 2) (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hmt))
    calc
      _ = (5524 / 1000 : ENNReal) * lawAvg M T (fun W => priceN wordDigit W - 2031 / 1024) + 2 * mean * mean := by ring
      _ ≤ lawAvg M T (fun W => priceN wordDigit W ^ 2) + mean ^ 2 := h
      _ ≤ (mean ^ 2 + 3417 / 1000000) + mean ^ 2 := add_le_add hsecond le_rfl
      _ = _ := by ring
  have hi : (1000 / 5524 : ENNReal) * (5524 / 1000) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  calc
    _ = (1000 / 5524 : ENNReal) * ((5524 / 1000) * lawAvg M T (fun W => priceN wordDigit W - 2031 / 1024)) := by
        rw [← mul_assoc, hi, one_mul]
    _ ≤ (1000 / 5524 : ENNReal) * (3417 / 1000000) := mul_le_mul' le_rfl hcancel
    _ ≤ _ := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

theorem cap_nearPrice_eq :
    lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (nearPriceN wordDigit) =
      54 * (A : ENNReal) * binomialAverage (2 ^ 31 : ENNReal)⁻¹ T (nearLoad wordDigit (vc := honest779) (C := Child)) := by
  unfold nearPriceN nearLoad
  rw [lawAvg_mul_left, lawAvg_sum]
  simp_rw [lawAvg_sum, law_marked_atIndex honest779 honest_sum_one, card_index]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← priceScale_mul,
    binomialAverage_mul_left]
  simp_rw [← SphincsSecurity.Concrete.binomialAverage_sum]
  have h : (54 : ENNReal) * 54⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [← mul_assoc, show (54 : ENNReal) * (priceScale * ((2 ^ 31 : ℕ) : ENNReal)) * 54⁻¹ =
    (54 * 54⁻¹) * (priceScale * ((2 ^ 31 : ℕ) : ENNReal)) by ring, h, one_mul]

theorem cap_near_le : lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (nearPriceN wordDigit) ≤ 300 - 1 / 16 := by
  rw [cap_nearPrice_eq hT1 hT2]
  have h := poissonCheckJ_sound (Dv := J779) (f := fNear) (dbase := 54 * Q ^ 9) (sn := 54 * A) (sd := 1) (Mn := 259)
    (Md := 1) nearJ_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rate_le_one 1 le_rfl
    (lam_window hT2) (rejection_window_sharp T hT1) _ (fun r _ => near_pay r) (fun r _ => near_pay_one r)
  simp only [Nat.cast_one, div_one, Nat.cast_ofNat, Nat.cast_mul] at h
  exact h.trans (by simpa only [div_one] using near_le_sub)

end Window

end ClaudeR3.Final
