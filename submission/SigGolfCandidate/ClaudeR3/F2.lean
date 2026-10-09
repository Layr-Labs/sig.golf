import SigGolfCandidate.ClaudeR3.F1
import SigGolfCandidate.ClaudeR3.R2
import SigGolfCandidate.ClaudeR3.R3

namespace ClaudeR3.Final
open Finset ENNReal
open ClaudeWCT.Numerics.N600 (uniformOn priceN nearPriceN nearLoad priceScale priceScale_mul card_index env_moment
  env_sq_moment nearEnv_moment xNum xfNum xfSum xfSum_eq yNum Nn Q A Kc card_table w1_table w2_table wf_table)
open ClaudeWCT.Numerics.Law (lawAvg marked lawAvg_mul_left lawAvg_sum lawAvg_le_uniform law_marked_atIndex
  lawAvg_mono lawAvg_const)
open ClaudeWCT.Numerics.Thinning (env env_le_one env_sq ListCov ListCovExcept nearEnv nearEnv_le_one)
open SphincsSecurity.Concrete (binomialAverage uniformWordAverage)
open ClaudeWCT.WCT9 (wordDigit Child Rank)
open ClaudeR3.Asm (capS J779 card_capS779 capS779_nonempty)
open ClaudeR3.BonfData

theorem w1T : ClaudeWCT.Numerics.N600.W1Table wordDigit :=
  fun p => w1_table ClaudeR3.Tab.wordsOf_wordDigit' (fun x j => ClaudeR3.Tab.wordDigit_le4 x j) p
theorem w2T : ClaudeWCT.Numerics.N600.W2Table wordDigit :=
  fun p => w2_table ClaudeR3.Tab.wordsOf_wordDigit' (fun x j => ClaudeR3.Tab.wordDigit_le4 x j) p
theorem wfT (i : Fin 6) : ClaudeWCT.Numerics.N600.WFTable wordDigit i :=
  fun p => wf_table ClaudeR3.Tab.wordsOf_wordDigit' (fun x j => ClaudeR3.Tab.wordDigit_le4 x j) i p

theorem near_check_all (r : ℕ) (h1 : 2 ≤ r) (h2 : r ≤ 20) : nearCheckR r = true := by
  interval_cases r
  exacts [near_r2, near_r3, near_r4, near_r5, near_r6, near_r7, near_r8, near_r9, near_r10, near_r11, near_r12, near_r13, near_r14, near_r15, near_r16, near_r17, near_r18, near_r19, near_r20]

theorem diag_check_all (r : ℕ) (h1 : 2 ≤ r) (h2 : r ≤ 20) : diagCheckR r = true := by
  interval_cases r
  exacts [diag_r2, diag_r3, diag_r4, diag_r5, diag_r6, diag_r7, diag_r8, diag_r9, diag_r10, diag_r11, diag_r12, diag_r13, diag_r14, diag_r15, diag_r16, diag_r17, diag_r18, diag_r19, diag_r20]

def fNear (r : ℕ) : ℕ := if 2 ≤ r ∧ r ≤ 20 then nearD.getD r 0 else 9 * 128 ^ 9 * (xNum r ^ 8 * xfSum r)
def fDiag (r : ℕ) : ℕ := if 2 ≤ r ∧ r ≤ 20 then diagD.getD r 0 else 128 ^ 9 * yNum r ^ 9

theorem rp_le (L : List ℕ) (k : ℕ) (h : ∀ r, 2 ≤ r → r ≤ 20 → L.getD r 0 ≤ r) (hk : k + 2 ≤ 20) :
    L.getD (k + 2) 0 ≤ k + 2 := h (k + 2) (by omega) hk

set_option maxRecDepth 10000 in
theorem nearRp_le : ∀ r, 2 ≤ r → r ≤ 20 → nearRp.getD r 0 ≤ r := by
  intro r h1 h2; interval_cases r <;> decide
set_option maxRecDepth 10000 in
theorem diagRp_le : ∀ r, 2 ≤ r → r ≤ 20 → diagRp.getD r 0 ≤ r := by
  intro r h1 h2; interval_cases r <;> decide

theorem density_conv (r X n c : ℕ) (hn : 0 < n) (hc : 0 < c) :
    kappa779 ^ r * ((X : ENNReal) / ((n * Q ^ (9 * r) : ℕ) : ENNReal)) =
      1 ^ r * (((c * X : ℕ) : ENNReal) / ((c * n * J779 ^ r : ℕ) : ENNReal)) := by
  unfold kappa779
  have hJ : (0 : ℝ) < J779 := by unfold J779; norm_num
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hQ : (0 : ℝ) < (Q : ℝ) := by unfold Q; norm_num
  apply (ENNReal.toReal_eq_toReal_iff' (by
      refine ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_)) ?_
      · unfold J779; simp
      · refine ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_
        have : 0 < n * Q ^ (9 * r) := by unfold Q; positivity
        exact_mod_cast this.ne')
    (by
      refine ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_)
      have : 0 < c * n * J779 ^ r := by unfold J779; positivity
      exact_mod_cast this.ne')).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, one_pow,
    one_mul]
  push_cast
  have hJ' : (J779 : ℝ) ≠ 0 := hJ.ne'
  rw [pow_mul, div_pow]
  field_simp
  try ring

section Pay
variable [SampleableType Coords]

theorem nearEnv_density (k : Fin 9) (t : Fin 6) (r : ℕ) :
    lawAvg honest779 r (nearEnv (C := Child) wordDigit k t) ≤
      kappa779 ^ r * (((xNum r ^ 8 * xfNum t r : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  rw [← nearEnv_moment wordDigit k t (Fintype.card_fin 563) (Fintype.card_fin 128) w1T (wfT t) r]
  exact lawAvg_le_uniform honest779 kappa779 honest_density r _

theorem nearLoad_density (r : ℕ) :
    nearLoad wordDigit (vc := honest779) (C := Child) r ≤
      kappa779 ^ r * (((xNum r ^ 8 * xfSum r : ℕ) : ENNReal) / ((6 * Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  unfold nearLoad
  set D : ENNReal := ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)
  calc (54 : ENNReal)⁻¹ * ∑ k : Fin 9, ∑ t : Fin 6, lawAvg honest779 r (nearEnv (C := Child) wordDigit k t)
      ≤ (54 : ENNReal)⁻¹ * ∑ _k : Fin 9, ∑ t : Fin 6, kappa779 ^ r * (((xNum r ^ 8 * xfNum t r : ℕ) : ENNReal) / D) :=
        mul_le_mul' le_rfl (sum_le_sum fun k _ => sum_le_sum fun t _ => nearEnv_density k t r)
    _ = kappa779 ^ r * (((xNum r ^ 8 * xfSum r : ℕ) : ENNReal) / (6 * D)) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
        have h63 : (54 : ENNReal)⁻¹ * ((9 : ℕ) : ENNReal) = 6⁻¹ := by
          rw [show (54 : ENNReal) = 9 * 6 by norm_num, ENNReal.mul_inv (by simp) (by simp), Nat.cast_ofNat,
            mul_comm (9 : ENNReal)⁻¹, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
        rw [h63, xfSum_eq, show xNum r ^ 8 * ∑ t : Fin 6, xfNum t r = ∑ t : Fin 6, xNum r ^ 8 * xfNum t r from
          Finset.mul_sum _ _ _, Nat.cast_sum]
        simp only [div_eq_mul_inv]
        rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine sum_congr rfl fun t _ => ?_
        ring
    _ = _ := by simp only [D]; push_cast; ring_nf

theorem near_pay (r : ℕ) :
    nearLoad wordDigit (vc := honest779) (C := Child) r ≤
      1 ^ r * ((fNear r : ENNReal) / ((54 * Q ^ 9 * J779 ^ r : ℕ) : ENNReal)) := by
  by_cases hr : 2 ≤ r ∧ r ≤ 20
  · obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    have hc := near_check_all (k + 2) hr.1 hr.2
    unfold nearCheckR at hc
    simp only [Bool.and_eq_true, Nat.ble_eq] at hc
    obtain ⟨hok, hle⟩ := hc
    simp only [Nat.add_sub_cancel] at hok hle
    have hb := ClaudeR3.Asm.near_bound k 104 (nearRp.getD (k + 2) 0) (2 ^ nearBB.getD (k + 2) 0) (by norm_num)
      (rp_le nearRp k nearRp_le hr.2) hok
    have hcount : ∀ (k₀ : Fin 9) (t : Fin 6), lawAvg honest779 (k + 2) (nearEnv (C := Child) wordDigit k₀ t) =
        (#{p : (Fin (k + 2) → Coords) × Coords | (∀ m, p.1 m ∈ capS 779) ∧
          ListCovExcept wordDigit k₀ t (List.ofFn p.1) p.2} : ENNReal) / ((J779 : ENNReal) ^ (k + 2) * ((Q ^ 9 : ℕ) : ENNReal)) := by
      intro k₀ t
      have h := ClaudeR3.Law.lawAvg_uniformOn_count (r := k + 2) (capS 779) (fun L t' => ListCovExcept wordDigit k₀ t L t')
      rw [card_capS779, card_coords] at h
      exact h
    unfold nearLoad
    simp_rw [hcount, div_eq_mul_inv, ← sum_mul, ← Nat.cast_sum]
    rw [one_pow, one_mul, fNear, if_pos hr]
    have e779 : capS (675 + 104) = capS 779 := rfl
    rw [e779] at hb
    have hX := hb.trans hle
    calc (54 : ENNReal)⁻¹ * (((∑ k₀ : Fin 9, ∑ t : Fin 6, #{p : (Fin (k + 2) → Coords) × Coords |
            (∀ m, p.1 m ∈ capS 779) ∧ ListCovExcept wordDigit k₀ t (List.ofFn p.1) p.2} : ℕ) : ENNReal) *
              ((J779 : ENNReal) ^ (k + 2) * ((Q ^ 9 : ℕ) : ENNReal))⁻¹)
        ≤ (54 : ENNReal)⁻¹ * (((nearD.getD (k + 2) 0 : ℕ) : ENNReal) *
              ((J779 : ENNReal) ^ (k + 2) * ((Q ^ 9 : ℕ) : ENNReal))⁻¹) := by
          gcongr
      _ = _ := by
          push_cast
          rw [mul_left_comm, ← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          congr 2
          ring
  · rw [fNear, if_neg hr]
    refine (nearLoad_density r).trans (le_of_eq ?_)
    rw [density_conv r _ (6 * Nn ^ 9) (9 * 128 ^ 9) (by norm_num [Nn]) (by norm_num)]
    congr 3

theorem diag_pay (r : ℕ) :
    lawAvg honest779 r (fun L => env (n := 9) (C := Child) wordDigit L ^ 2) ≤
      1 ^ r * ((fDiag r : ENNReal) / ((Q ^ 18 * J779 ^ r : ℕ) : ENNReal)) := by
  by_cases hr : 2 ≤ r ∧ r ≤ 20
  · obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    have hc := diag_check_all (k + 2) hr.1 hr.2
    unfold diagCheckR at hc
    simp only [Bool.and_eq_true, Nat.ble_eq] at hc
    obtain ⟨hok, hle⟩ := hc
    simp only [Nat.add_sub_cancel] at hok hle
    have hb := ClaudeR3.Asm.diag_bound k 104 (diagRp.getD (k + 2) 0) (2 ^ diagBB.getD (k + 2) 0) (by norm_num)
      (rp_le diagRp k diagRp_le hr.2) hok
    have h := ClaudeR3.Law.lawAvg_uniformOn_count (r := k + 2) (T := Coords × Coords) (capS 779)
      (fun L tt => ListCov wordDigit L tt.1 ∧ ListCov wordDigit L tt.2)
    have henv : (fun L => env (n := 9) (C := Child) wordDigit L ^ 2) =
        fun L => SigGolfResearch.Gate6.Moments.finiteAverage
          (fun tt : Coords × Coords => if ListCov wordDigit L tt.1 ∧ ListCov wordDigit L tt.2 then 1 else 0) := by
      funext L; exact env_sq wordDigit L
    rw [henv, show honest779 = uniformOn (capS 779) from rfl, h, card_capS779, Fintype.card_prod, card_coords, one_pow, one_mul, fDiag, if_pos hr]
    have e779 : capS (675 + 104) = capS 779 := rfl
    rw [e779] at hb
    calc _ ≤ ((diagD.getD (k + 2) 0 : ℕ) : ENNReal) /
          ((J779 : ENNReal) ^ (k + 2) * (((Q ^ 9 * Q ^ 9 : ℕ)) : ENNReal)) :=
          ENNReal.div_le_div_right (by exact_mod_cast hb.trans hle) _
      _ = _ := by push_cast; ring_nf
  · rw [fDiag, if_neg hr]
    have hd := lawAvg_le_uniform honest779 kappa779 honest_density r
      (fun L => env (n := 9) (C := Child) wordDigit L ^ 2)
    rw [env_sq_moment wordDigit (Fintype.card_fin 563) (Fintype.card_fin 128) w1T w2T r,
      density_conv r _ ((Kc * Nn ^ 2) ^ 9) (128 ^ 9) (by norm_num [Kc, Nn]) (by norm_num)] at hd
    refine hd.trans (le_of_eq ?_)
    congr 3

end Pay

end ClaudeR3.Final
