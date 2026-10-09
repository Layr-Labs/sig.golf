import SigGolfCandidate.ClaudeR3.R1
import SigGolfCandidate.ClaudeR3.Q7
import SigGolfCandidate.ClaudeR3.Q5

namespace ClaudeR3.Final
open Finset ENNReal
open ClaudeWCT.Numerics.N600 (uniformOn priceN priceScale priceScale_mul card_index env_moment xNum Nn Q A
  card_table w1_table)
open ClaudeWCT.Numerics.Law (lawAvg marked lawAvg_mul_left lawAvg_sum lawAvg_le_uniform law_marked_atIndex
  lawAvg_mono lawAvg_const)
open ClaudeWCT.Numerics.Thinning (env env_le_one ListCov)
open SphincsSecurity.Concrete (binomialAverage uniformWordAverage)
open ClaudeWCT.WCT9 (wordDigit Child Rank)
open ClaudeR3.Asm (capS J779 card_capS779 capS779_nonempty)
open ClaudeR3.BonfData

abbrev Coords := Fin 9 → Child × Rank

noncomputable def honest779 : Coords → ENNReal := uniformOn (capS 779)

theorem card_coords : Fintype.card Coords = Q ^ 9 := card_table (Fintype.card_fin 563) (Fintype.card_fin 128)

theorem uniformOn_sum_one {β : Type} [Fintype β] {C : Type} [Fintype C] [DecidableEq C]
    (S : Finset (Fin 9 → C × β)) (hS : S.Nonempty) : ∑ x, uniformOn S x = 1 := by
  classical
  unfold uniformOn
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, ENNReal.mul_inv_cancel (by simp [hS.ne_empty])
    (ENNReal.natCast_ne_top _)]

theorem honest_sum_one : ∑ x, honest779 x = 1 := uniformOn_sum_one (capS 779) capS779_nonempty

noncomputable def kappa779 : ENNReal := ((Q ^ 9 : ℕ) : ENNReal) / (J779 : ENNReal)

theorem honest_density (x : Coords) : honest779 x ≤ kappa779 * (Fintype.card Coords : ENNReal)⁻¹ := by
  classical
  unfold honest779 uniformOn kappa779
  rw [card_coords, ← card_capS779]
  split_ifs
  · rw [div_eq_mul_inv, mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel (by simp [Q]) (ENNReal.natCast_ne_top _),
      one_mul]
  · exact zero_le

theorem density_to_J (r X : ℕ) :
    kappa779 ^ r * ((X : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) =
      1 ^ r * (((128 ^ 9 * X : ℕ) : ENNReal) / ((Q ^ 9 * J779 ^ r : ℕ) : ENNReal)) := by
  unfold kappa779
  have hJ : (0 : ℝ) < J779 := by unfold J779; norm_num
  apply (ENNReal.toReal_eq_toReal_iff' (by
      refine ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_)) ?_
      · unfold J779; simp
      · exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp [Nn, Q]))
    (by
      refine ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_)
      unfold J779; simp [Q])).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, one_pow,
    one_mul]
  push_cast
  have hJ' : (J779 : ℝ) ≠ 0 := hJ.ne'
  have hN : (Nn : ℝ) ≠ 0 := by norm_num [Nn]
  rw [div_pow, ← pow_mul, show (Q : ℝ) = 128 * Nn by norm_num [Q, Nn]]
  field_simp
  ring

theorem mean_check_all (r : ℕ) (h1 : 2 ≤ r) (h2 : r ≤ 20) : meanCheckR r = true := by
  interval_cases r
  exacts [mean_r2, mean_r3, mean_r4, mean_r5, mean_r6, mean_r7, mean_r8, mean_r9, mean_r10, mean_r11, mean_r12,
    mean_r13, mean_r14, mean_r15, mean_r16, mean_r17, mean_r18, mean_r19, mean_r20]

set_option maxRecDepth 10000 in
theorem meanRp_le : ∀ r, 2 ≤ r → r ≤ 20 → meanRp.getD r 0 ≤ r := by
  intro r h1 h2; interval_cases r <;> decide

def fMean (r : ℕ) : ℕ := if 2 ≤ r ∧ r ≤ 20 then meanD.getD r 0 else 128 ^ 9 * xNum r ^ 9

theorem mean_pay [SampleableType Coords] (r : ℕ) :
    lawAvg honest779 r (env (n := 9) (C := Child) wordDigit) ≤
      1 ^ r * ((fMean r : ENNReal) / ((Q ^ 9 * J779 ^ r : ℕ) : ENNReal)) := by
  by_cases hr : 2 ≤ r ∧ r ≤ 20
  · obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    have hc := mean_check_all (k + 2) hr.1 hr.2
    unfold meanCheckR at hc
    simp only [Bool.and_eq_true, Nat.ble_eq] at hc
    obtain ⟨hok, hle⟩ := hc
    simp only [Nat.add_sub_cancel] at hok hle
    have hb := ClaudeR3.Asm.mean_bound k 104 (meanRp.getD (k + 2) 0) (2 ^ meanBB.getD (k + 2) 0) (by norm_num)
      (meanRp_le (k + 2) (by omega) hr.2) hok
    have hcount := ClaudeR3.Law.lawAvg_uniformOn_count (r := k + 2) (capS 779) (fun L t => ListCov wordDigit L t)
    show lawAvg (uniformOn (capS 779)) (k + 2) (fun L => SigGolfResearch.Gate6.Moments.finiteAverage
      (fun t => if ListCov wordDigit L t then 1 else 0)) ≤ _
    rw [hcount, card_capS779, card_coords, one_pow, one_mul, fMean, if_pos hr]
    have e779 : capS (675 + 104) = capS 779 := rfl
    rw [e779] at hb
    calc _ ≤ ((meanD.getD (k + 2) 0 : ℕ) : ENNReal) / ((J779 : ENNReal) ^ (k + 2) * ((Q ^ 9 : ℕ) : ENNReal)) :=
          ENNReal.div_le_div_right (by exact_mod_cast hb.trans hle) _
      _ = _ := by push_cast; ring_nf
  · have hd := lawAvg_le_uniform honest779 kappa779 honest_density r (env (n := 9) (C := Child) wordDigit)
    rw [env_moment wordDigit (Fintype.card_fin 563) (Fintype.card_fin 128)
      (fun p => w1_table ClaudeR3.Tab.wordsOf_wordDigit' (fun x j => ClaudeR3.Tab.wordDigit_le4 x j) p) r,
      density_to_J] at hd
    rw [fMean, if_neg hr]
    exact hd

theorem mean_pay_one (r : ℕ) : lawAvg honest779 r (env (n := 9) (C := Child) wordDigit) ≤ 1 :=
  (lawAvg_mono honest779 r (env_le_one wordDigit)).trans_eq (lawAvg_const honest779 honest_sum_one r 1)

theorem price_mean_eq (T : ℕ) :
    lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (priceN wordDigit) =
      (A : ENNReal) * binomialAverage (2 ^ 31 : ENNReal)⁻¹ T
        (fun r => lawAvg honest779 r (env (n := 9) (C := Child) wordDigit)) := by
  unfold priceN
  rw [lawAvg_mul_left, lawAvg_sum]
  simp_rw [law_marked_atIndex honest779 honest_sum_one, card_index]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← priceScale_mul]

def meanJCheck : Bool :=
  ClaudeR3.PoissonJ.poissonCheckJ J779 13533529 100000000 2 1 fMean (Q ^ 9) A 1 602 1000 80

end ClaudeR3.Final
