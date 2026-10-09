import SigGolfCandidate.ClaudeWCT.Numerics.N600Price

namespace ClaudeR3.PoissonJ
open ENNReal SphincsSecurity.Concrete
open ClaudeWCT.Numerics.Kernel (fact)
open ClaudeWCT.Numerics.PoissonReflect (binomWeight binomWeight_le binomialAverage_truncate binomial_tail
  range_foldr_eq_sum fact_eq scale_le)

def poissonCheckJ (Dv un ud ln ld : Nat) (f : Nat → Nat) (dbase sn sd Mn Md R : Nat) : Bool :=
  let S := (List.range (R + 1)).foldr (fun r s =>
    un * ln ^ r * ld ^ (R - r) * (fact R / fact r) * f r * Dv ^ (R - r) + s) 0
  Md * sn * (S * ld * (R + 1) + ln ^ (R + 1) * ud * dbase * Dv ^ R) ≤
    Mn * sd * ud * dbase * ld ^ (R + 1) * fact (R + 1) * Dv ^ R

def termNumJ (Dv un ln ld R : ℕ) (f : ℕ → ℕ) (r : ℕ) : ℕ :=
  un * ln ^ r * ld ^ (R - r) * (fact R / fact r) * f r * Dv ^ (R - r)
def denomJ (Dv ud ld dbase R : ℕ) : ℕ :=
  ud * dbase * ld ^ (R + 1) * fact (R + 1) * Dv ^ R
theorem denomJ_pos {Dv : ℕ} (hQ : 0 < Dv) (ud ld dbase R : ℕ) (hud : 0 < ud) (hld : 0 < ld) (hdb : 0 < dbase) :
    0 < denomJ Dv ud ld dbase R := by
  unfold denomJ
  rw [fact_eq]
  positivity
theorem termJ_eq {Dv : ℕ} (hQ : 0 < Dv) (un ud ln ld dbase R r : ℕ) (f : ℕ → ℕ) (hr : r ≤ R) (hud : 0 < ud)
    (hld : 0 < ld) (hdb : 0 < dbase) :
    (un : ENNReal) / ud * ((ln : ENNReal) / ld) ^ r / (r.factorial : ENNReal) *
        ((f r : ENNReal) / ((dbase * Dv ^ r : ℕ) : ENNReal)) =
      ((termNumJ Dv un ln ld R f r * ld * (R + 1) : ℕ) : ENNReal) / (denomJ Dv ud ld dbase R : ℕ) := by
  have hD := denomJ_pos hQ ud ld dbase R hud hld hdb
  have hne1 : (un : ENNReal) / ud * ((ln : ENNReal) / ld) ^ r / (r.factorial : ENNReal) *
      ((f r : ENNReal) / ((dbase * Dv ^ r : ℕ) : ENNReal)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.div_ne_top _ (by exact_mod_cast (Nat.factorial_pos r).ne')
      apply ENNReal.mul_ne_top (ENNReal.div_ne_top (by simp) (by exact_mod_cast hud.ne'))
      exact ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp) (by exact_mod_cast hld.ne'))
    · exact ENNReal.div_ne_top (by simp)
        (by exact_mod_cast (by positivity : 0 < dbase * Dv ^ r).ne')
  have hne2 : ((termNumJ Dv un ln ld R f r * ld * (R + 1) : ℕ) : ENNReal) /
      (denomJ Dv ud ld dbase R : ℕ) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hD.ne')
  apply (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  unfold termNumJ denomJ
  rw [Nat.add_sub_cancel_left, fact_eq, fact_eq, fact_eq, Nat.factorial_succ (r + k)]
  have hdvd : r.factorial ∣ (r + k).factorial := Nat.factorial_dvd_factorial (Nat.le_add_right r k)
  have hf0 : ((r.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  have hfk : (((r + k).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hud' : (ud : ℝ) ≠ 0 := by exact_mod_cast hud.ne'
  have hld' : (ld : ℝ) ≠ 0 := by exact_mod_cast hld.ne'
  have hdb' : (dbase : ℝ) ≠ 0 := by exact_mod_cast hdb.ne'
  have hQ' : (Dv : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  push_cast [Nat.cast_div hdvd hf0]
  simp only [div_pow]
  field_simp
  ring
theorem tailJ_eq {Dv : ℕ} (hQ : 0 < Dv) (ud ln ld dbase R : ℕ) (hud : 0 < ud) (hld : 0 < ld) (hdb : 0 < dbase) :
    ((ln : ENNReal) / ld) ^ (R + 1) / ((R + 1).factorial : ENNReal) =
      ((ln ^ (R + 1) * ud * dbase * Dv ^ R : ℕ) : ENNReal) / (denomJ Dv ud ld dbase R : ℕ) := by
  have hD := denomJ_pos hQ ud ld dbase R hud hld hdb
  have hne1 : ((ln : ENNReal) / ld) ^ (R + 1) / ((R + 1).factorial : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp)
      (by exact_mod_cast hld.ne'))) (by exact_mod_cast (Nat.factorial_pos _).ne')
  have hne2 : ((ln ^ (R + 1) * ud * dbase * Dv ^ R : ℕ) : ENNReal) /
      (denomJ Dv ud ld dbase R : ℕ) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hD.ne')
  apply (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  unfold denomJ
  rw [fact_eq]
  have hf0 : (((R + 1).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hud' : (ud : ℝ) ≠ 0 := by exact_mod_cast hud.ne'
  have hld' : (ld : ℝ) ≠ 0 := by exact_mod_cast hld.ne'
  have hdb' : (dbase : ℝ) ≠ 0 := by exact_mod_cast hdb.ne'
  have hQ' : (Dv : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  push_cast
  simp only [div_pow]
  field_simp
theorem binomWeight_tilt_le' (rate : ENNReal) (T R r : ℕ) (hr : r ≤ R) (κ lam u : ENNReal)
    (hlam : (T : ENNReal) * rate * κ ≤ lam) (hu : (1 - rate) ^ (T - R) ≤ u) :
    binomWeight rate T r * κ ^ r ≤ u * lam ^ r / r.factorial := by
  have h := binomWeight_le rate T R r hr ((T : ENNReal) * rate) u le_rfl hu
  calc binomWeight rate T r * κ ^ r ≤ u * ((T : ENNReal) * rate) ^ r / r.factorial * κ ^ r :=
        mul_le_mul' h le_rfl
    _ = u * ((T : ENNReal) * rate * κ) ^ r / r.factorial := by
        simp only [div_eq_mul_inv, mul_pow]; ring
    _ ≤ u * lam ^ r / r.factorial := by gcongr
theorem poissonCheckJ_sound {Dv un ud ln ld : ℕ} {f : ℕ → ℕ} {dbase sn sd Mn Md R : ℕ}
    (hcheck : poissonCheckJ Dv un ud ln ld f dbase sn sd Mn Md R = true) (hQ : 0 < Dv)
    (hud : 0 < ud) (hld : 0 < ld) (hdb : 0 < dbase) (hsd : 0 < sd) (hMd : 0 < Md)
    {rate : ENNReal} (hrate : rate ≤ 1) {T : ℕ} (κ : ENNReal) (hκ : 1 ≤ κ)
    (hlam : (T : ENNReal) * rate * κ ≤ (ln : ENNReal) / ld)
    (hu : (1 - rate) ^ (T - R) ≤ (un : ENNReal) / ud)
    (g : ℕ → ENNReal)
    (hpay : ∀ r ≤ R, g r ≤ κ ^ r * ((f r : ENNReal) / ((dbase * Dv ^ r : ℕ) : ENNReal)))
    (htail : ∀ r, R < r → g r ≤ 1) :
    (sn : ENNReal) / sd * binomialAverage rate T g ≤ (Mn : ENNReal) / Md := by
  have hineq : Md * sn * ((∑ r ∈ Finset.range (R + 1), termNumJ Dv un ln ld R f r) * ld * (R + 1) +
      ln ^ (R + 1) * ud * dbase * Dv ^ R) ≤ Mn * sd * denomJ Dv ud ld dbase R := by
    have h := hcheck
    simp only [poissonCheckJ, decide_eq_true_eq] at h
    rw [range_foldr_eq_sum] at h
    unfold denomJ termNumJ
    refine h.trans_eq ?_
    ring
  have hD := denomJ_pos hQ ud ld dbase R hud hld hdb
  refine le_trans (mul_le_mul' le_rfl ?_) (scale_le sn sd Mn Md _ _ hsd hMd hD hineq)
  refine (binomialAverage_truncate rate T (R + 1) g 1 (fun r hr => htail r hr)).trans ?_
  have hsplit : ((((∑ r ∈ Finset.range (R + 1), termNumJ Dv un ln ld R f r) * ld * (R + 1) +
      ln ^ (R + 1) * ud * dbase * Dv ^ R : ℕ)) : ENNReal) / (denomJ Dv ud ld dbase R : ℕ) =
      (∑ r ∈ Finset.range (R + 1),
        ((termNumJ Dv un ln ld R f r * ld * (R + 1) : ℕ) : ENNReal) / (denomJ Dv ud ld dbase R : ℕ)) +
      ((ln ^ (R + 1) * ud * dbase * Dv ^ R : ℕ) : ENNReal) / (denomJ Dv ud ld dbase R : ℕ) := by
    rw [Finset.sum_mul, Finset.sum_mul, Nat.cast_add, Nat.cast_sum, ENNReal.add_div]
    congr 1
    simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [one_mul, hsplit]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro r hr
    have hr' : r ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [← termJ_eq hQ un ud ln ld dbase R r f hr' hud hld hdb]
    calc binomWeight rate T r * g r
        ≤ binomWeight rate T r * (κ ^ r * ((f r : ENNReal) / ((dbase * Dv ^ r : ℕ) : ENNReal))) :=
          mul_le_mul' le_rfl (hpay r hr')
      _ = binomWeight rate T r * κ ^ r * ((f r : ENNReal) / ((dbase * Dv ^ r : ℕ) : ENNReal)) := by ring
      _ ≤ (un : ENNReal) / ud * ((ln : ENNReal) / ld) ^ r / (r.factorial : ENNReal) *
            ((f r : ENNReal) / ((dbase * Dv ^ r : ℕ) : ENNReal)) := by
          refine mul_le_mul' ?_ le_rfl
          exact binomWeight_tilt_le' rate T R r hr' κ _ _ hlam hu
  · refine (binomial_tail rate hrate T (R + 1)).trans ?_
    rw [← tailJ_eq hQ ud ln ld dbase R hud hld hdb]
    have hlam0 : (T : ENNReal) * rate ≤ (ln : ENNReal) / ld :=
      le_trans (le_mul_of_one_le_right' hκ) hlam
    gcongr
end ClaudeR3.PoissonJ
