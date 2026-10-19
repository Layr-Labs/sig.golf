import SigGolfCandidate.T3.Gate6.ChildCounting
import SigGolfCandidate.Research.V7Composed198Gate
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import SigGolfCandidate.ClaudeWCT.Numerics.N600PriceChecks
import SigGolfCandidate.ClaudeWCT.Numerics.N600Data
import Mathlib.Algebra.BigOperators.Ring.List
import SigGolfCandidate.ClaudeWCT.Numerics.PoissonReflect
import SigGolfCandidate.ClaudeWCT.Numerics.LawAverage


-- Check the independent arithmetic certificates sequentially to bound peak memory.
set_option Elab.async false
set_option maxRecDepth 100000
section


namespace ClaudeWCT.Numerics.N600
open Finset Polynomial ClaudeWCT.Numerics.Thinning
open ClaudeWCT.Numerics.Kernel (wpos wneg packPos packNeg dataPoly HB packPos_eq packNeg_eq packPos'_eq
  packNeg'_eq)
noncomputable def polyZ (d : List (ℕ × ℤ)) : ℤ[X] := (d.map fun e => C e.2 * X ^ e.1).sum
noncomputable def momF (x : ℤ) (r : ℕ) (f : ℤ[X]) : ℤ := f.sum fun n a => a * (x + n) ^ r
theorem momF_add (x : ℤ) (r : ℕ) (f g : ℤ[X]) : momF x r (f + g) = momF x r f + momF x r g :=
  Polynomial.sum_add_index f g _ (fun _ => by simp) (fun _ _ _ => by ring)
theorem momF_zero (x : ℤ) (r : ℕ) : momF x r 0 = 0 := by simp [momF]
theorem momF_monomial (x : ℤ) (r n : ℕ) (a : ℤ) : momF x r (C a * X ^ n) = a * (x + n) ^ r := by
  rw [momF, C_mul_X_pow_eq_monomial, sum_monomial_index]
  simp
theorem momF_list_sum (x : ℤ) (r : ℕ) (l : List ℤ[X]) : momF x r l.sum = (l.map (momF x r)).sum := by
  induction l with
  | nil => simp [momF_zero]
  | cons f l ih => simp [momF_add, ih]
theorem momF_polyZ (x : ℤ) (r : ℕ) (d : List (ℕ × ℤ)) : momF x r (polyZ d) = tmom d x r := by
  rw [polyZ, momF_list_sum, List.map_map, tmom]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  exact momF_monomial x r e.1 e.2
theorem momF_sq (x : ℤ) (r : ℕ) (d : List (ℕ × ℤ)) : momF x r (polyZ d * polyZ d) = tmom2 d x r := by
  have hmul : polyZ d * polyZ d =
      (d.map fun e₁ => (d.map fun e₂ => C (e₁.2 * e₂.2) * X ^ (e₁.1 + e₂.1)).sum).sum := by
    rw [polyZ, ← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun e₁ _ => ?_
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun e₂ _ => ?_
    rw [C_mul, pow_add]
    ring
  rw [hmul, momF_list_sum, List.map_map, tmom2]
  congr 1
  refine List.map_congr_left fun e₁ _ => ?_
  rw [Function.comp_apply, momF_list_sum, List.map_map, tmom, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun e₂ _ => ?_
  rw [Function.comp_apply, momF_monomial]
  push_cast
  ring
theorem polyZ_eq (d : List (ℕ × ℤ)) :
    polyZ d = (dataPoly d false).map (Nat.castRingHom ℤ) - (dataPoly d true).map (Nat.castRingHom ℤ) := by
  induction d with
  | nil => simp [polyZ, dataPoly]
  | cons e d ih =>
    have h1 : polyZ (e :: d) = C e.2 * X ^ e.1 + polyZ d := by simp [polyZ]
    have h2 : dataPoly (e :: d) false = C e.2.toNat * X ^ e.1 + dataPoly d false := rfl
    have h3 : dataPoly (e :: d) true = C (-e.2).toNat * X ^ e.1 + dataPoly d true := rfl
    rw [h1, h2, h3, ih, Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    have he := Int.toNat_sub_toNat_neg e.2
    have hC : (C e.2 : ℤ[X]) = C ((Nat.castRingHom ℤ) e.2.toNat) - C ((Nat.castRingHom ℤ) (-e.2).toNat) := by
      rw [← C_sub]
      simp only [eq_natCast, he]
    rw [hC]
    ring
theorem eval_one_w1_pos : (dataPoly w1Data false).eval 1 = 3415 := by
  rw [← packPos'_eq]; decide +kernel
theorem eval_one_w1_neg : (dataPoly w1Data true).eval 1 = 3415 := by
  rw [← packNeg'_eq]; decide +kernel
theorem eval_one_ww_pos : (dataPoly wwData false).eval 1 ≤ 2 ^ 100 := by
  rw [← packPos'_eq]; decide +kernel
theorem eval_one_ww_neg : (dataPoly wwData true).eval 1 ≤ 2 ^ 100 := by
  rw [← packNeg'_eq]; decide +kernel
theorem polyZ_w1_sq : polyZ w1Data * polyZ w1Data = polyZ wwData := by
  have hc := conv_ok
  unfold convCheck at hc
  replace hc := Nat.eq_of_beq_eq_true hc
  rw [packPos_eq, packPos_eq, packNeg_eq, packNeg_eq] at hc
  have hE : ((dataPoly w1Data false) ^ 2 + (dataPoly w1Data true) ^ 2 + dataPoly wwData true).eval HB =
      (dataPoly wwData false + 2 * dataPoly w1Data false * dataPoly w1Data true).eval HB := by
    simp only [eval_add, eval_mul, eval_pow, eval_ofNat]
    generalize (dataPoly w1Data false).eval HB = a at hc ⊢
    generalize (dataPoly w1Data true).eval HB = b at hc ⊢
    generalize (dataPoly wwData false).eval HB = c at hc ⊢
    generalize (dataPoly wwData true).eval HB = d at hc ⊢
    exact hc
  have hHB : 0 < HB := by unfold HB; positivity
  have e1 := eval_one_w1_pos
  have e2 := eval_one_w1_neg
  have h1 : ((dataPoly w1Data false) ^ 2 + (dataPoly w1Data true) ^ 2 + dataPoly wwData true).eval 1 < 2 ^ 127 := by
    have h : ((dataPoly w1Data false) ^ 2 + (dataPoly w1Data true) ^ 2 + dataPoly wwData true).eval 1 =
        3415 ^ 2 + 3415 ^ 2 + (dataPoly wwData true).eval 1 := by
      simp only [eval_add, eval_pow, e1, e2]
    have e3 := eval_one_ww_neg
    refine lt_of_eq_of_lt h ?_
    generalize (dataPoly wwData true).eval 1 = w at e3 ⊢
    omega
  have h2 : (dataPoly wwData false + 2 * dataPoly w1Data false * dataPoly w1Data true).eval 1 < 2 ^ 127 := by
    have h : (dataPoly wwData false + 2 * dataPoly w1Data false * dataPoly w1Data true).eval 1 =
        (dataPoly wwData false).eval 1 + 2 * 3415 * 3415 := by
      simp only [eval_add, eval_mul, eval_ofNat, e1, e2]
    have e3 := eval_one_ww_pos
    refine lt_of_eq_of_lt h ?_
    generalize (dataPoly wwData false).eval 1 = w at e3 ⊢
    omega
  have hpoly := eq_of_eval_eq hHB (fun j => Kernel.coeff_lt_of_eval_one h1 j)
    (fun j => Kernel.coeff_lt_of_eval_one h2 j) hE
  have hmap := congrArg (Polynomial.map (Nat.castRingHom ℤ)) hpoly
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat] at hmap
  rw [polyZ_eq, polyZ_eq]
  linear_combination hmap
theorem tmom2_w1Data (x : ℤ) (r : ℕ) : tmom2 w1Data x r = tmom wwData x r := by
  rw [← momF_sq, polyZ_w1_sq, momF_polyZ]
theorem xNum_cast (r : ℕ) (h : 0 ≤ tmom w1Data B1 r) : (xNum r : ℤ) = tmom w1Data B1 r := by
  have hw := wpos_sub_wneg w1Data B1 r
  unfold xNum
  omega
theorem xfNum_cast (t r : ℕ) (h : 0 ≤ tmom (wfData t) B1 r) : (xfNum t r : ℤ) = tmom (wfData t) B1 r := by
  have hw := wpos_sub_wneg (wfData t) B1 r
  unfold xfNum
  omega
theorem yNum_cast (r : ℕ) (h : 0 ≤ tmom w2Data B1 r + (Kc - 1 : ℕ) * tmom2 w1Data B2 r) :
    (yNum r : ℤ) = tmom w2Data B1 r + (Kc - 1 : ℕ) * tmom2 w1Data B2 r := by
  have hw := wpos_sub_wneg w2Data B1 r
  have hww := wpos_sub_wneg wwData B2 r
  rw [tmom2_w1Data] at h ⊢
  have hk : Kc - 1 = 127 := rfl
  unfold yNum yPos yNeg
  rw [hk] at h ⊢
  push_cast at h ⊢
  omega
section Closed
open SphincsSecurity.Concrete (uniformWordAverage)
variable {β : Type} [Fintype β] {C : Type} [Fintype C] [DecidableEq C]
def W1Table (val : β → Fin 6 → ℕ) : Prop :=
  ∀ p, (#{x : β × (Fin p → β) | CoversT val (val x.1) x.2} : ℤ) = (w1Data.map fun e => e.2 * (e.1 : ℤ) ^ p).sum
def W2Table (val : β → Fin 6 → ℕ) : Prop :=
  ∀ p, (#{x : β × β × (Fin p → β) | CoversT val (val x.1) x.2.2 ∧ CoversT val (val x.2.1) x.2.2} : ℤ) =
    (w2Data.map fun e => e.2 * (e.1 : ℤ) ^ p).sum
def WFTable (val : β → Fin 6 → ℕ) (i : Fin 6) : Prop :=
  ∀ p, (#{x : β × (Fin p → β) | CoversExcept val i (val x.1) x.2} : ℤ) =
    ((wfData i).map fun e => e.2 * (e.1 : ℤ) ^ p).sum
omit [DecidableEq C] in
theorem B1_eq (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128) :
    (((Fintype.card C - 1) * Fintype.card β : ℕ) : ℤ) = B1 := by
  rw [hβ, hC]; rfl
omit [DecidableEq C] in
theorem B2_eq (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128) :
    (((Fintype.card C - 2) * Fintype.card β : ℕ) : ℤ) = B2 := by
  rw [hβ, hC]; rfl
theorem coord_first_xNum (val : β → Fin 6 → ℕ) (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128)
    (h₁ : W1Table val) (r : ℕ) :
    #{y : (C × β) × (Fin r → C × β) | CovAt val y.1.1 (val y.1.2) y.2} = Kc * xNum r := by
  have hc := coord_first (C := C) val w1Data (fun p => (h₁ p).trans (tmom_zero w1Data p).symm) r
  rw [B1_eq hβ hC, hC] at hc
  have hnn : 0 ≤ tmom w1Data B1 r := by
    have := Int.natCast_nonneg (#{y : (C × β) × (Fin r → C × β) | CovAt val y.1.1 (val y.1.2) y.2})
    push_cast at hc
    omega
  have hx := xNum_cast r hnn
  have hK : Kc = 128 := rfl
  rw [hK]
  push_cast at hc
  omega
theorem coord_second_yNum (val : β → Fin 6 → ℕ) (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128)
    (h₁ : W1Table val) (h₂ : W2Table val) (r : ℕ) :
    #{y : ((C × β) × (C × β)) × (Fin r → C × β) |
      CovAt val y.1.1.1 (val y.1.1.2) y.2 ∧ CovAt val y.1.2.1 (val y.1.2.2) y.2} = Kc * yNum r := by
  have hc := coord_second (C := C) val w1Data w2Data (fun p => (h₁ p).trans (tmom_zero w1Data p).symm)
    (fun p => (h₂ p).trans (tmom_zero w2Data p).symm) r
  rw [B1_eq hβ hC, B2_eq hβ hC, hC] at hc
  have hK1 : ((Kc - 1 : ℕ) : ℤ) = 127 := rfl
  have hnn : 0 ≤ tmom w2Data B1 r + (Kc - 1 : ℕ) * tmom2 w1Data B2 r := by
    have := Int.natCast_nonneg (#{y : ((C × β) × (C × β)) × (Fin r → C × β) |
      CovAt val y.1.1.1 (val y.1.1.2) y.2 ∧ CovAt val y.1.2.1 (val y.1.2.2) y.2})
    rw [hK1]
    push_cast at hc
    omega
  have hy := yNum_cast r hnn
  rw [hK1] at hy
  have hK : Kc = 128 := rfl
  rw [hK]
  push_cast at hc
  omega
theorem coord_near_xfNum (val : β → Fin 6 → ℕ) (i : Fin 6) (hβ : Fintype.card β = 563)
    (hC : Fintype.card C = 128) (hf : WFTable val i) (r : ℕ) :
    #{y : (C × β) × (Fin r → C × β) | CovAtExcept val i y.1.1 (val y.1.2) y.2} = Kc * xfNum i r := by
  have hc := coord_near (C := C) val i (wfData i) (fun p => (hf p).trans (tmom_zero (wfData i) p).symm) r
  rw [B1_eq hβ hC, hC] at hc
  have hnn : 0 ≤ tmom (wfData i) B1 r := by
    have := Int.natCast_nonneg (#{y : (C × β) × (Fin r → C × β) | CovAtExcept val i y.1.1 (val y.1.2) y.2})
    push_cast at hc
    omega
  have hx := xfNum_cast i r hnn
  have hK : Kc = 128 := rfl
  rw [hK]
  push_cast at hc
  omega
omit [DecidableEq C] in
theorem card_table (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128) :
    Fintype.card (Fin 9 → C × β) = Q ^ 9 := by
  simp only [Fintype.card_fun, Fintype.card_prod, hβ, hC, Fintype.card_fin]
  rfl
variable [SampleableType (Fin 9 → C × β)]
theorem env_moment (val : β → Fin 6 → ℕ) (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128)
    (h₁ : W1Table val) (r : ℕ) :
    uniformWordAverage r (env (n := 9) (C := C) val) =
      ((xNum r ^ 9 : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal) := by
  have hE : Fintype.card (Fin r → Fin 9 → C × β) = (Q ^ 9) ^ r := by
    rw [Fintype.card_fun, card_table hβ hC, Fintype.card_fin]
  rw [env_moment_count, coord_first_xNum val hβ hC h₁ r, hE, card_table hβ hC]
  have hnum : (Kc * xNum r) ^ 9 = Kc ^ 9 * xNum r ^ 9 := by ring
  have hden : (Q ^ 9 : ℕ) * (Q ^ 9) ^ r = Kc ^ 9 * (Nn ^ 9 * Q ^ (9 * r)) := by
    rw [← pow_mul, ← mul_assoc, ← mul_pow]
    rfl
  rw [hnum, ← Nat.cast_mul, hden, Nat.cast_mul, Nat.cast_mul (Kc ^ 9)]
  exact ENNReal.mul_div_mul_left _ _ (by simp [Kc]) (by simp)
theorem env_sq_moment (val : β → Fin 6 → ℕ) (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128)
    (h₁ : W1Table val) (h₂ : W2Table val) (r : ℕ) :
    uniformWordAverage r (fun L => env (n := 9) (C := C) val L ^ 2) =
      ((yNum r ^ 9 : ℕ) : ENNReal) / (((Kc * Nn ^ 2) ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal) := by
  have hE : Fintype.card (Fin r → Fin 9 → C × β) = (Q ^ 9) ^ r := by
    rw [Fintype.card_fun, card_table hβ hC, Fintype.card_fin]
  rw [env_sq_moment_count, coord_second_yNum val hβ hC h₁ h₂ r, Fintype.card_prod, hE, card_table hβ hC]
  have hnum : (Kc * yNum r) ^ 9 = Kc ^ 9 * yNum r ^ 9 := by ring
  have hden : (Q ^ 9 * Q ^ 9 : ℕ) * (Q ^ 9) ^ r = Kc ^ 9 * ((Kc * Nn ^ 2) ^ 9 * Q ^ (9 * r)) := by
    rw [← pow_mul, ← mul_assoc, ← mul_pow, ← mul_pow, show Q * Q = Kc * (Kc * Nn ^ 2) from rfl]
  rw [hnum, ← Nat.cast_mul, hden, Nat.cast_mul, Nat.cast_mul (Kc ^ 9)]
  exact ENNReal.mul_div_mul_left _ _ (by simp [Kc]) (by simp)
theorem nearEnv_moment (val : β → Fin 6 → ℕ) (k₀ : Fin 9) (i₀ : Fin 6)
    (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128) (h₁ : W1Table val) (hf : WFTable val i₀)
    (r : ℕ) :
    uniformWordAverage r (nearEnv (C := C) val k₀ i₀) =
      ((xNum r ^ 8 * xfNum i₀ r : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal) := by
  have hE : Fintype.card (Fin r → Fin 9 → C × β) = (Q ^ 9) ^ r := by
    rw [Fintype.card_fun, card_table hβ hC, Fintype.card_fin]
  rw [nearEnv_moment_count, coord_first_xNum val hβ hC h₁ r, coord_near_xfNum val i₀ hβ hC hf r, hE,
    card_table hβ hC]
  have hnum : (Kc * xNum r) ^ (9 - 1) * (Kc * xfNum i₀ r) = Kc ^ 9 * (xNum r ^ 8 * xfNum i₀ r) := by ring
  have hden : (Q ^ 9 : ℕ) * (Q ^ 9) ^ r = Kc ^ 9 * (Nn ^ 9 * Q ^ (9 * r)) := by
    rw [← pow_mul, ← mul_assoc, ← mul_pow]
    rfl
  rw [hnum, ← Nat.cast_mul, hden, Nat.cast_mul, Nat.cast_mul (Kc ^ 9)]
  exact ENNReal.mul_div_mul_left _ _ (by simp [Kc]) (by simp)
end Closed
end ClaudeWCT.Numerics.N600


end

section


namespace ClaudeWCT.Numerics.N600
open ENNReal SphincsSecurity.Concrete
open ClaudeWCT.Numerics.PoissonReflect (binomWeight binomWeight_le binomialAverage_truncate binomial_tail
  range_foldr_eq_sum fact_eq scale_le)
def termNumQ (Qv un ln ld R : ℕ) (f : ℕ → ℕ) (r : ℕ) : ℕ :=
  un * ln ^ r * ld ^ (R - r) * (Kernel.fact R / Kernel.fact r) * f r * Qv ^ (9 * (R - r))
def denomQ (Qv ud ld dbase R : ℕ) : ℕ :=
  ud * dbase * ld ^ (R + 1) * Kernel.fact (R + 1) * Qv ^ (9 * R)
theorem denomQ_pos {Qv : ℕ} (hQ : 0 < Qv) (ud ld dbase R : ℕ) (hud : 0 < ud) (hld : 0 < ld) (hdb : 0 < dbase) :
    0 < denomQ Qv ud ld dbase R := by
  unfold denomQ
  rw [fact_eq]
  positivity
theorem termQ_eq {Qv : ℕ} (hQ : 0 < Qv) (un ud ln ld dbase R r : ℕ) (f : ℕ → ℕ) (hr : r ≤ R) (hud : 0 < ud)
    (hld : 0 < ld) (hdb : 0 < dbase) :
    (un : ENNReal) / ud * ((ln : ENNReal) / ld) ^ r / (r.factorial : ENNReal) *
        ((f r : ENNReal) / ((dbase * Qv ^ (9 * r) : ℕ) : ENNReal)) =
      ((termNumQ Qv un ln ld R f r * ld * (R + 1) : ℕ) : ENNReal) / (denomQ Qv ud ld dbase R : ℕ) := by
  have hD := denomQ_pos hQ ud ld dbase R hud hld hdb
  have hne1 : (un : ENNReal) / ud * ((ln : ENNReal) / ld) ^ r / (r.factorial : ENNReal) *
      ((f r : ENNReal) / ((dbase * Qv ^ (9 * r) : ℕ) : ENNReal)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.div_ne_top _ (by exact_mod_cast (Nat.factorial_pos r).ne')
      apply ENNReal.mul_ne_top (ENNReal.div_ne_top (by simp) (by exact_mod_cast hud.ne'))
      exact ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp) (by exact_mod_cast hld.ne'))
    · exact ENNReal.div_ne_top (by simp)
        (by exact_mod_cast (by positivity : 0 < dbase * Qv ^ (9 * r)).ne')
  have hne2 : ((termNumQ Qv un ln ld R f r * ld * (R + 1) : ℕ) : ENNReal) /
      (denomQ Qv ud ld dbase R : ℕ) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hD.ne')
  apply (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  unfold termNumQ denomQ
  rw [Nat.add_sub_cancel_left, fact_eq, fact_eq, fact_eq, Nat.factorial_succ (r + k)]
  have hdvd : r.factorial ∣ (r + k).factorial := Nat.factorial_dvd_factorial (Nat.le_add_right r k)
  have hf0 : ((r.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  have hfk : (((r + k).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hud' : (ud : ℝ) ≠ 0 := by exact_mod_cast hud.ne'
  have hld' : (ld : ℝ) ≠ 0 := by exact_mod_cast hld.ne'
  have hdb' : (dbase : ℝ) ≠ 0 := by exact_mod_cast hdb.ne'
  have hQ' : (Qv : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  push_cast [Nat.cast_div hdvd hf0]
  simp only [div_pow]
  field_simp
  ring
theorem tailQ_eq {Qv : ℕ} (hQ : 0 < Qv) (ud ln ld dbase R : ℕ) (hud : 0 < ud) (hld : 0 < ld) (hdb : 0 < dbase) :
    ((ln : ENNReal) / ld) ^ (R + 1) / ((R + 1).factorial : ENNReal) =
      ((ln ^ (R + 1) * ud * dbase * Qv ^ (9 * R) : ℕ) : ENNReal) / (denomQ Qv ud ld dbase R : ℕ) := by
  have hD := denomQ_pos hQ ud ld dbase R hud hld hdb
  have hne1 : ((ln : ENNReal) / ld) ^ (R + 1) / ((R + 1).factorial : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp)
      (by exact_mod_cast hld.ne'))) (by exact_mod_cast (Nat.factorial_pos _).ne')
  have hne2 : ((ln ^ (R + 1) * ud * dbase * Qv ^ (9 * R) : ℕ) : ENNReal) /
      (denomQ Qv ud ld dbase R : ℕ) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hD.ne')
  apply (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  unfold denomQ
  rw [fact_eq]
  have hf0 : (((R + 1).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hud' : (ud : ℝ) ≠ 0 := by exact_mod_cast hud.ne'
  have hld' : (ld : ℝ) ≠ 0 := by exact_mod_cast hld.ne'
  have hdb' : (dbase : ℝ) ≠ 0 := by exact_mod_cast hdb.ne'
  have hQ' : (Qv : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  push_cast
  simp only [div_pow]
  field_simp
theorem binomWeight_tilt_le (rate : ENNReal) (T R r : ℕ) (hr : r ≤ R) (κ lam u : ENNReal)
    (hlam : (T : ENNReal) * rate * κ ≤ lam) (hu : (1 - rate) ^ (T - R) ≤ u) :
    binomWeight rate T r * κ ^ r ≤ u * lam ^ r / r.factorial := by
  have h := binomWeight_le rate T R r hr ((T : ENNReal) * rate) u le_rfl hu
  calc binomWeight rate T r * κ ^ r ≤ u * ((T : ENNReal) * rate) ^ r / r.factorial * κ ^ r :=
        mul_le_mul' h le_rfl
    _ = u * ((T : ENNReal) * rate * κ) ^ r / r.factorial := by
        simp only [div_eq_mul_inv, mul_pow]; ring
    _ ≤ u * lam ^ r / r.factorial := by gcongr
theorem poissonCheckQ_sound_tilt {Qv un ud ln ld : ℕ} {f : ℕ → ℕ} {dbase sn sd Mn Md R : ℕ}
    (hcheck : poissonCheckQ Qv un ud ln ld f dbase sn sd Mn Md R = true) (hQ : 0 < Qv)
    (hud : 0 < ud) (hld : 0 < ld) (hdb : 0 < dbase) (hsd : 0 < sd) (hMd : 0 < Md)
    {rate : ENNReal} (hrate : rate ≤ 1) {T : ℕ} (κ : ENNReal) (hκ : 1 ≤ κ)
    (hlam : (T : ENNReal) * rate * κ ≤ (ln : ENNReal) / ld)
    (hu : (1 - rate) ^ (T - R) ≤ (un : ENNReal) / ud)
    (g : ℕ → ENNReal)
    (hpay : ∀ r ≤ R, g r ≤ κ ^ r * ((f r : ENNReal) / ((dbase * Qv ^ (9 * r) : ℕ) : ENNReal)))
    (htail : ∀ r, R < r → g r ≤ 1) :
    (sn : ENNReal) / sd * binomialAverage rate T g ≤ (Mn : ENNReal) / Md := by
  have hineq : Md * sn * ((∑ r ∈ Finset.range (R + 1), termNumQ Qv un ln ld R f r) * ld * (R + 1) +
      ln ^ (R + 1) * ud * dbase * Qv ^ (9 * R)) ≤ Mn * sd * denomQ Qv ud ld dbase R := by
    have h := hcheck
    simp only [poissonCheckQ, decide_eq_true_eq] at h
    rw [range_foldr_eq_sum] at h
    unfold denomQ termNumQ
    refine h.trans_eq ?_
    ring
  have hD := denomQ_pos hQ ud ld dbase R hud hld hdb
  refine le_trans (mul_le_mul' le_rfl ?_) (scale_le sn sd Mn Md _ _ hsd hMd hD hineq)
  refine (binomialAverage_truncate rate T (R + 1) g 1 (fun r hr => htail r hr)).trans ?_
  have hsplit : ((((∑ r ∈ Finset.range (R + 1), termNumQ Qv un ln ld R f r) * ld * (R + 1) +
      ln ^ (R + 1) * ud * dbase * Qv ^ (9 * R) : ℕ)) : ENNReal) / (denomQ Qv ud ld dbase R : ℕ) =
      (∑ r ∈ Finset.range (R + 1),
        ((termNumQ Qv un ln ld R f r * ld * (R + 1) : ℕ) : ENNReal) / (denomQ Qv ud ld dbase R : ℕ)) +
      ((ln ^ (R + 1) * ud * dbase * Qv ^ (9 * R) : ℕ) : ENNReal) / (denomQ Qv ud ld dbase R : ℕ) := by
    rw [Finset.sum_mul, Finset.sum_mul, Nat.cast_add, Nat.cast_sum, ENNReal.add_div]
    congr 1
    simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [one_mul, hsplit]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro r hr
    have hr' : r ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [← termQ_eq hQ un ud ln ld dbase R r f hr' hud hld hdb]
    calc binomWeight rate T r * g r
        ≤ binomWeight rate T r * (κ ^ r * ((f r : ENNReal) / ((dbase * Qv ^ (9 * r) : ℕ) : ENNReal))) :=
          mul_le_mul' le_rfl (hpay r hr')
      _ = binomWeight rate T r * κ ^ r * ((f r : ENNReal) / ((dbase * Qv ^ (9 * r) : ℕ) : ENNReal)) := by ring
      _ ≤ (un : ENNReal) / ud * ((ln : ENNReal) / ld) ^ r / (r.factorial : ENNReal) *
            ((f r : ENNReal) / ((dbase * Qv ^ (9 * r) : ℕ) : ENNReal)) := by
          refine mul_le_mul' ?_ le_rfl
          exact binomWeight_tilt_le rate T R r hr' κ _ _ hlam hu
  · refine (binomial_tail rate hrate T (R + 1)).trans ?_
    rw [← tailQ_eq hQ ud ln ld dbase R hud hld hdb]
    have hlam0 : (T : ENNReal) * rate ≤ (ln : ENNReal) / ld :=
      le_trans (le_mul_of_one_le_right' hκ) hlam
    gcongr
end ClaudeWCT.Numerics.N600
end

section


namespace ClaudeWCT.Numerics.N600
open Finset ENNReal
open ClaudeWCT.Numerics.Thinning (env nearEnv env_le_one env_cons_le nearEnv_le_one nearEnv_cons_le)
open ClaudeWCT.Numerics.Law
open SphincsSecurity.Concrete (uniformWordAverage binomialAverage binomialAverage_mono binomialAverage_mul_left)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open ClaudeWCT.Numerics.PoissonReflect (rejection_window_sharp rate_le_one)
noncomputable def priceScale : ENNReal := ((1353 * 563 ^ 9 : ℕ) : ENNReal) / 2 ^ 7
theorem priceScale_mul : priceScale * ((2 ^ 31 : ℕ) : ENNReal) = (A : ENNReal) := by
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold priceScale; finiteness) (by finiteness)).mp
  unfold priceScale
  norm_num [A, ENNReal.toReal_mul, ENNReal.toReal_div]
theorem priceScale_ne_top : priceScale ≠ ⊤ := by unfold priceScale; finiteness
section Law
variable {β : Type} [Fintype β] {C : Type} [Fintype C] [DecidableEq C]
structure LawOK (vc : (Fin 9 → C × β) → ENNReal) (κ : ENNReal) : Prop where
  sum_one : ∑ x, vc x = 1
  density : ∀ x, vc x ≤ κ * (Fintype.card (Fin 9 → C × β) : ENNReal)⁻¹
  one_le : 1 ≤ κ
  rate : ((2 ^ 32 : ℕ) : ENNReal) * (2 ^ 31 : ENNReal)⁻¹ * κ ≤ (LN : ENNReal) / LD
noncomputable def priceN (val : β → Fin 6 → ℕ) (W : List (Fin (2 ^ 31) × (Fin 9 → C × β))) : ENNReal :=
  priceScale * ∑ index : Fin (2 ^ 31), env (n := 9) val (atIndex index W)
noncomputable def nearPriceN (val : β → Fin 6 → ℕ) (W : List (Fin (2 ^ 31) × (Fin 9 → C × β))) : ENNReal :=
  priceScale * ∑ index : Fin (2 ^ 31), ∑ k : Fin 9, ∑ t : Fin 6, nearEnv val k t (atIndex index W)
variable (val : β → Fin 6 → ℕ) {vc : (Fin 9 → C × β) → ENNReal} {κ : ENNReal}
omit [DecidableEq C] in
theorem rate_window (hlaw : LawOK vc κ) {T : ℕ} (hT : T ≤ 2 ^ 32) :
    (T : ENNReal) * (2 ^ 31 : ENNReal)⁻¹ * κ ≤ (LN : ENNReal) / LD := by
  refine le_trans ?_ hlaw.rate
  gcongr
theorem card_index : (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹ = (2 ^ 31 : ENNReal)⁻¹ := by
  rw [Fintype.card_fin]; norm_num
theorem law_env_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128) (h₁ : W1Table val)
    (hlaw : LawOK vc κ) (r : ℕ) :
    lawAvg vc r (env (n := 9) (C := C) val) ≤ κ ^ r * (((xNum r ^ 9 : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  rw [← env_moment val hβ hC h₁ r]
  exact lawAvg_le_uniform vc κ hlaw.density r _
theorem law_env_le_one (hlaw : LawOK vc κ) (r : ℕ) : lawAvg vc r (env (n := 9) (C := C) val) ≤ 1 :=
  (lawAvg_mono vc r (env_le_one val)).trans_eq (lawAvg_const vc hlaw.sum_one r 1)
theorem law_env_sq_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128) (h₁ : W1Table val)
    (h₂ : W2Table val) (hlaw : LawOK vc κ) (r : ℕ) :
    lawAvg vc r (fun L => env (n := 9) (C := C) val L ^ 2) ≤
      κ ^ r * (((yNum r ^ 9 : ℕ) : ENNReal) / (((Kc * Nn ^ 2) ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  rw [← env_sq_moment val hβ hC h₁ h₂ r]
  exact lawAvg_le_uniform vc κ hlaw.density r _
theorem law_env_sq_le_one (hlaw : LawOK vc κ) (r : ℕ) :
    lawAvg vc r (fun L => env (n := 9) (C := C) val L ^ 2) ≤ 1 :=
  (lawAvg_mono vc r fun L => pow_le_one₀ zero_le (env_le_one val L)).trans_eq (lawAvg_const vc hlaw.sum_one r 1)
theorem law_price_mean_eq (hlaw : LawOK vc κ) (T : ℕ) :
    lawAvg (marked (α := Fin (2 ^ 31)) vc) T (priceN val) =
      (A : ENNReal) * binomialAverage (2 ^ 31 : ENNReal)⁻¹ T (fun r => lawAvg vc r (env (n := 9) (C := C) val)) := by
  unfold priceN
  rw [lawAvg_mul_left, lawAvg_sum]
  simp_rw [law_marked_atIndex vc hlaw.sum_one, card_index]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← priceScale_mul]
section Window
variable {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32)
include hT1 hT2
theorem law_price_mean_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128) (h₁ : W1Table val)
    (hlaw : LawOK vc κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) vc) T (priceN val) ≤ 675 / 1000 := by
  rw [law_price_mean_eq val hlaw]
  have h := poissonCheckQ_sound_tilt (Qv := Q) (f := fun r => xNum r ^ 9) (dbase := Nn ^ 9) (sn := A) (sd := 1)
    (Mn := 675) (Md := 1000) mean_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) rate_le_one κ hlaw.one_le (rate_window hlaw hT2) (rejection_window_sharp T hT1) _
    (fun r _ => law_env_le val hβ hC h₁ hlaw r) (fun r _ => law_env_le_one val hlaw r)
  simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using h
end Window
theorem priceScale_sq_mul : priceScale ^ 2 * ((2 ^ 31 : ℕ) : ENNReal) = (A : ENNReal) ^ 2 / 2 ^ 31 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold priceScale; finiteness) (by finiteness)).mp
  unfold priceScale
  norm_num [A, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]
theorem law_diag_eq (hlaw : LawOK vc κ) (T : ℕ) :
    priceScale ^ 2 * ∑ index : Fin (2 ^ 31), lawAvg (marked (α := Fin (2 ^ 31)) vc) T
        (fun W => env (n := 9) (C := C) val (atIndex index W) ^ 2) =
      (A : ENNReal) ^ 2 / 2 ^ 31 * binomialAverage (2 ^ 31 : ENNReal)⁻¹ T
        (fun r => lawAvg vc r (fun L => env (n := 9) (C := C) val L ^ 2)) := by
  simp_rw [law_marked_atIndex vc hlaw.sum_one _ T (fun L => env (n := 9) (C := C) val L ^ 2), card_index]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← priceScale_sq_mul]
theorem theta_excess_le_square_v5 (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 675 / 1000) :
    (1296 / 1000) * (value - 1023 / 1024) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 := by
  have hmf : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
  have hmr : mean.toReal ≤ 675 / 1000 := by
    have h := (ENNReal.toReal_le_toReal hmf (by finiteness)).mpr hmean
    simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using h
  have hm0 : 0 ≤ mean.toReal := ENNReal.toReal_nonneg
  by_cases hsmall : value ≤ 1023 / 1024
  · rw [tsub_eq_zero_of_le hsmall, mul_zero, zero_add]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_add,
      ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal)]
  · have hlarge : 1023 / 1024 ≤ value := le_of_not_ge hsmall
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hlarge hvalue, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal - 81 / 125)]
theorem priceN_ne_top (W : List (Fin (2 ^ 31) × (Fin 9 → C × β))) : priceN val W ≠ ⊤ := by
  unfold priceN
  exact ENNReal.mul_ne_top priceScale_ne_top
    (ENNReal.sum_ne_top.mpr fun index _ => ne_top_of_le_ne_top ENNReal.one_ne_top (env_le_one val _))
section Window2
variable {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32)
include hT1 hT2
theorem law_price_second_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 563)
    (hC : Fintype.card C = 128) (h₁ : W1Table val) (h₂ : W2Table val) (hlaw : LawOK vc κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) vc) T (fun W => priceN val W ^ 2) ≤
      lawAvg (marked (α := Fin (2 ^ 31)) vc) T (priceN val) ^ 2 + 3200 / 1000000 := by
  set M := marked (α := Fin (2 ^ 31)) vc
  have hsq := lawAvg_sum_square_le M T (fun index W => env (n := 9) (C := C) val (atIndex index W))
    (fun first second hne => law_marked_negative_correlation vc hlaw.sum_one first second hne T _ _
      (env_cons_le val) (env_cons_le val))
  have hmean : lawAvg M T (priceN val) =
      priceScale * ∑ index : Fin (2 ^ 31), lawAvg M T (fun W => env (n := 9) (C := C) val (atIndex index W)) := by
    unfold priceN; rw [lawAvg_mul_left, lawAvg_sum]
  have hcheck := poissonCheckQ_sound_tilt (Qv := Q) (f := fun r => yNum r ^ 9) (dbase := (Kc * Nn ^ 2) ^ 9)
    (sn := A ^ 2) (sd := 2 ^ 31) (Mn := 3200) (Md := 1000000) diag_ok (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rate_le_one κ hlaw.one_le (rate_window hlaw hT2) (rejection_window_sharp T hT1) _
    (fun r _ => law_env_sq_le val hβ hC h₁ h₂ hlaw r) (fun r _ => law_env_sq_le_one val hlaw r)
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hcheck
  calc lawAvg M T (fun W => priceN val W ^ 2)
      = priceScale ^ 2 * lawAvg M T (fun W => (∑ index : Fin (2 ^ 31), env (n := 9) (C := C) val (atIndex index W)) ^ 2) := by
        unfold priceN; simp_rw [mul_pow]; rw [lawAvg_mul_left]
    _ ≤ priceScale ^ 2 * ((∑ index : Fin (2 ^ 31), lawAvg M T (fun W => env (n := 9) (C := C) val (atIndex index W))) ^ 2 +
          ∑ index : Fin (2 ^ 31), lawAvg M T (fun W => env (n := 9) (C := C) val (atIndex index W) ^ 2)) :=
        mul_le_mul' le_rfl hsq
    _ = lawAvg M T (priceN val) ^ 2 + priceScale ^ 2 *
          ∑ index : Fin (2 ^ 31), lawAvg M T (fun W => env (n := 9) (C := C) val (atIndex index W) ^ 2) := by
        rw [hmean]; ring
    _ ≤ _ := by
        rw [law_diag_eq val hlaw T]
        exact add_le_add le_rfl hcheck
theorem law_price_excess_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 563)
    (hC : Fintype.card C = 128) (h₁ : W1Table val) (h₂ : W2Table val) (hlaw : LawOK vc κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) vc) T (fun W => priceN val W - 1023 / 1024) ≤ 247 / 100000 := by
  set M := marked (α := Fin (2 ^ 31)) vc
  have hmean := law_price_mean_le val hT1 hT2 hβ hC h₁ hlaw
  have hsecond := law_price_second_le val hT1 hT2 hβ hC h₁ h₂ hlaw
  set mean := lawAvg M T (priceN val)
  have hm : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
  have h := lawAvg_mono M T (fun W : List (Fin (2 ^ 31) × (Fin 9 → C × β)) =>
    theta_excess_le_square_v5 (priceN val W) mean (priceN_ne_top val W) hmean)
  rw [lawAvg_add, lawAvg_add, lawAvg_mul_left, lawAvg_mul_left,
    lawAvg_const M (marked_sum_one vc hlaw.sum_one) T] at h
  have hcancel : (1296 / 1000 : ENNReal) * lawAvg M T (fun W => priceN val W - 1023 / 1024) ≤ 3200 / 1000000 := by
    apply ENNReal.le_of_add_le_add_right (a := 2 * mean ^ 2) (by finiteness)
    calc
      _ = (1296 / 1000 : ENNReal) * lawAvg M T (fun W => priceN val W - 1023 / 1024) + 2 * mean * mean := by ring
      _ ≤ lawAvg M T (fun W => priceN val W ^ 2) + mean ^ 2 := h
      _ ≤ (mean ^ 2 + 3200 / 1000000) + mean ^ 2 := add_le_add hsecond le_rfl
      _ = _ := by ring
  have hi : (1000 / 1296 : ENNReal) * (1296 / 1000) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  calc
    _ = (1000 / 1296 : ENNReal) * ((1296 / 1000) * lawAvg M T (fun W => priceN val W - 1023 / 1024)) := by
        rw [← mul_assoc, hi, one_mul]
    _ ≤ (1000 / 1296 : ENNReal) * (3200 / 1000000) := mul_le_mul' le_rfl hcancel
    _ ≤ _ := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
end Window2
theorem law_nearEnv_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128)
    (h₁ : W1Table val) (hf : ∀ i, WFTable val i) (hlaw : LawOK vc κ) (k : Fin 9) (t : Fin 6) (r : ℕ) :
    lawAvg vc r (nearEnv (C := C) val k t) ≤
      κ ^ r * (((xNum r ^ 8 * xfNum t r : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  rw [← nearEnv_moment val k t hβ hC h₁ (hf t) r]
  exact lawAvg_le_uniform vc κ hlaw.density r _
theorem xfSum_eq (r : ℕ) : xfSum r = ∑ t : Fin 6, xfNum t r := by
  rw [Fin.sum_univ_six]; rfl
noncomputable def nearLoad (r : ℕ) : ENNReal :=
  (54 : ENNReal)⁻¹ * ∑ k : Fin 9, ∑ t : Fin 6, lawAvg vc r (nearEnv (C := C) val k t)
theorem nearLoad_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128)
    (h₁ : W1Table val) (hf : ∀ i, WFTable val i) (hlaw : LawOK vc κ) (r : ℕ) :
    nearLoad val (vc := vc) r ≤
      κ ^ r * (((xNum r ^ 8 * xfSum r : ℕ) : ENNReal) / ((6 * Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  unfold nearLoad
  set D : ENNReal := ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)
  have hD0 : D ≠ 0 := by simp [D, Nn, Q]
  have hDt : D ≠ ⊤ := ENNReal.natCast_ne_top _
  calc (54 : ENNReal)⁻¹ * ∑ k : Fin 9, ∑ t : Fin 6, lawAvg vc r (nearEnv (C := C) val k t)
      ≤ (54 : ENNReal)⁻¹ * ∑ _k : Fin 9, ∑ t : Fin 6, κ ^ r * (((xNum r ^ 8 * xfNum t r : ℕ) : ENNReal) / D) :=
        mul_le_mul' le_rfl (sum_le_sum fun k _ => sum_le_sum fun t _ => law_nearEnv_le val hβ hC h₁ hf hlaw k t r)
    _ = κ ^ r * (((xNum r ^ 8 * xfSum r : ℕ) : ENNReal) / (6 * D)) := by
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
theorem nearLoad_le_one (hlaw : LawOK vc κ) (r : ℕ) : nearLoad val (vc := vc) (C := C) r ≤ 1 := by
  unfold nearLoad
  calc (54 : ENNReal)⁻¹ * ∑ k : Fin 9, ∑ t : Fin 6, lawAvg vc r (nearEnv (C := C) val k t)
      ≤ (54 : ENNReal)⁻¹ * ∑ _k : Fin 9, ∑ _t : Fin 6, (1 : ENNReal) :=
        mul_le_mul' le_rfl (sum_le_sum fun k _ => sum_le_sum fun t _ =>
          (lawAvg_mono vc r (nearEnv_le_one val k t)).trans_eq (lawAvg_const vc hlaw.sum_one r 1))
    _ = 1 := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        rw [show ((9 : ℕ) : ENNReal) * (6 : ℕ) = 54 by norm_num, ENNReal.inv_mul_cancel (by simp) (by simp)]
theorem law_nearPrice_mean_eq (hlaw : LawOK vc κ) (T : ℕ) :
    lawAvg (marked (α := Fin (2 ^ 31)) vc) T (nearPriceN val) =
      54 * (A : ENNReal) * binomialAverage (2 ^ 31 : ENNReal)⁻¹ T (nearLoad val (vc := vc) (C := C)) := by
  unfold nearPriceN nearLoad
  rw [lawAvg_mul_left, lawAvg_sum]
  simp_rw [lawAvg_sum, law_marked_atIndex vc hlaw.sum_one, card_index]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← priceScale_mul,
    binomialAverage_mul_left]
  simp_rw [← SphincsSecurity.Concrete.binomialAverage_sum]
  have h : (54 : ENNReal) * 54⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [← mul_assoc, show (54 : ENNReal) * (priceScale * ((2 ^ 31 : ℕ) : ENNReal)) * 54⁻¹ =
    (54 * 54⁻¹) * (priceScale * ((2 ^ 31 : ℕ) : ENNReal)) by ring, h, one_mul]
theorem law_nearPrice_le [SampleableType (Fin 9 → C × β)] {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32)
    (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128) (h₁ : W1Table val) (hf : ∀ i, WFTable val i)
    (hlaw : LawOK vc κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) vc) T (nearPriceN val) ≤ 291 / 1 := by
  rw [law_nearPrice_mean_eq val hlaw]
  have h := poissonCheckQ_sound_tilt (Qv := Q) (f := fun r => xNum r ^ 8 * xfSum r) (dbase := 6 * Nn ^ 9)
    (sn := 54 * A) (sd := 1) (Mn := 291) (Md := 1) near_ok (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) rate_le_one κ hlaw.one_le (rate_window hlaw hT2) (rejection_window_sharp T hT1) _
    (fun r _ => (nearLoad_le val hβ hC h₁ hf hlaw r).trans_eq (by push_cast; ring_nf))
    (fun r _ => nearLoad_le_one val hlaw r)
  simpa only [Nat.cast_one, div_one, Nat.cast_ofNat, Nat.cast_mul] using h
theorem near_le_sub : (291 / 1 : ENNReal) ≤ 300 - 1 / 16 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le (by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp; norm_num [ENNReal.toReal_div])
    (by finiteness)]
  norm_num [ENNReal.toReal_div]
noncomputable def uniformOn (S : Finset (Fin 9 → C × β)) (x : Fin 9 → C × β) : ENNReal :=
  open Classical in if x ∈ S then (S.card : ENNReal)⁻¹ else 0
theorem lawOK_uniformOn (S : Finset (Fin 9 → C × β)) (hS : S.Nonempty)
    (hrate : 10 ^ 8 * 2 ^ 32 * Fintype.card (Fin 9 → C × β) ≤ 203317755 * 2 ^ 31 * S.card) :
    LawOK (uniformOn S) ((Fintype.card (Fin 9 → C × β) : ENNReal) / S.card) where
  sum_one := by
    classical
    unfold uniformOn
    rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, ENNReal.mul_inv_cancel (by simp [hS.ne_empty])
      (ENNReal.natCast_ne_top _)]
  density := fun x => by
    classical
    unfold uniformOn
    have hc : (Fintype.card (Fin 9 → C × β) : ENNReal) ≠ 0 := by
      have : 0 < Fintype.card (Fin 9 → C × β) := Fintype.card_pos_iff.mpr ⟨hS.choose⟩
      exact_mod_cast this.ne'
    split_ifs
    · rw [div_eq_mul_inv, mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel hc (ENNReal.natCast_ne_top _), one_mul]
    · exact zero_le
  one_le := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hS.ne_empty])) (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
    exact_mod_cast card_le_univ S
  rate := by
    have hS0 : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    apply (ENNReal.toReal_le_toReal (by
      refine ENNReal.mul_ne_top (by finiteness) (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp [hS.ne_empty])))
      (by unfold LN LD; finiteness)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_natCast, LN, LD,
      ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    have h : ((10 ^ 8 * 2 ^ 32 * Fintype.card (Fin 9 → C × β) : ℕ) : ℝ) ≤
        ((203317755 * 2 ^ 31 * S.card : ℕ) : ℝ) := by exact_mod_cast hrate
    push_cast at h ⊢
    set c : ℝ := (Fintype.card (Fin 9 → C × β) : ℝ)
    set t : ℝ := (S.card : ℝ)
    rw [show (4294967296 : ℝ) * (2 ^ 31)⁻¹ * (c / t) = (10 ^ 8 * 2 ^ 32 * c) / (10 ^ 8 * 2 ^ 31 * t) by
      field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    linarith
theorem lawOK_uniformOn' (S : Finset (Fin 9 → C × β)) (hS : S.Nonempty) (Ncoords Ns : ℕ)
    (hcard : Fintype.card (Fin 9 → C × β) = Ncoords) (hNs : S.card = Ns)
    (hrate : 10 ^ 8 * 2 ^ 32 * Ncoords ≤ 203317755 * 2 ^ 31 * Ns) :
    LawOK (uniformOn S) ((Ncoords : ENNReal) / Ns) := by
  have h := lawOK_uniformOn S hS (by rw [hcard, hNs]; exact hrate)
  rwa [hcard, hNs] at h
section Uniform
variable [SampleableType (Fin 9 → C × β)] [SampleableType (Fin (2 ^ 31) × (Fin 9 → C × β))]
end Uniform
end Law
end ClaudeWCT.Numerics.N600
end

namespace ClaudeWCT.Numerics.Winsor
open ENNReal Finset
open ClaudeWCT.Numerics.Law

/-- The rational constant is a convenient upper bound on `1 / exp 1`. -/
theorem linear_le_exp (x : ℝ) : x ≤ (3 / 8) * Real.exp x := by
  have hx : x ≤ Real.exp (x - 1) := by simpa using Real.add_one_le_exp (x - 1)
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hmul : Real.exp (x - 1) * Real.exp 1 = Real.exp x := by rw [← Real.exp_add]; congr 1; ring
  have hnonneg := (Real.exp_pos (x - 1)).le
  nlinarith [mul_le_mul_of_nonneg_left he hnonneg]

theorem cap_exp_majorant (c : ENNReal) (hc : c ≠ ⊤) :
    c ≤ 2031 / 1024 + (3 / 64) * ENNReal.ofReal (Real.exp (-(2031 / 128))) *
      ENNReal.ofReal (Real.exp (8 * c.toReal)) := by
  apply (ENNReal.toReal_le_toReal hc (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  have h := linear_le_exp (8 * c.toReal - 2031 / 128)
  have hexp : Real.exp (8 * c.toReal - 2031 / 128) =
      Real.exp (-(2031 / 128)) * Real.exp (8 * c.toReal) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp] at h
  nlinarith

theorem tail_constant_le :
    (3 / 64 : ENNReal) * ENNReal.ofReal (Real.exp (-(2031 / 128))) *
      ENNReal.ofReal (Real.exp 8) ≤ 3 / 100000 := by
  have hlow : (3125 / 2 : ℝ) ≤ Real.exp (1007 / 128) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1007 / 128) 16)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have he : Real.exp (-(2031 / 128)) * Real.exp 8 = (Real.exp (1007 / 128))⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]; congr 1; ring
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  rw [mul_assoc, he]
  have hinv : (Real.exp (1007 / 128))⁻¹ ≤ 2 / 3125 := by
    have h := (inv_le_inv₀ (Real.exp_pos (1007 / 128)) (by norm_num : (0 : ℝ) < 3125 / 2)).2 hlow
    norm_num at h
    exact h
  nlinarith

/-- A capped exponential moment and the discarded first moment suffice for the
FTS stop-loss estimate.  This statement is independent of the coverage counting. -/
theorem excess_le_of_capped_exp {β : Type} [Fintype β] (v : β → ENNReal) (T : ℕ)
    (price capped residual : List β → ENNReal)
    (hcapped : ∀ W, capped W ≠ ⊤)
    (hsplit : ∀ W, price W ≤ capped W + residual W)
    (hexp : lawAvg v T (fun W => ENNReal.ofReal (Real.exp (8 * (capped W).toReal))) ≤
      ENNReal.ofReal (Real.exp 8))
    (hres : lawAvg v T residual ≤ 1 / 5000) :
    lawAvg v T (fun W => price W - 2031 / 1024) ≤ 23 / 100000 := by
  let a : ENNReal := (3 / 64) * ENNReal.ofReal (Real.exp (-(2031 / 128)))
  have hpoint : ∀ W, price W - 2031 / 1024 ≤
      a * ENNReal.ofReal (Real.exp (8 * (capped W).toReal)) + residual W := by
    intro W
    apply (tsub_le_iff_right).2
    calc
      price W ≤ capped W + residual W := hsplit W
      _ ≤ (2031 / 1024 + a * ENNReal.ofReal (Real.exp (8 * (capped W).toReal))) + residual W :=
        add_le_add (cap_exp_majorant (capped W) (hcapped W)) le_rfl
      _ = _ := by ac_rfl
  calc
    lawAvg v T (fun W => price W - 2031 / 1024)
        ≤ lawAvg v T (fun W => a * ENNReal.ofReal (Real.exp (8 * (capped W).toReal)) + residual W) :=
      lawAvg_mono v T hpoint
    _ = a * lawAvg v T (fun W => ENNReal.ofReal (Real.exp (8 * (capped W).toReal))) +
        lawAvg v T residual := by rw [lawAvg_add, lawAvg_mul_left]
    _ ≤ a * ENNReal.ofReal (Real.exp 8) + 1 / 5000 :=
      add_le_add (mul_le_mul' le_rfl hexp) hres
    _ ≤ 3 / 100000 + 1 / 5000 := add_le_add tail_constant_le le_rfl
    _ = 23 / 100000 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div,
        ENNReal.toReal_ofNat, ENNReal.toReal_inv]
      norm_num

end ClaudeWCT.Numerics.Winsor

namespace ClaudeWCT.Numerics.N600
open ENNReal Finset
open ClaudeWCT.Numerics.Law
open ClaudeWCT.Numerics.Thinning (env ListCov)
open SigGolfCandidate.T3.BPORS.History (atIndex)

section WinsorInterface
variable {β : Type} [Fintype β] {C : Type} [Fintype C] [DecidableEq C]

noncomputable def bucketPrice (val : β → Fin 6 → ℕ) (L : List (Fin 9 → C × β)) : ENNReal :=
  priceScale * env val L
noncomputable def bucketCapped (val : β → Fin 6 → ℕ) (L : List (Fin 9 → C × β)) : ENNReal :=
  min (bucketPrice val L) 1
noncomputable def bucketResidual (val : β → Fin 6 → ℕ) (L : List (Fin 9 → C × β)) : ENNReal :=
  bucketPrice val L - 1
noncomputable def bucketExpIncrement (val : β → Fin 6 → ℕ) (L : List (Fin 9 → C × β)) : ENNReal :=
  ENNReal.ofReal (Real.exp (8 * (bucketCapped val L).toReal)) - 1

theorem env_insert_le (val : β → Fin 6 → ℕ) (L R : List (Fin 9 → C × β)) (b : Fin 9 → C × β) :
    env val (L ++ R) ≤ env val (L ++ b :: R) := by
  unfold env SigGolfResearch.Gate6.Moments.finiteAverage
  refine ENNReal.div_le_div_right (Finset.sum_le_sum fun t _ => ?_) _
  split_ifs with h₁ h₂
  · exact le_rfl
  · apply absurd ?_ h₂
    intro k i
    obtain ⟨e, he, h'⟩ := h₁ k i
    refine ⟨e, ?_, h'⟩
    rcases List.mem_append.mp he with he | he
    · exact List.mem_append.mpr (Or.inl he)
    · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem b he))
  · exact zero_le_one
  · exact le_rfl

/-- The complete analytic FTS tail theorem, parameterized only by two one-bucket
numerical bounds.  Finite coverage counting supplies these hypotheses. -/
theorem law_price_excess_le_winsor (val : β → Fin 6 → ℕ)
    {vc : (Fin 9 → C × β) → ENNReal} {κ : ENNReal} (hlaw : LawOK vc κ) (T : ℕ)
    (hmgf : (2 ^ 31 : ENNReal) * coordAverage (2 ^ 31 : ENNReal)⁻¹ vc T
      (bucketExpIncrement val) ≤ 8)
    (hres : (2 ^ 31 : ENNReal) * coordAverage (2 ^ 31 : ENNReal)⁻¹ vc T
      (bucketResidual val) ≤ 1 / 5000) :
    lawAvg (marked (α := Fin (2 ^ 31)) vc) T (fun W => priceN val W - 2031 / 1024) ≤
      23 / 100000 := by
  let cap : List (Fin (2 ^ 31) × (Fin 9 → C × β)) → ENNReal :=
    fun W => ∑ i : Fin (2 ^ 31), bucketCapped val (atIndex i W)
  let res : List (Fin (2 ^ 31) × (Fin 9 → C × β)) → ENNReal :=
    fun W => ∑ i : Fin (2 ^ 31), bucketResidual val (atIndex i W)
  apply ClaudeWCT.Numerics.Winsor.excess_le_of_capped_exp
    (marked (α := Fin (2 ^ 31)) vc) T (priceN val) cap res
  · intro W
    exact ENNReal.sum_ne_top.mpr fun i _ => ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  · intro W
    change priceScale * (∑ i : Fin (2 ^ 31), env val (atIndex i W)) ≤ _
    rw [Finset.mul_sum]
    change (∑ i : Fin (2 ^ 31), bucketPrice val (atIndex i W)) ≤ _
    change _ ≤ (∑ i : Fin (2 ^ 31), bucketCapped val (atIndex i W)) +
      ∑ i : Fin (2 ^ 31), bucketResidual val (atIndex i W)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact le_of_eq (by rw [bucketCapped, bucketResidual, add_comm, tsub_add_min])
  · apply law_marked_exp_sum_le vc hlaw.sum_one T (fun _ L => bucketCapped val L)
    · intro i L; exact min_le_right _ _
    · intro i L b R
      exact min_le_min (mul_le_mul' le_rfl (env_insert_le val L R b)) le_rfl
    · change (2 ^ 31 : ENNReal) * coordAverage (2 ^ 31 : ENNReal)⁻¹ vc T
        (fun L => ENNReal.ofReal (Real.exp (8 * (bucketCapped val L).toReal)) - 1) ≤ 8 at hmgf
      simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul] using hmgf
  · change lawAvg (marked (α := Fin (2 ^ 31)) vc) T
      (fun W => ∑ i : Fin (2 ^ 31), bucketResidual val (atIndex i W)) ≤ _
    rw [lawAvg_sum]
    simp_rw [law_marked_atIndex vc hlaw.sum_one]
    simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, coordAverage] using hres

end WinsorInterface
end ClaudeWCT.Numerics.N600


namespace ClaudeWCT.Numerics.Winsor
open Finset
/-- Independent coordinates preserve a retained weighted counting bound. -/
theorem tensor_retained_le {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq β]
    (label : α → β) (weight : α → ℕ) (retained : β → ℕ)
    (hret : ∀ b, retained b ≤ ∑ a, if label a=b then weight a else 0) (bs : ι → β) :
    (∏ i, retained (bs i)) ≤
      ∑ xs : ι → α, if (fun i => label (xs i)) = bs then ∏ i, weight (xs i) else 0 := by
  classical
  calc
    _ ≤ ∏ i, ∑ a, if label a=bs i then weight a else 0 :=
      prod_le_prod' fun i _ => hret (bs i)
    _ = _ := by
      rw [Fintype.prod_sum]
      apply sum_congr rfl
      intro xs _
      by_cases h : (fun i => label (xs i)) = bs
      · rw [if_pos h]
        apply prod_congr rfl
        intro i _
        simp [congrFun h i]
      · rw [if_neg h]
        have he : ∃ i, label (xs i) ≠ bs i := by simpa only [funext_iff, not_forall] using h
        obtain ⟨i, hi⟩ := he
        exact prod_eq_zero (mem_univ i) (if_neg hi)
end ClaudeWCT.Numerics.Winsor

namespace ClaudeWCT.Numerics.N600
open Finset Polynomial
/-- Radix extraction is exact because the retained polynomial's total mass fits. -/
theorem coverageRetainedCoeff_eq (r c : ℕ) (hm : coverageRetainedPack 1 r < 2^512) :
    coverageRetainedCoeff r c = (retainedCoveragePoly r).coeff c := by
  unfold coverageRetainedCoeff
  rw [← retainedCoveragePoly_eval r (2^512)]
  apply ClaudeWCT.Numerics.eval_div_pow_mod (by positivity)
  intro a
  exact (ClaudeWCT.Numerics.coeff_le_eval_one _ a).trans_lt
    ((retainedCoveragePoly_eval r 1).trans_lt hm)
noncomputable def coverageBinnedPoly (r : ℕ) : ℕ[X] :=
  ∑ c ∈ range 4096, C ((retainedCoveragePoly r).coeff c) * X ^ coverageBin c
/-- Shift extraction is used only as an efficient form of the proved radix identity. -/
theorem coverageBinnedPoly_eval (r b : ℕ) (hm : coverageRetainedPack 1 r < 2^512) :
    (coverageBinnedPoly r).eval b = coverageBinnedPack b r := by
  unfold coverageBinnedPoly coverageBinnedPack
  dsimp only
  have hs (n v a : ℕ) : (if n=0 then a else n*v+a) = n*v+a := by
    split_ifs with h
    · simp [h]
    · rfl
  simp only [hs]
  rw [ClaudeWCT.Numerics.PoissonReflect.range_foldr_eq_sum]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply sum_congr rfl
  intro c _
  have hc : ((coverageRetainedPack (2^512) r >>> (512*c)) % (2^512)) =
      (retainedCoveragePoly r).coeff c := by
    rw [Nat.shiftRight_eq_div_pow, pow_mul]
    exact coverageRetainedCoeff_eq r c hm
  rw [hc]
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
set_option maxHeartbeats 4000000 in
theorem coveragePrepared_eq (b : ℕ) : coveragePrepared b =
    coverageProfiles.map (fun ms => (ms, coverageProfilePack b ms)) := by
  simp [coveragePrepared, coverageProfiles, coverageProfilePackWith, coverageProfilePack,
    List.range_succ, List.zipIdx]
theorem coverageOtherPrepared_eq (b n : ℕ) :
    coverageOtherPrepared b (coveragePrepared b) n = coverageOtherPack b n := by
  rw [coveragePrepared_eq]
  simp [coverageOtherPrepared, coverageOtherPack, List.foldr_map]
theorem coverageRetainedFastPack_eq (b r : ℕ) :
    coverageRetainedFastPack b r = coverageRetainedPack b r := by
  simp only [coverageRetainedFastPack, coverageOtherPrepared_eq, coverageRetainedPack]
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open Finset Polynomial
variable {β C : Type} [Fintype β] [Fintype C] [DecidableEq C]
theorem fullCoverage_card_product {r n : ℕ} (val : β → Fin 6 → ℕ) (E : Fin r → Fin n → C × β) :
    #{t : Fin n → C × β | ClaudeWCT.Numerics.Thinning.FullCov val t E} =
      ∏ k, coordinateCoverage val (fun j => E j k) := by
  classical
  simp only [coordinateCoverage, card_filter]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro t _
  simp only [Fintype.prod_ite_zero, prod_const_one, ClaudeWCT.Numerics.Thinning.FullCov]
  exact congrArg (fun d : Decidable (∀ k, ClaudeWCT.Numerics.Thinning.CovAt val
    (t k).1 (val (t k).2) (fun m => E m k)) => @ite ℕ _ d 1 0) (Subsingleton.elim _ _)
theorem bucketPrice_ofFn {r : ℕ} (val : β → Fin 6 → ℕ)
    (hβ : Fintype.card β=563) (hC : Fintype.card C=128) (E : Fin r → Fin 9 → C × β) :
    bucketPrice val (List.ofFn E) = (1353 / 2^70 : ENNReal) *
      ((∏ k, coordinateCoverage val (fun j => E j k) : ℕ) : ENNReal) := by
  classical
  unfold bucketPrice ClaudeWCT.Numerics.Thinning.env SigGolfResearch.Gate6.Moments.finiteAverage
  simp_rw [ClaudeWCT.Numerics.Thinning.listCov_ofFn]
  rw [← Finset.natCast_card_filter, fullCoverage_card_product]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, hC, hβ]
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold priceScale; finiteness) (by finiteness)).mp
  simp only [priceScale, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  norm_num
  ring
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.Winsor
open Finset
noncomputable def taylor16 (x : ℝ) : ℝ :=
  (∑ i ∈ range 16, x^i / (i.factorial : ℝ)) + 17*x^16 / ((16:ℕ).factorial*16)
theorem exp8_le_taylor16 (x : ℝ) (h0 : 0≤x) (h1 : x≤1) : Real.exp (8*x) ≤ taylor16 x ^ 8 := by
  have h := Real.exp_bound' h0 h1 (n:=16) (by norm_num)
  have he : Real.exp x ≤ taylor16 x := by
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
    convert h using 1 <;> norm_num [taylor16, mul_comm]
  rw [show (8:ℝ)*x=(8:ℕ)*x by norm_num, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_nonneg x) he 8
theorem exp8_le_3001 : Real.exp 8 ≤ 3001 := by
  have h := exp8_le_taylor16 1 (by norm_num) (by norm_num)
  norm_num [taylor16, Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact h.trans (by norm_num)
end ClaudeWCT.Numerics.Winsor

namespace ClaudeWCT.Numerics.N600
theorem coverageHPackBits_eq (bits j : ℕ) : coverageHPackBits bits j = coverageHPack (2^bits) j := by
  simp only [coverageHPackBits, coverageHPack, Nat.shiftLeft_eq, pow_mul]
theorem coverageMarkedPackBits_eq (bits j : ℕ) :
    coverageMarkedPackBits bits j = coverageMarkedPack (2^bits) j := by
  simp only [coverageMarkedPackBits, coverageMarkedPack, Nat.shiftLeft_eq, pow_mul]
theorem coveragePreparedBits_eq (bits : ℕ) : coveragePreparedBits bits = coveragePrepared (2^bits) := by
  have hh : coverageHPackBits bits = coverageHPack (2^bits) := funext (coverageHPackBits_eq bits)
  simp only [coveragePreparedBits, coveragePrepared, hh]
theorem coverageOtherBits_eq (bits n : ℕ) (prepared : List (List ℕ × ℕ)) :
    coverageOtherBits bits prepared n = coverageOtherPrepared (2^bits) prepared n := by
  unfold coverageOtherBits coverageOtherPrepared
  congr 1
  funext e acc
  split_ifs
  · rw [Nat.shiftLeft_eq, pow_mul]
    ring
  · rfl
theorem coverageRetainedBits_eq (bits r : ℕ) :
    coverageRetainedBits bits r = coverageRetainedPack (2^bits) r := by
  simp only [coverageRetainedBits, coveragePreparedBits_eq, coverageMarkedPackBits_eq,
    coverageOtherBits_eq, coverageOtherPrepared_eq, coverageRetainedPack]
theorem coverageBinnedBits_eq (bits r : ℕ) :
    coverageBinnedBits bits r = coverageBinnedPack (2^bits) r := by
  simp only [coverageBinnedBits, coverageRetainedBits_eq, coverageBinnedPack, Nat.shiftLeft_eq, pow_mul]
theorem coverageProductBits_eq (r : ℕ) : coverageProductBits r = coverageProductPack r := by
  simp only [coverageProductBits, coverageBinnedBits_eq, coverageProductPack]
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.Winsor
theorem cappedExp_le_linear (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (8 * min x 1) - 1 ≤ 3000*x := by
  by_cases h : x ≤ 1
  · rw [min_eq_left h]
    have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (8:ℝ))
      (show 0 ≤ 1-x by linarith) hx (show (1-x)+x=1 by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    rw [mul_comm x 8] at hc
    have h1 := mul_le_mul_of_nonneg_left exp8_le_3001 hx
    nlinarith
  · rw [min_eq_right (le_of_not_ge h)]
    norm_num only [mul_one]
    nlinarith [exp8_le_3001]

theorem cappedExp_le_of_interval (x L U p : ℝ)
    (hxL : L ≤ x) (hxU : x ≤ U) (hp : 0 ≤ p)
    (hpay : Real.exp (8*min U 1)-1 ≤ L*p) :
    Real.exp (8*min x 1)-1 ≤ x*p := by
  have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (min_le_min_right 1 hxU) (by norm_num : (0:ℝ)≤8))
  exact (sub_le_sub_right h 1).trans (hpay.trans (mul_le_mul_of_nonneg_right hxL hp))

theorem residual_le_of_interval (x L U p : ℝ)
    (hx : 0 ≤ x) (hxL : L ≤ x) (hxU : x ≤ U) (hp : 0 ≤ p)
    (hpay : max (U-1) 0 ≤ L*p) : max (x-1) 0 ≤ x*p := by
  exact (max_le_max_right 0 (sub_le_sub_right hxU 1)).trans
    (hpay.trans (mul_le_mul_of_nonneg_right hxL hp))
end ClaudeWCT.Numerics.Winsor

namespace ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Winsor
open Finset

theorem winsorCeil_mul_le (n d : ℕ) (hd : 0 < d) : n ≤ winsorCeil n d * d := by
  have he := Nat.mod_add_div (n+d-1) d
  have hr := Nat.mod_lt (n+d-1) hd
  unfold winsorCeil
  rw [Nat.mul_comm d] at he
  omega

theorem winsorCeil_ratio_le (n d : ℕ) (hd : 0 < d) :
    (n:ℝ)/(d:ℝ) ≤ (winsorCeil n d : ℝ) := by
  apply (div_le_iff₀ (by exact_mod_cast hd)).2
  exact_mod_cast winsorCeil_mul_le n d hd

def taylorNumN (S u : ℕ) : ℕ :=
  16 * (List.range 16).foldr (fun i acc =>
    (ClaudeWCT.Numerics.Kernel.fact 16 / ClaudeWCT.Numerics.Kernel.fact i) * u ^ i * S ^ (16-i) + acc) 0 + 17 * u ^ 16
def taylorDenN (S : ℕ) : ℕ := ClaudeWCT.Numerics.Kernel.fact 16 * 16 * S ^ 16
set_option maxHeartbeats 1000000 in
theorem taylorNumN_ratio (S u : ℕ) (hS : (S:ℝ) ≠ 0) :
    (taylorNumN S u : ℝ) / (taylorDenN S : ℝ) = taylor16 ((u:ℝ) / (S:ℝ)) := by
  norm_num [taylorNumN, taylorDenN, ClaudeWCT.Numerics.Kernel.fact,
    List.range_succ, List.foldr_append, taylor16, Finset.sum_range_succ, Nat.factorial]
  field_simp
  ring

theorem winsorExp_ratio (u : ℕ) :
    (winsorExpNum u : ℝ) / (winsorExpDen : ℝ) = taylor16 ((u:ℝ) / (winsorScale:ℝ)) :=
  taylorNumN_ratio winsorScale u (by norm_num [winsorScale])
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
set_option maxRecDepth 10000
open ClaudeWCT.Numerics.Winsor
open Finset

theorem taylorNumN_ge_den (S u : ℕ) : taylorDenN S ≤ taylorNumN S u := by
  unfold taylorNumN taylorDenN
  rw [List.range_succ_eq_map]
  simp only [List.foldr_cons, Kernel.fact, Nat.div_one, pow_zero, mul_one, Nat.sub_zero]
  rw [Nat.mul_add]
  omega

theorem winsorExpNum_ge_den (u : ℕ) : winsorExpDen ≤ winsorExpNum u :=
  taylorNumN_ge_den winsorScale u

theorem winsorRound_le (un ud : ℕ) (hud : 0 < ud) :
    min ((un:ℝ)/(ud:ℝ)) 1 ≤
      ((min winsorScale (winsorCeil (winsorScale*un) ud) : ℕ) : ℝ) / (winsorScale:ℝ) := by
  have hS : (0:ℝ) < winsorScale := by norm_num [winsorScale]
  have hc := winsorCeil_ratio_le (winsorScale*un) ud hud
  have hratio : (un:ℝ)/(ud:ℝ) ≤ (winsorCeil (winsorScale*un) ud:ℝ)/(winsorScale:ℝ) := by
    apply (le_div_iff₀ hS).2
    push_cast at hc
    calc
      _ = (winsorScale:ℝ)*(un:ℝ)/(ud:ℝ) := by ring
      _ ≤ _ := hc
  rw [Nat.cast_min, ← min_div_div_right (le_of_lt hS), div_self (ne_of_gt hS)]
  exact (min_le_min_right 1 hratio).trans_eq (min_comm _ _)

theorem payRatio_le (S D p a b m : ℝ) (hS : 0<S) (hD : 0<D) (hb : 0<b)
    (hh : S*(p^8-D^8)*b*51^9 ≤ m*D^8*a*50^9) :
    (p/D)^8-1 ≤ a/b*(50/51:ℝ)^9*(m/S) := by
  field_simp
  nlinarith

theorem winsorMGF_cross_pay (un ud m : ℕ) (hun : 0 < un) (hud : 0 < ud)
    (hpay : winsorScale * (winsorExpNum (min winsorScale (winsorCeil (winsorScale*un) ud)) ^ 8 - winsorExpDen ^ 8) * ud * 51^9 ≤
      m * winsorExpDen ^ 8 * un * 50^9) :
    Real.exp (8*min ((un:ℝ)/(ud:ℝ)) 1)-1 ≤
      ((un:ℝ)/(ud:ℝ)) * (50/51:ℝ)^9 * ((m:ℝ)/(winsorScale:ℝ)) := by
  let u := min winsorScale (winsorCeil (winsorScale*un) ud)
  have hS : (0:ℝ) < winsorScale := by norm_num [winsorScale]
  have hD : (0:ℝ) < winsorExpDen := by norm_num [winsorExpDen, winsorScale, Kernel.fact]
  have hudR : (0:ℝ)<ud := by exact_mod_cast hud
  have hu : (u:ℝ)/(winsorScale:ℝ) ≤ 1 := by
    apply (div_le_iff₀ hS).2
    norm_num only [one_mul]
    exact_mod_cast min_le_left winsorScale (winsorCeil (winsorScale*un) ud)
  have hmono : Real.exp (8*min ((un:ℝ)/(ud:ℝ)) 1) ≤
      ((winsorExpNum u:ℝ)/(winsorExpDen:ℝ))^8 := by
    rw [winsorExp_ratio]
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (winsorRound_le un ud hud) (by norm_num))).trans
      (exp8_le_taylor16 _ (by positivity) hu)
  have hge : winsorExpDen^8 ≤ winsorExpNum u^8 := Nat.pow_le_pow_left (winsorExpNum_ge_den u) 8
  have hn : ((winsorExpNum u^8-winsorExpDen^8:ℕ):ℝ) =
      (winsorExpNum u:ℝ)^8-(winsorExpDen:ℝ)^8 := by
    rw [Nat.cast_sub hge, Nat.cast_pow, Nat.cast_pow]
  have hh : (winsorScale:ℝ) * ((winsorExpNum u:ℝ)^8-(winsorExpDen:ℝ)^8) * (ud:ℝ) * 51^9 ≤
      (m:ℝ) * (winsorExpDen:ℝ)^8 * (un:ℝ) * 50^9 := by
    have hc : (winsorScale:ℝ) * ((winsorExpNum u^8-winsorExpDen^8:ℕ):ℝ) * (ud:ℝ) * 51^9 ≤
        (m:ℝ) * (winsorExpDen:ℝ)^8 * (un:ℝ) * 50^9 := by exact_mod_cast hpay
    rwa [hn] at hc
  refine (sub_le_sub_right hmono 1).trans ?_
  exact payRatio_le _ _ _ _ _ _ hS hD hudR hh
theorem residualRatio_le (S a b t : ℝ) (hS : 0<S) (hb : 0<b)
    (hh : S*(a-b)*51^9 ≤ t*a*50^9) :
    a/b-1 ≤ a/b*(50/51:ℝ)^9*(t/S) := by
  field_simp
  nlinarith

theorem winsorResidual_cross_pay (un ud t : ℕ) (hud : 0 < ud)
    (hpay : winsorScale * (un-ud) * 51^9 ≤ t*un*50^9) :
    max ((un:ℝ)/(ud:ℝ)-1) 0 ≤
      ((un:ℝ)/(ud:ℝ)) * (50/51:ℝ)^9 * ((t:ℝ)/(winsorScale:ℝ)) := by
  by_cases h : un ≤ ud
  · have hr : (un:ℝ)/(ud:ℝ) ≤ 1 := (div_le_one (by positivity)).2 (by exact_mod_cast h)
    rw [max_eq_right (by linarith)]
    positivity
  · have hdu : ud ≤ un := by omega
    have hn : ((un-ud:ℕ):ℝ)=(un:ℝ)-(ud:ℝ) := Nat.cast_sub hdu
    have hh : (winsorScale:ℝ)*((un:ℝ)-(ud:ℝ))*51^9 ≤ (t:ℝ)*(un:ℝ)*50^9 := by
      have hc : (winsorScale:ℝ)*((un-ud:ℕ):ℝ)*51^9 ≤ (t:ℝ)*(un:ℝ)*50^9 := by exact_mod_cast hpay
      rwa [hn] at hc
    have hr : 1 ≤ (un:ℝ)/(ud:ℝ) := (one_le_div (by positivity)).2 (by exact_mod_cast hdu)
    rw [max_eq_left (by linarith)]
    exact residualRatio_le _ _ _ _ (by norm_num [winsorScale]) (by positivity) hh

end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Winsor
set_option maxRecDepth 10000

theorem winsorMGF_pay (un ud m : ℕ) (hud : 0 < ud) (x : ℝ) (hx : 0 ≤ x)
    (hlo : (un:ℝ)/(ud:ℝ)*(50/51:ℝ)^9 ≤ x) (hhi : x ≤ (un:ℝ)/(ud:ℝ))
    (hpay : m = 3000*winsorScale ∨
      winsorScale * (winsorExpNum (min winsorScale (winsorCeil (winsorScale*un) ud)) ^ 8 - winsorExpDen ^ 8) * ud * 51^9 ≤
        m * winsorExpDen ^ 8 * un * 50^9) :
    Real.exp (8*min x 1)-1 ≤ x*((m:ℝ)/(winsorScale:ℝ)) := by
  rcases hpay with hm|hm
  · rw [hm]
    norm_num [winsorScale]
    simpa [mul_comm] using cappedExp_le_linear x hx
  · by_cases hun : 0 < un
    · apply cappedExp_le_of_interval x ((un:ℝ)/(ud:ℝ)*(50/51:ℝ)^9) ((un:ℝ)/(ud:ℝ))
        ((m:ℝ)/(winsorScale:ℝ)) hlo hhi (by positivity)
      exact winsorMGF_cross_pay un ud m hun hud hm
    · have hu : un=0 := by omega
      rw [hu] at hhi
      norm_num at hhi
      have hzero : x=0 := le_antisymm hhi hx
      simp [hzero]

theorem winsorResidual_pay (un ud t : ℕ) (hud : 0 < ud) (x : ℝ) (hx : 0 ≤ x)
    (hlo : (un:ℝ)/(ud:ℝ)*(50/51:ℝ)^9 ≤ x) (hhi : x ≤ (un:ℝ)/(ud:ℝ))
    (hpay : t = winsorScale ∨ winsorScale*(un-ud)*51^9 ≤ t*un*50^9) :
    max (x-1) 0 ≤ x*((t:ℝ)/(winsorScale:ℝ)) := by
  rcases hpay with ht|ht
  · rw [ht, div_self (by norm_num [winsorScale]), mul_one]
    exact max_le (by linarith) hx
  · apply residual_le_of_interval x ((un:ℝ)/(ud:ℝ)*(50/51:ℝ)^9) ((un:ℝ)/(ud:ℝ))
      ((t:ℝ)/(winsorScale:ℝ)) hx hlo hhi (by positivity)
    exact winsorResidual_cross_pay un ud t hud ht

theorem winsorPayChecks_entry (h : winsorPayChecks = true) (m t b : ℕ)
    (he : ((m,t),b) ∈ (winsorMGFPayData.zip winsorResidualPayData).zipIdx) :
    (m = 3000*winsorScale ∨
      winsorScale * (winsorExpNum (min winsorScale (winsorCeil (winsorScale*(1353*51^b)) (2^70*50^b))) ^ 8 - winsorExpDen ^ 8) * (2^70*50^b) * 51^9 ≤
        m * winsorExpDen ^ 8 * (1353*51^b) * 50^9) ∧
    (t = winsorScale ∨ winsorScale*((1353*51^b)-(2^70*50^b))*51^9 ≤ t*(1353*51^b)*50^9) := by
  unfold winsorPayChecks at h
  have hh := List.all_eq_true.mp h ((m,t),b) he
  simpa only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] using hh
end ClaudeWCT.Numerics.N600

open Finset Polynomial
namespace ClaudeWCT.Numerics.N600
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def coveragePackedPairDots : List (ℕ × ℕ) → ℕ → ℕ × ℕ × ℕ
  | (m,t) :: ds, p =>
    let n := p % (2^4608)
    let v := coveragePackedPairDots ds (p / (2^4608))
    (n+v.1,n*m+v.2.1,n*t+v.2.2)
  | [], _ => (0,0,0)

theorem winsorPackedSums_eq_zip (m t : List ℕ) (p : ℕ) :
    winsorPackedSums m t p = coveragePackedPairDots (m.zip t) p := by
  induction m generalizing t p with
  | nil => simp [winsorPackedSums, coveragePackedPairDots]
  | cons m ms ih =>
    cases t with
    | nil => simp [winsorPackedSums, coveragePackedPairDots]
    | cons t ts => simp [winsorPackedSums, coveragePackedPairDots, ih]

noncomputable def coverageCoefficientDots (P : ℕ[X]) (ds : List (ℕ × ℕ)) (k : ℕ) : ℕ × ℕ × ℕ :=
  (ds.zipIdx k).foldr (fun e v =>
    (P.coeff e.2 + v.1, P.coeff e.2 * e.1.1 + v.2.1,
      P.coeff e.2 * e.1.2 + v.2.2)) (0,0,0)

theorem coveragePackedPairDots_eq (P : ℕ[X]) (hP : ∀ a, P.coeff a < 2^4608)
    (ds : List (ℕ × ℕ)) (k : ℕ) :
    coveragePackedPairDots ds (P.eval (2^4608) / (2^4608)^k) =
      coverageCoefficientDots P ds k := by
  induction ds generalizing k with
  | nil => simp [coveragePackedPairDots, coverageCoefficientDots]
  | cons e ds ih =>
    have hc := ClaudeWCT.Numerics.eval_div_pow_mod (B := 2^4608) (by positivity) k P hP
    have hd : P.eval (2^4608) / (2^4608)^k / 2^4608 = P.eval (2^4608) / (2^4608)^(k+1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ (2^4608) k]
    simp only [coveragePackedPairDots, hc, hd, ih, coverageCoefficientDots,
      List.zipIdx_cons, List.foldr_cons]

theorem winsorPackedSums_eq_coefficients (P : ℕ[X]) (hP : ∀ a, P.coeff a < 2^4608)
    (m t : List ℕ) :
    winsorPackedSums m t (P.eval (2^4608)) = coverageCoefficientDots P (m.zip t) 0 := by
  rw [winsorPackedSums_eq_zip]
  simpa using coveragePackedPairDots_eq P hP (m.zip t) 0

theorem sum_coeff_le_eval_one (P : ℕ[X]) (s : Finset ℕ) :
    (∑ a ∈ s, P.coeff a) ≤ P.eval 1 := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp only [one_pow, mul_one]
  exact Finset.sum_le_sum_of_ne_zero (fun a _ ha => Polynomial.mem_support_iff.mpr ha)

theorem binnedPower_coeff_lt (P : ℕ[X]) (s : Finset ℕ) (bin : ℕ → ℕ) (M : ℕ)
    (hP : P.eval 1 ≤ M) (hM : M < 2^512) (a : ℕ) :
    ((∑ c ∈ s, Polynomial.C (P.coeff c) * X ^ bin c : ℕ[X]) ^ 9).coeff a < 2^4608 := by
  let G : ℕ[X] := ∑ c ∈ s, Polynomial.C (P.coeff c) * X ^ bin c
  have hg : G.eval 1 ≤ M := by
    calc
      G.eval 1 = ∑ c ∈ s, P.coeff c := by simp only [G, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]
      _ ≤ P.eval 1 := sum_coeff_le_eval_one P s
      _ ≤ M := hP
  have hc := ClaudeWCT.Numerics.coeff_le_eval_one (G^9) a
  rw [Polynomial.eval_pow] at hc
  calc
    (G^9).coeff a ≤ (G.eval 1)^9 := hc
    _ ≤ M^9 := Nat.pow_le_pow_left hg 9
    _ < (2^512)^9 := Nat.pow_lt_pow_left hM (by decide)
    _ = 2^4608 := by rw [← pow_mul]
end ClaudeWCT.Numerics.N600

open Finset
namespace ClaudeWCT.Numerics.N600

theorem geometricBin_interval (c b : ℕ) (hc : 1 ≤ c) (hzero : c = 1 → b = 0)
    (hu : c*50^b ≤ 51^b) (hl : c ≤ 1 ∨ 51^(b-1) < c*50^(b-1)) :
    (51/50 : ℝ)^b * (50/51) ≤ (c : ℝ) ∧ (c : ℝ) ≤ (51/50 : ℝ)^b := by
  have hcR : (1:ℝ) ≤ c := by exact_mod_cast hc
  constructor
  · by_cases hb : b = 0
    · simp only [hb, pow_zero, one_mul]
      linarith
    · have hcl : ¬ c ≤ 1 := by
        intro h
        exact hb (hzero (by omega))
      have hL : (51 : ℝ)^(b-1) ≤ c*(50:ℝ)^(b-1) := by
        exact_mod_cast (hl.resolve_left hcl).le
      have hdiv : (51/50 : ℝ)^(b-1) ≤ c := by
        rw [div_pow]
        exact (div_le_iff₀ (by positivity)).2 hL
      have he : (51/50 : ℝ)^b * (50/51) = (51/50 : ℝ)^(b-1) := by
        conv_lhs => lhs; rw [show b = (b-1)+1 by omega, pow_succ]
        ring
      rw [he]
      exact hdiv
  · rw [div_pow]
    apply (le_div_iff₀ (by positivity)).2
    exact_mod_cast hu

theorem geometricBin_product_interval (c bins : Fin 9 → ℕ)
    (hs : ∀ k, (51/50 : ℝ)^(bins k)*(50/51) ≤ c k ∧
      (c k : ℝ) ≤ (51/50 : ℝ)^(bins k)) :
    let b := ∑ k, bins k
    let U := ((1353*51^b : ℕ):ℝ) / ((2^70*50^b : ℕ):ℝ)
    let x := (1353/2^70 : ℝ) * ∏ k, (c k : ℝ)
    U*(50/51 : ℝ)^9 ≤ x ∧ x ≤ U := by
  dsimp only
  have hlo : (∏ k, (51/50 : ℝ)^(bins k)*(50/51)) ≤ ∏ k, (c k : ℝ) := by
    exact Finset.prod_le_prod (fun _ _ => by positivity) (fun k _ => (hs k).1)
  have hhi : (∏ k, (c k : ℝ)) ≤ ∏ k, (51/50 : ℝ)^(bins k) := by
    exact Finset.prod_le_prod (fun _ _ => by positivity) (fun k _ => (hs k).2)
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Fin.prod_const] at hlo
  rw [Finset.prod_pow_eq_pow_sum] at hhi
  have hU : ((1353*51^(∑ k, bins k) : ℕ):ℝ) / ((2^70*50^(∑ k, bins k) : ℕ):ℝ) =
      (1353/2^70 : ℝ)*(51/50 : ℝ)^(∑ k, bins k) := by
    push_cast
    rw [div_pow]
    ring
  rw [hU]
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlo (show 0 ≤ (1353/2^70:ℝ) by positivity)
  · exact mul_le_mul_of_nonneg_left hhi (by positivity)
theorem coverageBin_one : coverageBin 1 = 0 := by decide +kernel

theorem coverageBin_interval_of_check (c : ℕ) (hc : 1 ≤ c) (hB : c < 4096)
    (hcheck : (List.range 4096).all (fun c =>
      c * 50 ^ coverageBin c ≤ 51 ^ coverageBin c &&
        (c ≤ 1 || 51 ^ (coverageBin c - 1) < c * 50 ^ (coverageBin c - 1))) = true) :
    (51/50 : ℝ)^(coverageBin c)*(50/51) ≤ (c:ℝ) ∧
      (c:ℝ) ≤ (51/50 : ℝ)^(coverageBin c) := by
  have hh := List.all_eq_true.mp hcheck c (List.mem_range.mpr hB)
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hh
  apply geometricBin_interval c (coverageBin c) hc
  · intro h
    subst c
    exact coverageBin_one
  · exact hh.1
  · exact hh.2

end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.Winsor
open Finset
set_option maxHeartbeats 1000000

theorem finite_bounded_payoff_le {α : Type*} [Fintype α]
    (weight fee : α → ℝ) (good : α → Prop) [DecidablePred good]
    (bin : α → ℕ) (retained pay : ℕ → ℝ) (M : ℝ) (B : ℕ)
    (hfee : ∀ a, fee a ≤ weight a * (if good a ∧ bin a < B then pay (bin a) else M))
    (hpay : ∀ b < B, pay b ≤ M)
    (hret : ∀ b < B, retained b ≤ ∑ a, if good a ∧ bin a = b then weight a else 0) :
    ∑ a, fee a ≤ (∑ b ∈ range B, retained b * pay b) +
      M * ((∑ a, weight a) - ∑ b ∈ range B, retained b) := by
  classical
  let discount (a : α) : ℝ := if good a ∧ bin a < B then weight a * (M-pay (bin a)) else 0
  have hd (a : α) : (∑ b ∈ range B, if good a ∧ bin a = b then weight a*(M-pay b) else 0) = discount a := by
    by_cases ha : good a ∧ bin a < B
    · rw [Finset.sum_eq_single (bin a)]
      · simp [discount, ha.1, ha.2]
      · intro b hb hne
        simp [Ne.symm hne]
      · simp [ha.2]
    · have hn (b : ℕ) (hb : b∈range B) : ¬(good a ∧ bin a=b) := by
        rintro ⟨hg,he⟩
        exact ha ⟨hg,he ▸ mem_range.mp hb⟩
      simp only [discount, if_neg ha]
      exact sum_eq_zero fun b hb => if_neg (hn b hb)
  have hdisc : (∑ b ∈ range B, retained b*(M-pay b)) ≤ ∑ a, discount a := by
    calc
      _ ≤ ∑ b ∈ range B, (∑ a, if good a ∧ bin a=b then weight a else 0)*(M-pay b) :=
        sum_le_sum fun b hb => mul_le_mul_of_nonneg_right (hret b (mem_range.mp hb))
          (sub_nonneg.mpr (hpay b (mem_range.mp hb)))
      _ = ∑ a, discount a := by
        simp_rw [sum_mul, ite_mul, zero_mul]
        rw [sum_comm]
        exact sum_congr rfl fun a _ => hd a
  have hp (a : α) : fee a ≤ M*weight a-discount a := by
    have h := hfee a
    by_cases ha : good a ∧ bin a < B
    · rw [if_pos ha] at h
      simp only [discount, if_pos ha]
      nlinarith
    · rw [if_neg ha] at h
      simpa [discount, ha, mul_comm] using h
  calc
    _ ≤ ∑ a, (M*weight a-discount a) := sum_le_sum fun a _ => hp a
    _ = M*(∑ a, weight a) - ∑ a, discount a := by rw [sum_sub_distrib, mul_sum]
    _ ≤ M*(∑ a, weight a) - ∑ b ∈ range B, retained b*(M-pay b) := by linarith
    _ = _ := by simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul]; ring
end ClaudeWCT.Numerics.Winsor

namespace ClaudeWCT.Numerics.N600
open Finset Polynomial
theorem finiteMonomialPower_coeff (D : ℕ → ℕ) (bin : ℕ → ℕ) (B n b : ℕ) :
    ((∑ c : Fin B, Polynomial.C (D c.val) * X ^ bin c.val : ℕ[X]) ^ n).coeff b =
      ∑ cs : Fin n → Fin B, if (∑ i, bin (cs i).val) = b then ∏ i, D (cs i).val else 0 := by
  classical
  have hp : (∑ c : Fin B, Polynomial.C (D c.val) * X ^ bin c.val : ℕ[X]) ^ n =
      ∑ cs : Fin n → Fin B, Polynomial.C (∏ i, D (cs i).val) * X ^ (∑ i, bin (cs i).val) := by
    rw [← Fin.prod_const, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro cs hcs
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  rw [hp]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, eq_comm]

theorem coverageBinnedPower_coeff (r b : ℕ) :
    ((coverageBinnedPoly r)^9).coeff b =
      ∑ cs : Fin 9 → Fin 4096,
        if (∑ i, coverageBin (cs i).val) = b then ∏ i, (retainedCoveragePoly r).coeff (cs i).val else 0 := by
  unfold coverageBinnedPoly
  rw [← Fin.sum_univ_eq_sum_range]
  exact finiteMonomialPower_coeff _ _ _ _ _

theorem bounded_fiber_group_sum {A : Type*} [Fintype A]
    (cc : A → ℕ) (weight : (Fin 9 → A) → ℕ) (bin : ℕ → ℕ) (B b : ℕ) :
    (∑ cs : Fin 9 → Fin B, if (∑ i, bin (cs i).val) = b then
      ∑ xs : Fin 9 → A, if (fun i => cc (xs i)) = (fun i => (cs i).val) then weight xs else 0 else 0) =
    ∑ xs : Fin 9 → A, if (∀ i, cc (xs i) < B) ∧ (∑ i, bin (cc (xs i))) = b then weight xs else 0 := by
  classical
  simp_rw [ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xs hxs
  by_cases hB : ∀ i, cc (xs i) < B
  · let cs0 : Fin 9 → Fin B := fun i => ⟨cc (xs i), hB i⟩
    rw [Finset.sum_eq_single cs0]
    · simp [cs0, hB]
    · intro cs hcs hne
      have he : (fun i => cc (xs i)) ≠ (fun i => (cs i).val) := by
        intro heq
        apply hne
        funext i
        apply Fin.ext
        exact (congrFun heq i).symm
      simp [he]
    · simp
  · have he (cs : Fin 9 → Fin B) : (fun i => cc (xs i)) ≠ (fun i => (cs i).val) := by
      intro heq
      apply hB
      intro i
      rw [congrFun heq i]
      exact (cs i).isLt
    simp [he, hB]

theorem coverageBinned_count_bound {β : Type*} [Fintype β]
    (val : β → Fin 6 → ℕ) (r b : ℕ)
    (hret : ∀ c, 128 * (retainedCoveragePoly r).coeff c ≤
      c * #{E : Fin r → Fin 128 × β | coordinateCoverage val E = c}) :
    128^9 * ((coverageBinnedPoly r)^9).coeff b ≤
      ∑ xs : Fin 9 → (Fin r → Fin 128 × β),
        if (∀ i, coordinateCoverage val (xs i) < 4096) ∧
            (∑ i, coverageBin (coordinateCoverage val (xs i))) = b
          then ∏ i, coordinateCoverage val (xs i) else 0 := by
  classical
  let cc : (Fin r → Fin 128 × β) → ℕ := coordinateCoverage val
  have hret' (c : ℕ) : 128 * (retainedCoveragePoly r).coeff c ≤
      ∑ E : Fin r → Fin 128 × β, if cc E = c then cc E else 0 := by
    convert hret c using 1
    rw [Finset.card_filter, mul_sum]
    apply Finset.sum_congr rfl
    intro E hE
    by_cases hc : cc E = c <;> simp [cc] at hc ⊢ <;> simp [hc]
  have ht (cs : Fin 9 → Fin 4096) := ClaudeWCT.Numerics.Winsor.tensor_retained_le
    cc cc (fun c => 128 * (retainedCoveragePoly r).coeff c) hret' (fun i => (cs i).val)
  rw [coverageBinnedPower_coeff, mul_sum]
  rw [← bounded_fiber_group_sum cc (fun xs => ∏ i, cc (xs i)) coverageBin 4096 b]
  apply Finset.sum_le_sum
  intro cs hcs
  by_cases hb : (∑ i, coverageBin (cs i).val) = b
  · rw [if_pos hb, if_pos hb]
    simpa only [Finset.prod_mul_distrib, Fin.prod_const] using ht cs
  · simp [hb]
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open Finset Polynomial
theorem coverageCoefficientDots_mass (P : ℕ[X]) (ds : List (ℕ × ℕ)) (k : ℕ) :
    (coverageCoefficientDots P ds k).1 = ∑ i ∈ range ds.length, P.coeff (k+i) := by
  induction ds generalizing k with
  | nil => simp [coverageCoefficientDots]
  | cons e ds ih =>
    change P.coeff k + (coverageCoefficientDots P ds (k+1)).1 = _
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    exact Nat.add_comm _ _


end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.Winsor
open Finset
set_option maxHeartbeats 1000000

theorem finite_nat_payoff_le {α : Type*} [Fintype α]
    (weight : α → ℕ) (fee : α → ℝ) (good : α → Prop) [DecidablePred good]
    (coeff pay : ℕ → ℕ) (label : α → ℕ) (M B S D X : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (hS : 0 < S)
    (hmass : ∑ z, weight z = D*X)
    (hcoeff : ∑ b ∈ range B, coeff b ≤ X)
    (hfee : ∀ z, fee z ≤ a*(weight z:ℝ) *
      (if good z ∧ label z < B then (pay (label z):ℝ)/S else M))
    (hpay : ∀ b < B, pay b ≤ M*S)
    (hret : ∀ b < B, D*coeff b ≤ ∑ z, if good z ∧ label z=b then weight z else 0) :
    ∑ z, fee z ≤ a*D/S *
      ((∑ b ∈ range B, coeff b*pay b) + M*S*(X-∑ b ∈ range B, coeff b) : ℕ) := by
  have h := finite_bounded_payoff_le (fun z => a*(weight z:ℝ)) fee good label
    (fun b => a*D*(coeff b:ℝ)) (fun b => (pay b:ℝ)/S) (M:ℝ) B hfee
    (fun b hb => (div_le_iff₀ (by exact_mod_cast hS)).2 (by exact_mod_cast hpay b hb))
    (fun b hb => ?_)
  · refine h.trans_eq ?_
    have hm : (∑ z, (weight z:ℝ)) = (D:ℝ)*X := by exact_mod_cast hmass
    have hs : (∑ b ∈ range B, a*(D:ℝ)*(coeff b:ℝ)*((pay b:ℝ)/(S:ℝ))) =
        a*D/S*(∑ b ∈ range B, (coeff b:ℝ)*(pay b:ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro b hb
      ring
    rw [hs]
    simp only [← mul_sum, hm]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hcoeff]
    push_cast
    field_simp
  · have hr : (D:ℝ)*(coeff b:ℝ) ≤ ∑ z, if good z ∧ label z=b then (weight z:ℝ) else 0 := by exact_mod_cast hret b hb
    simpa only [mul_assoc, mul_sum, mul_ite, mul_zero] using mul_le_mul_of_nonneg_left hr ha
end ClaudeWCT.Numerics.Winsor

namespace ClaudeWCT.Numerics.N600
open Finset
open ClaudeWCT.Numerics.Thinning
open SphincsSecurity.Concrete
open SigGolfResearch.Gate6.Moments
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

 theorem coverage_sum_xNum {β : Type} [Fintype β] (val : β → Fin 6 → ℕ)
    (hβ : Fintype.card β = 563) (h₁ : W1Table val) (r : ℕ) :
    ∑ E : Fin r → Fin 128 × β, coordinateCoverage val E = 128*xNum r := by
  classical
  have h := coord_first_xNum (C:=Fin 128) val hβ (by simp) h₁ r
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm] at h
  simpa only [coordinateCoverage, Finset.card_filter, Kc] using h

 theorem coverage_product_sum_xNum {β : Type} [Fintype β] (val : β → Fin 6 → ℕ)
    (hβ : Fintype.card β = 563) (h₁ : W1Table val) (r : ℕ) :
    ∑ xs : Fin 9 → (Fin r → Fin 128 × β), ∏ k, coordinateCoverage val (xs k) = 128^9*xNum r^9 := by
  rw [← Fintype.prod_sum]
  simp only [coverage_sum_xNum val hβ h₁ r, Fin.prod_const, mul_pow]
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
theorem zipIdx_eq_map_range (xs : List ℕ) :
    xs.zipIdx = (List.range xs.length).map (fun c => (xs[c]?.getD 0,c)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < xs.length := by simpa using hi
    simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range, Nat.zero_add,
      List.getElem?_eq_getElem h, Option.getD_some]

theorem coverageBinnedLinear_eq (bits r : ℕ) : coverageBinnedLinear bits r = coverageBinnedBits bits r := by
  unfold coverageBinnedLinear coverageBinnedBits
  rw [zipIdx_eq_map_range, List.foldr_map]
  have hl : coverageBinData.toList.length=4096 := by decide +kernel
  rw [hl]
  simp only [Array.getElem?_toList, coverageBin]

theorem coverageProductLinear_eq (r : ℕ) : coverageProductLinear r = coverageProductBits r := by
  simp only [coverageProductLinear, coverageBinnedLinear_eq, coverageProductBits]
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def winsorPayPair (b : ℕ) : ℕ × ℕ := (winsorMGFPayData.zip winsorResidualPayData)[b]?.getD (0,0)
theorem winsorPayPair_mem (b : ℕ) (hb : b < 2201)
    (hm : winsorMGFPayData.length=2201) (ht : winsorResidualPayData.length=2201) :
    (winsorPayPair b,b) ∈ (winsorMGFPayData.zip winsorResidualPayData).zipIdx := by
  have hl : b < (winsorMGFPayData.zip winsorResidualPayData).length := by simpa [List.length_zip,hm,ht] using hb
  have he := List.getElem_mem (l := (winsorMGFPayData.zip winsorResidualPayData).zipIdx) (n:=b) (by simpa using hl)
  simpa only [List.getElem_zipIdx, Nat.zero_add, winsorPayPair, List.getElem?_eq_getElem hl, Option.getD_some] using he

 theorem uniformWordAverage_coord_sum {β : Type} [Fintype β]
    [SampleableType (Fin 9 → Fin 128 × β)] (hβ : Fintype.card β=563)
    (r : ℕ) (fee : List (Fin 9 → Fin 128 × β) → ENNReal) :
    SphincsSecurity.Concrete.uniformWordAverage r fee =
      (∑ xs : Fin 9 → (Fin r → Fin 128 × β), fee (List.ofFn (fun j k => xs k j))) /
        ((Q^(9*r):ℕ):ENNReal) := by
  rw [SigGolfResearch.Gate6.Moments.word_array_average, SigGolfResearch.Gate6.Moments.finiteAverage]
  have hcard : Fintype.card (Fin r → Fin 9 → Fin 128 × β) = Q^(9*r) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, hβ, ← pow_mul]
    rfl
  rw [hcard]
  congr 1
  exact (Equiv.sum_comp (Equiv.piComm (fun _ : Fin 9 => fun _ : Fin r => Fin 128 × β))
    (fun E => fee (List.ofFn E))).symm
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

 theorem winsorPayPair_bound (b : ℕ) (hb : b < 2201)
    (hm : winsorMGFPayData.length=2201) (ht : winsorResidualPayData.length=2201)
    (hbound : (winsorMGFPayData.zip winsorResidualPayData).all (fun e =>
      e.1≤3000*winsorScale && e.2≤winsorScale)=true) :
    (winsorPayPair b).1≤3000*winsorScale ∧ (winsorPayPair b).2≤winsorScale := by
  have he := winsorPayPair_mem b hb hm ht
  have hv := (List.mem_zipIdx he).2.2
  have hl : b < (winsorMGFPayData.zip winsorResidualPayData).length := by simpa [List.length_zip,hm,ht] using hb
  have hg : winsorPayPair b ∈ winsorMGFPayData.zip winsorResidualPayData := by
    simpa only [Nat.sub_zero] using hv ▸ List.getElem_mem hl
  have h := List.all_eq_true.mp hbound _ hg
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h

 theorem winsor_product_pay (c : Fin 9 → ℕ) (hc : ∀ k, c k < 4096)
    (hb : (∑ k, coverageBin (c k)) < 2201)
    (hm : winsorMGFPayData.length=2201) (ht : winsorResidualPayData.length=2201)
    (hbin : (List.range 4096).all (fun c =>
      c*50^coverageBin c ≤ 51^coverageBin c &&
      (c≤1 || 51^(coverageBin c-1)<c*50^(coverageBin c-1)))=true)
    (hpay : winsorPayChecks=true) :
    let x := (1353/2^70 : ℝ)*∏ k,(c k:ℝ)
    let p := winsorPayPair (∑ k,coverageBin (c k))
    (Real.exp (8*min x 1)-1 ≤ x*((p.1:ℝ)/winsorScale)) ∧
      max (x-1) 0 ≤ x*((p.2:ℝ)/winsorScale) := by
  dsimp only
  by_cases hz : ∃ k, c k=0
  · obtain ⟨k,hk⟩ := hz
    have hp : ∏ j,(c j:ℝ)=0 := prod_eq_zero (mem_univ k) (by simp [hk])
    simp [hp]
  · have hc1 (k) : 1≤c k := by have h:=not_exists.mp hz k; omega
    let b := ∑ k,coverageBin (c k)
    have hint := geometricBin_product_interval c (fun k=>coverageBin (c k))
      (fun k=> coverageBin_interval_of_check (c k) (hc1 k) (hc k) hbin)
    have he := winsorPayChecks_entry hpay (winsorPayPair b).1 (winsorPayPair b).2 b
      (by simpa using winsorPayPair_mem b hb hm ht)
    exact ⟨winsorMGF_pay _ _ _ (by positivity) _ (by positivity) hint.1 hint.2 he.1,
      winsorResidual_pay _ _ _ (by positivity) _ (by positivity) hint.1 hint.2 he.2⟩
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open Finset Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem coverageCoefficientDots_mgf (P : ℕ[X]) (ds : List (ℕ × ℕ)) (k : ℕ) :
    (coverageCoefficientDots P ds k).2.1 =
      ∑ i ∈ range ds.length, P.coeff (k+i)*(ds[i]?.getD (0,0)).1 := by
  induction ds generalizing k with
  | nil => simp [coverageCoefficientDots]
  | cons e ds ih =>
    change P.coeff k*e.1+(coverageCoefficientDots P ds (k+1)).2.1 = _
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    exact Nat.add_comm _ _

theorem coverageCoefficientDots_residual (P : ℕ[X]) (ds : List (ℕ × ℕ)) (k : ℕ) :
    (coverageCoefficientDots P ds k).2.2 =
      ∑ i ∈ range ds.length, P.coeff (k+i)*(ds[i]?.getD (0,0)).2 := by
  induction ds generalizing k with
  | nil => simp [coverageCoefficientDots]
  | cons e ds ih =>
    change P.coeff k*e.2+(coverageCoefficientDots P ds (k+1)).2.2 = _
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    exact Nat.add_comm _ _
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open Finset Polynomial
open ClaudeWCT.Numerics.Winsor
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

 theorem coverageBinned_mass_le (r : ℕ) (hm : (retainedCoveragePoly r).eval 1 ≤ xNum r) :
    ((coverageBinnedPoly r)^9).eval 1 ≤ xNum r^9 := by
  rw [Polynomial.eval_pow]
  apply Nat.pow_le_pow_left
  calc
    (coverageBinnedPoly r).eval 1 = ∑ c ∈ range 4096, (retainedCoveragePoly r).coeff c := by
      simp only [coverageBinnedPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]
    _ ≤ (retainedCoveragePoly r).eval 1 := sum_coeff_le_eval_one _ _
    _ ≤ xNum r := hm

theorem winsorScale_pos : 0 < winsorScale := by norm_num [winsorScale]

attribute [local irreducible] coverageBinnedPoly retainedCoveragePoly xNum winsorScale winsorMGFPayData winsorResidualPayData coordinateCoverage coverageBin

 theorem raw_winsor_mgf_bound {β : Type} [Fintype β] (val : β → Fin 6 → ℕ)
    (hβ : Fintype.card β=563) (h₁ : W1Table val) (r : ℕ)
    (hret : ∀ c, 128*(retainedCoveragePoly r).coeff c ≤ c*#{E : Fin r → Fin 128 × β | coordinateCoverage val E=c})
    (hmass : (retainedCoveragePoly r).eval 1 ≤ xNum r)
    (hlenm : winsorMGFPayData.length=2201) (hlent : winsorResidualPayData.length=2201)
    (hbound : (winsorMGFPayData.zip winsorResidualPayData).all (fun e =>
      e.1≤3000*winsorScale && e.2≤winsorScale)=true)
    (hbin : (List.range 4096).all (fun c =>
      c*50^coverageBin c ≤ 51^coverageBin c &&
      (c≤1 || 51^(coverageBin c-1)<c*50^(coverageBin c-1)))=true)
    (hpay : winsorPayChecks=true) :
    let P := (coverageBinnedPoly r)^9
    let price := fun xs : Fin 9 → (Fin r → Fin 128 × β) =>
      (1353/2^70:ℝ)*(∏ k,coordinateCoverage val (xs k):ℕ)
    (∑ xs, (Real.exp (8*min (price xs) 1)-1)) ≤
      (1353/2^7:ℝ)/winsorScale *
        ((∑ b ∈ range 2201, P.coeff b*(winsorPayPair b).1) +
          3000*winsorScale*(xNum r^9-∑ b ∈ range 2201, P.coeff b):ℕ) := by
  classical
  dsimp only
  let cc := fun E : Fin r → Fin 128 × β => coordinateCoverage val E
  let good := fun xs : Fin 9 → (Fin r → Fin 128 × β) => ∀ k, cc (xs k)<4096
  let label := fun xs : Fin 9 → (Fin r → Fin 128 × β) => ∑ k, coverageBin (cc (xs k))
  apply (finite_nat_payoff_le (fun xs => ∏ k, cc (xs k))
    (fun xs => Real.exp (8*min ((1353/2^70:ℝ)*(∏ k,cc (xs k):ℕ)) 1)-1) good
    ((coverageBinnedPoly r)^9).coeff (fun b => (winsorPayPair b).1) label
    3000 2201 winsorScale (128^9) (xNum r^9) (1353/2^70) (by positivity)
    winsorScale_pos (coverage_product_sum_xNum val hβ h₁ r)
    ((sum_coeff_le_eval_one _ _).trans (coverageBinned_mass_le r hmass)) ?_ ?_ ?_).trans_eq
  · have hs : (1353/2^70:ℝ)*(128^9:ℕ)/winsorScale = (1353/2^7:ℝ)/winsorScale := by
      congr 1
      norm_num
    rw [hs]
  · intro xs
    by_cases h : good xs ∧ label xs<2201
    · rw [if_pos h]
      have hp := (winsor_product_pay (fun k=>cc (xs k)) h.1 h.2 hlenm hlent hbin hpay).1
      simpa only [Nat.cast_prod] using hp
    · rw [if_neg h]
      simpa only [mul_comm, Nat.cast_ofNat] using cappedExp_le_linear ((1353/2^70:ℝ)*(∏ k,cc (xs k):ℕ)) (by positivity)
  · intro b hb
    exact (winsorPayPair_bound b hb hlenm hlent hbound).1
  · intro b hb
    exact coverageBinned_count_bound val r b hret
 theorem raw_winsor_residual_bound {β : Type} [Fintype β] (val : β → Fin 6 → ℕ)
    (hβ : Fintype.card β=563) (h₁ : W1Table val) (r : ℕ)
    (hret : ∀ c, 128*(retainedCoveragePoly r).coeff c ≤ c*#{E : Fin r → Fin 128 × β | coordinateCoverage val E=c})
    (hmass : (retainedCoveragePoly r).eval 1 ≤ xNum r)
    (hlenm : winsorMGFPayData.length=2201) (hlent : winsorResidualPayData.length=2201)
    (hbound : (winsorMGFPayData.zip winsorResidualPayData).all (fun e =>
      e.1≤3000*winsorScale && e.2≤winsorScale)=true)
    (hbin : (List.range 4096).all (fun c =>
      c*50^coverageBin c ≤ 51^coverageBin c &&
      (c≤1 || 51^(coverageBin c-1)<c*50^(coverageBin c-1)))=true)
    (hpay : winsorPayChecks=true) :
    let P := (coverageBinnedPoly r)^9
    let price := fun xs : Fin 9 → (Fin r → Fin 128 × β) =>
      (1353/2^70:ℝ)*(∏ k,coordinateCoverage val (xs k):ℕ)
    (∑ xs, max (price xs-1) 0) ≤
      (1353/2^7:ℝ)/winsorScale *
        ((∑ b ∈ range 2201, P.coeff b*(winsorPayPair b).2) +
          winsorScale*(xNum r^9-∑ b ∈ range 2201, P.coeff b):ℕ) := by
  classical
  dsimp only
  let cc := fun E : Fin r → Fin 128 × β => coordinateCoverage val E
  let good := fun xs : Fin 9 → (Fin r → Fin 128 × β) => ∀ k, cc (xs k)<4096
  let label := fun xs : Fin 9 → (Fin r → Fin 128 × β) => ∑ k, coverageBin (cc (xs k))
  apply (finite_nat_payoff_le (fun xs => ∏ k, cc (xs k))
    (fun xs => max ((1353/2^70:ℝ)*(∏ k,cc (xs k):ℕ)-1) 0) good
    ((coverageBinnedPoly r)^9).coeff (fun b => (winsorPayPair b).2) label
    1 2201 winsorScale (128^9) (xNum r^9) (1353/2^70) (by positivity)
    winsorScale_pos (coverage_product_sum_xNum val hβ h₁ r)
    ((sum_coeff_le_eval_one _ _).trans (coverageBinned_mass_le r hmass)) ?_ ?_ ?_).trans_eq
  · simp only [Nat.one_mul]
    have hs : (1353/2^70:ℝ)*(128^9:ℕ)/winsorScale = (1353/2^7:ℝ)/winsorScale := by
      congr 1
      norm_num
    rw [hs]
  · intro xs
    by_cases h : good xs ∧ label xs<2201
    · rw [if_pos h]
      have hp := (winsor_product_pay (fun k=>cc (xs k)) h.1 h.2 hlenm hlent hbin hpay).2
      simpa only [Nat.cast_prod] using hp
    · rw [if_neg h]
      simp only [Nat.cast_one, mul_one]
      exact max_le (by linarith) (by positivity)
  · intro b hb
    simpa using (winsorPayPair_bound b hb hlenm hlent hbound).2
  · intro b hb
    exact coverageBinned_count_bound val r b hret
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
section
variable {β C : Type} [Fintype β] [Fintype C] [DecidableEq C]

theorem bucketPrice_ne_top (val : β → Fin 6 → ℕ) (L : List (Fin 9 → C × β)) :
    bucketPrice val L ≠ ⊤ := by
  exact ENNReal.mul_ne_top priceScale_ne_top
    (ne_top_of_le_ne_top ENNReal.one_ne_top (ClaudeWCT.Numerics.Thinning.env_le_one val L))

theorem bucketExpIncrement_real (val : β → Fin 6 → ℕ) (L : List (Fin 9 → C × β)) :
    bucketExpIncrement val L = ENNReal.ofReal
      (Real.exp (8*min (bucketPrice val L).toReal 1)-1) := by
  rw [bucketExpIncrement, bucketCapped, ENNReal.toReal_min (bucketPrice_ne_top val L) ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.ofReal_sub _ (by norm_num), ENNReal.ofReal_one]

theorem bucketResidual_real (val : β → Fin 6 → ℕ) (L : List (Fin 9 → C × β)) :
    bucketResidual val L = ENNReal.ofReal (max ((bucketPrice val L).toReal-1) 0) := by
  rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (by positivity),
    ENNReal.ofReal_sub _ (by norm_num), ENNReal.ofReal_toReal (bucketPrice_ne_top val L), ENNReal.ofReal_one]
  rfl


theorem bucketPrice_ofFn_real {r : ℕ} (val : β → Fin 6 → ℕ)
    (hβ : Fintype.card β=563) (hC : Fintype.card C=128) (E : Fin r → Fin 9 → C × β) :
    (bucketPrice val (List.ofFn E)).toReal =
      (1353/2^70:ℝ)*(∏ k,coordinateCoverage val (fun j=>E j k):ℕ) := by
  rw [bucketPrice_ofFn val hβ hC]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
end
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open Finset Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem coverageBinnedPower_packed (r : ℕ)
    (hm : (retainedCoveragePoly r).eval 1 ≤ xNum r) (hx : xNum r<2^512) :
    winsorPackedSums winsorMGFPayData winsorResidualPayData (coverageProductBits r) =
      coverageCoefficientDots ((coverageBinnedPoly r)^9) (winsorMGFPayData.zip winsorResidualPayData) 0 := by
  have hm' : coverageRetainedPack 1 r < 2^512 := by
    rw [← retainedCoveragePoly_eval]
    exact hm.trans_lt hx
  rw [coverageProductBits_eq, coverageProductPack, ← coverageBinnedPoly_eval r (2^4608) hm', ← Polynomial.eval_pow]
  apply winsorPackedSums_eq_coefficients
  exact binnedPower_coeff_lt (retainedCoveragePoly r) (range 4096) coverageBin (xNum r) hm hx

theorem winsorRowDots_model (r : ℕ) (hr : r≤20)
    (hm : (retainedCoveragePoly r).eval 1 ≤ xNum r) (hx : xNum r<2^512)
    (hlenm : winsorMGFPayData.length=2201) (hlent : winsorResidualPayData.length=2201) :
    let P := (coverageBinnedPoly r)^9
    winsorRowDots r =
      ((∑ b ∈ range 2201, P.coeff b*(winsorPayPair b).1) +
          3000*winsorScale*(xNum r^9-∑ b ∈ range 2201, P.coeff b),
       (∑ b ∈ range 2201, P.coeff b*(winsorPayPair b).2) +
          winsorScale*(xNum r^9-∑ b ∈ range 2201, P.coeff b)) := by
  simp only [winsorRowDots, if_pos hr, coverageProductLinear_eq]
  rw [coverageBinnedPower_packed r hm hx]
  simp only [coverageCoefficientDots_mass, coverageCoefficientDots_mgf, coverageCoefficientDots_residual,
    Nat.zero_add, List.length_zip, hlenm, hlent, Nat.min_self, winsorPayPair]
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem uniform_raw_bound {β : Type} [Fintype β] [SampleableType (Fin 9 → Fin 128 × β)]
    (hβ : Fintype.card β=563) (r d : ℕ)
    (fee : List (Fin 9 → Fin 128 × β) → ENNReal)
    (raw : (Fin 9 → (Fin r → Fin 128 × β)) → ℝ)
    (hnn : ∀ xs, 0≤raw xs)
    (heq : ∀ xs, fee (List.ofFn (fun j k=>xs k j))=ENNReal.ofReal (raw xs))
    (hraw : (∑ xs, raw xs) ≤ (1353/2^7:ℝ)/winsorScale*(d:ℝ)) :
    SphincsSecurity.Concrete.uniformWordAverage r fee ≤
      (1353/2^7:ENNReal)/winsorScale*(d:ENNReal)/((Q^(9*r):ℕ):ENNReal) := by
  have hS : (winsorScale:ENNReal)≠0 := by norm_num [winsorScale]
  have hQ : ((Q^(9*r):ℕ):ENNReal)≠0 := by exact_mod_cast (pow_ne_zero _ (by norm_num [Q] : Q≠0))
  rw [uniformWordAverage_coord_sum hβ]
  apply (ENNReal.toReal_le_toReal ?_ ?_).mp
  · rw [ENNReal.toReal_div, ENNReal.toReal_sum]
    · simp_rw [heq, ENNReal.toReal_ofReal (hnn _)]
      simpa only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofNat, ENNReal.toReal_natCast] using
        div_le_div_of_nonneg_right hraw (show (0:ℝ)≤(Q^(9*r):ℕ) by positivity)
    · intro xs hxs
      rw [heq]
      exact ENNReal.ofReal_ne_top
  · apply ENNReal.div_ne_top
    · exact ENNReal.sum_ne_top.mpr fun xs _=> by rw [heq]; exact ENNReal.ofReal_ne_top
    · exact_mod_cast (pow_ne_zero _ (by norm_num [Q] : Q≠0))
  · finiteness
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
attribute [local irreducible] coverageBinnedPoly retainedCoveragePoly xNum winsorScale winsorMGFPayData winsorResidualPayData coordinateCoverage coverageBin
 theorem uniform_winsor_rows {β : Type} [Fintype β] [SampleableType (Fin 9 → Fin 128 × β)]
    (val : β → Fin 6 → ℕ) (hβ : Fintype.card β=563) (h₁ : W1Table val) (r : ℕ) (hr : r≤20)
    (hret : ∀ c, 128*(retainedCoveragePoly r).coeff c ≤ c*#{E : Fin r → Fin 128 × β | coordinateCoverage val E=c})
    (hmass : (retainedCoveragePoly r).eval 1 ≤ xNum r) (hx : xNum r<2^512)
    (hlenm : winsorMGFPayData.length=2201) (hlent : winsorResidualPayData.length=2201)
    (hbound : (winsorMGFPayData.zip winsorResidualPayData).all (fun e =>
      e.1≤3000*winsorScale && e.2≤winsorScale)=true)
    (hbin : (List.range 4096).all (fun c =>
      c*50^coverageBin c ≤ 51^coverageBin c &&
      (c≤1 || 51^(coverageBin c-1)<c*50^(coverageBin c-1)))=true)
    (hpay : winsorPayChecks=true) :
    SphincsSecurity.Concrete.uniformWordAverage r (bucketExpIncrement (C:=Fin 128) val) ≤
      (1353/2^7:ENNReal)/winsorScale*((winsorRowDots r).1:ENNReal)/((Q^(9*r):ℕ):ENNReal) ∧
    SphincsSecurity.Concrete.uniformWordAverage r (bucketResidual (C:=Fin 128) val) ≤
      (1353/2^7:ENNReal)/winsorScale*((winsorRowDots r).2:ENNReal)/((Q^(9*r):ℕ):ENNReal) := by
  classical
  have hd := winsorRowDots_model r hr hmass hx hlenm hlent
  constructor
  · apply uniform_raw_bound hβ r (winsorRowDots r).1 (bucketExpIncrement (C:=Fin 128) val)
      (fun xs => Real.exp (8*min ((1353/2^70:ℝ)*(∏ k,coordinateCoverage val (xs k):ℕ)) 1)-1)
    · intro xs
      exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))
    · intro xs
      rw [bucketExpIncrement_real, bucketPrice_ofFn_real val hβ (by simp)]
    · rw [hd]
      exact raw_winsor_mgf_bound val hβ h₁ r hret hmass hlenm hlent hbound hbin hpay
  · apply uniform_raw_bound hβ r (winsorRowDots r).2 (bucketResidual (C:=Fin 128) val)
      (fun xs => max ((1353/2^70:ℝ)*(∏ k,coordinateCoverage val (xs k):ℕ)-1) 0)
    · intro xs; exact le_max_right _ _
    · intro xs
      rw [bucketResidual_real, bucketPrice_ofFn_real val hβ (by simp)]
    · rw [hd]
      exact raw_winsor_residual_bound val hβ h₁ r hret hmass hlenm hlent hbound hbin hpay
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open Finset ENNReal
open ClaudeWCT.Numerics.Law
open ClaudeWCT.Numerics.Thinning
open ClaudeWCT.Numerics.Winsor
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
section
variable {β C : Type} [Fintype β] [Fintype C] [DecidableEq C]

theorem bucketExpIncrement_le_price (val : β → Fin 6 → ℕ) (L : List (Fin 9 → C × β)) :
    bucketExpIncrement val L ≤ 3000*bucketPrice val L := by
  rw [bucketExpIncrement_real]
  calc
    _ ≤ ENNReal.ofReal (3000*(bucketPrice val L).toReal) :=
      ENNReal.ofReal_le_ofReal (cappedExp_le_linear _ ENNReal.toReal_nonneg)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal (bucketPrice_ne_top val L)]; norm_num

theorem bucketResidual_le_price (val : β → Fin 6 → ℕ) (L : List (Fin 9 → C × β)) :
    bucketResidual val L ≤ bucketPrice val L := tsub_le_self

 theorem priceScale_pos : 0 < priceScale := by norm_num [priceScale]
 theorem feeScale_ne_zero (M : ℕ) (hM : 0<M) : (M:ENNReal)*priceScale≠0 := by
  exact mul_ne_zero (by exact_mod_cast hM.ne') (ne_of_gt priceScale_pos)
 theorem feeScale_ne_top (M : ℕ) : (M:ENNReal)*priceScale≠⊤ := ENNReal.mul_ne_top (by simp) priceScale_ne_top

 theorem law_fee_norm_le_env (val : β → Fin 6 → ℕ)
    (fee : List (Fin 9 → C × β) → ENNReal) (M : ℕ) (hM : 0<M)
    (hfee : ∀ L, fee L ≤ (M:ENNReal)*priceScale*env val L)
    (vc : (Fin 9 → C × β) → ENNReal) (r : ℕ) :
    lawAvg vc r fee / ((M:ENNReal)*priceScale) ≤ lawAvg vc r (env val) := by
  have h := lawAvg_mono vc r hfee
  rw [lawAvg_mul_left] at h
  calc
    _ ≤ ((M:ENNReal)*priceScale)*lawAvg vc r (env val) / ((M:ENNReal)*priceScale) := by simpa only [div_eq_mul_inv] using mul_le_mul' h le_rfl
    _ = _ := by rw [mul_comm ((M:ENNReal)*priceScale), ENNReal.mul_div_cancel_right (feeScale_ne_zero M hM) (feeScale_ne_top M)]
end

theorem row_scale_normalize (M r d : ℕ) (hM : 0<M) :
    ((1353/2^7:ENNReal)/winsorScale*(d:ENNReal)/((Q^(9*r):ℕ):ENNReal)) /
      ((M:ENNReal)*priceScale) =
    (d:ENNReal)/((M*winsorScale*Nn^9*Q^(9*r):ℕ):ENNReal) := by
  have hS : (winsorScale:ENNReal)≠0 := by norm_num [winsorScale]
  have hQ : ((Q^(9*r):ℕ):ENNReal)≠0 := by exact_mod_cast (pow_ne_zero _ (by norm_num [Q] : Q≠0))
  have hM0 : (M:ENNReal)≠0 := by exact_mod_cast hM.ne'
  have hF := feeScale_ne_zero M hM
  have hN : (Nn:ENNReal)≠0 := by norm_num [Nn]
  have hDen : ((M*winsorScale*Nn^9*Q^(9*r):ℕ):ENNReal)≠0 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hM0 hS)
      (by simpa only [Nat.cast_pow] using pow_ne_zero 9 hN)) hQ
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast, priceScale, Nat.cast_mul, Nat.cast_pow]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Nn]
  have hmr : (M:ℝ)≠0 := by exact_mod_cast hM.ne'
  have hsr : (winsorScale:ℝ)≠0 := by norm_num [winsorScale]
  have hqr : ((Q^(9*r):ℕ):ℝ)≠0 := by exact_mod_cast (pow_ne_zero _ (by norm_num [Q] : Q≠0))
  push_cast
  field_simp
  <;> ring
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open Finset ENNReal
open ClaudeWCT.Numerics.Law
open ClaudeWCT.Numerics.Thinning
open SphincsSecurity.Concrete
open ClaudeWCT.Numerics.PoissonReflect
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
section
variable {β C : Type} [Fintype β] [Fintype C] [DecidableEq C]
variable [SampleableType (Fin 9 → C × β)]

theorem law_normalized_uniform_row (fee : List (Fin 9 → C × β) → ENNReal)
    {vc : (Fin 9 → C × β) → ENNReal} {κ : ENNReal} (hlaw : LawOK vc κ)
    (M r d : ℕ) (hM : 0<M)
    (hu : uniformWordAverage r fee ≤ (1353/2^7:ENNReal)/winsorScale*(d:ENNReal)/((Q^(9*r):ℕ):ENNReal)) :
    lawAvg vc r fee/((M:ENNReal)*priceScale) ≤
      κ^r*((d:ENNReal)/((M*winsorScale*Nn^9*Q^(9*r):ℕ):ENNReal)) := by
  have h := (lawAvg_le_uniform vc κ hlaw.density r fee).trans (mul_le_mul' le_rfl hu)
  calc
    _ ≤ (κ^r*((1353/2^7:ENNReal)/winsorScale*(d:ENNReal)/((Q^(9*r):ℕ):ENNReal)))/((M:ENNReal)*priceScale) := by
      simpa only [div_eq_mul_inv] using mul_le_mul' h le_rfl
    _ = _ := by rw [mul_div_assoc, row_scale_normalize M r d hM]

theorem full_row_normalize (M r : ℕ) (hM : 0<M) :
    ((M*winsorScale*xNum r^9:ℕ):ENNReal)/((M*winsorScale*Nn^9*Q^(9*r):ℕ):ENNReal) =
      ((xNum r^9:ℕ):ENNReal)/((Nn^9*Q^(9*r):ℕ):ENNReal) := by
  have h := ENNReal.mul_div_mul_left (c:=((M*winsorScale:ℕ):ENNReal))
    ((xNum r^9:ℕ):ENNReal) ((Nn^9*Q^(9*r):ℕ):ENNReal)
    (by exact_mod_cast Nat.mul_ne_zero hM.ne' (by norm_num [winsorScale])) (by finiteness)
  simpa only [Nat.cast_mul, mul_assoc] using h


theorem law_coord_bound_of_rows (val : β → Fin 6 → ℕ)
    (fee : List (Fin 9 → C × β) → ENNReal) (M Mn Md : ℕ) (hM : 0<M) (hMd : 0<Md)
    {vc : (Fin 9 → C × β) → ENNReal} {κ : ENNReal} (hlaw : LawOK vc κ)
    (T : ℕ) (hT1 : 2^32≤T) (hT2 : T≤2^32) (f : ℕ→ℕ)
    (hfee : ∀ L, fee L ≤ (M:ENNReal)*priceScale*env val L)
    (hcheck : poissonCheckQ Q 13533529 100000000 LN LD f (M*winsorScale*Nn^9) (M*A) 1 Mn Md 80=true)
    (hrow : ∀ r≤80, lawAvg vc r fee/((M:ENNReal)*priceScale) ≤
      κ^r*((f r:ENNReal)/((M*winsorScale*Nn^9*Q^(9*r):ℕ):ENNReal))) :
    (2^31:ENNReal)*coordAverage (2^31:ENNReal)⁻¹ vc T fee ≤ (Mn:ENNReal)/Md := by
  have h := poissonCheckQ_sound_tilt (Qv:=Q) (f:=f) (dbase:=M*winsorScale*Nn^9)
    (sn:=M*A) (sd:=1) (Mn:=Mn) (Md:=Md) hcheck (by norm_num [Q])
    (by norm_num) (by norm_num [LD]) (Nat.mul_pos (Nat.mul_pos hM (by norm_num [winsorScale])) (by norm_num [Nn])) (by norm_num) hMd
    rate_le_one κ hlaw.one_le (rate_window hlaw hT2) (rejection_window_sharp T hT1)
    (fun r=>lawAvg vc r fee/((M:ENNReal)*priceScale)) hrow
    (fun r _ => (law_fee_norm_le_env val fee M hM hfee vc r).trans (law_env_le_one val hlaw r))
  simp only [Nat.cast_one, div_one] at h
  have he : ((M*A:ℕ):ENNReal)*binomialAverage (2^31:ENNReal)⁻¹ T
      (fun r=>lawAvg vc r fee/((M:ENNReal)*priceScale)) =
      (2^31:ENNReal)*coordAverage (2^31:ENNReal)⁻¹ vc T fee := by
    unfold coordAverage
    simp_rw [div_eq_mul_inv, mul_comm (lawAvg vc _ fee), binomialAverage_mul_left]
    rw [← mul_assoc]
    congr 1
    rw [Nat.cast_mul, ← priceScale_mul]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [show (M:ENNReal)*(priceScale*2^31)*((M:ENNReal)*priceScale)⁻¹ =
      2^31*(((M:ENNReal)*priceScale)*((M:ENNReal)*priceScale)⁻¹) by ring,
      ENNReal.mul_inv_cancel (feeScale_ne_zero M hM) (feeScale_ne_top M), mul_one]
  rwa [he] at h
end
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open Finset ENNReal
open ClaudeWCT.Numerics.Law
open ClaudeWCT.Numerics.Thinning
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
attribute [local irreducible] coverageBinnedPoly retainedCoveragePoly xNum winsorScale winsorMGFPayData winsorResidualPayData coordinateCoverage coverageBin

 theorem law_price_excess_winsor_of_checks {β : Type} [Fintype β]
    [SampleableType (Fin 9 → Fin 128 × β)]
    (val : β → Fin 6 → ℕ) (hW : WordsOf val) (h4 : ∀ x i, val x i≤4)
    (hβ : Fintype.card β=563) (h₁ : W1Table val)
    {vc : (Fin 9 → Fin 128 × β) → ENNReal} {κ : ENNReal} (hlaw : LawOK vc κ)
    (T : ℕ) (hT1 : 2^32≤T) (hT2 : T≤2^32)
    (hlenm : winsorMGFPayData.length=2201) (hlent : winsorResidualPayData.length=2201)
    (hbound : (winsorMGFPayData.zip winsorResidualPayData).all (fun e =>
      e.1≤3000*winsorScale && e.2≤winsorScale)=true)
    (hbin : winsorBinCheck=true) (hpay : winsorPayChecks=true)
    (hmasses : (List.range 31).all winsorMassCheck=true)
    (hmgfcheck : poissonCheckQ Q 13533529 100000000 LN LD (fun r=>(winsorRowDots r).1)
      (3000*winsorScale*Nn^9) (3000*A) 1 8 1 80=true)
    (hrescheck : poissonCheckQ Q 13533529 100000000 LN LD (fun r=>(winsorRowDots r).2)
      (winsorScale*Nn^9) A 1 1 5000 80=true) :
    lawAvg (marked (α:=Fin (2^31)) vc) T (fun W=>priceN val W-2031/1024) ≤ 23/100000 := by
  have hmgfpoint (L : List (Fin 9 → Fin 128 × β)) :
      bucketExpIncrement val L ≤ (3000:ENNReal)*priceScale*env val L := by
    simpa only [bucketPrice, mul_assoc] using bucketExpIncrement_le_price val L
  have hrespoint (L : List (Fin 9 → Fin 128 × β)) :
      bucketResidual val L ≤ ((1:ℕ):ENNReal)*priceScale*env val L := by
    simpa only [Nat.cast_one, one_mul, bucketPrice] using bucketResidual_le_price val L
  have hrows (r : ℕ) (hr : r≤20) := by
    have hmass := List.all_eq_true.mp hmasses r (List.mem_range.mpr (by omega : r<31))
    simp only [winsorMassCheck, Bool.and_eq_true, decide_eq_true_eq] at hmass
    have hm : (retainedCoveragePoly r).eval 1 ≤ xNum r := by
      rw [retainedCoveragePoly_eval, ← coverageRetainedFastPack_eq]
      exact hmass.1
    have hret (c : ℕ) : 128*(retainedCoveragePoly r).coeff c ≤
        c*#{E : Fin r → Fin 128 × β | coordinateCoverage val E=c} :=
      retainedCoverage_count_bound_of_packed val hW h4 hβ coverageH_packed ⟨r,by omega⟩ c
    exact uniform_winsor_rows val hβ h₁ r hr hret hm hmass.2 hlenm hlent hbound hbin hpay
  have hmgf := law_coord_bound_of_rows val (bucketExpIncrement val) 3000 8 1
    (by norm_num) (by norm_num) hlaw T hT1 hT2 (fun r=>(winsorRowDots r).1) hmgfpoint hmgfcheck
    (fun r hr => by
      by_cases hcut : r≤20
      · exact law_normalized_uniform_row _ hlaw 3000 r _ (by norm_num) (hrows r hcut).1
      · simp only [winsorRowDots, if_neg hcut]
        rw [full_row_normalize 3000 r (by norm_num)]
        exact (law_fee_norm_le_env val _ 3000 (by norm_num) hmgfpoint vc r).trans
          (law_env_le val hβ (by simp) h₁ hlaw r))
  have hres := law_coord_bound_of_rows val (bucketResidual val) 1 1 5000
    (by norm_num) (by norm_num) hlaw T hT1 hT2 (fun r=>(winsorRowDots r).2) hrespoint
    (by simpa only [Nat.one_mul] using hrescheck)
    (fun r hr => by
      by_cases hcut : r≤20
      · exact law_normalized_uniform_row _ hlaw 1 r _ (by norm_num) (hrows r hcut).2
      · simp only [winsorRowDots, if_neg hcut]
        rw [show winsorScale*xNum r^9=1*winsorScale*xNum r^9 by simp, full_row_normalize 1 r (by norm_num)]
        exact (law_fee_norm_le_env val _ 1 (by norm_num) hrespoint vc r).trans
          (law_env_le val hβ (by simp) h₁ hlaw r))
  exact law_price_excess_le_winsor val hlaw T (by simpa using hmgf) (by simpa using hres)
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Law
/-- The finite kernel checks certify the winsorized excess bound. -/
theorem law_price_excess_winsor {β : Type} [Fintype β]
    [SampleableType (Fin 9 → Fin 128 × β)]
    (val : β → Fin 6 → ℕ) (hW : WordsOf val) (h4 : ∀ x i, val x i ≤ 4)
    (hβ : Fintype.card β = 563) (h₁ : W1Table val)
    {vc : (Fin 9 → Fin 128 × β) → ENNReal} {κ : ENNReal} (hlaw : LawOK vc κ)
    (T : ℕ) (hT1 : 2^32 ≤ T) (hT2 : T ≤ 2^32) :
    lawAvg (marked (α := Fin (2^31)) vc) T (fun W => priceN val W - 2031/1024) ≤ 23/100000 := by
  exact law_price_excess_winsor_of_checks val hW h4 hβ h₁ hlaw T hT1 hT2
    winsor_mgf_length winsor_residual_length winsor_pay_bounds winsor_bins_ok
    winsor_pay_ok winsor_masses_ok winsor_mgf_ok winsor_residual_ok
end ClaudeWCT.Numerics.N600

/-! Parameterized exponential stop-loss bound for the private shared-path
construction. The finite coverage certificate supplying the moment premises
is separate; these lemmas alone do not certify the changed scheme. -/
namespace ClaudeWCT.Numerics.SharedPathWinsor
open ENNReal Finset ClaudeWCT.Numerics.Law
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem positive_part_exp (x theta t : ℝ) (ht : 0 < t) :
    max 0 (x - theta) ≤ (3 / (8 * t)) * Real.exp (-t * theta) *
      Real.exp (t * x) := by
  have hp := ClaudeWCT.Numerics.Winsor.linear_le_exp (t * (x - theta))
  have he : Real.exp (t * (x - theta)) =
      Real.exp (-t * theta) * Real.exp (t * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hp
  have hden : 8 * t ≠ 0 := ne_of_gt (by positivity)
  have hcancel : t * ((3 / (8 * t)) * Real.exp (-t * theta) * Real.exp (t * x)) =
      (3 / 8) * (Real.exp (-t * theta) * Real.exp (t * x)) := by
    field_simp
    <;> ring
  apply max_le
  · positivity
  · apply (mul_le_mul_iff_right₀ ht).mp
    rw [hcancel]
    exact hp


#print axioms positive_part_exp
end ClaudeWCT.Numerics.SharedPathWinsor

namespace ClaudeWCT.Numerics.SharedPathWinsor
open ENNReal Finset ClaudeWCT.Numerics.Law

theorem cap_exp_majorant_general (c : ENNReal) (hc : c ≠ ⊤)
    (theta t : ℝ) (htheta : 0 ≤ theta) (ht : 0 < t) :
    c ≤ ENNReal.ofReal theta +
      ENNReal.ofReal ((3 / (8 * t)) * Real.exp (-t * theta)) *
        ENNReal.ofReal (Real.exp (t * c.toReal)) := by
  have h := positive_part_exp c.toReal theta t ht
  have hcR : c.toReal ≤ theta + (3 / (8 * t)) *
      Real.exp (-t * theta) * Real.exp (t * c.toReal) := by
    have hm := le_max_right 0 (c.toReal - theta)
    linarith
  calc
    c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hc).symm
    _ ≤ ENNReal.ofReal (theta + (3 / (8 * t)) *
        Real.exp (-t * theta) * Real.exp (t * c.toReal)) := ENNReal.ofReal_le_ofReal hcR
    _ = _ := by rw [ENNReal.ofReal_add htheta (by positivity), ENNReal.ofReal_mul (by positivity)]

/-- Generic bank excess bound from a capped moment and a residual first moment. -/
theorem excess_le_of_capped_exp_general {β : Type} [Fintype β]
    (v : β → ENNReal) (T : ℕ) (price capped residual : List β → ENNReal)
    (theta t bound residualBound resultBound : ℝ)
    (htheta : 0 ≤ theta) (ht : 0 < t) (hresBound : 0 ≤ residualBound)
    (hcapped : ∀ W, capped W ≠ ⊤)
    (hsplit : ∀ W, price W ≤ capped W + residual W)
    (hexp : lawAvg v T (fun W => ENNReal.ofReal (Real.exp (t * (capped W).toReal))) ≤
      ENNReal.ofReal (Real.exp bound))
    (hres : lawAvg v T residual ≤ ENNReal.ofReal residualBound)
    (hscalar : (3 / (8 * t)) * Real.exp (bound - t * theta) + residualBound ≤ resultBound) :
    lawAvg v T (fun W => price W - ENNReal.ofReal theta) ≤ ENNReal.ofReal resultBound := by
  let a : ENNReal := ENNReal.ofReal ((3 / (8 * t)) * Real.exp (-t * theta))
  have hpoint : ∀ W, price W - ENNReal.ofReal theta ≤
      a * ENNReal.ofReal (Real.exp (t * (capped W).toReal)) + residual W := by
    intro W
    apply (tsub_le_iff_right).2
    calc
      price W ≤ capped W + residual W := hsplit W
      _ ≤ (ENNReal.ofReal theta +
          a * ENNReal.ofReal (Real.exp (t * (capped W).toReal))) + residual W :=
        add_le_add (cap_exp_majorant_general (capped W) (hcapped W) theta t htheta ht) le_rfl
      _ = _ := by ac_rfl
  have he : ((3 / (8 * t)) * Real.exp (-t * theta)) * Real.exp bound =
      (3 / (8 * t)) * Real.exp (bound - t * theta) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  calc
    lawAvg v T (fun W => price W - ENNReal.ofReal theta) ≤
        lawAvg v T (fun W => a * ENNReal.ofReal (Real.exp (t * (capped W).toReal)) + residual W) :=
      lawAvg_mono v T hpoint
    _ = a * lawAvg v T (fun W => ENNReal.ofReal (Real.exp (t * (capped W).toReal))) +
        lawAvg v T residual := by rw [lawAvg_add, lawAvg_mul_left]
    _ ≤ a * ENNReal.ofReal (Real.exp bound) + ENNReal.ofReal residualBound :=
      add_le_add (mul_le_mul' le_rfl hexp) hres
    _ = ENNReal.ofReal ((3 / (8 * t)) * Real.exp (bound - t * theta) + residualBound) := by
      dsimp [a]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) hresBound, he]
    _ ≤ ENNReal.ofReal resultBound := ENNReal.ofReal_le_ofReal hscalar

#print axioms cap_exp_majorant_general
#print axioms excess_le_of_capped_exp_general
end ClaudeWCT.Numerics.SharedPathWinsor

namespace ClaudeWCT.Numerics.SharedPathWinsor
open ENNReal Finset ClaudeWCT.Numerics.Law
open SigGolfCandidate.T3.BPORS.History (atIndex)

/-- A forest-specific bucket estimate can be inserted here without changing the
negative-dependence argument across independently sampled signing indices. -/
theorem law_bucket_excess_general {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] (v : β → ENNReal) (hv : ∑ b, v b = 1) (T : ℕ)
    (bucket : List β → ENNReal) (cap : ENNReal) (hcap : cap ≠ ⊤)
    (theta t bound residualBound resultBound : ℝ)
    (htheta : 0 ≤ theta) (ht : 0 < t) (hbound : 0 ≤ bound) (hresBound : 0 ≤ residualBound)
    (hmono : ∀ L b R, bucket (L ++ R) ≤ bucket (L ++ b :: R))
    (hmgf : (∑ _i : α, coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => ENNReal.ofReal (Real.exp (t * (min (bucket L) cap).toReal)) - 1)) ≤
        ENNReal.ofReal bound)
    (hres : (∑ _i : α, coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => bucket L - cap)) ≤ ENNReal.ofReal residualBound)
    (hscalar : (3 / (8 * t)) * Real.exp (bound - t * theta) + residualBound ≤ resultBound) :
    lawAvg (marked (α := α) v) T
      (fun W => (∑ i : α, bucket (atIndex i W)) - ENNReal.ofReal theta) ≤
        ENNReal.ofReal resultBound := by
  let capped : List (α × β) → ENNReal := fun W => ∑ i : α, min (bucket (atIndex i W)) cap
  let residual : List (α × β) → ENNReal := fun W => ∑ i : α, (bucket (atIndex i W) - cap)
  apply excess_le_of_capped_exp_general (marked (α := α) v) T
    (fun W => ∑ i : α, bucket (atIndex i W)) capped residual
    theta t bound residualBound resultBound htheta ht hresBound
  · intro W
    exact ENNReal.sum_ne_top.mpr fun i _ => ne_top_of_le_ne_top hcap (min_le_right _ _)
  · intro W
    change (∑ i : α, bucket (atIndex i W)) ≤
      (∑ i : α, min (bucket (atIndex i W)) cap) + ∑ i : α, (bucket (atIndex i W) - cap)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact le_of_eq (by rw [add_comm, tsub_add_min])
  · apply law_marked_exp_sum_general v hv T (fun _ L => min (bucket L) cap) t bound ht.le hbound
    · intro i L
      exact ne_top_of_le_ne_top hcap (min_le_right _ _)
    · intro i L b R
      exact min_le_min (hmono L b R) le_rfl
    · exact hmgf
  · change lawAvg (marked (α := α) v) T
      (fun W => ∑ i : α, (bucket (atIndex i W) - cap)) ≤ _
    rw [lawAvg_sum]
    apply le_trans (le_of_eq (Finset.sum_congr rfl (fun i _ =>
      law_marked_atIndex v hv i T (fun L => bucket L - cap))))
    exact hres
  · exact hscalar

#print axioms law_bucket_excess_general
end ClaudeWCT.Numerics.SharedPathWinsor

namespace ClaudeWCT.Numerics.CanonicalCompression


/-- Convert a checked integer row into the real-valued rejection-loop inequality. -/
theorem transition_sound (zn zd den weighted value rejected unit : Nat)
    (hzd : 0 < zd) (hden : 0 < den) (hunit : 0 < unit)
    (hsub : zn * rejected ≤ zd * den)
    (hrow : zn * weighted ≤ value * (zd * den - zn * rejected)) :
    ((zn : ℝ) / zd) * ((weighted : ℝ) / (den * unit) +
        ((rejected : ℝ) / den) * ((value : ℝ) / unit)) ≤ (value : ℝ) / unit := by
  have hcast : (zn : ℝ) * weighted ≤ value * ((zd : ℝ) * den - (zn : ℝ) * rejected) := by
    have h := (Nat.cast_le (α := ℝ)).2 hrow
    push_cast [Nat.cast_sub hsub] at h
    exact h
  have he : ((zn : ℝ) / zd) * ((weighted : ℝ) / (den * unit) +
      ((rejected : ℝ) / den) * ((value : ℝ) / unit)) - (value : ℝ) / unit =
      ((zn : ℝ) * weighted - value * ((zd : ℝ) * den - (zn : ℝ) * rejected)) /
        ((zd : ℝ) * den * unit) := by
    have hz : (zd : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hzd
    have hd : (den : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hden
    have hu : (unit : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hunit
    field_simp
    <;> ring
  rw [← sub_nonpos, he]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcast) (by positivity)

#print axioms transition_sound
end ClaudeWCT.Numerics.CanonicalCompression


namespace ClaudeWCT.Numerics.SharedPathWinsor
open Finset
set_option maxHeartbeats 1000000

/-- The exponential cost per unit of retained first moment increases up to
the cap. This avoids losing the entire width of a geometric bin. -/
theorem exp_secant (t x u : ℝ) (hx : 0 ≤ x) (hxu : x ≤ u) (hu : 0 < u) :
    Real.exp (t * x) - 1 ≤ (x / u) * (Real.exp (t * u) - 1) := by
  have hr0 : 0 ≤ x / u := div_nonneg hx hu.le
  have hr1 : x / u ≤ 1 := (div_le_one hu).2 hxu
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (t * u))
    (show 0 ≤ 1 - x / u by linarith) hr0 (show (1 - x / u) + x / u = 1 by ring)
  have he : (1 - x / u) * 0 + (x / u) * (t * u) = t * x := by
    field_simp
    <;> ring
  simp only [smul_eq_mul, Real.exp_zero, mul_one] at hc
  rw [he] at hc
  nlinarith

end ClaudeWCT.Numerics.SharedPathWinsor

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600

/-- The unmarked occupancy polynomial counts all child/rank histories. -/
theorem fullOtherPoly_model {β : Type*} [Fintype β]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (n r : ℕ) :
    fullOtherPoly H (Fintype.card β) n r =
      ∑ E : Fin r → Fin n × β, (X : ℕ[X]) ^ coordinateCoverage val E := by
  classical
  have h := sum_word_product (C := Fin n) (r := r) val H hH
    (fun _ a => (X : ℕ[X]) ^ a.val)
  symm
  calc
    (∑ E : Fin r → Fin n × β, (X : ℕ[X]) ^ coordinateCoverage val E) =
        ∑ E : Fin r → Fin n × β, ∏ c : Fin n, (X : ℕ[X]) ^ atChildCoverage val E c := by
      apply Finset.sum_congr rfl
      intro E _
      rw [Finset.prod_pow_eq_pow_sum, coordinateCoverage_sum]
    _ = fullOtherPoly H (Fintype.card β) n r := by
      simpa only [atChildCoverageFin, fullOtherPoly, lawPoly, ← Polynomial.C_eq_natCast, Nat.cast_id] using h

theorem fullOtherPoly_coeff {β : Type*} [Fintype β]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (n r c : ℕ) :
    (fullOtherPoly H (Fintype.card β) n r).coeff c =
      #{E : Fin r → Fin n × β | coordinateCoverage val E = c} := by
  classical
  rw [fullOtherPoly_model val H hH]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, Finset.card_filter,
    eq_comm]

#print axioms fullOtherPoly_model
#print axioms fullOtherPoly_coeff
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathReflection
open Finset

theorem profileList_get (i : Fin 434) :
    profileList i = profiles[i.val]'(by rw [profile_count]; exact i.isLt) := by
  simp only [profileList, List.getElem?_eq_getElem (by rw [profile_count]; exact i.isLt),
    Option.getD_some]

theorem profile_valid (K : Nat) (hK : K ∈ [64, 128]) (r : Fin 21) (i : Fin 434)
    (hu : used (profileList i) ≤ r.val) :
    (∑ a : Fin 21, profileVector K r.val (profileList i) a) = K ∧
    (∑ a : Fin 21, profileVector K r.val (profileList i) a * a.val) = r.val ∧
    Nat.multinomial univ (profileVector K r.val (profileList i)) *
      (r.val.factorial / ∏ a : Fin 21, a.val.factorial ^ profileVector K r.val (profileList i) a) =
        profileWeight K r.val (profileList i) := by
  have h := List.all_eq_true.mp (show profileChecks = true from profile_checks) K hK
  have h := List.all_eq_true.mp h r.val (List.mem_range.mpr r.isLt)
  have hm : profileList i ∈ profiles := by rw [profileList_get]; exact List.getElem_mem _
  have h := List.all_eq_true.mp h (profileList i) hm
  simpa only [if_pos hu, decide_eq_true_eq] using h

theorem profileVector_injective (K r : Nat) :
    Function.Injective (fun i : Fin 434 => profileVector K r (profileList i)) := by
  intro i j heq
  have hl : profileList i = profileList j := by
    apply List.ext_getElem
    · rw [profile_lengths, profile_lengths]
    · intro a ha hb
      have ha7 : a < 7 := by simpa only [profile_lengths] using ha
      have h := congrFun heq (⟨a+2, by omega⟩ : Fin 21)
      simpa only [profileVector, show ¬a+2=0 by omega, show ¬a+2=1 by omega,
        if_false, Nat.add_sub_cancel, List.getElem?_eq_getElem ha,
        List.getElem?_eq_getElem hb, Option.getD_some] using h
  rw [profileList_get, profileList_get] at hl
  exact Fin.ext (profile_nodup.getElem_inj_iff.mp hl)

#print axioms profile_valid
#print axioms profileVector_injective
end ClaudeWCT.Numerics.SharedPathReflection


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedPathReflection

theorem profile_vector_product {R : Type*} [CommMonoid R] (K r : Nat)
    (ms : List Nat) (hms : ms.length = 7) (P : Nat → R) :
    (∏ a : Fin 21, P a.val ^ profileVector K r ms a) =
      P 0 ^ (K - ((r - used ms) + groups ms)) * P 1 ^ (r - used ms) *
        (ms.zipIdx 2).foldr (fun e s => P e.2 ^ e.1 * s) 1 := by
  cases ms with
  | nil => simp at hms
  | cons a ms =>
    cases ms with
    | nil => simp at hms
    | cons b ms =>
      cases ms with
      | nil => simp at hms
      | cons c ms =>
        cases ms with
        | nil => simp at hms
        | cons d ms =>
          cases ms with
          | nil => simp at hms
          | cons e ms =>
            cases ms with
            | nil => simp at hms
            | cons f ms =>
              cases ms with
              | nil => simp at hms
              | cons g ms =>
                have hn : ms = [] := List.eq_nil_of_length_eq_zero (by simpa using hms)
                subst ms
                simp [Fin.prod_univ_succ, profileVector, used, groups, List.zipIdx, mul_assoc]

noncomputable def coordinatePoly (K r : Nat) : Nat[X] :=
  ∑ i : Fin 434, if used (profileList i) ≤ r ∧
      r - used (profileList i) + groups (profileList i) ≤ K then
    Polynomial.C (profileWeight K r (profileList i)) *
      (Polynomial.C 563 * X) ^ (r - used (profileList i)) * coverageProfilePoly (profileList i)
    else 0

theorem profile_lawPoly_data (H : Nat → Nat → Nat) (ms : List Nat) (hms : ms.length = 7)
    (hP : ∀ j, 2 ≤ j → j ≤ 8 → lawPoly H 563 j = naturalDataPoly (coverageHData j)) :
    (ms.zipIdx 2).foldr (fun e s => lawPoly H 563 e.2 ^ e.1 * s) 1 =
      coverageProfilePoly ms := by
  have h2 := hP 2 (by decide) (by decide)
  have h3 := hP 3 (by decide) (by decide)
  have h4 := hP 4 (by decide) (by decide)
  have h5 := hP 5 (by decide) (by decide)
  have h6 := hP 6 (by decide) (by decide)
  have h7 := hP 7 (by decide) (by decide)
  have h8 := hP 8 (by decide) (by decide)
  cases ms with
  | nil => simp at hms
  | cons a ms =>
    cases ms with
    | nil => simp at hms
    | cons b ms =>
      cases ms with
      | nil => simp at hms
      | cons c ms =>
        cases ms with
        | nil => simp at hms
        | cons d ms =>
          cases ms with
          | nil => simp at hms
          | cons e ms =>
            cases ms with
            | nil => simp at hms
            | cons f ms =>
              cases ms with
              | nil => simp at hms
              | cons g ms =>
                have hn : ms = [] := List.eq_nil_of_length_eq_zero (by simpa using hms)
                subst ms
                simp [List.zipIdx, coverageProfilePoly, h2, h3, h4, h5, h6, h7, h8]

theorem coordinatePoly_below (H : Nat → Nat → Nat) (K : Nat) (hK : K ∈ [64, 128])
    (r : Fin 21) (h0 : lawPoly H 563 0 = 1)
    (h1 : lawPoly H 563 1 = Polynomial.C 563 * X)
    (hP : ∀ j, 2 ≤ j → j ≤ 8 → lawPoly H 563 j = naturalDataPoly (coverageHData j)) :
    CoeffLE (coordinatePoly K r.val) (fullOtherPoly H 563 K r.val) := by
  classical
  let v : Fin 434 → Fin 21 → Nat := fun i => profileVector K r.val (profileList i)
  let F : (Fin 21 → Nat) → Nat[X] := fun m =>
    if (∑ a, m a * a.val) = r.val then
      (Nat.multinomial univ m : Nat[X]) *
        (r.val.factorial / ∏ a : Fin 21, a.val.factorial ^ m a : Nat) *
          ∏ a : Fin 21, lawPoly H 563 a.val ^ m a else 0
  let s : Finset (Fin 434) := univ.filter (fun i => used (profileList i) ≤ r.val ∧
    r.val - used (profileList i) + groups (profileList i) ≤ K)
  have hf : fullOtherPoly H 563 K r.val = ∑ m ∈ piAntidiag univ K, F m :=
    occupancy_profile_sum_bounded K r.val 20 (by omega) (lawPoly H 563)
  have he : coordinatePoly K r.val = ∑ i ∈ s, F (v i) := by
    rw [coordinatePoly, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hu : used (profileList i) ≤ r.val ∧
        r.val - used (profileList i) + groups (profileList i) ≤ K
    · rw [if_pos hu, if_pos hu]
      dsimp [F, v]
      have hcheck := profile_valid K hK r i hu.1
      rw [if_pos hcheck.2.1, ← Nat.cast_mul, hcheck.2.2,
        profile_vector_product K r.val _ (profile_lengths i), h0, h1,
        one_pow, one_mul, profile_lawPoly_data H _ (profile_lengths i) hP]
      simp only [← Polynomial.C_eq_natCast, Nat.cast_id, mul_assoc]
    · simp only [if_neg hu]
  have hmem : ∀ i ∈ s, v i ∈ piAntidiag univ K := by
    intro i hi
    exact Finset.mem_piAntidiag.mpr
      ⟨(profile_valid K hK r i (Finset.mem_filter.mp hi).2.1).1,
        fun _ _ => Finset.mem_univ _⟩
  rw [he, hf]
  exact coeffSum_injective s (piAntidiag univ K) v
    (profileVector_injective K r.val) hmem F

#print axioms profile_vector_product
#print axioms coordinatePoly_below
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.Winsor

/-- Reuse the existing Taylor certificate at a rationally rounded argument. -/
theorem rational_exp_upper (S x u bound : Nat)
    (hS : 0 < S) (hxu : x ≤ 8 * u) (hu : u ≤ S)
    (hround : S * taylorNumN S u ^ 8 ≤ bound * taylorDenN S ^ 8) :
    Real.exp ((x : ℝ) / S) ≤ (bound : ℝ) / S := by
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hd : (0 : ℝ) < taylorDenN S := by
    unfold taylorDenN
    norm_num [ClaudeWCT.Numerics.Kernel.fact]
    positivity
  have hx : (x : ℝ) / S ≤ 8 * ((u : ℝ) / S) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hxu) hs.le
  have hur : (u : ℝ) / S ≤ 1 := (div_le_one hs).mpr (by exact_mod_cast hu)
  have he := exp8_le_taylor16 ((u : ℝ) / S) (by positivity) hur
  have ht : taylor16 ((u : ℝ) / S) ^ 8 ≤ (bound : ℝ) / S := by
    rw [← taylorNumN_ratio S u hs.ne', div_pow]
    apply (div_le_div_iff₀ (pow_pos hd 8) hs).mpr
    have hc : (S : ℝ) * (taylorNumN S u : ℝ) ^ 8 ≤
        (bound : ℝ) * (taylorDenN S : ℝ) ^ 8 := by exact_mod_cast hround
    nlinarith
  exact (Real.exp_le_exp.mpr hx).trans (he.trans ht)

#print axioms rational_exp_upper
end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedPathReflection
/-- Retained unmarked profiles are a subdistribution of true coverage counts. -/
theorem coordinatePoly_coeff_below {β : Type*} [Fintype β]
    (val : β → Fin 6 → Nat) (H : Nat → Nat → Nat)
    (hH : FullCoverageHistogram val H) (hβ : Fintype.card β = 563)
    (K : Nat) (hK : K ∈ [64, 128]) (r : Fin 21)
    (h0 : lawPoly H 563 0 = 1) (h1 : lawPoly H 563 1 = Polynomial.C 563 * X)
    (hP : ∀ j, 2 ≤ j → j ≤ 8 → lawPoly H 563 j = naturalDataPoly (coverageHData j))
    (c : Nat) :
    (coordinatePoly K r.val).coeff c ≤
      #{E : Fin r.val → Fin K × β | coordinateCoverage val E = c} := by
  have h := coordinatePoly_below H K hK r h0 h1 hP c
  rw [← hβ, fullOtherPoly_coeff val H hH] at h
  exact h

#print axioms coordinatePoly_coeff_below
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathReflection

theorem bin_pair_bounds_of_check (hcheck : binRunsCheck = true)
    (c b : Nat) (h : (c, b) ∈ binPairs) :
    1 ≤ c ∧ c * 100 ^ b ≤ 101 ^ b ∧ 100 * 101 ^ b ≤ 101 * c * 100 ^ b := by
  obtain ⟨e, he, hmem⟩ := List.mem_flatMap.mp h
  obtain ⟨a, ha, hpair⟩ := List.mem_map.mp hmem
  have hac : a = c := congrArg Prod.fst hpair
  have heb : e.2.2 = b := congrArg Prod.snd hpair
  subst a
  have hr := List.all_eq_true.mp hcheck e he
  simp only [decide_eq_true_eq] at hr
  have hc := List.mem_range'.mp ha
  rcases hc with ⟨i, hi, hc⟩
  simp only [Nat.one_mul] at hc
  rcases hr with ⟨hlo, hle, hupper, hlower⟩
  have hlow : e.1 ≤ c := by omega
  have hhigh : c ≤ e.2.1 := by omega
  rw [← heb]
  exact ⟨hlo.trans hlow, (Nat.mul_le_mul_right _ hhigh).trans hupper,
    hlower.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hlow))⟩

theorem bin_lookup_pair (hidx : binPairs.map Prod.fst = List.range' 1 11260)
    (c : Nat) (hc : 1 ≤ c) (hC : c ≤ 11260) :
    (c, bins[c]?.getD 0) ∈ binPairs := by
  have hlen : binPairs.length = 11260 := by
    have h := congrArg List.length hidx
    simpa only [List.length_map, List.length_range'] using h
  have hi : c - 1 < binPairs.length := by omega
  have hp : (binPairs[c - 1]).1 = c := by
    have h := congrArg (fun xs : List Nat => xs[c-1]?.getD 0) hidx
    rw [List.getElem?_eq_getElem (show c-1 < (binPairs.map Prod.fst).length by
      simpa only [List.length_map] using hi),
      List.getElem?_eq_getElem (show c-1 < (List.range' 1 11260).length by
        simp only [List.length_range']; omega)] at h
    simp only [List.getElem_map, List.getElem_range', Option.getD_some, Nat.one_mul] at h
    omega
  have hb : bins[c]?.getD 0 = (binPairs[c-1]).2 := by
    simp only [bins, List.getElem?_toArray]
    have he : c = (c-1)+1 := by omega
    conv_lhs => rw [he, List.getElem?_cons_succ]
    rw [List.getElem?_eq_getElem (show c-1 < (binPairs.map Prod.snd).length by
      simpa only [List.length_map] using hi)]
    simp only [List.getElem_map, Option.getD_some]
  have hm : ((binPairs[c-1]).1, (binPairs[c-1]).2) ∈ binPairs := List.getElem_mem hi
  simpa only [hp, ← hb] using hm

theorem bin_lookup_bounds (hcheck : binRunsCheck = true)
    (hidx : binPairs.map Prod.fst = List.range' 1 11260)
    (c : Nat) (hc : 1 ≤ c) (hC : c ≤ 11260) :
    c * 100 ^ (bins[c]?.getD 0) ≤ 101 ^ (bins[c]?.getD 0) ∧
    100 * 101 ^ (bins[c]?.getD 0) ≤ 101 * c * 100 ^ (bins[c]?.getD 0) :=
  (bin_pair_bounds_of_check hcheck c _ (bin_lookup_pair hidx c hc hC)).2

theorem geometric_bin_interval (c b : Nat)
    (hupper : c * 100 ^ b ≤ 101 ^ b)
    (hlower : 100 * 101 ^ b ≤ 101 * c * 100 ^ b) :
    (101 / 100 : ℝ) ^ b * (100 / 101) ≤ (c : ℝ) ∧
      (c : ℝ) ≤ (101 / 100 : ℝ) ^ b := by
  have hp : (0 : ℝ) < 100 ^ b := by positivity
  have hu : (c : ℝ) * 100 ^ b ≤ 101 ^ b := by exact_mod_cast hupper
  have hl : (100 : ℝ) * 101 ^ b ≤ 101 * c * 100 ^ b := by exact_mod_cast hlower
  constructor
  · rw [div_pow, div_mul_div_comm]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 100 ^ b * 101)).mpr
    nlinarith
  · rw [div_pow]
    exact (le_div_iff₀ hp).mpr hu

#print axioms bin_lookup_bounds
#print axioms geometric_bin_interval
end ClaudeWCT.Numerics.SharedPathReflection


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedPathReflection

theorem foldl_weighted_sum {α : Type*} (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun s e => s + f e) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

theorem foldl_weighted_prod {α : Type*} (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun s e => s * f e) a = a * (xs.map f).prod := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_assoc]

theorem foldr_weighted_prod {α : Type*} (xs : List α) (f : α → Nat) :
    xs.foldr (fun e s => f e * s) 1 = (xs.map f).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem profilePacked_eq (bits : Nat) (ms : List Nat) :
    profilePacked bits ms = (coverageProfilePoly ms).eval (2 ^ bits) := by
  rw [coverageProfilePoly_eval]
  simp only [profilePacked, coverageProfilePack, foldl_weighted_prod,
    foldr_weighted_prod, one_mul, coverageHPackBits_eq]

theorem sum_profiles (f : List Nat → Nat) :
    (profiles.map f).sum = ∑ i : Fin 434, f (profileList i) := by
  have h : ∀ (xs : List (List Nat)) (n : Nat) (hn : xs.length = n),
      (xs.map f).sum = ∑ i : Fin n, f (xs[i.val]'(by omega)) := by
    intro xs n hn
    subst hn
    rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]
  rw [h profiles 434 profile_count]
  apply Finset.sum_congr rfl
  intro i _
  rw [profileList_get]

theorem coordinatePacked_eval (bits K r : Nat) :
    coordinatePacked bits K r = (coordinatePoly K r).eval (2 ^ bits) := by
  let f : List Nat → Nat := fun ms =>
    if used ms ≤ r ∧ r - used ms + groups ms ≤ K then
      profileWeight K r ms * 563 ^ (r - used ms) *
        (profilePacked bits ms <<< (bits * (r - used ms))) else 0
  have he : coordinatePacked bits K r = (profiles.map f).sum := by
    have hf : (fun acc ms => if used ms ≤ r ∧ r - used ms + groups ms ≤ K then
        acc + profileWeight K r ms * 563 ^ (r - used ms) *
          (profilePacked bits ms <<< (bits * (r - used ms))) else acc) =
        (fun acc ms => acc + f ms) := by
      funext acc ms
      dsimp [f]
      split_ifs <;> simp
    rw [coordinatePacked, hf, foldl_weighted_sum, Nat.zero_add]
  rw [he, sum_profiles, coordinatePoly, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [f]
  split_ifs with h
  · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Nat.shiftLeft_eq, pow_mul, profilePacked_eq]
    ring
  · simp

#print axioms coordinatePacked_eval
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathReflection

theorem geometric_add_interval (d b : Nat)
    (hu : 100 ^ b * (101 ^ d + 100 ^ d) ≤ 101 ^ (b+d))
    (hl : 100 * 101 ^ (b+d) ≤ 101 * 100 ^ b * (101 ^ d + 100 ^ d)) :
    (101 / 100 : ℝ) ^ (b+d) * (100/101) ≤ (101/100 : ℝ)^d + 1 ∧
      (101/100 : ℝ)^d + 1 ≤ (101/100 : ℝ)^(b+d) := by
  have hu' : (100 : ℝ)^b * (101^d + 100^d) ≤ 101^(b+d) := by exact_mod_cast hu
  have hl' : (100 : ℝ)*101^(b+d) ≤ 101*100^b*(101^d+100^d) := by exact_mod_cast hl
  have hB : (0 : ℝ) < 100^b := by positivity
  have hD : (0 : ℝ) < 100^d := by positivity
  have he : ((101/100 : ℝ)^d + 1) = (101^d+100^d)/100^d := by
    rw [div_pow, add_div, div_self hD.ne']
  rw [he, div_pow, pow_add (100 : ℝ) b d]
  constructor
  · rw [div_mul_div_comm]
    apply (div_le_div_iff₀ (by positivity) hD).mpr
    nlinarith
  · apply (div_le_div_iff₀ hD (by positivity)).mpr
    nlinarith


#print axioms geometric_add_interval
end ClaudeWCT.Numerics.SharedPathReflection


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.Thinning
open ClaudeWCT.Numerics.Kernel (wpos wneg)

theorem signed_count_to_nat (count K base r : Nat) (d : List (Nat × Int))
    (hK : 0 < K) (he : (count : Int) = K * tmom d base r) :
    count = K * (wpos d base r - wneg d base r) := by
  have hK' : (0 : Int) < K := by exact_mod_cast hK
  have hnonneg : 0 ≤ tmom d base r := by
    have hn := Int.natCast_nonneg count
    nlinarith
  have hw := wpos_sub_wneg d base r
  have hle : wneg d base r ≤ wpos d base r := by omega
  have he' : (count : Int) = (K * (wpos d base r - wneg d base r) : Nat) := by
    rw [Nat.cast_mul, Nat.cast_sub hle, hw]
    exact he
  exact_mod_cast he'

theorem coordinate_first_count {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (K r : Nat) (hK : 0 < K) :
    #{y : (Fin K × β) × (Fin r → Fin K × β) |
      CovAt val y.1.1 (val y.1.2) y.2} = coordinateFormula K r := by
  have h := coord_first (C := Fin K) val w1Data
    (fun p => (hW p).trans (tmom_zero w1Data p).symm) r
  rw [Fintype.card_fin, hβ] at h
  exact signed_count_to_nat _ K ((K-1)*563) r w1Data hK h

theorem coordinate_first_sum {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (K r : Nat) (hK : 0 < K) :
    ∑ E : Fin r → Fin K × β, coordinateCoverage val E = coordinateFormula K r := by
  classical
  have h := coordinate_first_count val hβ hW K r hK
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm] at h
  simpa only [coordinateCoverage, Finset.card_filter] using h

theorem coordinate_near_count {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (i : Fin 6) (hW : WFTable val i) (K r : Nat) (hK : 0 < K) :
    #{y : (Fin K × β) × (Fin r → Fin K × β) |
      CovAtExcept val i y.1.1 (val y.1.2) y.2} =
      K * (wpos (wfData i) ((K-1)*563) r - wneg (wfData i) ((K-1)*563) r) := by
  have h := coord_near (C := Fin K) val i (wfData i)
    (fun p => (hW p).trans (tmom_zero (wfData i) p).symm) r
  rw [Fintype.card_fin, hβ] at h
  exact signed_count_to_nat _ K ((K-1)*563) r (wfData i) hK h

theorem coordinate_near_sum {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : ∀ i, WFTable val i) (K r : Nat) (hK : 0 < K) :
    (∑ i : Fin 6, #{y : (Fin K × β) × (Fin r → Fin K × β) |
      CovAtExcept val i y.1.1 (val y.1.2) y.2}) = coordinateNearFormula K r := by
  simp_rw [coordinate_near_count val hβ _ (hW _) K r hK]
  simp [coordinateNearFormula, Fin.sum_univ_succ, List.range_succ,
    List.foldr_append, mul_add, add_assoc]

#print axioms coordinate_first_sum
#print axioms coordinate_near_sum
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset

theorem sum_selector_occupancy {M : Type*} [AddCommMonoid M]
    (r : Nat) (F : Nat → Nat → M) :
    (∑ o : Fin r → Fin 2, F (occ o 0) (occ o 1)) =
      ∑ t ∈ Finset.range (r+1), r.choose t • F t (r-t) := by
  rw [sum_occ (fun k => F (k 0) (k 1))]
  symm
  refine Finset.sum_bij (fun t _ => ![t, r-t]) ?_ ?_ ?_ ?_
  · intro t ht
    apply Finset.mem_piAntidiag.mpr
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    have ht' := Finset.mem_range.mp ht
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    omega
  · intro t ht u hu he
    simpa using congrArg (fun k : Fin 2 → Nat => k 0) he
  · intro k hk
    have hs := (Finset.mem_piAntidiag.mp hk).1
    simp only [Fin.sum_univ_two] at hs
    refine ⟨k 0, Finset.mem_range.mpr (by omega), ?_⟩
    funext i
    fin_cases i <;> simp <;> omega
  · intro t ht
    have ht' : t ≤ r := by have h := Finset.mem_range.mp ht; omega
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [Nat.multinomial_univ_two, show t+(r-t)=r by omega,
      ← Nat.choose_eq_factorial_div_factorial ht']

#print axioms sum_selector_occupancy
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600

theorem sum_split_selector {α M : Type*} [Fintype α] [AddCommMonoid M]
    {r : Nat} (o : Fin r → Fin 2)
    (f : (Fin (occ o 0) → α) → (Fin (occ o 1) → α) → M) :
    (∑ A : Fin r → α, f (splitRanks o A 0) (splitRanks o A 1)) =
      ∑ A₀ : Fin (occ o 0) → α, ∑ A₁ : Fin (occ o 1) → α, f A₀ A₁ := by
  let e := (splitRanks (β := α) o).trans
    (piFinTwoEquiv (fun s => Fin (occ o s) → α))
  have h := e.sum_comp (fun p => f p.1 p.2)
  rw [Fintype.sum_prod_type] at h
  exact h

noncomputable def selectorValue {α : Type*} [Fintype α]
    (coverage : (n : Nat) → (Fin n → α) → Nat) {r : Nat}
    (o : Fin r → Fin 2) (A B : Fin r → α) (s : Fin 2) : Nat :=
  coverage (occ o s) (splitRanks o A s) * coverage (occ o s) (splitRanks o B s)

theorem sum_pair_selector {α M : Type*} [Fintype α] [AddCommMonoid M]
    (coverage : (n : Nat) → (Fin n → α) → Nat) (r : Nat) (F : Nat → Nat → M) :
    (∑ o : Fin r → Fin 2, ∑ A : Fin r → α, ∑ B : Fin r → α,
      F (selectorValue coverage o A B 0) (selectorValue coverage o A B 1)) =
      ∑ t ∈ range (r+1), r.choose t •
        (∑ A₀ : Fin t → α, ∑ A₁ : Fin (r-t) → α,
          ∑ B₀ : Fin t → α, ∑ B₁ : Fin (r-t) → α,
            F (coverage t A₀ * coverage t B₀) (coverage (r-t) A₁ * coverage (r-t) B₁)) := by
  have hs (o : Fin r → Fin 2) :
      (∑ A : Fin r → α, ∑ B : Fin r → α,
        F (selectorValue coverage o A B 0) (selectorValue coverage o A B 1)) =
        ∑ A₀ : Fin (occ o 0) → α, ∑ A₁ : Fin (occ o 1) → α,
          ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
            F (coverage _ A₀ * coverage _ B₀) (coverage _ A₁ * coverage _ B₁) := by
    unfold selectorValue
    trans ∑ A : Fin r → α, ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
      F (coverage _ (splitRanks o A 0) * coverage _ B₀)
        (coverage _ (splitRanks o A 1) * coverage _ B₁)
    · apply Finset.sum_congr rfl
      intro A _
      exact sum_split_selector o (fun B₀ B₁ =>
        F (coverage _ (splitRanks o A 0) * coverage _ B₀)
          (coverage _ (splitRanks o A 1) * coverage _ B₁))
    · exact sum_split_selector o (fun A₀ A₁ =>
        ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
          F (coverage _ A₀ * coverage _ B₀) (coverage _ A₁ * coverage _ B₁))
  simp_rw [hs]
  exact sum_selector_occupancy r (fun t u =>
    ∑ A₀ : Fin t → α, ∑ A₁ : Fin u → α, ∑ B₀ : Fin t → α, ∑ B₁ : Fin u → α,
      F (coverage t A₀ * coverage t B₀) (coverage u A₁ * coverage u B₁))

#print axioms sum_split_selector
#print axioms sum_pair_selector
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600

theorem independent_pair_sum {α β : Type*} [Fintype α] [Fintype β]
    (f : α → Nat) (g : β → Nat) :
    (∑ a : α, ∑ b : β, ∑ c : α, ∑ d : β, (f a * f c + g b * g d)) =
      (∑ a, f a)^2 * (Fintype.card β)^2 + (Fintype.card α)^2 * (∑ b, g b)^2 := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum, Nat.cast_id]
  ring

theorem binomial_reverse_sum (r : Nat) (f : Nat → Nat) :
    (∑ t ∈ range (r+1), r.choose t * f (r-t)) =
      ∑ t ∈ range (r+1), r.choose t * f t := by
  have h := Finset.sum_range_reflect (fun t => r.choose t * f t) (r+1)
  simp only [Nat.add_sub_cancel] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ r := by have h := Finset.mem_range.mp ht; omega
  rw [Nat.choose_symm ht']

theorem pair_first_moment {α : Type*} [Fintype α]
    (coverage : (n : Nat) → (Fin n → α) → Nat) (r : Nat) :
    (∑ o : Fin r → Fin 2, ∑ A : Fin r → α, ∑ B : Fin r → α,
      (selectorValue coverage o A B 0 + selectorValue coverage o A B 1)) =
      2 * ∑ t ∈ range (r+1), r.choose t *
        (∑ A : Fin t → α, coverage t A)^2 * (Fintype.card α)^(2*(r-t)) := by
  rw [sum_pair_selector coverage r (fun x y => x+y)]
  have hi (t : Nat) := independent_pair_sum (coverage t) (coverage (r-t))
  simp_rw [hi]
  simp only [Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
    mul_add, Finset.sum_add_distrib]
  let m := fun t => (∑ A : Fin t → α, coverage t A)
  have hp (t : Nat) : (Fintype.card α ^ t)^2 = Fintype.card α^(2*t) := by
    rw [← pow_mul, Nat.mul_comm t 2]
  simp only [hp]
  have hs : (∑ t ∈ range (r+1), r.choose t * (Fintype.card α^(2*t) * m (r-t)^2)) =
      ∑ t ∈ range (r+1), r.choose t * m t^2 * Fintype.card α^(2*(r-t)) := by
    have he := binomial_reverse_sum r (fun t => m t^2 * Fintype.card α^(2*(r-t)))
    have hl : (∑ t ∈ range (r+1), r.choose t *
        (m (r-t)^2 * Fintype.card α^(2*(r-(r-t))))) =
        ∑ t ∈ range (r+1), r.choose t * (Fintype.card α^(2*t) * m (r-t)^2) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' : t ≤ r := by have h := Finset.mem_range.mp ht; omega
      rw [Nat.sub_sub_self ht']
      ring
    rw [hl] at he
    simpa only [mul_assoc] using he
  change (∑ t ∈ range (r+1), r.choose t * (m t^2 * Fintype.card α^(2*(r-t)))) +
    (∑ t ∈ range (r+1), r.choose t * (Fintype.card α^(2*t) * m (r-t)^2)) = _
  rw [hs]
  dsimp only [m]
  simp only [mul_assoc]
  omega

#print axioms independent_pair_sum
#print axioms pair_first_moment
end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600

noncomputable def selectorKernel {α : Type*} [Fintype α]
    (kernel : (n : Nat) → (Fin n → α) → (Fin n → α) → Nat) {r : Nat}
    (o : Fin r → Fin 2) (A B : Fin r → α) (s : Fin 2) : Nat :=
  kernel (occ o s) (splitRanks o A s) (splitRanks o B s)

theorem sum_pair_kernel {α M : Type*} [Fintype α] [AddCommMonoid M]
    (kernel : (n : Nat) → (Fin n → α) → (Fin n → α) → Nat)
    (r : Nat) (F : Nat → Nat → M) :
    (∑ o : Fin r → Fin 2, ∑ A : Fin r → α, ∑ B : Fin r → α,
      F (selectorKernel kernel o A B 0) (selectorKernel kernel o A B 1)) =
      ∑ t ∈ range (r+1), r.choose t •
        (∑ A₀ : Fin t → α, ∑ A₁ : Fin (r-t) → α,
          ∑ B₀ : Fin t → α, ∑ B₁ : Fin (r-t) → α,
            F (kernel t A₀ B₀) (kernel (r-t) A₁ B₁)) := by
  have hs (o : Fin r → Fin 2) :
      (∑ A : Fin r → α, ∑ B : Fin r → α,
        F (selectorKernel kernel o A B 0) (selectorKernel kernel o A B 1)) =
        ∑ A₀ : Fin (occ o 0) → α, ∑ A₁ : Fin (occ o 1) → α,
          ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
            F (kernel _ A₀ B₀) (kernel _ A₁ B₁) := by
    unfold selectorKernel
    trans ∑ A : Fin r → α, ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
      F (kernel _ (splitRanks o A 0) B₀) (kernel _ (splitRanks o A 1) B₁)
    · apply Finset.sum_congr rfl
      intro A _
      exact sum_split_selector o (fun B₀ B₁ =>
        F (kernel _ (splitRanks o A 0) B₀) (kernel _ (splitRanks o A 1) B₁))
    · exact sum_split_selector o (fun A₀ A₁ =>
        ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
          F (kernel _ A₀ B₀) (kernel _ A₁ B₁))
  simp_rw [hs]
  exact sum_selector_occupancy r (fun t u =>
    ∑ A₀ : Fin t → α, ∑ A₁ : Fin u → α, ∑ B₀ : Fin t → α, ∑ B₁ : Fin u → α,
      F (kernel t A₀ B₀) (kernel u A₁ B₁))

theorem independent_kernel_sum {α β : Type*} [Fintype α] [Fintype β]
    (f : α → α → Nat) (g : β → β → Nat) :
    (∑ a : α, ∑ b : β, ∑ c : α, ∑ d : β, (f a c + g b d)) =
      (∑ a, ∑ c, f a c) * (Fintype.card β)^2 +
      (Fintype.card α)^2 * (∑ b, ∑ d, g b d) := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum, Nat.cast_id]
  ring

theorem pair_kernel_moment {α : Type*} [Fintype α]
    (kernel : (n : Nat) → (Fin n → α) → (Fin n → α) → Nat) (r : Nat) :
    (∑ o : Fin r → Fin 2, ∑ A : Fin r → α, ∑ B : Fin r → α,
      (selectorKernel kernel o A B 0 + selectorKernel kernel o A B 1)) =
      2 * ∑ t ∈ range (r+1), r.choose t *
        (∑ A : Fin t → α, ∑ B : Fin t → α, kernel t A B) *
          (Fintype.card α)^(2*(r-t)) := by
  rw [sum_pair_kernel kernel r (fun x y => x+y)]
  have hi (t : Nat) := independent_kernel_sum (kernel t) (kernel (r-t))
  simp_rw [hi]
  simp only [Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
    mul_add, Finset.sum_add_distrib]
  let m := fun t => (∑ A : Fin t → α, ∑ B : Fin t → α, kernel t A B)
  have hp (t : Nat) : (Fintype.card α ^ t)^2 = Fintype.card α^(2*t) := by
    rw [← pow_mul, Nat.mul_comm t 2]
  simp only [hp]
  have hs : (∑ t ∈ range (r+1), r.choose t * (Fintype.card α^(2*t) * m (r-t))) =
      ∑ t ∈ range (r+1), r.choose t * m t * Fintype.card α^(2*(r-t)) := by
    have he := binomial_reverse_sum r (fun t => m t * Fintype.card α^(2*(r-t)))
    have hl : (∑ t ∈ range (r+1), r.choose t *
        (m (r-t) * Fintype.card α^(2*(r-(r-t))))) =
        ∑ t ∈ range (r+1), r.choose t * (Fintype.card α^(2*t) * m (r-t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' : t ≤ r := by have h := Finset.mem_range.mp ht; omega
      rw [Nat.sub_sub_self ht']
      ring
    rw [hl] at he
    simpa only [mul_assoc] using he
  change (∑ t ∈ range (r+1), r.choose t * (m t * Fintype.card α^(2*(r-t)))) +
    (∑ t ∈ range (r+1), r.choose t * (Fintype.card α^(2*t) * m (r-t))) = _
  rw [hs]
  dsimp only [m]
  simp only [mul_assoc]
  omega

theorem pair_near_moment {α : Type*} [Fintype α]
    (coverage near : (n : Nat) → (Fin n → α) → Nat) (r : Nat) :
    (∑ o : Fin r → Fin 2, ∑ A : Fin r → α, ∑ B : Fin r → α,
      (selectorKernel (fun n A B => near n A * coverage n B + coverage n A * near n B) o A B 0 +
       selectorKernel (fun n A B => near n A * coverage n B + coverage n A * near n B) o A B 1)) =
      4 * ∑ t ∈ range (r+1), r.choose t *
        (∑ A : Fin t → α, coverage t A) * (∑ A : Fin t → α, near t A) *
          (Fintype.card α)^(2*(r-t)) := by
  rw [pair_kernel_moment]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

#print axioms pair_kernel_moment
#print axioms pair_near_moment
end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset

theorem independent_forest_first {α β : Type*} [Fintype α] [Fintype β]
    (f : α → Nat) (g : β → Nat) :
    (∑ A : Fin 4 → α, ∑ B : β, (∏ i, f (A i)) * g B) =
      (∑ A, f A)^4 * (∑ B, g B) := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Fintype.sum_pow]

theorem independent_forest_marked {α : Type*} [Fintype α]
    (f near : α → Nat) (k : Fin 4) :
    (∑ A : Fin 4 → α, ∏ i, if i = k then near (A i) else f (A i)) =
      (∑ A, near A) * (∑ A, f A)^3 := by
  classical
  rw [← Fintype.prod_sum (fun (i : Fin 4) (a : α) => if i = k then near a else f a)]
  fin_cases k <;> simp [Fin.prod_univ_succ] <;> ring

theorem independent_forest_near {α β : Type*} [Fintype α] [Fintype β]
    (f near : α → Nat) (g nearG : β → Nat) :
    (∑ A : Fin 4 → α, ∑ B : β,
      ((∑ k : Fin 4, ∏ i, if i = k then near (A i) else f (A i)) * g B +
        (∏ i, f (A i)) * nearG B)) =
      4 * (∑ A, near A) * (∑ A, f A)^3 * (∑ B, g B) +
        (∑ A, f A)^4 * (∑ B, nearG B) := by
  classical
  simp only [Finset.sum_add_distrib]
  rw [independent_forest_first f nearG]
  congr 1
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [independent_forest_marked f near]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

#print axioms independent_forest_first
#print axioms independent_forest_near
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.Thinning

abbrev PairHistory (β : Type) (r : Nat) :=
  (Fin r → Fin 2) × (Fin r → Fin 64 × β) × (Fin r → Fin 64 × β)

noncomputable def coordinateNear {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) {K r : Nat} (E : Fin r → Fin K × β) : Nat := by
  classical
  exact ∑ i : Fin 6, #{y : Fin K × β | CovAtExcept val i y.1 (val y.2) E}

theorem coordinate_near_history_sum {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : ∀ i, WFTable val i) (K r : Nat) (hK : 0 < K) :
    (∑ E : Fin r → Fin K × β, coordinateNear val E) = coordinateNearFormula K r := by
  classical
  have he (i : Fin 6) :
      (∑ E : Fin r → Fin K × β, #{y : Fin K × β | CovAtExcept val i y.1 (val y.2) E}) =
        #{y : (Fin K × β) × (Fin r → Fin K × β) |
          CovAtExcept val i y.1.1 (val y.1.2) y.2} := by
    simp only [Finset.card_filter, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_comm]
  unfold coordinateNear
  rw [Finset.sum_comm]
  simp_rw [he]
  exact coordinate_near_sum val hβ hW K r hK

noncomputable def pairCoverage {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) {r : Nat} (h : PairHistory β r) : Nat :=
  selectorValue (fun _ => coordinateCoverage val) h.1 h.2.1 h.2.2 0 +
  selectorValue (fun _ => coordinateCoverage val) h.1 h.2.1 h.2.2 1

noncomputable def pairNear {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) {r : Nat} (h : PairHistory β r) : Nat :=
  selectorKernel (fun _ A B => coordinateNear val A * coordinateCoverage val B +
    coordinateCoverage val A * coordinateNear val B) h.1 h.2.1 h.2.2 0 +
  selectorKernel (fun _ A B => coordinateNear val A * coordinateCoverage val B +
    coordinateCoverage val A * coordinateNear val B) h.1 h.2.1 h.2.2 1

theorem pair_coverage_history_sum {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (r : Nat) :
    (∑ h : PairHistory β r, pairCoverage val h) =
      2 * ∑ t ∈ range (r+1), r.choose t * (coordinateFormula 64 t)^2 *
        (64*563)^(2*(r-t)) := by
  have h := pair_first_moment (fun _ => coordinateCoverage val (C := Fin 64)) r
  simp only [Fintype.card_prod, Fintype.card_fin, hβ,
    coordinate_first_sum val hβ hW 64 _ (by decide)] at h
  simpa only [pairCoverage, Fintype.sum_prod_type] using h

theorem pair_near_history_sum {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (hN : ∀ i, WFTable val i) (r : Nat) :
    (∑ h : PairHistory β r, pairNear val h) =
      4 * ∑ t ∈ range (r+1), r.choose t * (coordinateFormula 64 t) *
        (coordinateNearFormula 64 t) * (64*563)^(2*(r-t)) := by
  have h := pair_near_moment (fun _ => coordinateCoverage val (C := Fin 64))
    (fun _ => coordinateNear val (K := 64)) r
  simp only [Fintype.card_prod, Fintype.card_fin, hβ,
    coordinate_first_sum val hβ hW 64 _ (by decide),
    coordinate_near_history_sum val hβ hN 64 _ (by decide)] at h
  simpa only [pairNear, Fintype.sum_prod_type] using h

#print axioms pair_coverage_history_sum
#print axioms pair_near_history_sum
end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedMoments
open Finset
open ClaudeWCT.Numerics.PoissonReflect (range_foldr_eq_sum fact_eq)

theorem row_values (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
  coord64[r]?.getD 0 = coordinateFormula 64 r ∧
  coord128[r]?.getD 0 = coordinateFormula 128 r ∧
  near64[r]?.getD 0 = coordinateNearFormula 64 r ∧
  near128[r]?.getD 0 = coordinateNearFormula 128 r ∧
  pairData[r]?.getD 0 = pairFormula r ∧ pairNearData[r]?.getD 0 = pairNearFormula r := by
  have h := List.all_eq_true.mp hrows r (List.mem_range.mpr hr)
  exact of_decide_eq_true h

theorem pairFormula_model (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
    pairFormula r = 2 * ∑ t ∈ range (r+1), r.choose t * (coordinateFormula 64 t)^2 *
      (64*563)^(2*(r-t)) := by
  unfold pairFormula
  rw [range_foldr_eq_sum]
  apply congrArg (fun n : Nat => 2*n)
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ r := by have h := Finset.mem_range.mp ht; omega
  rw [fact_eq, fact_eq, fact_eq, ← Nat.choose_eq_factorial_div_factorial ht',
    (row_values hrows t (by omega)).1]

theorem pairNearFormula_model (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
    pairNearFormula r = 4 * ∑ t ∈ range (r+1), r.choose t * (coordinateFormula 64 t) *
      (coordinateNearFormula 64 t) * (64*563)^(2*(r-t)) := by
  unfold pairNearFormula
  rw [range_foldr_eq_sum]
  apply congrArg (fun n : Nat => 4*n)
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ r := by have h := Finset.mem_range.mp ht; omega
  rw [fact_eq, fact_eq, fact_eq, ← Nat.choose_eq_factorial_div_factorial ht',
    (row_values hrows t (by omega)).1, (row_values hrows t (by omega)).2.2.1]
end ClaudeWCT.Numerics.SharedMoments

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.Thinning

theorem pair_coverage_data {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
    (∑ h : PairHistory β r, pairCoverage val h) = pairData[r]?.getD 0 := by
  rw [(row_values hrows r hr).2.2.2.2.1, pairFormula_model hrows r hr]
  exact pair_coverage_history_sum val hβ hW r

theorem pair_near_data {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (hN : ∀ i, WFTable val i)
    (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
    (∑ h : PairHistory β r, pairNear val h) = pairNearData[r]?.getD 0 := by
  rw [(row_values hrows r hr).2.2.2.2.2, pairNearFormula_model hrows r hr]
  exact pair_near_history_sum val hβ hW hN r

abbrev ForestHistory (β : Type) (r : Nat) :=
  (Fin 4 → PairHistory β r) × (Fin r → Fin 128 × β)

noncomputable def forestCoverage {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) {r : Nat} (h : ForestHistory β r) : Nat :=
  (∏ i, pairCoverage val (h.1 i)) * coordinateCoverage val h.2

noncomputable def forestNear {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) {r : Nat} (h : ForestHistory β r) : Nat :=
  (∑ k : Fin 4, ∏ i, if i = k then pairNear val (h.1 i) else pairCoverage val (h.1 i)) *
    coordinateCoverage val h.2 +
  (∏ i, pairCoverage val (h.1 i)) * coordinateNear val h.2

theorem forest_coverage_data {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
    (∑ h : ForestHistory β r, forestCoverage val h) = forestMoment r := by
  simp only [forestCoverage, Fintype.sum_prod_type]
  rw [independent_forest_first, pair_coverage_data val hβ hW hrows r hr,
    coordinate_first_sum val hβ hW 128 r (by decide), ← (row_values hrows r hr).2.1]
  rfl

theorem forest_near_data {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (hN : ∀ i, WFTable val i)
    (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
    (∑ h : ForestHistory β r, forestNear val h) = forestNearMoment r := by
  simp only [forestNear, Fintype.sum_prod_type]
  rw [independent_forest_near, pair_coverage_data val hβ hW hrows r hr,
    pair_near_data val hβ hW hN hrows r hr,
    coordinate_first_sum val hβ hW 128 r (by decide), ← (row_values hrows r hr).2.1,
    coordinate_near_history_sum val hβ hN 128 r (by decide), ← (row_values hrows r hr).2.2.2.1]
  rfl

#print axioms forest_coverage_data
#print axioms forest_near_data
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedFees
open ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathWinsor

theorem scale_pos : 0 < scale := by norm_num [scale]

theorem ceil_mul_bound (n d : Nat) (hd : 0 < d) : n ≤ ceilDiv n d * d :=
  winsorCeil_mul_le n d hd


theorem expUpper_sound (x : Nat) (hx : x ≤ 8*scale) :
    Real.exp ((x : ℝ)/scale) ≤ (expUpper x : ℝ)/scale := by
  have hd : 0 < taylorDen scale ^ 8 := by
    have hS := scale_pos
    unfold taylorDen
    norm_num [ClaudeWCT.Numerics.Kernel.fact]
    positivity
  apply rational_exp_upper scale x (ceilDiv x 8) (expUpper x) scale_pos
  · have h := ceil_mul_bound x 8 (by decide)
    omega
  · unfold ceilDiv
    omega
  · exact ceil_mul_bound (scale * taylorNum scale (ceilDiv x 8)^8) (taylorDen scale^8) hd


#print axioms expUpper_sound
end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.CanonicalCounting
open scoped BigOperators Polynomial
open Finset
set_option maxHeartbeats 1000000

def digit (bits packed position : Nat) : Nat :=
  (packed >>> (bits*position)) % 2^bits

theorem digit_histogram {α : Type} [Fintype α] (g : α → Nat) (bits : Nat)
    (hc : Fintype.card α < 2^bits) (k : Nat) :
    digit bits (∑ a, (2^bits)^(g a)) k = (univ.filter fun a => g a = k).card := by
  classical
  let P : Nat[X] := ∑ a, Polynomial.monomial (g a) 1
  have hp (j : Nat) : P.coeff j = (univ.filter fun a => g a = j).card := by
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, eq_comm]
  have hb (j : Nat) : P.coeff j < 2^bits := by
    rw [hp]
    exact (card_filter_le _ _).trans_lt (by simpa using hc)
  have he : P.eval (2^bits) = ∑ a, (2^bits)^(g a) := by simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_mul]
  rw [← he]
  unfold digit
  rw [Nat.shiftRight_eq_div_pow, pow_mul]
  exact (ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) k P hb).trans (hp k)


end ClaudeWCT.Numerics.CanonicalCounting


namespace SigGolfCandidate.Research.SharedFtsModel
attribute [local irreducible] Finset.univ
open scoped BigOperators
open Finset ClaudeWCT.WCT9 SharedPathPacking
open ClaudeWCT.Numerics.SharedFtsCount
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
abbrev Coordinate := Fin 32 × Fin 563
abbrev «Word» := (Fin 4 → Coordinate) × (Fin 5 → Coordinate)
def coordWeight (isA : Bool) (w : Coordinate) : Nat :=
  routineCost w.2 - 75 + (if isA then SharedForest.aCorrection w.1.val else SharedForest.bCorrection w.1.val)
def weight (w : «Word») : Nat :=
  (∑ i, coordWeight true (w.1 i)) + ∑ i, coordWeight false (w.2 i)

theorem rank_list : List.ofFn routineCost = routineCosts := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, routineCosts_length]
  · intro k hk hk'
    rw [List.getElem_ofFn]
    rfl

theorem weighted_ofFn_fold {n : Nat} (v : Fin n → Nat) (bits base : Nat) :
    (∑ i, (2^bits) ^ (v i - base)) =
      (List.ofFn v).foldl (fun s c => s + (1 <<< (bits * (c - base)))) 0 := by
  have hf : ∀ (xs : List Nat) (acc : Nat),
      xs.foldl (fun s c => s + (1 <<< (bits * (c - base)))) acc =
        acc + (xs.map (fun c => (2^bits) ^ (c - base))).sum := by
    intro xs
    induction xs with
    | nil => intro acc; simp
    | cons x xs ih =>
        intro acc
        rw [List.foldl_cons, ih]
        simp only [Nat.shiftLeft_eq, one_mul, ← pow_mul, List.map_cons,
          List.sum_cons, Nat.add_assoc]
  rw [hf, Nat.zero_add, List.map_ofFn, List.sum_ofFn]
  rfl

theorem rank_weight : (∑ r : Fin 563, radix ^ (routineCost r - 75)) = rankPacked := by
  have h := weighted_ofFn_fold routineCost 256 75
  rw [rank_list] at h
  exact h
theorem a_weight_poly (R : Nat) : (∑ c : Fin 32, R ^ SharedForest.aCorrection c.val) =
      13 + 16*R + 3*R^2 := by
  simp only [SharedForest.aCorrection_table]
  norm_num [Fin.sum_univ_succ, Fin.succ, SharedForest.correctionTable]
  ring
theorem b_weight_poly (R : Nat) : (∑ c : Fin 32, R ^ SharedForest.bCorrection c.val) =
      13 + 16*R + 3*R^2 := by
  simp only [SharedForest.bCorrection_table]
  norm_num [Fin.sum_univ_succ, Fin.succ, SharedForest.correctionTable]
  ring
theorem a_weight : (∑ c : Fin 32, radix ^ SharedForest.aCorrection c.val) = fieldA := a_weight_poly radix
theorem b_weight : (∑ c : Fin 32, radix ^ SharedForest.bCorrection c.val) = fieldBC := b_weight_poly radix

theorem sum_prod_pow {α β : Type} [Fintype α] [Fintype β]
    (R : Nat) (u : α → Nat) (v : β → Nat) :
    (∑ w : α × β, R ^ (v w.2 + u w.1)) = (∑ r, R ^ v r) * ∑ c, R ^ u c := by
  rw [Fintype.sum_prod_type]
  simp only [pow_add, ← Finset.sum_mul]
  rw [← Finset.mul_sum]

theorem coord_weight (isA : Bool) :
    (∑ w : Coordinate, radix ^ coordWeight isA w) = rankPacked * (if isA then fieldA else fieldBC) := by
  have hc : (∑ c : Fin 32, radix ^ (if isA then SharedForest.aCorrection c.val else SharedForest.bCorrection c.val)) =
      (if isA then fieldA else fieldBC) := by
    cases isA
    · exact b_weight
    · exact a_weight
  calc
    _ = (∑ r : Fin 563, radix ^ (routineCost r - 75)) *
        ∑ c : Fin 32, radix ^ (if isA then SharedForest.aCorrection c.val else SharedForest.bCorrection c.val) :=
      sum_prod_pow radix _ _
    _ = _ := congrArg₂ Nat.mul rank_weight hc

theorem weighted_pair {α : Type} [Fintype α]
    (R n m : Nat) (f g : α → Nat) :
    (∑ w : (Fin n → α) × (Fin m → α), R ^ ((∑ i, f (w.1 i)) + ∑ i, g (w.2 i))) =
      (∑ a, R ^ f a)^n * (∑ a, R ^ g a)^m := by
  rw [Fintype.sum_prod_type]
  simp only [pow_add]
  have tuples : ∀ (h : α → Nat) (k : Nat), (∑ d : Fin k → α, R ^ (∑ i, h (d i))) = (∑ a : α, R ^ h a) ^ k := by
    intro h k
    classical
    simpa only [Fintype.piFinset_univ, Finset.prod_pow_eq_pow_sum] using
      (Finset.sum_pow' (Finset.univ : Finset α) (fun a => R ^ h a) k).symm
  rw [← Finset.sum_mul_sum, tuples, tuples]

theorem weighted_words : (∑ w : «Word», radix ^ weight w) = fieldForestPacked := by
  calc
    _ = (∑ c : Coordinate, radix ^ coordWeight true c)^4 *
        (∑ c : Coordinate, radix ^ coordWeight false c)^5 :=
      weighted_pair radix 4 5 _ _
    _ = (rankPacked * fieldA)^4 * (rankPacked * fieldBC)^5 :=
      congrArg₂ (fun x y : Nat => x^4*y^5) (coord_weight true) (coord_weight false)
    _ = fieldForestPacked := rfl

theorem word_card_small : Fintype.card «Word» < radix - 1 := by
  norm_num [«Word», Coordinate, Fintype.card_prod, Fintype.card_fun, radix]

theorem accepted_card : (Finset.univ.filter fun w : «Word» => weight w ≤ 103).card = fieldRetained := by
  rw [SigGolfResearch.Gate6.generic_capped_card weight radix 103
    (by norm_num [radix]) word_card_small, weighted_words]
  rfl


end SigGolfCandidate.Research.SharedFtsModel


namespace SigGolfCandidate.Research.SharedFtsModel
open scoped BigOperators
open SigGolfCandidate.T3 ClaudeWCT.WCT9 SharedDigestFields

def group (f : Fin 9 → Coordinate) : «Word» :=
  (fun i => f ⟨2*i.val, by omega⟩,
   fun i => f ⟨min (2*i.val+1) 8, by omega⟩)
def ungroup (w : «Word») (k : Fin 9) : Coordinate :=
  if h : k.val < 8 ∧ k.val % 2 = 0 then w.1 ⟨k.val/2, by omega⟩
  else w.2 ⟨k.val/2, by omega⟩

def groupEquiv : (Fin 9 → Coordinate) ≃ «Word» where
  toFun := group
  invFun := ungroup
  left_inv f := by funext k; fin_cases k <;> rfl
  right_inv w := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl

theorem grouped_weight (f : Fin 9 → Coordinate) :
    (∑ k : Fin 9, coordWeight (SharedForest.firstCoord k.val) (f k)) = weight (group f) := by
  simp only [weight, group, Fin.sum_univ_succ]
  simp only [SharedForest.firstCoord, Fin.val_zero, Fin.val_succ]
  norm_num [Fin.succ]
  omega

def encodeFields (w : «Word») (index : BitVec 31) (gate : Fin 804) : Fields :=
  (fun k => BitVec.ofNat 5 (ungroup w k).1.val,
   fun k => BitVec.ofNat 10 (ungroup w k).2.val,
   index, BitVec.ofNat 14 gate.val)
def decodeFields (f : Fields) : «Word» :=
  group (fun k => (⟨(f.1 k).toNat, (f.1 k).isLt⟩, decodedRank f k))

theorem cost_encode_nat (w : «Word») (index : BitVec 31) (gate : Fin 804) (k : Fin 9) :
    ((encodeFields w index gate).1 k).toNat = (ungroup w k).1.val := by
  simp only [encodeFields, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (ungroup w k).1.isLt

theorem rank_encode_nat (w : «Word») (index : BitVec 31) (gate : Fin 804) (k : Fin 9) :
    ((encodeFields w index gate).2.1 k).toNat = (ungroup w k).2.val := by
  simp only [encodeFields, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h := (ungroup w k).2.isLt
  omega

theorem decodedRank_encode (w : «Word») (index : BitVec 31) (gate : Fin 804) (k : Fin 9) :
    decodedRank (encodeFields w index gate) k = (ungroup w k).2 := by
  apply Fin.ext
  simp only [decodedRank, rank_encode_nat, Nat.mod_eq_of_lt (ungroup w k).2.isLt]

theorem decode_encode (w : «Word») (index : BitVec 31) (gate : Fin 804) :
    decodeFields (encodeFields w index gate) = w := by
  have h : (fun k => (⟨((encodeFields w index gate).1 k).toNat,
      ((encodeFields w index gate).1 k).isLt⟩, decodedRank (encodeFields w index gate) k)) = ungroup w := by
    funext k
    apply Prod.ext
    · apply Fin.ext; exact cost_encode_nat w index gate k
    · exact decodedRank_encode w index gate k
  change group _ = w
  rw [h]
  exact groupEquiv.apply_symm_apply w

theorem cost_encode (w : «Word») (index : BitVec 31) (gate : Fin 804) :
    cost (encodeFields w index gate) = 675 + weight w := by
  have hc : coordinateCost (encodeFields w index gate) = fun k =>
      75 + coordWeight (SharedForest.firstCoord k.val) (ungroup w k) := by
    funext k
    simp only [coordinateCost, decodedRank_encode, cost_encode_nat, coordWeight]
    have h := (routineCost_bounds (ungroup w k).2).1
    omega
  unfold cost
  rw [hc, ← List.ofFn_eq_map, List.sum_ofFn]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, grouped_weight, show group (ungroup w) = w from groupEquiv.apply_symm_apply w]
end SigGolfCandidate.Research.SharedFtsModel


namespace SigGolfCandidate.Research.SharedFtsModel
open scoped BigOperators
open SigGolfCandidate.T3 ClaudeWCT.WCT9 SharedDigestFields
set_option maxHeartbeats 2000000
attribute [local irreducible] SharedDigestFields.cost SharedDigestFields.coordinateCost ClaudeWCT.WCT9.routineCost

theorem accepted_iff (f : Fields) : accepted f = true ↔
    f.2.2.2.toNat < 804 ∧ (∀ k, (f.2.1 k).toNat < 563) ∧ cost f ≤ 778 := by
  simp only [accepted, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  simp only [List.mem_finRange, forall_const]
  tauto

theorem ungroup_decode (f : Fields) : ungroup (decodeFields f) =
    fun k => (⟨(f.1 k).toNat, (f.1 k).isLt⟩, decodedRank f k) :=
  groupEquiv.symm_apply_apply (fun k => (⟨(f.1 k).toNat, (f.1 k).isLt⟩, decodedRank f k))

theorem encode_decode (f : Fields) (hg : f.2.2.2.toNat < 804)
    (hr : ∀ k, (f.2.1 k).toNat < 563) :
    encodeFields (decodeFields f) f.2.2.1 ⟨f.2.2.2.toNat,hg⟩ = f := by
  apply Prod.ext
  · funext k
    apply BitVec.eq_of_toNat_eq
    rw [cost_encode_nat]
    exact congrArg (fun g => (g k).1.val) (ungroup_decode f)
  · apply Prod.ext
    · funext k
      apply BitVec.eq_of_toNat_eq
      rw [rank_encode_nat]
      change (ungroup (decodeFields f) k).2.val = _
      rw [ungroup_decode]
      exact Nat.mod_eq_of_lt (hr k)
    · apply Prod.ext
      · rfl
      · apply BitVec.eq_of_toNat_eq
        change f.2.2.2.toNat % 2^14 = f.2.2.2.toNat
        exact Nat.mod_eq_of_lt f.2.2.2.isLt

theorem accepted_encode (w : «Word») (hw : weight w ≤ 103) (index : BitVec 31) (gate : Fin 804) :
    accepted (encodeFields w index gate) = true := by
  apply (accepted_iff _).mpr
  refine ⟨?_, ?_, ?_⟩
  · change gate.val % 2^14 < 804
    rw [Nat.mod_eq_of_lt (by have h := gate.isLt; omega)]
    exact gate.isLt
  · intro k
    rw [rank_encode_nat]
    exact (ungroup w k).2.isLt
  · rw [cost_encode]
    omega

theorem weight_decode (f : Fields) (hf : accepted f = true) : weight (decodeFields f) ≤ 103 := by
  obtain ⟨hg,hr,hc⟩ := (accepted_iff f).mp hf
  have he := encode_decode f hg hr
  have hw := cost_encode (decodeFields f) f.2.2.1 ⟨f.2.2.2.toNat,hg⟩
  rw [he] at hw
  omega

def acceptedEquiv : {f : Fields // accepted f = true} ≃
    {w : «Word» // weight w ≤ 103} × BitVec 31 × Fin 804 where
  toFun f := (⟨decodeFields f.val, weight_decode f.val f.property⟩,
    f.val.2.2.1, ⟨f.val.2.2.2.toNat, ((accepted_iff _).mp f.property).1⟩)
  invFun v := ⟨encodeFields v.1.val v.2.1 v.2.2, accepted_encode _ v.1.property _ _⟩
  left_inv f := by
    apply Subtype.ext
    exact encode_decode f.val ((accepted_iff _).mp f.property).1 ((accepted_iff _).mp f.property).2.1
  right_inv v := by
    apply Prod.ext
    · apply Subtype.ext
      exact decode_encode _ _ _
    · apply Prod.ext
      · rfl
      · apply Fin.ext
        change v.2.2.val % 2^14 = v.2.2.val
        exact Nat.mod_eq_of_lt (by have h := v.2.2.isLt; omega)

theorem accepted_fields_card : Fintype.card {f : Fields // accepted f = true} =
    (Finset.univ.filter fun w : «Word» => weight w ≤ 103).card * 2^31 * 804 := by
  rw [Fintype.card_congr acceptedEquiv]
  simp only [Fintype.card_prod, Fintype.card_bitVec, Fintype.card_fin,
    Fintype.card_subtype (fun w : «Word» => weight w ≤ 103)]
  omega

#print axioms acceptedEquiv
end SigGolfCandidate.Research.SharedFtsModel


namespace ClaudeWCT.Numerics.CanonicalCounting
open scoped BigOperators
open Finset

theorem card_filter_congr_generic {α : Type} [Fintype α]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ a, p a ↔ q a) : (univ.filter p).card = (univ.filter q).card := by
  apply congrArg Finset.card
  exact Finset.filter_congr (fun a _ => h a)


theorem lower_split (z w s zeros c : Nat) (hs : s ≤ 117) (hw : w ≤ 301)
    (hc : c < 128) :
    65536*z+128*w+s = 65536*zeros+128*201+c ↔ z=zeros ∧ w=201 ∧ s=c := by omega

theorem digit_histogram_of_weighted {α : Type} [Fintype α]
    (g : α → Nat) (P : α → Prop) [DecidablePred P]
    (bits packed k : Nat) (hc : Fintype.card α < 2^bits)
    (hp : (∑ a, (2^bits)^(g a)) = packed)
    (he : ∀ a, g a = k ↔ P a) :
    digit bits packed k = (univ.filter P).card := by
  classical
  exact ((congrArg (fun n => digit bits n k) hp).symm.trans
    (digit_histogram g bits hc k)).trans (card_filter_congr_generic _ _ he)


end ClaudeWCT.Numerics.CanonicalCounting


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

def digit (B p i : Nat) : Nat := p / B^i % B

def packFun (B n : Nat) (f : Nat → Nat) : Nat := ∑ i ∈ range n, f i * B^i

theorem digit_low (B p n i : Nat) (hi : i < n) :
    digit B (p % B^n) i = digit B p i := by
  unfold digit
  have he : n = i+(n-i) := by omega
  rw [he, pow_add, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (dvd_pow_self B (by omega : n-i ≠ 0))

theorem digit_high (B p n i : Nat) :
    digit B (p / B^n) i = digit B p (n+i) := by
  simp only [digit, Nat.div_div_eq_div_mul, pow_add]

theorem packFun_split (B n m : Nat) (f : Nat → Nat) :
    packFun B (n+m) f = packFun B n f + B^n * packFun B m (fun i => f (n+i)) := by
  simp only [packFun, Finset.sum_range_add, pow_add]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem packFun_digits (B p n : Nat) : packFun B n (digit B p) = p % B^n := by
  induction n with
  | zero => simp only [packFun, pow_zero, Finset.range_zero, Finset.sum_empty]; exact (Nat.mod_one p).symm
  | succ n ih =>
    simp only [packFun, Finset.sum_range_succ] at ih ⊢
    rw [ih, pow_succ, Nat.mod_mul]
    simp only [digit]
    ring

#print axioms digit_low
#print axioms packFun_digits
end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

def cross (B : Nat) : Nat → Nat → Nat → Nat
  | 0, a, b => a*b
  | h+1, a, b =>
    let q := B^(2^h)
    cross B h (a%q) (b%q) + q*cross B h (a/q) (b/q)

theorem cross_zero_left (B h b : Nat) : cross B h 0 b = 0 := by
  induction h generalizing b with
  | zero => simp [cross]
  | succ h ih => simp [cross, ih]

theorem cross_zero_right (B h a : Nat) : cross B h a 0 = 0 := by
  induction h generalizing a with
  | zero => simp [cross]
  | succ h ih => simp [cross, ih]

theorem cross_model (B : Nat) (hB : 0 < B) (h a b : Nat)
    (ha : a < B^(2^h)) (hb : b < B^(2^h)) :
    cross B h a b = packFun B (2^h) (fun i => digit B a i * digit B b i) := by
  induction h generalizing a b with
  | zero =>
    simp only [pow_zero, pow_one] at ha hb
    simp [cross, packFun, digit, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  | succ h ih =>
    have he : 2^(h+1) = 2^h+2^h := by simp only [pow_succ]; omega
    have hp : B^(2^(h+1)) = B^(2^h)*B^(2^h) := by rw [he, pow_add]
    have hq : 0 < B^(2^h) := pow_pos hB _
    have ha' : a/B^(2^h) < B^(2^h) := (Nat.div_lt_iff_lt_mul hq).2 (by simpa only [hp] using ha)
    have hb' : b/B^(2^h) < B^(2^h) := (Nat.div_lt_iff_lt_mul hq).2 (by simpa only [hp] using hb)
    rw [cross, ih _ _ (Nat.mod_lt _ hq) (Nat.mod_lt _ hq), ih _ _ ha' hb', he, packFun_split]
    congr 1
    · unfold packFun
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only
      rw [digit_low _ _ _ _ (mem_range.mp hi), digit_low _ _ _ _ (mem_range.mp hi)]
    · congr 1
      unfold packFun
      apply Finset.sum_congr rfl
      intro i _
      dsimp only
      rw [digit_high, digit_high]

#print axioms cross_model
end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000

theorem hadamard_eq_cross (h a b : Nat) :
    hadamard h a b = cross (2^1024) h a b := by
  induction h generalizing a b with
  | zero => rfl
  | succ h ih =>
    rw [hadamard]
    split_ifs with hz
    · rcases hz with rfl | rfl
      · exact (cross_zero_left _ _ _).symm
      · exact (cross_zero_right _ _ _).symm
    · simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow]
      simp only [Nat.and_two_pow_sub_one_eq_mod]
      simp only [pow_mul, ih, cross]
      rw [Nat.mul_comm (cross _ _ _ _)]

#print axioms hadamard_eq_cross
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

def changeBase (B C : Nat) : Nat → Nat → Nat
  | 0, a => a
  | h+1, a =>
    let q := B^(2^h)
    changeBase B C h (a%q) + C^(2^h)*changeBase B C h (a/q)

theorem changeBase_zero (B C h : Nat) : changeBase B C h 0 = 0 := by
  induction h with
  | zero => rfl
  | succ h ih => simp [changeBase, ih]

theorem changeBase_model (B C : Nat) (hB : 0 < B) (h a : Nat)
    (ha : a < B^(2^h)) :
    changeBase B C h a = packFun C (2^h) (digit B a) := by
  induction h generalizing a with
  | zero =>
    simp only [pow_zero, pow_one] at ha
    simp [changeBase, packFun, digit, Nat.mod_eq_of_lt ha]
  | succ h ih =>
    have he : 2^(h+1) = 2^h+2^h := by simp only [pow_succ]; omega
    have hp : B^(2^(h+1)) = B^(2^h)*B^(2^h) := by rw [he, pow_add]
    have hq : 0 < B^(2^h) := pow_pos hB _
    have ha' : a/B^(2^h) < B^(2^h) := (Nat.div_lt_iff_lt_mul hq).2 (by simpa only [hp] using ha)
    rw [changeBase, ih _ (Nat.mod_lt _ hq), ih _ ha', he, packFun_split]
    congr 1
    · unfold packFun
      apply Finset.sum_congr rfl
      intro i hi
      try dsimp only
      rw [digit_low _ _ _ _ (mem_range.mp hi)]
    · congr 1
      unfold packFun
      apply Finset.sum_congr rfl
      intro i _
      try dsimp only
      rw [digit_high]

#print axioms changeBase_model
end ClaudeWCT.Numerics.SharedDigitBlock

namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000

theorem spread_eq_changeBase (h a : Nat) :
    spread h a = changeBase (2^1024) (2^4096) h a := by
  induction h generalizing a with
  | zero => rfl
  | succ h ih =>
    rw [spread]
    split_ifs with hz
    · subst a
      exact (changeBase_zero _ _ _).symm
    · simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow]
      simp only [Nat.and_two_pow_sub_one_eq_mod]
      simp only [pow_mul, ih, changeBase]
      rw [Nat.mul_comm (changeBase _ _ _ _)]

#print axioms spread_eq_changeBase
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open scoped BigOperators Polynomial
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def geomPoly (n : Nat) : Nat[X] := ∑ i ∈ range n, Polynomial.monomial i 1

theorem geomPoly_eval (B n : Nat) : (geomPoly n).eval B = ∑ i ∈ range n, B^i := by
  simp only [geomPoly, Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_mul]

theorem prefixes_eq (a : Nat) :
    prefixes a = (a * (geomPoly 2048).eval (2^1024)) % (2^1024)^2048 := by
  rw [geomPoly_eval, Nat.geomSum_eq (by decide +kernel : 2 ≤ 2^1024)]
  unfold prefixes cutMask
  simp only [Nat.shiftLeft_eq, Nat.one_mul]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [pow_mul]

theorem prefixes_coefficient (P : Nat[X]) (i : Nat) (hi : i < 2048)
    (hb : ∀ j, (P*geomPoly 2048).coeff j < 2^1024) :
    digit (2^1024) (prefixes (P.eval (2^1024))) i = (P*geomPoly 2048).coeff i := by
  rw [prefixes_eq, ← Polynomial.eval_mul, digit_low _ _ _ _ hi]
  exact ClaudeWCT.Numerics.eval_div_pow_mod (pow_pos (by decide) _) i _ hb

#print axioms prefixes_coefficient
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem digit_shift_ge (B p n i : Nat) (hB : 0 < B) (hi : n ≤ i) :
    digit B (p*B^n) i = digit B p (i-n) := by
  have he : i = (i-n)+n := by omega
  unfold digit
  conv_lhs => rw [he, pow_add]
  rw [Nat.mul_div_mul_right _ _ (pow_pos hB _)]

theorem digit_shift_lt (B p n i : Nat) (hB : 0 < B) (hi : i < n) :
    digit B (p*B^n) i = 0 := by
  have he : n = (n-i)+i := by omega
  unfold digit
  rw [he, pow_add, ← Nat.mul_assoc, Nat.mul_div_left _ (pow_pos hB _)]
  have hd : B ∣ B^(n-i) := dvd_pow_self B (by omega : n-i ≠ 0)
  exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hd p)

theorem digit_shift (B p n i : Nat) (hB : 0 < B) :
    digit B (p*B^n) i = if n ≤ i then digit B p (i-n) else 0 := by
  split_ifs with hi
  · exact digit_shift_ge _ _ _ _ hB hi
  · exact digit_shift_lt _ _ _ _ hB (by omega)

theorem packFun_add (B n : Nat) (f g : Nat → Nat) :
    packFun B n (fun i => f i+g i) = packFun B n f + packFun B n g := by
  simp only [packFun, Nat.add_mul, Finset.sum_add_distrib]

theorem packFun_sub (B n : Nat) (f g : Nat → Nat) (hle : ∀ i, i<n → g i ≤ f i) :
    packFun B n (fun i => f i-g i) = packFun B n f - packFun B n g := by
  have he : packFun B n f = packFun B n g + packFun B n (fun i => f i-g i) := by
    rw [← packFun_add]
    unfold packFun
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [Nat.add_sub_of_le (hle i (mem_range.mp hi))]
  rw [he, Nat.add_sub_cancel_left]

theorem sub_packed_digits (B n a b : Nat) (ha : a < B^n) (hb : b < B^n)
    (hle : ∀ i, i<n → digit B b i ≤ digit B a i) :
    a-b = packFun B n (fun i => digit B a i - digit B b i) := by
  rw [packFun_sub _ _ _ _ hle, packFun_digits, packFun_digits,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

#print axioms digit_shift
#print axioms sub_packed_digits
end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000

noncomputable def polyOf (n : Nat) (f : Nat → Nat) : Nat[X] :=
  ∑ i ∈ range n, Polynomial.monomial i (f i)

theorem polyOf_eval (B n : Nat) (f : Nat → Nat) : (polyOf n f).eval B = packFun B n f := by
  simp only [polyOf, packFun, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem polyOf_coeff (n : Nat) (f : Nat → Nat) (i : Nat) :
    (polyOf n f).coeff i = if i<n then f i else 0 := by
  simp [polyOf, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, eq_comm]

theorem digit_packFun (B n : Nat) (f : Nat → Nat) (hB : 0 < B)
    (hf : ∀ j, j<n → f j < B) (i : Nat) (hi : i<n) :
    digit B (packFun B n f) i = f i := by
  have hb (j : Nat) : (polyOf n f).coeff j < B := by
    rw [polyOf_coeff]
    split_ifs with hj
    · exact hf j hj
    · exact hB
  rw [← polyOf_eval]
  exact (ClaudeWCT.Numerics.eval_div_pow_mod hB i _ hb).trans
    (by rw [polyOf_coeff, if_pos hi])

theorem digit_sub (B n a b : Nat) (hB : 0<B) (ha : a<B^n) (hb : b<B^n)
    (hle : ∀ j, j<n → digit B b j ≤ digit B a j) (i : Nat) (hi : i<n) :
    digit B (a-b) i = digit B a i - digit B b i := by
  rw [sub_packed_digits _ _ _ _ ha hb hle]
  apply digit_packFun _ _ _ hB _ _ hi
  intro j _
  exact (Nat.sub_le _ _).trans_lt (Nat.mod_lt _ hB)

#print axioms digit_packFun
#print axioms digit_sub
end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem window_eq (a lo hi : Nat) :
    window a lo hi = (a*(2^1024)^lo) % (2^1024)^2048 -
      (a*(2^1024)^(hi+1)) % (2^1024)^2048 := by
  unfold window cutMask
  simp only [Nat.shiftLeft_eq, Nat.one_mul]
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  simp only [pow_mul]

theorem window_digits (a lo hi i : Nat) (hlo : lo ≤ hi) (hi' : i < 2048)
    (hmono : ∀ j k, j ≤ k → k<2048 → digit (2^1024) a j ≤ digit (2^1024) a k) :
    digit (2^1024) (window a lo hi) i =
      (if lo ≤ i then digit (2^1024) a (i-lo) else 0) -
      (if hi+1 ≤ i then digit (2^1024) a (i-(hi+1)) else 0) := by
  let B : Nat := 2^1024
  have hB : 0<B := pow_pos (by decide) _
  have hp : 0<B^2048 := pow_pos hB _
  have hd (k j : Nat) (hj : j<2048) :
      digit B ((a*B^k)%B^2048) j = if k ≤ j then digit B a (j-k) else 0 := by
    rw [digit_low _ _ _ _ hj, digit_shift _ _ _ _ hB]
  have hle (j : Nat) (hj : j<2048) :
      digit B ((a*B^(hi+1))%B^2048) j ≤ digit B ((a*B^lo)%B^2048) j := by
    rw [hd _ _ hj, hd _ _ hj]
    by_cases hh : hi+1 ≤ j
    · have hl : lo ≤ j := by omega
      rw [if_pos hh, if_pos hl]
      exact hmono _ _ (by omega) (by omega)
    · rw [if_neg hh]
      exact Nat.zero_le _
  rw [window_eq]
  change digit B ((a*B^lo)%B^2048 - (a*B^(hi+1))%B^2048) i = _
  rw [digit_sub _ _ _ _ hB (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) hle i hi',
    hd _ _ hi', hd _ _ hi']

#print axioms window_digits
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open scoped BigOperators Polynomial
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem geomPoly_coeff (n i : Nat) : (geomPoly n).coeff i = if i<n then 1 else 0 :=
  polyOf_coeff n (fun _ => 1) i

theorem prefix_poly_coefficient (P : Nat[X]) (n i : Nat) (hi : i<n) :
    (P*geomPoly n).coeff i = ∑ k ∈ range (i+1), P.coeff k := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  rw [geomPoly_coeff, if_pos (by have hk' := mem_range.mp hk; omega), Nat.mul_one]

theorem prefix_poly_monotone (P : Nat[X]) (n j k : Nat) (hj : j≤k) (hk : k<n) :
    (P*geomPoly n).coeff j ≤ (P*geomPoly n).coeff k := by
  rw [prefix_poly_coefficient _ _ _ (by omega), prefix_poly_coefficient _ _ _ hk]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun _ _ _ => Nat.zero_le _)

theorem prefixes_digits_monotone (P : Nat[X])
    (hb : ∀ j, (P*geomPoly 2048).coeff j < 2^1024)
    (j k : Nat) (hj : j≤k) (hk : k<2048) :
    digit (2^1024) (prefixes (P.eval (2^1024))) j ≤
      digit (2^1024) (prefixes (P.eval (2^1024))) k := by
  rw [prefixes_coefficient _ _ (by omega) hb, prefixes_coefficient _ _ hk hb]
  exact prefix_poly_monotone _ _ _ _ hj hk

#print axioms prefixes_digits_monotone
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem hadamard_11_model (a b : Nat)
    (ha : a < (2^1024)^2048) (hb : b < (2^1024)^2048) :
    hadamard 11 a b = packFun (2^1024) 2048
      (fun i => digit (2^1024) a i * digit (2^1024) b i) := by
  have hq : (2:Nat)^11 = 2048 := by decide
  have ha' : a < (2^1024)^(2^11) := by simpa only [hq] using ha
  have hb' : b < (2^1024)^(2^11) := by simpa only [hq] using hb
  rw [hadamard_eq_cross]
  have h := cross_model (2^1024) (pow_pos (by decide) _) 11 a b ha' hb'
  simpa only [hq] using h

theorem window_bound (a lo hi : Nat) : window a lo hi < (2^1024)^2048 := by
  rw [window_eq]
  exact (Nat.sub_le _ _).trans_lt (Nat.mod_lt _ (pow_pos (pow_pos (by decide) _) _))

theorem directedFirst_model (a pref : Cell) (lo hi shift : Nat)
    (haP : a.1 < (2^1024)^2048) (haF : a.2 < (2^1024)^2048) :
    directedFirst a pref lo hi shift =
      (packFun (2^1024) 2048 (fun i =>
        digit (2^1024) a.2 i * digit (2^1024) (window pref.1 lo hi) i +
        digit (2^1024) a.1 i * digit (2^1024) (window pref.2 lo hi) i) *
        (2^1024)^shift) % (2^1024)^2048 := by
  unfold directedFirst
  rw [hadamard_11_model _ _ haF (window_bound _ _ _),
    hadamard_11_model _ _ haP (window_bound _ _ _), ← packFun_add]
  unfold cutMask
  simp only [Nat.shiftLeft_eq, Nat.one_mul]
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  simp only [pow_mul]

#print axioms directedFirst_model
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset
open scoped BigOperators

theorem packFun_const_mul (B n c : Nat) (f : Nat → Nat) :
    packFun B n (fun i => c * f i) = c * packFun B n f := by
  simp only [packFun, Finset.mul_sum, Nat.mul_assoc]

theorem packFun_sum {α : Type} [Fintype α] (B n : Nat) (f : α → Nat → Nat) :
    packFun B n (fun i => ∑ a, f a i) = ∑ a, packFun B n (f a) := by
  simp only [packFun, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem packFun_window (B p n start : Nat) :
    packFun B n (fun i => digit B p (start+i)) = p / B^start % B^n := by
  conv_lhs => arg 3; ext i; rw [← digit_high]
  exact packFun_digits B (p / B^start) n

theorem digit_window_sum {α : Type} [Fintype α] (B n : Nat)
    (p start coeff : α → Nat) (hB : 0 < B)
    (hsmall : ∀ i, i<n → (∑ a, coeff a * digit B (p a) (start a+i)) < B)
    (i : Nat) (hi : i<n) :
    digit B (∑ a, coeff a * (p a / B^(start a) % B^n)) i =
      ∑ a, coeff a * digit B (p a) (start a+i) := by
  have he : (∑ a, coeff a * (p a / B^(start a) % B^n)) =
      packFun B n (fun j => ∑ a, coeff a * digit B (p a) (start a+j)) := by
    rw [packFun_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [packFun_const_mul, packFun_window]
  rw [he]
  exact digit_packFun B n _ hB hsmall i hi
end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.SharedPathList
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def bucketSeries : List Nat → Nat → Nat → Cell
  | [], _, _ => (0,0)
  | b::bs, c, p =>
    let n := p % 2^512
    let v := bucketSeries bs (c+1) (p / 2^512)
    (n*(2^1024)^b+v.1, (c*n)*(2^1024)^b+v.2)

theorem bucketSeries_zero (bs : List Nat) (c : Nat) : bucketSeries bs c 0 = (0,0) := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp [bucketSeries, ih]

theorem bucket_eq_series (bs : List Nat) (c p : Nat) : bucket bs c p = bucketSeries bs c p := by
  induction bs generalizing c p with
  | nil => rfl
  | cons b bs ih =>
    by_cases hp : p=0
    · subst p
      rw [bucketSeries_zero]
      simp only [bucket, if_true]
    · simp only [bucket, if_neg hp, Nat.and_two_pow_sub_one_eq_mod,
        Nat.shiftRight_eq_div_pow, ih]
      dsimp only [bucketSeries]
      split_ifs with hn
      · simp only [hn, Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Prod.mk.eta]
      · simp only [Nat.shiftLeft_eq, pow_mul]

#print axioms bucket_eq_series
end ClaudeWCT.Numerics.SharedPathList

namespace ClaudeWCT.Numerics.CanonicalHistogram
open CanonicalCompression

theorem lower_histogram_digits : ∀ c : Fin 128,
    coefficient 132 (packHistogram 132 0 128 lowerCounts) c.val =
      histogramWeight lowerCounts c.val := by decide +kernel
end ClaudeWCT.Numerics.CanonicalHistogram


namespace ClaudeWCT.Numerics.CanonicalCounting
open Finset
open scoped BigOperators

theorem count_fibers_fin {α : Type} [Fintype α] (g : α → Nat) (P : α → Prop)
    [DecidablePred P] (n : Nat) :
    (∑ j : Fin n, (univ.filter fun a => g a = j.val ∧ P a).card) =
      (univ.filter fun a => g a < n ∧ P a).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : P a
  · simp only [hp, and_true]
    by_cases hg : g a < n
    · let j : Fin n := ⟨g a, hg⟩
      have he (k : Fin n) : g a = k.val ↔ k = j := by
        simp only [j, Fin.ext_iff]
        omega
      simp only [he, if_pos hg]
      simp
    · have he (k : Fin n) : ¬g a = k.val := by
        have := k.isLt
        omega
      simp only [he, if_neg, hg, if_false, Finset.sum_const_zero]
  · simp only [hp, and_false, if_false, Finset.sum_const_zero]

end ClaudeWCT.Numerics.CanonicalCounting


namespace ClaudeWCT.Numerics.SharedPathList
open Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def binnedPoly : List Nat → (Nat → Nat) → Nat[X]
  | [], _ => 0
  | b::bs, f => C (f 0) * X^b + binnedPoly bs (fun j => f (j+1))

theorem quotient_digit (B p j : Nat) :
    (p / B) / B^j % B = p / B^(j+1) % B := by
  rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm B]

theorem bucketSeries_poly (bs : List Nat) (c p : Nat) :
    (bucketSeries bs c p).1 =
      (binnedPoly bs (fun j => (p / (2^512)^j) % 2^512)).eval (2^1024) ∧
    (bucketSeries bs c p).2 =
      (binnedPoly bs (fun j => (c+j) * ((p / (2^512)^j) % 2^512))).eval (2^1024) := by
  induction bs generalizing c p with
  | nil => simp only [bucketSeries, binnedPoly, Polynomial.eval_zero, and_self]
  | cons b bs ih =>
    have h := ih (c+1) (p / 2^512)
    simp only [bucketSeries, binnedPoly, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, pow_zero,
      Nat.div_one, Nat.add_zero]
    constructor
    · rw [h.1]
      congr 2
      apply congrArg (binnedPoly bs)
      funext j
      exact quotient_digit (2^512) p j
    · rw [h.2]
      congr 2
      apply congrArg (binnedPoly bs)
      funext j
      rw [quotient_digit]
      congr 1
      omega


#print axioms bucketSeries_poly
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset
open scoped BigOperators
open SharedDigitBlock

theorem bits_digit_eq (bits p i : Nat) :
    (p >>> (bits*i)) % 2^bits = digit (2^bits) p i := by
  simp only [digit, Nat.shiftRight_eq_div_pow, pow_mul]

theorem shift_window_eq (bits p start len : Nat) :
    (p >>> (bits*start)) % 2^(bits*len) = p / (2^bits)^start % (2^bits)^len := by
  simp only [Nat.shiftRight_eq_div_pow, pow_mul]

end ClaudeWCT.Numerics.CanonicalHistogram


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem bucket_polynomial (bs : List Nat) (c : Nat) (P : Nat[X])
    (hP : ∀ i, P.coeff i < 2^512) :
    bucket bs c (P.eval (2^512)) =
      ((binnedPoly bs P.coeff).eval (2^1024),
       (binnedPoly bs (fun j => (c+j)*P.coeff j)).eval (2^1024)) := by
  rw [bucket_eq_series]
  have h := bucketSeries_poly bs c (P.eval (2^512))
  have hd (j : Nat) : P.eval (2^512) / (2^512)^j % 2^512 = P.coeff j :=
    ClaudeWCT.Numerics.eval_div_pow_mod (pow_pos (by decide) _) j P hP
  simp_rw [hd] at h
  exact Prod.ext h.1 h.2

#print axioms bucket_polynomial
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem binnedPoly_eq_sum (bs : List Nat) (f : Nat → Nat) :
    binnedPoly bs f = ∑ i : Fin bs.length, C (f i) * X^(bs[i]) := by
  induction bs generalizing f with
  | nil => simp [binnedPoly]
  | cons b bs ih =>
    rw [binnedPoly]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [Fin.getElem_fin, List.getElem_cons_zero, Fin.val_zero, Fin.val_succ, List.getElem_cons_succ]
    rw [ih]
    simp only [Fin.getElem_fin]

theorem binnedPoly_finite_coeff (bs : List Nat) (f : Nat → Nat) (k : Nat) :
    (binnedPoly bs f).coeff k = ∑ i : Fin bs.length, if bs[i] = k then f i else 0 := by
  rw [binnedPoly_eq_sum]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    mul_ite, Nat.mul_one, Nat.mul_zero, eq_comm]

theorem binnedPoly_mono (bs : List Nat) (f g : Nat → Nat)
    (h : ∀ i, i<bs.length → f i ≤ g i) (k : Nat) :
    (binnedPoly bs f).coeff k ≤ (binnedPoly bs g).coeff k := by
  rw [binnedPoly_finite_coeff, binnedPoly_finite_coeff]
  apply sum_le_sum
  intro i _
  split_ifs
  · exact h i i.isLt
  · rfl


#print axioms binnedPoly_eq_sum
#print axioms binnedPoly_mono
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem binnedPoly_fiber_coeff {α : Type} [Fintype α]
    (bs : List Nat) (value weight : α → Nat) (k : Nat) :
    (binnedPoly bs (fun i => ∑ a, if value a=i then weight a else 0)).coeff k =
      ∑ a, if h : value a < bs.length then
        (if bs[value a]'h = k then weight a else 0) else 0 := by
  rw [binnedPoly_finite_coeff]
  have he (i : Fin bs.length) :
      (if bs[i] = k then ∑ a, if value a=i.val then weight a else 0 else 0) =
      ∑ a, if bs[i] = k then (if value a=i.val then weight a else 0) else 0 := by
    by_cases hi : bs[i] = k
    · simp only [if_pos hi]
    · simp only [if_neg hi, Finset.sum_const_zero]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : value a < bs.length
  · rw [dif_pos ha]
    let i : Fin bs.length := ⟨value a, ha⟩
    rw [Finset.sum_eq_single i]
    · simp only [i, Fin.getElem_fin, if_true]
    · intro j _ hji
      have hn : value a ≠ j.val := by
        intro he
        apply hji
        exact Fin.ext he.symm
      simp only [if_neg hn, ite_self]
    · exact fun hi => (hi (Finset.mem_univ _)).elim
  · rw [dif_neg ha]
    apply Finset.sum_eq_zero
    intro i _
    have hn : value a ≠ i.val := by intro he; exact ha (he ▸ i.isLt)
    simp only [if_neg hn, ite_self]

theorem binnedPoly_fiber_lower {α : Type} [Fintype α]
    (bs : List Nat) (value weight : α → Nat) (f : Nat → Nat)
    (hf : ∀ i, i<bs.length → f i ≤ ∑ a, if value a=i then weight a else 0)
    (k : Nat) :
    (binnedPoly bs f).coeff k ≤
      ∑ a, if h : value a < bs.length then
        (if bs[value a]'h = k then weight a else 0) else 0 := by
  rw [← binnedPoly_fiber_coeff]
  exact binnedPoly_mono bs f _ hf k

#print axioms binnedPoly_fiber_coeff
#print axioms binnedPoly_fiber_lower
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem coordinate_coverage_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {K r : Nat} (E : Fin r → Fin K × β) :
    coordinateCoverage val E ≤ K*563 := by
  classical
  unfold coordinateCoverage
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (by simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hβ])

theorem pair_coverage_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {r : Nat} (h : PairHistory β r) :
    pairCoverage val h ≤ 2*(64*563)^2 := by
  have hb (s : Fin 2) : selectorValue (fun _ => coordinateCoverage val)
      h.1 h.2.1 h.2.2 s ≤ (64*563)^2 := by
    unfold selectorValue
    rw [pow_two]
    exact Nat.mul_le_mul (coordinate_coverage_le val hβ _) (coordinate_coverage_le val hβ _)
  unfold pairCoverage
  calc _ ≤ (64*563)^2+(64*563)^2 := Nat.add_le_add (hb 0) (hb 1)
       _ = _ := by omega

theorem forest_coverage_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {r : Nat} (h : ForestHistory β r) : forestCoverage val h ≤ alphabetSize := by
  have hp : (∏ i : Fin 4, pairCoverage val (h.1 i)) ≤ (2*(64*563)^2)^4 := by
    calc _ ≤ ∏ _i : Fin 4, (2*(64*563)^2) :=
          Finset.prod_le_prod' (fun i _ => pair_coverage_le val hβ (h.1 i))
         _ = _ := by rw [Fin.prod_const]
  exact Nat.mul_le_mul hp (coordinate_coverage_le val hβ h.2)

#print axioms forest_coverage_le
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open scoped BigOperators Polynomial
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem window_prefix_interval (P : Nat[X])
    (hb : ∀ j, (P*geomPoly 2048).coeff j < 2^1024)
    (lo hi i : Nat) (hlo : lo ≤ hi) (hi' : i<2048) :
    digit (2^1024) (window (prefixes (P.eval (2^1024))) lo hi) i =
      if lo ≤ i then ∑ j ∈ Ico (i-hi) (i-lo+1), P.coeff j else 0 := by
  rw [window_digits _ _ _ _ hlo hi' (prefixes_digits_monotone P hb)]
  by_cases hl : lo ≤ i
  · simp only [if_pos hl]
    rw [prefixes_coefficient _ _ (by omega) hb,
      prefix_poly_coefficient _ _ _ (by omega)]
    by_cases hh : hi+1 ≤ i
    · rw [if_pos hh, prefixes_coefficient _ _ (by omega) hb,
        prefix_poly_coefficient _ _ _ (by omega)]
      have he : i-(hi+1)+1 = i-hi := by omega
      rw [he]
      have hs := Finset.sum_range_add_sum_Ico P.coeff (show i-hi ≤ i-lo+1 by omega)
      omega
    · rw [if_neg hh, Nat.sub_zero]
      have he : i-hi = 0 := by omega
      rw [he, Nat.Ico_zero_eq_range]
  · have hh : ¬hi+1 ≤ i := by omega
    simp only [if_neg hl, if_neg hh, Nat.sub_self]

#print axioms window_prefix_interval
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedMoments
open ENNReal
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.PoissonReflect
open SphincsSecurity.Concrete
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000


theorem near_bound_of_rows (T : Nat) (hT : 2^32 ≤ T)
    (κ : ENNReal) (hκ : 1 ≤ κ)
    (hlam : (T : ENNReal)*(2^31:ENNReal)⁻¹*κ ≤ (2013623:ENNReal)/1000000)
    (g : Nat → ENNReal)
    (hpay : ∀ r ≤ 80, g r ≤ κ^r *
      ((16^r*forestNearMoment r : Nat) : ENNReal) /
        ((54*alphabetSize*fieldSize^(9*r) : Nat) : ENNReal))
    (htail : ∀ r, 80<r → g r ≤ 1) :
    ((54*priceScaleTotal : Nat) : ENNReal)*binomialAverage (2^31:ENNReal)⁻¹ T g ≤ 385 := by
  have h := poissonCheckQ_sound_tilt (Qv := fieldSize)
    (f := fun r => 16^r*forestNearMoment r) (dbase := 54*alphabetSize)
    (sn := 54*priceScaleTotal) (sd := 1) (Mn := 385) (Md := 1) (R := 80)
    near_moment_checked (by norm_num [fieldSize]) (by norm_num) (by norm_num)
    (by norm_num [alphabetSize]) (by norm_num) (by norm_num)
    rate_le_one κ hκ hlam (rejection_window_sharp T hT) g
    (fun r hr => by simpa only [mul_div_assoc] using hpay r hr) htail
  simpa only [Nat.cast_one, Nat.cast_ofNat, div_one] using h

#print axioms near_bound_of_rows
end ClaudeWCT.Numerics.SharedMoments


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weighted_fiber_count {α : Type} [Fintype α] (value : α → Nat) (c j : Nat) :
    (∑ a, if value a=j then c+value a else 0) =
      (c+j) * (Finset.univ.filter fun a => value a=j).card := by
  classical
  rw [Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : value a=j
  · simp only [ha, if_true, Nat.mul_one]
  · simp only [if_neg ha, Nat.mul_zero]


end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def weightedHistogram {α : Type} [Fintype α]
    (good : α → Prop) (bin weight : α → Nat) : Nat[X] := by
  classical
  exact ∑ a, if good a then C (weight a)*X^(bin a) else 0

theorem weightedHistogram_coeff {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat) (k : Nat) :
    (weightedHistogram good bin weight).coeff k =
      ∑ a, if good a ∧ bin a=k then weight a else 0 := by
  classical
  unfold weightedHistogram
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hg : good a
  · simp only [if_pos hg, Polynomial.coeff_C_mul_X_pow, hg, if_true, true_and, eq_comm]
  · simp only [if_neg hg, Polynomial.coeff_zero, hg, false_and, if_false]

theorem weightedHistogram_mul {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) (gb : β → Prop) (ba wa : α → Nat) (bb wb : β → Nat) :
    weightedHistogram ga ba wa * weightedHistogram gb bb wb =
      weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
        (fun p => ba p.1+bb p.2) (fun p => wa p.1*wb p.2) := by
  classical
  unfold weightedHistogram
  rw [Finset.sum_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : ga a <;> by_cases hb : gb b
  · simp only [if_pos ha, if_pos hb, if_pos (And.intro ha hb), Polynomial.C_mul, pow_add]
    ring
  · simp only [if_pos ha, if_neg hb, Nat.cast_id, mul_zero, ha, hb, true_and, if_false]
  · simp only [if_neg ha, zero_mul, ha, false_and, if_false]
  · simp only [if_neg ha, zero_mul, ha, false_and, if_false]

theorem weightedHistogram_product_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) (gb : β → Prop) (ba wa : α → Nat) (bb wb : β → Nat)
    (P Q : Nat[X]) (hP : CoeffLE P (weightedHistogram ga ba wa))
    (hQ : CoeffLE Q (weightedHistogram gb bb wb)) :
    CoeffLE (P*Q) (weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
      (fun p => ba p.1+bb p.2) (fun p => wa p.1*wb p.2)) := by
  rw [← weightedHistogram_mul]
  exact CoeffLE.mul _ _ _ _ hP hQ

#print axioms weightedHistogram_product_lower
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem sum_finite_fibers {α β : Type} [Fintype α] [DecidableEq β]
    (s : Finset β) (good : α → Prop) [DecidablePred good]
    (label : α → β) (weight : α → Nat) :
    (∑ b ∈ s, ∑ a, if good a ∧ label a=b then weight a else 0) =
      ∑ a, if good a ∧ label a∈s then weight a else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hg : good a
  · simp only [hg, true_and]
    by_cases hs : label a∈s
    · rw [if_pos hs, Finset.sum_eq_single (label a)]
      · simp only [if_true]
      · intro b _ hb
        exact if_neg (Ne.symm hb)
      · exact fun hn => (hn hs).elim
    · rw [if_neg hs]
      apply Finset.sum_eq_zero
      intro b hb
      exact if_neg (by intro he; exact hs (he ▸ hb))
  · simp only [hg, false_and, if_false, Finset.sum_const_zero]

theorem product_fiber_sum {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat) (i j : Nat) :
    (∑ p : α×β, if (ga p.1 ∧ ba p.1=i) ∧ (gb p.2 ∧ bb p.2=j)
      then wa p.1*wb p.2 else 0) =
      (∑ a, if ga a ∧ ba a=i then wa a else 0) *
      (∑ b, if gb b ∧ bb b=j then wb b else 0) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : ga a ∧ ba a=i <;> by_cases hb : gb b ∧ bb b=j <;>
    simp only [ha, hb, true_and, false_and, and_true, and_false, if_true, if_false,
      Nat.zero_mul, Nat.mul_zero]

#print axioms sum_finite_fibers
#print axioms product_fiber_sum
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem directedFirst_digit (a pref : Cell) (lo hi shift : Nat)
    (haP : a.1 < (2^1024)^2048) (haF : a.2 < (2^1024)^2048)
    (hsmall : ∀ j, j<2048 →
      digit (2^1024) a.2 j * digit (2^1024) (window pref.1 lo hi) j +
      digit (2^1024) a.1 j * digit (2^1024) (window pref.2 lo hi) j < 2^1024)
    (i : Nat) (hi' : i<2048) :
    digit (2^1024) (directedFirst a pref lo hi shift) i =
      if shift ≤ i then
        digit (2^1024) a.2 (i-shift) * digit (2^1024) (window pref.1 lo hi) (i-shift) +
        digit (2^1024) a.1 (i-shift) * digit (2^1024) (window pref.2 lo hi) (i-shift)
      else 0 := by
  rw [directedFirst_model _ _ _ _ _ haP haF, digit_low _ _ _ _ hi',
    digit_shift _ _ _ _ (pow_pos (by decide) _)]
  by_cases hs : shift ≤ i
  · rw [if_pos hs, if_pos hs]
    exact digit_packFun _ _ _ (pow_pos (by decide) _) hsmall _ (by omega)
  · rw [if_neg hs, if_neg hs]

#print axioms directedFirst_digit
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem product_filtered_sum {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (wa : α → Nat) (wb : β → Nat) :
    (∑ p : α×β, if ga p.1 ∧ gb p.2 then wa p.1*wb p.2 else 0) =
      (∑ a, if ga a then wa a else 0)*(∑ b, if gb b then wb b else 0) := by
  simpa only [and_true] using product_fiber_sum ga gb (fun _ => 0) wa (fun _ => 0) wb 0 0

theorem cross_filtered_sum {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (wa : α → Nat) (wb : β → Nat) :
    (∑ p : α×β, if ga p.1 ∧ gb p.2 then wa p.1+wb p.2 else 0) =
      (∑ a, if ga a then wa a else 0)*(∑ b, if gb b then 1 else 0) +
      (∑ a, if ga a then 1 else 0)*(∑ b, if gb b then wb b else 0) := by
  have he (p : α×β) :
      (if ga p.1 ∧ gb p.2 then wa p.1+wb p.2 else 0) =
      (if ga p.1 ∧ gb p.2 then wa p.1*1 else 0) +
      (if ga p.1 ∧ gb p.2 then 1*wb p.2 else 0) := by
    by_cases hp : ga p.1 ∧ gb p.2 <;> simp only [hp, true_and, if_true, if_false, mul_one, one_mul, Nat.zero_add]
  simp_rw [he]
  rw [Finset.sum_add_distrib, product_filtered_sum ga gb wa (fun _ => 1),
    product_filtered_sum ga gb (fun _ => 1) wb]

theorem directed_fiber_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat)
    (ap af bp bf : Nat → Nat)
    (haP : ∀ i, ap i ≤ ∑ a, if ga a ∧ ba a=i then 1 else 0)
    (haF : ∀ i, af i ≤ ∑ a, if ga a ∧ ba a=i then wa a else 0)
    (hbP : ∀ j, bp j ≤ ∑ b, if gb b ∧ bb b=j then 1 else 0)
    (hbF : ∀ j, bf j ≤ ∑ b, if gb b ∧ bb b=j then wb b else 0)
    (i : Nat) (s : Finset Nat) :
    af i*(∑ j ∈ s, bp j) + ap i*(∑ j ∈ s, bf j) ≤
      ∑ p : α×β, if (ga p.1 ∧ ba p.1=i) ∧ (gb p.2 ∧ bb p.2∈s)
        then wa p.1+wb p.2 else 0 := by
  rw [cross_filtered_sum (fun a => ga a ∧ ba a=i) (fun b => gb b ∧ bb b∈s) wa wb]
  apply Nat.add_le_add
  · apply Nat.mul_le_mul (haF i)
    rw [← sum_finite_fibers s gb bb (fun _ => 1)]
    exact Finset.sum_le_sum (fun j _ => hbP j)
  · apply Nat.mul_le_mul (haP i)
    rw [← sum_finite_fibers s gb bb wb]
    exact Finset.sum_le_sum (fun j _ => hbF j)

#print axioms directed_fiber_lower
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open scoped BigOperators Polynomial
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem directed_histogram_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat) (a pref : Cell)
    (bp bf : Nat → Nat) (lo hi shift : Nat)
    (haP : a.1 < (2^1024)^2048) (haF : a.2 < (2^1024)^2048)
    (hsmall : ∀ j, j<2048 →
      digit (2^1024) a.2 j * digit (2^1024) (window pref.1 lo hi) j +
      digit (2^1024) a.1 j * digit (2^1024) (window pref.2 lo hi) j < 2^1024)
    (hwinP : ∀ j, j<2048 → digit (2^1024) (window pref.1 lo hi) j =
      if lo≤j then ∑ t ∈ Ico (j-hi) (j-lo+1), bp t else 0)
    (hwinF : ∀ j, j<2048 → digit (2^1024) (window pref.2 lo hi) j =
      if lo≤j then ∑ t ∈ Ico (j-hi) (j-lo+1), bf t else 0)
    (hap : ∀ i, digit (2^1024) a.1 i ≤ ∑ x, if ga x ∧ ba x=i then 1 else 0)
    (haf : ∀ i, digit (2^1024) a.2 i ≤ ∑ x, if ga x ∧ ba x=i then wa x else 0)
    (hbp : ∀ i, bp i ≤ ∑ y, if gb y ∧ bb y=i then 1 else 0)
    (hbf : ∀ i, bf i ≤ ∑ y, if gb y ∧ bb y=i then wb y else 0)
    (k : Nat) (hk : k<2048) :
    digit (2^1024) (directedFirst a pref lo hi shift) k ≤
      (weightedHistogram
        (fun p : α×β => ga p.1 ∧ gb p.2 ∧ bb p.2≤ba p.1 ∧
          lo≤ba p.1-bb p.2 ∧ ba p.1-bb p.2≤hi)
        (fun p => ba p.1+shift) (fun p => wa p.1+wb p.2)).coeff k := by
  rw [directedFirst_digit _ _ _ _ _ haP haF hsmall _ hk, weightedHistogram_coeff]
  by_cases hs : shift≤k
  · rw [if_pos hs, hwinP _ (by omega), hwinF _ (by omega)]
    by_cases hl : lo≤k-shift
    · simp only [if_pos hl]
      apply (directed_fiber_lower ga gb ba wa bb wb _ _ bp bf hap haf hbp hbf
        (k-shift) (Ico (k-shift-hi) (k-shift-lo+1))).trans
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      simp only [Finset.mem_Ico]
      apply propext
      constructor
      · rintro ⟨⟨hga, hba⟩, hgb, hlo, hhi⟩
        refine ⟨⟨hga,hgb,?_,?_,?_⟩,?_⟩ <;> omega
      · rintro ⟨⟨hga,hgb,hj,hlo,hhi⟩,hba⟩
        exact ⟨⟨hga,by omega⟩,hgb,by omega,by omega⟩
    · simp only [if_neg hl, Nat.mul_zero, Nat.zero_add]
      exact Nat.zero_le _
  · rw [if_neg hs]
    exact Nat.zero_le _

#print axioms directed_histogram_lower
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weightedHistogram_eval_one {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat) :
    (weightedHistogram good bin weight).eval 1 = ∑ a, if good a then weight a else 0 := by
  classical
  unfold weightedHistogram
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : good a
  · simp only [if_pos ha, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, one_pow, Nat.mul_one]
  · simp only [if_neg ha, Polynomial.eval_zero]

theorem weightedHistogram_mass_le {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (M : Nat) (hM : ∀ a, good a → weight a≤M) :
    (weightedHistogram good bin weight).eval 1 ≤ Fintype.card α*M := by
  rw [weightedHistogram_eval_one]
  calc (∑ a, if good a then weight a else 0) ≤ ∑ _a : α, M := by
         apply Finset.sum_le_sum
         intro a _
         split_ifs with ha
         · exact hM a ha
         · exact Nat.zero_le _
       _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem polynomial_coeff_le_mass (P : Nat[X]) (i : Nat) : P.coeff i ≤ P.eval 1 := by
  have h := ClaudeWCT.Numerics.N600.sum_coeff_le_eval_one P {i}
  simpa only [Finset.sum_singleton] using h

theorem polynomial_mass_mono {P Q : Nat[X]} (h : CoeffLE P Q) :
    P.eval 1≤Q.eval 1 := by
  calc P.eval 1 = ∑ i ∈ P.support, P.coeff i := by
         simp [Polynomial.eval_eq_sum, Polynomial.sum_def]
       _ ≤ ∑ i ∈ P.support, Q.coeff i := Finset.sum_le_sum (fun i _ => h i)
       _ ≤ Q.eval 1 := sum_coeff_le_eval_one Q P.support

theorem histogram_lower_mass_le {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (P : Nat[X]) (hP : CoeffLE P (weightedHistogram good bin weight))
    (M : Nat) (hM : ∀ a, good a → weight a≤M) :
    P.eval 1 ≤ Fintype.card α*M :=
  (polynomial_mass_mono hP).trans
    (weightedHistogram_mass_le good bin weight M hM)

theorem histogram_lower_coeff_lt {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (P : Nat[X]) (hP : CoeffLE P (weightedHistogram good bin weight))
    (M B : Nat) (hM : ∀ a, good a → weight a≤M) (hB : Fintype.card α*M<B)
    (i : Nat) : P.coeff i<B :=
  (polynomial_coeff_le_mass P i).trans_lt
    ((histogram_lower_mass_le good bin weight P hP M hM).trans_lt hB)

#print axioms histogram_lower_coeff_lt
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedMoments
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem coordinate_history_card {β : Type} [Fintype β]
    (hβ : Fintype.card β=563) (K r : Nat) :
    Fintype.card (Fin r → Fin K×β) = (K*563)^r := by
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, hβ]

theorem pair_history_card {β : Type} [Fintype β]
    (hβ : Fintype.card β=563) (r : Nat) :
    Fintype.card (PairHistory β r) = (2*(64*563)^2)^r := by
  simp only [PairHistory, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, hβ,
    mul_pow, pow_two, Nat.mul_assoc]

theorem forest_history_card {β : Type} [Fintype β]
    (hβ : Fintype.card β=563) (r : Nat) :
    Fintype.card (ForestHistory β r) = alphabetSize^r := by
  simp only [ForestHistory, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    pair_history_card hβ r, hβ]
  rw [← pow_mul, Nat.mul_comm r 4, pow_mul]
  rw [← mul_pow]
  rfl

theorem coordinate_mass_small (K r : Nat) (hK : K≤128) (hr : r≤20) :
    (K*563)^r*(K*563) < 2^384 := by
  have hbase : K*563≤128*563 := Nat.mul_le_mul_right _ hK
  have hp : (K*563)^r≤(128*563)^20 :=
    (Nat.pow_le_pow_left hbase r).trans (Nat.pow_le_pow_right (by decide) hr)
  exact (Nat.mul_le_mul hp hbase).trans_lt (by decide +kernel)

theorem pair_mass_small (r : Nat) (hr : r≤20) :
    (2*(64*563)^2)^r*(2*(64*563)^2) < 2^1024 := by
  have hp := Nat.pow_le_pow_right (n:=2*(64*563)^2) (by decide : 0<2*(64*563)^2) hr
  exact (Nat.mul_le_mul_right _ hp).trans_lt (by decide +kernel)


#print axioms forest_history_card
#print axioms coordinate_mass_small
#print axioms pair_mass_small
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset ClaudeWCT.Numerics.N600
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem sum_pair_split {α M : Type*} [Fintype α] [AddCommMonoid M]
    (r : Nat) (F : (t u : Nat) → (Fin t → α) → (Fin t → α) →
      (Fin u → α) → (Fin u → α) → M) :
    (∑ o : Fin r → Fin 2, ∑ A : Fin r → α, ∑ B : Fin r → α,
      F (occ o 0) (occ o 1) (splitRanks o A 0) (splitRanks o B 0)
        (splitRanks o A 1) (splitRanks o B 1)) =
      ∑ t ∈ range (r+1), r.choose t •
        (∑ A₀ : Fin t → α, ∑ B₀ : Fin t → α,
          ∑ A₁ : Fin (r-t) → α, ∑ B₁ : Fin (r-t) → α,
            F t (r-t) A₀ B₀ A₁ B₁) := by
  have hs (o : Fin r → Fin 2) :
      (∑ A : Fin r → α, ∑ B : Fin r → α,
        F (occ o 0) (occ o 1) (splitRanks o A 0) (splitRanks o B 0)
          (splitRanks o A 1) (splitRanks o B 1)) =
        ∑ A₀ : Fin (occ o 0) → α, ∑ B₀ : Fin (occ o 0) → α,
          ∑ A₁ : Fin (occ o 1) → α, ∑ B₁ : Fin (occ o 1) → α,
            F (occ o 0) (occ o 1) A₀ B₀ A₁ B₁ := by
    trans ∑ A : Fin r → α, ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
      F (occ o 0) (occ o 1) (splitRanks o A 0) B₀ (splitRanks o A 1) B₁
    · apply Finset.sum_congr rfl
      intro A _
      exact sum_split_selector o (fun B₀ B₁ =>
        F (occ o 0) (occ o 1) (splitRanks o A 0) B₀ (splitRanks o A 1) B₁)
    · rw [sum_split_selector o (fun A₀ A₁ =>
        ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
          F (occ o 0) (occ o 1) A₀ B₀ A₁ B₁)]
      apply Finset.sum_congr rfl
      intro A₀ _
      rw [Finset.sum_comm]
  simp_rw [hs]
  exact sum_selector_occupancy r (fun t u =>
    ∑ A₀ : Fin t → α, ∑ B₀ : Fin t → α, ∑ A₁ : Fin u → α, ∑ B₁ : Fin u → α,
      F t u A₀ B₀ A₁ B₁)

#print axioms sum_pair_split
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem binnedPoly_histogram_lower {α : Type} [Fintype α]
    (bs : List Nat) (value weight : α → Nat) (f : Nat → Nat)
    (hf : ∀ i, i<bs.length → f i≤∑ a, if value a=i then weight a else 0) :
    CoeffLE (binnedPoly bs f)
      (weightedHistogram (fun a => value a<bs.length)
        (fun a => bs[value a]?.getD 0) weight) := by
  intro k
  have h := binnedPoly_fiber_lower bs value weight f hf k
  rw [weightedHistogram_coeff]
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : value a<bs.length
  · rw [dif_pos ha]
    simp only [ha, true_and, List.getElem?_eq_getElem ha, Option.getD_some]
  · rw [dif_neg ha]
    simp only [ha, false_and, if_false]

#print axioms binnedPoly_histogram_lower
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem packFun_lt (B n : Nat) (f : Nat → Nat) (hB : 0<B)
    (hf : ∀ i, i<n → f i<B) : packFun B n f<B^n := by
  induction n with
  | zero => simp only [packFun, Finset.range_zero, Finset.sum_empty, pow_zero]; exact Nat.zero_lt_one
  | succ n ih =>
    have hp := ih (fun i hi => hf i (by omega))
    have hn : f n+1≤B := hf n (by omega)
    have hm := Nat.mul_le_mul_right (B^n) hn
    simp only [packFun, Finset.sum_range_succ] at hp ⊢
    rw [pow_succ]
    nlinarith

theorem polynomial_eval_packFun (P : Nat[X]) (B n : Nat)
    (hz : ∀ i, n ≤ i → P.coeff i=0) : P.eval B=packFun B n P.coeff := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  unfold packFun
  apply Finset.sum_subset
  · intro i hi
    apply Finset.mem_range.mpr
    have hc := Polynomial.mem_support_iff.mp hi
    by_contra hn
    exact hc (hz i (by omega))
  · intro i _ hi
    have hz : P.coeff i=0 := by
      by_contra hn
      exact hi (Polynomial.mem_support_iff.mpr hn)
    rw [hz, Nat.zero_mul]

theorem polynomial_eval_lt (P : Nat[X]) (B n : Nat) (hB : 0<B)
    (hc : ∀ i, i<n → P.coeff i<B) (hz : ∀ i, n ≤ i → P.coeff i=0) :
    P.eval B<B^n := by
  rw [polynomial_eval_packFun P B n hz]
  exact packFun_lt B n P.coeff hB hc

#print axioms polynomial_eval_lt
end ClaudeWCT.Numerics.SharedDigitBlock

namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem binnedPoly_coeff_zero (bs : List Nat) (f : Nat → Nat) (n : Nat)
    (hb : ∀ i : Fin bs.length, bs[i]<n) (j : Nat) (hj : n≤j) :
    (binnedPoly bs f).coeff j=0 := by
  rw [binnedPoly_finite_coeff]
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (by have h := hb i; omega)

theorem binnedPoly_eval_lt (bs : List Nat) (f : Nat → Nat) (B n : Nat)
    (hB : 0<B) (hb : ∀ i : Fin bs.length, bs[i]<n)
    (hc : ∀ j, (binnedPoly bs f).coeff j<B) : (binnedPoly bs f).eval B<B^n := by
  exact polynomial_eval_lt _ B n hB (fun j _ => hc j) (binnedPoly_coeff_zero bs f n hb)

#print axioms binnedPoly_eval_lt
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem coordinate_histograms_lower {α : Type} [Fintype α]
    (bs : List Nat) (value : α → Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j≤(Finset.univ.filter fun a => value a=j).card) :
    CoeffLE (binnedPoly bs P.coeff)
      (weightedHistogram (fun a => value a<bs.length) (fun a => bs[value a]?.getD 0) (fun _ => 1)) ∧
    CoeffLE (binnedPoly bs (fun j => j*P.coeff j))
      (weightedHistogram (fun a => value a<bs.length) (fun a => bs[value a]?.getD 0) value) := by
  classical
  constructor
  · apply binnedPoly_histogram_lower
    intro j _
    simpa only [Finset.card_filter] using hP j
  · apply binnedPoly_histogram_lower
    intro j _
    have he := weighted_fiber_count value 0 j
    simp only [Nat.zero_add] at he
    rw [he]
    exact Nat.mul_le_mul_left j (hP j)

theorem coordinate_histograms_mass {α : Type} [Fintype α]
    (bs : List Nat) (value : α → Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j≤(Finset.univ.filter fun a => value a=j).card)
    (M : Nat) (hM : ∀ a, value a≤M) :
    (binnedPoly bs P.coeff).eval 1≤Fintype.card α ∧
    (binnedPoly bs (fun j => j*P.coeff j)).eval 1≤Fintype.card α*M := by
  have hp := coordinate_histograms_lower bs value P hP
  constructor
  · have h := histogram_lower_mass_le _ _ _ _ hp.1 1 (fun _ _ => le_rfl)
    simpa only [Nat.mul_one] using h
  · exact histogram_lower_mass_le _ _ _ _ hp.2 M (fun a _ => hM a)

#print axioms coordinate_histograms_lower
#print axioms coordinate_histograms_mass
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weightedHistogram_pi {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ i, Fintype (α i)] (good : (i : ι) → α i → Prop)
    (bin weight : (i : ι) → α i → Nat) :
    (∏ i, weightedHistogram (good i) (bin i) (weight i)) =
      weightedHistogram (fun a : (i : ι) → α i => ∀ i, good i (a i))
        (fun a => ∑ i, bin i (a i)) (fun a => ∏ i, weight i (a i)) := by
  classical
  unfold weightedHistogram
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : ∀ i, good i (a i)
  · rw [if_pos ha]
    simp only [ha, if_true]
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  · rw [if_neg ha]
    obtain ⟨i, hi⟩ := not_forall.mp ha
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

#print axioms weightedHistogram_pi
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem polynomial_prod_mono {ι : Type} [DecidableEq ι] (P Q : ι → Nat[X])
    (h : ∀ i, CoeffLE (P i) (Q i)) (s : Finset ι) :
    CoeffLE (∏ i ∈ s, P i) (∏ i ∈ s, Q i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; intro k; exact le_rfl
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact CoeffLE.mul _ _ _ _ (h i) ih

theorem weightedHistogram_pi_lower {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ i, Fintype (α i)] (good : (i : ι) → α i → Prop)
    (bin weight : (i : ι) → α i → Nat) (P : ι → Nat[X])
    (hP : ∀ i, CoeffLE (P i) (weightedHistogram (good i) (bin i) (weight i))) :
    CoeffLE (∏ i, P i)
      (weightedHistogram (fun a : (i : ι) → α i => ∀ i, good i (a i))
        (fun a => ∑ i, bin i (a i)) (fun a => ∏ i, weight i (a i))) := by
  classical
  rw [← weightedHistogram_pi]
  exact polynomial_prod_mono P _ hP Finset.univ

#print axioms weightedHistogram_pi_lower
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem bucket_no_carry {α : Type} [Fintype α]
    (bs : List Nat) (value : α → Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j≤(Finset.univ.filter fun a => value a=j).card)
    (M : Nat) (hM : ∀ a, value a≤M)
    (hcard : Fintype.card α<2^512) (hmass : Fintype.card α*M<2^1024) :
    bucket bs 0 (P.eval (2^512)) =
      ((binnedPoly bs P.coeff).eval (2^1024),
        (binnedPoly bs (fun j => j*P.coeff j)).eval (2^1024)) ∧
    (∀ j, (binnedPoly bs P.coeff).coeff j<2^1024) ∧
    (∀ j, (binnedPoly bs (fun j => j*P.coeff j)).coeff j<2^1024) := by
  classical
  have hc (j : Nat) : P.coeff j<2^512 := by
    have h := (Finset.card_le_card (Finset.filter_subset (fun a => value a=j) Finset.univ))
    rw [Finset.card_univ] at h
    exact (hP j).trans_lt (h.trans_lt hcard)
  have mass := coordinate_histograms_mass bs value P hP M hM
  refine ⟨?_,?_,?_⟩
  · simpa only [Nat.zero_add] using bucket_polynomial bs 0 P hc
  · intro j
    exact (polynomial_coeff_le_mass _ j).trans_lt
      (mass.1.trans_lt (hcard.trans_le (by decide +kernel)))
  · intro j
    exact (polynomial_coeff_le_mass _ j).trans_lt (mass.2.trans_lt hmass)

theorem bucket_histogram_bounds {α : Type} [Fintype α]
    (bs : List Nat) (value : α → Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j≤(Finset.univ.filter fun a => value a=j).card)
    (M n : Nat) (hM : ∀ a, value a≤M)
    (hcard : Fintype.card α<2^512) (hmass : Fintype.card α*M<2^1024)
    (hbin : ∀ i : Fin bs.length, bs[i]<n) :
    (bucket bs 0 (P.eval (2^512))).1<(2^1024)^n ∧
    (bucket bs 0 (P.eval (2^512))).2<(2^1024)^n := by
  have h := bucket_no_carry bs value P hP M hM hcard hmass
  rw [h.1]
  exact ⟨binnedPoly_eval_lt _ _ _ n (pow_pos (by decide) _) hbin h.2.1,
    binnedPoly_eval_lt _ _ _ n (pow_pos (by decide) _) hbin h.2.2⟩

#print axioms bucket_no_carry
#print axioms bucket_histogram_bounds
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem forest_histogram_lower {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (r : Nat)
    (gp : PairHistory β r → Prop) (bp : PairHistory β r → Nat)
    (gq : (Fin r → Fin 128×β) → Prop) (bq : (Fin r → Fin 128×β) → Nat)
    (P Q : Nat[X])
    (hP : CoeffLE P (weightedHistogram gp bp (pairCoverage val)))
    (hQ : CoeffLE Q (weightedHistogram gq bq (coordinateCoverage val))) :
    CoeffLE (P^4*Q)
      (weightedHistogram (fun h : ForestHistory β r => (∀ i, gp (h.1 i)) ∧ gq h.2)
        (fun h => (∑ i, bp (h.1 i))+bq h.2) (forestCoverage val)) := by
  classical
  have hpi : CoeffLE (P^4)
      (weightedHistogram (fun h : Fin 4 → PairHistory β r => ∀ i, gp (h i))
        (fun h => ∑ i, bp (h i)) (fun h => ∏ i, pairCoverage val (h i))) := by
    simpa only [Fin.prod_const] using
      weightedHistogram_pi_lower (fun _i : Fin 4 => gp) (fun _ => bp)
        (fun _ => pairCoverage val) (fun _ => P) (fun _ => hP)
  exact weightedHistogram_product_lower _ _ _ _ _ _ _ _ hpi hQ

#print axioms forest_histogram_lower
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weightedHistogram_equiv {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (good : β → Prop) (bin weight : β → Nat) :
    weightedHistogram (fun a => good (e a)) (fun a => bin (e a)) (fun a => weight (e a)) =
      weightedHistogram good bin weight := by
  classical
  unfold weightedHistogram
  exact e.sum_comp (fun b => if good b then C (weight b)*X^(bin b) else 0)

theorem weightedHistogram_partition {ι α : Type} [Fintype ι] [Fintype α]
    (piece : ι → α → Prop) (good : α → Prop) (label : ι → α → Nat)
    (bin weight : α → Nat)
    (hgood : ∀ i a, piece i a → good a)
    (hbin : ∀ i a, piece i a → label i a=bin a)
    (huniq : ∀ i j a, piece i a → piece j a → i=j) :
    CoeffLE (∑ i, weightedHistogram (piece i) (label i) weight)
      (weightedHistogram good bin weight) := by
  classical
  intro k
  rw [Polynomial.finsetSum_coeff, weightedHistogram_coeff]
  simp_rw [weightedHistogram_coeff]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases hex : ∃ i, piece i a
  · obtain ⟨i,hi⟩ := hex
    rw [Finset.sum_eq_single i]
    · rw [hbin i a hi]
      simp only [hi, hgood i a hi, true_and]
      exact le_rfl
    · intro j _ hji
      have hj : ¬piece j a := fun h => hji (huniq j i a h hi)
      simp only [hj, false_and, if_false]
    · exact fun hn => (hn (Finset.mem_univ i)).elim
  · have hz : (∑ i, if piece i a ∧ label i a=k then weight a else 0)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : ¬piece i a := fun h => hex ⟨i,h⟩
      simp only [hi, false_and, if_false]
    rw [hz]
    exact Nat.zero_le _

#print axioms weightedHistogram_partition
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathList
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem add_run_bounds (i : Fin addRuns.length) :
    addRuns[i].1 ≤ addRuns[i].2.1 ∧ addRuns[i].2.1<2047 ∧ addRuns[i].2.2 ≤ 70 ∧
    addEndpoint addRuns[i].1 addRuns[i].2.2 ∧ addEndpoint addRuns[i].2.1 addRuns[i].2.2 := by
  have h := List.all_eq_true.mp addRuns_valid addRuns[i] (List.getElem_mem _)
  exact of_decide_eq_true h

theorem add_run_unique (i j : Fin addRuns.length) (d : Nat)
    (hi : addRuns[i].1 ≤ d ∧ d ≤ addRuns[i].2.1)
    (hj : addRuns[j].1 ≤ d ∧ d ≤ addRuns[j].2.1) : i=j := by
  rcases lt_trichotomy i.val j.val with hlt|he|hgt
  · have h := List.pairwise_iff_getElem.mp addRuns_ordered i.val j.val i.isLt j.isLt hlt
    simp only [Fin.getElem_fin] at hi hj
    omega
  · exact Fin.ext he
  · have h := List.pairwise_iff_getElem.mp addRuns_ordered j.val i.val j.isLt i.isLt hgt
    simp only [Fin.getElem_fin] at hi hj
    omega

noncomputable def shiftFor (d : Nat) : Nat :=
  if h : ∃ i : Fin addRuns.length, addRuns[i].1 ≤ d ∧ d ≤ addRuns[i].2.1 then
    addRuns[Classical.choose h].2.2 else 0

theorem shiftFor_eq (i : Fin addRuns.length) (d : Nat)
    (hi : addRuns[i].1 ≤ d ∧ d ≤ addRuns[i].2.1) : shiftFor d=addRuns[i].2.2 := by
  have hex : ∃ i : Fin addRuns.length, addRuns[i].1 ≤ d ∧ d ≤ addRuns[i].2.1 := ⟨i,hi⟩
  rw [shiftFor, dif_pos hex]
  exact congrArg (fun e : Fin addRuns.length => addRuns[e].2.2)
    (add_run_unique (Classical.choose hex) i d (Classical.choose_spec hex) hi)

noncomputable def mergeBin (i j : Nat) : Nat := max i j+shiftFor (i-j+(j-i))

theorem mergeBin_comm (i j : Nat) : mergeBin i j=mergeBin j i := by
  unfold mergeBin
  rw [Nat.max_comm, Nat.add_comm (i-j) (j-i)]

theorem mergeBin_forward (e : Fin addRuns.length) (i j : Nat) (hj : j ≤ i)
    (hlo : addRuns[e].1 ≤ i-j) (hhi : i-j ≤ addRuns[e].2.1) :
    mergeBin i j=i+addRuns[e].2.2 := by
  unfold mergeBin
  rw [Nat.max_eq_left hj, Nat.sub_eq_zero_of_le hj, Nat.add_zero, shiftFor_eq e _ ⟨hlo,hhi⟩]

#print axioms add_run_unique
#print axioms mergeBin_forward
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathReflection
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem addEndpoint_ratio (d b : Nat) (h : addEndpoint d b) :
    (101/100 : ℝ)^b*(100/101) ≤ 1+(100/101 : ℝ)^d ∧
      1+(100/101 : ℝ)^d ≤ (101/100 : ℝ)^b := by
  have hh := geometric_add_interval d b h.1 h.2
  have hn : 0 ≤ (100/101 : ℝ)^d := by positivity
  have he : (101/100 : ℝ)^d*(100/101 : ℝ)^d=1 := by
    rw [← mul_pow]
    norm_num
  have h0 := mul_le_mul_of_nonneg_right hh.1 hn
  have h1 := mul_le_mul_of_nonneg_right hh.2 hn
  have hl : ((101/100 : ℝ)^(b+d)*(100/101))*(100/101 : ℝ)^d =
      (101/100 : ℝ)^b*(100/101) := by
    rw [pow_add]
    calc _ = ((101/100 : ℝ)^b*(100/101))*
        ((101/100 : ℝ)^d*(100/101 : ℝ)^d) := by ring
         _ = _ := by rw [he, mul_one]
  have hu : (101/100 : ℝ)^(b+d)*(100/101 : ℝ)^d=(101/100 : ℝ)^b := by
    rw [pow_add, mul_assoc, he, mul_one]
  rw [hl, add_mul, he, one_mul] at h0
  rw [hu, add_mul, he, one_mul] at h1
  exact ⟨h0,h1⟩

theorem pow_ratio_antitone (a b : Nat) (hab : a ≤ b) :
    (100/101 : ℝ)^b ≤ (100/101 : ℝ)^a := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  have hn : (100/101 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (mul_one _)

theorem add_run_ratio (e : Fin addRuns.length) (d : Nat)
    (hlo : addRuns[e].1 ≤ d) (hhi : d ≤ addRuns[e].2.1) :
    (101/100 : ℝ)^addRuns[e].2.2*(100/101) ≤ 1+(100/101 : ℝ)^d ∧
      1+(100/101 : ℝ)^d ≤ (101/100 : ℝ)^addRuns[e].2.2 := by
  have he := add_run_bounds e
  have hl := (addEndpoint_ratio _ _ he.2.2.2.1).2
  have hh := (addEndpoint_ratio _ _ he.2.2.2.2).1
  exact ⟨hh.trans (add_le_add le_rfl (pow_ratio_antitone _ _ hhi)),
    (add_le_add le_rfl (pow_ratio_antitone _ _ hlo)).trans hl⟩

#print axioms add_run_ratio
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathReflection
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem add_ratio_shift (i j b : Nat) (hj : j ≤ i)
    (h : (101/100 : ℝ)^b*(100/101) ≤ 1+(100/101 : ℝ)^(i-j) ∧
      1+(100/101 : ℝ)^(i-j) ≤ (101/100 : ℝ)^b) :
    (101/100 : ℝ)^(i+b)*(100/101) ≤ (101/100 : ℝ)^i+(101/100 : ℝ)^j ∧
      (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^(i+b) := by
  have he : (101/100 : ℝ)^(i-j)*(100/101 : ℝ)^(i-j)=1 := by
    rw [← mul_pow]
    norm_num
  have hid : (101/100 : ℝ)^i*(100/101 : ℝ)^(i-j)=(101/100 : ℝ)^j := by
    rw [show i=j+(i-j) by omega, pow_add]
    rw [show j+(i-j)-j=i-j by omega, mul_assoc, he, mul_one]
  have hlo := mul_le_mul_of_nonneg_left h.1 (show 0≤(101/100 : ℝ)^i by positivity)
  have hhi := mul_le_mul_of_nonneg_left h.2 (show 0≤(101/100 : ℝ)^i by positivity)
  have hl : (101/100 : ℝ)^i*((101/100 : ℝ)^b*(100/101)) =
      (101/100 : ℝ)^(i+b)*(100/101) := by rw [pow_add]; ring
  rw [hl, mul_add, mul_one, hid] at hlo
  rw [mul_add, mul_one, hid, ← pow_add] at hhi
  exact ⟨hlo,hhi⟩

theorem mergeBin_interval (e : Fin addRuns.length) (i j : Nat) (hj : j ≤ i)
    (hlo : addRuns[e].1 ≤ i-j) (hhi : i-j ≤ addRuns[e].2.1) :
    (101/100 : ℝ)^(mergeBin i j)*(100/101) ≤ (101/100 : ℝ)^i+(101/100 : ℝ)^j ∧
      (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^(mergeBin i j) := by
  rw [mergeBin_forward e i j hj hlo hhi]
  exact add_ratio_shift i j _ hj (add_run_ratio e _ hlo hhi)

#print axioms mergeBin_interval
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.CanonicalCompression
open Finset
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem fold_add_sum {α : Type} (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun s e => s + f e) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

theorem filter_sum {α : Type} (p : α → Prop) [DecidablePred p]
    (f : α → Nat) (xs : List α) :
    ((xs.filter fun a => decide (p a)).map f).sum =
      (xs.map fun a => if p a then f a else 0).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases hp : p x <;> simp [hp, ih]

theorem acceptedMass_sum (hist : List (Nat × Nat)) (floor : Nat) :
    acceptedMass hist floor = (hist.map fun e => if floor ≤ e.1 then e.2 else 0).sum := by
  rw [acceptedMass, fold_add_sum, Nat.zero_add]
  exact filter_sum _ _ _

theorem nextMass_sum (hist : List (Nat × Nat)) (floor residual : Nat) (next : Array Nat) :
    nextMass hist floor residual next =
      (hist.map fun e => if floor ≤ e.1 then e.2 * next[residual-e.1]?.getD 0 else 0).sum := by
  rw [nextMass, fold_add_sum, Nat.zero_add]
  exact filter_sum _ _ _

end ClaudeWCT.Numerics.CanonicalCompression
namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset CanonicalCompression
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem histogramWeight_sum (hist : List (Nat × Nat)) (credit : Nat) :
    histogramWeight hist credit =
      (hist.map fun e => if e.1 = credit then e.2 else 0).sum := by
  have he : (fun (s : Nat) (e : Nat × Nat) => if e.1 = credit then s + e.2 else s) =
      (fun s e => s + if e.1 = credit then e.2 else 0) := by
    funext s e
    split_ifs <;> simp
  rw [histogramWeight, he, fold_add_sum, Nat.zero_add]

theorem histogram_sum_weighted (hist : List (Nat × Nat)) (n : Nat)
    (hbound : ∀ e ∈ hist, e.1 < n) (f : Nat → Nat) :
    ∑ i : Fin n, histogramWeight hist i.val * f i.val =
      (hist.map fun e => e.2 * f e.1).sum := by
  induction hist with
  | nil => simp [histogramWeight_sum]
  | cons e hist ih =>
      have he : e.1 < n := hbound e List.mem_cons_self
      have hh : ∀ x ∈ hist, x.1 < n := fun x hx => hbound x (List.mem_cons_of_mem e hx)
      simp only [histogramWeight_sum, List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
      simp_rw [← histogramWeight_sum]
      rw [ih hh]
      congr 1
      have ht : (fun i : Fin n => (if e.1 = i.val then e.2 else 0) * f i.val) =
          (fun i => if i = (⟨e.1, he⟩ : Fin n) then e.2 * f e.1 else 0) := by
        funext i
        by_cases hc : e.1 = i.val
        · have hi : i = (⟨e.1, he⟩ : Fin n) := Fin.ext hc.symm
          simp only [if_pos hc, if_pos hi]
          rw [hc]
        · have hi : i ≠ (⟨e.1, he⟩ : Fin n) := fun hi => hc (congrArg Fin.val hi).symm
          simp only [if_neg hc, if_neg hi, zero_mul]
      rw [ht]
      simp

theorem acceptedMass_finite (hist : List (Nat × Nat)) (n floor : Nat)
    (hbound : ∀ e ∈ hist, e.1 < n) :
    acceptedMass hist floor = ∑ i : Fin n, if floor ≤ i.val then histogramWeight hist i.val else 0 := by
  have h := histogram_sum_weighted hist n hbound (fun c => if floor ≤ c then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [acceptedMass_sum]
  simpa only [mul_ite, mul_one, mul_zero] using h.symm

theorem nextMass_finite (hist : List (Nat × Nat)) (n floor residual : Nat) (next : Array Nat)
    (hbound : ∀ e ∈ hist, e.1 < n) :
    nextMass hist floor residual next =
      ∑ i : Fin n, if floor ≤ i.val then histogramWeight hist i.val * next[residual-i.val]?.getD 0 else 0 := by
  have h := histogram_sum_weighted hist n hbound
    (fun c => if floor ≤ c then next[residual-c]?.getD 0 else 0)
  simp only [mul_ite, mul_zero] at h
  rw [nextMass_sum]
  exact h.symm

#print axioms acceptedMass_finite
#print axioms nextMass_finite
end ClaudeWCT.Numerics.CanonicalHistogram

namespace ClaudeWCT.Numerics.CanonicalCompression
open ENNReal
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem transition_enn (zn zd den weighted value rejected unit : Nat)
    (hzd : 0 < zd) (hden : 0 < den) (hunit : 0 < unit)
    (hsub : zn * rejected ≤ zd * den)
    (hrow : zn * weighted ≤ value * (zd * den - zn * rejected)) :
    ((zn : ENNReal) / zd) * ((weighted : ENNReal) / (den * unit) +
      ((rejected : ENNReal) / den) * ((value : ENNReal) / unit)) ≤ (value : ENNReal) / unit := by
  have hden0 : (den : ENNReal) ≠ 0 := by exact_mod_cast hden.ne'
  have hzd0 : (zd : ENNReal) ≠ 0 := by exact_mod_cast hzd.ne'
  have hunit0 : (unit : ENNReal) ≠ 0 := by exact_mod_cast hunit.ne'
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_natCast, Nat.cast_mul]
  exact transition_sound zn zd den weighted value rejected unit hzd hden hunit hsub hrow

theorem recurrenceCheck_sound (den : Nat) (hist : List (Nat × Nat))
    (floor residual : Nat) (next : Array Nat) (value : Nat)
    (hden : 0 < den) (hcheck : recurrenceCheck den hist floor residual next value = true) :
    1 ≤ (value : ENNReal) / scale ∧
    ((zNum : ENNReal) / zDen) *
      ((nextMass hist floor residual next : ENNReal) / (den * scale) +
       ((den - acceptedMass hist floor : Nat) : ENNReal) / den * ((value : ENNReal) / scale)) ≤
      (value : ENNReal) / scale := by
  simp only [recurrenceCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hbase, hmass⟩, hnext⟩, hsub⟩, hrow⟩
  have hscale0 : (scale : ENNReal) ≠ 0 := by norm_num [scale]
  constructor
  · apply (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mp
    simp only [ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_natCast]
    apply (le_div_iff₀ (show (0 : ℝ) < scale by norm_num [scale])).2
    simpa using (show (scale : ℝ) ≤ value by exact_mod_cast hbase)
  · exact transition_enn zNum zDen den (nextMass hist floor residual next) value
      (den - acceptedMass hist floor) scale (by norm_num [zDen]) hden (by norm_num [scale])
      hsub.le hrow

#print axioms transition_enn
#print axioms recurrenceCheck_sound
end ClaudeWCT.Numerics.CanonicalCompression


namespace ClaudeWCT.Numerics.SharedPathList
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- A coverage value and its conservatively rounded geometric bin. -/
structure RoundedInterval (loss bin : Nat) (x : ℝ) : Prop where
  nonneg : 0 ≤ x
  lower : (100/101 : ℝ)^loss * (101/100 : ℝ)^bin ≤ x
  upper : x ≤ (101/100 : ℝ)^bin

theorem RoundedInterval.mul {a b i j : Nat} {x y : ℝ}
    (hx : RoundedInterval a i x) (hy : RoundedInterval b j y) :
    RoundedInterval (a+b) (i+j) (x*y) := by
  refine ⟨mul_nonneg hx.nonneg hy.nonneg, ?_, ?_⟩
  · calc
      (100/101 : ℝ)^(a+b) * (101/100 : ℝ)^(i+j) =
          ((100/101 : ℝ)^a * (101/100 : ℝ)^i) *
            ((100/101 : ℝ)^b * (101/100 : ℝ)^j) := by
              rw [pow_add, pow_add]
              ring
      _ ≤ x*y := mul_le_mul hx.lower hy.lower (by positivity) hx.nonneg
  · calc
      x*y ≤ (101/100 : ℝ)^i * (101/100 : ℝ)^j :=
        mul_le_mul hx.upper hy.upper hy.nonneg (by positivity)
      _ = _ := (pow_add _ _ _).symm

theorem RoundedInterval.add {a i j k : Nat} {x y : ℝ}
    (hx : RoundedInterval a i x) (hy : RoundedInterval a j y)
    (hlo : (101/100 : ℝ)^k*(100/101) ≤
      (101/100 : ℝ)^i+(101/100 : ℝ)^j)
    (hhi : (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^k) :
    RoundedInterval (a+1) k (x+y) := by
  refine ⟨add_nonneg hx.nonneg hy.nonneg, ?_, (add_le_add hx.upper hy.upper).trans hhi⟩
  calc
    (100/101 : ℝ)^(a+1) * (101/100 : ℝ)^k =
        (100/101 : ℝ)^a * ((101/100 : ℝ)^k*(100/101)) := by
          rw [pow_succ]
          ring
    _ ≤ (100/101 : ℝ)^a * ((101/100 : ℝ)^i+(101/100 : ℝ)^j) :=
      mul_le_mul_of_nonneg_left hlo (by positivity)
    _ ≤ x+y := by rw [mul_add]; exact add_le_add hx.lower hy.lower

theorem RoundedInterval.prod {ι : Type} [DecidableEq ι]
    (s : Finset ι) (loss bin : ι → Nat) (x : ι → ℝ)
    (hx : ∀ i ∈ s, RoundedInterval (loss i) (bin i) (x i)) :
    RoundedInterval (∑ i ∈ s, loss i) (∑ i ∈ s, bin i) (∏ i ∈ s, x i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; constructor <;> norm_num
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hx i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hx j (Finset.mem_insert_of_mem hj)))

theorem RoundedInterval.forest (bins : Fin 4 → Nat) (xs : Fin 4 → ℝ)
    (bin : Nat) (y : ℝ)
    (hx : ∀ i, RoundedInterval 3 (bins i) (xs i))
    (hy : RoundedInterval 1 bin y) :
    RoundedInterval 13 ((∑ i, bins i)+bin) ((∏ i, xs i)*y) := by
  have hp := RoundedInterval.prod Finset.univ (fun _ : Fin 4 => 3) bins xs
    (fun i _ => hx i)
  have hc : (∑ _i : Fin 4, (3 : Nat)) = 12 := by decide
  rw [hc] at hp
  exact hp.mul hy


#print axioms RoundedInterval.forest
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedFees
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem finite_bin_rebate {α : Type} [Fintype α]
    (n : Nat) (good : α → Prop) [DecidablePred good] (bin : α → Nat)
    (weight : α → ℝ) (rebate : Nat → ℝ) :
    (∑ j ∈ range n,
      (∑ a, if good a ∧ bin a=j then weight a else 0)*rebate j) =
    ∑ a, if good a ∧ bin a<n then weight a*rebate (bin a) else 0 := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hg : good a
  · simp only [hg, true_and, ite_mul, zero_mul]
    simp [Finset.mem_range, eq_comm]
  · simp [hg]

/-- A lower histogram certifies a rebate from a global cost bound. Histories
omitted by the histogram retain the full global cost. -/
theorem histogram_fee_bound {α : Type} [Fintype α]
    (n : Nat) (good : α → Prop) [DecidablePred good] (bin : α → Nat)
    (weight cost : α → ℝ) (lower fee : Nat → ℝ) (κ G : ℝ)
    (hκ : 0 ≤ κ)
    (hfee : ∀ j, j<n → fee j ≤ G)
    (hlower : ∀ j, j<n → lower j ≤
      ∑ a, if good a ∧ bin a=j then weight a else 0)
    (hglobal : ∀ a, cost a ≤ κ*weight a*G)
    (hlocal : ∀ a, good a → bin a<n → cost a ≤ κ*weight a*fee (bin a)) :
    (∑ a, cost a) + κ*(∑ j ∈ range n, lower j*(G-fee j)) ≤
      κ*(∑ a, weight a)*G := by
  classical
  have hpoint (a : α) : cost a +
      κ*(if good a ∧ bin a<n then weight a*(G-fee (bin a)) else 0) ≤
        κ*weight a*G := by
    by_cases hg : good a ∧ bin a<n
    · rw [if_pos hg]
      nlinarith [hlocal a hg.1 hg.2]
    · rw [if_neg hg, mul_zero, add_zero]
      exact hglobal a
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset α)) (fun a _ => hpoint a)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hs
  have hrebate : (∑ j ∈ range n, lower j*(G-fee j)) ≤
      ∑ a, if good a ∧ bin a<n then weight a*(G-fee (bin a)) else 0 := by
    rw [← finite_bin_rebate n good bin weight (fun j => G-fee j)]
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (hlower j (Finset.mem_range.mp hj))
      (sub_nonneg.mpr (hfee j (Finset.mem_range.mp hj)))
  exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hrebate hκ)).trans hs

#print axioms histogram_fee_bound
end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem packFun_finset_sum {ι : Type} (s : Finset ι) (B n : Nat) (f : ι → Nat → Nat) :
    packFun B n (fun j => ∑ i ∈ s, f i j) = ∑ i ∈ s, packFun B n (f i) := by
  unfold packFun
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

theorem sum_eq_packFun {ι : Type} (s : Finset ι) (B n : Nat) (a : ι → Nat)
    (ha : ∀ i ∈ s, a i < B^n) :
    (∑ i ∈ s, a i) = packFun B n (fun j => ∑ i ∈ s, digit B (a i) j) := by
  rw [packFun_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [packFun_digits, Nat.mod_eq_of_lt (ha i hi)]

theorem digit_sum_of_bound {ι : Type} (s : Finset ι) (B n : Nat) (a : ι → Nat)
    (hB : 0 < B) (ha : ∀ i ∈ s, a i < B^n)
    (hc : ∀ j, j < n → (∑ i ∈ s, digit B (a i) j) < B)
    (j : Nat) (hj : j < n) :
    digit B (∑ i ∈ s, a i) j = ∑ i ∈ s, digit B (a i) j := by
  rw [sum_eq_packFun s B n a ha]
  exact digit_packFun B n _ hB hc j hj

theorem sum_packed_lt {ι : Type} (s : Finset ι) (B n : Nat) (a : ι → Nat)
    (hB : 0 < B) (ha : ∀ i ∈ s, a i < B^n)
    (hc : ∀ j, j < n → (∑ i ∈ s, digit B (a i) j) < B) :
    (∑ i ∈ s, a i) < B^n := by
  rw [sum_eq_packFun s B n a ha]
  exact packFun_lt B n _ hB hc

theorem digit_polynomial_eval (P : Nat[X]) (B n : Nat)
    (hB : 0 < B) (hc : ∀ j, j < n → P.coeff j < B)
    (hz : ∀ j, n ≤ j → P.coeff j = 0)
    (j : Nat) (hj : j < n) : digit B (P.eval B) j = P.coeff j := by
  rw [polynomial_eval_packFun P B n hz]
  exact digit_packFun B n _ hB hc j hj

#print axioms digit_sum_of_bound
#print axioms digit_polynomial_eval
end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weightedHistogram_selector_split {α : Type} [Fintype α] (r : Nat)
    (good : (t u : Nat) → (Fin t → α) → (Fin t → α) →
      (Fin u → α) → (Fin u → α) → Prop)
    (bin weight : (t u : Nat) → (Fin t → α) → (Fin t → α) →
      (Fin u → α) → (Fin u → α) → Nat) :
    weightedHistogram
      (fun h : (Fin r → Fin 2) × (Fin r → α) × (Fin r → α) =>
        good (occ h.1 0) (occ h.1 1)
          (splitRanks h.1 h.2.1 0) (splitRanks h.1 h.2.2 0)
          (splitRanks h.1 h.2.1 1) (splitRanks h.1 h.2.2 1))
      (fun h => bin (occ h.1 0) (occ h.1 1)
          (splitRanks h.1 h.2.1 0) (splitRanks h.1 h.2.2 0)
          (splitRanks h.1 h.2.1 1) (splitRanks h.1 h.2.2 1))
      (fun h => weight (occ h.1 0) (occ h.1 1)
          (splitRanks h.1 h.2.1 0) (splitRanks h.1 h.2.2 0)
          (splitRanks h.1 h.2.1 1) (splitRanks h.1 h.2.2 1)) =
    ∑ t ∈ range (r+1), r.choose t •
      weightedHistogram
        (fun h : ((Fin t → α) × (Fin t → α)) ×
          ((Fin (r-t) → α) × (Fin (r-t) → α)) =>
            good t (r-t) h.1.1 h.1.2 h.2.1 h.2.2)
        (fun h => bin t (r-t) h.1.1 h.1.2 h.2.1 h.2.2)
        (fun h => weight t (r-t) h.1.1 h.1.2 h.2.1 h.2.2) := by
  classical
  unfold weightedHistogram
  simp only [Fintype.sum_prod_type]
  exact sum_pair_split r (fun t u A₀ B₀ A₁ B₁ =>
    if good t u A₀ B₀ A₁ B₁ then
      C (weight t u A₀ B₀ A₁ B₁)*X^(bin t u A₀ B₀ A₁ B₁) else 0)

#print axioms weightedHistogram_selector_split
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

abbrev AddPiece := Fin addRuns.length × Bool

def addPieceGood (e : AddPiece) (i j : Nat) : Prop :=
  if e.2 then i<j ∧ addRuns[e.1].1 ≤ j-i ∧ j-i ≤ addRuns[e.1].2.1
  else j ≤ i ∧ addRuns[e.1].1 ≤ i-j ∧ i-j ≤ addRuns[e.1].2.1

def addPieceBin (e : AddPiece) (i j : Nat) : Nat :=
  (if e.2 then j else i)+addRuns[e.1].2.2

theorem addPiece_unique (e f : AddPiece) (i j : Nat)
    (he : addPieceGood e i j) (hf : addPieceGood f i j) : e=f := by
  rcases e with ⟨e,be⟩
  rcases f with ⟨f,bf⟩
  cases be <;> cases bf <;> simp only [addPieceGood, Bool.false_eq_true, if_false, if_true] at he hf
  · exact Prod.ext (add_run_unique e f (i-j) he.2 hf.2) rfl
  · omega
  · omega
  · exact Prod.ext (add_run_unique e f (j-i) he.2 hf.2) rfl

theorem addPiece_bin (e : AddPiece) (i j : Nat) (he : addPieceGood e i j) :
    addPieceBin e i j=mergeBin i j := by
  rcases e with ⟨e,b⟩
  cases b <;> simp only [addPieceGood, Bool.false_eq_true, if_false, if_true] at he
  · exact (mergeBin_forward e i j he.1 he.2.1 he.2.2).symm
  · rw [mergeBin_comm]
    exact (mergeBin_forward e j i (Nat.le_of_lt he.1) he.2.1 he.2.2).symm

theorem pair_partition_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) (gb : β → Prop) (ba wa : α → Nat) (bb wb : β → Nat) :
    CoeffLE (∑ e : AddPiece,
      weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2 ∧ addPieceGood e (ba p.1) (bb p.2))
        (fun p => addPieceBin e (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2))
      (weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
        (fun p => mergeBin (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2)) := by
  apply weightedHistogram_partition
  · intro e p hp
    exact ⟨hp.1,hp.2.1⟩
  · intro e p hp
    exact addPiece_bin e _ _ hp.2.2
  · intro e f p he hf
    exact addPiece_unique e f _ _ he.2.2 hf.2.2

#print axioms pair_partition_lower
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset ClaudeWCT.Numerics.N600
set_option maxHeartbeats 2000000

theorem coordinate_coverage_pos {β C : Type} [Fintype β] [Fintype C] [DecidableEq C]
    (val : β → Fin 6 → Nat) {r : Nat} (hr : 0<r) (E : Fin r → C×β) :
    0<coordinateCoverage val E := by
  classical
  unfold coordinateCoverage
  apply Finset.card_pos.mpr
  refine ⟨E ⟨0,hr⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  intro i
  exact ⟨⟨0,hr⟩,rfl,le_rfl⟩

#print axioms coordinate_coverage_pos
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Disjoint retained pieces may be added in packed form without a carry.
The bound comes from the mass of the actual history space. -/
theorem packed_histogram_sum_lower {ι α : Type} [Fintype ι] [Fintype α]
    (B n M : Nat) (hB : 0<B)
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (p : ι → Nat) (P : ι → Nat[X])
    (hp : ∀ e, p e<B^n)
    (hd : ∀ e j, j<n → digit B (p e) j≤(P e).coeff j)
    (hP : CoeffLE (∑ e, P e) (weightedHistogram good bin weight))
    (hM : ∀ a, good a → weight a≤M) (hmass : Fintype.card α*M<B) :
    (∑ e, p e)<B^n ∧
      ∀ j, j<n → digit B (∑ e, p e) j≤(weightedHistogram good bin weight).coeff j := by
  have hc (j : Nat) (hj : j<n) :
      (∑ e, digit B (p e) j)<B := by
    calc _ ≤ ∑ e, (P e).coeff j := Finset.sum_le_sum (fun e _ => hd e j hj)
         _ = (∑ e, P e).coeff j := (Polynomial.finset_sum_coeff _ _ _).symm
         _ ≤ (weightedHistogram good bin weight).coeff j := hP j
         _ ≤ (weightedHistogram good bin weight).eval 1 := polynomial_coeff_le_mass _ _
         _ ≤ Fintype.card α*M := weightedHistogram_mass_le good bin weight M hM
         _ < B := hmass
  refine ⟨sum_packed_lt univ B n p hB (fun e _ => hp e) hc, ?_⟩
  intro j hj
  rw [digit_sum_of_bound univ B n p hB (fun e _ => hp e) hc j hj]
  calc _ ≤ ∑ e, (P e).coeff j := Finset.sum_le_sum (fun e _ => hd e j hj)
       _ = (∑ e, P e).coeff j := (Polynomial.finset_sum_coeff _ _ _).symm
       _ ≤ _ := hP j

#print axioms packed_histogram_sum_lower
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem directed_cross_small {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat)
    (ap af bp bf : Nat → Nat)
    (haP : ∀ i, ap i ≤ ∑ a, if ga a ∧ ba a=i then 1 else 0)
    (haF : ∀ i, af i ≤ ∑ a, if ga a ∧ ba a=i then wa a else 0)
    (hbP : ∀ j, bp j ≤ ∑ b, if gb b ∧ bb b=j then 1 else 0)
    (hbF : ∀ j, bf j ≤ ∑ b, if gb b ∧ bb b=j then wb b else 0)
    (Ma Mb B : Nat) (hwa : ∀ a, wa a≤Ma) (hwb : ∀ b, wb b≤Mb)
    (hB : Fintype.card α*Fintype.card β*(Ma+Mb)<B)
    (i : Nat) (s : Finset Nat) :
    af i*(∑ j ∈ s, bp j) + ap i*(∑ j ∈ s, bf j)<B := by
  apply (directed_fiber_lower ga gb ba wa bb wb ap af bp bf haP haF hbP hbF i s).trans_lt
  calc (∑ p : α×β, if (ga p.1 ∧ ba p.1=i) ∧ (gb p.2 ∧ bb p.2∈s)
          then wa p.1+wb p.2 else 0) ≤ ∑ _p : α×β, (Ma+Mb) := by
        apply Finset.sum_le_sum
        intro p _
        split_ifs
        · exact Nat.add_le_add (hwa p.1) (hwb p.2)
        · exact Nat.zero_le _
       _ = Fintype.card α*Fintype.card β*(Ma+Mb) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          nsmul_eq_mul, Nat.cast_id]
       _ < B := hB

#print axioms directed_cross_small
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset
open ClaudeWCT.Numerics.SharedPathList (Cell addRuns)
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem fold_add_pair {α : Type} (xs : List α) (f g : α → Nat) (acc : Nat) :
    xs.foldl (fun s e => s+f e+g e) acc =
      acc+(xs.map (fun e => f e+g e)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons e xs ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

theorem list_sum_fin {α : Type} (xs : List α) (f : α → Nat) :
    (xs.map f).sum = ∑ i : Fin xs.length, f xs[i] := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Fin.sum_univ_succ,
      Fin.getElem_fin, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ]

def addPieceValue (a b : Cell) (e : Fin addRuns.length × Bool) : Nat :=
  if e.2 then
    if addRuns[e.1].2.1=0 then 0 else
      directedFirst b (prefixes a.1, prefixes a.2)
        (max 1 addRuns[e.1].1) addRuns[e.1].2.1 addRuns[e.1].2.2
  else directedFirst a (prefixes b.1, prefixes b.2)
      addRuns[e.1].1 addRuns[e.1].2.1 addRuns[e.1].2.2

theorem addFirst_eq_piece_sum (a b : Cell) :
    addFirst a b = ∑ e : Fin addRuns.length × Bool, addPieceValue a b e := by
  rw [addFirst, fold_add_pair, Nat.zero_add, list_sum_fin]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [addPieceValue, Nat.add_comm]

theorem addPieceValue_bound (a b : Cell) (e : Fin addRuns.length × Bool) :
    addPieceValue a b e < (2^1024)^2048 := by
  have hb (a pref : Cell) (lo hi shift : Nat) :
      directedFirst a pref lo hi shift < (2^1024)^2048 := by
    unfold directedFirst cutMask
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, ←pow_mul]
    exact Nat.mod_lt _ (by positivity)
  unfold addPieceValue
  split_ifs
  · positivity
  · exact hb _ _ _ _ _
  · exact hb _ _ _ _ _

#print axioms addFirst_eq_piece_sum
#print axioms addPieceValue_bound
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem addFirst_histogram_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat) (a b : Cell)
    (Ma Mb : Nat) (hwa : ∀ x, wa x≤Ma) (hwb : ∀ y, wb y≤Mb)
    (hmass : Fintype.card α*Fintype.card β*(Ma+Mb)<2^1024)
    (hpiece : ∀ (e : AddPiece) j, j<2048 →
      digit (2^1024) (addPieceValue a b e) j ≤
        (weightedHistogram
          (fun p : α×β => ga p.1 ∧ gb p.2 ∧ addPieceGood e (ba p.1) (bb p.2))
          (fun p => addPieceBin e (ba p.1) (bb p.2))
          (fun p => wa p.1+wb p.2)).coeff j) :
    addFirst a b<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024) (addFirst a b) j≤
        (weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
          (fun p => mergeBin (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2)).coeff j := by
  classical
  rw [addFirst_eq_piece_sum]
  apply packed_histogram_sum_lower (2^1024) 2048 (Ma+Mb) (by positivity)
    (fun p : α×β => ga p.1 ∧ gb p.2)
    (fun p => mergeBin (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2)
    (addPieceValue a b)
    (fun e => weightedHistogram
      (fun p : α×β => ga p.1 ∧ gb p.2 ∧ addPieceGood e (ba p.1) (bb p.2))
      (fun p => addPieceBin e (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2))
    (addPieceValue_bound a b) hpiece (pair_partition_lower ga gb ba wa bb wb)
  · intro p _
    exact Nat.add_le_add (hwa p.1) (hwb p.2)
  · simpa only [Fintype.card_prod] using hmass

#print axioms addFirst_histogram_lower
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedFees
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Exact integer accounting of retained fees and omitted first moment. -/
theorem histogram_paid_bound {α : Type} [Fintype α]
    (n : Nat) (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (cost : α → ℝ) (lower fee : Nat → Nat) (κ : ℝ) (G : Nat)
    (hκ : 0≤κ) (hfee : ∀ j, j<n → fee j≤G)
    (hlower : ∀ j, j<n → lower j≤∑ a, if good a ∧ bin a=j then weight a else 0)
    (hmass : (∑ j ∈ range n, lower j)≤∑ a, weight a)
    (hglobal : ∀ a, cost a≤κ*(weight a : ℝ)*G)
    (hlocal : ∀ a, good a → bin a<n → cost a≤κ*(weight a : ℝ)*(fee (bin a) : ℝ)) :
    (∑ a, cost a)≤κ*((((∑ j ∈ range n, lower j*fee j) +
      G*((∑ a, weight a)-(∑ j ∈ range n, lower j)) : Nat) : ℝ)) := by
  classical
  have h := histogram_fee_bound n good bin (fun a => (weight a : ℝ)) cost
    (fun j => (lower j : ℝ)) (fun j => (fee j : ℝ)) κ (G : ℝ) hκ
    (fun j hj => by exact_mod_cast hfee j hj)
    (fun j hj => by exact_mod_cast hlower j hj) hglobal hlocal
  have he : (∑ j ∈ range n, (lower j : ℝ)*((G : ℝ)-(fee j : ℝ))) =
      (G : ℝ)*(∑ j ∈ range n, (lower j : ℝ))-
        ∑ j ∈ range n, (lower j : ℝ)*(fee j : ℝ) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ←Finset.sum_mul]
    ring
  rw [he] at h
  push_cast [Nat.cast_sub hmass]
  nlinarith [h]

#print axioms histogram_paid_bound
end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def packedPoly (B n p : Nat) : Nat[X] := polyOf n (digit B p)

theorem packedPoly_eval (B n p : Nat) (hp : p<B^n) :
    (packedPoly B n p).eval B=p := by
  rw [packedPoly, polyOf_eval, packFun_digits, Nat.mod_eq_of_lt hp]


theorem packedPoly_below (B n p : Nat) (Q : Nat[X])
    (hd : ∀ j, j<n → digit B p j≤Q.coeff j) :
    CoeffLE (packedPoly B n p) Q := by
  intro j
  rw [packedPoly, polyOf_coeff]
  split_ifs with hj
  · exact hd j hj
  · exact Nat.zero_le _

theorem changeBase_polynomial (B C h p : Nat) (hB : 0<B) (hp : p<B^(2^h)) :
    changeBase B C h p=(packedPoly B (2^h) p).eval C := by
  rw [changeBase_model B C hB h p hp, packedPoly, polyOf_eval]

#print axioms packedPoly_below
#print axioms changeBase_polynomial
end ClaudeWCT.Numerics.SharedDigitBlock

namespace ClaudeWCT.Numerics.SharedPathPacked
open Polynomial ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000

theorem spread_polynomial (h p : Nat) (hp : p<(2^1024)^(2^h)) :
    spread h p=(packedPoly (2^1024) (2^h) p).eval (2^4096) := by
  rw [spread_eq_changeBase]
  exact changeBase_polynomial _ _ h p (by positivity) hp

theorem forest_packed_polynomial (p q : Nat)
    (hp : p<(2^1024)^2048) (hq : q<(2^1024)^1024) :
    (spread 11 p)^4*spread 10 q =
      ((packedPoly (2^1024) 2048 p)^4*packedPoly (2^1024) 1024 q).eval (2^4096) := by
  have hp' : p<(2^1024)^(2^11) := by simpa only [show (2:Nat)^11=2048 from rfl] using hp
  have hq' : q<(2^1024)^(2^10) := by simpa only [show (2:Nat)^10=1024 from rfl] using hq
  rw [spread_polynomial 11 p hp', spread_polynomial 10 q hq']
  simp only [Polynomial.eval_mul, Polynomial.eval_pow,
    show (2:Nat)^11=2048 from rfl, show (2:Nat)^10=1024 from rfl]

#print axioms forest_packed_polynomial
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem histogram_moment_bound {α : Type} [Fintype α]
    (n total G : Nat) (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (P : Nat[X]) (hP : CoeffLE P (weightedHistogram good bin weight))
    (htotal : (∑ a, weight a)=total)
    (cost : α → ℝ) (fee : Nat → Nat) (κ : ℝ)
    (hκ : 0≤κ) (hfee : ∀ j, j<n → fee j≤G)
    (hglobal : ∀ a, cost a≤κ*(weight a : ℝ)*G)
    (hlocal : ∀ a, good a → bin a<n → cost a≤κ*(weight a : ℝ)*(fee (bin a) : ℝ)) :
    (∑ a, cost a)≤κ*((((∑ j ∈ range n, P.coeff j*fee j) +
      G*(total-(∑ j ∈ range n, P.coeff j)) : Nat) : ℝ)) := by
  classical
  have hm : (∑ j ∈ range n, P.coeff j)≤∑ a, weight a := by
    calc _ ≤ P.eval 1 := sum_coeff_le_eval_one P (range n)
         _ ≤ (weightedHistogram good bin weight).eval 1 := polynomial_mass_mono hP
         _ = ∑ a, if good a then weight a else 0 := weightedHistogram_eval_one good bin weight
         _ ≤ ∑ a, weight a := Finset.sum_le_sum (fun a _ => by split_ifs <;> omega)
  have h := histogram_paid_bound n good bin weight cost P.coeff fee κ G hκ hfee
    (fun j _ => by simpa only [weightedHistogram_coeff] using hP j) hm hglobal hlocal
  simpa only [htotal] using h


#print axioms histogram_moment_bound
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.CanonicalCompression
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem acceptedMass_antitone (hist : List (Nat × Nat)) {floor lower : Nat} (hle : lower ≤ floor) :
    acceptedMass hist floor ≤ acceptedMass hist lower := by
  induction hist with
  | nil => simp [acceptedMass_sum]
  | cons e hist ih =>
      simp only [acceptedMass_sum, List.map_cons, List.sum_cons] at ih ⊢
      by_cases hf : floor ≤ e.1
      · have hl := hle.trans hf
        simp only [if_pos hf, if_pos hl]
        omega
      · by_cases hl : lower ≤ e.1
        · simp only [if_neg hf, if_pos hl]
          omega
        · simp only [if_neg hf, if_neg hl]
          simpa only [Nat.zero_add] using ih

#print axioms acceptedMass_antitone
end ClaudeWCT.Numerics.CanonicalCompression

namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem prefix_coeff_lt_of_mass (P : Nat[X]) (n B : Nat) (h : P.eval 1*n<B)
    (j : Nat) : (P*geomPoly n).coeff j<B := by
  apply (polynomial_coeff_le_mass _ j).trans_lt
  simpa [Polynomial.eval_mul, geomPoly_eval] using h

theorem directed_polynomial_histogram_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat)
    (aP aF bP bF : Nat[X]) (lo hi shift Ma Mb : Nat)
    (haP : aP.eval (2^1024)<(2^1024)^2048)
    (haF : aF.eval (2^1024)<(2^1024)^2048)
    (haPc : ∀ j, aP.coeff j<2^1024) (haFc : ∀ j, aF.coeff j<2^1024)
    (hbPm : bP.eval 1*2048<2^1024) (hbFm : bF.eval 1*2048<2^1024)
    (hap : CoeffLE aP (weightedHistogram ga ba (fun _ => 1)))
    (haf : CoeffLE aF (weightedHistogram ga ba wa))
    (hbp : CoeffLE bP (weightedHistogram gb bb (fun _ => 1)))
    (hbf : CoeffLE bF (weightedHistogram gb bb wb))
    (hlo : lo≤hi) (hwa : ∀ a, wa a≤Ma) (hwb : ∀ b, wb b≤Mb)
    (hsize : Fintype.card α*Fintype.card β*(Ma+Mb)<2^1024)
    (k : Nat) (hk : k<2048) :
    digit (2^1024)
      (directedFirst (aP.eval (2^1024),aF.eval (2^1024))
        (prefixes (bP.eval (2^1024)),prefixes (bF.eval (2^1024))) lo hi shift) k ≤
      (weightedHistogram
        (fun p : α×β => ga p.1 ∧ gb p.2 ∧ bb p.2≤ba p.1 ∧
          lo≤ba p.1-bb p.2 ∧ ba p.1-bb p.2≤hi)
        (fun p => ba p.1+shift) (fun p => wa p.1+wb p.2)).coeff k := by
  have da (j : Nat) : digit (2^1024) (aP.eval (2^1024)) j=aP.coeff j :=
    ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j aP haPc
  have df (j : Nat) : digit (2^1024) (aF.eval (2^1024)) j=aF.coeff j :=
    ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j aF haFc
  have hbp' (j : Nat) : bP.coeff j≤∑ b, if gb b ∧ bb b=j then 1 else 0 := by
    simpa only [weightedHistogram_coeff] using hbp j
  have hbf' (j : Nat) : bF.coeff j≤∑ b, if gb b ∧ bb b=j then wb b else 0 := by
    simpa only [weightedHistogram_coeff] using hbf j
  have hap' (j : Nat) : digit (2^1024) (aP.eval (2^1024)) j≤
      ∑ a, if ga a ∧ ba a=j then 1 else 0 := by
    rw [da]; simpa only [weightedHistogram_coeff] using hap j
  have haf' (j : Nat) : digit (2^1024) (aF.eval (2^1024)) j≤
      ∑ a, if ga a ∧ ba a=j then wa a else 0 := by
    rw [df]; simpa only [weightedHistogram_coeff] using haf j
  have wp := window_prefix_interval bP (prefix_coeff_lt_of_mass bP 2048 _ hbPm) lo hi
  have wf := window_prefix_interval bF (prefix_coeff_lt_of_mass bF 2048 _ hbFm) lo hi
  apply directed_histogram_lower ga gb ba wa bb wb _ _ bP.coeff bF.coeff lo hi shift
    haP haF ?_ (fun j hj => wp j hlo hj) (fun j hj => wf j hlo hj)
    hap' haf' hbp' hbf' k hk
  intro j hj
  dsimp only
  rw [wp j hlo hj, wf j hlo hj]
  by_cases hl : lo≤j
  · simp only [if_pos hl]
    exact directed_cross_small ga gb ba wa bb wb _ _ bP.coeff bF.coeff
      hap' haf' hbp' hbf' Ma Mb _ hwa hwb hsize j (Ico (j-hi) (j-lo+1))
  · simp only [if_neg hl, Nat.mul_zero, Nat.zero_add]
    positivity

#print axioms prefix_coeff_lt_of_mass
#print axioms directed_polynomial_histogram_lower
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedPathCoordinate
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

abbrev binList : List Nat := 0 :: binPairs.map Prod.snd

theorem binList_length : binList.length = 11261 := by
  have h := congrArg List.length bin_indices_checked
  simp only [List.length_map, List.length_range'] at h
  simp only [binList, List.length_cons, List.length_map, h]

theorem binList_bound_checked : binList.all (fun b => decide (b<1024)) = true := by decide +kernel

theorem binList_bound (i : Fin binList.length) : binList[i]<1024 := by
  have h := List.all_eq_true.mp binList_bound_checked _ (List.getElem_mem i.isLt)
  exact of_decide_eq_true h

private theorem child_bounds (K : Nat) (hK : K ∈ [64,128]) : 1 ≤ K ∧ K ≤ 128 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
  rcases hK with hK | hK <;> subst K <;> decide

theorem history_mass_small {β : Type} [Fintype β] (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21) :
    Fintype.card (Fin r.val → Fin K×β)<2^384 ∧
      Fintype.card (Fin r.val → Fin K×β)*(K*563)<2^384 := by
  rw [coordinate_history_card hβ K r.val]
  have hmass := coordinate_mass_small K r.val (child_bounds K hK).2 (by omega)
  refine ⟨?_,hmass⟩
  calc
    (K*563)^r.val = (K*563)^r.val*1 := (Nat.mul_one _).symm
    _ ≤ (K*563)^r.val*(K*563) := Nat.mul_le_mul_left _ (by have := (child_bounds K hK).1; omega)
    _ < 2^384 := hmass

/-- The concrete packed coordinate stores the two retained histograms exactly;
no arithmetic carry can cross the1024-bit bins. -/
theorem coordinate_polynomial {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    coordinate K r.val =
      ((binnedPoly binList (coordinatePoly K r.val).coeff).eval (2^1024),
       (binnedPoly binList (fun j => j*(coordinatePoly K r.val).coeff j)).eval (2^1024)) := by
  have hm := history_mass_small hβ K hK r
  have h := bucket_no_carry binList (coordinateCoverage val) (coordinatePoly K r.val) hp (K*563)
    (coordinate_coverage_le val hβ) (hm.1.trans_le (by decide +kernel))
    (hm.2.trans_le (by decide +kernel))
  simpa only [coordinate, coordinatePacked_eval, binList] using h.1

theorem coordinate_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    CoeffLE (binnedPoly binList (coordinatePoly K r.val).coeff)
      (weightedHistogram (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (fun _ => 1)) ∧
    CoeffLE (binnedPoly binList (fun j => j*(coordinatePoly K r.val).coeff j))
      (weightedHistogram (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (coordinateCoverage val)) :=
  coordinate_histograms_lower binList (coordinateCoverage val) (coordinatePoly K r.val) hp

theorem coordinate_mass {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    (binnedPoly binList (coordinatePoly K r.val).coeff).eval 1<2^384 ∧
    (binnedPoly binList (fun j => j*(coordinatePoly K r.val).coeff j)).eval 1<2^384 := by
  have h := coordinate_histograms_mass binList (coordinateCoverage val) (coordinatePoly K r.val) hp
    (K*563) (coordinate_coverage_le val hβ)
  have hm := history_mass_small hβ K hK r
  exact ⟨h.1.trans_lt hm.1,h.2.trans_lt hm.2⟩

theorem coordinate_size {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    (coordinate K r.val).1<(2^1024)^1024 ∧ (coordinate K r.val).2<(2^1024)^1024 := by
  have hm := history_mass_small hβ K hK r
  have h := bucket_histogram_bounds binList (coordinateCoverage val) (coordinatePoly K r.val) hp
    (K*563) 1024 (coordinate_coverage_le val hβ) (hm.1.trans_le (by decide +kernel))
      (hm.2.trans_le (by decide +kernel)) binList_bound
  simpa only [coordinate, coordinatePacked_eval, binList] using h

#print axioms coordinate_polynomial
#print axioms coordinate_histogram
#print axioms coordinate_mass
#print axioms coordinate_size
end ClaudeWCT.Numerics.SharedPathCoordinate


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def pieceValueWith
    (F : Cell → Cell → Nat → Nat → Nat → Nat) (P : Nat → Nat)
    (runs : List (Nat × Nat × Nat)) (a b : Cell) (e : Fin runs.length × Bool) : Nat :=
  if e.2 then
    if runs[e.1].2.1=0 then 0 else
      F b (P a.1,P a.2) (max 1 runs[e.1].1) runs[e.1].2.1 runs[e.1].2.2
  else F a (P b.1,P b.2) runs[e.1].1 runs[e.1].2.1 runs[e.1].2.2

theorem pieceValueWith_reverse
    (F : Cell → Cell → Nat → Nat → Nat → Nat) (P : Nat → Nat)
    (runs : List (Nat × Nat × Nat)) (a b : Cell) (e : Fin runs.length)
    (hz : runs[e].2.1≠0) :
    pieceValueWith F P runs a b (e,true) =
      F b (P a.1,P a.2) (max 1 runs[e].1) runs[e].2.1 runs[e].2.2 := by
  simp only [pieceValueWith, if_true, if_neg hz]

theorem pieceValueWith_forward
    (F : Cell → Cell → Nat → Nat → Nat → Nat) (P : Nat → Nat)
    (runs : List (Nat × Nat × Nat)) (a b : Cell) (e : Fin runs.length) :
    pieceValueWith F P runs a b (e,false) =
      F a (P b.1,P b.2) runs[e].1 runs[e].2.1 runs[e].2.2 := rfl

theorem addPieceValue_model (a b : Cell) (e : AddPiece) :
    addPieceValue a b e=pieceValueWith directedFirst prefixes addRuns a b e := rfl

theorem addPieceValue_forward (a b : Cell) (e : Fin addRuns.length) :
    addPieceValue a b (e,false) =
      directedFirst a (prefixes b.1,prefixes b.2)
        addRuns[e].1 addRuns[e].2.1 addRuns[e].2.2 :=
  (addPieceValue_model a b (e,false)).trans
    (pieceValueWith_forward directedFirst prefixes addRuns a b e)

theorem addPieceValue_reverse (a b : Cell) (e : Fin addRuns.length)
    (hz : addRuns[e].2.1≠0) :
    addPieceValue a b (e,true) =
      directedFirst b (prefixes a.1,prefixes a.2)
        (max 1 addRuns[e].1) addRuns[e].2.1 addRuns[e].2.2 :=
  (addPieceValue_model a b (e,true)).trans
    (pieceValueWith_reverse directedFirst prefixes addRuns a b e hz)

theorem histogram_reverse {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) (gb : β → Prop)
    (ba wa : α → Nat) (bb wb : β → Nat) (lo hi shift : Nat) :
    weightedHistogram
      (fun p : β×α => gb p.1 ∧ ga p.2 ∧ ba p.2≤bb p.1 ∧
        max 1 lo≤bb p.1-ba p.2 ∧ bb p.1-ba p.2≤hi)
      (fun p => bb p.1+shift) (fun p => wb p.1+wa p.2) =
    weightedHistogram
      (fun p : α×β => ga p.1 ∧ gb p.2 ∧ ba p.1<bb p.2 ∧
        lo≤bb p.2-ba p.1 ∧ bb p.2-ba p.1≤hi)
      (fun p => bb p.2+shift) (fun p => wa p.1+wb p.2) := by
  classical
  have he := weightedHistogram_equiv (Equiv.prodComm α β)
    (fun p : β×α => gb p.1 ∧ ga p.2 ∧ ba p.2≤bb p.1 ∧
      max 1 lo≤bb p.1-ba p.2 ∧ bb p.1-ba p.2≤hi)
    (fun p => bb p.1+shift) (fun p => wb p.1+wa p.2)
  have hg : (fun p : α×β => gb p.2 ∧ ga p.1 ∧ ba p.1≤bb p.2 ∧
      max 1 lo≤bb p.2-ba p.1 ∧ bb p.2-ba p.1≤hi) =
      (fun p : α×β => ga p.1 ∧ gb p.2 ∧ ba p.1<bb p.2 ∧
        lo≤bb p.2-ba p.1 ∧ bb p.2-ba p.1≤hi) := by
    funext p
    apply propext
    constructor
    · rintro ⟨hb,ha,hle,hlo,hhi⟩
      exact ⟨ha,hb,by omega,by omega,hhi⟩
    · rintro ⟨ha,hb,hlt,hlo,hhi⟩
      exact ⟨hb,ha,by omega,by omega,hhi⟩
  calc _ = _ := he.symm
       _ = _ := by
        change weightedHistogram
          (fun p : α×β => gb p.2 ∧ ga p.1 ∧ ba p.1≤bb p.2 ∧
            max 1 lo≤bb p.2-ba p.1 ∧ bb p.2-ba p.1≤hi)
          (fun p => bb p.2+shift) (fun p => wb p.2+wa p.1) = _
        rw [hg]
        congr 1
        funext p
        exact Nat.add_comm _ _

theorem addFirst_polynomial_histogram_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat)
    (aP aF bP bF : Nat[X]) (Ma Mb : Nat)
    (haP : aP.eval (2^1024)<(2^1024)^2048)
    (haF : aF.eval (2^1024)<(2^1024)^2048)
    (hbP : bP.eval (2^1024)<(2^1024)^2048)
    (hbF : bF.eval (2^1024)<(2^1024)^2048)
    (haPm : aP.eval 1*2048<2^1024) (haFm : aF.eval 1*2048<2^1024)
    (hbPm : bP.eval 1*2048<2^1024) (hbFm : bF.eval 1*2048<2^1024)
    (hap : CoeffLE aP (weightedHistogram ga ba (fun _ => 1)))
    (haf : CoeffLE aF (weightedHistogram ga ba wa))
    (hbp : CoeffLE bP (weightedHistogram gb bb (fun _ => 1)))
    (hbf : CoeffLE bF (weightedHistogram gb bb wb))
    (hwa : ∀ a, wa a≤Ma) (hwb : ∀ b, wb b≤Mb)
    (hsize : Fintype.card α*Fintype.card β*(Ma+Mb)<2^1024) :
    addFirst (aP.eval (2^1024),aF.eval (2^1024))
        (bP.eval (2^1024),bF.eval (2^1024))<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024)
        (addFirst (aP.eval (2^1024),aF.eval (2^1024))
          (bP.eval (2^1024),bF.eval (2^1024))) j≤
        (weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
          (fun p => mergeBin (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2)).coeff j := by
  classical
  have coeff (P : Nat[X]) (h : P.eval 1*2048<2^1024) (j : Nat) : P.coeff j<2^1024 := by
    have hc := polynomial_coeff_le_mass P j
    omega
  apply addFirst_histogram_lower ga gb ba wa bb wb _ _ Ma Mb hwa hwb hsize
  intro e k hk
  rcases e with ⟨e,b⟩
  cases b
  · apply (congrArg (fun x => digit (2^1024) x k)
      (addPieceValue_forward (aP.eval (2^1024),aF.eval (2^1024))
        (bP.eval (2^1024),bF.eval (2^1024)) e)).le.trans
    exact directed_polynomial_histogram_lower ga gb ba wa bb wb aP aF bP bF
      addRuns[e].1 addRuns[e].2.1 addRuns[e].2.2 Ma Mb
      haP haF (coeff aP haPm) (coeff aF haFm) hbPm hbFm hap haf hbp hbf
      (add_run_bounds e).1 hwa hwb hsize k hk
  · by_cases hz : addRuns[e].2.1=0
    · simp only [addPieceValue, if_true, hz, digit, Nat.zero_div, Nat.zero_mod]
      exact Nat.zero_le _
    · have hlo : max 1 addRuns[e].1≤addRuns[e].2.1 := by
        have h := (add_run_bounds e).1
        omega
      have hs : Fintype.card β*Fintype.card α*(Mb+Ma)<2^1024 := by
        simpa only [Nat.mul_comm, Nat.add_comm] using hsize
      have h := directed_polynomial_histogram_lower gb ga bb wb ba wa bP bF aP aF
        (max 1 addRuns[e].1) addRuns[e].2.1 addRuns[e].2.2 Mb Ma
        hbP hbF (coeff bP hbPm) (coeff bF hbFm) haPm haFm hbp hbf hap haf
        hlo hwb hwa hs k hk
      have he' := histogram_reverse ga gb ba wa bb wb
        addRuns[e].1 addRuns[e].2.1 addRuns[e].2.2
      have hh := h.trans_eq (congrArg (fun P : Nat[X] => P.coeff k) he')
      exact (congrArg (fun x => digit (2^1024) x k)
        (addPieceValue_reverse (aP.eval (2^1024),aF.eval (2^1024))
          (bP.eval (2^1024),bF.eval (2^1024)) e hz)).le.trans hh

#print axioms addPieceValue_reverse
#print axioms addFirst_polynomial_histogram_lower
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedPathCoordinate
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable abbrev probPoly (K r : Nat) : Nat[X] := binnedPoly binList (coordinatePoly K r).coeff
noncomputable abbrev firstPoly (K r : Nat) : Nat[X] :=
  binnedPoly binList (fun j => j*(coordinatePoly K r).coeff j)

attribute [local irreducible] binnedPoly coordinatePoly

noncomputable def coordinateGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : Fin r → Fin K×β) : Prop := coordinateCoverage val h<binList.length
noncomputable def coordinateBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : Fin r → Fin K×β) : Nat := binList[coordinateCoverage val h]?.getD 0

abbrev BranchHistory (β : Type) (K r : Nat) :=
  (Fin r → Fin K×β) × (Fin r → Fin K×β)
noncomputable def branchGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : BranchHistory β K r) : Prop :=
  coordinateGood val h.1 ∧ coordinateGood val h.2
noncomputable def branchBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : BranchHistory β K r) : Nat := coordinateBin val h.1+coordinateBin val h.2
noncomputable def branchCoverage {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : BranchHistory β K r) : Nat :=
  coordinateCoverage val h.1*coordinateCoverage val h.2

theorem branch_bin_bound {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) {K r : Nat} (h : BranchHistory β K r)
    (hg : branchGood val h) : branchBin val h<2047 := by
  have hb (a : Fin r → Fin K×β) (ha : coordinateGood val a) : coordinateBin val a<1024 := by
    unfold coordinateGood at ha
    unfold coordinateBin
    rw [List.getElem?_eq_getElem ha]
    exact binList_bound ⟨coordinateCoverage val a,ha⟩
  have h1 := hb h.1 hg.1
  have h2 := hb h.2 hg.2
  unfold branchBin
  omega

theorem branch_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    CoeffLE ((probPoly K r.val)^2) (weightedHistogram (branchGood val)
      (branchBin val) (fun _ : BranchHistory β K r.val => 1)) ∧
    CoeffLE ((firstPoly K r.val)^2) (weightedHistogram (branchGood val)
      (branchBin val) (branchCoverage (K:=K) (r:=r.val) val)) := by
  have h := coordinate_histogram val hβ K hK r hp
  unfold probPoly firstPoly branchGood branchBin branchCoverage coordinateGood coordinateBin
  constructor
  · simpa only [pow_two, probPoly, branchGood, coordinateGood, branchBin, coordinateBin,
      Nat.one_mul] using weightedHistogram_product_lower
        (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (fun _ => 1)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (fun _ => 1)
        _ _ h.1 h.1
  · simpa only [pow_two, firstPoly, branchGood, coordinateGood, branchBin, coordinateBin,
      branchCoverage] using weightedHistogram_product_lower
        (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (coordinateCoverage val)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (coordinateCoverage val)
        _ _ h.2 h.2

theorem product_polynomial {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    SharedPathPacked.product (coordinate K r.val) =
      (((probPoly K r.val)^2).eval (2^1024), ((firstPoly K r.val)^2).eval (2^1024)) := by
  rw [coordinate_polynomial val hβ K hK r hp]
  simp only [SharedPathPacked.product, Polynomial.eval_pow, probPoly, firstPoly]

theorem square_mass (a : Nat) (ha : a<2^384) : a^2*2048<2^1024 := by
  have h : a^2≤(2^384)^2 := Nat.pow_le_pow_left ha.le 2
  exact lt_of_le_of_lt (Nat.mul_le_mul_right 2048 h) (by decide +kernel)

theorem product_mass {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    ((probPoly K r.val)^2).eval 1*2048<2^1024 ∧
      ((firstPoly K r.val)^2).eval 1*2048<2^1024 := by
  have hm := coordinate_mass val hβ K hK r hp
  simpa only [Polynomial.eval_pow, probPoly, firstPoly] using
    And.intro (square_mass _ hm.1) (square_mass _ hm.2)

theorem product_size {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    (SharedPathPacked.product (coordinate K r.val)).1<(2^1024)^2048 ∧
      (SharedPathPacked.product (coordinate K r.val)).2<(2^1024)^2048 := by
  have hm := coordinate_size val hβ K hK r hp
  have hs (a : Nat) (ha : a<(2^1024)^1024) : a^2<(2^1024)^2048 := by
    have h := Nat.pow_lt_pow_left ha (by decide : 2≠0)
    simpa only [← pow_mul] using h
  exact ⟨hs _ hm.1,hs _ hm.2⟩

theorem split_product_size {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r t : Nat) (hr : r≤20) (ht : t≤r)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    (SharedPathPacked.product (coordinate 64 t)).1<(2^1024)^2048 ∧
    (SharedPathPacked.product (coordinate 64 t)).2<(2^1024)^2048 ∧
    (SharedPathPacked.product (coordinate 64 (r-t))).1<(2^1024)^2048 ∧
    (SharedPathPacked.product (coordinate 64 (r-t))).2<(2^1024)^2048 := by
  have h1 := product_size val hβ 64 (by simp) (⟨t,by omega⟩ : Fin 21) (hp t ht)
  have h2 := product_size val hβ 64 (by simp) (⟨r-t,by omega⟩ : Fin 21) (hp (r-t) (Nat.sub_le ..))
  exact ⟨h1.1,h1.2,h2.1,h2.2⟩

#print axioms branch_histogram
#print axioms product_polynomial
#print axioms product_mass
#print axioms product_size
#print axioms split_product_size
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem branch_coverage_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    {K r : Nat} (h : BranchHistory β K r) : branchCoverage val h≤(K*563)^2 := by
  exact (Nat.mul_le_mul (coordinate_coverage_le val hβ h.1)
    (coordinate_coverage_le val hβ h.2)).trans_eq (pow_two _).symm

theorem split_branch_mass {β : Type} [Fintype β]
    (hβ : Fintype.card β=563) (r t : Nat) (hr : r≤20) (ht : t≤r) :
    Fintype.card (BranchHistory β 64 t)*Fintype.card (BranchHistory β 64 (r-t))*
      ((64*563)^2+(64*563)^2)<2^1024 := by
  simp only [BranchHistory, Fintype.card_prod, coordinate_history_card hβ]
  have he : (64*563)^t*(64*563)^t*((64*563)^(r-t)*(64*563)^(r-t)) =
      ((64*563)^r)^2 := by
    calc
      _ = ((64*563)^t*(64*563)^(r-t))^2 := by ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le ht]
  rw [he]
  have hs : ((64*563)^r)^2*((64*563)^2+(64*563)^2) =
      ((64*563)^r*(64*563))^2*2 := by ring
  rw [hs]
  have hmass := coordinate_mass_small 64 r (by decide) hr
  have h := square_mass _ hmass
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (by decide : 2≤2048)) h

#print axioms split_branch_mass
end ClaudeWCT.Numerics.SharedPathCoordinate


namespace ClaudeWCT.Numerics.SharedPathList
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false

def runsCoverCheck : List (Nat × Nat × Nat) → Nat → Nat → Bool
  | [], start, finish => decide (start=finish)
  | e::es, start, finish => decide (e.1=start ∧ start≤e.2.1) &&
      runsCoverCheck es (e.2.1+1) finish

theorem runsCoverCheck_sound (runs : List (Nat × Nat × Nat)) (start finish d : Nat)
    (h : runsCoverCheck runs start finish=true) (hd : start≤d ∧ d<finish) :
    ∃ e ∈ runs, e.1≤d ∧ d≤e.2.1 := by
  induction runs generalizing start with
  | nil => simp only [runsCoverCheck, decide_eq_true_eq] at h; omega
  | cons e es ih =>
    simp only [runsCoverCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases he : d≤e.2.1
    · exact ⟨e,List.mem_cons_self,by omega,he⟩
    · obtain ⟨v,hv,hvd⟩ := ih (e.2.1+1) h.2 (by omega)
      exact ⟨v,List.mem_cons_of_mem _ hv,hvd⟩

theorem add_runs_contiguous : runsCoverCheck addRuns 0 2047=true := by decide +kernel

theorem add_runs_cover_checked (d : Fin 2047) : ∃ e : Fin addRuns.length,
    addRuns[e].1 ≤ d.val ∧ d.val ≤ addRuns[e].2.1 := by
  obtain ⟨v,hv,hd⟩ := runsCoverCheck_sound addRuns 0 2047 d.val
    add_runs_contiguous ⟨Nat.zero_le _,d.isLt⟩
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hv
  refine ⟨i,?_⟩
  simpa only [←hi, List.get_eq_getElem, Fin.getElem_fin] using hd

theorem mergeBin_interval_of_lt (i j : Nat) (hi : i<2047) (hj : j<2047) :
    (101/100 : ℝ)^(mergeBin i j)*(100/101) ≤ (101/100 : ℝ)^i+(101/100 : ℝ)^j ∧
      (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^(mergeBin i j) := by
  rcases le_total j i with hji|hij
  · obtain ⟨e,hlo,hhi⟩ := add_runs_cover_checked ⟨i-j,by omega⟩
    exact mergeBin_interval e i j hji hlo hhi
  · obtain ⟨e,hlo,hhi⟩ := add_runs_cover_checked ⟨j-i,by omega⟩
    have h := mergeBin_interval e j i hij hlo hhi
    simpa only [mergeBin_comm j i, add_comm] using h

theorem RoundedInterval.merge {a i j : Nat} {x y : ℝ}
    (hx : RoundedInterval a i x) (hy : RoundedInterval a j y)
    (hi : i<2047) (hj : j<2047) :
    RoundedInterval (a+1) (mergeBin i j) (x+y) := by
  have h := mergeBin_interval_of_lt i j hi hj
  exact hx.add hy h.1 h.2

#print axioms add_runs_cover_checked
#print axioms RoundedInterval.merge
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

noncomputable def reverseFeePoly (n : Nat) (f : Nat → Nat) : Nat[X] :=
  ∑ i ∈ range n, C (f i)*X^(n-1-i)

theorem reverseFeePoly_eval_one (n : Nat) (f : Nat → Nat) :
    (reverseFeePoly n f).eval 1=∑ i ∈ range n, f i := by
  simp only [reverseFeePoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]

theorem reverseFeePoly_dot (P : Nat[X]) (n : Nat) (f : Nat → Nat) :
    (P*reverseFeePoly n f).coeff (n-1)=∑ i ∈ range n, P.coeff i*f i := by
  simp only [reverseFeePoly, Finset.mul_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [←mul_assoc, Polynomial.coeff_mul_X_pow', if_pos (by omega),
    show n-1-(n-1-i)=i by omega, Polynomial.coeff_mul_C]

theorem packed_convolution_dot (P : Nat[X]) (B n : Nat) (f : Nat → Nat)
    (hB : 0<B) (hmass : P.eval 1*(∑ i ∈ range n, f i)<B) :
    (P.eval B*(reverseFeePoly n f).eval B/B^(n-1))%B =
      ∑ i ∈ range n, P.coeff i*f i := by
  have hc (i : Nat) : (P*reverseFeePoly n f).coeff i<B := by
    have h := ClaudeWCT.Numerics.N600.sum_coeff_le_eval_one (P*reverseFeePoly n f) {i}
    simp only [Finset.sum_singleton, Polynomial.eval_mul, reverseFeePoly_eval_one] at h
    exact h.trans_lt hmass
  rw [←Polynomial.eval_mul]
  exact (ClaudeWCT.Numerics.eval_div_pow_mod hB (n-1) (P*reverseFeePoly n f) hc).trans
    (reverseFeePoly_dot P n f)

#print axioms packed_convolution_dot
end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathCoordinate
open ClaudeWCT.Numerics.SharedPathPacked ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

noncomputable def splitGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (t u : Nat) (h : BranchHistory β 64 t × BranchHistory β 64 u) : Prop :=
  if t=0 then branchGood val h.2 else if u=0 then branchGood val h.1 else
    branchGood val h.1 ∧ branchGood val h.2
noncomputable def splitBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (t u : Nat) (h : BranchHistory β 64 t × BranchHistory β 64 u) : Nat :=
  if t=0 then branchBin val h.2 else if u=0 then branchBin val h.1 else
    mergeBin (branchBin val h.1) (branchBin val h.2)
noncomputable def splitWeight {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (t u : Nat) (h : BranchHistory β 64 t × BranchHistory β 64 u) : Nat :=
  branchCoverage val h.1+branchCoverage val h.2

def splitRow (r t : Nat) : Nat :=
  let a := SharedPathPacked.product (coordinate 64 t)
  let b := SharedPathPacked.product (coordinate 64 (r-t))
  if t=0 then b.2 else if r-t=0 then a.2 else addFirst a b

end ClaudeWCT.Numerics.SharedPathPair

namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathCoordinate ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

noncomputable def pairGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (h : PairHistory β r) : Prop :=
  splitGood val (occ h.1 0) (occ h.1 1)
    ((splitRanks h.1 h.2.1 0,splitRanks h.1 h.2.2 0),
     (splitRanks h.1 h.2.1 1,splitRanks h.1 h.2.2 1))
noncomputable def pairBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (h : PairHistory β r) : Nat :=
  splitBin val (occ h.1 0) (occ h.1 1)
    ((splitRanks h.1 h.2.1 0,splitRanks h.1 h.2.2 0),
     (splitRanks h.1 h.2.1 1,splitRanks h.1 h.2.2 1))

end ClaudeWCT.Numerics.SharedPathPair

namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathCoordinate
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

theorem coordinate_empty {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (K : Nat) (h : Fin 0 → Fin K×β) : coordinateCoverage val h=0 := by
  classical
  unfold coordinateCoverage
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp ha).2 (0 : Fin 6)
  exact Fin.elim0 i

theorem branch_empty {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (K : Nat) (h : BranchHistory β K 0) : branchCoverage val h=0 := by
  simp only [branchCoverage, coordinate_empty, Nat.zero_mul]

theorem coordinate_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (hr : 0<r) (h : Fin r → Fin K×β) (hg : coordinateGood val h) :
    RoundedInterval 1 (coordinateBin val h) (coordinateCoverage val h : ℝ) := by
  have hpos := coordinate_coverage_pos val hr h
  have hlen : coordinateCoverage val h≤11260 := by
    unfold coordinateGood at hg
    rw [binList_length] at hg
    omega
  have hb := bin_lookup_bounds bin_runs_checked bin_indices_checked
    (coordinateCoverage val h) (by omega) hlen
  have he : bins[coordinateCoverage val h]?.getD 0=coordinateBin val h := by
    simp only [bins, coordinateBin, binList, List.getElem?_toArray]
  rw [he] at hb
  have hi := geometric_bin_interval _ _ hb.1 hb.2
  exact ⟨by positivity,by simpa only [pow_one,mul_comm] using hi.1,hi.2⟩

theorem branch_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (hr : 0<r) (h : BranchHistory β K r) (hg : branchGood val h) :
    RoundedInterval 2 (branchBin val h) (branchCoverage val h : ℝ) := by
  have h1 := coordinate_interval val hr h.1 hg.1
  have h2 := coordinate_interval val hr h.2 hg.2
  simpa only [branchBin, branchCoverage, Nat.cast_mul] using h1.mul h2

theorem interval_weaken {a b i : Nat} {x : ℝ}
    (h : RoundedInterval a i x) (hab : a≤b) : RoundedInterval b i x := by
  refine ⟨h.nonneg,?_,h.upper⟩
  apply le_trans ?_ h.lower
  apply mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hab

theorem split_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (t u : Nat) (hpos : 0<t+u) (h : BranchHistory β 64 t × BranchHistory β 64 u)
    (hg : splitGood val t u h) :
    RoundedInterval 3 (splitBin val t u h) (splitWeight val t u h : ℝ) := by
  by_cases ht : t=0
  · subst t
    have hu : 0<u := by omega
    have hI := interval_weaken (branch_interval val hu h.2 (by simpa only [splitGood,ite_true] using hg)) (by decide : 2≤3)
    simpa only [splitBin,splitWeight,ite_true,branch_empty,Nat.zero_add] using hI
  · by_cases hu : u=0
    · subst u
      have ht' : 0<t := by omega
      have hI := interval_weaken (branch_interval val ht' h.1 (by simpa only [splitGood,if_neg ht,ite_true] using hg)) (by decide : 2≤3)
      simpa only [splitBin,splitWeight,if_neg ht,ite_true,branch_empty,Nat.add_zero] using hI
    · have hg' : branchGood val h.1 ∧ branchGood val h.2 := by
        simpa only [splitGood,if_neg ht,if_neg hu] using hg
      have h1 := branch_interval val (by omega : 0<t) h.1 hg'.1
      have h2 := branch_interval val (by omega : 0<u) h.2 hg'.2
      have hI := h1.merge h2 (branch_bin_bound val h.1 hg'.1) (branch_bin_bound val h.2 hg'.2)
      simpa only [splitBin,splitWeight,if_neg ht,if_neg hu,Nat.cast_add] using hI

theorem pair_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (hr : 0<r) (h : PairHistory β r) (hg : pairGood val h) :
    RoundedInterval 3 (pairBin val h) (pairCoverage val h : ℝ) := by
  have hs : occ h.1 0+occ h.1 1=r := by
    simpa only [Fin.sum_univ_two] using occ_sum h.1
  exact split_interval val _ _ (by omega)
    ((splitRanks h.1 h.2.1 0,splitRanks h.1 h.2.2 0),
     (splitRanks h.1 h.2.1 1,splitRanks h.1 h.2.2 1)) hg

#print axioms pair_interval
end ClaudeWCT.Numerics.SharedPathPair


namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathCoordinate
open ClaudeWCT.Numerics.SharedPathPacked ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

private theorem histogram_left_unique_lower {α β : Type} [Fintype α] [Unique α] [Fintype β]
    (g : β → Prop) (b w : β → Nat) (v : α → Nat) :
    CoeffLE (weightedHistogram g b w)
      (weightedHistogram (fun p : α×β => g p.2) (fun p => b p.2) (fun p => v p.1+w p.2)) := by
  classical
  intro j
  rw [weightedHistogram_coeff, weightedHistogram_coeff, Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  apply Finset.sum_le_sum
  intro a _
  split_ifs <;> omega

private theorem histogram_right_unique_lower {α β : Type} [Fintype α] [Fintype β] [Unique β]
    (g : α → Prop) (b w : α → Nat) (v : β → Nat) :
    CoeffLE (weightedHistogram g b w)
      (weightedHistogram (fun p : α×β => g p.1) (fun p => b p.1) (fun p => w p.1+v p.2)) := by
  classical
  intro j
  rw [weightedHistogram_coeff, weightedHistogram_coeff, Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  apply Finset.sum_le_sum
  intro a _
  split_ifs <;> omega

theorem product_first_digit {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K∈[64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) (j : Nat) :
    digit (2^1024) (SharedPathPacked.product (coordinate K r.val)).2 j =
      ((firstPoly K r.val)^2).coeff j := by
  rw [product_polynomial val hβ K hK r hp]
  exact ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j _ (fun i => by
    have h1 := (product_mass val hβ K hK r hp).2
    have h2 := polynomial_coeff_le_mass ((firstPoly K r.val)^2) i
    omega)

theorem split_row_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r t : Nat) (hr : r≤20) (ht : t≤r)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    splitRow r t<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024) (splitRow r t) j ≤
        (weightedHistogram (splitGood val t (r-t)) (splitBin val t (r-t))
          (splitWeight val t (r-t))).coeff j := by
  classical
  have hsize := split_product_size val hβ r t hr ht hp
  have ht' : t<21 := by omega
  have hu' : r-t<21 := by omega
  have hPt := branch_histogram val hβ 64 (by simp) (⟨t,ht'⟩ : Fin 21) (hp t ht)
  have hPu := branch_histogram val hβ 64 (by simp) (⟨r-t,hu'⟩ : Fin 21) (hp _ (Nat.sub_le ..))
  letI : Unique (BranchHistory β 64 0) := {
    default := (Fin.elim0, Fin.elim0)
    uniq := by intro x; apply Prod.ext <;> funext i <;> exact Fin.elim0 i }
  unfold splitGood splitBin splitWeight
  by_cases h0 : t=0
  · subst t
    simp only [splitRow, if_pos rfl, Nat.sub_zero, ite_true]
    refine ⟨hsize.2.2.2,?_⟩
    intro j hj
    rw [product_first_digit val hβ 64 (by simp) (⟨r,by omega⟩ : Fin 21) (hp r le_rfl)]
    apply (hPu.2 j).trans
    simpa only [splitGood, splitBin, splitWeight, if_pos rfl, Nat.sub_zero, ite_true] using
      histogram_left_unique_lower (α:=BranchHistory β 64 0)
        (branchGood (K:=64) (r:=r) val) (branchBin val) (branchCoverage val)
        (branchCoverage val) j
  · by_cases h1 : r-t=0
    · have htr : t=r := by omega
      subst t
      letI : Unique (BranchHistory β 64 (r-r)) := by
        simpa only [Nat.sub_self] using (inferInstance : Unique (BranchHistory β 64 0))
      simp only [splitRow, if_neg h0, Nat.sub_self, if_pos rfl, ite_true]
      refine ⟨hsize.2.1,?_⟩
      intro j hj
      rw [product_first_digit val hβ 64 (by simp) (⟨r,by omega⟩ : Fin 21) (hp r le_rfl)]
      apply (hPt.2 j).trans
      simpa only [splitGood, splitBin, splitWeight, if_neg h0, Nat.sub_self, if_pos rfl, ite_true] using
        histogram_right_unique_lower (β:=BranchHistory β 64 (r-r))
          (branchGood (K:=64) (r:=r) val) (branchBin val) (branchCoverage val)
          (branchCoverage val) j
    · have hmt := product_mass val hβ 64 (by simp) (⟨t,ht'⟩ : Fin 21) (hp t ht)
      have hmu := product_mass val hβ 64 (by simp) (⟨r-t,hu'⟩ : Fin 21) (hp _ (Nat.sub_le ..))
      have hEt := product_polynomial val hβ 64 (by simp) (⟨t,ht'⟩ : Fin 21) (hp t ht)
      have hEu := product_polynomial val hβ 64 (by simp) (⟨r-t,hu'⟩ : Fin 21) (hp _ (Nat.sub_le ..))
      rw [hEt,hEu] at hsize
      have h := addFirst_polynomial_histogram_lower
        (branchGood (K:=64) (r:=t) val) (branchGood (K:=64) (r:=r-t) val)
        (branchBin val) (branchCoverage val) (branchBin val) (branchCoverage val)
        ((probPoly 64 t)^2) ((firstPoly 64 t)^2) ((probPoly 64 (r-t))^2) ((firstPoly 64 (r-t))^2)
        ((64*563)^2) ((64*563)^2)
        hsize.1 hsize.2.1 hsize.2.2.1 hsize.2.2.2 hmt.1 hmt.2 hmu.1 hmu.2
        hPt.1 hPt.2 hPu.1 hPu.2
        (branch_coverage_le val hβ) (branch_coverage_le val hβ) (split_branch_mass hβ r t hr ht)
      simpa only [splitRow, if_neg h0, if_neg h1, hEt, hEu, splitGood, splitBin, splitWeight, ite_true] using h

#print axioms product_first_digit
#print axioms split_row_histogram
end ClaudeWCT.Numerics.SharedPathPair


namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathCoordinate ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

theorem pair_histogram_split {β : Type} [Fintype β] (val : β → Fin 6 → Nat) (r : Nat) :
    weightedHistogram (pairGood (r:=r) val) (pairBin val) (pairCoverage val) =
      ∑ t ∈ range (r+1), r.choose t • weightedHistogram (splitGood val t (r-t))
        (splitBin val t (r-t)) (splitWeight val t (r-t)) := by
  exact weightedHistogram_selector_split r
    (fun t u A B C D => splitGood val t u ((A,B),(C,D)))
    (fun t u A B C D => splitBin val t u ((A,B),(C,D)))
    (fun t u A B C D => splitWeight val t u ((A,B),(C,D)))

private theorem range_map_sum (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ t ∈ range n, f t := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton, ih, Finset.sum_range_succ]

theorem pairFirst_sum (r : Nat) :
    pairFirst r = ∑ t ∈ range (r+1), r.choose t * splitRow r t := by
  classical
  unfold pairFirst
  rw [foldl_weighted_sum, Nat.zero_add, range_map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have htr : t≤r := by have h := Finset.mem_range.mp ht; omega
  have ht' : t<r+1 := by omega
  have hu' : r-t<r+1 := by omega
  have get (u : Nat) (hu : u<r+1) :
      ((List.range (r+1)).map fun t => SharedPathPacked.product (coordinate 64 t)).getD u (0,0) =
        SharedPathPacked.product (coordinate 64 u) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hu)]
    simp only [List.getElem_map, List.getElem_range]
  rw [get t ht', get (r-t) hu']
  rw [PoissonReflect.fact_eq, PoissonReflect.fact_eq, PoissonReflect.fact_eq, ← Nat.choose_eq_factorial_div_factorial htr]
  rfl

private theorem eval_nsmul_nat (P : Nat[X]) (n B : Nat) :
    (n • P).eval B=n*P.eval B := by
  induction n with
  | zero => simp only [zero_nsmul,Polynomial.eval_zero,Nat.zero_mul]
  | succ n ih => rw [succ_nsmul,Polynomial.eval_add,ih,Nat.succ_mul]

private theorem coeff_nsmul_nat (P : Nat[X]) (n j : Nat) :
    (n • P).coeff j=n*P.coeff j := by
  induction n with
  | zero => simp only [zero_nsmul,Polynomial.coeff_zero,Nat.zero_mul]
  | succ n ih => rw [succ_nsmul,Polynomial.coeff_add,ih,Nat.succ_mul]

noncomputable def pairPoly (r : Nat) : Nat[X] :=
  ∑ t ∈ range (r+1), r.choose t • packedPoly (2^1024) 2048 (splitRow r t)

theorem pair_polynomial {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    (pairPoly r).eval (2^1024)=pairFirst r ∧
      CoeffLE (pairPoly r) (weightedHistogram (pairGood val) (pairBin val) (pairCoverage (r:=r) val)) := by
  classical
  constructor
  · rw [pairFirst_sum]
    unfold pairPoly
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [eval_nsmul_nat,
      packedPoly_eval _ _ _ (split_row_histogram val hβ r t hr (Nat.le_of_lt_succ (Finset.mem_range.mp ht)) hp).1]
  · rw [pair_histogram_split]
    intro j
    simp only [pairPoly, Polynomial.finsetSum_coeff, coeff_nsmul_nat]
    apply Finset.sum_le_sum
    intro t ht
    exact Nat.mul_le_mul_left _
      (packedPoly_below _ _ _ _ (split_row_histogram val hβ r t hr (Nat.le_of_lt_succ (Finset.mem_range.mp ht)) hp).2 j)

theorem pairFirst_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    pairFirst r<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024) (pairFirst r) j ≤
        (weightedHistogram (pairGood val) (pairBin val) (pairCoverage (r:=r) val)).coeff j := by
  classical
  have h := pair_polynomial val hβ r hr hp
  have hc (j : Nat) : (pairPoly r).coeff j<2^1024 := by
    apply histogram_lower_coeff_lt _ _ _ _ h.2 (2*(64*563)^2) _
    · intro a _
      exact pair_coverage_le val hβ a
    · rw [pair_history_card hβ]
      exact pair_mass_small r hr
  have hz (j : Nat) (hj : 2048≤j) : (pairPoly r).coeff j=0 := by
    simp only [pairPoly, Polynomial.finsetSum_coeff, coeff_nsmul_nat, packedPoly,
      polyOf_coeff, if_neg (by omega : ¬j<2048), Nat.mul_zero, Finset.sum_const_zero]
  rw [←h.1]
  refine ⟨polynomial_eval_lt _ _ _ (by positivity) (fun j _ => hc j) hz,?_⟩
  intro j hj
  rw [digit_polynomial_eval _ _ _ (by positivity) (fun i _ => hc i) hz j hj]
  exact h.2 j

#print axioms pair_histogram_split
#print axioms pairFirst_sum
#print axioms pairFirst_histogram
end ClaudeWCT.Numerics.SharedPathPair


namespace ClaudeWCT.Numerics.SharedPathForest
open Finset Polynomial ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false

noncomputable def encodedForestPoly (p q : Nat) : Nat[X] :=
  (packedPoly (2^1024) 2048 p)^4 * packedPoly (2^1024) 1024 q

theorem encodedForest_encoding (p q : Nat)
    (hp : p < (2^1024)^2048) (hq : q < (2^1024)^1024) :
    (SharedPathPacked.spread 11 p)^4*SharedPathPacked.spread 10 q =
      (encodedForestPoly p q).eval (2^4096) :=
  SharedPathPacked.forest_packed_polynomial p q hp hq

theorem encodedForest_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (r p q : Nat)
    (gp : PairHistory β r → Prop) [DecidablePred gp] (bp : PairHistory β r → Nat)
    (gq : (Fin r → Fin 128×β) → Prop) [DecidablePred gq]
    (bq : (Fin r → Fin 128×β) → Nat)
    (hp : ∀ j, j < 2048 → digit (2^1024) p j ≤
      (weightedHistogram gp bp (pairCoverage val)).coeff j)
    (hq : ∀ j, j < 1024 → digit (2^1024) q j ≤
      (weightedHistogram gq bq (coordinateCoverage val)).coeff j) :
    CoeffLE (encodedForestPoly p q)
      (weightedHistogram (fun h : ForestHistory β r => (∀ i, gp (h.1 i)) ∧ gq h.2)
        (fun h => (∑ i, bp (h.1 i))+bq h.2) (forestCoverage val)) := by
  exact forest_histogram_lower val r gp bp gq bq _ _
    (packedPoly_below _ _ _ _ hp) (packedPoly_below _ _ _ _ hq)


theorem forest_interval {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (r : Nat)
    (gp : PairHistory β r → Prop) (bp : PairHistory β r → Nat)
    (gq : (Fin r → Fin 128×β) → Prop) (bq : (Fin r → Fin 128×β) → Nat)
    (hp : ∀ h, gp h → RoundedInterval 3 (bp h) (pairCoverage val h : ℝ))
    (hq : ∀ h, gq h → RoundedInterval 1 (bq h) (coordinateCoverage val h : ℝ))
    (h : ForestHistory β r) (hg : (∀ i, gp (h.1 i)) ∧ gq h.2) :
    RoundedInterval 13 ((∑ i, bp (h.1 i))+bq h.2) (forestCoverage val h : ℝ) := by
  have hf := RoundedInterval.forest (fun i => bp (h.1 i))
    (fun i => (pairCoverage val (h.1 i) : ℝ)) (bq h.2) (coordinateCoverage val h.2 : ℝ)
    (fun i => hp _ (hg.1 i)) (hq _ hg.2)
  simpa only [forestCoverage, Nat.cast_mul, Nat.cast_prod] using hf

#print axioms encodedForest_histogram
#print axioms forest_interval
end ClaudeWCT.Numerics.SharedPathForest

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial ENNReal
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
attribute [local irreducible] feeRuns feeEntries fees scale

theorem ofReal_sum_nat_bound {α : Type} [Fintype α]
    (f : α → ℝ) (κ : ℝ) (A B : Nat) (hκ : 0 ≤ κ) (hB : 0 < B)
    (hf : ∀ a, 0 ≤ f a) (h : (∑ a, f a) ≤ κ/(B : ℝ)*(A : ℝ)) :
    (∑ a, ENNReal.ofReal (f a)) ≤ ENNReal.ofReal κ/(B : ENNReal)*(A : ENNReal) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hf a)]
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  calc
    _ ≤ ENNReal.ofReal (κ/(B : ℝ)*(A : ℝ)) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [ENNReal.ofReal_mul (div_nonneg hκ hBR.le), ENNReal.ofReal_div_of_pos hBR,
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]


end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedPathForest
open Finset Polynomial ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathCoordinate ClaudeWCT.Numerics.SharedPathPair
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

noncomputable def actualGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (h : ForestHistory β r) : Prop :=
  (∀ i, pairGood val (h.1 i)) ∧ coordinateGood val h.2
noncomputable def actualBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (h : ForestHistory β r) : Nat :=
  (∑ i, pairBin val (h.1 i))+coordinateBin val h.2
noncomputable def actualPoly (r : Nat) : Nat[X] :=
  encodedForestPoly (SharedPathPacked.pairFirst r) (coordinate 128 r).2

theorem coordinate_first_digit {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K∈[64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) (j : Nat) :
    digit (2^1024) (coordinate K r.val).2 j = (firstPoly K r.val).coeff j := by
  rw [coordinate_polynomial val hβ K hK r hp]
  exact ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j _ (fun i => by
    have h1 := (coordinate_mass val hβ K hK r hp).2
    have h2 := polynomial_coeff_le_mass (firstPoly K r.val) i
    have h3 : 2^384<2^1024 := by decide +kernel
    exact h2.trans_lt (h1.trans h3))

theorem coordinate_first_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K∈[64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    ∀ j, digit (2^1024) (coordinate K r.val).2 j ≤
      (weightedHistogram (coordinateGood val) (coordinateBin val) (coordinateCoverage (C:=Fin K) (r:=r.val) val)).coeff j := by
  intro j
  rw [coordinate_first_digit val hβ K hK r hp]
  exact (coordinate_histogram val hβ K hK r hp).2 j

theorem actual_encoding {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) :
    SharedPathPacked.forest r=(actualPoly r).eval (2^4096) := by
  exact encodedForest_encoding _ _ (pairFirst_histogram val hβ r hr (hp 64 (by simp))).1
    (coordinate_size val hβ 128 (by simp) ⟨r,by omega⟩ (hp 128 (by simp) r le_rfl)).2

theorem actual_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) :
    CoeffLE (actualPoly r) (weightedHistogram (actualGood val) (actualBin val) (forestCoverage (r:=r) val)) := by
  classical
  exact encodedForest_histogram val r _ _ (pairGood val) (pairBin val)
    (coordinateGood val) (coordinateBin val)
    (pairFirst_histogram val hβ r hr (hp 64 (by simp))).2
    (fun j _ => coordinate_first_histogram val hβ 128 (by simp) ⟨r,by omega⟩
      (hp 128 (by simp) r le_rfl) j)


theorem actual_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (hr : 0<r) (h : ForestHistory β r) (hg : actualGood val h) :
    RoundedInterval 13 (actualBin val h) (forestCoverage val h : ℝ) := by
  exact forest_interval val r (pairGood val) (pairBin val) (coordinateGood val) (coordinateBin val)
    (fun h hh => pair_interval val hr h hh) (fun h hh => coordinate_interval val hr h hh) h hg

#print axioms actual_encoding
#print axioms actual_histogram
#print axioms actual_interval
end ClaudeWCT.Numerics.SharedPathForest


namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell coordinate)
open ClaudeWCT.Numerics.SharedCoverage (foldl_weighted_sum)
open ClaudeWCT.Numerics.Kernel (fact)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false

def pairChunkWith (coord : Nat → Nat → Cell) (r start size : Nat) : Nat :=
  let branches := (List.range (r+1)).map fun t => product (coord 64 t)
  (List.range' start size).foldl (fun acc t =>
    let a := branches.getD t (0,0)
    let b := branches.getD (r-t) (0,0)
    let row := if t=0 then b.2 else if r-t=0 then a.2 else addFirst a b
    acc + fact r / (fact t * fact (r-t)) * row) 0

/-- `pairChunkWith` evaluated through `addFirstFast` (theorem `pairChunkWith_eq_fast`). -/
def pairChunkWithFast (coord : Nat → Nat → Cell) (r start size : Nat) : Nat :=
  let branches := (List.range (r+1)).map fun t => product (coord 64 t)
  (List.range' start size).foldl (fun acc t =>
    let a := branches.getD t (0,0)
    let b := branches.getD (r-t) (0,0)
    let row := if t=0 then b.2 else if r-t=0 then a.2 else addFirstFast a b
    acc + fact r / (fact t * fact (r-t)) * row) 0

theorem pairChunkWith_eq_fast : pairChunkWith = pairChunkWithFast := by
  funext coord r start size
  unfold pairChunkWith pairChunkWithFast
  rw [addFirst_eq_fast]


theorem pairFirst_eq_chunk (r : Nat) :
    pairFirst r = pairChunkWith coordinate r 0 (r+1) := by
  unfold pairFirst pairChunkWith
  rw [List.range_eq_range']


theorem pairChunkWith_congr (coord other : Nat → Nat → Cell) (r start size : Nat)
    (h : ∀ t, t ≤ r → coord 64 t = other 64 t) :
    pairChunkWith coord r start size = pairChunkWith other r start size := by
  have he : (List.range (r+1)).map (fun t => product (coord 64 t)) =
      (List.range (r+1)).map (fun t => product (other 64 t)) := by
    apply List.map_congr_left
    intro t ht
    rw [h t (by have := List.mem_range.mp ht; omega)]
  unfold pairChunkWith
  rw [he]

#print axioms pairChunkWith_congr
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell coordinate)
open ClaudeWCT.Numerics.SharedCoverage (foldl_weighted_sum)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem pairChunkWith_eq_singletons (coord : Nat → Nat → Cell) (r start size : Nat) :
    pairChunkWith coord r start size =
      ((List.range' start size).map (fun t => pairChunkWith coord r t 1)).sum := by
  unfold pairChunkWith
  simp only [foldl_weighted_sum, Nat.zero_add, List.range'_succ, List.range'_zero,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

theorem pairFirst_eq_singletons (coord : Nat → Nat → Cell) (r : Nat)
    (h : ∀ t, t ≤ r → coordinate 64 t = coord 64 t) :
    pairFirst r = ((List.range (r+1)).map (fun t => pairChunkWith coord r t 1)).sum := by
  rw [pairFirst_eq_chunk, pairChunkWith_congr coordinate coord r 0 (r+1) h,
    pairChunkWith_eq_singletons, ← List.range_eq_range']

#print axioms pairChunkWith_eq_singletons
#print axioms pairFirst_eq_singletons
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

def packTree (bits : Nat) : Nat → Nat → (Nat → Nat) → Nat
  | 0, start, f => f start
  | h+1, start, f =>
    packTree bits h start f + (packTree bits h (start+2^h) f <<< (bits*2^h))

theorem packTree_sum (bits h start : Nat) (f : Nat → Nat) :
    packTree bits h start f =
      ∑ i ∈ range (2^h), f (start+i)*(2^bits)^i := by
  induction h generalizing start with
  | zero => simp [packTree]
  | succ h ih =>
    rw [packTree, ih, ih, Nat.shiftLeft_eq, pow_mul]
    rw [show 2^(h+1)=2^h+2^h by omega]
    rw [Finset.sum_range_add]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_add]
    rw [Nat.add_assoc]
    ring

theorem packTree_reversed (bits h n : Nat) (f : Nat → Nat) (hn : n≤2^h) :
    packTree bits h 0 (fun i => if i<n then f (n-1-i) else 0) =
      (reverseFeePoly n f).eval (2^bits) := by
  rw [packTree_sum]
  simp only [Nat.zero_add, ite_mul, zero_mul]
  rw [← Finset.sum_range_add_sum_Ico _ hn]
  have hz : (∑ i ∈ Ico n (2^h), if i<n then f (n-1-i)*(2^bits)^i else 0)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (by have := (Finset.mem_Ico.mp hi).1; omega)]
  rw [hz, Nat.add_zero]
  have hs : (∑ i ∈ range n, if i<n then f (n-1-i)*(2^bits)^i else 0)=
      ∑ i ∈ range n, f (n-1-i)*(2^bits)^i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
  rw [hs, ← Finset.sum_range_reflect]
  simp only [reverseFeePoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i hi
  have hi := Finset.mem_range.mp hi
  congr 2
  omega

#print axioms packTree_sum
#print axioms packTree_reversed
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedPathForest
open Finset Polynomial SharedCoverage SharedMoments Thinning N600 SharedPathList
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem actual_mass_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) :
    (actualPoly r).eval 1≤alphabetSize^r*alphabetSize := by
  classical
  have hm := histogram_lower_mass_le (actualGood val) (actualBin val)
    (forestCoverage (r:=r) val) (actualPoly r) (actual_histogram val hβ r hr hp)
    alphabetSize (fun h _ => forest_coverage_le val hβ h)
  rwa [forest_history_card hβ r] at hm

#print axioms actual_mass_le
end ClaudeWCT.Numerics.SharedPathForest

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open ClaudeWCT.Numerics.SharedMoments
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
attribute [local irreducible] fees scale

def feeValue (which i : Nat) : Nat :=
  if which=0 then 1 else if which=1 then (fees[i]?.getD (0,0)).1 else (fees[i]?.getD (0,0)).2

def packedFee (which : Nat) : Nat :=
  packTree 4096 13 0 (fun i => if i < 7210 then feeValue which (7209-i) else 0)

def packedDot (p q : Nat) : Nat := ((p*q) >>> (4096*7209)) % 2^4096


theorem packedFee_model (which : Nat) :
    packedFee which = (reverseFeePoly 7210 (feeValue which)).eval (2^4096) := by
  exact packTree_reversed 4096 13 7210 (feeValue which) (by decide)

theorem convolution_shift (P : Nat[X]) (bits n : Nat) (f : Nat → Nat)
    (hmass : P.eval 1*(∑ i ∈ range n, f i) < 2^bits) :
    ((P.eval (2^bits)*(reverseFeePoly n f).eval (2^bits)) >>> (bits*(n-1))) % 2^bits =
      ∑ i ∈ range n, P.coeff i*f i := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul]
  exact packed_convolution_dot P (2^bits) n f (by positivity) hmass

theorem packedDot_fee (P : Nat[X]) (p which : Nat)
    (hp : p=P.eval (2^4096))
    (hmass : P.eval 1*(∑ i ∈ range 7210, feeValue which i) < 2^4096) :
    packedDot p (packedFee which) = ∑ i ∈ range 7210, P.coeff i*feeValue which i := by
  unfold packedDot
  rw [packedFee_model, hp]
  exact convolution_shift P 4096 7210 (feeValue which) hmass


end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open ClaudeWCT.Numerics.SharedMoments
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false


theorem forest_mass_3072 (r : Nat) (hr : r ≤ 20) :
    alphabetSize^r*alphabetSize ≤ 2^3072 := by
  have hp := Nat.pow_le_pow_right (n:=alphabetSize) (by decide : 0 < alphabetSize) hr
  exact (Nat.mul_le_mul_right _ hp).trans (by decide +kernel)


end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem packTree_congr (bits h a b : Nat) (f g : Nat → Nat)
    (hfg : ∀ i, i < 2^h → f (a+i)=g (b+i)) :
    packTree bits h a f=packTree bits h b g := by
  induction h generalizing a b with
  | zero => simpa [packTree] using hfg 0 (by decide)
  | succ h ih =>
    have hp : 2^(h+1)=2^h+2^h := by omega
    simp only [packTree]
    apply congrArg₂ Nat.add
    · apply ih
      intro i hi
      exact hfg i (by rw [hp]; omega)
    · apply congrArg (fun n => n <<< (bits*2^h))
      apply ih
      intro i hi
      simpa only [Nat.add_assoc] using hfg (2^h+i) (by rw [hp]; omega)

def packList (bits : Nat) : Nat → List Nat → Nat
  | 0, xs => xs.headD 0
  | h+1, xs =>
    packList bits h (xs.take (2^h)) + (packList bits h (xs.drop (2^h)) <<< (bits*2^h))

theorem packList_eq_tree (bits h : Nat) (xs : List Nat) :
    packList bits h xs=packTree bits h 0 (fun i => xs[i]?.getD 0) := by
  induction h generalizing xs with
  | zero => cases xs <;> rfl
  | succ h ih =>
    rw [packList, ih, ih]
    conv_rhs => rw [packTree]
    apply congrArg₂ Nat.add
    · apply packTree_congr
      intro i hi
      simp only [Nat.zero_add, List.getElem?_take_of_lt hi]
    · apply congrArg (fun n => n <<< (bits*2^h))
      apply packTree_congr
      intro i hi
      simp only [Nat.zero_add, List.getElem?_drop]

#print axioms packTree_congr
#print axioms packList_eq_tree
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

def feeVector (which : Nat) : List Nat :=
  feeEntries.map (fun e => if which=0 then 1 else if which=1 then e.2.1 else e.2.2)

def packedFeeVector (which : Nat) : Nat :=
  packList 4096 13 (feeVector which).reverse

theorem feeVector_length (which : Nat) (hl : feeEntries.length=7210) :
    (feeVector which).length=7210 := by simpa [feeVector] using hl

theorem feeVector_get (which i : Nat) (hl : feeEntries.length=7210) (hi : i < 7210) :
    (feeVector which)[i]?.getD 0=feeValue which i := by
  have h : i < feeEntries.length := by omega
  simp only [feeVector, feeValue, fees, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem h, Option.map_some, Option.getD_some]

theorem packedFeeVector_eq (which : Nat) (hl : feeEntries.length=7210) :
    packedFeeVector which=packedFee which := by
  rw [packedFeeVector, packList_eq_tree, packedFee]
  apply packTree_congr
  intro i hi
  simp only [Nat.zero_add]
  by_cases h : i < 7210
  · rw [List.getElem?_reverse (by rw [feeVector_length which hl]; exact h),
      feeVector_length which hl, if_pos h]
    exact feeVector_get which (7209-i) hl (by omega)
  · have hh : (feeVector which).reverse.length ≤ i := by
      rw [List.length_reverse, feeVector_length which hl]
      omega
    rw [List.getElem?_eq_none hh, if_neg h]
    rfl


#print axioms packedFeeVector_eq
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedGeneratedFeeVector
open Lean Elab Command
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

elab "fee_vector_numeral% " which:num : term =>
  return ClaudeWCT.Numerics.SharedGeneratedCoordinate.limbExpr (packedFeeVector which.getNat)

elab "certify_fee_vector " which:num cached:ident proof:ident : command => do
  elabCommand (← `(noncomputable def $cached : Nat := fee_vector_numeral% $which))
  elabCommand (← `(theorem $proof : packedFeeVector $which = $cached := by decide +kernel))

certify_fee_vector 0 MassFee mass_fee_checked
#print axioms mass_fee_checked
end ClaudeWCT.Numerics.SharedGeneratedFeeVector

namespace ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem feeEntries_length : feeEntries.length=7210 := by
  have h := congrArg List.length fee_indices
  simpa only [List.length_map, List.length_range] using h

theorem packedFee_0_checked : packedFee 0=MassFee :=
  (packedFeeVector_eq 0 feeEntries_length).symm.trans mass_fee_checked

#print axioms packedFee_0_checked
end ClaudeWCT.Numerics.SharedGeneratedFeeVector

namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem pairFirst_eq_cached_sum (coord : Nat → Nat → Cell) (chunks : Nat → Nat)
    (r : Nat)
    (hc : ∀ t, t ≤ r → ClaudeWCT.Numerics.SharedPathList.coordinate 64 t = coord 64 t)
    (hp : ∀ t, t ≤ r → pairChunkWith coord r t 1 = chunks t) :
    pairFirst r = ((List.range (r+1)).map chunks).sum := by
  calc
    pairFirst r = ((List.range (r+1)).map (fun t => pairChunkWith coord r t 1)).sum :=
      pairFirst_eq_singletons coord r hc
    _ = _ := congrArg List.sum (List.map_congr_left (fun t ht => hp t (by
      have := List.mem_range.mp ht
      omega)))

#print axioms pairFirst_eq_cached_sum
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open Lean Elab Command
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedPathList (Cell coordinate)
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def cachedCoordinate (_ r : Nat) : Cell :=
  match r with
  | 0 => Coordinate_64_0
  | 1 => Coordinate_64_1
  | 2 => Coordinate_64_2
  | 3 => Coordinate_64_3
  | 4 => Coordinate_64_4
  | 5 => Coordinate_64_5
  | 6 => Coordinate_64_6
  | 7 => Coordinate_64_7
  | 8 => Coordinate_64_8
  | 9 => Coordinate_64_9
  | 10 => Coordinate_64_10
  | 11 => Coordinate_64_11
  | 12 => Coordinate_64_12
  | 13 => Coordinate_64_13
  | 14 => Coordinate_64_14
  | 15 => Coordinate_64_15
  | 16 => Coordinate_64_16
  | 17 => Coordinate_64_17
  | 18 => Coordinate_64_18
  | _ => (0,0)

theorem cachedCoordinate_correct (r : Nat) (hr : r ≤ 18) :
    ClaudeWCT.Numerics.SharedPathList.coordinate 64 r = cachedCoordinate 64 r := by
  interval_cases r
  · exact coordinate_64_0_checked
  · exact coordinate_64_1_checked
  · exact coordinate_64_2_checked
  · exact coordinate_64_3_checked
  · exact coordinate_64_4_checked
  · exact coordinate_64_5_checked
  · exact coordinate_64_6_checked
  · exact coordinate_64_7_checked
  · exact coordinate_64_8_checked
  · exact coordinate_64_9_checked
  · exact coordinate_64_10_checked
  · exact coordinate_64_11_checked
  · exact coordinate_64_12_checked
  · exact coordinate_64_13_checked
  · exact coordinate_64_14_checked
  · exact coordinate_64_15_checked
  · exact coordinate_64_16_checked
  · exact coordinate_64_17_checked
  · exact coordinate_64_18_checked

/- The elaborator only proposes a numeral. The following theorem checks the
entire arithmetic expression in the kernel, independently of that proposal. -/
elab "pair_chunk_numeral% " r:num start:num size:num : term => do
  let mut coordinates : Array Cell := #[]
  for i in [:19] do
    let info ← getConstInfo ((s!"ClaudeWCT.Numerics.SharedGeneratedCoordinate.Coordinate_64_{i}").toName)
    let args := info.value!.getAppArgs
    match limbValue? args[2]!, limbValue? args[3]! with
    | some x, some y => coordinates := coordinates.push (x,y)
    | _, _ => throwError "coordinate cache {i} is not a pair of Nat literals"
  let value := pairChunkWithFast (fun _ n => coordinates[n]?.getD (0,0))
    r.getNat start.getNat size.getNat
  return limbExpr value

elab "certify_pair_chunk " r:num start:num size:num cached:ident proof:ident : command => do
  elabCommand (← `(noncomputable def $cached : Nat := pair_chunk_numeral% $r $start $size))
  elabCommand (← `(theorem $proof :
    pairChunkWith cachedCoordinate $r $start $size = $cached := by
      rw [pairChunkWith_eq_fast]; decide +kernel))

elab "pair_sum_numeral% " r:num : term => do
  let mut total := 0
  for i in [:r.getNat+1] do
    let info ← getConstInfo ((← getCurrNamespace) ++ Name.mkSimple s!"Pair_{r.getNat}_{i}")
    match limbValue? info.value! with
    | some n => total := total+n
    | none => throwError "pair chunk {i} is not a Nat literal"
  return limbExpr total

end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked

certify_pair_chunk 5 0 1 Pair_5_0 pair_5_0_checked
#print axioms pair_5_0_checked
certify_pair_chunk 5 1 1 Pair_5_1 pair_5_1_checked
#print axioms pair_5_1_checked
certify_pair_chunk 5 2 1 Pair_5_2 pair_5_2_checked
#print axioms pair_5_2_checked
certify_pair_chunk 5 3 1 Pair_5_3 pair_5_3_checked
#print axioms pair_5_3_checked
certify_pair_chunk 5 4 1 Pair_5_4 pair_5_4_checked
#print axioms pair_5_4_checked
certify_pair_chunk 5 5 1 Pair_5_5 pair_5_5_checked
#print axioms pair_5_5_checked

noncomputable def Pair_5 : Nat := pair_sum_numeral% 5

noncomputable def chunks_5 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_5_0
  | 1 => Pair_5_1
  | 2 => Pair_5_2
  | 3 => Pair_5_3
  | 4 => Pair_5_4
  | 5 => Pair_5_5
  | _ => 0

theorem chunks_5_checked (t : Nat) (ht : t ≤ 5) :
    pairChunkWith cachedCoordinate 5 t 1 = chunks_5 t := by
  interval_cases t
  · exact pair_5_0_checked
  · exact pair_5_1_checked
  · exact pair_5_2_checked
  · exact pair_5_3_checked
  · exact pair_5_4_checked
  · exact pair_5_5_checked

theorem pair_5_checked : pairFirst 5 = Pair_5 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_5 5
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_5_checked
  exact h.trans (by decide +kernel)
#print axioms pair_5_checked

certify_pair_chunk 6 0 1 Pair_6_0 pair_6_0_checked
#print axioms pair_6_0_checked
certify_pair_chunk 6 1 1 Pair_6_1 pair_6_1_checked
#print axioms pair_6_1_checked
certify_pair_chunk 6 2 1 Pair_6_2 pair_6_2_checked
#print axioms pair_6_2_checked
certify_pair_chunk 6 3 1 Pair_6_3 pair_6_3_checked
#print axioms pair_6_3_checked
certify_pair_chunk 6 4 1 Pair_6_4 pair_6_4_checked
#print axioms pair_6_4_checked
certify_pair_chunk 6 5 1 Pair_6_5 pair_6_5_checked
#print axioms pair_6_5_checked
certify_pair_chunk 6 6 1 Pair_6_6 pair_6_6_checked
#print axioms pair_6_6_checked

noncomputable def Pair_6 : Nat := pair_sum_numeral% 6

noncomputable def chunks_6 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_6_0
  | 1 => Pair_6_1
  | 2 => Pair_6_2
  | 3 => Pair_6_3
  | 4 => Pair_6_4
  | 5 => Pair_6_5
  | 6 => Pair_6_6
  | _ => 0

theorem chunks_6_checked (t : Nat) (ht : t ≤ 6) :
    pairChunkWith cachedCoordinate 6 t 1 = chunks_6 t := by
  interval_cases t
  · exact pair_6_0_checked
  · exact pair_6_1_checked
  · exact pair_6_2_checked
  · exact pair_6_3_checked
  · exact pair_6_4_checked
  · exact pair_6_5_checked
  · exact pair_6_6_checked

theorem pair_6_checked : pairFirst 6 = Pair_6 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_6 6
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_6_checked
  exact h.trans (by decide +kernel)
#print axioms pair_6_checked

certify_pair_chunk 7 0 1 Pair_7_0 pair_7_0_checked
#print axioms pair_7_0_checked
certify_pair_chunk 7 1 1 Pair_7_1 pair_7_1_checked
#print axioms pair_7_1_checked
certify_pair_chunk 7 2 1 Pair_7_2 pair_7_2_checked
#print axioms pair_7_2_checked
certify_pair_chunk 7 3 1 Pair_7_3 pair_7_3_checked
#print axioms pair_7_3_checked
certify_pair_chunk 7 4 1 Pair_7_4 pair_7_4_checked
#print axioms pair_7_4_checked
certify_pair_chunk 7 5 1 Pair_7_5 pair_7_5_checked
#print axioms pair_7_5_checked
certify_pair_chunk 7 6 1 Pair_7_6 pair_7_6_checked
#print axioms pair_7_6_checked
certify_pair_chunk 7 7 1 Pair_7_7 pair_7_7_checked
#print axioms pair_7_7_checked

noncomputable def Pair_7 : Nat := pair_sum_numeral% 7

noncomputable def chunks_7 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_7_0
  | 1 => Pair_7_1
  | 2 => Pair_7_2
  | 3 => Pair_7_3
  | 4 => Pair_7_4
  | 5 => Pair_7_5
  | 6 => Pair_7_6
  | 7 => Pair_7_7
  | _ => 0

theorem chunks_7_checked (t : Nat) (ht : t ≤ 7) :
    pairChunkWith cachedCoordinate 7 t 1 = chunks_7 t := by
  interval_cases t
  · exact pair_7_0_checked
  · exact pair_7_1_checked
  · exact pair_7_2_checked
  · exact pair_7_3_checked
  · exact pair_7_4_checked
  · exact pair_7_5_checked
  · exact pair_7_6_checked
  · exact pair_7_7_checked

theorem pair_7_checked : pairFirst 7 = Pair_7 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_7 7
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_7_checked
  exact h.trans (by decide +kernel)
#print axioms pair_7_checked

certify_pair_chunk 8 0 1 Pair_8_0 pair_8_0_checked
#print axioms pair_8_0_checked
certify_pair_chunk 8 1 1 Pair_8_1 pair_8_1_checked
#print axioms pair_8_1_checked
certify_pair_chunk 8 2 1 Pair_8_2 pair_8_2_checked
#print axioms pair_8_2_checked
certify_pair_chunk 8 3 1 Pair_8_3 pair_8_3_checked
#print axioms pair_8_3_checked
certify_pair_chunk 8 4 1 Pair_8_4 pair_8_4_checked
#print axioms pair_8_4_checked
certify_pair_chunk 8 5 1 Pair_8_5 pair_8_5_checked
#print axioms pair_8_5_checked
certify_pair_chunk 8 6 1 Pair_8_6 pair_8_6_checked
#print axioms pair_8_6_checked
certify_pair_chunk 8 7 1 Pair_8_7 pair_8_7_checked
#print axioms pair_8_7_checked
certify_pair_chunk 8 8 1 Pair_8_8 pair_8_8_checked
#print axioms pair_8_8_checked

noncomputable def Pair_8 : Nat := pair_sum_numeral% 8

noncomputable def chunks_8 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_8_0
  | 1 => Pair_8_1
  | 2 => Pair_8_2
  | 3 => Pair_8_3
  | 4 => Pair_8_4
  | 5 => Pair_8_5
  | 6 => Pair_8_6
  | 7 => Pair_8_7
  | 8 => Pair_8_8
  | _ => 0

theorem chunks_8_checked (t : Nat) (ht : t ≤ 8) :
    pairChunkWith cachedCoordinate 8 t 1 = chunks_8 t := by
  interval_cases t
  · exact pair_8_0_checked
  · exact pair_8_1_checked
  · exact pair_8_2_checked
  · exact pair_8_3_checked
  · exact pair_8_4_checked
  · exact pair_8_5_checked
  · exact pair_8_6_checked
  · exact pair_8_7_checked
  · exact pair_8_8_checked

theorem pair_8_checked : pairFirst 8 = Pair_8 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_8 8
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_8_checked
  exact h.trans (by decide +kernel)
#print axioms pair_8_checked

certify_pair_chunk 9 0 1 Pair_9_0 pair_9_0_checked
#print axioms pair_9_0_checked
certify_pair_chunk 9 1 1 Pair_9_1 pair_9_1_checked
#print axioms pair_9_1_checked
certify_pair_chunk 9 2 1 Pair_9_2 pair_9_2_checked
#print axioms pair_9_2_checked
certify_pair_chunk 9 3 1 Pair_9_3 pair_9_3_checked
#print axioms pair_9_3_checked
certify_pair_chunk 9 4 1 Pair_9_4 pair_9_4_checked
#print axioms pair_9_4_checked
certify_pair_chunk 9 5 1 Pair_9_5 pair_9_5_checked
#print axioms pair_9_5_checked
certify_pair_chunk 9 6 1 Pair_9_6 pair_9_6_checked
#print axioms pair_9_6_checked
certify_pair_chunk 9 7 1 Pair_9_7 pair_9_7_checked
#print axioms pair_9_7_checked
certify_pair_chunk 9 8 1 Pair_9_8 pair_9_8_checked
#print axioms pair_9_8_checked
certify_pair_chunk 9 9 1 Pair_9_9 pair_9_9_checked
#print axioms pair_9_9_checked

noncomputable def Pair_9 : Nat := pair_sum_numeral% 9

noncomputable def chunks_9 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_9_0
  | 1 => Pair_9_1
  | 2 => Pair_9_2
  | 3 => Pair_9_3
  | 4 => Pair_9_4
  | 5 => Pair_9_5
  | 6 => Pair_9_6
  | 7 => Pair_9_7
  | 8 => Pair_9_8
  | 9 => Pair_9_9
  | _ => 0

theorem chunks_9_checked (t : Nat) (ht : t ≤ 9) :
    pairChunkWith cachedCoordinate 9 t 1 = chunks_9 t := by
  interval_cases t
  · exact pair_9_0_checked
  · exact pair_9_1_checked
  · exact pair_9_2_checked
  · exact pair_9_3_checked
  · exact pair_9_4_checked
  · exact pair_9_5_checked
  · exact pair_9_6_checked
  · exact pair_9_7_checked
  · exact pair_9_8_checked
  · exact pair_9_9_checked

theorem pair_9_checked : pairFirst 9 = Pair_9 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_9 9
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_9_checked
  exact h.trans (by decide +kernel)
#print axioms pair_9_checked

certify_pair_chunk 10 0 1 Pair_10_0 pair_10_0_checked
#print axioms pair_10_0_checked
certify_pair_chunk 10 1 1 Pair_10_1 pair_10_1_checked
#print axioms pair_10_1_checked
certify_pair_chunk 10 2 1 Pair_10_2 pair_10_2_checked
#print axioms pair_10_2_checked
certify_pair_chunk 10 3 1 Pair_10_3 pair_10_3_checked
#print axioms pair_10_3_checked
certify_pair_chunk 10 4 1 Pair_10_4 pair_10_4_checked
#print axioms pair_10_4_checked
certify_pair_chunk 10 5 1 Pair_10_5 pair_10_5_checked
#print axioms pair_10_5_checked
certify_pair_chunk 10 6 1 Pair_10_6 pair_10_6_checked
#print axioms pair_10_6_checked
certify_pair_chunk 10 7 1 Pair_10_7 pair_10_7_checked
#print axioms pair_10_7_checked
certify_pair_chunk 10 8 1 Pair_10_8 pair_10_8_checked
#print axioms pair_10_8_checked
certify_pair_chunk 10 9 1 Pair_10_9 pair_10_9_checked
#print axioms pair_10_9_checked
certify_pair_chunk 10 10 1 Pair_10_10 pair_10_10_checked
#print axioms pair_10_10_checked

noncomputable def Pair_10 : Nat := pair_sum_numeral% 10

noncomputable def chunks_10 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_10_0
  | 1 => Pair_10_1
  | 2 => Pair_10_2
  | 3 => Pair_10_3
  | 4 => Pair_10_4
  | 5 => Pair_10_5
  | 6 => Pair_10_6
  | 7 => Pair_10_7
  | 8 => Pair_10_8
  | 9 => Pair_10_9
  | 10 => Pair_10_10
  | _ => 0

theorem chunks_10_checked (t : Nat) (ht : t ≤ 10) :
    pairChunkWith cachedCoordinate 10 t 1 = chunks_10 t := by
  interval_cases t
  · exact pair_10_0_checked
  · exact pair_10_1_checked
  · exact pair_10_2_checked
  · exact pair_10_3_checked
  · exact pair_10_4_checked
  · exact pair_10_5_checked
  · exact pair_10_6_checked
  · exact pair_10_7_checked
  · exact pair_10_8_checked
  · exact pair_10_9_checked
  · exact pair_10_10_checked

theorem pair_10_checked : pairFirst 10 = Pair_10 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_10 10
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_10_checked
  exact h.trans (by decide +kernel)
#print axioms pair_10_checked

certify_pair_chunk 11 0 1 Pair_11_0 pair_11_0_checked
#print axioms pair_11_0_checked
certify_pair_chunk 11 1 1 Pair_11_1 pair_11_1_checked
#print axioms pair_11_1_checked
certify_pair_chunk 11 2 1 Pair_11_2 pair_11_2_checked
#print axioms pair_11_2_checked
certify_pair_chunk 11 3 1 Pair_11_3 pair_11_3_checked
#print axioms pair_11_3_checked
certify_pair_chunk 11 4 1 Pair_11_4 pair_11_4_checked
#print axioms pair_11_4_checked
certify_pair_chunk 11 5 1 Pair_11_5 pair_11_5_checked
#print axioms pair_11_5_checked
certify_pair_chunk 11 6 1 Pair_11_6 pair_11_6_checked
#print axioms pair_11_6_checked
certify_pair_chunk 11 7 1 Pair_11_7 pair_11_7_checked
#print axioms pair_11_7_checked
certify_pair_chunk 11 8 1 Pair_11_8 pair_11_8_checked
#print axioms pair_11_8_checked
certify_pair_chunk 11 9 1 Pair_11_9 pair_11_9_checked
#print axioms pair_11_9_checked
certify_pair_chunk 11 10 1 Pair_11_10 pair_11_10_checked
#print axioms pair_11_10_checked
certify_pair_chunk 11 11 1 Pair_11_11 pair_11_11_checked
#print axioms pair_11_11_checked

noncomputable def Pair_11 : Nat := pair_sum_numeral% 11

noncomputable def chunks_11 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_11_0
  | 1 => Pair_11_1
  | 2 => Pair_11_2
  | 3 => Pair_11_3
  | 4 => Pair_11_4
  | 5 => Pair_11_5
  | 6 => Pair_11_6
  | 7 => Pair_11_7
  | 8 => Pair_11_8
  | 9 => Pair_11_9
  | 10 => Pair_11_10
  | 11 => Pair_11_11
  | _ => 0

theorem chunks_11_checked (t : Nat) (ht : t ≤ 11) :
    pairChunkWith cachedCoordinate 11 t 1 = chunks_11 t := by
  interval_cases t
  · exact pair_11_0_checked
  · exact pair_11_1_checked
  · exact pair_11_2_checked
  · exact pair_11_3_checked
  · exact pair_11_4_checked
  · exact pair_11_5_checked
  · exact pair_11_6_checked
  · exact pair_11_7_checked
  · exact pair_11_8_checked
  · exact pair_11_9_checked
  · exact pair_11_10_checked
  · exact pair_11_11_checked

theorem pair_11_checked : pairFirst 11 = Pair_11 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_11 11
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_11_checked
  exact h.trans (by decide +kernel)
#print axioms pair_11_checked

end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 12 0 1 Pair_12_0 pair_12_0_checked
#print axioms pair_12_0_checked
certify_pair_chunk 12 1 1 Pair_12_1 pair_12_1_checked
#print axioms pair_12_1_checked
certify_pair_chunk 12 2 1 Pair_12_2 pair_12_2_checked
#print axioms pair_12_2_checked
certify_pair_chunk 12 3 1 Pair_12_3 pair_12_3_checked
#print axioms pair_12_3_checked
certify_pair_chunk 12 4 1 Pair_12_4 pair_12_4_checked
#print axioms pair_12_4_checked
certify_pair_chunk 12 5 1 Pair_12_5 pair_12_5_checked
#print axioms pair_12_5_checked
certify_pair_chunk 12 6 1 Pair_12_6 pair_12_6_checked
#print axioms pair_12_6_checked
certify_pair_chunk 12 7 1 Pair_12_7 pair_12_7_checked
#print axioms pair_12_7_checked
certify_pair_chunk 12 8 1 Pair_12_8 pair_12_8_checked
#print axioms pair_12_8_checked
certify_pair_chunk 12 9 1 Pair_12_9 pair_12_9_checked
#print axioms pair_12_9_checked
certify_pair_chunk 12 10 1 Pair_12_10 pair_12_10_checked
#print axioms pair_12_10_checked
certify_pair_chunk 12 11 1 Pair_12_11 pair_12_11_checked
#print axioms pair_12_11_checked
certify_pair_chunk 12 12 1 Pair_12_12 pair_12_12_checked
#print axioms pair_12_12_checked

noncomputable def Pair_12 : Nat := pair_sum_numeral% 12

noncomputable def chunks_12 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_12_0
  | 1 => Pair_12_1
  | 2 => Pair_12_2
  | 3 => Pair_12_3
  | 4 => Pair_12_4
  | 5 => Pair_12_5
  | 6 => Pair_12_6
  | 7 => Pair_12_7
  | 8 => Pair_12_8
  | 9 => Pair_12_9
  | 10 => Pair_12_10
  | 11 => Pair_12_11
  | 12 => Pair_12_12
  | _ => 0

theorem chunks_12_checked (t : Nat) (ht : t ≤ 12) :
    pairChunkWith cachedCoordinate 12 t 1 = chunks_12 t := by
  interval_cases t
  · exact pair_12_0_checked
  · exact pair_12_1_checked
  · exact pair_12_2_checked
  · exact pair_12_3_checked
  · exact pair_12_4_checked
  · exact pair_12_5_checked
  · exact pair_12_6_checked
  · exact pair_12_7_checked
  · exact pair_12_8_checked
  · exact pair_12_9_checked
  · exact pair_12_10_checked
  · exact pair_12_11_checked
  · exact pair_12_12_checked

theorem pair_12_checked : pairFirst 12 = Pair_12 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_12 12
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_12_checked
  exact h.trans (by decide +kernel)
#print axioms pair_12_checked


end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem forest_eq_of_inputs (r p : Nat) (q : Cell)
    (hp : pairFirst r=p) (hq : ClaudeWCT.Numerics.SharedPathList.coordinate 128 r=q) :
    forest r=(spread 11 p)^4*spread 10 q.2 :=
  congrArg₂ (fun (x : Nat) (y : Cell) => (spread 11 x)^4*spread 10 y.2) hp hq

#print axioms forest_eq_of_inputs
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

elab "forest_numeral% " r:num : term => do
  let pInfo ← getConstInfo ((s!"ClaudeWCT.Numerics.SharedGeneratedPair.Pair_{r.getNat}").toName)
  let qInfo ← getConstInfo ((s!"ClaudeWCT.Numerics.SharedGeneratedCoordinate.Coordinate_128_{r.getNat}").toName)
  match limbValue? pInfo.value!, limbValue? qInfo.value!.getAppArgs[3]! with
  | some p, some q => return limbExpr ((spread 11 p)^4 * spread 10 q)
  | _, _ => throwError "forest inputs are not Nat literals"

noncomputable def Forest_5 : Nat := forest_numeral% 5

theorem forest_5_checked : forest 5=Forest_5 := by
  exact (forest_eq_of_inputs 5 Pair_5 Coordinate_128_5
    pair_5_checked coordinate_128_5_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_5_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_6 : Nat := forest_numeral% 6

theorem forest_6_checked : forest 6=Forest_6 := by
  exact (forest_eq_of_inputs 6 Pair_6 Coordinate_128_6
    pair_6_checked coordinate_128_6_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_6_checked


noncomputable def Forest_7 : Nat := forest_numeral% 7

theorem forest_7_checked : forest 7=Forest_7 := by
  exact (forest_eq_of_inputs 7 Pair_7 Coordinate_128_7
    pair_7_checked coordinate_128_7_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_7_checked


noncomputable def Forest_8 : Nat := forest_numeral% 8

theorem forest_8_checked : forest 8=Forest_8 := by
  exact (forest_eq_of_inputs 8 Pair_8 Coordinate_128_8
    pair_8_checked coordinate_128_8_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_8_checked


noncomputable def Forest_9 : Nat := forest_numeral% 9

theorem forest_9_checked : forest 9=Forest_9 := by
  exact (forest_eq_of_inputs 9 Pair_9 Coordinate_128_9
    pair_9_checked coordinate_128_9_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_9_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 13 0 1 Pair_13_0 pair_13_0_checked
#print axioms pair_13_0_checked
certify_pair_chunk 13 1 1 Pair_13_1 pair_13_1_checked
#print axioms pair_13_1_checked
certify_pair_chunk 13 2 1 Pair_13_2 pair_13_2_checked
#print axioms pair_13_2_checked
certify_pair_chunk 13 3 1 Pair_13_3 pair_13_3_checked
#print axioms pair_13_3_checked
certify_pair_chunk 13 4 1 Pair_13_4 pair_13_4_checked
#print axioms pair_13_4_checked
certify_pair_chunk 13 5 1 Pair_13_5 pair_13_5_checked
#print axioms pair_13_5_checked
certify_pair_chunk 13 6 1 Pair_13_6 pair_13_6_checked
#print axioms pair_13_6_checked
certify_pair_chunk 13 7 1 Pair_13_7 pair_13_7_checked
#print axioms pair_13_7_checked
certify_pair_chunk 13 8 1 Pair_13_8 pair_13_8_checked
#print axioms pair_13_8_checked
certify_pair_chunk 13 9 1 Pair_13_9 pair_13_9_checked
#print axioms pair_13_9_checked
certify_pair_chunk 13 10 1 Pair_13_10 pair_13_10_checked
#print axioms pair_13_10_checked
certify_pair_chunk 13 11 1 Pair_13_11 pair_13_11_checked
#print axioms pair_13_11_checked
certify_pair_chunk 13 12 1 Pair_13_12 pair_13_12_checked
#print axioms pair_13_12_checked
certify_pair_chunk 13 13 1 Pair_13_13 pair_13_13_checked
#print axioms pair_13_13_checked

noncomputable def Pair_13 : Nat := pair_sum_numeral% 13

noncomputable def chunks_13 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_13_0
  | 1 => Pair_13_1
  | 2 => Pair_13_2
  | 3 => Pair_13_3
  | 4 => Pair_13_4
  | 5 => Pair_13_5
  | 6 => Pair_13_6
  | 7 => Pair_13_7
  | 8 => Pair_13_8
  | 9 => Pair_13_9
  | 10 => Pair_13_10
  | 11 => Pair_13_11
  | 12 => Pair_13_12
  | 13 => Pair_13_13
  | _ => 0

theorem chunks_13_checked (t : Nat) (ht : t ≤ 13) :
    pairChunkWith cachedCoordinate 13 t 1 = chunks_13 t := by
  interval_cases t
  · exact pair_13_0_checked
  · exact pair_13_1_checked
  · exact pair_13_2_checked
  · exact pair_13_3_checked
  · exact pair_13_4_checked
  · exact pair_13_5_checked
  · exact pair_13_6_checked
  · exact pair_13_7_checked
  · exact pair_13_8_checked
  · exact pair_13_9_checked
  · exact pair_13_10_checked
  · exact pair_13_11_checked
  · exact pair_13_12_checked
  · exact pair_13_13_checked

theorem pair_13_checked : pairFirst 13 = Pair_13 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_13 13
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_13_checked
  exact h.trans (by decide +kernel)
#print axioms pair_13_checked


end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_10 : Nat := forest_numeral% 10

theorem forest_10_checked : forest 10=Forest_10 := by
  exact (forest_eq_of_inputs 10 Pair_10 Coordinate_128_10
    pair_10_checked coordinate_128_10_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_10_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_11 : Nat := forest_numeral% 11

theorem forest_11_checked : forest 11=Forest_11 := by
  exact (forest_eq_of_inputs 11 Pair_11 Coordinate_128_11
    pair_11_checked coordinate_128_11_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_11_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_12 : Nat := forest_numeral% 12

theorem forest_12_checked : forest 12=Forest_12 := by
  exact (forest_eq_of_inputs 12 Pair_12 Coordinate_128_12
    pair_12_checked coordinate_128_12_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_12_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_13 : Nat := forest_numeral% 13

theorem forest_13_checked : forest 13=Forest_13 := by
  exact (forest_eq_of_inputs 13 Pair_13 Coordinate_128_13
    pair_13_checked coordinate_128_13_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_13_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 14 0 1 Pair_14_0 pair_14_0_checked
#print axioms pair_14_0_checked
certify_pair_chunk 14 1 1 Pair_14_1 pair_14_1_checked
#print axioms pair_14_1_checked
certify_pair_chunk 14 2 1 Pair_14_2 pair_14_2_checked
#print axioms pair_14_2_checked
certify_pair_chunk 14 3 1 Pair_14_3 pair_14_3_checked
#print axioms pair_14_3_checked
certify_pair_chunk 14 4 1 Pair_14_4 pair_14_4_checked
#print axioms pair_14_4_checked
certify_pair_chunk 14 5 1 Pair_14_5 pair_14_5_checked
#print axioms pair_14_5_checked
certify_pair_chunk 14 6 1 Pair_14_6 pair_14_6_checked
#print axioms pair_14_6_checked
certify_pair_chunk 14 7 1 Pair_14_7 pair_14_7_checked
#print axioms pair_14_7_checked
certify_pair_chunk 14 8 1 Pair_14_8 pair_14_8_checked
#print axioms pair_14_8_checked
certify_pair_chunk 14 9 1 Pair_14_9 pair_14_9_checked
#print axioms pair_14_9_checked
certify_pair_chunk 14 10 1 Pair_14_10 pair_14_10_checked
#print axioms pair_14_10_checked
certify_pair_chunk 14 11 1 Pair_14_11 pair_14_11_checked
#print axioms pair_14_11_checked
certify_pair_chunk 14 12 1 Pair_14_12 pair_14_12_checked
#print axioms pair_14_12_checked
certify_pair_chunk 14 13 1 Pair_14_13 pair_14_13_checked
#print axioms pair_14_13_checked
certify_pair_chunk 14 14 1 Pair_14_14 pair_14_14_checked
#print axioms pair_14_14_checked

noncomputable def Pair_14 : Nat := pair_sum_numeral% 14

noncomputable def chunks_14 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_14_0
  | 1 => Pair_14_1
  | 2 => Pair_14_2
  | 3 => Pair_14_3
  | 4 => Pair_14_4
  | 5 => Pair_14_5
  | 6 => Pair_14_6
  | 7 => Pair_14_7
  | 8 => Pair_14_8
  | 9 => Pair_14_9
  | 10 => Pair_14_10
  | 11 => Pair_14_11
  | 12 => Pair_14_12
  | 13 => Pair_14_13
  | 14 => Pair_14_14
  | _ => 0

theorem chunks_14_checked (t : Nat) (ht : t ≤ 14) :
    pairChunkWith cachedCoordinate 14 t 1 = chunks_14 t := by
  interval_cases t
  · exact pair_14_0_checked
  · exact pair_14_1_checked
  · exact pair_14_2_checked
  · exact pair_14_3_checked
  · exact pair_14_4_checked
  · exact pair_14_5_checked
  · exact pair_14_6_checked
  · exact pair_14_7_checked
  · exact pair_14_8_checked
  · exact pair_14_9_checked
  · exact pair_14_10_checked
  · exact pair_14_11_checked
  · exact pair_14_12_checked
  · exact pair_14_13_checked
  · exact pair_14_14_checked

theorem pair_14_checked : pairFirst 14 = Pair_14 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_14 14
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_14_checked
  exact h.trans (by decide +kernel)
#print axioms pair_14_checked


end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_14 : Nat := forest_numeral% 14

theorem forest_14_checked : forest 14=Forest_14 := by
  exact (forest_eq_of_inputs 14 Pair_14 Coordinate_128_14
    pair_14_checked coordinate_128_14_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_14_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 15 0 1 Pair_15_0 pair_15_0_checked
#print axioms pair_15_0_checked
certify_pair_chunk 15 1 1 Pair_15_1 pair_15_1_checked
#print axioms pair_15_1_checked
certify_pair_chunk 15 2 1 Pair_15_2 pair_15_2_checked
#print axioms pair_15_2_checked
certify_pair_chunk 15 3 1 Pair_15_3 pair_15_3_checked
#print axioms pair_15_3_checked
certify_pair_chunk 15 4 1 Pair_15_4 pair_15_4_checked
#print axioms pair_15_4_checked
certify_pair_chunk 15 5 1 Pair_15_5 pair_15_5_checked
#print axioms pair_15_5_checked
certify_pair_chunk 15 6 1 Pair_15_6 pair_15_6_checked
#print axioms pair_15_6_checked
certify_pair_chunk 15 7 1 Pair_15_7 pair_15_7_checked
#print axioms pair_15_7_checked
certify_pair_chunk 15 8 1 Pair_15_8 pair_15_8_checked
#print axioms pair_15_8_checked
certify_pair_chunk 15 9 1 Pair_15_9 pair_15_9_checked
#print axioms pair_15_9_checked
certify_pair_chunk 15 10 1 Pair_15_10 pair_15_10_checked
#print axioms pair_15_10_checked
certify_pair_chunk 15 11 1 Pair_15_11 pair_15_11_checked
#print axioms pair_15_11_checked
certify_pair_chunk 15 12 1 Pair_15_12 pair_15_12_checked
#print axioms pair_15_12_checked
certify_pair_chunk 15 13 1 Pair_15_13 pair_15_13_checked
#print axioms pair_15_13_checked
certify_pair_chunk 15 14 1 Pair_15_14 pair_15_14_checked
#print axioms pair_15_14_checked
certify_pair_chunk 15 15 1 Pair_15_15 pair_15_15_checked
#print axioms pair_15_15_checked

noncomputable def Pair_15 : Nat := pair_sum_numeral% 15

noncomputable def chunks_15 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_15_0
  | 1 => Pair_15_1
  | 2 => Pair_15_2
  | 3 => Pair_15_3
  | 4 => Pair_15_4
  | 5 => Pair_15_5
  | 6 => Pair_15_6
  | 7 => Pair_15_7
  | 8 => Pair_15_8
  | 9 => Pair_15_9
  | 10 => Pair_15_10
  | 11 => Pair_15_11
  | 12 => Pair_15_12
  | 13 => Pair_15_13
  | 14 => Pair_15_14
  | 15 => Pair_15_15
  | _ => 0

theorem chunks_15_checked (t : Nat) (ht : t ≤ 15) :
    pairChunkWith cachedCoordinate 15 t 1 = chunks_15 t := by
  interval_cases t
  · exact pair_15_0_checked
  · exact pair_15_1_checked
  · exact pair_15_2_checked
  · exact pair_15_3_checked
  · exact pair_15_4_checked
  · exact pair_15_5_checked
  · exact pair_15_6_checked
  · exact pair_15_7_checked
  · exact pair_15_8_checked
  · exact pair_15_9_checked
  · exact pair_15_10_checked
  · exact pair_15_11_checked
  · exact pair_15_12_checked
  · exact pair_15_13_checked
  · exact pair_15_14_checked
  · exact pair_15_15_checked

theorem pair_15_checked : pairFirst 15 = Pair_15 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_15 15
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_15_checked
  exact h.trans (by decide +kernel)
#print axioms pair_15_checked


end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_15 : Nat := forest_numeral% 15

theorem forest_15_checked : forest 15=Forest_15 := by
  exact (forest_eq_of_inputs 15 Pair_15 Coordinate_128_15
    pair_15_checked coordinate_128_15_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_15_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 16 0 1 Pair_16_0 pair_16_0_checked
#print axioms pair_16_0_checked
certify_pair_chunk 16 1 1 Pair_16_1 pair_16_1_checked
#print axioms pair_16_1_checked
certify_pair_chunk 16 2 1 Pair_16_2 pair_16_2_checked
#print axioms pair_16_2_checked
certify_pair_chunk 16 3 1 Pair_16_3 pair_16_3_checked
#print axioms pair_16_3_checked
certify_pair_chunk 16 4 1 Pair_16_4 pair_16_4_checked
#print axioms pair_16_4_checked
certify_pair_chunk 16 5 1 Pair_16_5 pair_16_5_checked
#print axioms pair_16_5_checked
certify_pair_chunk 16 6 1 Pair_16_6 pair_16_6_checked
#print axioms pair_16_6_checked
certify_pair_chunk 16 7 1 Pair_16_7 pair_16_7_checked
#print axioms pair_16_7_checked
certify_pair_chunk 16 8 1 Pair_16_8 pair_16_8_checked
#print axioms pair_16_8_checked
certify_pair_chunk 16 9 1 Pair_16_9 pair_16_9_checked
#print axioms pair_16_9_checked
certify_pair_chunk 16 10 1 Pair_16_10 pair_16_10_checked
#print axioms pair_16_10_checked
certify_pair_chunk 16 11 1 Pair_16_11 pair_16_11_checked
#print axioms pair_16_11_checked
certify_pair_chunk 16 12 1 Pair_16_12 pair_16_12_checked
#print axioms pair_16_12_checked
certify_pair_chunk 16 13 1 Pair_16_13 pair_16_13_checked
#print axioms pair_16_13_checked
certify_pair_chunk 16 14 1 Pair_16_14 pair_16_14_checked
#print axioms pair_16_14_checked
certify_pair_chunk 16 15 1 Pair_16_15 pair_16_15_checked
#print axioms pair_16_15_checked
certify_pair_chunk 16 16 1 Pair_16_16 pair_16_16_checked
#print axioms pair_16_16_checked

noncomputable def Pair_16 : Nat := pair_sum_numeral% 16

noncomputable def chunks_16 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_16_0
  | 1 => Pair_16_1
  | 2 => Pair_16_2
  | 3 => Pair_16_3
  | 4 => Pair_16_4
  | 5 => Pair_16_5
  | 6 => Pair_16_6
  | 7 => Pair_16_7
  | 8 => Pair_16_8
  | 9 => Pair_16_9
  | 10 => Pair_16_10
  | 11 => Pair_16_11
  | 12 => Pair_16_12
  | 13 => Pair_16_13
  | 14 => Pair_16_14
  | 15 => Pair_16_15
  | 16 => Pair_16_16
  | _ => 0

theorem chunks_16_checked (t : Nat) (ht : t ≤ 16) :
    pairChunkWith cachedCoordinate 16 t 1 = chunks_16 t := by
  interval_cases t
  · exact pair_16_0_checked
  · exact pair_16_1_checked
  · exact pair_16_2_checked
  · exact pair_16_3_checked
  · exact pair_16_4_checked
  · exact pair_16_5_checked
  · exact pair_16_6_checked
  · exact pair_16_7_checked
  · exact pair_16_8_checked
  · exact pair_16_9_checked
  · exact pair_16_10_checked
  · exact pair_16_11_checked
  · exact pair_16_12_checked
  · exact pair_16_13_checked
  · exact pair_16_14_checked
  · exact pair_16_15_checked
  · exact pair_16_16_checked

theorem pair_16_checked : pairFirst 16 = Pair_16 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_16 16
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_16_checked
  exact h.trans (by decide +kernel)
#print axioms pair_16_checked


end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_16 : Nat := forest_numeral% 16

theorem forest_16_checked : forest 16=Forest_16 := by
  exact (forest_eq_of_inputs 16 Pair_16 Coordinate_128_16
    pair_16_checked coordinate_128_16_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_16_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 17 0 1 Pair_17_0 pair_17_0_checked
#print axioms pair_17_0_checked
certify_pair_chunk 17 1 1 Pair_17_1 pair_17_1_checked
#print axioms pair_17_1_checked
certify_pair_chunk 17 2 1 Pair_17_2 pair_17_2_checked
#print axioms pair_17_2_checked
certify_pair_chunk 17 3 1 Pair_17_3 pair_17_3_checked
#print axioms pair_17_3_checked
certify_pair_chunk 17 4 1 Pair_17_4 pair_17_4_checked
#print axioms pair_17_4_checked
certify_pair_chunk 17 5 1 Pair_17_5 pair_17_5_checked
#print axioms pair_17_5_checked
certify_pair_chunk 17 6 1 Pair_17_6 pair_17_6_checked
#print axioms pair_17_6_checked
certify_pair_chunk 17 7 1 Pair_17_7 pair_17_7_checked
#print axioms pair_17_7_checked
certify_pair_chunk 17 8 1 Pair_17_8 pair_17_8_checked
#print axioms pair_17_8_checked
certify_pair_chunk 17 9 1 Pair_17_9 pair_17_9_checked
#print axioms pair_17_9_checked
certify_pair_chunk 17 10 1 Pair_17_10 pair_17_10_checked
#print axioms pair_17_10_checked
certify_pair_chunk 17 11 1 Pair_17_11 pair_17_11_checked
#print axioms pair_17_11_checked
certify_pair_chunk 17 12 1 Pair_17_12 pair_17_12_checked
#print axioms pair_17_12_checked
certify_pair_chunk 17 13 1 Pair_17_13 pair_17_13_checked
#print axioms pair_17_13_checked
certify_pair_chunk 17 14 1 Pair_17_14 pair_17_14_checked
#print axioms pair_17_14_checked
certify_pair_chunk 17 15 1 Pair_17_15 pair_17_15_checked
#print axioms pair_17_15_checked
certify_pair_chunk 17 16 1 Pair_17_16 pair_17_16_checked
#print axioms pair_17_16_checked
certify_pair_chunk 17 17 1 Pair_17_17 pair_17_17_checked
#print axioms pair_17_17_checked

noncomputable def Pair_17 : Nat := pair_sum_numeral% 17

noncomputable def chunks_17 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_17_0
  | 1 => Pair_17_1
  | 2 => Pair_17_2
  | 3 => Pair_17_3
  | 4 => Pair_17_4
  | 5 => Pair_17_5
  | 6 => Pair_17_6
  | 7 => Pair_17_7
  | 8 => Pair_17_8
  | 9 => Pair_17_9
  | 10 => Pair_17_10
  | 11 => Pair_17_11
  | 12 => Pair_17_12
  | 13 => Pair_17_13
  | 14 => Pair_17_14
  | 15 => Pair_17_15
  | 16 => Pair_17_16
  | 17 => Pair_17_17
  | _ => 0

theorem chunks_17_checked (t : Nat) (ht : t ≤ 17) :
    pairChunkWith cachedCoordinate 17 t 1 = chunks_17 t := by
  interval_cases t
  · exact pair_17_0_checked
  · exact pair_17_1_checked
  · exact pair_17_2_checked
  · exact pair_17_3_checked
  · exact pair_17_4_checked
  · exact pair_17_5_checked
  · exact pair_17_6_checked
  · exact pair_17_7_checked
  · exact pair_17_8_checked
  · exact pair_17_9_checked
  · exact pair_17_10_checked
  · exact pair_17_11_checked
  · exact pair_17_12_checked
  · exact pair_17_13_checked
  · exact pair_17_14_checked
  · exact pair_17_15_checked
  · exact pair_17_16_checked
  · exact pair_17_17_checked

theorem pair_17_checked : pairFirst 17 = Pair_17 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_17 17
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_17_checked
  exact h.trans (by decide +kernel)
#print axioms pair_17_checked


end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_17 : Nat := forest_numeral% 17

theorem forest_17_checked : forest 17=Forest_17 := by
  exact (forest_eq_of_inputs 17 Pair_17 Coordinate_128_17
    pair_17_checked coordinate_128_17_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_17_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false
certify_pair_chunk 18 0 1 Pair_18_0 pair_18_0_checked
#print axioms pair_18_0_checked
certify_pair_chunk 18 1 1 Pair_18_1 pair_18_1_checked
#print axioms pair_18_1_checked
certify_pair_chunk 18 2 1 Pair_18_2 pair_18_2_checked
#print axioms pair_18_2_checked
certify_pair_chunk 18 3 1 Pair_18_3 pair_18_3_checked
#print axioms pair_18_3_checked
certify_pair_chunk 18 4 1 Pair_18_4 pair_18_4_checked
#print axioms pair_18_4_checked
certify_pair_chunk 18 5 1 Pair_18_5 pair_18_5_checked
#print axioms pair_18_5_checked
certify_pair_chunk 18 6 1 Pair_18_6 pair_18_6_checked
#print axioms pair_18_6_checked
certify_pair_chunk 18 7 1 Pair_18_7 pair_18_7_checked
#print axioms pair_18_7_checked
certify_pair_chunk 18 8 1 Pair_18_8 pair_18_8_checked
#print axioms pair_18_8_checked
certify_pair_chunk 18 9 1 Pair_18_9 pair_18_9_checked
#print axioms pair_18_9_checked
certify_pair_chunk 18 10 1 Pair_18_10 pair_18_10_checked
#print axioms pair_18_10_checked
certify_pair_chunk 18 11 1 Pair_18_11 pair_18_11_checked
#print axioms pair_18_11_checked
certify_pair_chunk 18 12 1 Pair_18_12 pair_18_12_checked
#print axioms pair_18_12_checked
certify_pair_chunk 18 13 1 Pair_18_13 pair_18_13_checked
#print axioms pair_18_13_checked
certify_pair_chunk 18 14 1 Pair_18_14 pair_18_14_checked
#print axioms pair_18_14_checked
certify_pair_chunk 18 15 1 Pair_18_15 pair_18_15_checked
#print axioms pair_18_15_checked
certify_pair_chunk 18 16 1 Pair_18_16 pair_18_16_checked
#print axioms pair_18_16_checked
certify_pair_chunk 18 17 1 Pair_18_17 pair_18_17_checked
#print axioms pair_18_17_checked
certify_pair_chunk 18 18 1 Pair_18_18 pair_18_18_checked
#print axioms pair_18_18_checked

noncomputable def Pair_18 : Nat := pair_sum_numeral% 18

noncomputable def chunks_18 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_18_0
  | 1 => Pair_18_1
  | 2 => Pair_18_2
  | 3 => Pair_18_3
  | 4 => Pair_18_4
  | 5 => Pair_18_5
  | 6 => Pair_18_6
  | 7 => Pair_18_7
  | 8 => Pair_18_8
  | 9 => Pair_18_9
  | 10 => Pair_18_10
  | 11 => Pair_18_11
  | 12 => Pair_18_12
  | 13 => Pair_18_13
  | 14 => Pair_18_14
  | 15 => Pair_18_15
  | 16 => Pair_18_16
  | 17 => Pair_18_17
  | 18 => Pair_18_18
  | _ => 0

theorem chunks_18_checked (t : Nat) (ht : t ≤ 18) :
    pairChunkWith cachedCoordinate 18 t 1 = chunks_18 t := by
  interval_cases t
  · exact pair_18_0_checked
  · exact pair_18_1_checked
  · exact pair_18_2_checked
  · exact pair_18_3_checked
  · exact pair_18_4_checked
  · exact pair_18_5_checked
  · exact pair_18_6_checked
  · exact pair_18_7_checked
  · exact pair_18_8_checked
  · exact pair_18_9_checked
  · exact pair_18_10_checked
  · exact pair_18_11_checked
  · exact pair_18_12_checked
  · exact pair_18_13_checked
  · exact pair_18_14_checked
  · exact pair_18_15_checked
  · exact pair_18_16_checked
  · exact pair_18_17_checked
  · exact pair_18_18_checked

theorem pair_18_checked : pairFirst 18 = Pair_18 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_18 18
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_18_checked
  exact h.trans (by decide +kernel)
#print axioms pair_18_checked


end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_18 : Nat := forest_numeral% 18

theorem forest_18_checked : forest 18=Forest_18 := by
  exact (forest_eq_of_inputs 18 Pair_18 Coordinate_128_18
    pair_18_checked coordinate_128_18_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_18_checked


end ClaudeWCT.Numerics.SharedGeneratedForest
