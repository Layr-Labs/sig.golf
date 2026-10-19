import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_ProducerDecodeV5
import SigGolfCandidate.T3_Gate6_ChildCounting
import SigGolfCandidate.T3_Nonbinary_Counting
import SigGolfCandidate.Research_V7Composed198Gate
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import SigGolfCandidate.ClaudeWCT_Numerics_N600PriceChecks
import SigGolfCandidate.ClaudeWCT_Numerics_N600Data
import Mathlib.Algebra.BigOperators.Ring.List
import SigGolfCandidate.ClaudeWCT_Numerics_PoissonReflect
import SigGolfCandidate.ClaudeWCT_Numerics_LawAverage



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
theorem theta_excess_le_square_54 (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 675 / 1000) :
    (5232 / 1000) * (value - 2031 / 1024) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 := by
  have hmf : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
  have hmr : mean.toReal ≤ 675 / 1000 := by
    have h := (ENNReal.toReal_le_toReal hmf (by finiteness)).mpr hmean
    simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using h
  have hm0 : 0 ≤ mean.toReal := ENNReal.toReal_nonneg
  by_cases hsmall : value ≤ 2031 / 1024
  · rw [tsub_eq_zero_of_le hsmall, mul_zero, zero_add]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_add,
      ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal)]
  · have hlarge : 2031 / 1024 ≤ value := le_of_not_ge hsmall
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hlarge hvalue, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal - 654 / 250)]
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
theorem law_price_excess_le_54 [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 563)
    (hC : Fintype.card C = 128) (h₁ : W1Table val) (h₂ : W2Table val) (hlaw : LawOK vc κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) vc) T (fun W => priceN val W - 2031 / 1024) ≤ 6117 / 10000000 := by
  set M := marked (α := Fin (2 ^ 31)) vc
  have hmean := law_price_mean_le val hT1 hT2 hβ hC h₁ hlaw
  have hsecond := law_price_second_le val hT1 hT2 hβ hC h₁ h₂ hlaw
  set mean := lawAvg M T (priceN val)
  have hm : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
  have h := lawAvg_mono M T (fun W : List (Fin (2 ^ 31) × (Fin 9 → C × β)) =>
    theta_excess_le_square_54 (priceN val W) mean (priceN_ne_top val W) hmean)
  rw [lawAvg_add, lawAvg_add, lawAvg_mul_left, lawAvg_mul_left,
    lawAvg_const M (marked_sum_one vc hlaw.sum_one) T] at h
  have hcancel : (5232 / 1000 : ENNReal) * lawAvg M T (fun W => priceN val W - 2031 / 1024) ≤ 3200 / 1000000 := by
    apply ENNReal.le_of_add_le_add_right (a := 2 * mean ^ 2) (by finiteness)
    calc
      _ = (5232 / 1000 : ENNReal) * lawAvg M T (fun W => priceN val W - 2031 / 1024) + 2 * mean * mean := by ring
      _ ≤ lawAvg M T (fun W => priceN val W ^ 2) + mean ^ 2 := h
      _ ≤ (mean ^ 2 + 3200 / 1000000) + mean ^ 2 := add_le_add hsecond le_rfl
      _ = _ := by ring
  have hi : (1000 / 5232 : ENNReal) * (5232 / 1000) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  calc
    _ = (1000 / 5232 : ENNReal) * ((5232 / 1000) * lawAvg M T (fun W => priceN val W - 2031 / 1024)) := by
        rw [← mul_assoc, hi, one_mul]
    _ ≤ (1000 / 5232 : ENNReal) * (3200 / 1000000) := mul_le_mul' le_rfl hcancel
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
theorem lawOK_uniform (hne : Fintype.card (Fin 9 → C × β) ≠ 0) :
    LawOK (fun _ : Fin 9 → C × β => (Fintype.card (Fin 9 → C × β) : ENNReal)⁻¹) 1 where
  sum_one := by
    rw [sum_const, card_univ, nsmul_eq_mul, ENNReal.mul_inv_cancel (by exact_mod_cast hne)
      (ENNReal.natCast_ne_top _)]
  density := fun _ => by rw [one_mul]
  one_le := le_rfl
  rate := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold LN LD; finiteness)).mp
    simp only [LN, LD]
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv]
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
theorem lawAvg_marked_uniform (T : ℕ) (f : List (Fin (2 ^ 31) × (Fin 9 → C × β)) → ENNReal) :
    lawAvg (marked (α := Fin (2 ^ 31)) (fun _ : Fin 9 → C × β => (Fintype.card (Fin 9 → C × β) : ENNReal)⁻¹)) T f =
      uniformWordAverage T f := by
  rw [← lawAvg_uniform]
  congr 1
  funext p
  simp only [marked, Fintype.card_prod]
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (ENNReal.natCast_ne_top _))]
theorem uniform_price_excess_le {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32)
    (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128) (h₁ : W1Table val) (h₂ : W2Table val) :
    uniformWordAverage T (fun W : List (Fin (2 ^ 31) × (Fin 9 → C × β)) => priceN val W - 1023 / 1024) ≤
      247 / 100000 := by
  rw [← lawAvg_marked_uniform]
  exact law_price_excess_le val hT1 hT2 hβ hC h₁ h₂ (lawOK_uniform (by simp [hβ, hC]))
theorem uniform_price_mean_le {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32)
    (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128) (h₁ : W1Table val) :
    uniformWordAverage T (priceN (C := C) val) ≤ 675 / 1000 := by
  rw [← lawAvg_marked_uniform]
  exact law_price_mean_le val hT1 hT2 hβ hC h₁ (lawOK_uniform (by simp [hβ, hC]))
theorem uniform_nearPrice_le {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32)
    (hβ : Fintype.card β = 563) (hC : Fintype.card C = 128) (h₁ : W1Table val) (hf : ∀ i, WFTable val i) :
    uniformWordAverage T (nearPriceN (C := C) val) ≤ 291 / 1 := by
  rw [← lawAvg_marked_uniform]
  exact law_nearPrice_le val hT1 hT2 hβ hC h₁ hf (lawOK_uniform (by simp [hβ, hC]))
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
/-- A retained subdistribution pays its bin-specific bound; omitted mass pays `M`. -/
theorem finite_retained_payoff_le {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (label : α → β) (weight fee : α → ℝ) (retained pay : β → ℝ) (M : ℝ)
    (hfee : ∀ a, fee a ≤ weight a * pay (label a))
    (hpay : ∀ b, pay b ≤ M)
    (hret : ∀ b, retained b ≤ ∑ a, if label a = b then weight a else 0) :
    ∑ a, fee a ≤ ∑ b, retained b * pay b + M * ((∑ a, weight a) - ∑ b, retained b) := by
  classical
  have hdisc : (∑ b, retained b * (M-pay b)) ≤
      ∑ a, weight a * (M-pay (label a)) := by
    calc
      _ ≤ ∑ b, (∑ a, if label a=b then weight a else 0) * (M-pay b) :=
        sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hret b) (sub_nonneg.mpr (hpay b))
      _ = _ := by
        simp_rw [sum_mul]
        rw [sum_comm]
        apply sum_congr rfl
        intro a _
        simp
  calc
    _ ≤ ∑ a, weight a * pay (label a) := sum_le_sum fun a _ => hfee a
    _ = M * (∑ a, weight a) - ∑ a, weight a * (M-pay (label a)) := by
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ M * (∑ a, weight a) - ∑ b, retained b * (M-pay b) := by linarith
    _ = _ := by
      simp_rw [mul_sub]
      rw [sum_sub_distrib, ← sum_mul]
      ring
end ClaudeWCT.Numerics.Winsor

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
/-- Combining bins preserves domination of a finite retained measure. -/
theorem retained_pushforward_le {α β γ : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [DecidableEq γ] (label : α → β) (group : β → γ)
    (weight : α → ℕ) (retained : β → ℕ)
    (hret : ∀ b, retained b ≤ ∑ a, if label a=b then weight a else 0) (c : γ) :
    (∑ b, if group b=c then retained b else 0) ≤
      ∑ a, if group (label a)=c then weight a else 0 := by
  classical
  calc
    _ ≤ ∑ b, if group b=c then ∑ a, if label a=b then weight a else 0 else 0 := by
      apply sum_le_sum
      intro b _
      split_ifs <;> first | exact hret b | exact le_rfl
    _ = _ := by
      simp_rw [ite_sum_zero]
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      have hh : ∀ b, (if group b=c then if label a=b then weight a else 0 else 0) =
          (if label a=b then if group b=c then weight a else 0 else 0) := by
        intro b
        split_ifs <;> rfl
      simp_rw [hh]
      simp
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
theorem coverageFastBinnedPack_eq (b r : ℕ) : coverageFastBinnedPack b r = coverageBinnedPack b r := by
  simp only [coverageFastBinnedPack, coverageRetainedFastPack_eq, coverageBinnedPack]
theorem coverageFastProductPack_eq (r : ℕ) : coverageFastProductPack r = coverageProductPack r := by
  simp only [coverageFastProductPack, coverageFastBinnedPack_eq, coverageProductPack]
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

theorem coverageCoefficientDots_mass_le (P : ℕ[X]) (ds : List (ℕ × ℕ)) :
    (coverageCoefficientDots P ds 0).1 ≤ P.eval 1 := by
  rw [coverageCoefficientDots_mass]
  simp only [Nat.zero_add]
  exact sum_coeff_le_eval_one P (range ds.length)

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

theorem bucketExpIncrement_ne_top (val : β → Fin 6 → ℕ) (L : List (Fin 9 → C × β)) :
    bucketExpIncrement val L ≠ ⊤ := by rw [bucketExpIncrement_real]; exact ENNReal.ofReal_ne_top

theorem bucketResidual_ne_top (val : β → Fin 6 → ℕ) (L : List (Fin 9 → C × β)) :
    bucketResidual val L ≠ ⊤ := by rw [bucketResidual_real]; exact ENNReal.ofReal_ne_top

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

theorem split_excess (price capped residual theta t : ℝ)
    (ht : 0 < t) (hr : 0 ≤ residual) (hsplit : price ≤ capped + residual) :
    max 0 (price - theta) ≤ residual + (3 / (8 * t)) *
      Real.exp (-t * theta) * Real.exp (t * capped) := by
  have h := positive_part_exp capped theta t ht
  apply max_le
  · positivity
  · have hc := le_max_right 0 (capped - theta)
    linarith

/-- A single capped exponential estimate closes both endpoints of the
continuous large-query envelope and the small-query bank threshold. -/
theorem endpoint_high :
    (3 / 48 : ℝ) * Real.exp (61 / 10 - 6 * (2 - 2 / 1250 - 1 / 1024)) +
      3 / 5000 ≤ 49 / 62500 := by
  let x : ℝ := 6 * (2 - 2 / 1250 - 1 / 1024) - 61 / 10
  have hx : (0 : ℝ) ≤ x := by norm_num [x]
  have he : (340 : ℝ) ≤ Real.exp x := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx 16)
    norm_num [x, Finset.sum_range_succ, Nat.factorial]
  have hi : (Real.exp x)⁻¹ ≤ (340 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) (by norm_num)).2 he
  have hn : 61 / 10 - 6 * (2 - 2 / 1250 - 1 / 1024) = -x := by dsimp [x]; ring
  rw [hn, Real.exp_neg]
  norm_num at hi ⊢
  linarith

theorem endpoint_small :
    (3 / 48 : ℝ) * Real.exp (61 / 10 - 6 * (249 / 125 - 1 / 1024)) +
      3 / 5000 ≤ 1 / 1000 := by
  let x : ℝ := 6 * (249 / 125 - 1 / 1024) - 61 / 10
  have hx : (0 : ℝ) ≤ x := by norm_num [x]
  have he : (200 : ℝ) ≤ Real.exp x := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx 16)
    norm_num [x, Finset.sum_range_succ, Nat.factorial]
  have hi : (Real.exp x)⁻¹ ≤ (200 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) (by norm_num)).2 he
  have hn : 61 / 10 - 6 * (249 / 125 - 1 / 1024) = -x := by dsimp [x]; ring
  rw [hn, Real.exp_neg]
  norm_num at hi ⊢
  linarith

theorem endpoint_low :
    (3 / 48 : ℝ) * Real.exp (61 / 10 - 6 * (1 - 1 / 1024)) +
      3 / 5000 ≤ 49 / 100 := by
  have hx : (61 / 10 - 6 * (1 - 1 / 1024) : ℝ) ≤ 1 := by norm_num
  have he := (Real.exp_le_exp.mpr hx).trans (le_of_lt Real.exp_one_lt_d9)
  nlinarith

#print axioms positive_part_exp
#print axioms split_excess
#print axioms endpoint_high
#print axioms endpoint_small
#print axioms endpoint_low
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

/-- Moment of a truncated rejection loop, given the success-weighted continuation. -/
noncomputable def retryMoment (z good bad : ℝ) : Nat → ℝ
  | 0 => 1
  | fuel + 1 => z * (good + bad * retryMoment z good bad fuel)

theorem retryMoment_le (z good bad value : ℝ) (hz : 0 ≤ z) (hbad : 0 ≤ bad)
    (hbase : 1 ≤ value) (hstep : z * (good + bad * value) ≤ value) :
    ∀ fuel, retryMoment z good bad fuel ≤ value := by
  intro fuel
  induction fuel with
  | zero => exact hbase
  | succ fuel ih =>
      exact (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hbad)) hz).trans hstep

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

#print axioms retryMoment_le
#print axioms transition_sound
end ClaudeWCT.Numerics.CanonicalCompression

namespace ClaudeWCT.Numerics.SharedPathWinsor.Canonical
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- A conservative scalar certificate for gate734/cap788. Its two moment
premises, at most6.87 and0.00075, still require a finite coverage proof. -/
theorem endpoint_middle :
    (3 / 48 : ℝ) * Real.exp (687 / 100 - 6 * (99847 / 50000 - 1 / 1024)) +
      3 / 4000 ≤ 23 / 20000 := by
  let x : ℝ := 6 * (99847 / 50000 - 1 / 1024) - 687 / 100
  have hx : (0 : ℝ) ≤ x := by norm_num [x]
  have he : (160 : ℝ) ≤ Real.exp x := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx 18)
    norm_num [x, Finset.sum_range_succ, Nat.factorial]
  have hi : (Real.exp x)⁻¹ ≤ (160 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) (by norm_num)).2 he
  have hn : 687 / 100 - 6 * (99847 / 50000 - 1 / 1024) = -x := by dsimp [x]; ring
  rw [hn, Real.exp_neg]
  norm_num at hi ⊢
  linarith

theorem endpoint_high :
    (3 / 48 : ℝ) * Real.exp (687 / 100 - 6 * (2 - 6 / 2500 - 1 / 1024)) +
      3 / 4000 ≤ 147 / 125000 := by
  have h := endpoint_middle
  have he := Real.exp_le_exp.mpr (show
      (687 / 100 - 6 * (2 - 6 / 2500 - 1 / 1024) : ℝ) ≤
        687 / 100 - 6 * (99847 / 50000 - 1 / 1024) by norm_num)
  linarith

theorem endpoint_low :
    (3 / 48 : ℝ) * Real.exp (687 / 100 - 6 * (1 - 1 / 1024)) +
      3 / 4000 ≤ 49 / 100 := by
  have hx : (687 / 100 - 6 * (1 - 1 / 1024) : ℝ) ≤ 1 := by norm_num
  have he := (Real.exp_le_exp.mpr hx).trans (le_of_lt Real.exp_one_lt_d9)
  nlinarith

#print axioms endpoint_middle
#print axioms endpoint_high
#print axioms endpoint_low
end ClaudeWCT.Numerics.SharedPathWinsor.Canonical

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

theorem capped_exp_ratio (t x cap pivot pay : ℝ)
    (ht : 0 ≤ t) (hx : 0 ≤ x) (hc : 0 < cap) (hp : 0 < pivot)
    (hpay : 0 ≤ pay)
    (hbelow : x ≤ cap → x ≤ pivot ∧ pivot ≤ cap)
    (habove : cap ≤ x → cap ≤ pivot ∧ pivot ≤ x)
    (hbound : Real.exp (t * min pivot cap) - 1 ≤ pivot * pay) :
    Real.exp (t * min x cap) - 1 ≤ x * pay := by
  by_cases hxc : x ≤ cap
  · rw [min_eq_left hxc]
    obtain ⟨hxp, hpc⟩ := hbelow hxc
    rw [min_eq_left hpc] at hbound
    have hs := exp_secant t x pivot hx hxp hp
    have hm := mul_le_mul_of_nonneg_left hbound (div_nonneg hx hp.le)
    have he : x / pivot * (pivot * pay) = x * pay := by field_simp
    rw [he] at hm
    exact hs.trans hm
  · have hcx : cap ≤ x := le_of_lt (lt_of_not_ge hxc)
    obtain ⟨hcp, hpx⟩ := habove hcx
    rw [min_eq_right hcx]
    rw [min_eq_right hcp] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right hpx hpay)
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
