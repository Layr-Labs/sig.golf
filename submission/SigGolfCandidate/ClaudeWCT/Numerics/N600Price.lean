import SigGolfCandidate.ClaudeWCT.Numerics.N600Data
import Mathlib.Algebra.BigOperators.Ring.List
import SigGolfCandidate.ClaudeWCT.Numerics.PoissonReflect
import SigGolfCandidate.ClaudeWCT.Numerics.LawAverage

section


namespace ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Kernel (wpos wneg fact HB packPos packNeg)
def Nn : Nat := 600
def Kc : Nat := 128
def Q : Nat := 76800
def B1 : Nat := 76200
def B2 : Nat := 75600
def xNum (r : Nat) : Nat := wpos w1Data B1 r - wneg w1Data B1 r
def xfNum (t r : Nat) : Nat := wpos (wfData t) B1 r - wneg (wfData t) B1 r
def xfSum (r : Nat) : Nat := xfNum 0 r + xfNum 1 r + xfNum 2 r + xfNum 3 r + xfNum 4 r + xfNum 5 r + xfNum 6 r
def yPos (r : Nat) : Nat := wpos w2Data B1 r + (Kc - 1) * wpos wwData B2 r
def yNeg (r : Nat) : Nat := wneg w2Data B1 r + (Kc - 1) * wneg wwData B2 r
def yNum (r : Nat) : Nat := yPos r - yNeg r
def poissonCheckQ (Qv un ud ln ld : Nat) (f : Nat → Nat) (dbase sn sd Mn Md R : Nat) : Bool :=
  let S := (List.range (R + 1)).foldr (fun r s =>
    un * ln ^ r * ld ^ (R - r) * (fact R / fact r) * f r * Qv ^ (9 * (R - r)) + s) 0
  Md * sn * (S * ld * (R + 1) + ln ^ (R + 1) * ud * dbase * Qv ^ (9 * R)) ≤
    Mn * sd * ud * dbase * ld ^ (R + 1) * fact (R + 1) * Qv ^ (9 * R)
def A : Nat := 1137 * 2 ^ 8 * 2025 ^ 9
def LN : Nat := 2048795
def LD : Nat := 1000000
def MN : Nat := 3269
def MD : Nat := 10000
def DN : Nat := 20837
def DD : Nat := 50000000
def NN : Nat := 12855
def ND : Nat := 100
def meanCheck : Bool := poissonCheckQ Q 271 2000 LN LD (fun r => xNum r ^ 9) (Nn ^ 9) A 1 MN MD 80
def diagCheck : Bool :=
  poissonCheckQ Q 271 2000 LN LD (fun r => yNum r ^ 9) ((Kc * Nn ^ 2) ^ 9) (A ^ 2) (2 ^ 31) DN DD 80
def nearCheck : Bool :=
  poissonCheckQ Q 271 2000 LN LD (fun r => xNum r ^ 8 * xfSum r) (7 * Nn ^ 9) (63 * A) 1 NN ND 80
def convCheck : Bool :=
  Nat.beq (packPos w1Data ^ 2 + packNeg w1Data ^ 2 + packNeg wwData) (packPos wwData + 2 * packPos w1Data * packNeg w1Data)
end ClaudeWCT.Numerics.N600
end

section

namespace ClaudeWCT.Numerics.N600
theorem mean_ok : meanCheck = true := by decide +kernel
theorem near_ok : nearCheck = true := by decide +kernel
theorem diag_ok : diagCheck = true := by decide +kernel
theorem conv_ok : convCheck = true := by decide +kernel
end ClaudeWCT.Numerics.N600
end

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
theorem eval_one_w1_pos : (dataPoly w1Data false).eval 1 = 3500 := by
  rw [← packPos'_eq]; decide +kernel
theorem eval_one_w1_neg : (dataPoly w1Data true).eval 1 = 3500 := by
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
        3500 ^ 2 + 3500 ^ 2 + (dataPoly wwData true).eval 1 := by
      simp only [eval_add, eval_pow, e1, e2]
    have e3 := eval_one_ww_neg
    refine lt_of_eq_of_lt h ?_
    generalize (dataPoly wwData true).eval 1 = w at e3 ⊢
    omega
  have h2 : (dataPoly wwData false + 2 * dataPoly w1Data false * dataPoly w1Data true).eval 1 < 2 ^ 127 := by
    have h : (dataPoly wwData false + 2 * dataPoly w1Data false * dataPoly w1Data true).eval 1 =
        (dataPoly wwData false).eval 1 + 2 * 3500 * 3500 := by
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
def W1Table (val : β → Fin 7 → ℕ) : Prop :=
  ∀ p, (#{x : β × (Fin p → β) | CoversT val (val x.1) x.2} : ℤ) = (w1Data.map fun e => e.2 * (e.1 : ℤ) ^ p).sum
def W2Table (val : β → Fin 7 → ℕ) : Prop :=
  ∀ p, (#{x : β × β × (Fin p → β) | CoversT val (val x.1) x.2.2 ∧ CoversT val (val x.2.1) x.2.2} : ℤ) =
    (w2Data.map fun e => e.2 * (e.1 : ℤ) ^ p).sum
def WFTable (val : β → Fin 7 → ℕ) (i : Fin 7) : Prop :=
  ∀ p, (#{x : β × (Fin p → β) | CoversExcept val i (val x.1) x.2} : ℤ) =
    ((wfData i).map fun e => e.2 * (e.1 : ℤ) ^ p).sum
omit [DecidableEq C] in
theorem B1_eq (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128) :
    (((Fintype.card C - 1) * Fintype.card β : ℕ) : ℤ) = B1 := by
  rw [hβ, hC]; rfl
omit [DecidableEq C] in
theorem B2_eq (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128) :
    (((Fintype.card C - 2) * Fintype.card β : ℕ) : ℤ) = B2 := by
  rw [hβ, hC]; rfl
theorem coord_first_xNum (val : β → Fin 7 → ℕ) (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128)
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
theorem coord_second_yNum (val : β → Fin 7 → ℕ) (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128)
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
theorem coord_near_xfNum (val : β → Fin 7 → ℕ) (i : Fin 7) (hβ : Fintype.card β = 600)
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
theorem card_table (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128) :
    Fintype.card (Fin 9 → C × β) = Q ^ 9 := by
  simp only [Fintype.card_fun, Fintype.card_prod, hβ, hC, Fintype.card_fin]
  rfl
variable [SampleableType (Fin 9 → C × β)]
theorem env_moment (val : β → Fin 7 → ℕ) (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128)
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
theorem env_sq_moment (val : β → Fin 7 → ℕ) (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128)
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
theorem nearEnv_moment (val : β → Fin 7 → ℕ) (k₀ : Fin 9) (i₀ : Fin 7)
    (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128) (h₁ : W1Table val) (hf : WFTable val i₀)
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
open ClaudeWCT.Numerics.PoissonReflect (rejection_window rate_le_one)
noncomputable def priceScale : ENNReal := ((1137 * 2025 ^ 9 : ℕ) : ENNReal) / 2 ^ 23
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
  rate : ((2 ^ 32 + 2 ^ 23 : ℕ) : ENNReal) * (2 ^ 31 : ENNReal)⁻¹ * κ ≤ (LN : ENNReal) / LD
noncomputable def priceN (val : β → Fin 7 → ℕ) (W : List (Fin (2 ^ 31) × (Fin 9 → C × β))) : ENNReal :=
  priceScale * ∑ index : Fin (2 ^ 31), env (n := 9) val (atIndex index W)
noncomputable def nearPriceN (val : β → Fin 7 → ℕ) (W : List (Fin (2 ^ 31) × (Fin 9 → C × β))) : ENNReal :=
  priceScale * ∑ index : Fin (2 ^ 31), ∑ k : Fin 9, ∑ t : Fin 7, nearEnv val k t (atIndex index W)
variable (val : β → Fin 7 → ℕ) {vc : (Fin 9 → C × β) → ENNReal} {κ : ENNReal}
omit [DecidableEq C] in
theorem rate_window (hlaw : LawOK vc κ) {T : ℕ} (hT : T ≤ 2 ^ 32 + 2 ^ 23) :
    (T : ENNReal) * (2 ^ 31 : ENNReal)⁻¹ * κ ≤ (LN : ENNReal) / LD := by
  refine le_trans ?_ hlaw.rate
  gcongr
theorem card_index : (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹ = (2 ^ 31 : ENNReal)⁻¹ := by
  rw [Fintype.card_fin]; norm_num
theorem law_env_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128) (h₁ : W1Table val)
    (hlaw : LawOK vc κ) (r : ℕ) :
    lawAvg vc r (env (n := 9) (C := C) val) ≤ κ ^ r * (((xNum r ^ 9 : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  rw [← env_moment val hβ hC h₁ r]
  exact lawAvg_le_uniform vc κ hlaw.density r _
theorem law_env_le_one (hlaw : LawOK vc κ) (r : ℕ) : lawAvg vc r (env (n := 9) (C := C) val) ≤ 1 :=
  (lawAvg_mono vc r (env_le_one val)).trans_eq (lawAvg_const vc hlaw.sum_one r 1)
theorem law_env_sq_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128) (h₁ : W1Table val)
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
variable {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23)
include hT1 hT2
theorem law_price_mean_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128) (h₁ : W1Table val)
    (hlaw : LawOK vc κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) vc) T (priceN val) ≤ 3269 / 10000 := by
  rw [law_price_mean_eq val hlaw]
  have h := poissonCheckQ_sound_tilt (Qv := Q) (f := fun r => xNum r ^ 9) (dbase := Nn ^ 9) (sn := A) (sd := 1)
    (Mn := 3269) (Md := 10000) mean_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) rate_le_one κ hlaw.one_le (rate_window hlaw hT2) (rejection_window T hT1) _
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
theorem theta_excess_le_square_v5 (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 3269 / 10000) :
    (26299 / 10000) * (value - 63 / 64) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 := by
  have hmf : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
  have hmr : mean.toReal ≤ 3269 / 10000 := by
    have h := (ENNReal.toReal_le_toReal hmf (by finiteness)).mpr hmean
    simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using h
  have hm0 : 0 ≤ mean.toReal := ENNReal.toReal_nonneg
  by_cases hsmall : value ≤ 63 / 64
  · rw [tsub_eq_zero_of_le hsmall, mul_zero, zero_add]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_add,
      ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal)]
  · have hlarge : 63 / 64 ≤ value := le_of_not_ge hsmall
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hlarge hvalue, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal - 26299 / 20000)]
theorem priceN_ne_top (W : List (Fin (2 ^ 31) × (Fin 9 → C × β))) : priceN val W ≠ ⊤ := by
  unfold priceN
  exact ENNReal.mul_ne_top priceScale_ne_top
    (ENNReal.sum_ne_top.mpr fun index _ => ne_top_of_le_ne_top ENNReal.one_ne_top (env_le_one val _))
section Window2
variable {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23)
include hT1 hT2
theorem law_price_second_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 600)
    (hC : Fintype.card C = 128) (h₁ : W1Table val) (h₂ : W2Table val) (hlaw : LawOK vc κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) vc) T (fun W => priceN val W ^ 2) ≤
      lawAvg (marked (α := Fin (2 ^ 31)) vc) T (priceN val) ^ 2 + 20837 / 50000000 := by
  set M := marked (α := Fin (2 ^ 31)) vc
  have hsq := lawAvg_sum_square_le M T (fun index W => env (n := 9) (C := C) val (atIndex index W))
    (fun first second hne => law_marked_negative_correlation vc hlaw.sum_one first second hne T _ _
      (env_cons_le val) (env_cons_le val))
  have hmean : lawAvg M T (priceN val) =
      priceScale * ∑ index : Fin (2 ^ 31), lawAvg M T (fun W => env (n := 9) (C := C) val (atIndex index W)) := by
    unfold priceN; rw [lawAvg_mul_left, lawAvg_sum]
  have hcheck := poissonCheckQ_sound_tilt (Qv := Q) (f := fun r => yNum r ^ 9) (dbase := (Kc * Nn ^ 2) ^ 9)
    (sn := A ^ 2) (sd := 2 ^ 31) (Mn := 20837) (Md := 50000000) diag_ok (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rate_le_one κ hlaw.one_le (rate_window hlaw hT2) (rejection_window T hT1) _
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
theorem law_price_excess_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 600)
    (hC : Fintype.card C = 128) (h₁ : W1Table val) (h₂ : W2Table val) (hlaw : LawOK vc κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) vc) T (fun W => priceN val W - 63 / 64) ≤ 15847 / 100000000 := by
  set M := marked (α := Fin (2 ^ 31)) vc
  have hmean := law_price_mean_le val hT1 hT2 hβ hC h₁ hlaw
  have hsecond := law_price_second_le val hT1 hT2 hβ hC h₁ h₂ hlaw
  set mean := lawAvg M T (priceN val)
  have hm : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
  have h := lawAvg_mono M T (fun W : List (Fin (2 ^ 31) × (Fin 9 → C × β)) =>
    theta_excess_le_square_v5 (priceN val W) mean (priceN_ne_top val W) hmean)
  rw [lawAvg_add, lawAvg_add, lawAvg_mul_left, lawAvg_mul_left,
    lawAvg_const M (marked_sum_one vc hlaw.sum_one) T] at h
  have hcancel : (26299 / 10000 : ENNReal) * lawAvg M T (fun W => priceN val W - 63 / 64) ≤ 20837 / 50000000 := by
    apply ENNReal.le_of_add_le_add_right (a := 2 * mean ^ 2) (by finiteness)
    calc
      _ = (26299 / 10000 : ENNReal) * lawAvg M T (fun W => priceN val W - 63 / 64) + 2 * mean * mean := by ring
      _ ≤ lawAvg M T (fun W => priceN val W ^ 2) + mean ^ 2 := h
      _ ≤ (mean ^ 2 + 20837 / 50000000) + mean ^ 2 := add_le_add hsecond le_rfl
      _ = _ := by ring
  have hi : (10000 / 26299 : ENNReal) * (26299 / 10000) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  calc
    _ = (10000 / 26299 : ENNReal) * ((26299 / 10000) * lawAvg M T (fun W => priceN val W - 63 / 64)) := by
        rw [← mul_assoc, hi, one_mul]
    _ ≤ (10000 / 26299 : ENNReal) * (20837 / 50000000) := mul_le_mul' le_rfl hcancel
    _ ≤ _ := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
end Window2
theorem law_nearEnv_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128)
    (h₁ : W1Table val) (hf : ∀ i, WFTable val i) (hlaw : LawOK vc κ) (k : Fin 9) (t : Fin 7) (r : ℕ) :
    lawAvg vc r (nearEnv (C := C) val k t) ≤
      κ ^ r * (((xNum r ^ 8 * xfNum t r : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  rw [← nearEnv_moment val k t hβ hC h₁ (hf t) r]
  exact lawAvg_le_uniform vc κ hlaw.density r _
theorem xfSum_eq (r : ℕ) : xfSum r = ∑ t : Fin 7, xfNum t r := by
  rw [Fin.sum_univ_seven]; rfl
noncomputable def nearLoad (r : ℕ) : ENNReal :=
  (63 : ENNReal)⁻¹ * ∑ k : Fin 9, ∑ t : Fin 7, lawAvg vc r (nearEnv (C := C) val k t)
theorem nearLoad_le [SampleableType (Fin 9 → C × β)] (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128)
    (h₁ : W1Table val) (hf : ∀ i, WFTable val i) (hlaw : LawOK vc κ) (r : ℕ) :
    nearLoad val (vc := vc) r ≤
      κ ^ r * (((xNum r ^ 8 * xfSum r : ℕ) : ENNReal) / ((7 * Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  unfold nearLoad
  set D : ENNReal := ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)
  have hD0 : D ≠ 0 := by simp [D, Nn, Q]
  have hDt : D ≠ ⊤ := ENNReal.natCast_ne_top _
  calc (63 : ENNReal)⁻¹ * ∑ k : Fin 9, ∑ t : Fin 7, lawAvg vc r (nearEnv (C := C) val k t)
      ≤ (63 : ENNReal)⁻¹ * ∑ _k : Fin 9, ∑ t : Fin 7, κ ^ r * (((xNum r ^ 8 * xfNum t r : ℕ) : ENNReal) / D) :=
        mul_le_mul' le_rfl (sum_le_sum fun k _ => sum_le_sum fun t _ => law_nearEnv_le val hβ hC h₁ hf hlaw k t r)
    _ = κ ^ r * (((xNum r ^ 8 * xfSum r : ℕ) : ENNReal) / (7 * D)) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
        have h63 : (63 : ENNReal)⁻¹ * ((9 : ℕ) : ENNReal) = 7⁻¹ := by
          rw [show (63 : ENNReal) = 9 * 7 by norm_num, ENNReal.mul_inv (by simp) (by simp), Nat.cast_ofNat,
            mul_comm (9 : ENNReal)⁻¹, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
        rw [h63, xfSum_eq, show xNum r ^ 8 * ∑ t : Fin 7, xfNum t r = ∑ t : Fin 7, xNum r ^ 8 * xfNum t r from
          Finset.mul_sum _ _ _, Nat.cast_sum]
        simp only [div_eq_mul_inv]
        rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine sum_congr rfl fun t _ => ?_
        ring
    _ = _ := by simp only [D]; push_cast; ring_nf
theorem nearLoad_le_one (hlaw : LawOK vc κ) (r : ℕ) : nearLoad val (vc := vc) (C := C) r ≤ 1 := by
  unfold nearLoad
  calc (63 : ENNReal)⁻¹ * ∑ k : Fin 9, ∑ t : Fin 7, lawAvg vc r (nearEnv (C := C) val k t)
      ≤ (63 : ENNReal)⁻¹ * ∑ _k : Fin 9, ∑ _t : Fin 7, (1 : ENNReal) :=
        mul_le_mul' le_rfl (sum_le_sum fun k _ => sum_le_sum fun t _ =>
          (lawAvg_mono vc r (nearEnv_le_one val k t)).trans_eq (lawAvg_const vc hlaw.sum_one r 1))
    _ = 1 := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        rw [show ((9 : ℕ) : ENNReal) * (7 : ℕ) = 63 by norm_num, ENNReal.inv_mul_cancel (by simp) (by simp)]
theorem law_nearPrice_mean_eq (hlaw : LawOK vc κ) (T : ℕ) :
    lawAvg (marked (α := Fin (2 ^ 31)) vc) T (nearPriceN val) =
      63 * (A : ENNReal) * binomialAverage (2 ^ 31 : ENNReal)⁻¹ T (nearLoad val (vc := vc) (C := C)) := by
  unfold nearPriceN nearLoad
  rw [lawAvg_mul_left, lawAvg_sum]
  simp_rw [lawAvg_sum, law_marked_atIndex vc hlaw.sum_one, card_index]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← priceScale_mul,
    binomialAverage_mul_left]
  simp_rw [← SphincsSecurity.Concrete.binomialAverage_sum]
  have h : (63 : ENNReal) * 63⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [← mul_assoc, show (63 : ENNReal) * (priceScale * ((2 ^ 31 : ℕ) : ENNReal)) * 63⁻¹ =
    (63 * 63⁻¹) * (priceScale * ((2 ^ 31 : ℕ) : ENNReal)) by ring, h, one_mul]
theorem law_nearPrice_le [SampleableType (Fin 9 → C × β)] {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23)
    (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128) (h₁ : W1Table val) (hf : ∀ i, WFTable val i)
    (hlaw : LawOK vc κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) vc) T (nearPriceN val) ≤ 12855 / 100 := by
  rw [law_nearPrice_mean_eq val hlaw]
  have h := poissonCheckQ_sound_tilt (Qv := Q) (f := fun r => xNum r ^ 8 * xfSum r) (dbase := 7 * Nn ^ 9)
    (sn := 63 * A) (sd := 1) (Mn := 12855) (Md := 100) near_ok (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) rate_le_one κ hlaw.one_le (rate_window hlaw hT2) (rejection_window T hT1) _
    (fun r _ => (nearLoad_le val hβ hC h₁ hf hlaw r).trans_eq (by push_cast; ring_nf))
    (fun r _ => nearLoad_le_one val hlaw r)
  simpa only [Nat.cast_one, div_one, Nat.cast_ofNat, Nat.cast_mul] using h
theorem near_le_sub : (12855 / 100 : ENNReal) ≤ 131 - 1 / 16 := by
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
    (hrate : 10 ^ 6 * (2 ^ 32 + 2 ^ 23) * Fintype.card (Fin 9 → C × β) ≤ 2048795 * 2 ^ 31 * S.card) :
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
    have h : ((10 ^ 6 * (2 ^ 32 + 2 ^ 23) * Fintype.card (Fin 9 → C × β) : ℕ) : ℝ) ≤
        ((2048795 * 2 ^ 31 * S.card : ℕ) : ℝ) := by exact_mod_cast hrate
    push_cast at h ⊢
    set c : ℝ := (Fintype.card (Fin 9 → C × β) : ℝ)
    set t : ℝ := (S.card : ℝ)
    rw [show (4303355904 : ℝ) * (2 ^ 31)⁻¹ * (c / t) = (4303355904000000 * c) / (2147483648000000 * t) by
      field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    calc 4303355904000000 * c ≤ 4399753760604160 * t := h
      _ = 2048795 / 1000000 * (2147483648000000 * t) := by ring
theorem lawOK_uniformOn' (S : Finset (Fin 9 → C × β)) (hS : S.Nonempty) (Ncoords Ns : ℕ)
    (hcard : Fintype.card (Fin 9 → C × β) = Ncoords) (hNs : S.card = Ns)
    (hrate : 10 ^ 6 * (2 ^ 32 + 2 ^ 23) * Ncoords ≤ 2048795 * 2 ^ 31 * Ns) :
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
theorem uniform_price_excess_le {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23)
    (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128) (h₁ : W1Table val) (h₂ : W2Table val) :
    uniformWordAverage T (fun W : List (Fin (2 ^ 31) × (Fin 9 → C × β)) => priceN val W - 63 / 64) ≤
      15847 / 100000000 := by
  rw [← lawAvg_marked_uniform]
  exact law_price_excess_le val hT1 hT2 hβ hC h₁ h₂ (lawOK_uniform (by simp [hβ, hC]))
theorem uniform_price_mean_le {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23)
    (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128) (h₁ : W1Table val) :
    uniformWordAverage T (priceN (C := C) val) ≤ 3269 / 10000 := by
  rw [← lawAvg_marked_uniform]
  exact law_price_mean_le val hT1 hT2 hβ hC h₁ (lawOK_uniform (by simp [hβ, hC]))
theorem uniform_nearPrice_le {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23)
    (hβ : Fintype.card β = 600) (hC : Fintype.card C = 128) (h₁ : W1Table val) (hf : ∀ i, WFTable val i) :
    uniformWordAverage T (nearPriceN (C := C) val) ≤ 12855 / 100 := by
  rw [← lawAvg_marked_uniform]
  exact law_nearPrice_le val hT1 hT2 hβ hC h₁ hf (lawOK_uniform (by simp [hβ, hC]))
end Uniform
end Law
end ClaudeWCT.Numerics.N600
end
