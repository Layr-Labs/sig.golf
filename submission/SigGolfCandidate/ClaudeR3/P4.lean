import SigGolfCandidate.ClaudeR3.Q4
import SigGolfCandidate.ClaudeR3.P3
import SigGolfCandidate.ClaudeR3.P2

namespace ClaudeR3.Poly
open Finset
open ClaudeWCT.Numerics.N600
open ClaudeWCT.WCT9 (wordDigit routineCost childExtra Child Rank)
open ClaudeR3.Tab (lev keyU digit rhoU extCount sum_child tabM tabN tabS Tab)
open ClaudeR3.IE (CovAtM Alw)

abbrev Cell := Child × Rank

def sc (x : Cell) : ℕ := lev x.2 + childExtra x.1

theorem freeOk_none (u : Fin 6 → Fin 6) : FreeOk (fun _ => false) u := fun j hj => absurd hj (by simp)

theorem freeOk_single (i₀ : Fin 6) (u : Fin 6 → Fin 6) : FreeOk (fun j => decide (j = i₀)) u ↔ u i₀ = 5 := by
  unfold FreeOk
  constructor
  · intro h; exact h i₀ (by simp)
  · intro h j hj; simp at hj; subst hj; exact h

theorem lookup_gNear (u : Fin 6 → Fin 6) :
    lookup ClaudeR3.Tab.gNearT (digitsOf u) = M1 wordDigit u * #{j | u j = 5} := by
  unfold ClaudeR3.Tab.gNearT
  rw [lookup_zipT _ 6 _ _ _ ClaudeR3.Tab.full_g1T' (ClaudeR3.Tab.full_fourT 6 0)
    (digitsOf_length u), g1T_eq ClaudeR3.Tab.wordsOf_wordDigit' (fun x j => ClaudeR3.Tab.wordDigit_le4 x j),
    ClaudeR3.Tab.lookup_fourT 6 0 _ (digitsOf_length u) (digitsOf_le u), ClaudeR3.Tab.count_digitsOf', zero_add,
    Nat.mul_eq]

section
variable {R : Type*} [CommRing R]

def wt (k L : ℕ) (x : R) (m : Fin (k + 2)) (y : Cell) : R :=
  if (m : ℕ) = 0 then x ^ sc y else if (m : ℕ) = 1 then (x ^ L) ^ sc y else 1

def Rt (x : R) : R := ∑ b : Rank, x ^ lev b
def Et (x : R) : R := ∑ c : Child, x ^ childExtra c
def rhoK (key : ℕ) (x : R) : R := ∑ l ∈ range 15, (digit key l : R) * x ^ l
def LamP (e key : ℕ) (x : R) : R := (Et x - x ^ e) * Rt x + x ^ e * rhoK key x

def tabSum (tab : Tab) (Ψ : ℕ → R) : R := (tab.map fun e => ((e.2 : ℤ) : R) * Ψ e.1).sum

theorem rhoK_keyU (u : Fin 6 → Fin 6) (x : R) :
    rhoK (keyU u) x = ∑ b : Rank, if (∀ j, wordDigit b j < u j) then x ^ lev b else 0 := by
  have h := congrArg (Polynomial.eval₂ (Nat.castRingHom R) x) (ClaudeR3.Tab.rhoU_eq_digits u)
  unfold ClaudeR3.Tab.rhoU at h
  rw [Polynomial.eval₂_finset_sum, Polynomial.eval₂_finset_sum] at h
  unfold rhoK
  calc ∑ l ∈ range 15, (digit (keyU u) l : R) * x ^ l
      = ∑ l ∈ range 15, Polynomial.eval₂ (Nat.castRingHom R) x
          (Polynomial.C (digit (keyU u) l) * Polynomial.X ^ l) := by
        refine sum_congr rfl fun l _ => ?_
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, eq_natCast]
    _ = ∑ b : Rank, Polynomial.eval₂ (Nat.castRingHom R) x
          (if (∀ j, wordDigit b j < u j) then (Polynomial.X : Polynomial ℕ) ^ lev b else 0) := h.symm
    _ = ∑ b : Rank, if (∀ j, wordDigit b j < u j) then x ^ lev b else 0 := by
        refine sum_congr rfl fun b _ => ?_
        split_ifs <;> simp

theorem sum_X_sc (x : R) : ∑ y : Cell, x ^ sc y = Et x * Rt x := by
  unfold Et Rt
  rw [Fintype.sum_prod_type, sum_mul_sum]
  refine sum_congr rfl fun c _ => sum_congr rfl fun b _ => ?_
  unfold sc
  rw [pow_add, mul_comm]

theorem sum_X_sc_child (c : Child) (x : R) :
    ∑ y : Cell, (if y.1 = c then x ^ sc y else 0) = x ^ childExtra c * Rt x := by
  unfold Rt
  rw [Fintype.sum_prod_type, sum_comm, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  dsimp only
  rw [sum_ite_eq', if_pos (mem_univ c)]
  unfold sc
  rw [pow_add, mul_comm]

theorem sum_X_sc_childD (c : Child) (u : Fin 6 → Fin 6) (x : R) :
    ∑ y : Cell, (if y.1 = c ∧ (∀ j, wordDigit y.2 j < u j) then x ^ sc y else 0) =
      x ^ childExtra c * rhoK (keyU u) x := by
  rw [rhoK_keyU, Fintype.sum_prod_type, sum_comm, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  dsimp only
  simp_rw [ite_and]
  rw [sum_ite_eq', if_pos (mem_univ c)]
  split_ifs
  · unfold sc
    rw [pow_add, mul_comm]
  · rw [mul_zero]

theorem alw_split_X (c : Child) (u : Fin 6 → Fin 6) (x : R) (y : Cell) :
    (if Alw wordDigit c u y then x ^ sc y else 0) =
      x ^ sc y - (if y.1 = c then x ^ sc y else 0) +
        (if y.1 = c ∧ (∀ j, wordDigit y.2 j < u j) then x ^ sc y else 0) := by
  unfold Alw
  by_cases h1 : y.1 = c <;> by_cases h2 : ∀ j, wordDigit y.2 j < u j <;> simp [h1, h2]

theorem LamP_expand (e key : ℕ) (x : R) : LamP e key x = Et x * Rt x - x ^ e * Rt x + x ^ e * rhoK key x := by
  unfold LamP
  ring

theorem sum_alw_X (c : Child) (u : Fin 6 → Fin 6) (x : R) :
    ∑ y : Cell, (if Alw wordDigit c u y then x ^ sc y else 0) = LamP (childExtra c) (keyU u) x := by
  rw [sum_congr rfl fun y _ => alw_split_X c u x y, sum_add_distrib, sum_sub_distrib, sum_X_sc,
    sum_X_sc_child, sum_X_sc_childD, LamP_expand]

theorem sum_alw_one (c : Child) (u : Fin 6 → Fin 6) :
    ∑ y : Cell, (if Alw wordDigit c u y then (1 : R) else 0) = LamP (childExtra c) (keyU u) (1 : R) := by
  rw [← sum_alw_X]
  simp only [one_pow]

def lam3 (k L e key : ℕ) (x : R) : R := LamP e key x * LamP e key (x ^ L) * LamP e key 1 ^ k

theorem prod_wt_alw (k L : ℕ) (x : R) (c : Child) (u : Fin 6 → Fin 6) :
    ∏ m : Fin (k + 2), ∑ y : Cell, (if Alw wordDigit c u y then wt k L x m y else 0) =
      lam3 k L (childExtra c) (keyU u) x := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  have h0 : ∀ y : Cell, wt k L x 0 y = x ^ sc y := fun y => by simp [wt]
  have h1 : ∀ y : Cell, wt k L x (Fin.succ 0) y = (x ^ L) ^ sc y := fun y => by simp [wt]
  have h2 : ∀ (i : Fin k) (y : Cell), wt k L x i.succ.succ y = 1 := fun i y => by simp [wt]
  simp_rw [h0, h1, h2, sum_alw_X, sum_alw_one, prod_const, card_univ, Fintype.card_fin, lam3, mul_assoc]

def Psi (k L key : ℕ) (x : R) : R := ∑ c : Child, lam3 k L (childExtra c) key x

theorem key_mean_R (Ψ : ℕ → R) :
    ∑ u : Fin 6 → Fin 6, (((if parU u then (-1 : ℤ) else 1 : ℤ)) : R) *
        (((lookup g1T (digitsOf u) : ℕ) : R) * Ψ (lookup ClaudeR3.Tab.keyT (digitsOf u))) = tabSum tabM Ψ := by
  simpa only [zsmul_eq_mul, nsmul_eq_mul, tabSum] using ClaudeR3.Tab.key_mean (M := R) Ψ

theorem key_near_R (Ψ : ℕ → R) :
    ∑ u : Fin 6 → Fin 6, (((if parU u then (-1 : ℤ) else 1 : ℤ)) : R) *
        (((lookup ClaudeR3.Tab.gNearT (digitsOf u) : ℕ) : R) * Ψ (lookup ClaudeR3.Tab.keyT (digitsOf u))) =
      tabSum tabN Ψ := by
  simpa only [zsmul_eq_mul, nsmul_eq_mul, tabSum] using ClaudeR3.Tab.key_near (M := R) Ψ

theorem key_same_R (Ψ : ℕ → R) :
    ∑ u : Fin 6 → Fin 6, (((if parU u then (-1 : ℤ) else 1 : ℤ)) : R) *
        (((lookup g2T (digitsOf u) : ℕ) : R) * Ψ (lookup ClaudeR3.Tab.keyT (digitsOf u))) = tabSum tabS Ψ := by
  simpa only [zsmul_eq_mul, nsmul_eq_mul, tabSum] using ClaudeR3.Tab.key_same (M := R) Ψ

def Wm (k L : ℕ) (x : R) : R :=
  ∑ t : Cell, ∑ E : Fin (k + 2) → Cell,
    if CovAtM wordDigit (fun _ => false) t.1 (wordDigit t.2) E then ∏ m, wt k L x m (E m) else 0

theorem Wm_lattice (k L : ℕ) (x : R) :
    Wm k L x = ∑ u : Fin 6 → Fin 6, (((if parU u then (-1 : ℤ) else 1 : ℤ)) : R) *
      (((M1 wordDigit u : ℕ) : R) * Psi k L (keyU u) x) := by
  rw [Wm, Fintype.sum_prod_type]
  simp_rw [ClaudeR3.IE.sum_weighted_covAtM wordDigit (fun _ => false) _ ClaudeR3.Tab.wordDigit_le4 (wt k L x),
    prod_wt_alw, freeOk_none, if_true]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [Psi, mul_sum, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [sgnU_eq u]
  ring

theorem Wm_table (k L : ℕ) (x : R) : Wm k L x = tabSum tabM (fun key => Psi k L key x) := by
  rw [Wm_lattice, ← key_mean_R]
  refine sum_congr rfl fun u _ => ?_
  rw [g1T_eq ClaudeR3.Tab.wordsOf_wordDigit' (fun x j => ClaudeR3.Tab.wordDigit_le4 x j),
    ClaudeR3.Tab.lookup_keyT]

def Wn (k L : ℕ) (x : R) : R :=
  ∑ i₀ : Fin 6, ∑ t : Cell, ∑ E : Fin (k + 2) → Cell,
    if CovAtM wordDigit (fun j => decide (j = i₀)) t.1 (wordDigit t.2) E then ∏ m, wt k L x m (E m) else 0

theorem Wn_lattice (k L : ℕ) (x : R) :
    Wn k L x = ∑ u : Fin 6 → Fin 6, (((if parU u then (-1 : ℤ) else 1 : ℤ)) : R) *
      ((((M1 wordDigit u * #{j | u j = 5} : ℕ)) : R) * Psi k L (keyU u) x) := by
  rw [Wn]
  have h : ∀ i₀ : Fin 6, ∑ t : Cell, ∑ E : Fin (k + 2) → Cell,
      (if CovAtM wordDigit (fun j => decide (j = i₀)) t.1 (wordDigit t.2) E then ∏ m, wt k L x m (E m) else 0) =
      ∑ u : Fin 6 → Fin 6, (if u i₀ = 5 then (sgnU u : R) * (M1 wordDigit u : R) else 0) * Psi k L (keyU u) x := by
    intro i₀
    rw [Fintype.sum_prod_type]
    simp_rw [ClaudeR3.IE.sum_weighted_covAtM wordDigit (fun j => decide (j = i₀)) _ ClaudeR3.Tab.wordDigit_le4
      (wt k L x), prod_wt_alw, freeOk_single]
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [Psi, mul_sum]
  simp_rw [h]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [← sum_mul, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  rw [sgnU_eq u]
  push_cast
  ring

theorem Wn_table (k L : ℕ) (x : R) : Wn k L x = tabSum tabN (fun key => Psi k L key x) := by
  rw [Wn_lattice, ← key_near_R]
  refine sum_congr rfl fun u _ => ?_
  rw [lookup_gNear, ClaudeR3.Tab.lookup_keyT]

def Ws (k L : ℕ) (x : R) : R :=
  ∑ c : Child, ∑ ab : Rank × Rank, ∑ E : Fin (k + 2) → Cell,
    if CovAtM wordDigit (fun _ => false) c (wordDigit ab.1) E ∧ CovAtM wordDigit (fun _ => false) c (wordDigit ab.2) E
    then ∏ m, wt k L x m (E m) else 0

theorem Ws_table (k L : ℕ) (x : R) : Ws k L x = tabSum tabS (fun key => Psi k L key x) := by
  have hlat : Ws k L x = ∑ u : Fin 6 → Fin 6, (((if parU u then (-1 : ℤ) else 1 : ℤ)) : R) *
      (((M2 wordDigit u : ℕ) : R) * Psi k L (keyU u) x) := by
    rw [Ws]
    simp_rw [ClaudeR3.IE.sum_weighted_covAtM_pair wordDigit _ ClaudeR3.Tab.wordDigit_le4 (wt k L x), prod_wt_alw]
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [Psi, mul_sum, mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [sgnU_eq u]
    ring
  rw [hlat, ← key_same_R]
  refine sum_congr rfl fun u _ => ?_
  rw [g2T_eq ClaudeR3.Tab.wordsOf_wordDigit' (fun x j => ClaudeR3.Tab.wordDigit_le4 x j), ClaudeR3.Tab.lookup_keyT]

end

end ClaudeR3.Poly
