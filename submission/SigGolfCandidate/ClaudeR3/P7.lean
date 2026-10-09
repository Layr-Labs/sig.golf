import SigGolfCandidate.ClaudeR3.P6

namespace ClaudeR3.Diff
open Finset
open ClaudeR3.Poly
open ClaudeR3.KEval
open ClaudeR3.Tab (digit extCount Tab)

section
variable {R : Type*} [CommRing R]

def single (base j : ℕ) (x y : R) (a : ℕ × ℤ) : Sums R :=
  let α := (a.2 : R) * ((base : R) + dsumI a.1) ^ j
  ⟨α, α * rhoI a.1 x, α * rhoI a.1 y, α * rhoI a.1 x * rhoI a.1 y⟩

def nine (e f : ℕ) (x y : R) (P Q : Sums R) : R :=
  AI2 e f x * AI2 e f y * P.s0 * Q.s0 + AI2 e f x * y ^ e * P.s1y * Q.s0 + AI2 e f x * y ^ f * P.s0 * Q.s1y
    + x ^ e * AI2 e f y * P.s1x * Q.s0 + x ^ e * y ^ e * P.s2 * Q.s0 + x ^ e * y ^ f * P.s1x * Q.s1y
    + x ^ f * AI2 e f y * P.s0 * Q.s1x + x ^ f * y ^ e * P.s1y * Q.s1x + x ^ f * y ^ f * P.s0 * Q.s2

def addS (P Q : Sums R) : Sums R := ⟨P.s0 + Q.s0, P.s1x + Q.s1x, P.s1y + Q.s1y, P.s2 + Q.s2⟩
def zeroS : Sums R := ⟨0, 0, 0, 0⟩
def sumS (l : List (ℕ × ℤ)) (F : ℕ × ℤ → Sums R) : Sums R := (l.map F).foldr addS zeroS

theorem pointwise (k L e f : ℕ) (x : R) (a b : ℕ × ℤ) :
    (a.2 : R) * (b.2 : R) * lam3b k L e f a.1 b.1 x =
      ∑ j ∈ range (k + 1), (k.choose j : R) *
        nine e f x (x ^ L) (single 70938 j x (x ^ L) a) (single 0 (k - j) x (x ^ L) b) := by
  unfold lam3b
  rw [LamP2_eval_one, LamP2_eval, LamP2_eval]
  rw [show (70938 : R) + (dsumI a.1 : R) + (dsumI b.1 : R) = ((70938 : ℕ) : R) + (dsumI a.1 : R) + (dsumI b.1 : R) by
    norm_num, add_pow]
  simp only [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [nine, single, Nat.cast_zero, zero_add]
  ring

theorem nine_add_left (e f : ℕ) (x y : R) (P P' Q : Sums R) :
    nine e f x y (addS P P') Q = nine e f x y P Q + nine e f x y P' Q := by
  simp only [nine, addS]; ring

theorem nine_add_right (e f : ℕ) (x y : R) (P Q Q' : Sums R) :
    nine e f x y P (addS Q Q') = nine e f x y P Q + nine e f x y P Q' := by
  simp only [nine, addS]; ring

theorem nine_zero_left (e f : ℕ) (x y : R) (Q : Sums R) : nine e f x y zeroS Q = 0 := by
  simp only [nine, zeroS]; ring

theorem nine_zero_right (e f : ℕ) (x y : R) (P : Sums R) : nine e f x y P zeroS = 0 := by
  simp only [nine, zeroS]; ring

theorem nine_sum_right (e f : ℕ) (x y : R) (P : Sums R) (l : List (ℕ × ℤ)) (G : ℕ × ℤ → Sums R) :
    (l.map fun b => nine e f x y P (G b)).sum = nine e f x y P (sumS l G) := by
  induction l with
  | nil => simp [sumS, nine_zero_right]
  | cons b l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    show _ = nine e f x y P (addS (G b) (sumS l G))
    rw [nine_add_right]

theorem nine_sum_left (e f : ℕ) (x y : R) (Q : Sums R) (l : List (ℕ × ℤ)) (F : ℕ × ℤ → Sums R) :
    (l.map fun a => nine e f x y (F a) Q).sum = nine e f x y (sumS l F) Q := by
  induction l with
  | nil => simp [sumS, nine_zero_left]
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    show _ = nine e f x y (addS (F a) (sumS l F)) Q
    rw [nine_add_left]

def sumsB (tab : Tab) (base j : ℕ) (x y : R) : Sums R where
  s0 := (tab.map fun a => (a.2 : R) * ((base : R) + dsumI a.1) ^ j).sum
  s1x := (tab.map fun a => (a.2 : R) * ((base : R) + dsumI a.1) ^ j * rhoI a.1 x).sum
  s1y := rsum 15 fun l => y ^ l * (tab.map fun a => (a.2 : R) * ((base : R) + dsumI a.1) ^ j * (digit a.1 l : R)).sum
  s2 := rsum 15 fun l => y ^ l *
    (tab.map fun a => (a.2 : R) * ((base : R) + dsumI a.1) ^ j * (digit a.1 l : R) * rhoI a.1 x).sum

theorem sumS_s0 (l : List (ℕ × ℤ)) (F : ℕ × ℤ → Sums R) : (sumS l F).s0 = (l.map fun a => (F a).s0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sumS, addS] at ih ⊢; exact ih
theorem sumS_s1x (l : List (ℕ × ℤ)) (F : ℕ × ℤ → Sums R) : (sumS l F).s1x = (l.map fun a => (F a).s1x).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sumS, addS] at ih ⊢; exact ih
theorem sumS_s1y (l : List (ℕ × ℤ)) (F : ℕ × ℤ → Sums R) : (sumS l F).s1y = (l.map fun a => (F a).s1y).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sumS, addS] at ih ⊢; exact ih
theorem sumS_s2 (l : List (ℕ × ℤ)) (F : ℕ × ℤ → Sums R) : (sumS l F).s2 = (l.map fun a => (F a).s2).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sumS, addS] at ih ⊢; exact ih

theorem sumS_single (tab : Tab) (base j : ℕ) (x y : R) : sumS tab (single base j x y) = sumsB tab base j x y := by
  have e1 := sumS_s0 tab (single base j x y)
  have e2 := sumS_s1x tab (single base j x y)
  have e3 := sumS_s1y tab (single base j x y)
  have e4 := sumS_s2 tab (single base j x y)
  cases h : sumS tab (single base j x y) with
  | mk a0 a1 a2 a3 =>
    rw [h] at e1 e2 e3 e4
    simp only [single] at e1 e2 e3 e4
    simp only [sumsB, Sums.mk.injEq]
    refine ⟨e1, e2, ?_, ?_⟩
    · rw [e3, rsum_eq]
      simp_rw [rhoI_y _ y, mul_sum]
      rw [list_sum_finset]
      refine sum_congr rfl fun l _ => ?_
      rw [← list_sum_mul_left]
      exact congrArg List.sum (List.map_congr_left fun a _ => by ring)
    · rw [e4, rsum_eq]
      simp_rw [rhoI_y _ y, mul_sum]
      rw [list_sum_finset]
      refine sum_congr rfl fun l _ => ?_
      rw [← list_sum_mul_left]
      exact congrArg List.sum (List.map_congr_left fun a _ => by ring)

def famEvalD (tab : Tab) (k L : ℕ) (x : R) : R :=
  rsum (k + 1) fun j => (k.choose j : R) *
    (rsum 4 fun e => rsum 4 fun f => (nPair e f : R) *
      nine e f x (x ^ L) (sumsB tab 70938 j x (x ^ L)) (sumsB tab 0 (k - j) x (x ^ L)))

theorem Psi2_eval (k L key key' : ℕ) (x : R) :
    Psi2 k L key key' x = ∑ e ∈ range 4, ∑ f ∈ range 4, (nPair e f : R) * lam3b k L e f key key' x := by
  unfold Psi2
  rw [sum_child_pair (fun e f => lam3b k L e f key key' x)]

theorem pair_term (k L : ℕ) (x : R) (a b : ℕ × ℤ) :
    (a.2 : R) * ((b.2 : R) * Psi2 k L a.1 b.1 x) =
      ∑ j ∈ range (k + 1), (k.choose j : R) * ∑ e ∈ range 4, ∑ f ∈ range 4, (nPair e f : R) *
        nine e f x (x ^ L) (single 70938 j x (x ^ L) a) (single 0 (k - j) x (x ^ L) b) := by
  calc (a.2 : R) * ((b.2 : R) * Psi2 k L a.1 b.1 x)
      = ∑ e ∈ range 4, ∑ f ∈ range 4, (nPair e f : R) * ((a.2 : R) * (b.2 : R) * lam3b k L e f a.1 b.1 x) := by
        rw [Psi2_eval]; simp only [mul_sum]
        refine sum_congr rfl fun e _ => sum_congr rfl fun f _ => by ring
    _ = ∑ e ∈ range 4, ∑ f ∈ range 4, (nPair e f : R) * ∑ j ∈ range (k + 1), (k.choose j : R) *
          nine e f x (x ^ L) (single 70938 j x (x ^ L) a) (single 0 (k - j) x (x ^ L) b) := by
        simp only [pointwise]
    _ = _ := by
        simp only [mul_sum]
        simp_rw [Finset.sum_comm (s := range 4) (t := range (k + 1))]
        refine sum_congr rfl fun j _ => sum_congr rfl fun e _ => sum_congr rfl fun f _ => by ring

theorem famEvalD_eq (tab : Tab) (k L : ℕ) (x : R) :
    tabSum tab (fun key => tabSum tab (fun key' => Psi2 k L key key' x)) = famEvalD tab k L x := by
  set y := x ^ L
  have h1 : ∀ a : ℕ × ℤ, ((a.2 : ℤ) : R) * (tab.map fun b => ((b.2 : ℤ) : R) * Psi2 k L a.1 b.1 x).sum =
      ∑ j ∈ range (k + 1), (k.choose j : R) * ∑ e ∈ range 4, ∑ f ∈ range 4, (nPair e f : R) *
        (tab.map fun b => nine e f x y (single 70938 j x y a) (single 0 (k - j) x y b)).sum := by
    intro a
    rw [← list_sum_mul_left, List.map_congr_left (fun b _ => pair_term k L x a b), list_sum_finset]
    refine sum_congr rfl fun j _ => ?_
    rw [list_sum_mul_left, list_sum_finset]
    congr 1
    refine sum_congr rfl fun e _ => ?_
    rw [list_sum_finset]
    refine sum_congr rfl fun f _ => ?_
    rw [list_sum_mul_left]
  simp only [tabSum]
  rw [List.map_congr_left (fun a _ => h1 a), list_sum_finset, famEvalD, rsum_eq]
  refine sum_congr rfl fun j _ => ?_
  rw [list_sum_mul_left, list_sum_finset, rsum_eq]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  rw [list_sum_finset, rsum_eq]
  refine sum_congr rfl fun f _ => ?_
  rw [list_sum_mul_left]
  congr 1
  simp_rw [nine_sum_right]
  rw [nine_sum_left, sumS_single, sumS_single]

end

end ClaudeR3.Diff
