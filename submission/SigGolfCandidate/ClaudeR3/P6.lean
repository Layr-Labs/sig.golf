import SigGolfCandidate.ClaudeR3.P5

namespace ClaudeR3.Diff
open Finset
open ClaudeR3.Poly
open ClaudeR3.KEval
open ClaudeR3.Tab (digit extCount levs sum_child lev keyU tabM Tab)
open ClaudeR3.IE (CovAtM Alw)
open ClaudeWCT.Numerics.N600
open ClaudeWCT.WCT9 (wordDigit childExtra Child Rank)

def nPair (e f : ℕ) : ℤ := (extCount e : ℤ) * extCount f - if e = f then (extCount e : ℤ) else 0

section
variable {R : Type*} [CommRing R]

theorem sum_child_pair (g : ℕ → ℕ → R) :
    ∑ c : Child, ∑ c' : Child, (if c = c' then (0 : R) else g (childExtra c) (childExtra c')) =
      ∑ e ∈ range 4, ∑ f ∈ range 4, (nPair e f : R) * g e f := by
  have h1 : ∀ c : Child, ∑ c' : Child, (if c = c' then (0 : R) else g (childExtra c) (childExtra c')) =
      ∑ c' : Child, g (childExtra c) (childExtra c') - g (childExtra c) (childExtra c) := by
    intro c
    rw [eq_sub_iff_add_eq, ← sum_erase_add _ _ (mem_univ c), if_pos rfl, add_zero,
      ← sum_erase_add (univ : Finset Child) _ (mem_univ c)]
    congr 1
    refine sum_congr rfl fun c' hc' => ?_
    rw [if_neg (Ne.symm (ne_of_mem_erase hc'))]
  simp_rw [h1]
  rw [sum_sub_distrib]
  have h2 : ∑ c : Child, ∑ c' : Child, g (childExtra c) (childExtra c') =
      ∑ e ∈ range 4, ∑ f ∈ range 4, ((extCount e : R) * extCount f) * g e f := by
    rw [sum_child (fun e => ∑ c' : Child, g e (childExtra c'))]
    refine sum_congr rfl fun e _ => ?_
    rw [sum_child (fun f => g e f), nsmul_eq_mul, mul_sum]
    refine sum_congr rfl fun f _ => ?_
    rw [nsmul_eq_mul]
    ring
  have h3 : ∑ c : Child, g (childExtra c) (childExtra c) =
      ∑ e ∈ range 4, ∑ f ∈ range 4, (if e = f then (extCount e : R) else 0) * g e f := by
    rw [sum_child (fun e => g e e)]
    refine sum_congr rfl fun e he => ?_
    rw [sum_eq_single e]
    · simp [nsmul_eq_mul]
    · intro f _ hf; simp [Ne.symm hf]
    · intro h; exact absurd he h
  rw [h2, h3, ← sum_sub_distrib]
  refine sum_congr rfl fun e _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun f _ => ?_
  unfold nPair
  push_cast
  split_ifs <;> ring

def LamP2 (e f key key' : ℕ) (x : R) : R :=
  (Et x - x ^ e - x ^ f) * Rt x + x ^ e * rhoK key x + x ^ f * rhoK key' x

def lam3b (k L e f key key' : ℕ) (x : R) : R :=
  LamP2 e f key key' x * LamP2 e f key key' (x ^ L) * LamP2 e f key key' 1 ^ k

theorem alw2_split_X (c c' : Child) (hc : c ≠ c') (u u' : Fin 6 → Fin 6) (x : R) (y : Cell) :
    (if Alw wordDigit c u y ∧ Alw wordDigit c' u' y then x ^ sc y else 0) =
      x ^ sc y - (if y.1 = c then x ^ sc y else 0) - (if y.1 = c' then x ^ sc y else 0)
        + (if y.1 = c ∧ (∀ j, wordDigit y.2 j < u j) then x ^ sc y else 0)
        + (if y.1 = c' ∧ (∀ j, wordDigit y.2 j < u' j) then x ^ sc y else 0) := by
  unfold Alw
  by_cases h1 : y.1 = c
  · have h2 : y.1 ≠ c' := fun h => hc (h1.symm.trans h)
    by_cases h3 : ∀ j, wordDigit y.2 j < u j <;> simp [h1, h2, h3, hc]
  · by_cases h2 : y.1 = c'
    · by_cases h3 : ∀ j, wordDigit y.2 j < u' j <;> simp [h1, h2, h3, Ne.symm hc]
    · simp [h1, h2]

theorem sum_alw2_X (c c' : Child) (hc : c ≠ c') (u u' : Fin 6 → Fin 6) (x : R) :
    ∑ y : Cell, (if Alw wordDigit c u y ∧ Alw wordDigit c' u' y then x ^ sc y else 0) =
      LamP2 (childExtra c) (childExtra c') (keyU u) (keyU u') x := by
  rw [sum_congr rfl fun y _ => alw2_split_X c c' hc u u' x y]
  rw [sum_add_distrib, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, sum_X_sc, sum_X_sc_child,
    sum_X_sc_child, sum_X_sc_childD, sum_X_sc_childD]
  unfold LamP2
  ring

theorem sum_alw2_one (c c' : Child) (hc : c ≠ c') (u u' : Fin 6 → Fin 6) :
    ∑ y : Cell, (if Alw wordDigit c u y ∧ Alw wordDigit c' u' y then (1 : R) else 0) =
      LamP2 (childExtra c) (childExtra c') (keyU u) (keyU u') (1 : R) := by
  rw [← sum_alw2_X c c' hc u u']
  simp only [one_pow]

theorem prod_wt_alw2 (k L : ℕ) (x : R) (c c' : Child) (hc : c ≠ c') (u u' : Fin 6 → Fin 6) :
    ∏ m : Fin (k + 2), ∑ y : Cell, (if Alw wordDigit c u y ∧ Alw wordDigit c' u' y then wt k L x m y else 0) =
      lam3b k L (childExtra c) (childExtra c') (keyU u) (keyU u') x := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  have h0 : ∀ y : Cell, wt k L x 0 y = x ^ sc y := fun y => by simp [wt]
  have h1 : ∀ y : Cell, wt k L x (Fin.succ 0) y = (x ^ L) ^ sc y := fun y => by simp [wt]
  have h2 : ∀ (i : Fin k) (y : Cell), wt k L x i.succ.succ y = 1 := fun i y => by simp [wt]
  simp_rw [h0, h1, h2, sum_alw2_X c c' hc, sum_alw2_one c c' hc, prod_const, card_univ, Fintype.card_fin, lam3b,
    mul_assoc]

def Wd (k L : ℕ) (x : R) : R :=
  ∑ c : Child, ∑ c' : Child, if c = c' then 0 else
    ∑ ab : Rank × Rank, ∑ E : Fin (k + 2) → Cell,
      if CovAtM wordDigit (fun _ => false) c (wordDigit ab.1) E ∧ CovAtM wordDigit (fun _ => false) c' (wordDigit ab.2) E
      then ∏ m, wt k L x m (E m) else 0

def Psi2 (k L key key' : ℕ) (x : R) : R :=
  ∑ c : Child, ∑ c' : Child, if c = c' then 0 else lam3b k L (childExtra c) (childExtra c') key key' x

theorem Wd_lattice (k L : ℕ) (x : R) :
    Wd k L x = ∑ uu : (Fin 6 → Fin 6) × (Fin 6 → Fin 6),
      ((sgnU uu.1 : R) * (M1 wordDigit uu.1 : R)) * ((sgnU uu.2 : R) * (M1 wordDigit uu.2 : R)) *
        Psi2 k L (keyU uu.1) (keyU uu.2) x := by
  have hcc : ∀ c c' : Child, (if c = c' then (0 : R) else
      ∑ ab : Rank × Rank, ∑ E : Fin (k + 2) → Cell,
        if CovAtM wordDigit (fun _ => false) c (wordDigit ab.1) E ∧ CovAtM wordDigit (fun _ => false) c' (wordDigit ab.2) E
        then ∏ m, wt k L x m (E m) else 0) =
      ∑ uu : (Fin 6 → Fin 6) × (Fin 6 → Fin 6),
        ((sgnU uu.1 : R) * (M1 wordDigit uu.1 : R)) * ((sgnU uu.2 : R) * (M1 wordDigit uu.2 : R)) *
          (if c = c' then 0 else lam3b k L (childExtra c) (childExtra c') (keyU uu.1) (keyU uu.2) x) := by
    intro c c'
    by_cases h : c = c'
    · subst h
      simp only [if_true, mul_zero, sum_const_zero]
    · rw [if_neg h, ClaudeR3.IE.sum_weighted_covAtM_two wordDigit c c' ClaudeR3.Tab.wordDigit_le4 (wt k L x)]
      refine sum_congr rfl fun uu _ => ?_
      rw [prod_wt_alw2 k L x c c' h, if_neg h]
  rw [Wd, sum_congr rfl fun c _ => sum_congr rfl fun c' _ => hcc c c']
  rw [sum_congr rfl fun c _ => sum_comm, sum_comm]
  refine sum_congr rfl fun uu _ => ?_
  rw [Psi2, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [mul_sum]

theorem sgn_mul' (u : Fin 6 → Fin 6) (n : ℕ) (P : R) :
    (sgnU u : R) * (n : R) * P = (((if parU u then (-1 : ℤ) else 1 : ℤ)) : R) * ((n : R) * P) := by
  rw [sgnU_eq u, mul_assoc]

theorem Wd_table (k L : ℕ) (x : R) :
    Wd k L x = tabSum tabM (fun key => tabSum tabM (fun key' => Psi2 k L key key' x)) := by
  have hW := ClaudeR3.Tab.wordsOf_wordDigit'
  have h3 : ∀ x j, wordDigit x j ≤ 4 := fun x j => ClaudeR3.Tab.wordDigit_le4 x j
  have inner : ∀ key : ℕ, ∑ u' : Fin 6 → Fin 6, (sgnU u' : R) * (M1 wordDigit u' : R) * Psi2 k L key (keyU u') x =
      tabSum tabM (fun key' => Psi2 k L key key' x) := by
    intro key
    rw [← key_mean_R (fun key' => Psi2 k L key key' x)]
    refine sum_congr rfl fun u' _ => ?_
    rw [sgn_mul', g1T_eq hW h3, ClaudeR3.Tab.lookup_keyT]
  rw [Wd_lattice, Fintype.sum_prod_type]
  have outer : ∀ u : Fin 6 → Fin 6, ∑ u' : Fin 6 → Fin 6,
      (sgnU u : R) * (M1 wordDigit u : R) * ((sgnU u' : R) * (M1 wordDigit u' : R)) *
        Psi2 k L (keyU u) (keyU u') x =
      (sgnU u : R) * (M1 wordDigit u : R) * tabSum tabM (fun key' => Psi2 k L (keyU u) key' x) := by
    intro u
    rw [← inner, mul_sum]
    refine sum_congr rfl fun u' _ => ?_
    ring
  rw [sum_congr rfl fun u _ => outer u]
  rw [← key_mean_R (fun key => tabSum tabM (fun key' => Psi2 k L key key' x))]
  refine sum_congr rfl fun u _ => ?_
  rw [sgn_mul', g1T_eq hW h3, ClaudeR3.Tab.lookup_keyT]

def AI2 (e f : ℕ) (x : R) : R := (EtI x - x ^ e - x ^ f) * RtI x

theorem LamP2_eval (e f key key' : ℕ) (x : R) :
    LamP2 e f key key' x = AI2 e f x + x ^ e * rhoI key x + x ^ f * rhoI key' x := by
  unfold LamP2 AI2
  rw [Rt_eval, Et_eval, rhoK_eval, rhoK_eval]

theorem LamP2_eval_one (e f key key' : ℕ) : LamP2 e f key key' (1 : R) = 70938 + dsumI key + dsumI key' := by
  rw [LamP2_eval]
  unfold AI2
  rw [EtI_one, RtI_one, rhoI_one, rhoI_one]
  ring

end

end ClaudeR3.Diff
