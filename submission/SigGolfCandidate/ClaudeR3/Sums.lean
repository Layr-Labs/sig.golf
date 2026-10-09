import SigGolfCandidate.ClaudeR3.Tables
import SigGolfCandidate.ClaudeWCT.WCT9.Core
import SigGolfCandidate.ClaudeR3.Lemmas
import SigGolfCandidate.ClaudeWCT.Numerics.N600CapCount

section
set_option maxRecDepth 200000

namespace ClaudeR3.Tab
open Finset Polynomial
open ClaudeWCT.Numerics.N600
open ClaudeWCT.WCT9 (wordDigit routineCost routineCosts childExtra Child Rank)

def lev (b : Rank) : ℕ := routineCost b - 75

def keyU (u : Fin 6 → Fin 6) : ℕ := ∑ b : Rank, if (∀ j, wordDigit b j < u j) then 1024 ^ lev b else 0

set_option maxRecDepth 100000 in
theorem codeWords_eq' : ClaudeWCT.WCT9.codeWords = words := by decide +kernel

set_option maxRecDepth 100000 in
theorem levs_eq : levs = routineCosts.map (· - 75) := by decide +kernel

theorem levs_length : levs.length = 563 := by
  rw [levs_eq, List.length_map, ClaudeWCT.WCT9.routineCosts_length]

theorem words_length' : words.length = 563 := by
  rw [← codeWords_eq']; exact ClaudeWCT.WCT9.codeWords_length

theorem words_get (b : Rank) : words[b.val]'(by rw [words_length']; exact b.isLt) = List.ofFn (wordDigit b) := by
  have h := ClaudeWCT.WCT9.ofFn_wordDigit b
  rw [ClaudeWCT.WCT9.codeword_embed] at h
  rw [h]
  simp only [codeWords_eq']

theorem levs_get (b : Rank) : levs[b.val]'(by rw [levs_length]; exact b.isLt) = lev b := by
  simp only [levs_eq, List.getElem_map]
  rfl

theorem keyItems_eq : keyItems = List.ofFn (fun b : Rank => (List.ofFn (wordDigit b), 1024 ^ lev b)) := by
  apply List.ext_getElem
  · rw [keyItems, List.length_zipWith, words_length', levs_length, List.length_ofFn]; rfl
  · intro i h1 h2
    have hi : i < 563 := by rwa [List.length_ofFn] at h2
    rw [List.getElem_ofFn]
    simp only [keyItems, List.getElem_zipWith]
    rw [words_get ⟨i, hi⟩, levs_get ⟨i, hi⟩]

theorem lookup_keyT (u : Fin 6 → Fin 6) : lookup keyT (digitsOf u) = keyU u := by
  have hlen : ∀ p ∈ keyItems, p.1.length = 6 := by
    intro p hp
    rw [keyItems_eq, List.mem_ofFn] at hp
    obtain ⟨b, rfl⟩ := hp
    simp
  rw [keyT, lookupW 6 keyItems hlen _ (digitsOf_length u) (digitsOf_le u), wsum, keyItems_eq,
    List.map_ofFn, List.sum_ofFn, keyU]
  refine sum_congr rfl fun b _ => ?_
  exact if_congr (ltB_ofFn_iff _ u) rfl rfl

theorem ofFn_wordDigit_list' : List.ofFn (fun b : Rank => List.ofFn (wordDigit b)) = words := by
  apply List.ext_getElem
  · rw [List.length_ofFn, words_length']
  · intro i h1 h2
    have hi : i < 563 := by rwa [List.length_ofFn] at h1
    rw [List.getElem_ofFn, ← words_get ⟨i, hi⟩]

theorem wordsOf_wordDigit' : WordsOf wordDigit := by
  unfold WordsOf
  rw [Fin.univ_val_map, ofFn_wordDigit_list']

theorem wordDigit_le4 (b : Rank) (j : Fin 6) : wordDigit b j ≤ 4 := ClaudeWCT.WCT9.wordDigit_le_four b j

def digit (k l : ℕ) : ℕ := k / 1024 ^ l % 1024

noncomputable def rhoU (u : Fin 6 → Fin 6) : ℕ[X] := ∑ b : Rank, if (∀ j, wordDigit b j < u j) then X ^ lev b else 0

theorem rhoU_eval (u : Fin 6 → Fin 6) : (rhoU u).eval 1024 = keyU u := by
  simp [rhoU, keyU, eval_finsetSum, apply_ite]

theorem rhoU_eval_one (u : Fin 6 → Fin 6) : (rhoU u).eval 1 = #{b : Rank | ∀ j, wordDigit b j < u j} := by
  simp [rhoU, eval_finsetSum, apply_ite, Finset.sum_boole]

theorem lev_le (b : Rank) : lev b ≤ 14 := by
  have := (ClaudeWCT.WCT9.routineCost_bounds b).2
  unfold lev; omega

theorem rhoU_coeff_lt (u : Fin 6 → Fin 6) (i : ℕ) : (rhoU u).coeff i < 1024 := by
  refine lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one _ i) ?_
  rw [rhoU_eval_one]
  have := card_le_univ (filter (fun b : Rank => ∀ j, wordDigit b j < u j) univ)
  simp only [Fintype.card_fin] at this
  omega

theorem rhoU_natDegree (u : Fin 6 → Fin 6) : (rhoU u).natDegree ≤ 14 := by
  unfold rhoU
  refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  split_ifs
  · rw [natDegree_X_pow]; exact lev_le b
  · simp

theorem rhoU_eq_digits (u : Fin 6 → Fin 6) :
    rhoU u = ∑ l ∈ range 15, C (digit (keyU u) l) * X ^ l := by
  conv_lhs => rw [as_sum_range' (rhoU u) 15 (by have := rhoU_natDegree u; omega)]
  refine sum_congr rfl fun l _ => ?_
  rw [digit, ← rhoU_eval, ClaudeWCT.Numerics.eval_div_pow_mod (by norm_num) l _ (rhoU_coeff_lt u),
    C_mul_X_pow_eq_monomial]

def extCount (e : ℕ) : ℕ := #{c : Child | childExtra c = e}

theorem extCount_vals : extCount 0 = 2 ∧ extCount 1 = 72 ∧ extCount 2 = 52 ∧ extCount 3 = 2 := by
  unfold extCount; decide

theorem childExtra_le (c : Child) : childExtra c ≤ 3 := by
  unfold childExtra ClaudeWCT.WCT9.maxChildSave; omega

theorem sum_child {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ c : Child, f (childExtra c) = ∑ e ∈ range 4, extCount e • f e := by
  rw [← sum_fiberwise_of_maps_to (g := childExtra) (t := range 4)
    (fun c _ => mem_range.mpr (by have := childExtra_le c; omega))]
  refine sum_congr rfl fun e _ => ?_
  rw [sum_congr rfl fun c hc => by rw [(mem_filter.mp hc).2], sum_const]
  rfl

end ClaudeR3.Tab
end

section
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
end

section
namespace ClaudeR3.KEval
open Finset
open ClaudeR3.Poly
open ClaudeR3.Tab (digit extCount levs sum_child lev Tab)
open ClaudeWCT.WCT9 (childExtra Child Rank)

section
variable {R : Type*} [CommRing R]

def rsum (n : ℕ) (f : ℕ → R) : R := (List.range n).foldr (fun i s => f i + s) 0

theorem rsum_eq (n : ℕ) (f : ℕ → R) : rsum n f = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rsum, List.range_succ, List.foldr_append, Finset.sum_range_succ]
    simp only [List.foldr_cons, List.foldr_nil, add_zero]
    have hshift : ∀ (l : List ℕ) (c : R), l.foldr (fun i s => f i + s) c = l.foldr (fun i s => f i + s) 0 + c := by
      intro l c
      induction l with
      | nil => simp
      | cons a l ihl => simp only [List.foldr_cons, ihl]; ring
    rw [hshift, ← rsum, ih]

def rhoI (key : ℕ) (x : R) : R := rsum 15 fun l => (digit key l : R) * x ^ l
def dsumI (key : ℕ) : R := rsum 15 fun l => (digit key l : R)
def RtI (x : R) : R := (levs.map fun l => x ^ l).sum
def EtI (x : R) : R := rsum 4 fun e => (extCount e : R) * x ^ e
def AI (e : ℕ) (x : R) : R := (EtI x - x ^ e) * RtI x

theorem Rt_eval (x : R) : Rt x = RtI x := by
  unfold Rt RtI
  rw [← List.ofFn_getElem (xs := levs), List.map_ofFn, List.sum_ofFn]
  refine Fintype.sum_equiv (finCongr ClaudeR3.Tab.levs_length.symm) _ _ fun b => ?_
  simp only [Function.comp, finCongr_apply, Fin.coe_cast]
  rw [ClaudeR3.Tab.levs_get]

theorem Et_eval (x : R) : Et x = EtI x := by
  unfold Et EtI
  rw [rsum_eq, sum_child (fun e => x ^ e)]
  simp [nsmul_eq_mul]

theorem rhoK_eval (key : ℕ) (x : R) : rhoK key x = rhoI key x := by
  unfold rhoK rhoI
  rw [rsum_eq]

theorem LamP_eval (e key : ℕ) (x : R) : LamP e key x = AI e x + x ^ e * rhoI key x := by
  unfold LamP AI
  rw [Rt_eval, Et_eval, rhoK_eval]

theorem EtI_one : EtI (1 : R) = 128 := by
  have h := ClaudeR3.Tab.extCount_vals
  rw [EtI, rsum_eq]
  simp [Finset.sum_range_succ, h.1, h.2.1, h.2.2.1, h.2.2.2]
  norm_num

theorem RtI_one : RtI (1 : R) = 563 := by
  simp only [RtI, one_pow]
  rw [List.map_const', List.sum_replicate, ClaudeR3.Tab.levs_length, nsmul_eq_mul, mul_one]
  norm_num

theorem rhoI_one (key : ℕ) : rhoI key (1 : R) = dsumI key := by
  simp [rhoI, dsumI]

theorem LamP_eval_one (e key : ℕ) : LamP e key (1 : R) = 71501 + dsumI key := by
  rw [LamP_eval]
  unfold AI
  rw [EtI_one, RtI_one, rhoI_one]
  ring

theorem lam3_eval (k L e key : ℕ) (x : R) :
    lam3 k L e key x =
      (AI e x + x ^ e * rhoI key x) * (AI e (x ^ L) + (x ^ L) ^ e * rhoI key (x ^ L)) * (71501 + dsumI key) ^ k := by
  unfold lam3
  rw [LamP_eval_one, LamP_eval, LamP_eval]

theorem Psi_eval (k L key : ℕ) (x : R) :
    Psi k L key x = ∑ e ∈ range 4, (extCount e : R) *
      ((AI e x + x ^ e * rhoI key x) * (AI e (x ^ L) + (x ^ L) ^ e * rhoI key (x ^ L)) *
        (71501 + dsumI key) ^ k) := by
  unfold Psi
  rw [sum_child (fun e => lam3 k L e key x)]
  refine sum_congr rfl fun e _ => ?_
  rw [nsmul_eq_mul, lam3_eval]

abbrev Rec := ℕ × ℤ

theorem list_sum_finset {ι : Type*} (l : List Rec) (s : Finset ι) (f : Rec → ι → R) :
    (l.map fun a => ∑ i ∈ s, f a i).sum = ∑ i ∈ s, (l.map fun a => f a i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, sum_add_distrib]

structure Sums (R : Type*) where
  s0 : R
  s1x : R
  s1y : R
  s2 : R

def alphaI (k : ℕ) (a : Rec) : R := (a.2 : R) * (71501 + dsumI a.1) ^ k

def sums (tab : Tab) (k : ℕ) (x y : R) : Sums R where
  s0 := (tab.map fun a => alphaI k a).sum
  s1x := (tab.map fun a => alphaI k a * rhoI a.1 x).sum
  s1y := rsum 15 fun l => y ^ l * (tab.map fun a => alphaI k a * (digit a.1 l : R)).sum
  s2 := rsum 15 fun l => y ^ l * (tab.map fun a => alphaI k a * (digit a.1 l : R) * rhoI a.1 x).sum

def combine (S : Sums R) (x y : R) : R :=
  rsum 4 fun e => (extCount e : R) *
    (AI e x * AI e y * S.s0 + AI e x * y ^ e * S.s1y + x ^ e * AI e y * S.s1x + x ^ e * y ^ e * S.s2)

def famEval (tab : Tab) (k L : ℕ) (x : R) : R := combine (sums tab k x (x ^ L)) x (x ^ L)

theorem rhoI_y (key : ℕ) (y : R) : rhoI key y = ∑ l ∈ range 15, (digit key l : R) * y ^ l := by
  rw [rhoI, rsum_eq]

theorem per_rec (k L : ℕ) (x : R) (a : Rec) :
    ((a.2 : ℤ) : R) * Psi k L a.1 x = ∑ e ∈ range 4, (extCount e : R) *
      (AI e x * AI e (x ^ L) * alphaI k a
        + AI e x * (x ^ L) ^ e * (∑ l ∈ range 15, (x ^ L) ^ l * (alphaI k a * (digit a.1 l : R)))
        + x ^ e * AI e (x ^ L) * (alphaI k a * rhoI a.1 x)
        + x ^ e * (x ^ L) ^ e * (∑ l ∈ range 15, (x ^ L) ^ l * (alphaI k a * (digit a.1 l : R) * rhoI a.1 x))) := by
  rw [Psi_eval, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  have hA : ∑ l ∈ range 15, (x ^ L) ^ l * (alphaI k a * (digit a.1 l : R)) = alphaI k a * rhoI a.1 (x ^ L) := by
    rw [rhoI_y, mul_sum]; exact sum_congr rfl fun l _ => by ring
  have hB : ∑ l ∈ range 15, (x ^ L) ^ l * (alphaI k a * (digit a.1 l : R) * rhoI a.1 x) =
      alphaI k a * rhoI a.1 x * rhoI a.1 (x ^ L) := by
    rw [rhoI_y a.1 (x ^ L), mul_sum]; exact sum_congr rfl fun l _ => by ring
  rw [hA, hB, alphaI]
  ring

theorem list_sum_mul_left (l : List Rec) (c : R) (f : Rec → R) :
    (l.map fun a => c * f a).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, mul_add]

theorem list_sum_add (l : List Rec) (f g : Rec → R) :
    (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

theorem famEval_eq (tab : Tab) (k L : ℕ) (x : R) : tabSum tab (fun key => Psi k L key x) = famEval tab k L x := by
  unfold tabSum
  simp_rw [per_rec k L x]
  rw [list_sum_finset]
  unfold famEval combine
  rw [rsum_eq]
  refine sum_congr rfl fun e _ => ?_
  rw [list_sum_mul_left, list_sum_add, list_sum_add, list_sum_add, list_sum_mul_left, list_sum_mul_left,
    list_sum_mul_left, list_sum_mul_left, list_sum_finset, list_sum_finset]
  simp only [sums, rsum_eq, list_sum_mul_left]

end

end ClaudeR3.KEval
end

section
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
end

section
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
end

section
namespace ClaudeR3.Asm
open Finset Polynomial
open ClaudeR3.Poly
open ClaudeR3.KEval
open ClaudeR3.Prod9
open ClaudeR3.IE (CovAtM)
open ClaudeR3.Tab (tabM tabN tabS lev Tab)
open ClaudeWCT.WCT9 (wordDigit routineCost childExtra Child Rank)
open ClaudeWCT.Numerics.Thinning (ListCov listCov_ofFn FullCov CovAt coordEquiv)
open ClaudeWCT.Numerics.N600Cap (pairCost)

abbrev Coords := Fin 9 → Cell

def capS (cap : ℕ) : Finset Coords := univ.filter fun c => pairCost c ≤ cap

theorem pairCost_eq (c : Coords) : pairCost c = (∑ k, sc (c k)) + 675 := by
  unfold pairCost sc lev
  have h : ∀ k, routineCost (c k).2 + childExtra (c k).1 = (routineCost (c k).2 - 75 + childExtra (c k).1) + 75 := by
    intro k
    have := (ClaudeWCT.WCT9.routineCost_bounds (c k).2).1
    omega
  rw [sum_congr rfl fun k _ => h k, sum_add_distrib]
  simp

theorem sc_le (x : Cell) : sc x ≤ 17 := by
  unfold sc
  have := ClaudeR3.Tab.lev_le x.2
  have := ClaudeR3.Tab.childExtra_le x.1
  omega

abbrev Item (k : ℕ) := Cell × (Fin (k + 2) → Cell)

def Ycov (k : ℕ) : Finset (Item k) := univ.filter fun y => CovAtM wordDigit (fun _ => false) y.1.1 (wordDigit y.1.2) y.2

theorem covAtM_iff {r : ℕ} (c : Child) (v : Fin 6 → ℕ) (E : Fin r → Cell) :
    CovAtM wordDigit (fun _ => false) c v E ↔ CovAt wordDigit c v E := by
  unfold CovAtM CovAt; simp

def tr (k : ℕ) : (Fin 9 → Item k) ≃ (Fin (k + 2) → Coords) × Coords :=
  (coordEquiv Cell (k + 2) Cell).trans (Equiv.prodComm _ _)

theorem tr_apply_fst (k : ℕ) (x : Fin 9 → Item k) (m : Fin (k + 2)) (j : Fin 9) : (tr k x).1 m j = (x j).2 m := rfl
theorem tr_apply_snd (k : ℕ) (x : Fin 9 → Item k) (j : Fin 9) : (tr k x).2 j = (x j).1 := rfl

theorem listCov_tr (k : ℕ) (x : Fin 9 → Item k) :
    ListCov wordDigit (List.ofFn (tr k x).1) (tr k x).2 ↔ ∀ j, x j ∈ Ycov k := by
  rw [listCov_ofFn]
  unfold FullCov
  refine forall_congr' fun j => ?_
  simp only [Ycov, mem_filter, mem_univ, true_and, covAtM_iff]
  rfl

theorem cost_tr (k : ℕ) (x : Fin 9 → Item k) (m : Fin (k + 2)) :
    pairCost ((tr k x).1 m) = (∑ j, sc ((x j).2 m)) + 675 := by
  rw [pairCost_eq]; rfl

theorem card_tr (k : ℕ) (Q : (Fin (k + 2) → Coords) × Coords → Prop) [DecidablePred Q] :
    #{p : (Fin (k + 2) → Coords) × Coords | Q p} = #{x : Fin 9 → Item k | Q (tr k x)} := by
  symm
  refine Finset.card_equiv (tr k) fun x => ?_
  simp

theorem pi_filter (k : ℕ) (R : (Fin 9 → Item k) → Prop) [DecidablePred R] :
    #{x : Fin 9 → Item k | (∀ j, x j ∈ Ycov k) ∧ R x} = #{x ∈ Fintype.piFinset (fun _ => Ycov k) | R x} := by
  apply congrArg Finset.card
  ext x
  simp [Fintype.mem_piFinset]

section Generic
variable {Y Tgt : Type} [Fintype Y] [DecidableEq Y] [Fintype Tgt] {k : ℕ}
  (e : (Fin 9 → Y) ≃ (Fin (k + 2) → Coords) × Tgt) (sig : Y → Fin (k + 2) → Cell)
  (he : ∀ x m j, (e x).1 m j = sig (x j) m)

def sa (sig : Y → Fin (k + 2) → Cell) (y : Y) : ℕ := sc (sig y 0)
def sb (sig : Y → Fin (k + 2) → Cell) (y : Y) : ℕ := sc (sig y 1)

include he in
theorem cost_e (x : Fin 9 → Y) (m : Fin (k + 2)) : pairCost ((e x).1 m) = (∑ j, sc (sig (x j) m)) + 675 := by
  rw [pairCost_eq]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [he]

theorem card_e (Q : (Fin (k + 2) → Coords) × Tgt → Prop) [DecidablePred Q] :
    #{p : (Fin (k + 2) → Coords) × Tgt | Q p} = #{x : Fin 9 → Y | Q (e x)} := by
  symm
  refine Finset.card_equiv e fun x => ?_
  simp

theorem pi_filter' (C : Fin 9 → Finset Y) (R : (Fin 9 → Y) → Prop) [DecidablePred R] :
    #{x : Fin 9 → Y | (∀ j, x j ∈ C j) ∧ R x} = #{x ∈ Fintype.piFinset C | R x} := by
  congr 1
  ext x
  simp [Fintype.mem_piFinset]

variable (Pcov : (Fin (k + 2) → Coords) × Tgt → Prop) [DecidablePred Pcov] (C : Fin 9 → Finset Y)
  (htr : ∀ x, Pcov (e x) ↔ ∀ j, x j ∈ C j)

include htr in
theorem gen_base : #{p : (Fin (k + 2) → Coords) × Tgt | Pcov p} = (∏ j, genP (C j) (sa sig) (sb sig)).eval 1 := by
  rw [card_e e]
  simp_rw [htr]
  have h := pi_filter' C (fun _ => True)
  simp only [and_true, filter_true] at h
  rw [h, base_count C (sa sig) (sb sig)]

include he htr in
theorem gen_tail1 (A : ℕ) (hA : A < 153) (B : ℕ)
    (hB : (∏ j, genP (C j) (sa sig) (sb sig)).eval 1 * ((153 - A) * 154) < B) :
    #{p : (Fin (k + 2) → Coords) × Tgt | 675 + A < pairCost (p.1 0) ∧ Pcov p} =
      (∏ j, genP (C j) (sa sig) (sb sig)).eval B * (Mask (153 - A) 154).eval B / B ^ Ntop % B := by
  rw [card_e e]
  simp_rw [htr, cost_e e sig he]
  have h : ∀ x : Fin 9 → Y, (675 + A < (∑ j, sc (sig (x j) 0)) + 675 ∧ ∀ j, x j ∈ C j) ↔
      ((∀ j, x j ∈ C j) ∧ A < ∑ j, sa sig (x j)) := by
    intro x
    unfold sa
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩
  simp_rw [h]
  rw [pi_filter' C (fun x => A < ∑ j, sa sig (x j)),
    tail1_extract C (sa sig) (sb sig) (fun y => sc_le _) (fun y => sc_le _) A hA B hB]

include he htr in
theorem gen_tail2 (A : ℕ) (hA : A < 153) (B : ℕ)
    (hB : (∏ j, genP (C j) (sa sig) (sb sig)).eval 1 * ((153 - A) * (153 - A)) < B) :
    #{p : (Fin (k + 2) → Coords) × Tgt | 675 + A < pairCost (p.1 0) ∧ 675 + A < pairCost (p.1 1) ∧ Pcov p} =
      (∏ j, genP (C j) (sa sig) (sb sig)).eval B * (Mask (153 - A) (153 - A)).eval B / B ^ Ntop % B := by
  rw [card_e e]
  simp_rw [htr, cost_e e sig he]
  have h : ∀ x : Fin 9 → Y,
      (675 + A < (∑ j, sc (sig (x j) 0)) + 675 ∧ 675 + A < (∑ j, sc (sig (x j) 1)) + 675 ∧ ∀ j, x j ∈ C j) ↔
      ((∀ j, x j ∈ C j) ∧ (A < ∑ j, sa sig (x j) ∧ A < ∑ j, sb sig (x j))) := by
    intro x
    unfold sa sb
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h3, by omega, by omega⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h1⟩
  simp_rw [h]
  rw [pi_filter' C (fun x => A < ∑ j, sa sig (x j) ∧ A < ∑ j, sb sig (x j)),
    tail2_extract C (sa sig) (sb sig) (fun y => sc_le _) (fun y => sc_le _) A hA B hB]

include he htr in
theorem gen_tail1c (A : ℕ) (hA : A < 153) :
    #{p : (Fin (k + 2) → Coords) × Tgt | 675 + A < pairCost (p.1 0) ∧ Pcov p} =
      ((∏ j, genP (C j) (sa sig) (sb sig)) * Mask (153 - A) 154).coeff Ntop := by
  rw [card_e e]
  simp_rw [htr, cost_e e sig he]
  have h : ∀ x : Fin 9 → Y, (675 + A < (∑ j, sc (sig (x j) 0)) + 675 ∧ ∀ j, x j ∈ C j) ↔
      ((∀ j, x j ∈ C j) ∧ A < ∑ j, sa sig (x j)) := by
    intro x
    unfold sa
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩
  simp_rw [h]
  rw [pi_filter' C (fun x => A < ∑ j, sa sig (x j)),
    tail1_count C (sa sig) (sb sig) (fun y => sc_le _) (fun y => sc_le _) A, coeff_mask1 _ A hA]

include he htr in
theorem gen_tail2c (A : ℕ) (hA : A < 153) :
    #{p : (Fin (k + 2) → Coords) × Tgt | 675 + A < pairCost (p.1 0) ∧ 675 + A < pairCost (p.1 1) ∧ Pcov p} =
      ((∏ j, genP (C j) (sa sig) (sb sig)) * Mask (153 - A) (153 - A)).coeff Ntop := by
  rw [card_e e]
  simp_rw [htr, cost_e e sig he]
  have h : ∀ x : Fin 9 → Y,
      (675 + A < (∑ j, sc (sig (x j) 0)) + 675 ∧ 675 + A < (∑ j, sc (sig (x j) 1)) + 675 ∧ ∀ j, x j ∈ C j) ↔
      ((∀ j, x j ∈ C j) ∧ (A < ∑ j, sa sig (x j) ∧ A < ∑ j, sb sig (x j))) := by
    intro x
    unfold sa sb
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h3, by omega, by omega⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h1⟩
  simp_rw [h]
  rw [pi_filter' C (fun x => A < ∑ j, sa sig (x j) ∧ A < ∑ j, sb sig (x j)),
    tail2_count C (sa sig) (sb sig) (fun y => sc_le _) (fun y => sc_le _) A, coeff_mask2 _ A hA]

end Generic

def sigI (k : ℕ) (y : Item k) : Fin (k + 2) → Cell := y.2

theorem tr_he (k : ℕ) : ∀ (x : Fin 9 → Item k) m j, (tr k x).1 m j = sigI k (x j) m := fun _ _ _ => rfl

section
variable {R : Type*} [CommRing R]

theorem sum_Ycov (k L : ℕ) (x : R) :
    ∑ y ∈ Ycov k, x ^ sa (sigI k) y * (x ^ L) ^ sb (sigI k) y = Wm k L x := by
  unfold Wm Ycov
  rw [sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun t _ => sum_congr rfl fun E _ => ?_
  dsimp only
  split_ifs with h
  · rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp [wt, sa, sb, sigI]
  · rfl

end

theorem genP_Ycov (k : ℕ) (B : ℕ) :
    (((genP (Ycov k) (sa (sigI k)) (sb (sigI k))).eval B : ℕ) : ℤ) = Wm k 154 (B : ℤ) := by
  rw [← sum_Ycov]
  unfold genP
  rw [eval_finset_sum, Nat.cast_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [eval_pow, eval_X]
  push_cast
  ring

theorem prod_const9 {Y : Type} [DecidableEq Y] (S : Finset Y) (a b : Y → ℕ) :
    (∏ _j : Fin 9, genP S a b) = genP S a b ^ 9 := by
  rw [prod_const, card_univ, Fintype.card_fin]

theorem htr_mean (k : ℕ) (x : Fin 9 → Item k) :
    ListCov wordDigit (List.ofFn (tr k x).1) (tr k x).2 ↔ ∀ j, x j ∈ (fun _ : Fin 9 => Ycov k) j := listCov_tr k x

def nsumR (n : ℕ) (f : ℕ → ℕ) : ℕ := (List.range n).foldr (fun i s => f i + s) 0

theorem nsumR_eq (n : ℕ) (f : ℕ → ℕ) : nsumR n f = ∑ i ∈ range n, f i := by
  have h := rsum_eq (R := ℤ) n (fun i => (f i : ℤ))
  have h2 : rsum n (fun i => (f i : ℤ)) = (nsumR n f : ℤ) := by
    unfold rsum nsumR
    induction (List.range n) with
    | nil => rfl
    | cons a l ih => simp [ih]
  rw [h2, ← Nat.cast_sum] at h
  exact_mod_cast h

def maskV (n₁ n₂ B : ℕ) : ℕ := nsumR n₁ (fun i => B ^ i) * nsumR n₂ (fun j => B ^ (154 * j))

theorem maskV_eq (n₁ n₂ B : ℕ) : maskV n₁ n₂ B = (Mask n₁ n₂).eval B := by
  rw [maskV, Mask_eval, nsumR_eq, nsumR_eq]

theorem nat_bound {c b x y : ℕ} (h : (c : ℤ) ≤ b - x + y) : c ≤ (b + y) - x := by omega

def bonfN (P1 PB A r' B : ℕ) : ℕ :=
  (P1 + r'.choose 2 * (PB * maskV (153 - A) (153 - A) B / B ^ Ntop % B)) -
    r' * (PB * maskV (153 - A) 154 B / B ^ Ntop % B)

theorem gen_bound {Y Tgt : Type} [Fintype Y] [DecidableEq Y] [Fintype Tgt] {k : ℕ}
    (e : (Fin 9 → Y) ≃ (Fin (k + 2) → Coords) × Tgt) (sig : Y → Fin (k + 2) → Cell)
    (he : ∀ x m j, (e x).1 m j = sig (x j) m)
    (Pcov : (Fin (k + 2) → Coords) × Tgt → Prop) [DecidablePred Pcov] (C : Fin 9 → Finset Y)
    (htr : ∀ x, Pcov (e x) ↔ ∀ j, x j ∈ C j)
    (hsym : ∀ (σ : Equiv.Perm (Fin (k + 2))) E t, Pcov (E ∘ σ, t) ↔ Pcov (E, t))
    (A r' B : ℕ) (hA : A < 153) (hr' : r' ≤ k + 2)
    (hB : (∏ j, genP (C j) (sa sig) (sb sig)).eval 1 * ((153 - A) * 154) < B) :
    #{p : (Fin (k + 2) → Coords) × Tgt | (∀ m, p.1 m ∈ capS (675 + A)) ∧ Pcov p} ≤
      bonfN ((∏ j, genP (C j) (sa sig) (sb sig)).eval 1) ((∏ j, genP (C j) (sa sig) (sb sig)).eval B) A r' B := by
  have hB2 : (∏ j, genP (C j) (sa sig) (sb sig)).eval 1 * ((153 - A) * (153 - A)) < B :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))) hB
  have hb := ClaudeR3.bonf_count (β := Coords) (T := Tgt) (r := k + 2) (fun e => 675 + A < pairCost e)
    (fun E t => Pcov (E, t)) (fun σ E t => hsym σ E t) 0 1 (by simp) r' hr'
  have e0 : ∀ p : (Fin (k + 2) → Coords) × Tgt, (∀ m, ¬ (675 + A < pairCost (p.1 m))) ↔ ∀ m, p.1 m ∈ capS (675 + A) := by
    intro p; simp [capS, not_lt]
  simp only [e0, Prod.mk.eta] at hb
  rw [gen_base e sig Pcov C htr, gen_tail1 e sig he Pcov C htr A hA B hB, gen_tail2 e sig he Pcov C htr A hA B hB2,
    ← maskV_eq, ← maskV_eq] at hb
  unfold bonfN
  apply nat_bound
  push_cast at hb ⊢
  linarith

def Wv (tab : Tab) (k B : ℕ) : ℕ := (famEval tab k 154 (B : ℤ)).toNat

def bonfMeanN (k A r' B : ℕ) : ℕ := bonfN (Wv tabM k 1 ^ 9) (Wv tabM k B ^ 9) A r' B

def meanOk (k A B : ℕ) : Bool := Wv tabM k 1 ^ 9 * ((153 - A) * 154) < B

theorem genP_eval_Wv (k B : ℕ) : (genP (Ycov k) (sa (sigI k)) (sb (sigI k))).eval B = Wv tabM k B := by
  have h := genP_Ycov k B
  rw [Wm_table, famEval_eq] at h
  unfold Wv
  rw [← h, Int.toNat_natCast]

theorem mean_bound (k A r' B : ℕ) (hA : A < 153) (hr' : r' ≤ k + 2) (hok : meanOk k A B = true) :
    #{p : (Fin (k + 2) → Coords) × Coords | (∀ m, p.1 m ∈ capS (675 + A)) ∧ ListCov wordDigit (List.ofFn p.1) p.2} ≤
      bonfMeanN k A r' B := by
  have h := gen_bound (tr k) (sigI k) (tr_he k) (fun p => ListCov wordDigit (List.ofFn p.1) p.2) (fun _ => Ycov k)
    (htr_mean k) (fun σ E t => ClaudeR3.Law.listCov_perm wordDigit σ E t) A r' B hA hr'
    (by rw [prod_const9, eval_pow, genP_eval_Wv]; simpa [meanOk] using hok)
  rw [prod_const9, eval_pow, eval_pow, genP_eval_Wv, genP_eval_Wv] at h
  exact h

end ClaudeR3.Asm
end

section
namespace ClaudeR3.Asm
open Finset Polynomial
set_option maxRecDepth 100000
open ClaudeWCT.Numerics.N600Cap (pairCost pairPoly pairEval card_pairCost_eq range_foldr_eq_sum' eval_pairPoly eval_one_pairPoly)

def J779 : ℕ := 50017003700803880389270367190751792644955136

def capCheck779 : Bool :=
  Nat.beq ((List.range 780).foldr (fun t s => pairEval (2 ^ 150) ^ 9 / (2 ^ 150) ^ t % 2 ^ 150 + s) 0) J779

theorem capCheck779_ok : capCheck779 = true := by decide +kernel

theorem mem_capS (cap : ℕ) (c : Coords) : c ∈ capS cap ↔ pairCost c ≤ cap := by
  simp only [capS, mem_filter, mem_univ, true_and]

set_option linter.constructorNameAsVariable false in
theorem card_capS779 : (capS 779).card = J779 := by
  have hB : 0 < 2 ^ 150 := by positivity
  have hcoeff : ∀ i, (pairPoly ^ 9).coeff i < 2 ^ 150 := by
    intro i
    refine lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one _ i) ?_
    rw [eval_pow, eval_one_pairPoly]
    norm_num
  have hext : ∀ t, (pairPoly ^ 9).coeff t = pairEval (2 ^ 150) ^ 9 / (2 ^ 150) ^ t % 2 ^ 150 := by
    intro t
    rw [← ClaudeWCT.Numerics.eval_div_pow_mod hB t _ hcoeff, eval_pow, eval_pairPoly]
  have hsplit : (capS 779).card = ∑ t ∈ range 780, #{c : Fin 9 → ClaudeWCT.WCT9.Child × ClaudeWCT.WCT9.Rank |
      pairCost c = t} := by
    have hmem : ∀ c ∈ capS 779, pairCost c ∈ range 780 := by
      intro c hc
      rw [mem_capS] at hc
      rw [mem_range]
      omega
    rw [card_eq_sum_card_fiberwise hmem]
    unfold capS
    refine sum_congr rfl fun t ht => ?_
    rw [filter_filter]
    exact congrArg Finset.card (filter_congr fun c _ => ⟨fun h => h.2,
      fun h => ⟨by rw [h]; have h2 := mem_range.mp ht; omega, h⟩⟩)
  have hc := capCheck779_ok
  unfold capCheck779 at hc
  rw [hsplit]
  simp_rw [card_pairCost_eq, hext]
  rw [← range_foldr_eq_sum']
  exact Nat.eq_of_beq_eq_true hc

theorem capS779_nonempty : (capS 779).Nonempty := by
  rw [← card_pos, card_capS779]; unfold J779; norm_num

end ClaudeR3.Asm
end

section
namespace ClaudeR3.Asm
open Finset Polynomial
open ClaudeR3.Poly
open ClaudeR3.KEval
open ClaudeR3.Prod9
open ClaudeR3.IE (CovAtM)
open ClaudeR3.Tab (tabM tabN tabS lev Tab)
open ClaudeWCT.WCT9 (wordDigit routineCost childExtra Child Rank)
open ClaudeWCT.Numerics.Thinning (ListCov listCov_ofFn FullCov CovAt coordEquiv pairEquiv ListCovExcept
  listCovExcept_ofFn FullNear)
open ClaudeWCT.Numerics.N600Cap (pairCost)

def Ynear (k : ℕ) (i₀ : Fin 6) : Finset (Item k) :=
  univ.filter fun y => CovAtM wordDigit (fun j => decide (j = i₀)) y.1.1 (wordDigit y.1.2) y.2

def Cn (k : ℕ) (k₀ : Fin 9) (i₀ : Fin 6) (j : Fin 9) : Finset (Item k) := if j = k₀ then Ynear k i₀ else Ycov k

theorem mem_Ynear (k : ℕ) (i₀ : Fin 6) (y : Item k) :
    y ∈ Ynear k i₀ ↔ CovAtM wordDigit (fun j => decide (j = i₀)) y.1.1 (wordDigit y.1.2) y.2 := by
  unfold Ynear
  simp only [mem_filter, mem_univ, true_and]

theorem mem_Ycov (k : ℕ) (y : Item k) :
    y ∈ Ycov k ↔ CovAtM wordDigit (fun _ => false) y.1.1 (wordDigit y.1.2) y.2 := by
  unfold Ycov
  simp only [mem_filter, mem_univ, true_and]

theorem htr_near (k : ℕ) (k₀ : Fin 9) (i₀ : Fin 6) (x : Fin 9 → Item k) :
    ListCovExcept wordDigit k₀ i₀ (List.ofFn (tr k x).1) (tr k x).2 ↔ ∀ j, x j ∈ Cn k k₀ i₀ j := by
  rw [listCovExcept_ofFn]
  unfold FullNear
  refine forall_congr' fun j => ?_
  unfold Cn
  by_cases hj : j = k₀
  · subst hj
    rw [if_pos rfl, mem_Ynear]
    unfold CovAtM
    refine forall_congr' fun i => ?_
    simp only [ne_eq, Prod.mk.injEq, true_and, decide_eq_false_iff_not]
    rfl
  · rw [if_neg hj, mem_Ycov]
    unfold CovAtM
    refine forall_congr' fun i => ?_
    simp only [ne_eq, Prod.mk.injEq, hj, false_and, not_false_eq_true, forall_const]
    rfl

theorem prod_Cn (k : ℕ) (k₀ : Fin 9) (i₀ : Fin 6) (a b : Item k → ℕ) :
    ∏ j, genP (Cn k k₀ i₀ j) a b = genP (Ynear k i₀) a b * genP (Ycov k) a b ^ 8 := by
  unfold Cn
  simp_rw [apply_ite (fun S => genP S a b)]
  rw [prod_ite, filter_eq', filter_ne', if_pos (mem_univ _), prod_singleton, prod_const,
    card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

section
variable {R : Type*} [CommRing R]

theorem sum_Ynear (k L : ℕ) (x : R) :
    ∑ i₀ : Fin 6, ∑ y ∈ Ynear k i₀, x ^ sa (sigI k) y * (x ^ L) ^ sb (sigI k) y = Wn k L x := by
  unfold Wn
  refine sum_congr rfl fun i₀ _ => ?_
  unfold Ynear
  rw [sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun t _ => sum_congr rfl fun E _ => ?_
  dsimp only
  split_ifs with h
  · rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp [wt, sa, sb, sigI]
  · rfl

end

theorem genP_Ynear (k B : ℕ) :
    (∑ i₀ : Fin 6, (((genP (Ynear k i₀) (sa (sigI k)) (sb (sigI k))).eval B : ℕ) : ℤ)) = Wn k 154 (B : ℤ) := by
  rw [← sum_Ynear]
  refine sum_congr rfl fun i₀ _ => ?_
  unfold genP
  rw [eval_finset_sum, Nat.cast_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [eval_pow, eval_X]
  push_cast
  ring

theorem sum_genP_Ynear_eval (k B : ℕ) :
    ∑ i₀ : Fin 6, (genP (Ynear k i₀) (sa (sigI k)) (sb (sigI k))).eval B = Wv tabN k B := by
  have h := genP_Ynear k B
  rw [Wn_table, famEval_eq] at h
  unfold Wv
  rw [← h, ← Nat.cast_sum, Int.toNat_natCast]

noncomputable def Pnear (k : ℕ) : ℕ[X] :=
  9 * (genP (Ycov k) (sa (sigI k)) (sb (sigI k)) ^ 8 * ∑ i₀ : Fin 6, genP (Ynear k i₀) (sa (sigI k)) (sb (sigI k)))

theorem sum_prod_Cn (k : ℕ) :
    ∑ k₀ : Fin 9, ∑ i₀ : Fin 6, ∏ j, genP (Cn k k₀ i₀ j) (sa (sigI k)) (sb (sigI k)) = Pnear k := by
  simp_rw [prod_Cn]
  unfold Pnear
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [mul_sum]
  push_cast
  refine sum_congr rfl fun i₀ _ => ?_
  ring

theorem Pnear_eval (k B : ℕ) : (Pnear k).eval B = 9 * (Wv tabM k B ^ 8 * Wv tabN k B) := by
  unfold Pnear
  rw [eval_mul, eval_mul, eval_pow, eval_finset_sum, sum_genP_Ynear_eval, genP_eval_Wv]
  simp

def bonfNearN (k A r' B : ℕ) : ℕ :=
  bonfN (9 * (Wv tabM k 1 ^ 8 * Wv tabN k 1)) (9 * (Wv tabM k B ^ 8 * Wv tabN k B)) A r' B

def nearOk (k A B : ℕ) : Bool := 9 * (Wv tabM k 1 ^ 8 * Wv tabN k 1) * ((153 - A) * 154) < B

theorem near_bound (k A r' B : ℕ) (hA : A < 153) (hr' : r' ≤ k + 2) (hok : nearOk k A B = true) :
    ∑ k₀ : Fin 9, ∑ i₀ : Fin 6,
      #{p : (Fin (k + 2) → Coords) × Coords | (∀ m, p.1 m ∈ capS (675 + A)) ∧
        ListCovExcept wordDigit k₀ i₀ (List.ofFn p.1) p.2} ≤ bonfNearN k A r' B := by
  have hok' : (Pnear k).eval 1 * ((153 - A) * 154) < B := by
    rw [Pnear_eval]; simpa [nearOk] using hok
  have hok2 : (Pnear k).eval 1 * ((153 - A) * (153 - A)) < B :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))) hok'

  have hb : ∀ k₀ : Fin 9, ∀ i₀ : Fin 6,
      (#{p : (Fin (k + 2) → Coords) × Coords | (∀ m, p.1 m ∈ capS (675 + A)) ∧
        ListCovExcept wordDigit k₀ i₀ (List.ofFn p.1) p.2} : ℤ) ≤
      ((∏ j, genP (Cn k k₀ i₀ j) (sa (sigI k)) (sb (sigI k))).eval 1 : ℕ)
        - r' * ((((∏ j, genP (Cn k k₀ i₀ j) (sa (sigI k)) (sb (sigI k))) * Mask (153 - A) 154).coeff Ntop : ℕ) : ℤ)
        + (r'.choose 2 : ℤ) *
          ((((∏ j, genP (Cn k k₀ i₀ j) (sa (sigI k)) (sb (sigI k))) * Mask (153 - A) (153 - A)).coeff Ntop : ℕ) : ℤ) := by
    intro k₀ i₀
    have h := ClaudeR3.bonf_count (β := Coords) (T := Coords) (r := k + 2) (fun e => 675 + A < pairCost e)
      (fun E t => ListCovExcept wordDigit k₀ i₀ (List.ofFn E) t)
      (fun σ E t => ClaudeR3.Law.listCovExcept_perm wordDigit k₀ i₀ σ E t) 0 1 (by simp) r' hr'
    have e0 : ∀ p : (Fin (k + 2) → Coords) × Coords, (∀ m, ¬ (675 + A < pairCost (p.1 m))) ↔
        ∀ m, p.1 m ∈ capS (675 + A) := by
      intro p; simp [capS, not_lt]
    simp only [e0] at h
    have htr := htr_near k k₀ i₀
    rw [gen_base (tr k) (sigI k) (fun p => ListCovExcept wordDigit k₀ i₀ (List.ofFn p.1) p.2) (Cn k k₀ i₀) htr,
      gen_tail1c (tr k) (sigI k) (tr_he k) (fun p => ListCovExcept wordDigit k₀ i₀ (List.ofFn p.1) p.2) (Cn k k₀ i₀)
        htr A hA,
      gen_tail2c (tr k) (sigI k) (tr_he k) (fun p => ListCovExcept wordDigit k₀ i₀ (List.ofFn p.1) p.2) (Cn k k₀ i₀)
        htr A hA] at h
    exact h
  have hsum := sum_le_sum fun k₀ (_ : k₀ ∈ (univ : Finset (Fin 9))) =>
    sum_le_sum fun i₀ (_ : i₀ ∈ (univ : Finset (Fin 6))) => hb k₀ i₀
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum] at hsum
  have eB : ∑ k₀ : Fin 9, ∑ i₀ : Fin 6, (((∏ j, genP (Cn k k₀ i₀ j) (sa (sigI k)) (sb (sigI k))).eval 1 : ℕ) : ℤ) =
      ((Pnear k).eval 1 : ℕ) := by
    rw [← sum_prod_Cn, eval_finset_sum, Nat.cast_sum]
    refine sum_congr rfl fun k₀ _ => ?_
    rw [eval_finset_sum, Nat.cast_sum]
  have eT : ∀ M : ℕ[X], ∑ k₀ : Fin 9, ∑ i₀ : Fin 6,
      ((((∏ j, genP (Cn k k₀ i₀ j) (sa (sigI k)) (sb (sigI k))) * M).coeff Ntop : ℕ) : ℤ) =
      (((Pnear k * M).coeff Ntop : ℕ) : ℤ) := by
    intro M
    rw [← sum_prod_Cn, sum_mul, finset_sum_coeff, Nat.cast_sum]
    refine sum_congr rfl fun k₀ _ => ?_
    rw [sum_mul, finset_sum_coeff, Nat.cast_sum]
  rw [eB, eT, eT] at hsum
  rw [extract _ B (by rw [eval_mul, Mask_eval_one]; exact hok') Ntop,
    extract _ B (by rw [eval_mul, Mask_eval_one]; exact hok2) Ntop, eval_mul, eval_mul, ← maskV_eq, ← maskV_eq,
    Pnear_eval, Pnear_eval] at hsum
  unfold bonfNearN bonfN
  apply nat_bound
  push_cast at hsum ⊢
  linarith

abbrev Item2 (k : ℕ) := (Cell × Cell) × (Fin (k + 2) → Cell)

def tr2 (k : ℕ) : (Fin 9 → Item2 k) ≃ (Fin (k + 2) → Coords) × (Coords × Coords) :=
  (coordEquiv (Cell × Cell) (k + 2) Cell).trans
    ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (pairEquiv Cell)))

def sig2 (k : ℕ) (y : Item2 k) : Fin (k + 2) → Cell := y.2

theorem tr2_he (k : ℕ) : ∀ (x : Fin 9 → Item2 k) m j, (tr2 k x).1 m j = sig2 k (x j) m := fun _ _ _ => rfl

def Ycov2 (k : ℕ) : Finset (Item2 k) :=
  univ.filter fun y => CovAtM wordDigit (fun _ => false) y.1.1.1 (wordDigit y.1.1.2) y.2 ∧
    CovAtM wordDigit (fun _ => false) y.1.2.1 (wordDigit y.1.2.2) y.2

theorem htr_diag (k : ℕ) (x : Fin 9 → Item2 k) :
    (ListCov wordDigit (List.ofFn (tr2 k x).1) (tr2 k x).2.1 ∧ ListCov wordDigit (List.ofFn (tr2 k x).1) (tr2 k x).2.2) ↔
      ∀ j, x j ∈ (fun _ : Fin 9 => Ycov2 k) j := by
  rw [listCov_ofFn, listCov_ofFn]
  unfold FullCov
  simp only [Ycov2, mem_filter, mem_univ, true_and, covAtM_iff, ← forall_and]
  rfl

theorem diag_perm (k : ℕ) (σ : Equiv.Perm (Fin (k + 2))) (E : Fin (k + 2) → Coords) (t : Coords × Coords) :
    (ListCov wordDigit (List.ofFn (E ∘ σ)) t.1 ∧ ListCov wordDigit (List.ofFn (E ∘ σ)) t.2) ↔
      (ListCov wordDigit (List.ofFn E) t.1 ∧ ListCov wordDigit (List.ofFn E) t.2) := by
  rw [ClaudeR3.Law.listCov_perm, ClaudeR3.Law.listCov_perm]

section
variable {R : Type*} [CommRing R]

theorem sum_Ycov2 (k L : ℕ) (x : R) :
    ∑ y ∈ Ycov2 k, x ^ sa (sig2 k) y * (x ^ L) ^ sb (sig2 k) y = Ws k L x + ClaudeR3.Diff.Wd k L x := by
  set G : Child → Child → R := fun c c' => ∑ ab : Rank × Rank, ∑ E : Fin (k + 2) → Cell,
    if CovAtM wordDigit (fun _ => false) c (wordDigit ab.1) E ∧ CovAtM wordDigit (fun _ => false) c' (wordDigit ab.2) E
    then ∏ m, wt k L x m (E m) else 0 with hG
  have hL : ∑ y ∈ Ycov2 k, x ^ sa (sig2 k) y * (x ^ L) ^ sb (sig2 k) y = ∑ c : Child, ∑ c' : Child, G c c' := by
    unfold Ycov2
    rw [sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [hG]
    dsimp only
    rw [sum_congr rfl fun c _ => sum_comm]
    refine sum_congr rfl fun c _ => sum_congr rfl fun c' _ => ?_
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => sum_congr rfl fun a' _ => sum_congr rfl fun E _ => ?_
    simp only [sa, sb, sig2]
    split_ifs
    · rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp [wt]
    · rfl
  have hsplit : ∀ c : Child, ∑ c' : Child, G c c' = G c c + ∑ c' : Child, (if c = c' then 0 else G c c') := by
    intro c
    rw [← add_sum_erase _ _ (mem_univ c), ← add_sum_erase (univ : Finset Child) _ (mem_univ c), if_pos rfl,
      zero_add]
    refine congrArg (G c c + ·) (sum_congr rfl fun c' hc' => ?_)
    rw [if_neg (Ne.symm (ne_of_mem_erase hc'))]
  rw [hL, sum_congr rfl fun c _ => hsplit c, sum_add_distrib]
  unfold Ws ClaudeR3.Diff.Wd
  rfl

end

theorem genP_Ycov2 (k B : ℕ) :
    (((genP (Ycov2 k) (sa (sig2 k)) (sb (sig2 k))).eval B : ℕ) : ℤ) = Ws k 154 (B : ℤ) + ClaudeR3.Diff.Wd k 154 (B : ℤ) := by
  rw [← sum_Ycov2]
  unfold genP
  rw [eval_finset_sum, Nat.cast_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [eval_pow, eval_X]
  push_cast
  ring

def Wv2 (k B : ℕ) : ℕ := (famEval tabS k 154 (B : ℤ) + ClaudeR3.Diff.famEvalD tabM k 154 (B : ℤ)).toNat

theorem genP_eval_Wv2 (k B : ℕ) : (genP (Ycov2 k) (sa (sig2 k)) (sb (sig2 k))).eval B = Wv2 k B := by
  have h := genP_Ycov2 k B
  rw [Ws_table, ClaudeR3.Diff.Wd_table, famEval_eq, ClaudeR3.Diff.famEvalD_eq] at h
  unfold Wv2
  rw [← h, Int.toNat_natCast]

def bonfDiagN (k A r' B : ℕ) : ℕ := bonfN (Wv2 k 1 ^ 9) (Wv2 k B ^ 9) A r' B

def diagOk (k A B : ℕ) : Bool := Wv2 k 1 ^ 9 * ((153 - A) * 154) < B

theorem diag_bound (k A r' B : ℕ) (hA : A < 153) (hr' : r' ≤ k + 2) (hok : diagOk k A B = true) :
    #{p : (Fin (k + 2) → Coords) × (Coords × Coords) | (∀ m, p.1 m ∈ capS (675 + A)) ∧
        (ListCov wordDigit (List.ofFn p.1) p.2.1 ∧ ListCov wordDigit (List.ofFn p.1) p.2.2)} ≤
      bonfDiagN k A r' B := by
  have h := gen_bound (tr2 k) (sig2 k) (tr2_he k)
    (fun p => ListCov wordDigit (List.ofFn p.1) p.2.1 ∧ ListCov wordDigit (List.ofFn p.1) p.2.2) (fun _ => Ycov2 k)
    (htr_diag k) (fun σ E t => diag_perm k σ E t) A r' B hA hr'
    (by rw [prod_const9, eval_pow, genP_eval_Wv2]; simpa [diagOk] using hok)
  rw [prod_const9, eval_pow, eval_pow, genP_eval_Wv2, genP_eval_Wv2] at h
  exact h

end ClaudeR3.Asm
end
