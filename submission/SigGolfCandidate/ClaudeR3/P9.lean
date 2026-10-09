import SigGolfCandidate.ClaudeR3.P8
import SigGolfCandidate.ClaudeR3.P7

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
