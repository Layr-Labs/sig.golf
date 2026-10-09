import SigGolfCandidate.ClaudeR3.P5
import SigGolfCandidate.ClaudeR3.Q6
import SigGolfCandidate.ClaudeR3.Q3
import SigGolfCandidate.ClaudeWCT.Numerics.N600CapCount

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
