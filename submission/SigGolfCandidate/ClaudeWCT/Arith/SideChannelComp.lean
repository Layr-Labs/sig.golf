import SigGolfCandidate.ClaudeWCT.Arith.SideChannel
import VCVio.OracleComp.ProbComp

/-!
# Side channel of test programs with coins (campaign X1, stage B, item B1')

`tree_mass_le` for oracle programs `OracleComp (TSpec ι V) α` that interleave uniform coins (`unifSpec`) and
equality tests on a hidden vector `y : ι → V`. The semantics are given by structural recursion
(`OracleComp.construct`):

* `prT y A p`: probability that `p`, run against `y` (coins uniform), returns a result in `A`;
* `tdepth p`: the largest number of tests on a path;
* `amLen p`: expected number of tests when every test answers "miss" (the all-miss run);
* `enT y p`: expected number of tests in the run against `y`.

Main results (laws `P`, `Q` with uniform 3-wise marginals, `δ = |V|^-3`, `δ₁ = |V|^-1`, `tdepth p ≤ D`):

* `comp_mass_le`: `P(A) ≤ Q(A) + 2 δ K(D) · amLen p` with `K(D) = C(3D, 2) + C(D, 2)`;
* `amLen_le_enT`: `amLen p · (1 - δ₁ D) ≤ E_P[number of tests]`.

So the separation is charged to the expected number of tests actually made, which is summable over independent
families (one per lower WOTS leaf).
-/

namespace ClaudeWCT.Arith.SideChannel

open OracleComp OracleSpec Finset

variable {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- Programs with uniform coins and equality tests on `y : ι → V`. -/
abbrev TSpec (ι V : Type) : OracleSpec (ℕ ⊕ (ι × V)) := unifSpec + ((ι × V) →ₒ Bool)

section Semantics
variable {α : Type}

/-- Probability that `p`, run against `y`, returns a result in `A`. -/
noncomputable def prT (y : ι → V) (A : α → Prop) : OracleComp (TSpec ι V) α → ℝ :=
  OracleComp.construct (C := fun _ => ℝ) (fun a => by classical exact if A a then 1 else 0)
    (fun t _ r => match t, r with
      | .inl n, r => (∑ u : Fin (n + 1), r u) / (n + 1)
      | .inr p, r => by classical exact r (decide (y p.1 = p.2)))

/-- Largest number of tests on a path. -/
noncomputable def tdepth : OracleComp (TSpec ι V) α → ℕ :=
  OracleComp.construct (C := fun _ => ℕ) (fun _ => 0)
    (fun t _ r => match t, r with
      | .inl _, r => univ.sup r
      | .inr _, r => max (r true) (r false) + 1)

/-- Expected number of tests when every test answers "miss". -/
noncomputable def amLen : OracleComp (TSpec ι V) α → ℝ :=
  OracleComp.construct (C := fun _ => ℝ) (fun _ => 0)
    (fun t _ r => match t, r with
      | .inl n, r => (∑ u : Fin (n + 1), r u) / (n + 1)
      | .inr _, r => r false + 1)

/-- Expected number of tests in the run against `y`. -/
noncomputable def enT (y : ι → V) : OracleComp (TSpec ι V) α → ℝ :=
  OracleComp.construct (C := fun _ => ℝ) (fun _ => 0)
    (fun t _ r => match t, r with
      | .inl n, r => (∑ u : Fin (n + 1), r u) / (n + 1)
      | .inr p, r => by classical exact r (decide (y p.1 = p.2)) + 1)

/-- Query a coin. -/
def coinQ (n : ℕ) : OracleComp (TSpec ι V) (Fin (n + 1)) := liftM ((TSpec ι V).query (.inl n))
/-- Query a test. -/
def testQ (p : ι × V) : OracleComp (TSpec ι V) Bool := liftM ((TSpec ι V).query (.inr p))

theorem prT_pure (y : ι → V) (A : α → Prop) (a : α) :
    prT y A (pure a : OracleComp (TSpec ι V) α) = by classical exact if A a then 1 else 0 := rfl
theorem prT_coin (y : ι → V) (A : α → Prop) (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    prT y A (coinQ n >>= k) = (∑ u : Fin (n + 1), prT y A (k u)) / (n + 1) := rfl
theorem prT_test (y : ι → V) (A : α → Prop) (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    prT y A (testQ p >>= k) = by classical exact prT y A (k (decide (y p.1 = p.2))) := rfl
theorem tdepth_pure (a : α) : tdepth (pure a : OracleComp (TSpec ι V) α) = 0 := rfl
theorem tdepth_coin (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    tdepth (coinQ n >>= k) = univ.sup fun u => tdepth (k u) := rfl
theorem tdepth_test (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    tdepth (testQ p >>= k) = max (tdepth (k true)) (tdepth (k false)) + 1 := rfl
theorem amLen_pure (a : α) : amLen (pure a : OracleComp (TSpec ι V) α) = 0 := rfl
theorem amLen_coin (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    amLen (coinQ n >>= k) = (∑ u : Fin (n + 1), amLen (k u)) / (n + 1) := rfl
theorem amLen_test (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    amLen (testQ p >>= k) = amLen (k false) + 1 := rfl
theorem enT_pure (y : ι → V) (a : α) : enT y (pure a : OracleComp (TSpec ι V) α) = 0 := rfl
theorem enT_coin (y : ι → V) (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    enT y (coinQ n >>= k) = (∑ u : Fin (n + 1), enT y (k u)) / (n + 1) := rfl
theorem enT_test (y : ι → V) (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    enT y (testQ p >>= k) = by classical exact enT y (k (decide (y p.1 = p.2))) + 1 := rfl

/-- Induction principle splitting queries into coins and tests. -/
theorem tinduction {C : OracleComp (TSpec ι V) α → Prop} (pure : ∀ a, C (pure a))
    (coin : ∀ n (k : Fin (n + 1) → OracleComp (TSpec ι V) α), (∀ u, C (k u)) → C (coinQ n >>= k))
    (test : ∀ p (k : Bool → OracleComp (TSpec ι V) α), (∀ b, C (k b)) → C (testQ p >>= k))
    (oa : OracleComp (TSpec ι V) α) : C oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact pure a
  | query_bind t k ih =>
      rcases t with n | p
      · exact coin n k ih
      · exact test p k ih

theorem prT_nonneg (y : ι → V) (A : α → Prop) (oa : OracleComp (TSpec ι V) α) : 0 ≤ prT y A oa := by
  induction oa using tinduction with
  | pure a => rw [prT_pure]; split <;> norm_num
  | coin n k ih => rw [prT_coin]; exact div_nonneg (sum_nonneg fun u _ => ih u) (by positivity)
  | test p k ih => rw [prT_test]; exact ih _

theorem prT_le_one (y : ι → V) (A : α → Prop) (oa : OracleComp (TSpec ι V) α) : prT y A oa ≤ 1 := by
  induction oa using tinduction with
  | pure a => rw [prT_pure]; split <;> norm_num
  | coin n k ih =>
      rw [prT_coin, div_le_one (by positivity)]
      calc (∑ u : Fin (n + 1), prT y A (k u)) ≤ ∑ _u : Fin (n + 1), (1 : ℝ) := sum_le_sum fun u _ => ih u
        _ = n + 1 := by simp
  | test p k ih => rw [prT_test]; exact ih _

theorem amLen_nonneg (oa : OracleComp (TSpec ι V) α) : 0 ≤ amLen oa := by
  induction oa using tinduction with
  | pure a => rw [amLen_pure]
  | coin n k ih => rw [amLen_coin]; exact div_nonneg (sum_nonneg fun u _ => ih u) (by positivity)
  | test p k ih => rw [amLen_test]; linarith [ih false]

theorem amLen_le_tdepth (oa : OracleComp (TSpec ι V) α) : amLen oa ≤ tdepth oa := by
  induction oa using tinduction with
  | pure a => rw [amLen_pure, tdepth_pure]; simp
  | coin n k ih =>
      rw [amLen_coin, tdepth_coin, div_le_iff₀ (by positivity)]
      calc (∑ u : Fin (n + 1), amLen (k u)) ≤ ∑ _u : Fin (n + 1), ((univ.sup fun u => tdepth (k u) : ℕ) : ℝ) :=
            sum_le_sum fun u _ => (ih u).trans (by exact_mod_cast le_sup (f := fun u => tdepth (k u)) (mem_univ u))
        _ = _ := by simp; ring
  | test p k ih =>
      rw [amLen_test, tdepth_test]
      have h1 := ih false
      have h2 : ((tdepth (k false) + 1 : ℕ) : ℝ) ≤ ((max (tdepth (k true)) (tdepth (k false)) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show tdepth (k false) + 1 ≤ max (tdepth (k true)) (tdepth (k false)) + 1 by omega)
      push_cast at h2 ⊢
      linarith

end Semantics

/-! ### Mass of a context times the success probability -/

section Bound
variable (P Q : (ι → V) → ℝ) (δ : ℝ)
variable {α : Type} (A : α → Prop)

/-- `Σ_y R y · 1{Ctx y H M} · prT y A p`. -/
noncomputable def cmass (R : (ι → V) → ℝ) (H M : Finset (ι × V)) (oa : OracleComp (TSpec ι V) α) : ℝ :=
  by classical exact ∑ y, (if Ctx y H M then R y else 0) * prT y A oa

theorem cmass_pure (R : (ι → V) → ℝ) (H M : Finset (ι × V)) (a : α) :
    cmass A R H M (pure a) = by classical exact if A a then mass R (fun y => Ctx y H M) else 0 := by
  classical
  unfold cmass mass
  split_ifs with ha
  · refine sum_congr rfl fun y _ => ?_
    rw [prT_pure, if_pos ha, mul_one]
  · refine sum_eq_zero fun y _ => ?_
    rw [prT_pure, if_neg ha, mul_zero]

theorem cmass_coin (R : (ι → V) → ℝ) (H M : Finset (ι × V)) (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    cmass A R H M (coinQ n >>= k) = (∑ u : Fin (n + 1), cmass A R H M (k u)) / (n + 1) := by
  classical
  unfold cmass
  simp only [prT_coin, mul_div_assoc', ← sum_div, mul_sum]
  rw [sum_comm]

theorem cmass_test (R : (ι → V) → ℝ) (H M : Finset (ι × V)) (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    cmass A R H M (testQ p >>= k) = cmass A R (insert p H) M (k true) + cmass A R H (insert p M) (k false) := by
  classical
  unfold cmass
  rw [← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [prT_test]
  by_cases hy : y p.1 = p.2
  · have h1 : Ctx y (insert p H) M ↔ Ctx y H M := by rw [ctx_insert_hit]; simp [hy]
    have h2 : ¬Ctx y H (insert p M) := by rw [ctx_insert_miss]; simp [hy]
    simp only [hy, decide_true, h1, h2, if_false, zero_mul, add_zero]
  · have h1 : ¬Ctx y (insert p H) M := by rw [ctx_insert_hit]; simp [hy]
    have h2 : Ctx y H (insert p M) ↔ Ctx y H M := by rw [ctx_insert_miss]; simp [hy]
    simp only [hy, decide_false, h1, h2, if_false, zero_mul, zero_add]

theorem cmass_nonneg (R : (ι → V) → ℝ) (hR : ∀ y, 0 ≤ R y) (H M : Finset (ι × V)) (oa : OracleComp (TSpec ι V) α) :
    0 ≤ cmass A R H M oa := by
  classical
  unfold cmass
  exact sum_nonneg fun y _ => mul_nonneg (by split <;> simp [hR y]) (prT_nonneg y A oa)

theorem cmass_le_mass (R : (ι → V) → ℝ) (hR : ∀ y, 0 ≤ R y) (H M : Finset (ι × V)) (oa : OracleComp (TSpec ι V) α) :
    cmass A R H M oa ≤ mass R (fun y => Ctx y H M) := by
  classical
  unfold cmass mass
  refine sum_le_sum fun y _ => ?_
  have h1 := prT_le_one y A oa
  have h0 := prT_nonneg y A oa
  split_ifs
  · nlinarith [hR y]
  · simp

theorem cmass_eq_zero (R : (ι → V) → ℝ) (H M : Finset (ι × V)) (oa : OracleComp (TSpec ι V) α)
    (h : ∀ y, ¬Ctx y H M) : cmass A R H M oa = 0 := by
  classical
  unfold cmass
  exact sum_eq_zero fun y _ => by rw [if_neg (h y), zero_mul]

variable (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) (hδ : 0 ≤ δ)
  (h2 : ∀ S : Finset (ι × V), S.card ≤ 2 → mass P (fun y => AllHit y S) = mass Q (fun y => AllHit y S))
  (h3P : ∀ S : Finset (ι × V), S.card = 3 → mass P (fun y => AllHit y S) ≤ δ)
  (h3Q : ∀ S : Finset (ι × V), S.card = 3 → mass Q (fun y => AllHit y S) ≤ δ)
include hP hQ hδ h2 h3P h3Q

/-- Depth bound for every context: `2 δ C(|M| + 2 · tdepth, 3 - |H|)`. -/
theorem comp_ctx_le : ∀ (oa : OracleComp (TSpec ι V) α) (H M : Finset (ι × V)),
    cmass A P H M oa ≤ cmass A Q H M oa + 2 * δ * ((M.card + 2 * tdepth oa).choose (3 - H.card) : ℝ) := by
  classical
  have big : ∀ (oa : OracleComp (TSpec ι V) α) (H M : Finset (ι × V)), 3 ≤ H.card →
      cmass A P H M oa ≤ cmass A Q H M oa + 2 * δ * ((M.card + 2 * tdepth oa).choose (3 - H.card) : ℝ) := by
    intro oa H M hH
    obtain ⟨S, hSH, hS⟩ := Finset.exists_subset_card_eq hH
    have hle : cmass A P H M oa ≤ δ :=
      (cmass_le_mass A P hP H M oa).trans ((mass_mono P hP fun y hy p hp => hy.1 p (hSH hp)).trans (h3P S hS))
    have hq := cmass_nonneg A Q hQ H M oa
    rw [show 3 - H.card = 0 by omega, Nat.choose_zero_right, Nat.cast_one, mul_one]
    linarith
  intro oa
  induction oa using tinduction with
  | pure a =>
      intro H M
      by_cases hH : 3 ≤ H.card
      · exact big _ H M hH
      rw [cmass_pure, cmass_pure, tdepth_pure]
      split_ifs with ha
      · simpa using ctx_mass_le P Q δ hP hQ hδ h2 h3P h3Q H M (by omega)
      · have : 0 ≤ 2 * δ * ((M.card + 2 * 0).choose (3 - H.card) : ℝ) := by positivity
        linarith
  | coin n k ih =>
      intro H M
      rw [cmass_coin, cmass_coin, tdepth_coin]
      have hmono : ∀ u, ((M.card + 2 * tdepth (k u)).choose (3 - H.card) : ℝ) ≤
          ((M.card + 2 * univ.sup fun u => tdepth (k u)).choose (3 - H.card) : ℝ) := fun u => by
        exact_mod_cast Nat.choose_le_choose _ (by
          have := le_sup (f := fun u => tdepth (k u)) (mem_univ u); omega)
      rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
      calc (∑ u : Fin (n + 1), cmass A P H M (k u))
          ≤ ∑ u : Fin (n + 1), (cmass A Q H M (k u) + 2 * δ *
              ((M.card + 2 * univ.sup fun u => tdepth (k u)).choose (3 - H.card) : ℝ)) :=
            sum_le_sum fun u _ => (ih u H M).trans (by nlinarith [hmono u])
        _ = _ := by rw [sum_add_distrib]; simp; ring
  | test p k ih =>
      intro H M
      by_cases hH : 3 ≤ H.card
      · exact big _ H M hH
      rw [cmass_test, cmass_test, tdepth_test]
      set d := max (tdepth (k true)) (tdepth (k false))
      have mono : ∀ {a b : ℕ} (c : ℕ), a ≤ b → ((a.choose c : ℕ) : ℝ) ≤ (b.choose c : ℝ) :=
        fun c hab => by exact_mod_cast Nat.choose_le_choose c hab
      have hδ2 : 0 ≤ 2 * δ := by linarith
      have qt := cmass_nonneg A Q hQ (insert p H) M (k true)
      have qf := cmass_nonneg A Q hQ H (insert p M) (k false)
      by_cases hpH : p ∈ H
      · rw [Finset.insert_eq_of_mem hpH] at qt ⊢
        rw [cmass_eq_zero A P H (insert p M) (k false) (fun y hy =>
          ((ctx_insert_miss y H M p).mp hy).2 (hy.1 p hpH))]
        have ht := ih true H M
        have hm := mono (3 - H.card) (show M.card + 2 * tdepth (k true) ≤ M.card + 2 * (d + 1) by omega)
        nlinarith [mul_le_mul_of_nonneg_left hm hδ2]
      by_cases hpM : p ∈ M
      · rw [Finset.insert_eq_of_mem hpM] at qf ⊢
        rw [cmass_eq_zero A P (insert p H) M (k true) (fun y hy =>
          (hy.2 p hpM) ((ctx_insert_hit y H M p).mp hy).2)]
        have hf := ih false H M
        have hm := mono (3 - H.card) (show M.card + 2 * tdepth (k false) ≤ M.card + 2 * (d + 1) by omega)
        nlinarith [mul_le_mul_of_nonneg_left hm hδ2]
      · have ht := ih true (insert p H) M
        have hf := ih false H (insert p M)
        rw [Finset.card_insert_of_notMem hpH] at ht
        rw [Finset.card_insert_of_notMem hpM] at hf
        obtain ⟨j, hj⟩ : ∃ j, 3 - H.card = j + 1 := ⟨3 - H.card - 1, by omega⟩
        rw [show 3 - (H.card + 1) = j by omega] at ht
        rw [hj] at hf ⊢
        have m1 := mono j (show M.card + 2 * tdepth (k true) ≤ M.card + 2 * d by omega)
        have m2 := mono (j + 1) (show M.card + 1 + 2 * tdepth (k false) ≤ M.card + 2 * d + 1 by omega)
        have pascal : ((M.card + 2 * d).choose j : ℝ) + ((M.card + 2 * d + 1).choose (j + 1) : ℝ) ≤
            ((M.card + 2 * (d + 1)).choose (j + 1) : ℝ) := by
          have hn : (M.card + 2 * d).choose j + (M.card + 2 * d + 1).choose (j + 1) ≤
              (M.card + 2 * (d + 1)).choose (j + 1) := by
            rw [show M.card + 2 * (d + 1) = (M.card + 2 * d + 1) + 1 by ring,
              Nat.choose_succ_succ' (M.card + 2 * d + 1) j]
            have : (M.card + 2 * d).choose j ≤ (M.card + 2 * d + 1).choose j := Nat.choose_le_choose j (by omega)
            omega
          exact_mod_cast hn
        have e1 := mul_le_mul_of_nonneg_left m1 hδ2
        have e2 := mul_le_mul_of_nonneg_left m2 hδ2
        have e3 := mul_le_mul_of_nonneg_left pascal hδ2
        nlinarith

/-- The constant of the all-miss bound. -/
def kconst (D : ℕ) : ℕ := (3 * D).choose 2 + D.choose 2

/-- All-miss bound: `2 δ (C(|M|, 3) + K(D) · amLen)` for programs with `|M| + tdepth ≤ D`. -/
theorem comp_ctx_le_am (D : ℕ) : ∀ (oa : OracleComp (TSpec ι V) α) (M : Finset (ι × V)),
    M.card + tdepth oa ≤ D →
    cmass A P ∅ M oa ≤ cmass A Q ∅ M oa + 2 * δ * ((M.card.choose 3 : ℝ) + kconst D * amLen oa) := by
  classical
  intro oa
  have hK0 : (0 : ℝ) ≤ kconst D := Nat.cast_nonneg _
  induction oa using tinduction with
  | pure a =>
      intro M _
      have h := comp_ctx_le P Q δ A hP hQ hδ h2 h3P h3Q (pure a) ∅ M
      rw [tdepth_pure] at h
      rw [amLen_pure]
      simpa using h
  | coin n k ih =>
      intro M hD
      rw [cmass_coin, cmass_coin, amLen_coin, tdepth_coin] at *
      have hD' : ∀ u, M.card + tdepth (k u) ≤ D := fun u => by
        have := le_sup (f := fun u => tdepth (k u)) (mem_univ u); omega
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hB : (∑ u : Fin (n + 1), 2 * δ * ((M.card.choose 3 : ℝ) + kconst D * amLen (k u))) =
          2 * δ * (((n : ℝ) + 1) * (M.card.choose 3 : ℝ) + kconst D * ∑ u, amLen (k u)) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum]
        simp [card_univ]
      calc (∑ u : Fin (n + 1), cmass A P ∅ M (k u)) / (n + 1)
          ≤ (∑ u : Fin (n + 1), (cmass A Q ∅ M (k u) + 2 * δ * ((M.card.choose 3 : ℝ) + kconst D * amLen (k u)))) /
              (n + 1) :=
            div_le_div_of_nonneg_right (sum_le_sum fun u _ => ih u M (hD' u)) hn.le
        _ = _ := by
          rw [sum_add_distrib, add_div, hB]
          congr 1
          field_simp
  | test p k ih =>
      intro M hD
      rw [cmass_test, cmass_test, amLen_test]
      rw [tdepth_test] at hD
      have hδ2 : 0 ≤ 2 * δ := by linarith
      have qt := cmass_nonneg A Q hQ (insert p ∅) M (k true)
      have qf := cmass_nonneg A Q hQ ∅ (insert p M) (k false)
      have hal := amLen_nonneg (k false)
      have hc3 : (0 : ℝ) ≤ (M.card.choose 3 : ℝ) := Nat.cast_nonneg _
      by_cases hpM : p ∈ M
      · rw [Finset.insert_eq_of_mem hpM] at qf ⊢
        rw [cmass_eq_zero A P (insert p ∅) M (k true) (fun y hy =>
          (hy.2 p hpM) ((ctx_insert_hit y ∅ M p).mp hy).2)]
        have hf := ih false M (by omega)
        nlinarith [mul_nonneg hδ2 hK0]
      · -- hit branch: one hit, depth bound; miss branch: induction with one more miss
        have ht := comp_ctx_le P Q δ A hP hQ hδ h2 h3P h3Q (k true) (insert p ∅) M
        have hf := ih false (insert p M) (by rw [Finset.card_insert_of_notMem hpM]; omega)
        rw [Finset.card_insert_of_notMem hpM] at hf
        simp only [Finset.insert_empty, Finset.card_singleton] at ht ⊢
        have hm := (show ((M.card + 2 * tdepth (k true)).choose (3 - 1) : ℝ) ≤ ((3 * D).choose 2 : ℝ) by
          exact_mod_cast Nat.choose_le_choose 2 (by omega))
        have hs : ((M.card + 1).choose 3 : ℝ) = (M.card.choose 3 : ℝ) + (M.card.choose 2 : ℝ) := by
          rw [Nat.choose_succ_succ' M.card 2]; push_cast; ring
        have hm2 : (M.card.choose 2 : ℝ) ≤ (D.choose 2 : ℝ) := by
          exact_mod_cast Nat.choose_le_choose 2 (by omega)
        have hk : ((3 * D).choose 2 : ℝ) + (D.choose 2 : ℝ) = kconst D := by unfold kconst; push_cast; ring
        rw [hs] at hf
        have e1 := mul_le_mul_of_nonneg_left hm hδ2
        have e2 := mul_le_mul_of_nonneg_left hm2 hδ2
        nlinarith [mul_nonneg hδ2 hK0]

/-- **Side channel of test programs.** -/
theorem comp_mass_le (D : ℕ) (oa : OracleComp (TSpec ι V) α) (hD : tdepth oa ≤ D) :
    (by classical exact ∑ y, P y * prT y A oa) ≤
      (by classical exact ∑ y, Q y * prT y A oa) + 2 * δ * kconst D * amLen oa := by
  classical
  have h := comp_ctx_le_am P Q δ A hP hQ hδ h2 h3P h3Q D oa ∅ (by simpa using hD)
  have e : ∀ R : (ι → V) → ℝ, cmass A R ∅ ∅ oa = ∑ y, R y * prT y A oa := fun R => by
    unfold cmass
    refine sum_congr rfl fun y _ => ?_
    rw [if_pos (by simp [Ctx, AllHit])]
  rw [e P, e Q] at h
  simpa [mul_assoc] using h

end Bound

/-! ### The all-miss length against the actual number of tests -/

section Count
variable (P : (ι → V) → ℝ) (δ₁ : ℝ)
variable {α : Type}

/-- `Σ_y P y · 1{Ctx y ∅ M} · enT y p`. -/
noncomputable def cnt (M : Finset (ι × V)) (oa : OracleComp (TSpec ι V) α) : ℝ :=
  by classical exact ∑ y, (if Ctx y ∅ M then P y else 0) * enT y oa

theorem enT_nonneg (y : ι → V) (oa : OracleComp (TSpec ι V) α) : 0 ≤ enT y oa := by
  induction oa using tinduction with
  | pure a => rw [enT_pure]
  | coin n k ih => rw [enT_coin]; exact div_nonneg (sum_nonneg fun u _ => ih u) (by positivity)
  | test p k ih => rw [enT_test]; linarith [ih (decide (y p.1 = p.2))]

variable (hP : ∀ y, 0 ≤ P y) (hδ₁ : 0 ≤ δ₁) (h1 : ∀ p : ι × V, mass P (fun y => y p.1 = p.2) ≤ δ₁)
include hP hδ₁ h1

/-- `cnt M p ≥ amLen p · (mass(Ctx ∅ M) - δ₁ · tdepth p)`. -/
theorem cnt_ge : ∀ (oa : OracleComp (TSpec ι V) α) (M : Finset (ι × V)),
    amLen oa * (mass P (fun y => Ctx y ∅ M) - δ₁ * tdepth oa) ≤ cnt P M oa := by
  classical
  intro oa
  induction oa using tinduction with
  | pure a =>
      intro M
      rw [amLen_pure, zero_mul]
      unfold cnt
      exact sum_nonneg fun y _ => mul_nonneg (by split <;> simp [hP y]) (enT_nonneg y _)
  | coin n k ih =>
      intro M
      have hcnt : cnt P M (coinQ n >>= k) = (∑ u : Fin (n + 1), cnt P M (k u)) / (n + 1) := by
        unfold cnt
        simp only [enT_coin, mul_div_assoc', ← sum_div, mul_sum]
        rw [sum_comm]
      rw [hcnt, amLen_coin, tdepth_coin]
      have hmono : ∀ u, mass P (fun y => Ctx y ∅ M) - δ₁ * ((univ.sup fun u => tdepth (k u) : ℕ) : ℝ) ≤
          mass P (fun y => Ctx y ∅ M) - δ₁ * (tdepth (k u) : ℝ) := fun u => by
        have : (tdepth (k u) : ℝ) ≤ ((univ.sup fun u => tdepth (k u) : ℕ) : ℝ) := by
          exact_mod_cast le_sup (f := fun u => tdepth (k u)) (mem_univ u)
        nlinarith
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity), sum_mul]
      exact sum_le_sum fun u _ => (mul_le_mul_of_nonneg_left (hmono u) (amLen_nonneg (k u))).trans (ih u M)
  | test p k ih =>
      intro M
      have hcnt : cnt P M (testQ p >>= k) ≥ mass P (fun y => Ctx y ∅ M) + cnt P (insert p M) (k false) := by
        unfold cnt mass
        rw [← sum_add_distrib]
        refine sum_le_sum fun y _ => ?_
        rw [enT_test]
        have he := enT_nonneg y (k (decide (y p.1 = p.2)))
        by_cases hy : y p.1 = p.2
        · have h2 : ¬Ctx y ∅ (insert p M) := by rw [ctx_insert_miss]; simp [hy]
          simp only [h2, if_false, zero_mul, add_zero]
          split_ifs
          · nlinarith [hP y]
          · simp
        · have h2 : Ctx y ∅ (insert p M) ↔ Ctx y ∅ M := by rw [ctx_insert_miss]; simp [hy]
          simp only [hy, decide_false, h2]
          split_ifs
          · nlinarith [hP y]
          · simp
      have hmass : mass P (fun y => Ctx y ∅ M) - δ₁ ≤ mass P (fun y => Ctx y ∅ (insert p M)) := by
        have hs := mass_split P (fun y => Ctx y ∅ M) (fun y => y p.1 = p.2)
        have hhit : mass P (fun y => Ctx y ∅ M ∧ y p.1 = p.2) ≤ δ₁ :=
          (mass_mono P hP fun y hy => hy.2).trans (h1 p)
        have hmiss : mass P (fun y => Ctx y ∅ M ∧ ¬y p.1 = p.2) = mass P (fun y => Ctx y ∅ (insert p M)) :=
          mass_congr P fun y => by rw [ctx_insert_miss]
        linarith
      have hf := ih false (insert p M)
      rw [amLen_test, tdepth_test]
      have hal := amLen_nonneg (k false)
      have hdf : ((tdepth (k false) + 1 : ℕ) : ℝ) ≤ ((max (tdepth (k true)) (tdepth (k false)) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show tdepth (k false) + 1 ≤ max (tdepth (k true)) (tdepth (k false)) + 1 by omega)
      set Dp : ℝ := ((max (tdepth (k true)) (tdepth (k false)) + 1 : ℕ) : ℝ)
      set d' : ℝ := (tdepth (k false) : ℝ)
      push_cast at hdf
      have hm0 := mass_nonneg P hP (fun y => Ctx y ∅ M)
      have hD0 : 0 ≤ Dp := by positivity
      have k1 : 0 ≤ amLen (k false) * (mass P (fun y => Ctx y ∅ (insert p M)) - (mass P (fun y => Ctx y ∅ M) - δ₁)) :=
        mul_nonneg hal (by linarith)
      have k2 : 0 ≤ amLen (k false) * (δ₁ * (Dp - d' - 1)) := mul_nonneg hal (mul_nonneg hδ₁ (by linarith))
      have k3 : 0 ≤ δ₁ * Dp := mul_nonneg hδ₁ hD0
      nlinarith

/-- **All-miss length against the actual number of tests:** `amLen p · (mass P - δ₁ · tdepth p) ≤ E_P[#tests]`. -/
theorem amLen_le_enT (oa : OracleComp (TSpec ι V) α) :
    amLen oa * (mass P (fun _ => True) - δ₁ * tdepth oa) ≤ (by classical exact ∑ y, P y * enT y oa) := by
  classical
  have h := cnt_ge P δ₁ hP hδ₁ h1 oa ∅
  have e1 : mass P (fun y => Ctx y ∅ ∅) = mass P (fun _ => True) := mass_congr P fun y => by simp [Ctx, AllHit]
  have e2 : cnt P ∅ oa = ∑ y, P y * enT y oa := by
    unfold cnt
    refine sum_congr rfl fun y _ => ?_
    rw [if_pos (by simp [Ctx, AllHit])]
  rw [e1, e2] at h
  exact h

end Count
end ClaudeWCT.Arith.SideChannel
