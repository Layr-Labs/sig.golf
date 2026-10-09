import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Side channel of adaptive equality tests (campaign X1, stage B, item B1)

A hidden vector `y : ι → V` is drawn from one of two laws `P`, `Q` (real weights). An adaptive strategy is a
decision tree `Tree ι V α` whose inner nodes test `y i = v` and branch on the answer. If the two laws agree on
every event "at most two tests all hit" (`h2`) and every event "three tests all hit" has mass at most `δ` under
both laws (`h3P`, `h3Q`), then for every set `A` of results

  `P(run ∈ A) ≤ Q(run ∈ A) + 2 δ · C(2 · depth, 3)`        (`tree_mass_le`).

Proof: induction on the tree, carrying the sets `H` / `M` of tests answered "hit" / "miss" on the current path,
with the bound `2 δ · C(|M| + 2 r, 3 - |H|)` (`r` = remaining depth). At a leaf this is the third Bonferroni
term relative to `H` (`ctx_mass_le`); at a test node it is Pascal's rule. For the lower WOTS seed families the
two laws are "seed of chain `a` from the family" and "seed of chain `a` independent", with `δ = 2^-384`
(DESIGN-A-SEC §5 Stage B, side channel).
-/

namespace ClaudeWCT.Arith.SideChannel

open Finset

variable {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- All tests of `S` hit `y`. -/
def AllHit (y : ι → V) (S : Finset (ι × V)) : Prop := ∀ p ∈ S, y p.1 = p.2

/-- The path context: every test of `H` hit and every test of `M` missed. -/
def Ctx (y : ι → V) (H M : Finset (ι × V)) : Prop := AllHit y H ∧ ∀ p ∈ M, y p.1 ≠ p.2

/-- Mass of an event under a weight function. -/
noncomputable def mass (P : (ι → V) → ℝ) (E : (ι → V) → Prop) : ℝ :=
  by classical exact ∑ y, if E y then P y else 0

/-- Adaptive equality-test strategies. -/
inductive Tree (ι V α : Type) where
  | leaf : α → Tree ι V α
  | test : ι × V → (Bool → Tree ι V α) → Tree ι V α

namespace Tree
variable {α : Type}

/-- Run a strategy against the hidden vector `y`. -/
def run (y : ι → V) : Tree ι V α → α
  | leaf a => a
  | test p k => (k (decide (y p.1 = p.2))).run y

/-- Number of tests on the longest path. -/
def depth : Tree ι V α → Nat
  | leaf _ => 0
  | test _ k => max (k true).depth (k false).depth + 1

end Tree

section Mass
variable (P : (ι → V) → ℝ)

theorem mass_congr {E F : (ι → V) → Prop} (h : ∀ y, E y ↔ F y) : mass P E = mass P F := by
  classical
  unfold mass
  exact Finset.sum_congr rfl fun y _ => by simp only [h y]

theorem mass_nonneg (hP : ∀ y, 0 ≤ P y) (E : (ι → V) → Prop) : 0 ≤ mass P E := by
  classical
  unfold mass
  exact Finset.sum_nonneg fun y _ => by split <;> simp [hP y]

theorem mass_mono (hP : ∀ y, 0 ≤ P y) {E F : (ι → V) → Prop} (h : ∀ y, E y → F y) : mass P E ≤ mass P F := by
  classical
  unfold mass
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases hE : E y
  · rw [if_pos hE, if_pos (h y hE)]
  · rw [if_neg hE]
    split <;> simp [hP y]

theorem mass_split (E F : (ι → V) → Prop) :
    mass P E = mass P (fun y => E y ∧ F y) + mass P (fun y => E y ∧ ¬F y) := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hE : E y <;> by_cases hF : F y <;> simp [hE, hF]

theorem mass_false (E : (ι → V) → Prop) (h : ∀ y, ¬E y) : mass P E = 0 := by
  classical
  unfold mass
  exact Finset.sum_eq_zero fun y _ => if_neg (h y)

end Mass

/-! ### Pointwise Bonferroni -/

/-- Truncated alternating binomial sum `∑_{k ≤ r} (-1)^k C(N, k)`. -/
def alt (r N : Nat) : ℝ := ∑ k ∈ range (r + 1), (-1 : ℝ) ^ k * (N.choose k : ℝ)

theorem bonferroni_point (r N : Nat) (hr : r ≤ 2) :
    |(if N = 0 then (1 : ℝ) else 0) - alt r N| ≤ (N.choose (r + 1) : ℝ) := by
  have h2 : (N.choose 2 : ℝ) * 2 = N * (N - 1) := by
    rcases N with _ | N
    · simp
    · push_cast
      have h' : ((N + 1).choose 2 : ℝ) * 2 = (N + 1) * N := by
        have := Nat.choose_mul_succ_eq N 1
        have e := Nat.succ_sub_one N
        rw [show (N + 1).choose 2 = (N + 1).choose (1 + 1) from rfl]
        have key : (N + 1).choose 2 * 2 = (N + 1) * N := by
          rw [Nat.choose_two_right]
          have : 2 ∣ (N + 1) * N := by
            rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
            · exact ⟨(N + 1) * k, by rw [hk]; ring⟩
            · exact ⟨(k + 1) * N, by rw [hk]; ring⟩
          exact Nat.div_mul_cancel this
        exact_mod_cast key
      rw [h']
      ring
  have h3 : (N.choose 3 : ℝ) * 3 = (N.choose 2 : ℝ) * (N - 2) := by
    have e := Nat.choose_succ_right_eq N 2
    rcases Nat.lt_or_ge N 2 with hN | hN
    · interval_cases N <;> simp [Nat.choose_eq_zero_of_lt]
    · have : ((N.choose (2 + 1) * (2 + 1) : ℕ) : ℝ) = (N.choose 2 * (N - 2) : ℕ) := by rw [e]
      push_cast [Nat.cast_sub hN] at this
      linarith
  interval_cases r
  · simp only [alt, zero_add, range_one, sum_singleton, pow_zero, Nat.choose_zero_right, Nat.cast_one,
      mul_one, Nat.choose_one_right]
    rcases N with _ | N
    · simp
    · simp only [Nat.add_one_ne_zero, if_false]; push_cast
      rw [abs_le]; constructor <;> linarith
  · simp only [alt, show (1 + 1 : Nat) = 2 from rfl, sum_range_succ, range_one, sum_singleton, pow_zero,
      Nat.choose_zero_right, Nat.cast_one, one_mul, pow_one, Nat.choose_one_right, neg_mul, one_mul]
    rcases N with _ | N
    · simp
    · simp only [Nat.add_one_ne_zero, if_false]
      push_cast at h2 ⊢
      rw [abs_le]
      rcases N with _ | N
      · simp
      · push_cast at h2 ⊢
        have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        constructor <;> nlinarith
  · simp only [alt, show (2 + 1 : Nat) = 3 from rfl, sum_range_succ, range_one, sum_singleton, pow_zero,
      Nat.choose_zero_right, Nat.cast_one, one_mul, pow_one, Nat.choose_one_right, neg_mul, one_mul]
    rcases N with _ | N
    · simp
    · simp only [Nat.add_one_ne_zero, if_false]
      push_cast at h2 h3 ⊢
      rw [abs_le]
      have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have hc2 : (0 : ℝ) ≤ ((N + 1).choose 2 : ℝ) := Nat.cast_nonneg _
      rcases Nat.lt_or_ge N 2 with hN | hN
      · interval_cases N <;> norm_num
      · have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
        constructor <;> nlinarith

/-! ### Bonferroni for one context -/

/-- Number of tests of `M` that hit `y`. -/
noncomputable def hits (y : ι → V) (M : Finset (ι × V)) : Nat := by
  classical exact (M.filter fun p => y p.1 = p.2).card

theorem choose_hits (y : ι → V) (M : Finset (ι × V)) (k : Nat) :
    ((hits y M).choose k : ℝ) = ∑ J ∈ M.powersetCard k, if AllHit y J then (1 : ℝ) else 0 := by
  classical
  unfold hits
  rw [← Finset.card_powersetCard, Finset.sum_boole]
  congr 1
  congr 1
  ext J
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hJ, hc⟩
    exact ⟨⟨fun p hp => (Finset.mem_filter.mp (hJ hp)).1, hc⟩, fun p hp => (Finset.mem_filter.mp (hJ hp)).2⟩
  · rintro ⟨⟨hJ, hc⟩, hh⟩
    exact ⟨fun p hp => Finset.mem_filter.mpr ⟨hJ hp, hh p hp⟩, hc⟩

theorem ctx_iff (y : ι → V) (H M : Finset (ι × V)) :
    Ctx y H M ↔ AllHit y H ∧ hits y M = 0 := by
  classical
  unfold Ctx hits
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]

/-- Expectation of `1_H · C(hits M, k)` as a sum over the `k`-subsets of `M`. -/
theorem mass_choose (P : (ι → V) → ℝ) (H M : Finset (ι × V)) (k : Nat) :
    (∑ y, P y * ((if AllHit y H then (1 : ℝ) else 0) * ((hits y M).choose k : ℝ))) =
      ∑ J ∈ M.powersetCard k, mass P (fun y => AllHit y (H ∪ J)) := by
  classical
  simp only [choose_hits, Finset.mul_sum, mass]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun y _ => ?_
  have hu : AllHit y (H ∪ J) ↔ AllHit y H ∧ AllHit y J := by
    simp only [AllHit, Finset.mem_union]
    exact ⟨fun h => ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩,
      fun h p hp => hp.elim (h.1 p) (h.2 p)⟩
  by_cases hH : AllHit y H <;> by_cases hJ : AllHit y J <;> simp [hH, hJ, hu]

variable (P Q : (ι → V) → ℝ) (δ : ℝ)

/-- The leaf step: a context with at most two hits has the same mass under both laws up to `2 δ C(|M|, 3 - |H|)`. -/
theorem ctx_mass_le (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) (hδ : 0 ≤ δ)
    (h2 : ∀ S : Finset (ι × V), S.card ≤ 2 → mass P (fun y => AllHit y S) = mass Q (fun y => AllHit y S))
    (h3P : ∀ S : Finset (ι × V), S.card = 3 → mass P (fun y => AllHit y S) ≤ δ)
    (h3Q : ∀ S : Finset (ι × V), S.card = 3 → mass Q (fun y => AllHit y S) ≤ δ)
    (H M : Finset (ι × V)) (hH : H.card ≤ 2) :
    mass P (fun y => Ctx y H M) ≤ mass Q (fun y => Ctx y H M) + 2 * δ * (M.card.choose (3 - H.card) : ℝ) := by
  classical
  by_cases hd : Disjoint H M
  swap
  · rw [mass_false P _ (fun y hy => by
      obtain ⟨p, hpH, hpM⟩ := Finset.not_disjoint_iff.mp hd
      exact hy.2 p hpM (hy.1 p hpH))]
    have h1 : 0 ≤ mass Q (fun y => Ctx y H M) := mass_nonneg Q hQ _
    have h2 : 0 ≤ 2 * δ * (M.card.choose (3 - H.card) : ℝ) := by positivity
    linarith
  set r := 2 - H.card with hr
  have hrr : r ≤ 2 := by omega
  have hk : 3 - H.card = r + 1 := by omega
  -- pointwise bounds
  have hpoint : ∀ y, |(if Ctx y H M then (1 : ℝ) else 0) -
      (if AllHit y H then (1 : ℝ) else 0) * alt r (hits y M)| ≤
      (if AllHit y H then (1 : ℝ) else 0) * ((hits y M).choose (r + 1) : ℝ) := by
    intro y
    by_cases hy : AllHit y H
    · have hb := bonferroni_point r (hits y M) hrr
      simp only [hy, if_true, one_mul, ctx_iff, true_and]
      exact hb
    · have : ¬Ctx y H M := fun h => hy h.1
      simp [hy, this]
  -- the agreeing part
  have hagree : (∑ y, P y * ((if AllHit y H then (1 : ℝ) else 0) * alt r (hits y M))) =
      ∑ y, Q y * ((if AllHit y H then (1 : ℝ) else 0) * alt r (hits y M)) := by
    have hexp : ∀ R : (ι → V) → ℝ, (∑ y, R y * ((if AllHit y H then (1 : ℝ) else 0) * alt r (hits y M))) =
        ∑ k ∈ range (r + 1), (-1 : ℝ) ^ k * ∑ J ∈ M.powersetCard k, mass R (fun y => AllHit y (H ∪ J)) := by
      intro R
      simp only [alt, Finset.mul_sum, ← mass_choose]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun y _ => by ring
    rw [hexp P, hexp Q]
    refine Finset.sum_congr rfl fun k hk' => ?_
    congr 1
    refine Finset.sum_congr rfl fun J hJ => h2 _ ?_
    have hJc := (Finset.mem_powersetCard.mp hJ).2
    have := Finset.card_union_le H J
    have hkr := Finset.mem_range.mp hk'
    omega
  -- the error parts
  have herr : ∀ R : (ι → V) → ℝ, (∀ S : Finset (ι × V), S.card = 3 → mass R (fun y => AllHit y S) ≤ δ) →
      (∑ y, R y * ((if AllHit y H then (1 : ℝ) else 0) * ((hits y M).choose (r + 1) : ℝ))) ≤
        (M.card.choose (r + 1) : ℝ) * δ := by
    intro R h3R
    rw [mass_choose]
    calc (∑ J ∈ M.powersetCard (r + 1), mass R (fun y => AllHit y (H ∪ J)))
        ≤ ∑ J ∈ M.powersetCard (r + 1), δ := Finset.sum_le_sum fun J hJ => by
          apply h3R
          rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right
            (Finset.mem_powersetCard.mp hJ).1 hd), (Finset.mem_powersetCard.mp hJ).2]
          omega
      _ = (M.card.choose (r + 1) : ℝ) * δ := by rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  have hupper : mass P (fun y => Ctx y H M) ≤
      (∑ y, P y * ((if AllHit y H then (1 : ℝ) else 0) * alt r (hits y M))) +
      ∑ y, P y * ((if AllHit y H then (1 : ℝ) else 0) * ((hits y M).choose (r + 1) : ℝ)) := by
    unfold mass
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y _ => ?_
    have h := (abs_le.mp (hpoint y)).2
    have hPy := hP y
    by_cases hc : Ctx y H M
    · simp only [hc, if_true] at h ⊢
      nlinarith
    · simp only [hc, if_false] at h ⊢
      nlinarith
  have hlower : (∑ y, Q y * ((if AllHit y H then (1 : ℝ) else 0) * alt r (hits y M))) -
      ∑ y, Q y * ((if AllHit y H then (1 : ℝ) else 0) * ((hits y M).choose (r + 1) : ℝ)) ≤
      mass Q (fun y => Ctx y H M) := by
    unfold mass
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun y _ => ?_
    have h := (abs_le.mp (hpoint y)).1
    have hQy := hQ y
    by_cases hc : Ctx y H M
    · simp only [hc, if_true] at h ⊢
      nlinarith
    · simp only [hc, if_false] at h ⊢
      nlinarith
  have eP := herr P h3P
  have eQ := herr Q h3Q
  rw [hk]
  linarith

/-! ### Induction on the strategy tree -/

theorem ctx_insert_hit (y : ι → V) (H M : Finset (ι × V)) (p : ι × V) :
    Ctx y (insert p H) M ↔ Ctx y H M ∧ y p.1 = p.2 := by
  unfold Ctx AllHit
  simp only [Finset.mem_insert, forall_eq_or_imp]
  tauto
theorem ctx_insert_miss (y : ι → V) (H M : Finset (ι × V)) (p : ι × V) :
    Ctx y H (insert p M) ↔ Ctx y H M ∧ ¬y p.1 = p.2 := by
  unfold Ctx AllHit
  simp only [Finset.mem_insert, forall_eq_or_imp]
  tauto

/-- The induction claim: `2 δ C(|M| + 2 · depth, 3 - |H|)`. -/
theorem tree_ctx_le (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) (hδ : 0 ≤ δ)
    (h2 : ∀ S : Finset (ι × V), S.card ≤ 2 → mass P (fun y => AllHit y S) = mass Q (fun y => AllHit y S))
    (h3P : ∀ S : Finset (ι × V), S.card = 3 → mass P (fun y => AllHit y S) ≤ δ)
    (h3Q : ∀ S : Finset (ι × V), S.card = 3 → mass Q (fun y => AllHit y S) ≤ δ)
    {α : Type} (A : α → Prop) :
    ∀ (T : Tree ι V α) (H M : Finset (ι × V)),
      mass P (fun y => Ctx y H M ∧ A (T.run y)) ≤ mass Q (fun y => Ctx y H M ∧ A (T.run y)) +
        2 * δ * ((M.card + 2 * T.depth).choose (3 - H.card) : ℝ) := by
  classical
  intro T
  -- contexts with three hits are bounded directly
  have big : ∀ (T : Tree ι V α) (H M : Finset (ι × V)), 3 ≤ H.card →
      mass P (fun y => Ctx y H M ∧ A (T.run y)) ≤ mass Q (fun y => Ctx y H M ∧ A (T.run y)) +
        2 * δ * ((M.card + 2 * T.depth).choose (3 - H.card) : ℝ) := by
    intro T H M hH
    obtain ⟨S, hSH, hS⟩ := Finset.exists_subset_card_eq hH
    have hle : mass P (fun y => Ctx y H M ∧ A (T.run y)) ≤ δ :=
      (mass_mono P hP fun y hy p hp => hy.1.1 p (hSH hp)).trans (h3P S hS)
    have hq := mass_nonneg Q hQ (fun y => Ctx y H M ∧ A (T.run y))
    rw [show 3 - H.card = 0 by omega, Nat.choose_zero_right, Nat.cast_one, mul_one]
    linarith
  induction T with
  | leaf a =>
      intro H M
      by_cases hH : 3 ≤ H.card
      · exact big _ H M hH
      by_cases ha : A a
      · have e : ∀ R : (ι → V) → ℝ, mass R (fun y => Ctx y H M ∧ A ((Tree.leaf a : Tree ι V α).run y)) =
            mass R (fun y => Ctx y H M) := fun R => mass_congr R fun y => by simp [Tree.run, ha]
        rw [e P, e Q]
        simpa [Tree.depth] using ctx_mass_le P Q δ hP hQ hδ h2 h3P h3Q H M (by omega)
      · rw [mass_false P _ (fun y hy => ha hy.2)]
        have h1 := mass_nonneg Q hQ (fun y => Ctx y H M ∧ A ((Tree.leaf a : Tree ι V α).run y))
        have h2' : 0 ≤ 2 * δ * ((M.card + 2 * (Tree.leaf a : Tree ι V α).depth).choose (3 - H.card) : ℝ) := by
          positivity
        linarith
  | test p k ih =>
      intro H M
      by_cases hH : 3 ≤ H.card
      · exact big _ H M hH
      -- split on the answer to the test
      have hsplit : ∀ R : (ι → V) → ℝ, mass R (fun y => Ctx y H M ∧ A ((Tree.test p k).run y)) =
          mass R (fun y => Ctx y (insert p H) M ∧ A ((k true).run y)) +
            mass R (fun y => Ctx y H (insert p M) ∧ A ((k false).run y)) := by
        intro R
        rw [mass_split R _ (fun y => y p.1 = p.2)]
        congr 1
        · refine mass_congr R fun y => ?_
          rw [ctx_insert_hit]
          constructor
          · rintro ⟨⟨hc, ha⟩, hp⟩
            simp only [Tree.run, hp, decide_true] at ha
            exact ⟨⟨hc, hp⟩, ha⟩
          · rintro ⟨⟨hc, hp⟩, ha⟩
            refine ⟨⟨hc, ?_⟩, hp⟩
            simp only [Tree.run, hp, decide_true]
            exact ha
        · refine mass_congr R fun y => ?_
          rw [ctx_insert_miss]
          constructor
          · rintro ⟨⟨hc, ha⟩, hp⟩
            simp only [Tree.run, hp, decide_false] at ha
            exact ⟨⟨hc, hp⟩, ha⟩
          · rintro ⟨⟨hc, hp⟩, ha⟩
            refine ⟨⟨hc, ?_⟩, hp⟩
            simp only [Tree.run, hp, decide_false]
            exact ha
      rw [hsplit P, hsplit Q]
      have hdep : (Tree.test p k).depth = max (k true).depth (k false).depth + 1 := rfl
      set d := max (k true).depth (k false).depth with hd
      have dt : (k true).depth ≤ d := le_max_left _ _
      have df : (k false).depth ≤ d := le_max_right _ _
      have mono : ∀ {a b : Nat} (c : Nat), a ≤ b → ((a.choose c : Nat) : ℝ) ≤ (b.choose c : ℝ) :=
        fun c hab => by exact_mod_cast Nat.choose_le_choose c hab
      have hδ2 : 0 ≤ 2 * δ := by linarith
      have qt := mass_nonneg Q hQ (fun y => Ctx y (insert p H) M ∧ A ((k true).run y))
      have qf := mass_nonneg Q hQ (fun y => Ctx y H (insert p M) ∧ A ((k false).run y))
      by_cases hpH : p ∈ H
      · -- the miss branch is impossible
        rw [Finset.insert_eq_of_mem hpH, mass_false P (fun y => Ctx y H (insert p M) ∧ A ((k false).run y))
          (fun y hy => (ctx_insert_miss y H M p).mp hy.1 |>.2 (hy.1.1 p hpH))]
        have ht := ih true H M
        rw [Finset.insert_eq_of_mem hpH] at qt
        have hm := mono (3 - H.card) (show M.card + 2 * (k true).depth ≤ M.card + 2 * (d + 1) by omega)
        rw [hdep]
        nlinarith [mul_le_mul_of_nonneg_left hm hδ2]
      by_cases hpM : p ∈ M
      · rw [Finset.insert_eq_of_mem hpM, mass_false P (fun y => Ctx y (insert p H) M ∧ A ((k true).run y))
          (fun y hy => (hy.1.2 p hpM) ((ctx_insert_hit y H M p).mp hy.1).2)]
        have hf := ih false H M
        rw [Finset.insert_eq_of_mem hpM] at qf
        have hm := mono (3 - H.card) (show M.card + 2 * (k false).depth ≤ M.card + 2 * (d + 1) by omega)
        rw [hdep]
        nlinarith [mul_le_mul_of_nonneg_left hm hδ2]
      · have ht := ih true (insert p H) M
        have hf := ih false H (insert p M)
        rw [Finset.card_insert_of_notMem hpH] at ht
        rw [Finset.card_insert_of_notMem hpM] at hf
        have k1 : 3 - (H.card + 1) = (3 - H.card) - 1 := by omega
        have hpos : 1 ≤ 3 - H.card := by omega
        have m1 := mono (3 - (H.card + 1)) (show M.card + 2 * (k true).depth ≤ M.card + 2 * d by omega)
        have m2 := mono (3 - H.card) (show M.card + 1 + 2 * (k false).depth ≤ M.card + 2 * d + 1 by omega)
        have pascal : ((M.card + 2 * d).choose (3 - H.card - 1) : ℝ) + ((M.card + 2 * d + 1).choose (3 - H.card) : ℝ)
            ≤ ((M.card + 2 * (d + 1)).choose (3 - H.card) : ℝ) := by
          obtain ⟨j, hj⟩ : ∃ j, 3 - H.card = j + 1 := ⟨3 - H.card - 1, by omega⟩
          have hn : (M.card + 2 * d).choose j + (M.card + 2 * d + 1).choose (j + 1) ≤
              (M.card + 2 * (d + 1)).choose (j + 1) := by
            rw [show M.card + 2 * (d + 1) = (M.card + 2 * d + 1) + 1 by ring,
              Nat.choose_succ_succ' (M.card + 2 * d + 1) j]
            have : (M.card + 2 * d).choose j ≤ (M.card + 2 * d + 1).choose j :=
              Nat.choose_le_choose j (by omega)
            omega
          rw [hj, show j + 1 - 1 = j by omega]
          exact_mod_cast hn
        rw [k1] at ht m1
        rw [hdep]
        have e1 := mul_le_mul_of_nonneg_left m1 hδ2
        have e2 := mul_le_mul_of_nonneg_left m2 hδ2
        have e3 := mul_le_mul_of_nonneg_left pascal hδ2
        nlinarith

/-- **Side-channel bound.** If the laws `P`, `Q` agree on all events "≤ 2 tests hit" and give mass `≤ δ` to every
event "3 tests hit", then an adaptive strategy of depth `g` separates them by at most `2 δ C(2g, 3)`. -/
theorem tree_mass_le (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) (hδ : 0 ≤ δ)
    (h2 : ∀ S : Finset (ι × V), S.card ≤ 2 → mass P (fun y => AllHit y S) = mass Q (fun y => AllHit y S))
    (h3P : ∀ S : Finset (ι × V), S.card = 3 → mass P (fun y => AllHit y S) ≤ δ)
    (h3Q : ∀ S : Finset (ι × V), S.card = 3 → mass Q (fun y => AllHit y S) ≤ δ)
    {α : Type} (T : Tree ι V α) (A : α → Prop) :
    mass P (fun y => A (T.run y)) ≤ mass Q (fun y => A (T.run y)) + 2 * δ * ((2 * T.depth).choose 3 : ℝ) := by
  have h := tree_ctx_le P Q δ hP hQ hδ h2 h3P h3Q A T ∅ ∅
  have e : ∀ R : (ι → V) → ℝ, mass R (fun y => Ctx y ∅ ∅ ∧ A (T.run y)) = mass R (fun y => A (T.run y)) :=
    fun R => mass_congr R fun y => by simp [Ctx, AllHit]
  rw [e P, e Q] at h
  simpa using h

/-! ### Refinement: charge the all-miss path

Summed over many independent families (one per lower leaf) the depth bound is useless: every leaf would be
charged the global query budget. The refined bound charges `C(ℓ, 3) + ℓ · C(ℓ + 2D, 2)` where `ℓ = amLen T`
is the number of tests on the all-miss path (the path taken when no test hits, i.e. the typical number of
tests on this family) and `D` bounds the depth. -/

namespace Tree
variable {α : Type}
/-- Number of tests on the all-miss path. -/
def amLen : Tree ι V α → Nat
  | leaf _ => 0
  | test _ k => (k false).amLen + 1

theorem amLen_le_depth : ∀ T : Tree ι V α, T.amLen ≤ T.depth
  | leaf _ => le_refl _
  | test p k => by
      have := amLen_le_depth (k false)
      simp only [amLen, depth]
      omega
end Tree

theorem tree_ctx_le_am (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) (hδ : 0 ≤ δ)
    (h2 : ∀ S : Finset (ι × V), S.card ≤ 2 → mass P (fun y => AllHit y S) = mass Q (fun y => AllHit y S))
    (h3P : ∀ S : Finset (ι × V), S.card = 3 → mass P (fun y => AllHit y S) ≤ δ)
    (h3Q : ∀ S : Finset (ι × V), S.card = 3 → mass Q (fun y => AllHit y S) ≤ δ)
    {α : Type} (A : α → Prop) (D : Nat) :
    ∀ (T : Tree ι V α), T.depth ≤ D → ∀ (M : Finset (ι × V)),
      mass P (fun y => Ctx y ∅ M ∧ A (T.run y)) ≤ mass Q (fun y => Ctx y ∅ M ∧ A (T.run y)) +
        2 * δ * (((M.card + T.amLen).choose 3 : ℝ) + T.amLen * ((M.card + T.amLen + 2 * D).choose 2 : ℝ)) := by
  classical
  intro T
  induction T with
  | leaf a =>
      intro _ M
      have h := tree_ctx_le P Q δ hP hQ hδ h2 h3P h3Q A (Tree.leaf a) ∅ M
      simp only [Finset.card_empty, Nat.sub_zero, Tree.depth, Tree.amLen, mul_zero, add_zero, Nat.cast_zero,
        zero_mul] at h ⊢
      exact h
  | test p k ih =>
      intro hD M
      have hdep : (Tree.test p k).depth = max (k true).depth (k false).depth + 1 := rfl
      have hDt : (k true).depth ≤ D := by omega
      have hDf : (k false).depth ≤ D := by omega
      have ham : (Tree.test p k).amLen = (k false).amLen + 1 := rfl
      set ℓ := (k false).amLen with hℓ
      have hsplit : ∀ R : (ι → V) → ℝ, mass R (fun y => Ctx y ∅ M ∧ A ((Tree.test p k).run y)) =
          mass R (fun y => Ctx y (insert p ∅) M ∧ A ((k true).run y)) +
            mass R (fun y => Ctx y ∅ (insert p M) ∧ A ((k false).run y)) := by
        intro R
        rw [mass_split R _ (fun y => y p.1 = p.2)]
        congr 1
        · refine mass_congr R fun y => ?_
          rw [ctx_insert_hit]
          constructor
          · rintro ⟨⟨hc, ha⟩, hp⟩
            simp only [Tree.run, hp, decide_true] at ha
            exact ⟨⟨hc, hp⟩, ha⟩
          · rintro ⟨⟨hc, hp⟩, ha⟩
            refine ⟨⟨hc, ?_⟩, hp⟩
            simp only [Tree.run, hp, decide_true]
            exact ha
        · refine mass_congr R fun y => ?_
          rw [ctx_insert_miss]
          constructor
          · rintro ⟨⟨hc, ha⟩, hp⟩
            simp only [Tree.run, hp, decide_false] at ha
            exact ⟨⟨hc, hp⟩, ha⟩
          · rintro ⟨⟨hc, hp⟩, ha⟩
            refine ⟨⟨hc, ?_⟩, hp⟩
            simp only [Tree.run, hp, decide_false]
            exact ha
      rw [hsplit P, hsplit Q, ham]
      have hδ2 : 0 ≤ 2 * δ := by linarith
      have qt := mass_nonneg Q hQ (fun y => Ctx y (insert p ∅) M ∧ A ((k true).run y))
      have qf := mass_nonneg Q hQ (fun y => Ctx y ∅ (insert p M) ∧ A ((k false).run y))
      have mono : ∀ {a b : Nat} (c : Nat), a ≤ b → ((a.choose c : Nat) : ℝ) ≤ (b.choose c : ℝ) :=
        fun c hab => by exact_mod_cast Nat.choose_le_choose c hab
      have hc3 : (0 : ℝ) ≤ ((M.card + (ℓ + 1)).choose 3 : ℝ) := Nat.cast_nonneg _
      have hc2 : (0 : ℝ) ≤ ((M.card + (ℓ + 1) + 2 * D).choose 2 : ℝ) := Nat.cast_nonneg _
      by_cases hpM : p ∈ M
      · rw [Finset.insert_eq_of_mem hpM, mass_false P (fun y => Ctx y (insert p ∅) M ∧ A ((k true).run y))
          (fun y hy => (hy.1.2 p hpM) ((ctx_insert_hit y ∅ M p).mp hy.1).2)]
        have hf := ih false hDf M
        rw [Finset.insert_eq_of_mem hpM] at qf
        have m1 := mono 3 (show M.card + ℓ ≤ M.card + (ℓ + 1) by omega)
        have m2 := mono 2 (show M.card + ℓ + 2 * D ≤ M.card + (ℓ + 1) + 2 * D by omega)
        have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
        have e1 := mul_le_mul_of_nonneg_left m1 hδ2
        have e2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m2 hℓ0) hδ2
        push_cast
        nlinarith [mul_nonneg hδ2 hc2]
      · -- hit branch: one hit, bounded by the depth bound; miss branch: induction
        have ht := tree_ctx_le P Q δ hP hQ hδ h2 h3P h3Q A (k true) (insert p ∅) M
        have hf := ih false hDf (insert p M)
        rw [Finset.card_insert_of_notMem hpM] at hf
        simp only [Finset.insert_empty, Finset.card_singleton] at ht ⊢
        have m1 := mono (3 - 1) (show M.card + 2 * (k true).depth ≤ M.card + (ℓ + 1) + 2 * D by omega)
        have m2 := mono 2 (show M.card + 1 + ℓ + 2 * D ≤ M.card + (ℓ + 1) + 2 * D by omega)
        have m3 : ((M.card + 1 + ℓ).choose 3 : ℝ) = ((M.card + (ℓ + 1)).choose 3 : ℝ) := by
          congr 2; omega
        have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
        have e1 := mul_le_mul_of_nonneg_left m1 hδ2
        have e2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m2 hℓ0) hδ2
        rw [m3] at hf
        push_cast
        nlinarith

/-- **Side-channel bound charged to the all-miss path** (`ℓ` tests on it, depth `≤ D`). -/
theorem tree_mass_le_am (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) (hδ : 0 ≤ δ)
    (h2 : ∀ S : Finset (ι × V), S.card ≤ 2 → mass P (fun y => AllHit y S) = mass Q (fun y => AllHit y S))
    (h3P : ∀ S : Finset (ι × V), S.card = 3 → mass P (fun y => AllHit y S) ≤ δ)
    (h3Q : ∀ S : Finset (ι × V), S.card = 3 → mass Q (fun y => AllHit y S) ≤ δ)
    {α : Type} (T : Tree ι V α) (D : Nat) (hD : T.depth ≤ D) (A : α → Prop) :
    mass P (fun y => A (T.run y)) ≤ mass Q (fun y => A (T.run y)) +
      2 * δ * ((T.amLen.choose 3 : ℝ) + T.amLen * ((T.amLen + 2 * D).choose 2 : ℝ)) := by
  have h := tree_ctx_le_am P Q δ hP hQ hδ h2 h3P h3Q A D T hD ∅
  have e : ∀ R : (ι → V) → ℝ, mass R (fun y => Ctx y ∅ ∅ ∧ A (T.run y)) = mass R (fun y => A (T.run y)) :=
    fun R => mass_congr R fun y => by simp [Ctx, AllHit]
  rw [e P, e Q] at h
  simpa using h

/-! ### Laws with uniform small marginals -/

section KWise
variable [Nonempty V] (P : (ι → V) → ℝ)

/-- `P` has uniform `k`-wise marginals: any `≤ k` coordinates take any prescribed values with mass `|V|^-t`. -/
def KWise (k : Nat) : Prop :=
  ∀ (T : Finset ι) (v : ι → V), T.card ≤ k →
    mass P (fun y => ∀ i ∈ T, y i = v i) = ((Fintype.card V : ℝ)⁻¹) ^ T.card

/-- Under `KWise k`, a set `S` of at most `k` tests all hit with mass `|V|^-|S|` if no coordinate is tested with
two values, and `0` otherwise. -/
theorem mass_allHit_of_kwise (hP : ∀ y, 0 ≤ P y) {k : Nat} (hk : KWise P k) (S : Finset (ι × V))
    (hS : S.card ≤ k) :
    mass P (fun y => AllHit y S) =
      if (∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → p = q) then ((Fintype.card V : ℝ)⁻¹) ^ S.card else 0 := by
  classical
  split_ifs with hfun
  · -- `S` is the graph of a function on its coordinates
    set T := S.image Prod.fst with hT
    have hinj : Set.InjOn Prod.fst (S : Set (ι × V)) := fun p hp q hq h => hfun p hp q hq h
    have hcard : T.card = S.card := Finset.card_image_of_injOn hinj
    -- choose the prescribed value of each tested coordinate
    let v : ι → V := fun i => if h : ∃ p ∈ S, p.1 = i then (Classical.choose h).2 else
      Classical.arbitrary V
    have hv : ∀ p ∈ S, v p.1 = p.2 := by
      intro p hp
      have h : ∃ q ∈ S, q.1 = p.1 := ⟨p, hp, rfl⟩
      simp only [v, dif_pos h]
      have hq := Classical.choose_spec h
      exact (congrArg Prod.snd (hfun _ hq.1 p hp hq.2)).trans rfl
    have e : mass P (fun y => AllHit y S) = mass P (fun y => ∀ i ∈ T, y i = v i) := by
      refine mass_congr P fun y => ?_
      simp only [AllHit, hT, Finset.mem_image]
      constructor
      · rintro h i ⟨p, hp, rfl⟩
        rw [h p hp, hv p hp]
      · intro h p hp
        rw [h p.1 ⟨p, hp, rfl⟩, hv p hp]
    rw [e, hk T v (hcard ▸ hS), hcard]
  · push Not at hfun
    obtain ⟨p, hp, q, hq, he, hne⟩ := hfun
    refine mass_false P _ fun y hy => hne ?_
    exact Prod.ext he ((hy p hp).symm.trans (he ▸ hy q hq))

/-- Two laws with uniform 3-wise marginals satisfy the hypotheses of `tree_mass_le` with `δ = |V|^-3`. -/
theorem tree_mass_le_of_kwise (Q : (ι → V) → ℝ) (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y)
    (hkP : KWise P 3) (hkQ : KWise Q 3) {α : Type} (T : Tree ι V α) (A : α → Prop) :
    mass P (fun y => A (T.run y)) ≤ mass Q (fun y => A (T.run y)) +
      2 * ((Fintype.card V : ℝ)⁻¹) ^ 3 * ((2 * T.depth).choose 3 : ℝ) := by
  classical
  have hV : (0 : ℝ) ≤ (Fintype.card V : ℝ)⁻¹ := by positivity
  have hV1 : (Fintype.card V : ℝ)⁻¹ ≤ 1 := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with h | h
    · simp [h]
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast h)
  refine tree_mass_le P Q _ hP hQ (by positivity) ?_ ?_ ?_ T A
  · intro S hS
    rw [mass_allHit_of_kwise P hP (k := 3) hkP S (by omega), mass_allHit_of_kwise Q hQ (k := 3) hkQ S (by omega)]
  · intro S hS
    rw [mass_allHit_of_kwise P hP hkP S (by omega), hS]
    split_ifs
    · exact le_rfl
    · positivity
  · intro S hS
    rw [mass_allHit_of_kwise Q hQ hkQ S (by omega), hS]
    split_ifs
    · exact le_rfl
    · positivity
/-- `tree_mass_le_am` for laws with uniform 3-wise marginals. -/
theorem tree_mass_le_am_of_kwise (Q : (ι → V) → ℝ) (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y)
    (hkP : KWise P 3) (hkQ : KWise Q 3) {α : Type} (T : Tree ι V α) (D : Nat) (hD : T.depth ≤ D)
    (A : α → Prop) :
    mass P (fun y => A (T.run y)) ≤ mass Q (fun y => A (T.run y)) +
      2 * ((Fintype.card V : ℝ)⁻¹) ^ 3 * ((T.amLen.choose 3 : ℝ) + T.amLen * ((T.amLen + 2 * D).choose 2 : ℝ)) := by
  classical
  have hV : (0 : ℝ) ≤ (Fintype.card V : ℝ)⁻¹ := by positivity
  refine tree_mass_le_am P Q _ hP hQ (by positivity) ?_ ?_ ?_ T D hD A
  · intro S hS
    rw [mass_allHit_of_kwise P hP (k := 3) hkP S (by omega), mass_allHit_of_kwise Q hQ (k := 3) hkQ S (by omega)]
  · intro S hS
    rw [mass_allHit_of_kwise P hP hkP S (by omega), hS]
    split_ifs
    · exact le_rfl
    · positivity
  · intro S hS
    rw [mass_allHit_of_kwise Q hQ hkQ S (by omega), hS]
    split_ifs
    · exact le_rfl
    · positivity
end KWise

end ClaudeWCT.Arith.SideChannel
