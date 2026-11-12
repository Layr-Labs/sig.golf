import SigGolfCandidate.Merge019
import Mathlib.Data.Nat.Choose.Sum
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
open Finset
namespace ClaudeWCT.Arith.SideChannel.Four

theorem alt_succ (r n : Nat) : alt r (n+1) = (-1 : ℝ)^r * (n.choose r : ℝ) := by
  have h := Int.alternating_sum_range_choose_eq_choose (n := n) (m := r)
  have hc := congrArg (fun x : ℤ => (x : ℝ)) h
  simpa [alt] using hc

theorem bonferroni (r N : Nat) :
    |(if N = 0 then (1 : ℝ) else 0) - alt r N| ≤ (N.choose (r+1) : ℝ) := by
  cases N with
  | zero =>
    have hz : alt r 0 = 1 := by
      induction r with
      | zero => simp [alt]
      | succ r ih => simpa [alt, sum_range_succ] using ih
    simp [hz]
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero _), alt_succ]
    simp only [zero_sub, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (Nat.cast_nonneg (n.choose r) : (0 : ℝ) ≤ _)]
    exact_mod_cast (show n.choose r ≤ (n+1).choose (r+1) from by rw [Nat.choose_succ_succ']; omega)

variable {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable
variable (P Q : (ι → V) → ℝ) (δ : ℝ)
theorem ctx_mass_le (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) (hδ : 0 ≤ δ)
    (h2 : ∀ S : Finset (ι × V), S.card ≤ 3 → mass P (fun y => AllHit y S) = mass Q (fun y => AllHit y S))
    (h3P : ∀ S : Finset (ι × V), S.card = 4 → mass P (fun y => AllHit y S) ≤ δ)
    (h3Q : ∀ S : Finset (ι × V), S.card = 4 → mass Q (fun y => AllHit y S) ≤ δ)
    (H M : Finset (ι × V)) (hH : H.card ≤ 3) :
    mass P (fun y => Ctx y H M) ≤ mass Q (fun y => Ctx y H M) + 2 * δ * (M.card.choose (4 - H.card) : ℝ) := by
  classical
  by_cases hd : Disjoint H M
  swap
  · rw [mass_false P _ (fun y hy => by
      obtain ⟨p, hpH, hpM⟩ := Finset.not_disjoint_iff.mp hd
      exact hy.2 p hpM (hy.1 p hpH))]
    have h1 : 0 ≤ mass Q (fun y => Ctx y H M) := mass_nonneg Q hQ _
    have h2 : 0 ≤ 2 * δ * (M.card.choose (4 - H.card) : ℝ) := by positivity
    linarith
  set r := 3 - H.card with hr
  have hrr : r ≤ 3 := by omega
  have hk : 4 - H.card = r + 1 := by omega
  -- pointwise bounds
  have hpoint : ∀ y, |(if Ctx y H M then (1 : ℝ) else 0) -
      (if AllHit y H then (1 : ℝ) else 0) * alt r (hits y M)| ≤
      (if AllHit y H then (1 : ℝ) else 0) * ((hits y M).choose (r + 1) : ℝ) := by
    intro y
    by_cases hy : AllHit y H
    · have hb := bonferroni r (hits y M)
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
  have herr : ∀ R : (ι → V) → ℝ, (∀ S : Finset (ι × V), S.card = 4 → mass R (fun y => AllHit y S) ≤ δ) →
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


theorem tree_ctx_le (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) (hδ : 0 ≤ δ)
    (h2 : ∀ S : Finset (ι × V), S.card ≤ 3 → mass P (fun y => AllHit y S) = mass Q (fun y => AllHit y S))
    (h3P : ∀ S : Finset (ι × V), S.card = 4 → mass P (fun y => AllHit y S) ≤ δ)
    (h3Q : ∀ S : Finset (ι × V), S.card = 4 → mass Q (fun y => AllHit y S) ≤ δ)
    {α : Type} (A : α → Prop) :
    ∀ (T : Tree ι V α) (H M : Finset (ι × V)),
      mass P (fun y => Ctx y H M ∧ A (T.run y)) ≤ mass Q (fun y => Ctx y H M ∧ A (T.run y)) +
        2 * δ * ((M.card + 2 * T.depth).choose (4 - H.card) : ℝ) := by
  classical
  intro T
  -- contexts with three hits are bounded directly
  have big : ∀ (T : Tree ι V α) (H M : Finset (ι × V)), 4 ≤ H.card →
      mass P (fun y => Ctx y H M ∧ A (T.run y)) ≤ mass Q (fun y => Ctx y H M ∧ A (T.run y)) +
        2 * δ * ((M.card + 2 * T.depth).choose (4 - H.card) : ℝ) := by
    intro T H M hH
    obtain ⟨S, hSH, hS⟩ := Finset.exists_subset_card_eq hH
    have hle : mass P (fun y => Ctx y H M ∧ A (T.run y)) ≤ δ :=
      (mass_mono P hP fun y hy p hp => hy.1.1 p (hSH hp)).trans (h3P S hS)
    have hq := mass_nonneg Q hQ (fun y => Ctx y H M ∧ A (T.run y))
    rw [show 4 - H.card = 0 by omega, Nat.choose_zero_right, Nat.cast_one, mul_one]
    linarith
  induction T with
  | leaf a =>
      intro H M
      by_cases hH : 4 ≤ H.card
      · exact big _ H M hH
      by_cases ha : A a
      · have e : ∀ R : (ι → V) → ℝ, mass R (fun y => Ctx y H M ∧ A ((Tree.leaf a : Tree ι V α).run y)) =
            mass R (fun y => Ctx y H M) := fun R => mass_congr R fun y => by simp [Tree.run, ha]
        rw [e P, e Q]
        simpa [Tree.depth] using ctx_mass_le P Q δ hP hQ hδ h2 h3P h3Q H M (by omega)
      · rw [mass_false P _ (fun y hy => ha hy.2)]
        have h1 := mass_nonneg Q hQ (fun y => Ctx y H M ∧ A ((Tree.leaf a : Tree ι V α).run y))
        have h2' : 0 ≤ 2 * δ * ((M.card + 2 * (Tree.leaf a : Tree ι V α).depth).choose (4 - H.card) : ℝ) := by
          positivity
        linarith
  | test p k ih =>
      intro H M
      by_cases hH : 4 ≤ H.card
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
        have hm := mono (4 - H.card) (show M.card + 2 * (k true).depth ≤ M.card + 2 * (d + 1) by omega)
        rw [hdep]
        nlinarith [mul_le_mul_of_nonneg_left hm hδ2]
      by_cases hpM : p ∈ M
      · rw [Finset.insert_eq_of_mem hpM, mass_false P (fun y => Ctx y (insert p H) M ∧ A ((k true).run y))
          (fun y hy => (hy.1.2 p hpM) ((ctx_insert_hit y H M p).mp hy.1).2)]
        have hf := ih false H M
        rw [Finset.insert_eq_of_mem hpM] at qf
        have hm := mono (4 - H.card) (show M.card + 2 * (k false).depth ≤ M.card + 2 * (d + 1) by omega)
        rw [hdep]
        nlinarith [mul_le_mul_of_nonneg_left hm hδ2]
      · have ht := ih true (insert p H) M
        have hf := ih false H (insert p M)
        rw [Finset.card_insert_of_notMem hpH] at ht
        rw [Finset.card_insert_of_notMem hpM] at hf
        have k1 : 4 - (H.card + 1) = (4 - H.card) - 1 := by omega
        have hpos : 1 ≤ 4 - H.card := by omega
        have m1 := mono (4 - (H.card + 1)) (show M.card + 2 * (k true).depth ≤ M.card + 2 * d by omega)
        have m2 := mono (4 - H.card) (show M.card + 1 + 2 * (k false).depth ≤ M.card + 2 * d + 1 by omega)
        have pascal : ((M.card + 2 * d).choose (4 - H.card - 1) : ℝ) + ((M.card + 2 * d + 1).choose (4 - H.card) : ℝ)
            ≤ ((M.card + 2 * (d + 1)).choose (4 - H.card) : ℝ) := by
          obtain ⟨j, hj⟩ : ∃ j, 4 - H.card = j + 1 := ⟨4 - H.card - 1, by omega⟩
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


theorem tree_ctx_le_am (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) (hδ : 0 ≤ δ)
    (h2 : ∀ S : Finset (ι × V), S.card ≤ 3 → mass P (fun y => AllHit y S) = mass Q (fun y => AllHit y S))
    (h3P : ∀ S : Finset (ι × V), S.card = 4 → mass P (fun y => AllHit y S) ≤ δ)
    (h3Q : ∀ S : Finset (ι × V), S.card = 4 → mass Q (fun y => AllHit y S) ≤ δ)
    {α : Type} (A : α → Prop) (D : Nat) :
    ∀ (T : Tree ι V α), T.depth ≤ D → ∀ (M : Finset (ι × V)),
      mass P (fun y => Ctx y ∅ M ∧ A (T.run y)) ≤ mass Q (fun y => Ctx y ∅ M ∧ A (T.run y)) +
        2 * δ * (((M.card + T.amLen).choose 4 : ℝ) + T.amLen * ((M.card + T.amLen + 2 * D).choose 3 : ℝ)) := by
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
      have hc3 : (0 : ℝ) ≤ ((M.card + (ℓ + 1)).choose 4 : ℝ) := Nat.cast_nonneg _
      have hc2 : (0 : ℝ) ≤ ((M.card + (ℓ + 1) + 2 * D).choose 3 : ℝ) := Nat.cast_nonneg _
      by_cases hpM : p ∈ M
      · rw [Finset.insert_eq_of_mem hpM, mass_false P (fun y => Ctx y (insert p ∅) M ∧ A ((k true).run y))
          (fun y hy => (hy.1.2 p hpM) ((ctx_insert_hit y ∅ M p).mp hy.1).2)]
        have hf := ih false hDf M
        rw [Finset.insert_eq_of_mem hpM] at qf
        have m1 := mono 4 (show M.card + ℓ ≤ M.card + (ℓ + 1) by omega)
        have m2 := mono 3 (show M.card + ℓ + 2 * D ≤ M.card + (ℓ + 1) + 2 * D by omega)
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
        have m1 := mono (4 - 1) (show M.card + 2 * (k true).depth ≤ M.card + (ℓ + 1) + 2 * D by omega)
        have m2 := mono 3 (show M.card + 1 + ℓ + 2 * D ≤ M.card + (ℓ + 1) + 2 * D by omega)
        have m3 : ((M.card + 1 + ℓ).choose 4 : ℝ) = ((M.card + (ℓ + 1)).choose 4 : ℝ) := by
          congr 2; omega
        have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
        have e1 := mul_le_mul_of_nonneg_left m1 hδ2
        have e2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m2 hℓ0) hδ2
        rw [m3] at hf
        push_cast
        nlinarith

/-- **Side-channel bound charged to the all-miss path** (`ℓ` tests on it, depth `≤ D`). -/
theorem tree_mass_le_am (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) (hδ : 0 ≤ δ)
    (h2 : ∀ S : Finset (ι × V), S.card ≤ 3 → mass P (fun y => AllHit y S) = mass Q (fun y => AllHit y S))
    (h3P : ∀ S : Finset (ι × V), S.card = 4 → mass P (fun y => AllHit y S) ≤ δ)
    (h3Q : ∀ S : Finset (ι × V), S.card = 4 → mass Q (fun y => AllHit y S) ≤ δ)
    {α : Type} (T : Tree ι V α) (D : Nat) (hD : T.depth ≤ D) (A : α → Prop) :
    mass P (fun y => A (T.run y)) ≤ mass Q (fun y => A (T.run y)) +
      2 * δ * ((T.amLen.choose 4 : ℝ) + T.amLen * ((T.amLen + 2 * D).choose 3 : ℝ)) := by
  have h := tree_ctx_le_am P Q δ hP hQ hδ h2 h3P h3Q A D T hD ∅
  have e : ∀ R : (ι → V) → ℝ, mass R (fun y => Ctx y ∅ ∅ ∧ A (T.run y)) = mass R (fun y => A (T.run y)) :=
    fun R => mass_congr R fun y => by simp [Ctx, AllHit]
  rw [e P, e Q] at h
  simpa using h


open OracleComp
variable {α : Type} (A : α → Prop)
variable (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) (hδ : 0 ≤ δ)
  (h2 : ∀ S : Finset (ι × V), S.card ≤ 3 → mass P (fun y => AllHit y S) = mass Q (fun y => AllHit y S))
  (h3P : ∀ S : Finset (ι × V), S.card = 4 → mass P (fun y => AllHit y S) ≤ δ)
  (h3Q : ∀ S : Finset (ι × V), S.card = 4 → mass Q (fun y => AllHit y S) ≤ δ)
include hP hQ hδ h2 h3P h3Q
theorem comp_ctx_le : ∀ (oa : OracleComp (TSpec ι V) α) (H M : Finset (ι × V)),
    cmass A P H M oa ≤ cmass A Q H M oa + 2 * δ * ((M.card + 2 * tdepth oa).choose (4 - H.card) : ℝ) := by
  classical
  have big : ∀ (oa : OracleComp (TSpec ι V) α) (H M : Finset (ι × V)), 4 ≤ H.card →
      cmass A P H M oa ≤ cmass A Q H M oa + 2 * δ * ((M.card + 2 * tdepth oa).choose (4 - H.card) : ℝ) := by
    intro oa H M hH
    obtain ⟨S, hSH, hS⟩ := Finset.exists_subset_card_eq hH
    have hle : cmass A P H M oa ≤ δ :=
      (cmass_le_mass A P hP H M oa).trans ((mass_mono P hP fun y hy p hp => hy.1 p (hSH hp)).trans (h3P S hS))
    have hq := cmass_nonneg A Q hQ H M oa
    rw [show 4 - H.card = 0 by omega, Nat.choose_zero_right, Nat.cast_one, mul_one]
    linarith
  intro oa
  induction oa using tinduction with
  | pure a =>
      intro H M
      by_cases hH : 4 ≤ H.card
      · exact big _ H M hH
      rw [cmass_pure, cmass_pure, tdepth_pure]
      split_ifs with ha
      · simpa using ctx_mass_le P Q δ hP hQ hδ h2 h3P h3Q H M (by omega)
      · have : 0 ≤ 2 * δ * ((M.card + 2 * 0).choose (4 - H.card) : ℝ) := by positivity
        linarith
  | coin n k ih =>
      intro H M
      rw [cmass_coin, cmass_coin, tdepth_coin]
      have hmono : ∀ u, ((M.card + 2 * tdepth (k u)).choose (4 - H.card) : ℝ) ≤
          ((M.card + 2 * univ.sup fun u => tdepth (k u)).choose (4 - H.card) : ℝ) := fun u => by
        exact_mod_cast Nat.choose_le_choose _ (by
          have := le_sup (f := fun u => tdepth (k u)) (mem_univ u); omega)
      rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
      calc (∑ u : Fin (n + 1), cmass A P H M (k u))
          ≤ ∑ u : Fin (n + 1), (cmass A Q H M (k u) + 2 * δ *
              ((M.card + 2 * univ.sup fun u => tdepth (k u)).choose (4 - H.card) : ℝ)) :=
            sum_le_sum fun u _ => (ih u H M).trans (by nlinarith [hmono u])
        _ = _ := by rw [sum_add_distrib]; simp; ring
  | test p k ih =>
      intro H M
      by_cases hH : 4 ≤ H.card
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
        have hm := mono (4 - H.card) (show M.card + 2 * tdepth (k true) ≤ M.card + 2 * (d + 1) by omega)
        nlinarith [mul_le_mul_of_nonneg_left hm hδ2]
      by_cases hpM : p ∈ M
      · rw [Finset.insert_eq_of_mem hpM] at qf ⊢
        rw [cmass_eq_zero A P (insert p H) M (k true) (fun y hy =>
          (hy.2 p hpM) ((ctx_insert_hit y H M p).mp hy).2)]
        have hf := ih false H M
        have hm := mono (4 - H.card) (show M.card + 2 * tdepth (k false) ≤ M.card + 2 * (d + 1) by omega)
        nlinarith [mul_le_mul_of_nonneg_left hm hδ2]
      · have ht := ih true (insert p H) M
        have hf := ih false H (insert p M)
        rw [Finset.card_insert_of_notMem hpH] at ht
        rw [Finset.card_insert_of_notMem hpM] at hf
        obtain ⟨j, hj⟩ : ∃ j, 4 - H.card = j + 1 := ⟨4 - H.card - 1, by omega⟩
        rw [show 4 - (H.card + 1) = j by omega] at ht
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

theorem comp_ctx_le_am (D : ℕ) : ∀ (oa : OracleComp (TSpec ι V) α) (M : Finset (ι × V)),
    M.card + tdepth oa ≤ D →
    cmass A P ∅ M oa ≤ cmass A Q ∅ M oa + (2 * δ) * ((M.card.choose 4 : ℝ) + (2 * ((2 * D).choose 3 : ℝ)) * amLen oa) := by
  classical
  intro oa
  have hK0 : (0 : ℝ) ≤ (2 * ((2 * D).choose 3 : ℝ)) := by positivity
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
      have hB : (∑ u : Fin (n + 1), (2 * δ) * ((M.card.choose 4 : ℝ) + (2 * ((2 * D).choose 3 : ℝ)) * amLen (k u))) =
          (2 * δ) * (((n : ℝ) + 1) * (M.card.choose 4 : ℝ) + (2 * ((2 * D).choose 3 : ℝ)) * ∑ u, amLen (k u)) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum]
        simp [card_univ]
      calc (∑ u : Fin (n + 1), cmass A P ∅ M (k u)) / (n + 1)
          ≤ (∑ u : Fin (n + 1), (cmass A Q ∅ M (k u) +
              (2 * δ) * ((M.card.choose 4 : ℝ) + (2 * ((2 * D).choose 3 : ℝ)) * amLen (k u)))) / (n + 1) :=
            div_le_div_of_nonneg_right (sum_le_sum fun u _ => ih u M (hD' u)) hn.le
        _ = _ := by
          rw [sum_add_distrib, add_div, hB]
          congr 1
          field_simp
  | test p k ih =>
      intro M hD
      rw [cmass_test, cmass_test, amLen_test]
      rw [tdepth_test] at hD
      have qt := cmass_nonneg A Q hQ (insert p ∅) M (k true)
      have qf := cmass_nonneg A Q hQ ∅ (insert p M) (k false)
      have hal := amLen_nonneg (k false)
      have hc3 : (0 : ℝ) ≤ (M.card.choose 4 : ℝ) := Nat.cast_nonneg _
      by_cases hpM : p ∈ M
      · rw [Finset.insert_eq_of_mem hpM] at qf ⊢
        rw [cmass_eq_zero A P (insert p ∅) M (k true) (fun y hy =>
          (hy.2 p hpM) ((ctx_insert_hit y ∅ M p).mp hy).2)]
        have hf := ih false M (by omega)
        nlinarith [mul_nonneg (by positivity : 0 ≤ 2*δ) hK0]
      · have ht := comp_ctx_le P Q δ A hP hQ hδ h2 h3P h3Q (k true) (insert p ∅) M
        have hf := ih false (insert p M) (by rw [Finset.card_insert_of_notMem hpM]; omega)
        rw [Finset.card_insert_of_notMem hpM] at hf
        simp only [Finset.insert_empty, Finset.card_singleton] at ht ⊢
        have hs : ((M.card + 1).choose 4 : ℝ) = (M.card.choose 4 : ℝ) + (M.card.choose 3 : ℝ) := by
          rw [Nat.choose_succ_succ' M.card 3]; push_cast; ring
        have hcomb : (M.card.choose 3 : ℝ) + ((M.card + 2 * tdepth (k true)).choose (4 - 1) : ℝ) ≤
            (2 * ((2 * D).choose 3 : ℝ)) := by
          have h1 : M.card.choose 3 ≤ (2 * D).choose 3 := Nat.choose_le_choose 3 (by omega)
          have h2 : (M.card + 2 * tdepth (k true)).choose 3 ≤ (2 * D).choose 3 := Nat.choose_le_choose 3 (by omega)
          have h : M.card.choose 3 + (M.card + 2 * tdepth (k true)).choose 3 ≤ 2 * (2 * D).choose 3 := by omega
          exact_mod_cast h
        rw [hs] at hf
        have e := mul_le_mul_of_nonneg_left hcomb (by positivity : 0 ≤ 2*δ)
        nlinarith [mul_nonneg (by positivity : 0 ≤ 2*δ) hK0]



theorem comp_mass_le (D : ℕ) (oa : OracleComp (TSpec ι V) α) (hD : tdepth oa ≤ D) :
    (by classical exact ∑ y, P y * prT y A oa) ≤
      (by classical exact ∑ y, Q y * prT y A oa) + 32 * δ * (D : ℝ)^3 * amLen oa := by
  classical
  have h := comp_ctx_le_am P Q δ A hP hQ hδ h2 h3P h3Q D oa ∅ (by simpa using hD)
  have e : ∀ R : (ι → V) → ℝ, cmass A R ∅ ∅ oa = ∑ y, R y * prT y A oa := fun R => by
    unfold cmass
    refine sum_congr rfl fun y _ => ?_
    rw [if_pos (by simp [Ctx, AllHit])]
  rw [e P, e Q] at h
  have hk : ((2*D).choose 3 : ℝ) ≤ 8*(D : ℝ)^3 := by
    have hn := Nat.choose_le_pow (2*D) 3
    have hh : ((2*D).choose 3 : ℝ) ≤ ((2*D : ℕ) : ℝ)^3 := by exact_mod_cast hn
    convert hh using 1 <;> push_cast <;> ring
  have hal := amLen_nonneg oa
  simp only [Finset.card_empty, Nat.choose_zero_succ, Nat.cast_zero, zero_add] at h
  have he := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk hal) hδ
  nlinarith

omit hP hQ hδ h2 h3P h3Q
open SigGolfCandidate.T3 (Digest)
variable {C : Type} [Fintype C] [DecidableEq C] (n : Nat) (pt : C → Nat) (R : Finset C) (r : C → Digest)
theorem realLaw_kwise (hpt : Function.Injective pt) (hsmall : ∀ c, pt c < 1024) (h : R.card + 4 ≤ n) :
    KWise (realLaw n pt R r) 4 := by
  intro T v hT
  rw [realLaw, mass_pushW]
  dsimp only
  have hc := famA_card_extend (n := n) (r := r) hpt hsmall T v (by omega)
  have h0 := famA_card (n := n) (r := r) hpt hsmall (show R.card ≤ n by omega)
  have hp := pow_ratio (n - R.card) T.card (by omega)
  rw [show 128 * ((n - R.card) - T.card) = 128 * (n - (R.card + T.card)) by omega] at hp
  have hd : ((Fintype.card Digest : ℝ))⁻¹ ^ T.card = ((2 : ℝ) ^ 128)⁻¹ ^ T.card := by
    congr 2
    convert card_digest_real
  rw [hd, ← hp]
  have e1 : (((famA n pt R r).filter fun K => ∀ i ∈ T, familyEval (List.ofFn K) (pt i.val) = v i).card : ℝ) =
      (2 : ℝ) ^ (128 * (n - (R.card + T.card))) := by exact_mod_cast hc
  have e0 : ((famA n pt R r).card : ℝ) = (2 : ℝ) ^ (128 * (n - R.card)) := by exact_mod_cast h0
  rw [← e1, ← e0]
  congr

theorem hybLaw_kwise (hpt : Function.Injective pt) (hsmall : ∀ c, pt c < 1024) (a : Free R)
    (h : R.card + 4 ≤ n) : KWise (hybLaw n pt R r a) 4 := by
  intro T v hT
  rw [hybLaw, mass_pushW]
  dsimp only
  have h0 := famA_card (n := n) (r := r) hpt hsmall (show R.card ≤ n by omega)
  have hd : ((Fintype.card Digest : ℝ))⁻¹ ^ T.card = ((2 : ℝ) ^ 128)⁻¹ ^ T.card := by
    congr 2
    convert card_digest_real
  rw [hd]
  have hden : ((famA n pt R r ×ˢ (univ : Finset Digest)).card : ℝ) = (2 : ℝ) ^ (128 * (n - R.card) + 128) := by
    rw [Finset.card_product, Finset.card_univ]
    push_cast
    rw [h0, card_digest_real]
    push_cast
    rw [pow_add]
  by_cases ha : a ∈ T
  · have hset : ((famA n pt R r ×ˢ (univ : Finset Digest)).filter fun Ks : (Fin n → Digest) × Digest =>
        ∀ i ∈ T, (if i = a then Ks.2 else familyEval (List.ofFn Ks.1) (pt i.val)) = v i) =
        ((famA n pt R r).filter fun K => ∀ i ∈ T.erase a, familyEval (List.ofFn K) (pt i.val) = v i) ×ˢ
          {v a} := by
      ext ⟨K, s⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, Finset.mem_singleton,
        Finset.mem_erase]
      constructor
      · rintro ⟨hK, hT⟩
        refine ⟨⟨hK, fun i ⟨hne, hi⟩ => by simpa [hne] using hT i hi⟩, by simpa using hT a ha⟩
      · rintro ⟨⟨hK, hT⟩, rfl⟩
        refine ⟨hK, fun i hi => ?_⟩
        by_cases hia : i = a
        · simp [hia]
        · simpa [hia] using hT i ⟨hia, hi⟩
    have hT1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨a, ha⟩
    have hc := famA_card_extend (n := n) (r := r) hpt hsmall (T.erase a) v
      (by rw [Finset.card_erase_of_mem ha]; omega)
    rw [Finset.card_erase_of_mem ha] at hc
    have hnum : (((famA n pt R r ×ˢ (univ : Finset Digest)).filter fun Ks : (Fin n → Digest) × Digest =>
        ∀ i ∈ T, (if i = a then Ks.2 else familyEval (List.ofFn Ks.1) (pt i.val)) = v i).card : ℝ) =
        (2 : ℝ) ^ (128 * ((n - R.card + 1) - T.card)) := by
      rw [hset, Finset.card_product, Finset.card_singleton, mul_one, hc]
      push_cast
      congr 1
      omega
    have hp := pow_ratio (n - R.card + 1) T.card (by omega)
    rw [show 128 * (n - R.card + 1) = 128 * (n - R.card) + 128 by ring] at hp
    rw [← hp, ← hnum, ← hden]
    congr
  · have hset : ((famA n pt R r ×ˢ (univ : Finset Digest)).filter fun Ks : (Fin n → Digest) × Digest =>
        ∀ i ∈ T, (if i = a then Ks.2 else familyEval (List.ofFn Ks.1) (pt i.val)) = v i) =
        ((famA n pt R r).filter fun K => ∀ i ∈ T, familyEval (List.ofFn K) (pt i.val) = v i) ×ˢ univ := by
      ext ⟨K, s⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      constructor
      · rintro ⟨hK, hT⟩
        exact ⟨hK, fun i hi => by simpa [show i ≠ a from fun e => ha (e ▸ hi)] using hT i hi⟩
      · rintro ⟨hK, hT⟩
        exact ⟨hK, fun i hi => by simpa [show i ≠ a from fun e => ha (e ▸ hi)] using hT i hi⟩
    have hc := famA_card_extend (n := n) (r := r) hpt hsmall T v (by omega)
    have hnum : (((famA n pt R r ×ˢ (univ : Finset Digest)).filter fun Ks : (Fin n → Digest) × Digest =>
        ∀ i ∈ T, (if i = a then Ks.2 else familyEval (List.ofFn Ks.1) (pt i.val)) = v i).card : ℝ) =
        (2 : ℝ) ^ (128 * ((n - R.card) - T.card) + 128) := by
      rw [hset, Finset.card_product, Finset.card_univ, hc]
      push_cast
      rw [card_digest_real, ← pow_add]
      congr 1
      omega
    have hp := pow_ratio (n - R.card) T.card (by omega)
    have hm : ((2 : ℝ) ^ (128 * ((n - R.card) - T.card)) * 2 ^ 128) / (2 ^ (128 * (n - R.card)) * 2 ^ 128) =
        (2 : ℝ) ^ (128 * ((n - R.card) - T.card)) / 2 ^ (128 * (n - R.card)) :=
      mul_div_mul_right _ _ (by positivity)
    rw [← hp, ← hm, ← pow_add, ← pow_add, ← hnum, ← hden]
    congr

variable {n pt R r}
variable (Rev : Finset C)
variable (hpt : Function.Injective pt) (hsmall : ∀ c, pt c < 1024) (hRev : Rev.card + 4 ≤ n)
include hpt hsmall hRev
theorem kwise_hyps (r : C → Digest) (a : Free Rev) :
    (∀ S : Finset (Free Rev × Digest), S.card ≤ 3 →
      mass (realLaw n pt Rev r) (fun y => AllHit y S) = mass (hybLaw n pt Rev r a) (fun y => AllHit y S)) ∧
    (∀ S : Finset (Free Rev × Digest), S.card = 4 →
      mass (realLaw n pt Rev r) (fun y => AllHit y S) ≤ ((Fintype.card Digest : ℝ)⁻¹) ^ 4) ∧
    (∀ S : Finset (Free Rev × Digest), S.card = 4 →
      mass (hybLaw n pt Rev r a) (fun y => AllHit y S) ≤ ((Fintype.card Digest : ℝ)⁻¹) ^ 4) := by
  have hkP := realLaw_kwise n pt Rev r hpt hsmall hRev
  have hkQ := hybLaw_kwise n pt Rev r hpt hsmall a hRev
  have hP : ∀ y, 0 ≤ realLaw n pt Rev r y := pushW_nonneg _ _
  have hQ : ∀ y, 0 ≤ hybLaw n pt Rev r a y := pushW_nonneg _ _
  refine ⟨fun S hS => ?_, fun S hS => ?_, fun S hS => ?_⟩
  · rw [mass_allHit_of_kwise _ hP (k := 4) hkP S (by omega), mass_allHit_of_kwise _ hQ (k := 4) hkQ S (by omega)]
  · rw [mass_allHit_of_kwise _ hP hkP S (by omega), hS]
    split_ifs
    · exact le_rfl
    · positivity
  · rw [mass_allHit_of_kwise _ hQ hkQ S (by omega), hS]
    split_ifs
    · exact le_rfl
    · positivity

/-- **Family test, real ≤ hybrid.** -/
theorem family_test_le (a : Free Rev) {α : Type} (A : (C → Digest) → α → Prop)
    (tr : (C → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : ℕ) (hD : ∀ r, tdepth (tr r) ≤ D) :
    ∑ K : Fin n → Digest, prT (seedsY pt Rev K) (A (seedsR pt Rev K)) (tr (seedsR pt Rev K)) ≤
      ∑ K : Fin n → Digest, (∑ s, prT (seedsH pt Rev a K s) (A (seedsR pt Rev K)) (tr (seedsR pt Rev K))) / Fintype.card Digest +
        32 * ((Fintype.card Digest : ℝ)⁻¹) ^ 4 * (D : ℝ)^3 * ∑ K : Fin n → Digest, amLen (tr (seedsR pt Rev K)) := by
  rw [sum_group_real pt Rev (fun r y => prT y (A r) (tr r)), sum_group_hyb pt Rev a (fun r y => prT y (A r) (tr r)),
    sum_group_real pt Rev (fun r _ => amLen (tr r)), mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun r _ => ?_
  obtain ⟨h2, h3P, h3Q⟩ := kwise_hyps Rev hpt hsmall hRev r a
  have hc := comp_mass_le (realLaw n pt Rev r) (hybLaw n pt Rev r a) (((Fintype.card Digest : ℝ)⁻¹) ^ 4) (A r)
    (pushW_nonneg _ _) (pushW_nonneg _ _) (by positivity) h2 h3P h3Q D (tr r) (hD r)
  have hm : ∑ y, realLaw n pt Rev r y * amLen (tr r) = amLen (tr r) := by
    rw [← sum_mul, realLaw_sum hpt hsmall (by omega : Rev.card + 3 ≤ n), one_mul]
  rw [hm]
  have hcard : (0 : ℝ) ≤ (famA n pt Rev r).card := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hc hcard]

/-- **Family test, hybrid ≤ real.** -/
theorem family_test_ge (a : Free Rev) {α : Type} (A : (C → Digest) → α → Prop)
    (tr : (C → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : ℕ) (hD : ∀ r, tdepth (tr r) ≤ D) :
    ∑ K : Fin n → Digest, (∑ s, prT (seedsH pt Rev a K s) (A (seedsR pt Rev K)) (tr (seedsR pt Rev K))) / Fintype.card Digest ≤
      ∑ K : Fin n → Digest, prT (seedsY pt Rev K) (A (seedsR pt Rev K)) (tr (seedsR pt Rev K)) +
        32 * ((Fintype.card Digest : ℝ)⁻¹) ^ 4 * (D : ℝ)^3 * ∑ K : Fin n → Digest, amLen (tr (seedsR pt Rev K)) := by
  rw [sum_group_real pt Rev (fun r y => prT y (A r) (tr r)), sum_group_hyb pt Rev a (fun r y => prT y (A r) (tr r)),
    sum_group_real pt Rev (fun r _ => amLen (tr r)), mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun r _ => ?_
  obtain ⟨h2, h3P, h3Q⟩ := kwise_hyps Rev hpt hsmall hRev r a
  have hc := comp_mass_le (hybLaw n pt Rev r a) (realLaw n pt Rev r) (((Fintype.card Digest : ℝ)⁻¹) ^ 4) (A r)
    (pushW_nonneg _ _) (pushW_nonneg _ _) (by positivity) (fun S hS => (h2 S hS).symm) h3Q h3P D (tr r) (hD r)
  have hm : ∑ y, realLaw n pt Rev r y * amLen (tr r) = amLen (tr r) := by
    rw [← sum_mul, realLaw_sum hpt hsmall (by omega : Rev.card + 3 ≤ n), one_mul]
  rw [hm]
  have hcard : (0 : ℝ) ≤ (famA n pt Rev r).card := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hc hcard]

#print axioms family_test_le
#print axioms family_test_ge
end ClaudeWCT.Arith.SideChannel.Four
