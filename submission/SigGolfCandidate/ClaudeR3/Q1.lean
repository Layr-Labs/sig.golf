import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset

namespace ClaudeR3

theorem bonf_nat (k : ℕ) : ((if k = 0 then 1 else 0 : ℤ)) ≤ 1 - k + (k.choose 2 : ℤ) := by
  rcases k with _ | k
  · simp
  · have h : (k + 1).choose 2 = k + k.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    simp only [Nat.succ_ne_zero, if_false, h]
    push_cast
    have : (0 : ℤ) ≤ (k.choose 2 : ℤ) := Nat.cast_nonneg _
    linarith

variable {r : ℕ}

theorem bonferroni2 (X : Fin r → Prop) [DecidablePred X] :
    ((if ∀ j, ¬ X j then 1 else 0 : ℤ)) ≤
      1 - ∑ j, (if X j then 1 else 0 : ℤ) +
        ∑ p ∈ (univ : Finset (Fin r × Fin r)).filter (fun p => p.1 < p.2),
          (if X p.1 then 1 else 0 : ℤ) * (if X p.2 then 1 else 0) := by
  set S := (univ : Finset (Fin r)).filter X with hS
  have hk : ∑ j, (if X j then 1 else 0 : ℤ) = S.card := by
    rw [← sum_filter]; simp [hS]
  have hpairs : ∑ p ∈ (univ : Finset (Fin r × Fin r)).filter (fun p => p.1 < p.2),
      (if X p.1 then 1 else 0 : ℤ) * (if X p.2 then 1 else 0) = (S.card.choose 2 : ℤ) := by
    have : ∀ p : Fin r × Fin r, (if X p.1 then 1 else 0 : ℤ) * (if X p.2 then 1 else 0) =
        if X p.1 ∧ X p.2 then 1 else 0 := by
      intro p; by_cases h1 : X p.1 <;> by_cases h2 : X p.2 <;> simp [h1, h2]
    simp_rw [this]
    rw [← sum_filter, sum_const, nsmul_one, filter_filter]
    congr 1
    rw [← Finset.card_powersetCard 2 S]
    refine Finset.card_bij (fun p _ => ({p.1, p.2} : Finset (Fin r))) ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      rw [mem_powersetCard]
      refine ⟨?_, card_pair (ne_of_lt hp.1)⟩
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hS, hp.2.1, hp.2.2]
    · intro p hp q hq hpq
      simp only [mem_filter, mem_univ, true_and] at hp hq
      have h1 := hp.1; have h2 := hq.1
      have e : ({p.1, p.2} : Finset (Fin r)) = {q.1, q.2} := hpq
      have hp1 : p.1 ∈ ({q.1, q.2} : Finset (Fin r)) := e ▸ (by simp)
      have hp2 : p.2 ∈ ({q.1, q.2} : Finset (Fin r)) := e ▸ (by simp)
      simp only [mem_insert, mem_singleton] at hp1 hp2
      ext <;> omega
    · intro T hT
      rw [mem_powersetCard] at hT
      obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hT.2
      rcases lt_or_gt_of_ne hab with h | h
      · refine ⟨(a, b), ?_, rfl⟩
        simp only [mem_filter, mem_univ, true_and]
        refine ⟨h, ?_, ?_⟩ <;> [exact (mem_filter.mp (hT.1 (by simp))).2; exact (mem_filter.mp (hT.1 (by simp))).2]
      · refine ⟨(b, a), ?_, by simp [pair_comm]⟩
        simp only [mem_filter, mem_univ, true_and]
        refine ⟨h, ?_, ?_⟩ <;> [exact (mem_filter.mp (hT.1 (by simp))).2; exact (mem_filter.mp (hT.1 (by simp))).2]
  have hnone : ((if ∀ j, ¬ X j then 1 else 0 : ℤ)) = if S.card = 0 then 1 else 0 := by
    have : (∀ j, ¬ X j) ↔ S.card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]; simp
    by_cases h : ∀ j, ¬ X j
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]
  rw [hnone, hk, hpairs]
  exact bonf_nat S.card

end ClaudeR3
