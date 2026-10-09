import SigGolfCandidate.ClaudeR3.Q1
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fintype
import Mathlib.GroupTheory.Perm.Basic

open Finset

namespace ClaudeR3

theorem card_pairs (n : ℕ) : #{p : Fin n × Fin n | p.1 < p.2} = n.choose 2 := by
  have hc : n.choose 2 = #((univ : Finset (Fin n)).powersetCard 2) := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]
  rw [hc]
  refine Finset.card_bij (fun p _ => ({p.1, p.2} : Finset (Fin n))) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    rw [mem_powersetCard]
    exact ⟨subset_univ _, card_pair (ne_of_lt hp)⟩
  · intro p hp q hq hpq
    simp only [mem_filter, mem_univ, true_and] at hp hq
    have e : ({p.1, p.2} : Finset (Fin n)) = {q.1, q.2} := hpq
    have hp1 : p.1 ∈ ({q.1, q.2} : Finset (Fin n)) := e ▸ (by simp)
    have hp2 : p.2 ∈ ({q.1, q.2} : Finset (Fin n)) := e ▸ (by simp)
    simp only [mem_insert, mem_singleton] at hp1 hp2
    ext <;> omega
  · intro T hT
    rw [mem_powersetCard] at hT
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hT.2
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨(a, b), by simp [h], rfl⟩
    · exact ⟨(b, a), by simp [h], by simp [pair_comm]⟩

variable {β T : Type*} [Fintype β] [Fintype T] {r : ℕ}

theorem card_perm (σ : Equiv.Perm (Fin r)) (Q : (Fin r → β) × T → Prop) [DecidablePred Q] :
    #{p : (Fin r → β) × T | Q (p.1 ∘ σ, p.2)} = #{p : (Fin r → β) × T | Q p} := by
  refine Finset.card_equiv ((Equiv.arrowCongr σ.symm (Equiv.refl β)).prodCongr (Equiv.refl T)) fun p => ?_
  simp only [mem_filter, mem_univ, true_and, Equiv.prodCongr_apply, Equiv.arrowCongr_apply,
    Equiv.symm_symm, Equiv.coe_refl, Prod.map_apply, id_eq, Function.comp_id]
  rfl

variable (X : β → Prop) [DecidablePred X] (cov : (Fin r → β) → T → Prop) [∀ E t, Decidable (cov E t)]

theorem card_track1 (hsym : ∀ (σ : Equiv.Perm (Fin r)) E t, cov (E ∘ σ) t ↔ cov E t) (i₀ m : Fin r) :
    #{p : (Fin r → β) × T | X (p.1 m) ∧ cov p.1 p.2} = #{p : (Fin r → β) × T | X (p.1 i₀) ∧ cov p.1 p.2} := by
  rw [← card_perm (Equiv.swap i₀ m) (fun p => X (p.1 i₀) ∧ cov p.1 p.2)]
  congr 1
  refine filter_congr fun p _ => ?_
  simp only [Function.comp, Equiv.swap_apply_left]
  rw [hsym]

theorem card_track2 (hsym : ∀ (σ : Equiv.Perm (Fin r)) E t, cov (E ∘ σ) t ↔ cov E t) (i₀ i₁ m m' : Fin r)
    (hi : i₀ ≠ i₁) (hm : m ≠ m') :
    #{p : (Fin r → β) × T | X (p.1 m) ∧ X (p.1 m') ∧ cov p.1 p.2} =
      #{p : (Fin r → β) × T | X (p.1 i₀) ∧ X (p.1 i₁) ∧ cov p.1 p.2} := by
  set m'' := Equiv.swap i₀ m m'
  have hm'' : m'' ≠ i₀ := by
    intro h
    have := congrArg (Equiv.swap i₀ m) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact hm this.symm
  let σ : Equiv.Perm (Fin r) := (Equiv.swap i₁ m'').trans (Equiv.swap i₀ m)
  have h0 : σ i₀ = m := by
    show Equiv.swap i₀ m (Equiv.swap i₁ m'' i₀) = m
    rw [Equiv.swap_apply_of_ne_of_ne hi hm''.symm, Equiv.swap_apply_left]
  have h1 : σ i₁ = m' := by
    show Equiv.swap i₀ m (Equiv.swap i₁ m'' i₁) = m'
    rw [Equiv.swap_apply_left, Equiv.swap_apply_self]
  rw [← card_perm σ (fun p => X (p.1 i₀) ∧ X (p.1 i₁) ∧ cov p.1 p.2)]
  congr 1
  refine filter_congr fun p _ => ?_
  simp only [Function.comp, h0, h1]
  rw [hsym]

theorem bonf_count (hsym : ∀ (σ : Equiv.Perm (Fin r)) E t, cov (E ∘ σ) t ↔ cov E t) (i₀ i₁ : Fin r)
    (hi : i₀ ≠ i₁) (r' : ℕ) (hr' : r' ≤ r) :
    (#{p : (Fin r → β) × T | (∀ m, ¬ X (p.1 m)) ∧ cov p.1 p.2} : ℤ) ≤
      #{p : (Fin r → β) × T | cov p.1 p.2}
        - r' * #{p : (Fin r → β) × T | X (p.1 i₀) ∧ cov p.1 p.2}
        + (r'.choose 2 : ℤ) * #{p : (Fin r → β) × T | X (p.1 i₀) ∧ X (p.1 i₁) ∧ cov p.1 p.2} := by
  let ι : Fin r' → Fin r := Fin.castLE hr'
  have hι : Function.Injective ι := Fin.castLE_injective hr'

  have hpt : ∀ p : (Fin r → β) × T,
      (if (∀ m, ¬ X (p.1 m)) ∧ cov p.1 p.2 then (1 : ℤ) else 0) ≤
        (if cov p.1 p.2 then (1 : ℤ) else 0) - ∑ j : Fin r', (if X (p.1 (ι j)) ∧ cov p.1 p.2 then 1 else 0) +
          ∑ q ∈ (univ : Finset (Fin r' × Fin r')).filter (fun q => q.1 < q.2),
            (if X (p.1 (ι q.1)) ∧ X (p.1 (ι q.2)) ∧ cov p.1 p.2 then 1 else 0) := by
    intro p
    by_cases hc : cov p.1 p.2
    · have hb := bonferroni2 (fun j : Fin r' => X (p.1 (ι j)))
      have hle : ((if (∀ m, ¬ X (p.1 m)) ∧ cov p.1 p.2 then (1 : ℤ) else 0)) ≤
          (if ∀ j : Fin r', ¬ X (p.1 (ι j)) then 1 else 0) := by
        by_cases h : ∀ m, ¬ X (p.1 m)
        · rw [if_pos ⟨h, hc⟩, if_pos (fun j => h _)]
        · rw [if_neg (fun h' => h h'.1)]; split_ifs <;> norm_num
      refine hle.trans (hb.trans (le_of_eq ?_))
      simp only [hc, and_true, if_true]
      congr 1
      refine sum_congr rfl fun q _ => ?_
      by_cases h1 : X (p.1 (ι q.1)) <;> by_cases h2 : X (p.1 (ι q.2)) <;> simp [h1, h2]
    · simp [hc]
  have hsum := sum_le_sum fun p (_ : p ∈ (univ : Finset ((Fin r → β) × T))) => hpt p
  rw [sum_add_distrib, sum_sub_distrib] at hsum
  rw [natCast_card_filter, natCast_card_filter]
  refine hsum.trans (le_of_eq ?_)
  rw [Finset.sum_comm (f := fun (p : (Fin r → β) × T) (j : Fin r') => if X (p.1 (ι j)) ∧ cov p.1 p.2 then (1 : ℤ) else 0),
    Finset.sum_comm (f := fun (p : (Fin r → β) × T) (q : Fin r' × Fin r') =>
      if X (p.1 (ι q.1)) ∧ X (p.1 (ι q.2)) ∧ cov p.1 p.2 then (1 : ℤ) else 0)]
  have e1 : ∀ j : Fin r', ∑ p : (Fin r → β) × T, (if X (p.1 (ι j)) ∧ cov p.1 p.2 then (1 : ℤ) else 0) =
      #{p : (Fin r → β) × T | X (p.1 i₀) ∧ cov p.1 p.2} := by
    intro j
    rw [← natCast_card_filter, card_track1 X cov hsym i₀ (ι j)]
  have e2 : ∀ q ∈ (univ : Finset (Fin r' × Fin r')).filter (fun q => q.1 < q.2),
      ∑ p : (Fin r → β) × T, (if X (p.1 (ι q.1)) ∧ X (p.1 (ι q.2)) ∧ cov p.1 p.2 then (1 : ℤ) else 0) =
      #{p : (Fin r → β) × T | X (p.1 i₀) ∧ X (p.1 i₁) ∧ cov p.1 p.2} := by
    intro q hq
    have hlt : q.1 < q.2 := (mem_filter.mp hq).2
    rw [← natCast_card_filter, card_track2 X cov hsym i₀ i₁ (ι q.1) (ι q.2) hi
      (fun h => absurd (hι h) (ne_of_lt hlt))]
  rw [sum_congr rfl fun j _ => e1 j, sum_congr rfl e2, sum_const, sum_const, card_univ, Fintype.card_fin,
    card_pairs, nsmul_eq_mul, nsmul_eq_mul]

end ClaudeR3
