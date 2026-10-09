import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fintype
import Mathlib.GroupTheory.Perm.Basic
import SigGolfCandidate.ClaudeWCT.Numerics.N600Price
import SigGolfCandidate.ClaudeWCT.Numerics.CoverW1

section
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
end

section
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
end

section
namespace ClaudeR3.Law
open Finset ENNReal
open ClaudeWCT.Numerics.Law (lawAvg lawAvg_succ lawAvg_zero)
open ClaudeWCT.Numerics.Thinning (env ListCov listCov_ofFn FullCov CovAt nearEnv ListCovExcept
  listCovExcept_ofFn FullNear)
open SigGolfResearch.Gate6.Moments (finiteAverage)

theorem lawAvg_eq_sum {β : Type} [Fintype β] (v : β → ENNReal) :
    ∀ (r : ℕ) (f : List β → ENNReal), lawAvg v r f = ∑ E : Fin r → β, (∏ m, v (E m)) * f (List.ofFn E)
  | 0, f => by
    rw [lawAvg_zero, Fintype.sum_unique]
    simp
  | r + 1, f => by
    rw [lawAvg_succ]
    simp_rw [lawAvg_eq_sum v r]
    rw [← (Fin.consEquiv fun _ : Fin (r + 1) => β).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun b _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun E _ => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, List.ofFn_succ, mul_assoc]

section
variable {β : Type} [Fintype β] [DecidableEq β] {C : Type} [Fintype C] [DecidableEq C]

theorem prod_uniformOn {r : ℕ} (S : Finset (Fin 9 → C × β)) (E : Fin r → Fin 9 → C × β) :
    ∏ m, ClaudeWCT.Numerics.N600.uniformOn S (E m) =
      if ∀ m, E m ∈ S then ((S.card : ENNReal)⁻¹) ^ r else 0 := by
  classical
  unfold ClaudeWCT.Numerics.N600.uniformOn
  by_cases h : ∀ m, E m ∈ S
  · rw [if_pos h]
    simp only [h, if_true, prod_const, card_univ, Fintype.card_fin]
  · rw [if_neg h]
    push Not at h
    obtain ⟨m, hm⟩ := h
    exact prod_eq_zero (mem_univ m) (if_neg hm)

theorem lawAvg_uniformOn_count {r : ℕ} {T : Type} [Fintype T] (S : Finset (Fin 9 → C × β))
    (Pt : List (Fin 9 → C × β) → T → Prop) [∀ L, DecidablePred (Pt L)] :
    lawAvg (ClaudeWCT.Numerics.N600.uniformOn S) r (fun L => finiteAverage (fun t : T => if Pt L t then 1 else 0)) =
      (#{p : (Fin r → Fin 9 → C × β) × T | (∀ m, p.1 m ∈ S) ∧ Pt (List.ofFn p.1) p.2} : ENNReal) /
        ((S.card : ENNReal) ^ r * Fintype.card T) := by
  classical
  rw [lawAvg_eq_sum]
  simp_rw [prod_uniformOn]
  rw [natCast_card_filter, Fintype.sum_prod_type]
  simp only [finiteAverage, div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))),
    ← ENNReal.inv_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun E _ => ?_
  rcases em (∀ m, E m ∈ S) with hE | hE
  · simp only [hE, implies_true, if_true, true_and]
    ring
  · simp [hE]

end

theorem listCov_perm {c n : ℕ} {β : Type} {C : Type} (val : β → Fin c → ℕ) {r : ℕ} (σ : Equiv.Perm (Fin r))
    (E : Fin r → Fin n → C × β) (t : Fin n → C × β) :
    ListCov val (List.ofFn (E ∘ σ)) t ↔ ListCov val (List.ofFn E) t := by
  rw [listCov_ofFn, listCov_ofFn]
  unfold FullCov CovAt
  refine forall_congr' fun k => forall_congr' fun i => ?_
  constructor
  · rintro ⟨m, h⟩; exact ⟨σ m, h⟩
  · rintro ⟨m, h⟩; exact ⟨σ.symm m, by simpa using h⟩

theorem listCovExcept_perm {c n : ℕ} {β : Type} {C : Type} (val : β → Fin c → ℕ) (k₀ : Fin n) (i₀ : Fin c)
    {r : ℕ} (σ : Equiv.Perm (Fin r)) (E : Fin r → Fin n → C × β) (t : Fin n → C × β) :
    ListCovExcept val k₀ i₀ (List.ofFn (E ∘ σ)) t ↔ ListCovExcept val k₀ i₀ (List.ofFn E) t := by
  rw [listCovExcept_ofFn, listCovExcept_ofFn]
  unfold FullNear
  refine forall_congr' fun k => forall_congr' fun i => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨m, h⟩; exact ⟨σ m, h⟩
  · rintro ⟨m, h⟩; exact ⟨σ.symm m, by simpa using h⟩

end ClaudeR3.Law
end

section
namespace ClaudeR3.PoissonJ
open ENNReal SphincsSecurity.Concrete
open ClaudeWCT.Numerics.Kernel (fact)
open ClaudeWCT.Numerics.PoissonReflect (binomWeight binomWeight_le binomialAverage_truncate binomial_tail
  range_foldr_eq_sum fact_eq scale_le)

def poissonCheckJ (Dv un ud ln ld : Nat) (f : Nat → Nat) (dbase sn sd Mn Md R : Nat) : Bool :=
  let S := (List.range (R + 1)).foldr (fun r s =>
    un * ln ^ r * ld ^ (R - r) * (fact R / fact r) * f r * Dv ^ (R - r) + s) 0
  Md * sn * (S * ld * (R + 1) + ln ^ (R + 1) * ud * dbase * Dv ^ R) ≤
    Mn * sd * ud * dbase * ld ^ (R + 1) * fact (R + 1) * Dv ^ R

def termNumJ (Dv un ln ld R : ℕ) (f : ℕ → ℕ) (r : ℕ) : ℕ :=
  un * ln ^ r * ld ^ (R - r) * (fact R / fact r) * f r * Dv ^ (R - r)
def denomJ (Dv ud ld dbase R : ℕ) : ℕ :=
  ud * dbase * ld ^ (R + 1) * fact (R + 1) * Dv ^ R
theorem denomJ_pos {Dv : ℕ} (hQ : 0 < Dv) (ud ld dbase R : ℕ) (hud : 0 < ud) (hld : 0 < ld) (hdb : 0 < dbase) :
    0 < denomJ Dv ud ld dbase R := by
  unfold denomJ
  rw [fact_eq]
  positivity
theorem termJ_eq {Dv : ℕ} (hQ : 0 < Dv) (un ud ln ld dbase R r : ℕ) (f : ℕ → ℕ) (hr : r ≤ R) (hud : 0 < ud)
    (hld : 0 < ld) (hdb : 0 < dbase) :
    (un : ENNReal) / ud * ((ln : ENNReal) / ld) ^ r / (r.factorial : ENNReal) *
        ((f r : ENNReal) / ((dbase * Dv ^ r : ℕ) : ENNReal)) =
      ((termNumJ Dv un ln ld R f r * ld * (R + 1) : ℕ) : ENNReal) / (denomJ Dv ud ld dbase R : ℕ) := by
  have hD := denomJ_pos hQ ud ld dbase R hud hld hdb
  have hne1 : (un : ENNReal) / ud * ((ln : ENNReal) / ld) ^ r / (r.factorial : ENNReal) *
      ((f r : ENNReal) / ((dbase * Dv ^ r : ℕ) : ENNReal)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.div_ne_top _ (by exact_mod_cast (Nat.factorial_pos r).ne')
      apply ENNReal.mul_ne_top (ENNReal.div_ne_top (by simp) (by exact_mod_cast hud.ne'))
      exact ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp) (by exact_mod_cast hld.ne'))
    · exact ENNReal.div_ne_top (by simp)
        (by exact_mod_cast (by positivity : 0 < dbase * Dv ^ r).ne')
  have hne2 : ((termNumJ Dv un ln ld R f r * ld * (R + 1) : ℕ) : ENNReal) /
      (denomJ Dv ud ld dbase R : ℕ) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hD.ne')
  apply (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  unfold termNumJ denomJ
  rw [Nat.add_sub_cancel_left, fact_eq, fact_eq, fact_eq, Nat.factorial_succ (r + k)]
  have hdvd : r.factorial ∣ (r + k).factorial := Nat.factorial_dvd_factorial (Nat.le_add_right r k)
  have hf0 : ((r.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  have hfk : (((r + k).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hud' : (ud : ℝ) ≠ 0 := by exact_mod_cast hud.ne'
  have hld' : (ld : ℝ) ≠ 0 := by exact_mod_cast hld.ne'
  have hdb' : (dbase : ℝ) ≠ 0 := by exact_mod_cast hdb.ne'
  have hQ' : (Dv : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  push_cast [Nat.cast_div hdvd hf0]
  simp only [div_pow]
  field_simp
  ring
theorem tailJ_eq {Dv : ℕ} (hQ : 0 < Dv) (ud ln ld dbase R : ℕ) (hud : 0 < ud) (hld : 0 < ld) (hdb : 0 < dbase) :
    ((ln : ENNReal) / ld) ^ (R + 1) / ((R + 1).factorial : ENNReal) =
      ((ln ^ (R + 1) * ud * dbase * Dv ^ R : ℕ) : ENNReal) / (denomJ Dv ud ld dbase R : ℕ) := by
  have hD := denomJ_pos hQ ud ld dbase R hud hld hdb
  have hne1 : ((ln : ENNReal) / ld) ^ (R + 1) / ((R + 1).factorial : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp)
      (by exact_mod_cast hld.ne'))) (by exact_mod_cast (Nat.factorial_pos _).ne')
  have hne2 : ((ln ^ (R + 1) * ud * dbase * Dv ^ R : ℕ) : ENNReal) /
      (denomJ Dv ud ld dbase R : ℕ) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hD.ne')
  apply (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  unfold denomJ
  rw [fact_eq]
  have hf0 : (((R + 1).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hud' : (ud : ℝ) ≠ 0 := by exact_mod_cast hud.ne'
  have hld' : (ld : ℝ) ≠ 0 := by exact_mod_cast hld.ne'
  have hdb' : (dbase : ℝ) ≠ 0 := by exact_mod_cast hdb.ne'
  have hQ' : (Dv : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  push_cast
  simp only [div_pow]
  field_simp
theorem binomWeight_tilt_le' (rate : ENNReal) (T R r : ℕ) (hr : r ≤ R) (κ lam u : ENNReal)
    (hlam : (T : ENNReal) * rate * κ ≤ lam) (hu : (1 - rate) ^ (T - R) ≤ u) :
    binomWeight rate T r * κ ^ r ≤ u * lam ^ r / r.factorial := by
  have h := binomWeight_le rate T R r hr ((T : ENNReal) * rate) u le_rfl hu
  calc binomWeight rate T r * κ ^ r ≤ u * ((T : ENNReal) * rate) ^ r / r.factorial * κ ^ r :=
        mul_le_mul' h le_rfl
    _ = u * ((T : ENNReal) * rate * κ) ^ r / r.factorial := by
        simp only [div_eq_mul_inv, mul_pow]; ring
    _ ≤ u * lam ^ r / r.factorial := by gcongr
theorem poissonCheckJ_sound {Dv un ud ln ld : ℕ} {f : ℕ → ℕ} {dbase sn sd Mn Md R : ℕ}
    (hcheck : poissonCheckJ Dv un ud ln ld f dbase sn sd Mn Md R = true) (hQ : 0 < Dv)
    (hud : 0 < ud) (hld : 0 < ld) (hdb : 0 < dbase) (hsd : 0 < sd) (hMd : 0 < Md)
    {rate : ENNReal} (hrate : rate ≤ 1) {T : ℕ} (κ : ENNReal) (hκ : 1 ≤ κ)
    (hlam : (T : ENNReal) * rate * κ ≤ (ln : ENNReal) / ld)
    (hu : (1 - rate) ^ (T - R) ≤ (un : ENNReal) / ud)
    (g : ℕ → ENNReal)
    (hpay : ∀ r ≤ R, g r ≤ κ ^ r * ((f r : ENNReal) / ((dbase * Dv ^ r : ℕ) : ENNReal)))
    (htail : ∀ r, R < r → g r ≤ 1) :
    (sn : ENNReal) / sd * binomialAverage rate T g ≤ (Mn : ENNReal) / Md := by
  have hineq : Md * sn * ((∑ r ∈ Finset.range (R + 1), termNumJ Dv un ln ld R f r) * ld * (R + 1) +
      ln ^ (R + 1) * ud * dbase * Dv ^ R) ≤ Mn * sd * denomJ Dv ud ld dbase R := by
    have h := hcheck
    simp only [poissonCheckJ, decide_eq_true_eq] at h
    rw [range_foldr_eq_sum] at h
    unfold denomJ termNumJ
    refine h.trans_eq ?_
    ring
  have hD := denomJ_pos hQ ud ld dbase R hud hld hdb
  refine le_trans (mul_le_mul' le_rfl ?_) (scale_le sn sd Mn Md _ _ hsd hMd hD hineq)
  refine (binomialAverage_truncate rate T (R + 1) g 1 (fun r hr => htail r hr)).trans ?_
  have hsplit : ((((∑ r ∈ Finset.range (R + 1), termNumJ Dv un ln ld R f r) * ld * (R + 1) +
      ln ^ (R + 1) * ud * dbase * Dv ^ R : ℕ)) : ENNReal) / (denomJ Dv ud ld dbase R : ℕ) =
      (∑ r ∈ Finset.range (R + 1),
        ((termNumJ Dv un ln ld R f r * ld * (R + 1) : ℕ) : ENNReal) / (denomJ Dv ud ld dbase R : ℕ)) +
      ((ln ^ (R + 1) * ud * dbase * Dv ^ R : ℕ) : ENNReal) / (denomJ Dv ud ld dbase R : ℕ) := by
    rw [Finset.sum_mul, Finset.sum_mul, Nat.cast_add, Nat.cast_sum, ENNReal.add_div]
    congr 1
    simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [one_mul, hsplit]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro r hr
    have hr' : r ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [← termJ_eq hQ un ud ln ld dbase R r f hr' hud hld hdb]
    calc binomWeight rate T r * g r
        ≤ binomWeight rate T r * (κ ^ r * ((f r : ENNReal) / ((dbase * Dv ^ r : ℕ) : ENNReal))) :=
          mul_le_mul' le_rfl (hpay r hr')
      _ = binomWeight rate T r * κ ^ r * ((f r : ENNReal) / ((dbase * Dv ^ r : ℕ) : ENNReal)) := by ring
      _ ≤ (un : ENNReal) / ud * ((ln : ENNReal) / ld) ^ r / (r.factorial : ENNReal) *
            ((f r : ENNReal) / ((dbase * Dv ^ r : ℕ) : ENNReal)) := by
          refine mul_le_mul' ?_ le_rfl
          exact binomWeight_tilt_le' rate T R r hr' κ _ _ hlam hu
  · refine (binomial_tail rate hrate T (R + 1)).trans ?_
    rw [← tailJ_eq hQ ud ln ld dbase R hud hld hdb]
    have hlam0 : (T : ENNReal) * rate ≤ (ln : ENNReal) / ld :=
      le_trans (le_mul_of_one_le_right' hκ) hlam
    gcongr
end ClaudeR3.PoissonJ
end

section
namespace ClaudeR3.Prod9
open Finset Polynomial

variable {Y : Type*} [DecidableEq Y]

noncomputable def genP (S : Finset Y) (a b : Y → ℕ) : ℕ[X] := ∑ y ∈ S, X ^ (a y + 154 * b y)

def Ntop : ℕ := 153 + 154 * 153

theorem sum_le_153 (a : Y → ℕ) (ha : ∀ y, a y ≤ 17) (x : Fin 9 → Y) : ∑ i, a (x i) ≤ 153 := by
  calc ∑ i, a (x i) ≤ ∑ _i : Fin 9, 17 := sum_le_sum fun i _ => ha (x i)
    _ = 153 := by simp

theorem fiber_count (C : Fin 9 → Finset Y) (a b : Y → ℕ) (ha : ∀ y, a y ≤ 17) (hb : ∀ y, b y ≤ 17)
    (s₁ s₂ : ℕ) (hs₁ : s₁ ≤ 153) :
    #{x ∈ Fintype.piFinset C | ∑ i, a (x i) = s₁ ∧ ∑ i, b (x i) = s₂} =
      (∏ i, genP (C i) a b).coeff (s₁ + 154 * s₂) := by
  unfold genP
  rw [← ClaudeWCT.Numerics.card_pi_sum_eq_coeff C (fun y => a y + 154 * b y) (s₁ + 154 * s₂)]
  congr 1
  refine filter_congr fun x _ => ?_
  have h1 := sum_le_153 a ha x
  rw [sum_add_distrib, ← mul_sum]
  omega

theorem tail2_count (C : Fin 9 → Finset Y) (a b : Y → ℕ) (ha : ∀ y, a y ≤ 17) (hb : ∀ y, b y ≤ 17)
    (A : ℕ) :
    #{x ∈ Fintype.piFinset C | A < ∑ i, a (x i) ∧ A < ∑ i, b (x i)} =
      ∑ s₁ ∈ Ioc A 153, ∑ s₂ ∈ Ioc A 153, (∏ i, genP (C i) a b).coeff (s₁ + 154 * s₂) := by
  have hmaps : ∀ x ∈ ({x ∈ Fintype.piFinset C | A < ∑ i, a (x i) ∧ A < ∑ i, b (x i)} : Finset _),
      (∑ i, a (x i), ∑ i, b (x i)) ∈ Ioc A 153 ×ˢ Ioc A 153 := by
    intro x hx
    rw [mem_filter] at hx
    have h1 := sum_le_153 a ha x
    have h2 := sum_le_153 b hb x
    simp only [mem_product, mem_Ioc]
    omega
  rw [card_eq_sum_card_fiberwise hmaps, sum_product]
  refine sum_congr rfl fun s₁ hs₁ => sum_congr rfl fun s₂ hs₂ => ?_
  rw [← fiber_count C a b ha hb s₁ s₂ (mem_Ioc.mp hs₁).2, filter_filter]
  congr 1
  refine filter_congr fun x _ => ?_
  simp only [Prod.mk.injEq]
  have := mem_Ioc.mp hs₁
  have := mem_Ioc.mp hs₂
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, by omega⟩, h1, h2⟩

theorem tail1_count (C : Fin 9 → Finset Y) (a b : Y → ℕ) (ha : ∀ y, a y ≤ 17) (hb : ∀ y, b y ≤ 17)
    (A : ℕ) :
    #{x ∈ Fintype.piFinset C | A < ∑ i, a (x i)} =
      ∑ s₁ ∈ Ioc A 153, ∑ s₂ ∈ range 154, (∏ i, genP (C i) a b).coeff (s₁ + 154 * s₂) := by
  have hmaps : ∀ x ∈ ({x ∈ Fintype.piFinset C | A < ∑ i, a (x i)} : Finset _),
      (∑ i, a (x i), ∑ i, b (x i)) ∈ Ioc A 153 ×ˢ range 154 := by
    intro x hx
    rw [mem_filter] at hx
    have h1 := sum_le_153 a ha x
    have h2 := sum_le_153 b hb x
    simp only [mem_product, mem_Ioc, mem_range]
    omega
  rw [card_eq_sum_card_fiberwise hmaps, sum_product]
  refine sum_congr rfl fun s₁ hs₁ => sum_congr rfl fun s₂ hs₂ => ?_
  rw [← fiber_count C a b ha hb s₁ s₂ (mem_Ioc.mp hs₁).2, filter_filter]
  congr 1
  refine filter_congr fun x _ => ?_
  simp only [Prod.mk.injEq]
  have := mem_Ioc.mp hs₁
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩

theorem base_count (C : Fin 9 → Finset Y) (a b : Y → ℕ) :
    #(Fintype.piFinset C) = (∏ i, genP (C i) a b).eval 1 := by
  rw [Fintype.card_piFinset, eval_prod]
  refine prod_congr rfl fun i _ => ?_
  simp [genP, eval_finset_sum]

theorem reflect_Ioc (A : ℕ) (hA : A < 153) (f : ℕ → ℕ) :
    ∑ i ∈ range (153 - A), f (153 - i) = ∑ s ∈ Ioc A 153, f s := by
  refine sum_nbij' (fun i => 153 - i) (fun s => 153 - s) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_range, coe_range, Set.mem_Iio] at hi; simp only [mem_Ioc, coe_Ioc, Set.mem_Ioc]; omega
  · intro s hs; simp only [mem_Ioc, coe_Ioc, Set.mem_Ioc] at hs; simp only [mem_range, coe_range, Set.mem_Iio]; omega
  · intro i hi; simp only [mem_range, coe_range, Set.mem_Iio] at hi; omega
  · intro s hs; simp only [mem_Ioc, coe_Ioc, Set.mem_Ioc] at hs; omega
  · intro i _; rfl

theorem reflect_range (f : ℕ → ℕ) : ∑ j ∈ range 154, f (153 - j) = ∑ s ∈ range 154, f s := by
  have h := Finset.sum_range_reflect f 154
  simpa using h

noncomputable def Mask (n₁ n₂ : ℕ) : ℕ[X] := ∑ i ∈ range n₁, ∑ j ∈ range n₂, X ^ (i + 154 * j)

theorem Mask_eval (n₁ n₂ B : ℕ) :
    (Mask n₁ n₂).eval B = (∑ i ∈ range n₁, B ^ i) * ∑ j ∈ range n₂, B ^ (154 * j) := by
  rw [Mask, eval_finset_sum, sum_mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [eval_finset_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_pow, eval_X, pow_add]

theorem Mask_eval_one (n₁ n₂ : ℕ) : (Mask n₁ n₂).eval 1 = n₁ * n₂ := by
  rw [Mask_eval]; simp

theorem coeff_mul_mask (P : ℕ[X]) (n₁ n₂ : ℕ) (h₁ : n₁ ≤ 154) (h₂ : n₂ ≤ 154) :
    (P * Mask n₁ n₂).coeff Ntop =
      ∑ i ∈ range n₁, ∑ j ∈ range n₂, P.coeff ((153 - i) + 154 * (153 - j)) := by
  rw [Mask]
  simp_rw [mul_sum, finset_sum_coeff, coeff_mul_X_pow']
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  rw [if_pos (by unfold Ntop; omega)]
  congr 1
  unfold Ntop
  omega

theorem coeff_mask2 (P : ℕ[X]) (A : ℕ) (hA : A < 153) :
    (P * Mask (153 - A) (153 - A)).coeff Ntop = ∑ s₁ ∈ Ioc A 153, ∑ s₂ ∈ Ioc A 153, P.coeff (s₁ + 154 * s₂) := by
  rw [coeff_mul_mask P _ _ (by omega) (by omega)]
  rw [← reflect_Ioc A hA (fun s₁ => ∑ s₂ ∈ Ioc A 153, P.coeff (s₁ + 154 * s₂))]
  refine sum_congr rfl fun i _ => ?_
  exact reflect_Ioc A hA (fun s₂ => P.coeff ((153 - i) + 154 * s₂))

theorem coeff_mask1 (P : ℕ[X]) (A : ℕ) (hA : A < 153) :
    (P * Mask (153 - A) 154).coeff Ntop = ∑ s₁ ∈ Ioc A 153, ∑ s₂ ∈ range 154, P.coeff (s₁ + 154 * s₂) := by
  rw [coeff_mul_mask P _ _ (by omega) le_rfl]
  rw [← reflect_Ioc A hA (fun s₁ => ∑ s₂ ∈ range 154, P.coeff (s₁ + 154 * s₂))]
  refine sum_congr rfl fun i _ => ?_
  exact reflect_range (fun s₂ => P.coeff ((153 - i) + 154 * s₂))

theorem extract (Q : ℕ[X]) (B : ℕ) (hB : Q.eval 1 < B) (j : ℕ) : Q.coeff j = Q.eval B / B ^ j % B := by
  have hB0 : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hB
  rw [ClaudeWCT.Numerics.eval_div_pow_mod hB0 j Q fun i =>
    lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one Q i) hB]

theorem tail2_extract (C : Fin 9 → Finset Y) (a b : Y → ℕ) (ha : ∀ y, a y ≤ 17) (hb : ∀ y, b y ≤ 17)
    (A : ℕ) (hA : A < 153) (B : ℕ)
    (hB : (∏ i, genP (C i) a b).eval 1 * ((153 - A) * (153 - A)) < B) :
    #{x ∈ Fintype.piFinset C | A < ∑ i, a (x i) ∧ A < ∑ i, b (x i)} =
      (∏ i, genP (C i) a b).eval B * (Mask (153 - A) (153 - A)).eval B / B ^ Ntop % B := by
  rw [tail2_count C a b ha hb A, ← coeff_mask2 _ A hA,
    extract _ B (by rw [eval_mul, Mask_eval_one]; exact hB), eval_mul]

theorem tail1_extract (C : Fin 9 → Finset Y) (a b : Y → ℕ) (ha : ∀ y, a y ≤ 17) (hb : ∀ y, b y ≤ 17)
    (A : ℕ) (hA : A < 153) (B : ℕ)
    (hB : (∏ i, genP (C i) a b).eval 1 * ((153 - A) * 154) < B) :
    #{x ∈ Fintype.piFinset C | A < ∑ i, a (x i)} =
      (∏ i, genP (C i) a b).eval B * (Mask (153 - A) 154).eval B / B ^ Ntop % B := by
  rw [tail1_count C a b ha hb A, ← coeff_mask1 _ A hA,
    extract _ B (by rw [eval_mul, Mask_eval_one]; exact hB), eval_mul]

end ClaudeR3.Prod9
end
