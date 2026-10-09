import SigGolfCandidate.ClaudeWCT.Numerics.N600Price
import SigGolfCandidate.ClaudeR3.Q2

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
