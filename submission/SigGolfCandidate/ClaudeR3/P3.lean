import SigGolfCandidate.ClaudeWCT.Numerics.N600Cover

namespace ClaudeR3.IE
open Finset
open ClaudeWCT.Numerics.N600 (sgnU Compat FreeOk M1 M2 compat_iff sum_fin6_single)

section
variable {β : Type*} [Fintype β] {C : Type*} [Fintype C] [DecidableEq C] (val : β → Fin 6 → ℕ)

def CovAtM {p : ℕ} (free : Fin 6 → Bool) (c : C) (v : Fin 6 → ℕ) (E : Fin p → C × β) : Prop :=
  ∀ j, free j = false → ∃ m, (E m).1 = c ∧ v j ≤ val (E m).2 j

instance {p : ℕ} (free : Fin 6 → Bool) (c : C) (v : Fin 6 → ℕ) : DecidablePred (CovAtM val (p := p) free c v) :=
  fun _ => Fintype.decidableForallFintype

def Alw (c : C) (u : Fin 6 → Fin 6) (x : C × β) : Prop := x.1 = c → ∀ j, val x.2 j < u j

instance (c : C) (u : Fin 6 → Fin 6) : DecidablePred (Alw val c u) :=
  fun _ => by unfold Alw; infer_instance

omit [Fintype β] [Fintype C] in
theorem indicator_covAtM {p : ℕ} (free : Fin 6 → Bool) (c : C) (v : Fin 6 → ℕ) (hv : ∀ j, v j ≤ 4)
    (h3 : ∀ x j, val x j ≤ 4) (E : Fin p → C × β) :
    (if CovAtM val free c v E then (1 : ℤ) else 0) =
      ∑ u : Fin 6 → Fin 6, if Compat free v u then
        sgnU u * ∏ m, (if Alw val c u (E m) then (1 : ℤ) else 0) else 0 := by
  set A : Fin 6 → ℕ → ℤ := fun j t => ∏ m, (if ((E m).1 = c → val (E m).2 j < t) then (1 : ℤ) else 0) with hA
  have h1 : (if CovAtM val free c v E then (1 : ℤ) else 0) =
      ∏ j, (if free j = false then 1 - A j (v j) else 1) := by
    by_cases hc : CovAtM val free c v E
    · rw [if_pos hc]
      symm
      refine prod_eq_one fun j _ => ?_
      split_ifs with hf
      · obtain ⟨m, hm1, hm2⟩ := hc j hf
        simp only [hA]
        rw [prod_eq_zero (mem_univ m) (if_neg (fun h => Nat.not_lt.mpr hm2 (h hm1))), sub_zero]
      · rfl
    · rw [if_neg hc]
      have : ∃ j, free j = false ∧ ∀ m, (E m).1 = c → val (E m).2 j < v j := by
        by_contra hn
        push Not at hn
        exact hc fun j hj => by
          obtain ⟨m, hm1, hm2⟩ := hn j hj
          exact ⟨m, hm1, hm2⟩
      obtain ⟨j, hj, hlt⟩ := this
      symm
      refine prod_eq_zero (mem_univ j) ?_
      rw [if_pos hj, hA]
      simp only
      rw [prod_eq_one (fun m _ => by rw [if_pos (hlt m)]), sub_self]
  have h2 : ∀ j, (if free j = false then 1 - A j (v j) else 1) =
      ∑ t : Fin 6, (if t = 5 then 1 else if free j = false ∧ (t : ℕ) = v j then -A j t else 0) := by
    intro j
    rw [sum_fin6_single (v j) (hv j) (free j = false) (fun t => -A j t)]
    split_ifs <;> ring
  rw [h1]
  simp_rw [h2]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun u _ => ?_
  by_cases hc : Compat free v u
  · rw [if_pos hc]
    have h4 : ∀ j, (if u j = 5 then (1 : ℤ) else if free j = false ∧ (u j : ℕ) = v j then -A j (u j) else 0) =
        (if u j ≠ 5 then (-1 : ℤ) else 1) * A j (u j) := by
      intro j
      by_cases hu : u j = 5
      · rw [if_pos hu, if_neg (not_not.mpr hu), one_mul, hA]
        symm
        refine prod_eq_one fun m _ => ?_
        rw [if_pos]
        intro _
        rw [hu]
        have := h3 (E m).2 j
        show val (E m).2 j < 5
        omega
      · rw [if_neg hu, if_pos ((hc j).resolve_left hu), if_pos hu]
        ring
    rw [prod_congr rfl fun j _ => h4 j, prod_mul_distrib]
    congr 1
    · rw [sgnU, prod_ite, prod_const_one, mul_one, prod_const]
    · rw [hA]
      simp only
      rw [prod_comm]
      refine prod_congr rfl fun m _ => ?_
      by_cases hall : Alw val c u (E m)
      · rw [if_pos hall]
        exact prod_eq_one fun j _ => by rw [if_pos (fun h => hall h j)]
      · rw [if_neg hall]
        unfold Alw at hall
        push Not at hall
        obtain ⟨hcm, j, hj⟩ := hall
        exact prod_eq_zero (mem_univ j) (by rw [if_neg (fun h => absurd (h hcm) (by omega))])
  · rw [if_neg hc]
    have : ∃ j, u j ≠ 5 ∧ ¬(free j = false ∧ (u j : ℕ) = v j) := by
      by_contra hn
      push Not at hn
      exact hc fun j => by
        by_cases hu : u j = 5
        · exact Or.inl hu
        · exact Or.inr (hn j hu)
    obtain ⟨j, hu, hn⟩ := this
    exact prod_eq_zero (mem_univ j) (by rw [if_neg hu, if_neg hn])

variable {R : Type*} [CommRing R]

theorem sum_prod_ind {p : ℕ} {κ : Type*} [Fintype κ] (coef : κ → R) (S : κ → C × β → Prop)
    [∀ k, DecidablePred (S k)] (wt : Fin p → C × β → R) :
    ∑ E : Fin p → C × β, (∑ k, coef k * ∏ m, (if S k (E m) then (1 : R) else 0)) * ∏ m, wt m (E m) =
      ∑ k, coef k * ∏ m, ∑ x, (if S k x then wt m x else 0) := by
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  simp_rw [mul_assoc, ← mul_sum, ← prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun E _ => prod_congr rfl fun m _ => ?_
  split_ifs <;> simp

omit [Fintype β] [Fintype C] in
theorem indicator_covAtM_R {p : ℕ} (free : Fin 6 → Bool) (c : C) (v : Fin 6 → ℕ) (hv : ∀ j, v j ≤ 4)
    (h3 : ∀ x j, val x j ≤ 4) (E : Fin p → C × β) :
    (if CovAtM val free c v E then (1 : R) else 0) =
      ∑ u : Fin 6 → Fin 6, (if Compat free v u then (sgnU u : R) else 0) *
        ∏ m, (if Alw val c u (E m) then (1 : R) else 0) := by
  have h := congrArg (fun z : ℤ => (z : R)) (indicator_covAtM val free c v hv h3 E)
  simp only [apply_ite (fun z : ℤ => (z : R)), Int.cast_one, Int.cast_zero, Int.cast_sum, Int.cast_mul,
    Int.cast_prod] at h
  rw [h]
  refine sum_congr rfl fun u _ => ?_
  split_ifs <;> simp

theorem weighted_covAtM {p : ℕ} (free : Fin 6 → Bool) (c : C) (v : Fin 6 → ℕ) (hv : ∀ j, v j ≤ 4)
    (h3 : ∀ x j, val x j ≤ 4) (wt : Fin p → C × β → R) :
    ∑ E : Fin p → C × β, (if CovAtM val free c v E then ∏ m, wt m (E m) else 0) =
      ∑ u : Fin 6 → Fin 6, (if Compat free v u then (sgnU u : R) else 0) *
        ∏ m, ∑ x, (if Alw val c u x then wt m x else 0) := by
  have hI : ∀ E : Fin p → C × β, (if CovAtM val free c v E then ∏ m, wt m (E m) else 0) =
      (if CovAtM val free c v E then (1 : R) else 0) * ∏ m, wt m (E m) := by
    intro E; split_ifs <;> simp
  simp_rw [hI, indicator_covAtM_R val free c v hv h3]
  exact sum_prod_ind _ (fun u => Alw val c u) wt

theorem sum_weighted_covAtM {p : ℕ} (free : Fin 6 → Bool) (c : C) (h3 : ∀ x j, val x j ≤ 4)
    (wt : Fin p → C × β → R) :
    ∑ a : β, ∑ E : Fin p → C × β, (if CovAtM val free c (val a) E then ∏ m, wt m (E m) else 0) =
      ∑ u : Fin 6 → Fin 6, (if FreeOk free u then (sgnU u : R) * (M1 val u : R) else 0) *
        ∏ m, ∑ x, (if Alw val c u x then wt m x else 0) := by
  simp_rw [weighted_covAtM val free c _ (fun j => h3 _ j) h3 wt]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [← sum_mul]
  congr 1
  simp_rw [compat_iff]
  by_cases hf : FreeOk free u
  · simp only [hf, true_and, if_true]
    rw [← sum_filter, sum_const, nsmul_eq_mul, M1]
    ring
  · simp [hf]

omit [Fintype β] [Fintype C] in
theorem covAtM_max {p : ℕ} (free : Fin 6 → Bool) (c : C) (v₁ v₂ : Fin 6 → ℕ) (E : Fin p → C × β) :
    CovAtM val free c (fun j => max (v₁ j) (v₂ j)) E ↔ CovAtM val free c v₁ E ∧ CovAtM val free c v₂ E := by
  unfold CovAtM
  constructor
  · intro h
    exact ⟨fun j hj => (h j hj).imp fun m hm => ⟨hm.1, le_trans (le_max_left _ _) hm.2⟩,
      fun j hj => (h j hj).imp fun m hm => ⟨hm.1, le_trans (le_max_right _ _) hm.2⟩⟩
  · rintro ⟨h₁, h₂⟩ j hj
    rcases le_total (v₁ j) (v₂ j) with hle | hle
    · obtain ⟨m, hm1, hm2⟩ := h₂ j hj
      exact ⟨m, hm1, max_le (hle.trans hm2) hm2⟩
    · obtain ⟨m, hm1, hm2⟩ := h₁ j hj
      exact ⟨m, hm1, max_le hm2 (hle.trans hm2)⟩

theorem sum_weighted_covAtM_pair {p : ℕ} (c : C) (h3 : ∀ x j, val x j ≤ 4) (wt : Fin p → C × β → R) :
    ∑ ab : β × β, ∑ E : Fin p → C × β,
        (if CovAtM val (fun _ => false) c (val ab.1) E ∧ CovAtM val (fun _ => false) c (val ab.2) E then
          ∏ m, wt m (E m) else 0) =
      ∑ u : Fin 6 → Fin 6, (sgnU u : R) * (M2 val u : R) * ∏ m, ∑ x, (if Alw val c u x then wt m x else 0) := by
  have hmax : ∀ ab : β × β, ∀ E : Fin p → C × β,
      (if CovAtM val (fun _ => false) c (val ab.1) E ∧ CovAtM val (fun _ => false) c (val ab.2) E then
        ∏ m, wt m (E m) else 0) =
      (if CovAtM val (fun _ => false) c (fun j => max (val ab.1 j) (val ab.2 j)) E then ∏ m, wt m (E m) else 0) := by
    intro ab E
    exact if_congr (covAtM_max val _ c _ _ E).symm rfl rfl
  simp_rw [hmax, weighted_covAtM val (fun _ => false) c _ (fun j => max_le (h3 _ j) (h3 _ j)) h3 wt]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [← sum_mul]
  congr 1
  have hfree : FreeOk (fun _ => false) u := fun j hj => absurd hj (by simp)
  simp_rw [compat_iff, hfree, true_and]
  rw [← sum_filter, sum_const, nsmul_eq_mul, M2]
  ring

theorem sum_weighted_covAtM_two {p : ℕ} (c c' : C) (h3 : ∀ x j, val x j ≤ 4) (wt : Fin p → C × β → R) :
    ∑ ab : β × β, ∑ E : Fin p → C × β,
        (if CovAtM val (fun _ => false) c (val ab.1) E ∧ CovAtM val (fun _ => false) c' (val ab.2) E then
          ∏ m, wt m (E m) else 0) =
      ∑ uu : (Fin 6 → Fin 6) × (Fin 6 → Fin 6),
        ((sgnU uu.1 : R) * (M1 val uu.1 : R)) * ((sgnU uu.2 : R) * (M1 val uu.2 : R)) *
          ∏ m, ∑ x, (if Alw val c uu.1 x ∧ Alw val c' uu.2 x then wt m x else 0) := by
  have hfree : ∀ u : Fin 6 → Fin 6, FreeOk (fun _ => false) u := fun u j hj => absurd hj (by simp)
  have hind : ∀ (ab : β × β) (E : Fin p → C × β),
      (if CovAtM val (fun _ => false) c (val ab.1) E ∧ CovAtM val (fun _ => false) c' (val ab.2) E then
        ∏ m, wt m (E m) else 0) =
      (∑ uu : (Fin 6 → Fin 6) × (Fin 6 → Fin 6),
        ((if Compat (fun _ => false) (val ab.1) uu.1 then (sgnU uu.1 : R) else 0) *
          (if Compat (fun _ => false) (val ab.2) uu.2 then (sgnU uu.2 : R) else 0)) *
        ∏ m, (if Alw val c uu.1 (E m) ∧ Alw val c' uu.2 (E m) then (1 : R) else 0)) * ∏ m, wt m (E m) := by
    intro ab E
    have e1 := indicator_covAtM_R (R := R) val (fun _ => false) c (val ab.1) (fun j => h3 _ j) h3 E
    have e2 := indicator_covAtM_R (R := R) val (fun _ => false) c' (val ab.2) (fun j => h3 _ j) h3 E
    have hsplit : (if CovAtM val (fun _ => false) c (val ab.1) E ∧ CovAtM val (fun _ => false) c' (val ab.2) E then
        ∏ m, wt m (E m) else 0) =
        ((if CovAtM val (fun _ => false) c (val ab.1) E then (1 : R) else 0) *
          (if CovAtM val (fun _ => false) c' (val ab.2) E then (1 : R) else 0)) * ∏ m, wt m (E m) := by
      by_cases h1 : CovAtM val (fun _ => false) c (val ab.1) E <;>
        by_cases h2 : CovAtM val (fun _ => false) c' (val ab.2) E <;> simp [h1, h2]
    rw [hsplit, e1, e2, sum_mul_sum, Fintype.sum_prod_type]
    congr 1
    refine sum_congr rfl fun u1 _ => sum_congr rfl fun u2 _ => ?_
    rw [mul_mul_mul_comm, ← prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun m _ => ?_
    by_cases h1 : Alw val c u1 (E m) <;> by_cases h2 : Alw val c' u2 (E m) <;> simp [h1, h2]
  have hc : ∀ u : Fin 6 → Fin 6, ∑ a : β, (if Compat (fun _ => false) (val a) u then (sgnU u : R) else 0) =
      (sgnU u : R) * (M1 val u : R) := by
    intro u
    simp_rw [compat_iff, hfree, true_and]
    rw [← sum_filter, sum_const, nsmul_eq_mul, M1]
    ring
  rw [sum_congr rfl fun ab _ => sum_congr rfl fun E _ => hind ab E]
  rw [sum_congr rfl fun ab _ => sum_prod_ind
    (fun uu : (Fin 6 → Fin 6) × (Fin 6 → Fin 6) =>
      (if Compat (fun _ => false) (val ab.1) uu.1 then (sgnU uu.1 : R) else 0) *
        (if Compat (fun _ => false) (val ab.2) uu.2 then (sgnU uu.2 : R) else 0))
    (fun (uu : (Fin 6 → Fin 6) × (Fin 6 → Fin 6)) (x : C × β) => Alw val c uu.1 x ∧ Alw val c' uu.2 x) wt]
  rw [sum_comm]
  refine sum_congr rfl fun uu _ => ?_
  rw [← sum_mul]
  refine congrArg (· * _) ?_
  rw [Fintype.sum_prod_type, ← hc uu.1, ← hc uu.2, sum_mul_sum]

end
end ClaudeR3.IE
