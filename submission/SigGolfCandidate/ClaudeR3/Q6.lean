import SigGolfCandidate.ClaudeWCT.Numerics.CoverW1

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
