import SigGolfCandidate.Merge024
import SigGolfCandidate.Merge031

-- ==== merged from ClaudeWCT_Numerics_Covariance ====
section

section
namespace ClaudeWCT.Numerics.Thinning
open Finset ClaudeWCT.Numerics
def tmom (d : List (ℕ × ℤ)) (X : ℤ) (r : ℕ) : ℤ := (d.map fun e => e.2 * (X + e.1) ^ r).sum
def tmom2 (d : List (ℕ × ℤ)) (X : ℤ) (r : ℕ) : ℤ := (d.map fun e => e.2 * tmom d (X + e.1) r).sum
theorem tmom_zero (d : List (ℕ × ℤ)) (r : ℕ) : tmom d 0 r = (d.map fun e => e.2 * (e.1 : ℤ) ^ r).sum := by
  simp [tmom]
theorem tmom_expand (d : List (ℕ × ℤ)) (X : ℤ) (r : ℕ) :
    tmom d X r = ∑ p ∈ range (r + 1), tmom d 0 p * (X ^ (r - p) * (r.choose p : ℤ)) := by
  induction d with
  | nil => simp [tmom]
  | cons e d ih =>
    simp only [tmom, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, add_comm X, add_pow, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    ring
theorem sum_list_swap {ι : Type*} (s : Finset ι) (d : List (ℕ × ℤ)) (F : ℕ × ℤ → ι → ℤ) :
    ∑ a ∈ s, (d.map fun e => F e a).sum = (d.map fun e => ∑ a ∈ s, F e a).sum := by
  induction d with
  | nil => simp
  | cons e d ih => simp only [List.map_cons, List.sum_cons, sum_add_distrib, ih]
theorem transfer {ι : Type*} (s : Finset ι) (σ V : ι → ℤ) (d : List (ℕ × ℤ))
    (h : ∀ p, ∑ a ∈ s, σ a * V a ^ p = tmom d 0 p) (X : ℤ) (r : ℕ) :
    ∑ a ∈ s, σ a * (X + V a) ^ r = tmom d X r := by
  rw [tmom_expand]
  simp_rw [← h, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [add_comm X, add_pow, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  ring
section Thin
variable {c : ℕ} {β : Type*} [Fintype β] {C : Type*} [Fintype C] [DecidableEq C]
def CovAt {p : ℕ} (val : β → Fin c → ℕ) (j : C) (v : Fin c → ℕ) (E : Fin p → C × β) : Prop :=
  ∀ i, ∃ m, (E m).1 = j ∧ v i ≤ val (E m).2 i
instance {p : ℕ} (val : β → Fin c → ℕ) (j : C) (v : Fin c → ℕ) :
    DecidablePred (CovAt (p := p) val j v) :=
  fun _ => Fintype.decidableForallFintype
def shiftv (val : β → Fin c → ℕ) (j : C) (x : C × β) (i : Fin c) : ℕ :=
  if x.1 = j then val x.2 i + 1 else 0
omit [Fintype β] [Fintype C] in
theorem covAt_iff {p : ℕ} (val : β → Fin c → ℕ) (j : C) (v : Fin c → ℕ) (E : Fin p → C × β) :
    CovAt val j v E ↔ CoversT (shiftv val j) (fun i => v i + 1) E := by
  unfold CovAt CoversT shiftv
  refine forall_congr' fun i => exists_congr fun m => ?_
  split_ifs with h
  · simp [h]
  · simp [h]
omit [Fintype β] [Fintype C] in
theorem violates_shift (val : β → Fin c → ℕ) (j : C) (v : Fin c → ℕ) (s : Fin c → Bool) (x : C × β) :
    Violates (shiftv val j) (fun i => v i + 1) s x ↔ (x.1 = j → Violates val v s x.2) := by
  unfold Violates shiftv
  by_cases h : x.1 = j
  · simp only [h, if_true, true_imp_iff]
    exact forall_congr' fun i => imp_congr_right fun _ => by omega
  · simp only [h, if_false, false_imp_iff, iff_true]
    intro i _
    omega
theorem card_violates_shift (val : β → Fin c → ℕ) (j : C) (v : Fin c → ℕ) (s : Fin c → Bool) :
    #{x : C × β | Violates (shiftv val j) (fun i => v i + 1) s x} =
      (Fintype.card C - 1) * Fintype.card β + #{b : β | Violates val v s b} := by
  rw [card_filter, Fintype.sum_prod_type]
  simp_rw [violates_shift]
  rw [← add_sum_erase _ _ (mem_univ j)]
  have hoff : ∀ a ∈ univ.erase j,
      (∑ b : β, if (a = j → Violates val v s b) then 1 else 0) = Fintype.card β := by
    intro a ha
    have hne : a ≠ j := ne_of_mem_erase ha
    simp [hne]
  rw [sum_congr rfl hoff, sum_const, card_erase_of_mem (mem_univ j), card_univ, smul_eq_mul,
    card_filter]
  simp only [true_imp_iff]
  ring
theorem card_violates_shift_pair (val : β → Fin c → ℕ) (j₁ j₂ : C) (hne : j₁ ≠ j₂)
    (v₁ v₂ : Fin c → ℕ) (s₁ s₂ : Fin c → Bool) :
    #{x : C × β | Violates (shiftv val j₁) (fun i => v₁ i + 1) s₁ x ∧
        Violates (shiftv val j₂) (fun i => v₂ i + 1) s₂ x} =
      (Fintype.card C - 2) * Fintype.card β + #{b : β | Violates val v₁ s₁ b} +
        #{b : β | Violates val v₂ s₂ b} := by
  rw [card_filter, Fintype.sum_prod_type]
  simp_rw [violates_shift]
  have hj₂ : j₂ ∈ univ.erase j₁ := mem_erase.mpr ⟨hne.symm, mem_univ _⟩
  rw [← add_sum_erase _ _ (mem_univ j₁), ← add_sum_erase _ _ hj₂]
  have hoff : ∀ a ∈ (univ.erase j₁).erase j₂,
      (∑ b : β, if ((a = j₁ → Violates val v₁ s₁ b) ∧ (a = j₂ → Violates val v₂ s₂ b)) then 1 else 0) =
        Fintype.card β := by
    intro a ha
    have h₂ : a ≠ j₂ := ne_of_mem_erase ha
    have h₁ : a ≠ j₁ := ne_of_mem_erase (mem_of_mem_erase ha)
    simp [h₁, h₂]
  rw [sum_congr rfl hoff, sum_const, card_erase_of_mem hj₂, card_erase_of_mem (mem_univ j₁), card_univ,
    smul_eq_mul, card_filter, card_filter]
  simp only [true_imp_iff, hne, hne.symm, and_true, true_and, IsEmpty.forall_iff]
  rw [Nat.sub_sub]
  ring
omit [Fintype β] [Fintype C] in
theorem indicator_covAt {p : ℕ} (val : β → Fin c → ℕ) (j : C) (v : Fin c → ℕ) (E : Fin p → C × β) :
    (if CovAt val j v E then (1 : ℤ) else 0) =
      ∑ s : Fin c → Bool, (-1) ^ #{i | s i = true} *
        ∏ m, (if Violates (shiftv val j) (fun i => v i + 1) s (E m) then (1 : ℤ) else 0) := by
  rw [← indicator_covers]
  exact if_congr (covAt_iff val j v E) rfl rfl
theorem card_covAt (val : β → Fin c → ℕ) (j : C) (v : Fin c → ℕ) (r : ℕ) :
    (#{E : Fin r → C × β | CovAt val j v E} : ℤ) =
      ∑ s : Fin c → Bool, (-1) ^ #{i | s i = true} *
        ((((Fintype.card C - 1) * Fintype.card β : ℕ) : ℤ) + #{b : β | Violates val v s b}) ^ r := by
  rw [filter_congr (fun E _ => covAt_iff val j v E), card_covered_eq]
  simp_rw [card_violates_shift]
  push_cast
  rfl
theorem card_covAt_pair (val : β → Fin c → ℕ) (j₁ j₂ : C) (hne : j₁ ≠ j₂) (v₁ v₂ : Fin c → ℕ)
    (r : ℕ) :
    (#{E : Fin r → C × β | CovAt val j₁ v₁ E ∧ CovAt val j₂ v₂ E} : ℤ) =
      ∑ s₁ : Fin c → Bool, ∑ s₂ : Fin c → Bool,
        ((-1) ^ #{i | s₁ i = true} * (-1) ^ #{i | s₂ i = true}) *
          ((((Fintype.card C - 2) * Fintype.card β : ℕ) : ℤ) + (#{b : β | Violates val v₁ s₁ b} : ℤ) +
            #{b : β | Violates val v₂ s₂ b}) ^ r := by
  set g₁ : (Fin c → Bool) → C × β → ℤ := fun s x =>
    if Violates (shiftv val j₁) (fun i => v₁ i + 1) s x then 1 else 0 with hg₁
  set g₂ : (Fin c → Bool) → C × β → ℤ := fun s x =>
    if Violates (shiftv val j₂) (fun i => v₂ i + 1) s x then 1 else 0 with hg₂
  have hind : ∀ E : Fin r → C × β, (if CovAt val j₁ v₁ E ∧ CovAt val j₂ v₂ E then (1 : ℤ) else 0) =
      ∑ s₁ : Fin c → Bool, ∑ s₂ : Fin c → Bool,
        ((-1) ^ #{i | s₁ i = true} * (-1) ^ #{i | s₂ i = true}) * ∏ m, (g₁ s₁ (E m) * g₂ s₂ (E m)) := by
    intro E
    rw [← mul_one (1 : ℤ), ← ite_zero_mul_ite_zero, indicator_covAt, indicator_covAt, sum_mul_sum]
    refine sum_congr rfl fun s₁ _ => sum_congr rfl fun s₂ _ => ?_
    rw [prod_mul_distrib]
    ring
  rw [natCast_card_filter]
  simp_rw [hind]
  rw [sum_comm]
  refine sum_congr rfl fun s₁ _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun s₂ _ => ?_
  rw [← mul_sum, (Fintype.sum_pow (fun x => g₁ s₁ x * g₂ s₂ x) r).symm]
  congr 2
  have hcnt : ∑ x, g₁ s₁ x * g₂ s₂ x =
      (#{x : C × β | Violates (shiftv val j₁) (fun i => v₁ i + 1) s₁ x ∧
        Violates (shiftv val j₂) (fun i => v₂ i + 1) s₂ x} : ℤ) := by
    rw [natCast_card_filter]
    refine sum_congr rfl fun x _ => ?_
    simp only [hg₁, hg₂, ite_zero_mul_ite_zero, mul_one]
  rw [hcnt, card_violates_shift_pair val j₁ j₂ hne]
  push_cast
  ring
theorem cover_ie {τ : Type*} [Fintype τ] (tv : τ → Fin c → ℕ) (val : β → Fin c → ℕ) (p : ℕ) :
    (#{x : τ × (Fin p → β) | CoversT val (tv x.1) x.2} : ℤ) =
      ∑ y : τ × (Fin c → Bool), (-1) ^ #{i | y.2 i = true} *
        ((#{b : β | Violates val (tv y.1) y.2 b} : ℕ) : ℤ) ^ p := by
  rw [natCast_card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  dsimp only
  rw [← natCast_card_filter, card_covered_eq]
theorem thin_ie {τ : Type*} [Fintype τ] (tv : τ → Fin c → ℕ) (val : β → Fin c → ℕ) (j : C) (r : ℕ) :
    (#{x : τ × (Fin r → C × β) | CovAt val j (tv x.1) x.2} : ℤ) =
      ∑ y : τ × (Fin c → Bool), (-1) ^ #{i | y.2 i = true} *
        ((((Fintype.card C - 1) * Fintype.card β : ℕ) : ℤ) +
          ((#{b : β | Violates val (tv y.1) y.2 b} : ℕ) : ℤ)) ^ r := by
  rw [natCast_card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  dsimp only
  rw [← natCast_card_filter, card_covAt]
theorem thin_count {τ : Type*} [Fintype τ] (tv : τ → Fin c → ℕ) (val : β → Fin c → ℕ)
    (d : List (ℕ × ℤ)) (h : ∀ p, (#{x : τ × (Fin p → β) | CoversT val (tv x.1) x.2} : ℤ) = tmom d 0 p)
    (j : C) (r : ℕ) :
    (#{x : τ × (Fin r → C × β) | CovAt val j (tv x.1) x.2} : ℤ) =
      tmom d (((Fintype.card C - 1) * Fintype.card β : ℕ) : ℤ) r := by
  rw [thin_ie]
  refine transfer univ _ _ d (fun p => ?_) _ r
  rw [← h p, cover_ie]
theorem thin_count_pair {τ : Type*} [Fintype τ] (tv : τ → Fin c → ℕ) (val : β → Fin c → ℕ)
    (d : List (ℕ × ℤ)) (h : ∀ p, (#{x : τ × (Fin p → β) | CoversT val (tv x.1) x.2} : ℤ) = tmom d 0 p)
    (j₁ j₂ : C) (hne : j₁ ≠ j₂) (r : ℕ) :
    (#{x : (τ × τ) × (Fin r → C × β) | CovAt val j₁ (tv x.1.1) x.2 ∧ CovAt val j₂ (tv x.1.2) x.2} : ℤ) =
      tmom2 d (((Fintype.card C - 2) * Fintype.card β : ℕ) : ℤ) r := by
  have hm : ∀ p, ∑ y : τ × (Fin c → Bool), (-1) ^ #{i | y.2 i = true} *
      ((#{b : β | Violates val (tv y.1) y.2 b} : ℕ) : ℤ) ^ p = tmom d 0 p := fun p => by
    rw [← h p, cover_ie]
  set B : ℤ := (((Fintype.card C - 2) * Fintype.card β : ℕ) : ℤ)
  set V : τ × (Fin c → Bool) → ℤ := fun y => ((#{b : β | Violates val (tv y.1) y.2 b} : ℕ) : ℤ)
  set σ : τ × (Fin c → Bool) → ℤ := fun y => (-1) ^ #{i | y.2 i = true}
  have hm' : ∀ p, ∑ y, σ y * V y ^ p = tmom d 0 p := hm
  calc (#{x : (τ × τ) × (Fin r → C × β) | CovAt val j₁ (tv x.1.1) x.2 ∧ CovAt val j₂ (tv x.1.2) x.2} : ℤ)
      = ∑ a₁ : τ, ∑ a₂ : τ, ∑ s₁ : Fin c → Bool, ∑ s₂ : Fin c → Bool,
          σ (a₁, s₁) * σ (a₂, s₂) * (B + V (a₁, s₁) + V (a₂, s₂)) ^ r := by
        rw [natCast_card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
        refine sum_congr rfl fun a₁ _ => sum_congr rfl fun a₂ _ => ?_
        dsimp only
        rw [← natCast_card_filter]
        exact card_covAt_pair val j₁ j₂ hne _ _ r
    _ = ∑ a₁ : τ, ∑ s₁ : Fin c → Bool, ∑ a₂ : τ, ∑ s₂ : Fin c → Bool,
          σ (a₁, s₁) * σ (a₂, s₂) * (B + V (a₁, s₁) + V (a₂, s₂)) ^ r := by
        refine sum_congr rfl fun a₁ _ => ?_
        exact sum_comm
    _ = ∑ y₁, ∑ y₂, σ y₁ * σ y₂ * (B + V y₁ + V y₂) ^ r := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
    _ = ∑ y₂, σ y₂ * ∑ y₁, σ y₁ * ((B + V y₂) + V y₁) ^ r := by
        rw [sum_comm]
        simp_rw [mul_sum]
        refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => ?_
        ring
    _ = ∑ y₂, σ y₂ * tmom d (B + V y₂) r := by
        refine sum_congr rfl fun y₂ _ => ?_
        rw [transfer univ σ V d hm' (B + V y₂) r]
    _ = (d.map fun e => e.2 * ∑ y₂, σ y₂ * ((B + e.1) + V y₂) ^ r).sum := by
        simp only [tmom]
        simp_rw [← List.sum_map_mul_left]
        rw [sum_list_swap]
        congr 1
        refine List.map_congr_left fun e _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun y₂ _ => ?_
        ring
    _ = tmom2 d B r := by
        unfold tmom2
        congr 1
        refine List.map_congr_left fun e _ => ?_
        rw [transfer univ σ V d hm' (B + e.1) r]
omit [Fintype β] [Fintype C] [DecidableEq C] in
theorem coversT_max {p : ℕ} (val : β → Fin c → ℕ) (v₁ v₂ : Fin c → ℕ) (E : Fin p → β) :
    CoversT val (fun i => max (v₁ i) (v₂ i)) E ↔ CoversT val v₁ E ∧ CoversT val v₂ E := by
  unfold CoversT
  constructor
  · intro h
    exact ⟨fun i => (h i).imp fun m hm => le_trans (le_max_left _ _) hm,
      fun i => (h i).imp fun m hm => le_trans (le_max_right _ _) hm⟩
  · rintro ⟨h₁, h₂⟩ i
    rcases le_total (v₁ i) (v₂ i) with hle | hle
    · obtain ⟨m, hm⟩ := h₂ i
      exact ⟨m, max_le (hle.trans hm) hm⟩
    · obtain ⟨m, hm⟩ := h₁ i
      exact ⟨m, max_le hm (hle.trans hm)⟩
omit [Fintype β] [Fintype C] in
theorem covAt_max {p : ℕ} (val : β → Fin c → ℕ) (j : C) (v₁ v₂ : Fin c → ℕ) (E : Fin p → C × β) :
    CovAt val j (fun i => max (v₁ i) (v₂ i)) E ↔ CovAt val j v₁ E ∧ CovAt val j v₂ E := by
  rw [covAt_iff, covAt_iff, covAt_iff]
  have h : (fun i => max (v₁ i) (v₂ i) + 1) = fun i => max (v₁ i + 1) (v₂ i + 1) := by
    funext i; exact (Nat.add_max_add_right _ _ _).symm
  rw [h, coversT_max]
theorem thin_count_same (val : β → Fin c → ℕ) (d₂ : List (ℕ × ℤ))
    (h₂ : ∀ p, (#{x : β × β × (Fin p → β) | CoversT val (val x.1) x.2.2 ∧ CoversT val (val x.2.1) x.2.2} : ℤ) =
      tmom d₂ 0 p) (j : C) (r : ℕ) :
    (#{x : (β × β) × (Fin r → C × β) | CovAt val j (val x.1.1) x.2 ∧ CovAt val j (val x.1.2) x.2} : ℤ) =
      tmom d₂ (((Fintype.card C - 1) * Fintype.card β : ℕ) : ℤ) r := by
  have hh : ∀ p, (#{x : (β × β) × (Fin p → β) |
      CoversT val ((fun a : β × β => fun i => max (val a.1 i) (val a.2 i)) x.1) x.2} : ℤ) = tmom d₂ 0 p := by
    intro p
    rw [← h₂ p]
    congr 1
    refine card_equiv (Equiv.prodAssoc β β (Fin p → β)) fun x => ?_
    simp only [mem_filter, mem_univ, true_and, Equiv.prodAssoc_apply]
    exact coversT_max val _ _ _
  rw [← thin_count (fun a : β × β => fun i => max (val a.1 i) (val a.2 i)) val d₂ hh j r]
  congr 2
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact (covAt_max val j _ _ _).symm
theorem coord_first (val : β → Fin c → ℕ) (d₁ : List (ℕ × ℤ))
    (h₁ : ∀ p, (#{x : β × (Fin p → β) | CoversT val (val x.1) x.2} : ℤ) = tmom d₁ 0 p) (r : ℕ) :
    (#{x : (C × β) × (Fin r → C × β) | CovAt val x.1.1 (val x.1.2) x.2} : ℤ) =
      Fintype.card C * tmom d₁ (((Fintype.card C - 1) * Fintype.card β : ℕ) : ℤ) r := by
  rw [natCast_card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hj : ∀ j : C, (∑ u : β, ∑ E : Fin r → C × β,
      if CovAt val ((j, u), E).1.1 (val ((j, u), E).1.2) ((j, u), E).2 then (1 : ℤ) else 0) =
      tmom d₁ (((Fintype.card C - 1) * Fintype.card β : ℕ) : ℤ) r := by
    intro j
    rw [← thin_count val val d₁ h₁ j r, natCast_card_filter, Fintype.sum_prod_type]
  rw [sum_congr rfl fun j _ => hj j, sum_const, card_univ, nsmul_eq_mul]
theorem coord_second (val : β → Fin c → ℕ) (d₁ d₂ : List (ℕ × ℤ))
    (h₁ : ∀ p, (#{x : β × (Fin p → β) | CoversT val (val x.1) x.2} : ℤ) = tmom d₁ 0 p)
    (h₂ : ∀ p, (#{x : β × β × (Fin p → β) | CoversT val (val x.1) x.2.2 ∧ CoversT val (val x.2.1) x.2.2} : ℤ) =
      tmom d₂ 0 p) (r : ℕ) :
    (#{x : ((C × β) × (C × β)) × (Fin r → C × β) |
        CovAt val x.1.1.1 (val x.1.1.2) x.2 ∧ CovAt val x.1.2.1 (val x.1.2.2) x.2} : ℤ) =
      Fintype.card C * tmom d₂ (((Fintype.card C - 1) * Fintype.card β : ℕ) : ℤ) r +
        Fintype.card C * (Fintype.card C - 1 : ℕ) *
          tmom2 d₁ (((Fintype.card C - 2) * Fintype.card β : ℕ) : ℤ) r := by
  set F : C → C → ℤ := fun j₁ j₂ =>
    (#{x : (β × β) × (Fin r → C × β) | CovAt val j₁ (val x.1.1) x.2 ∧ CovAt val j₂ (val x.1.2) x.2} : ℤ)
    with hF
  have hsplit : (#{x : ((C × β) × (C × β)) × (Fin r → C × β) |
      CovAt val x.1.1.1 (val x.1.1.2) x.2 ∧ CovAt val x.1.2.1 (val x.1.2.2) x.2} : ℤ) =
      ∑ j₁, ∑ j₂, F j₁ j₂ := by
    rw [natCast_card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun j₁ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun j₂ _ => ?_
    simp only [hF]
    rw [natCast_card_filter, Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
  rw [hsplit]
  have hrow : ∀ j₁ : C, ∑ j₂, F j₁ j₂ =
      tmom d₂ (((Fintype.card C - 1) * Fintype.card β : ℕ) : ℤ) r +
        (Fintype.card C - 1 : ℕ) * tmom2 d₁ (((Fintype.card C - 2) * Fintype.card β : ℕ) : ℤ) r := by
    intro j₁
    rw [← add_sum_erase _ _ (mem_univ j₁)]
    have hoff : ∀ j₂ ∈ univ.erase j₁, F j₁ j₂ =
        tmom2 d₁ (((Fintype.card C - 2) * Fintype.card β : ℕ) : ℤ) r := by
      intro j₂ hj₂
      exact thin_count_pair val val d₁ h₁ j₁ j₂ (ne_of_mem_erase hj₂).symm r
    rw [sum_congr rfl hoff, sum_const, card_erase_of_mem (mem_univ j₁), card_univ, nsmul_eq_mul]
    simp only [hF]
    rw [thin_count_same val d₂ h₂ j₁ r]
  rw [sum_congr rfl fun j₁ _ => hrow j₁, sum_const, card_univ, nsmul_eq_mul]
  ring
end Thin
section Product
variable {c n : ℕ} {β : Type*} [Fintype β] {C : Type*} [Fintype C] [DecidableEq C]
theorem card_pi_forall {X : Type*} [Fintype X] (P : Fin n → X → Prop)
    [∀ k, DecidablePred (P k)] :
    #{f : Fin n → X | ∀ k, P k (f k)} = ∏ k, #{x : X | P k x} := by
  have h : ({f : Fin n → X | ∀ k, P k (f k)} : Finset (Fin n → X)) =
      Fintype.piFinset (fun k => ({x : X | P k x} : Finset X)) := by
    ext f
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]
def FullCov {r : ℕ} (val : β → Fin c → ℕ) (t : Fin n → C × β) (E : Fin r → Fin n → C × β) : Prop :=
  ∀ k, CovAt val (t k).1 (val (t k).2) (fun m => E m k)
instance {r : ℕ} (val : β → Fin c → ℕ) (t : Fin n → C × β) :
    DecidablePred (FullCov (r := r) val t) :=
  fun _ => Fintype.decidableForallFintype
def coordEquiv (T : Type*) (r : ℕ) (Y : Type*) :
    (Fin n → T × (Fin r → Y)) ≃ (Fin n → T) × (Fin r → Fin n → Y) where
  toFun f := (fun k => (f k).1, fun m k => (f k).2 m)
  invFun x := fun k => (x.1 k, fun m => x.2 m k)
  left_inv _ := rfl
  right_inv _ := rfl
theorem card_full_first (val : β → Fin c → ℕ) (r : ℕ) :
    #{x : (Fin n → C × β) × (Fin r → Fin n → C × β) | FullCov val x.1 x.2} =
      #{y : (C × β) × (Fin r → C × β) | CovAt val y.1.1 (val y.1.2) y.2} ^ n := by
  have h1 : #{x : (Fin n → C × β) × (Fin r → Fin n → C × β) | FullCov val x.1 x.2} =
      #{f : Fin n → (C × β) × (Fin r → C × β) | ∀ k, CovAt val (f k).1.1 (val (f k).1.2) (f k).2} := by
    symm
    refine card_equiv (coordEquiv (C × β) r (C × β)) fun f => ?_
    simp only [mem_filter, mem_univ, true_and]
    rfl
  rw [h1, card_pi_forall (fun (_ : Fin n) (y : (C × β) × (Fin r → C × β)) => CovAt val y.1.1 (val y.1.2) y.2),
    prod_const, card_univ, Fintype.card_fin]
def FullCov2 {r : ℕ} (val : β → Fin c → ℕ) (t : (Fin n → C × β) × (Fin n → C × β))
    (E : Fin r → Fin n → C × β) : Prop :=
  FullCov val t.1 E ∧ FullCov val t.2 E
instance {r : ℕ} (val : β → Fin c → ℕ) (t : (Fin n → C × β) × (Fin n → C × β)) :
    DecidablePred (FullCov2 (r := r) val t) :=
  fun _ => instDecidableAnd
def pairEquiv (T : Type*) : (Fin n → T × T) ≃ (Fin n → T) × (Fin n → T) where
  toFun f := (fun k => (f k).1, fun k => (f k).2)
  invFun x := fun k => (x.1 k, x.2 k)
  left_inv _ := rfl
  right_inv _ := rfl
theorem card_full_second (val : β → Fin c → ℕ) (r : ℕ) :
    #{x : ((Fin n → C × β) × (Fin n → C × β)) × (Fin r → Fin n → C × β) | FullCov2 val x.1 x.2} =
      #{y : ((C × β) × (C × β)) × (Fin r → C × β) |
        CovAt val y.1.1.1 (val y.1.1.2) y.2 ∧ CovAt val y.1.2.1 (val y.1.2.2) y.2} ^ n := by
  let e : (Fin n → ((C × β) × (C × β)) × (Fin r → C × β)) ≃
      ((Fin n → C × β) × (Fin n → C × β)) × (Fin r → Fin n → C × β) :=
    (coordEquiv ((C × β) × (C × β)) r (C × β)).trans
      (Equiv.prodCongr (pairEquiv (C × β)) (Equiv.refl _))
  have h1 : #{x : ((Fin n → C × β) × (Fin n → C × β)) × (Fin r → Fin n → C × β) | FullCov2 val x.1 x.2} =
      #{f : Fin n → ((C × β) × (C × β)) × (Fin r → C × β) |
        ∀ k, CovAt val (f k).1.1.1 (val (f k).1.1.2) (f k).2 ∧ CovAt val (f k).1.2.1 (val (f k).1.2.2) (f k).2} := by
    symm
    refine card_equiv e fun f => ?_
    simp only [mem_filter, mem_univ, true_and, forall_and]
    rfl
  rw [h1, card_pi_forall (fun (_ : Fin n) (y : ((C × β) × (C × β)) × (Fin r → C × β)) =>
      CovAt val y.1.1.1 (val y.1.1.2) y.2 ∧ CovAt val y.1.2.1 (val y.1.2.2) y.2),
    prod_const, card_univ, Fintype.card_fin]
end Product
section KernelForms
open ClaudeWCT.Numerics.Kernel
theorem wpos_sub_wneg (d : List (ℕ × ℤ)) (base r : ℕ) :
    (wpos d base r : ℤ) - wneg d base r = tmom d base r := by
  induction d with
  | nil => simp [wpos, wneg, tmom]
  | cons e d ih =>
    simp only [wpos, wneg, tmom, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
    push_cast
    rw [← ih]
    have he := Int.toNat_sub_toNat_neg e.2
    linear_combination ((base : ℤ) + e.1) ^ r * he
theorem wwpos_sub_wwneg_aux (l d : List (ℕ × ℤ)) (base r : ℕ) :
    ((l.foldr (fun e s => e.2.toNat * wpos d (base + e.1) r + (-e.2).toNat * wneg d (base + e.1) r + s) 0 : ℕ) : ℤ) -
      ((l.foldr (fun e s => e.2.toNat * wneg d (base + e.1) r + (-e.2).toNat * wpos d (base + e.1) r + s) 0 : ℕ) : ℤ) =
      (l.map fun e => e.2 * tmom d ((base : ℤ) + e.1) r).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
    push_cast at ih ⊢
    rw [← ih]
    have he := Int.toNat_sub_toNat_neg e.2
    have hw := wpos_sub_wneg d (base + e.1) r
    push_cast at hw
    linear_combination ((wpos d (base + e.1) r : ℤ) - wneg d (base + e.1) r) * he + e.2 * hw
theorem wwpos_sub_wwneg (d : List (ℕ × ℤ)) (base r : ℕ) :
    (wwpos d base r : ℤ) - wwneg d base r = tmom2 d base r :=
  wwpos_sub_wwneg_aux d d base r
theorem xNum_cast (r : ℕ) (h : 0 ≤ tmom w1Data B1 r) : (xNum r : ℤ) = tmom w1Data B1 r := by
  have hw := wpos_sub_wneg w1Data B1 r
  unfold xNum
  omega
theorem yNum_cast (r : ℕ) (h : 0 ≤ tmom w2Data B1 r + (Kc - 1 : ℕ) * tmom2 w1Data B2 r) :
    (yNum r : ℤ) = tmom w2Data B1 r + (Kc - 1 : ℕ) * tmom2 w1Data B2 r := by
  have hw := wpos_sub_wneg w2Data B1 r
  have hww := wwpos_sub_wwneg w1Data B2 r
  have hk : Kc - 1 = 127 := rfl
  unfold yNum yPos yNeg
  rw [hk] at h ⊢
  push_cast at h ⊢
  omega
end KernelForms
section Prob
open SphincsSecurity.Concrete (uniformWordAverage)
open SigGolfResearch.Gate6.Moments (finiteAverage word_array_average)
variable {c n : ℕ} {β : Type} [Fintype β] {C : Type} [Fintype C] [DecidableEq C]
def ListCov (val : β → Fin c → ℕ) (L : List (Fin n → C × β)) (t : Fin n → C × β) : Prop :=
  ∀ k i, ∃ e ∈ L, (e k).1 = (t k).1 ∧ val (t k).2 i ≤ val (e k).2 i
instance (val : β → Fin c → ℕ) (L : List (Fin n → C × β)) : DecidablePred (ListCov val L) := by
  unfold ListCov
  infer_instance
noncomputable def env (val : β → Fin c → ℕ) (L : List (Fin n → C × β)) : ENNReal :=
  finiteAverage (fun t : Fin n → C × β => if ListCov val L t then 1 else 0)
omit [Fintype β] [Fintype C] [DecidableEq C] in
theorem listCov_ofFn {r : ℕ} (val : β → Fin c → ℕ) (E : Fin r → Fin n → C × β) (t : Fin n → C × β) :
    ListCov val (List.ofFn E) t ↔ FullCov val t E := by
  simp only [ListCov, FullCov, CovAt, List.mem_ofFn]
  refine forall_congr' fun k => forall_congr' fun i => ?_
  constructor
  · rintro ⟨e, ⟨m, rfl⟩, h⟩
    exact ⟨m, h⟩
  · rintro ⟨m, h⟩
    exact ⟨E m, ⟨m, rfl⟩, h⟩
omit [Fintype β] [Fintype C] [DecidableEq C] in
theorem listCov_cons (val : β → Fin c → ℕ) (a : Fin n → C × β) (L : List (Fin n → C × β))
    (t : Fin n → C × β) (h : ListCov val L t) : ListCov val (a :: L) t := by
  intro k i
  obtain ⟨e, he, h'⟩ := h k i
  exact ⟨e, List.mem_cons_of_mem a he, h'⟩
theorem env_cons_le (val : β → Fin c → ℕ) (a : Fin n → C × β) (L : List (Fin n → C × β)) :
    env val L ≤ env val (a :: L) := by
  unfold env finiteAverage
  refine ENNReal.div_le_div_right (sum_le_sum fun t _ => ?_) _
  split_ifs with h₁ h₂
  · exact le_rfl
  · exact absurd (listCov_cons val a L t h₁) h₂
  · exact zero_le_one
  · exact le_rfl
theorem env_le_one (val : β → Fin c → ℕ) (L : List (Fin n → C × β)) : env val L ≤ 1 := by
  unfold env finiteAverage
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  calc ∑ t : Fin n → C × β, (if ListCov val L t then (1 : ENNReal) else 0)
      ≤ ∑ _t : Fin n → C × β, (1 : ENNReal) := sum_le_sum fun t _ => by split_ifs <;> simp
    _ = Fintype.card (Fin n → C × β) := by simp
theorem env_ne_top (val : β → Fin c → ℕ) (L : List (Fin n → C × β)) : env val L ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (env_le_one val L)
theorem avg_avg_ind {T A : Type} [Fintype T] [Fintype A] (P : T → A → Prop) [∀ t, DecidablePred (P t)] :
    finiteAverage (fun a : A => finiteAverage (fun t : T => if P t a then (1 : ENNReal) else 0)) =
      (#{x : T × A | P x.1 x.2} : ENNReal) / ((Fintype.card T : ENNReal) * Fintype.card A) := by
  unfold finiteAverage
  simp only [div_eq_mul_inv]
  rw [← sum_mul, mul_assoc,
    ← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  congr 1
  rw [natCast_card_filter, Fintype.sum_prod_type, sum_comm]
theorem env_sq (val : β → Fin c → ℕ) (L : List (Fin n → C × β)) :
    env val L ^ 2 = finiteAverage (fun tt : (Fin n → C × β) × (Fin n → C × β) =>
      if ListCov val L tt.1 ∧ ListCov val L tt.2 then 1 else 0) := by
  unfold env finiteAverage
  simp only [div_eq_mul_inv]
  rw [mul_pow, ← ENNReal.inv_pow, sq, sq, sum_mul_sum, Fintype.card_prod, Nat.cast_mul,
    Fintype.sum_prod_type]
  congr 1
  refine sum_congr rfl fun t₁ _ => sum_congr rfl fun t₂ _ => ?_
  rw [ite_zero_mul_ite_zero, mul_one]
variable [SampleableType (Fin n → C × β)]
theorem env_moment_count (val : β → Fin c → ℕ) (r : ℕ) :
    uniformWordAverage r (env (n := n) (C := C) val) =
      ((#{y : (C × β) × (Fin r → C × β) | CovAt val y.1.1 (val y.1.2) y.2} ^ n : ℕ) : ENNReal) /
        ((Fintype.card (Fin n → C × β) : ENNReal) * Fintype.card (Fin r → Fin n → C × β)) := by
  rw [word_array_average]
  unfold env
  rw [avg_avg_ind (fun (t : Fin n → C × β) (E : Fin r → Fin n → C × β) => ListCov val (List.ofFn E) t),
    ← card_full_first (C := C) (β := β) (n := n) val r]
  congr 3
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact listCov_ofFn val x.2 x.1
theorem env_sq_moment_count (val : β → Fin c → ℕ) (r : ℕ) :
    uniformWordAverage r (fun L => env (n := n) (C := C) val L ^ 2) =
      ((#{y : ((C × β) × (C × β)) × (Fin r → C × β) |
          CovAt val y.1.1.1 (val y.1.1.2) y.2 ∧ CovAt val y.1.2.1 (val y.1.2.2) y.2} ^ n : ℕ) : ENNReal) /
        ((Fintype.card ((Fin n → C × β) × (Fin n → C × β)) : ENNReal) *
          Fintype.card (Fin r → Fin n → C × β)) := by
  rw [word_array_average]
  simp_rw [env_sq]
  rw [avg_avg_ind (fun (tt : (Fin n → C × β) × (Fin n → C × β)) (E : Fin r → Fin n → C × β) =>
      ListCov val (List.ofFn E) tt.1 ∧ ListCov val (List.ofFn E) tt.2),
    ← card_full_second (C := C) (β := β) (n := n) val r]
  congr 3
  ext x
  simp only [mem_filter, mem_univ, true_and]
  simp only [FullCov2, listCov_ofFn]
end Prob
section Closed
open ClaudeWCT.Numerics.Kernel
open SphincsSecurity.Concrete (uniformWordAverage)
variable {β : Type} [Fintype β] {C : Type} [Fintype C] [DecidableEq C]
def W1Table (val : β → Fin 7 → ℕ) : Prop :=
  ∀ p, (#{x : β × (Fin p → β) | CoversT val (val x.1) x.2} : ℤ) = (w1Data.map fun e => e.2 * (e.1 : ℤ) ^ p).sum
def W2Table (val : β → Fin 7 → ℕ) : Prop :=
  ∀ p, (#{x : β × β × (Fin p → β) | CoversT val (val x.1) x.2.2 ∧ CoversT val (val x.2.1) x.2.2} : ℤ) =
    (w2Data.map fun e => e.2 * (e.1 : ℤ) ^ p).sum
omit [DecidableEq C] in
theorem B1_eq (hβ : Fintype.card β = 728) (hC : Fintype.card C = 128) :
    (((Fintype.card C - 1) * Fintype.card β : ℕ) : ℤ) = B1 := by
  rw [hβ, hC]; rfl
omit [DecidableEq C] in
theorem B2_eq (hβ : Fintype.card β = 728) (hC : Fintype.card C = 128) :
    (((Fintype.card C - 2) * Fintype.card β : ℕ) : ℤ) = B2 := by
  rw [hβ, hC]; rfl
theorem coord_first_xNum (val : β → Fin 7 → ℕ) (hβ : Fintype.card β = 728) (hC : Fintype.card C = 128)
    (h₁ : W1Table val) (r : ℕ) :
    #{y : (C × β) × (Fin r → C × β) | CovAt val y.1.1 (val y.1.2) y.2} = Kc * xNum r := by
  have hc := coord_first (C := C) val w1Data (fun p => (h₁ p).trans (tmom_zero w1Data p).symm) r
  rw [B1_eq hβ hC, hC] at hc
  have hnn : 0 ≤ tmom w1Data B1 r := by
    have := Int.natCast_nonneg (#{y : (C × β) × (Fin r → C × β) | CovAt val y.1.1 (val y.1.2) y.2})
    push_cast at hc
    omega
  have hx := xNum_cast r hnn
  have hK : Kc = 128 := rfl
  rw [hK]
  push_cast at hc
  omega
theorem coord_second_yNum (val : β → Fin 7 → ℕ) (hβ : Fintype.card β = 728) (hC : Fintype.card C = 128)
    (h₁ : W1Table val) (h₂ : W2Table val) (r : ℕ) :
    #{y : ((C × β) × (C × β)) × (Fin r → C × β) |
      CovAt val y.1.1.1 (val y.1.1.2) y.2 ∧ CovAt val y.1.2.1 (val y.1.2.2) y.2} = Kc * yNum r := by
  have hc := coord_second (C := C) val w1Data w2Data (fun p => (h₁ p).trans (tmom_zero w1Data p).symm)
    (fun p => (h₂ p).trans (tmom_zero w2Data p).symm) r
  rw [B1_eq hβ hC, B2_eq hβ hC, hC] at hc
  have hK1 : ((Kc - 1 : ℕ) : ℤ) = 127 := rfl
  have hnn : 0 ≤ tmom w2Data B1 r + (Kc - 1 : ℕ) * tmom2 w1Data B2 r := by
    have := Int.natCast_nonneg (#{y : ((C × β) × (C × β)) × (Fin r → C × β) |
      CovAt val y.1.1.1 (val y.1.1.2) y.2 ∧ CovAt val y.1.2.1 (val y.1.2.2) y.2})
    rw [hK1]
    push_cast at hc
    omega
  have hy := yNum_cast r hnn
  rw [hK1] at hy
  have hK : Kc = 128 := rfl
  rw [hK]
  push_cast at hc
  omega
omit [DecidableEq C] in
theorem card_table (hβ : Fintype.card β = 728) (hC : Fintype.card C = 128) :
    Fintype.card (Fin 9 → C × β) = Q ^ 9 := by
  simp only [Fintype.card_fun, Fintype.card_prod, hβ, hC, Fintype.card_fin]
  rfl
variable [SampleableType (Fin 9 → C × β)]
theorem env_moment (val : β → Fin 7 → ℕ) (hβ : Fintype.card β = 728) (hC : Fintype.card C = 128)
    (h₁ : W1Table val) (r : ℕ) :
    uniformWordAverage r (env (n := 9) (C := C) val) =
      ((xNum r ^ 9 : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal) := by
  have hE : Fintype.card (Fin r → Fin 9 → C × β) = (Q ^ 9) ^ r := by
    rw [Fintype.card_fun, card_table hβ hC, Fintype.card_fin]
  rw [env_moment_count, coord_first_xNum val hβ hC h₁ r, hE, card_table hβ hC]
  have hnum : (Kc * xNum r) ^ 9 = Kc ^ 9 * xNum r ^ 9 := by ring
  have hden : (Q ^ 9 : ℕ) * (Q ^ 9) ^ r = Kc ^ 9 * (Nn ^ 9 * Q ^ (9 * r)) := by
    rw [← pow_mul, ← mul_assoc, ← mul_pow]
    rfl
  rw [hnum, ← Nat.cast_mul, hden, Nat.cast_mul, Nat.cast_mul (Kc ^ 9)]
  exact ENNReal.mul_div_mul_left _ _ (by simp [Kc]) (by simp)
theorem env_sq_moment (val : β → Fin 7 → ℕ) (hβ : Fintype.card β = 728) (hC : Fintype.card C = 128)
    (h₁ : W1Table val) (h₂ : W2Table val) (r : ℕ) :
    uniformWordAverage r (fun L => env (n := 9) (C := C) val L ^ 2) =
      ((yNum r ^ 9 : ℕ) : ENNReal) / (((Kc * Nn ^ 2) ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal) := by
  have hE : Fintype.card (Fin r → Fin 9 → C × β) = (Q ^ 9) ^ r := by
    rw [Fintype.card_fun, card_table hβ hC, Fintype.card_fin]
  rw [env_sq_moment_count, coord_second_yNum val hβ hC h₁ h₂ r, Fintype.card_prod, hE, card_table hβ hC]
  have hnum : (Kc * yNum r) ^ 9 = Kc ^ 9 * yNum r ^ 9 := by ring
  have hden : (Q ^ 9 * Q ^ 9 : ℕ) * (Q ^ 9) ^ r = Kc ^ 9 * ((Kc * Nn ^ 2) ^ 9 * Q ^ (9 * r)) := by
    rw [← pow_mul, ← mul_assoc, ← mul_pow, ← mul_pow, show Q * Q = Kc * (Kc * Nn ^ 2) from rfl]
  rw [hnum, ← Nat.cast_mul, hden, Nat.cast_mul, Nat.cast_mul (Kc ^ 9)]
  exact ENNReal.mul_div_mul_left _ _ (by simp [Kc]) (by simp)
end Closed
section Near
variable {c n : ℕ} {β : Type} [Fintype β] {C : Type} [Fintype C] [DecidableEq C]
def CovAtExcept {p : ℕ} (val : β → Fin c → ℕ) (i : Fin c) (j : C) (v : Fin c → ℕ) (E : Fin p → C × β) :
    Prop :=
  ∀ i', i' ≠ i → ∃ m, (E m).1 = j ∧ v i' ≤ val (E m).2 i'
instance {p : ℕ} (val : β → Fin c → ℕ) (i : Fin c) (j : C) (v : Fin c → ℕ) :
    DecidablePred (CovAtExcept (p := p) val i j v) :=
  fun _ => Fintype.decidableForallFintype
omit [Fintype β] [Fintype C] [DecidableEq C] in
theorem covAtExcept_iff {p : ℕ} (val : β → Fin (c + 1) → ℕ) (i : Fin (c + 1)) (j : C) (v : Fin (c + 1) → ℕ)
    (E : Fin p → C × β) :
    CovAtExcept val i j v E ↔ CovAt (fun b k => val b (i.succAbove k)) j (fun k => v (i.succAbove k)) E := by
  constructor
  · intro h k
    exact h _ (Fin.succAbove_ne i k)
  · intro h k hk
    obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hk
    exact h k'
def WFTable (val : β → Fin 7 → ℕ) (i : Fin 7) : Prop :=
  ∀ p, (#{x : β × (Fin p → β) | CoversExcept val i (val x.1) x.2} : ℤ) =
    (Kernel.wfData.map fun e => e.2 * (e.1 : ℤ) ^ p).sum
theorem coord_near (val : β → Fin (c + 1) → ℕ) (i : Fin (c + 1)) (d : List (ℕ × ℤ))
    (h : ∀ p, (#{x : β × (Fin p → β) | CoversExcept val i (val x.1) x.2} : ℤ) = tmom d 0 p) (r : ℕ) :
    (#{x : (C × β) × (Fin r → C × β) | CovAtExcept val i x.1.1 (val x.1.2) x.2} : ℤ) =
      Fintype.card C * tmom d (((Fintype.card C - 1) * Fintype.card β : ℕ) : ℤ) r := by
  have h' : ∀ p, (#{x : β × (Fin p → β) | CoversT (fun b k => val b (i.succAbove k))
      ((fun b k => val b (i.succAbove k)) x.1) x.2} : ℤ) = tmom d 0 p := by
    intro p
    rw [← h p]
    congr 2
    ext x
    simp only [mem_filter, mem_univ, true_and]
    exact (coversExcept_iff val i _ _).symm
  rw [← coord_first (C := C) (fun b k => val b (i.succAbove k)) d h' r]
  congr 2
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact covAtExcept_iff val i _ _ _
def nearPred {r : ℕ} (val : β → Fin c → ℕ) (k₀ : Fin n) (i₀ : Fin c) (k : Fin n)
    (y : (C × β) × (Fin r → C × β)) : Prop :=
  ∀ i, (k, i) ≠ (k₀, i₀) → ∃ m, (y.2 m).1 = y.1.1 ∧ val y.1.2 i ≤ val (y.2 m).2 i
instance {r : ℕ} (val : β → Fin c → ℕ) (k₀ : Fin n) (i₀ : Fin c) (k : Fin n) :
    DecidablePred (nearPred (r := r) (C := C) val k₀ i₀ k) :=
  fun _ => Fintype.decidableForallFintype
def FullNear {r : ℕ} (val : β → Fin c → ℕ) (k₀ : Fin n) (i₀ : Fin c) (t : Fin n → C × β)
    (E : Fin r → Fin n → C × β) : Prop :=
  ∀ k i, (k, i) ≠ (k₀, i₀) → ∃ m, (E m k).1 = (t k).1 ∧ val (t k).2 i ≤ val (E m k).2 i
instance {r : ℕ} (val : β → Fin c → ℕ) (k₀ : Fin n) (i₀ : Fin c) (t : Fin n → C × β) :
    DecidablePred (FullNear (r := r) val k₀ i₀ t) :=
  fun _ => Fintype.decidableForallFintype
theorem card_full_near (val : β → Fin c → ℕ) (k₀ : Fin n) (i₀ : Fin c) (r : ℕ) :
    #{x : (Fin n → C × β) × (Fin r → Fin n → C × β) | FullNear val k₀ i₀ x.1 x.2} =
      #{y : (C × β) × (Fin r → C × β) | CovAt val y.1.1 (val y.1.2) y.2} ^ (n - 1) *
        #{y : (C × β) × (Fin r → C × β) | CovAtExcept val i₀ y.1.1 (val y.1.2) y.2} := by
  have h1 : #{x : (Fin n → C × β) × (Fin r → Fin n → C × β) | FullNear val k₀ i₀ x.1 x.2} =
      #{f : Fin n → (C × β) × (Fin r → C × β) | ∀ k, nearPred val k₀ i₀ k (f k)} := by
    symm
    refine card_equiv (coordEquiv (C × β) r (C × β)) fun f => ?_
    simp only [mem_filter, mem_univ, true_and]
    rfl
  have hk : ∀ k, #{y : (C × β) × (Fin r → C × β) | nearPred val k₀ i₀ k y} =
      if k = k₀ then #{y : (C × β) × (Fin r → C × β) | CovAtExcept val i₀ y.1.1 (val y.1.2) y.2}
      else #{y : (C × β) × (Fin r → C × β) | CovAt val y.1.1 (val y.1.2) y.2} := by
    intro k
    split_ifs with hk
    · subst hk
      congr 1
      ext y
      simp only [mem_filter, mem_univ, true_and]
      simp only [nearPred, CovAtExcept, ne_eq, Prod.mk.injEq, true_and]
    · congr 1
      ext y
      simp only [mem_filter, mem_univ, true_and]
      simp only [nearPred, CovAt, ne_eq, Prod.mk.injEq, hk, false_and, not_false_eq_true, forall_const]
  rw [h1, card_pi_forall (fun (k : Fin n) (y : (C × β) × (Fin r → C × β)) => nearPred val k₀ i₀ k y)]
  simp_rw [hk]
  rw [← mul_prod_erase univ _ (mem_univ k₀), if_pos rfl,
    prod_congr rfl (fun k hk' => if_neg (ne_of_mem_erase hk')), prod_const, card_erase_of_mem (mem_univ _),
    card_univ, Fintype.card_fin, mul_comm]
open SphincsSecurity.Concrete (uniformWordAverage)
open SigGolfResearch.Gate6.Moments (finiteAverage word_array_average)
def ListCovExcept (val : β → Fin c → ℕ) (k₀ : Fin n) (i₀ : Fin c) (L : List (Fin n → C × β))
    (t : Fin n → C × β) : Prop :=
  ∀ k i, (k, i) ≠ (k₀, i₀) → ∃ e ∈ L, (e k).1 = (t k).1 ∧ val (t k).2 i ≤ val (e k).2 i
instance (val : β → Fin c → ℕ) (k₀ : Fin n) (i₀ : Fin c) (L : List (Fin n → C × β)) :
    DecidablePred (ListCovExcept val k₀ i₀ L) := by
  unfold ListCovExcept
  infer_instance
noncomputable def nearEnv (val : β → Fin c → ℕ) (k₀ : Fin n) (i₀ : Fin c) (L : List (Fin n → C × β)) :
    ENNReal :=
  finiteAverage (fun t : Fin n → C × β => if ListCovExcept val k₀ i₀ L t then 1 else 0)
omit [Fintype β] [Fintype C] [DecidableEq C] in
theorem listCovExcept_ofFn {r : ℕ} (val : β → Fin c → ℕ) (k₀ : Fin n) (i₀ : Fin c)
    (E : Fin r → Fin n → C × β) (t : Fin n → C × β) :
    ListCovExcept val k₀ i₀ (List.ofFn E) t ↔ FullNear val k₀ i₀ t E := by
  simp only [ListCovExcept, FullNear, List.mem_ofFn]
  refine forall_congr' fun k => forall_congr' fun i => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨e, ⟨m, rfl⟩, h⟩
    exact ⟨m, h⟩
  · rintro ⟨m, h⟩
    exact ⟨E m, ⟨m, rfl⟩, h⟩
theorem nearEnv_cons_le (val : β → Fin c → ℕ) (k₀ : Fin n) (i₀ : Fin c) (a : Fin n → C × β)
    (L : List (Fin n → C × β)) : nearEnv val k₀ i₀ L ≤ nearEnv val k₀ i₀ (a :: L) := by
  unfold nearEnv finiteAverage
  refine ENNReal.div_le_div_right (sum_le_sum fun t _ => ?_) _
  split_ifs with h₁ h₂
  · exact le_rfl
  · refine absurd (fun k i hki => ?_) h₂
    obtain ⟨e, he, h'⟩ := h₁ k i hki
    exact ⟨e, List.mem_cons_of_mem a he, h'⟩
  · exact zero_le_one
  · exact le_rfl
theorem nearEnv_le_one (val : β → Fin c → ℕ) (k₀ : Fin n) (i₀ : Fin c) (L : List (Fin n → C × β)) :
    nearEnv val k₀ i₀ L ≤ 1 := by
  unfold nearEnv finiteAverage
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  calc ∑ t : Fin n → C × β, (if ListCovExcept val k₀ i₀ L t then (1 : ENNReal) else 0)
      ≤ ∑ _t : Fin n → C × β, (1 : ENNReal) := sum_le_sum fun t _ => by split_ifs <;> simp
    _ = Fintype.card (Fin n → C × β) := by simp
theorem nearEnv_moment_count [SampleableType (Fin n → C × β)] (val : β → Fin c → ℕ) (k₀ : Fin n)
    (i₀ : Fin c) (r : ℕ) :
    uniformWordAverage r (nearEnv (C := C) val k₀ i₀) =
      ((#{y : (C × β) × (Fin r → C × β) | CovAt val y.1.1 (val y.1.2) y.2} ^ (n - 1) *
          #{y : (C × β) × (Fin r → C × β) | CovAtExcept val i₀ y.1.1 (val y.1.2) y.2} : ℕ) : ENNReal) /
        ((Fintype.card (Fin n → C × β) : ENNReal) * Fintype.card (Fin r → Fin n → C × β)) := by
  rw [word_array_average]
  unfold nearEnv
  rw [avg_avg_ind (fun (t : Fin n → C × β) (E : Fin r → Fin n → C × β) =>
      ListCovExcept val k₀ i₀ (List.ofFn E) t), ← card_full_near val k₀ i₀ r]
  congr 3
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact listCovExcept_ofFn val k₀ i₀ x.2 x.1
open ClaudeWCT.Numerics.Kernel
theorem xfNum_cast (r : ℕ) (h : 0 ≤ tmom wfData B1 r) : (xfNum r : ℤ) = tmom wfData B1 r := by
  have hw := wpos_sub_wneg wfData B1 r
  unfold xfNum
  omega
theorem coord_near_xfNum (val : β → Fin 7 → ℕ) (i : Fin 7) (hβ : Fintype.card β = 728)
    (hC : Fintype.card C = 128) (hf : WFTable val i) (r : ℕ) :
    #{y : (C × β) × (Fin r → C × β) | CovAtExcept val i y.1.1 (val y.1.2) y.2} = Kc * xfNum r := by
  have hc := coord_near (C := C) val i wfData (fun p => (hf p).trans (tmom_zero wfData p).symm) r
  rw [B1_eq hβ hC, hC] at hc
  have hnn : 0 ≤ tmom wfData B1 r := by
    have := Int.natCast_nonneg (#{y : (C × β) × (Fin r → C × β) | CovAtExcept val i y.1.1 (val y.1.2) y.2})
    push_cast at hc
    omega
  have hx := xfNum_cast r hnn
  have hK : Kc = 128 := rfl
  rw [hK]
  push_cast at hc
  omega
theorem nearEnv_moment [SampleableType (Fin 9 → C × β)] (val : β → Fin 7 → ℕ) (k₀ : Fin 9) (i₀ : Fin 7)
    (hβ : Fintype.card β = 728) (hC : Fintype.card C = 128) (h₁ : W1Table val) (hf : WFTable val i₀)
    (r : ℕ) :
    uniformWordAverage r (nearEnv (C := C) val k₀ i₀) =
      ((xNum r ^ 8 * xfNum r : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal) := by
  have hE : Fintype.card (Fin r → Fin 9 → C × β) = (Q ^ 9) ^ r := by
    rw [Fintype.card_fun, card_table hβ hC, Fintype.card_fin]
  rw [nearEnv_moment_count, coord_first_xNum val hβ hC h₁ r, coord_near_xfNum val i₀ hβ hC hf r, hE,
    card_table hβ hC]
  have hnum : (Kc * xNum r) ^ (9 - 1) * (Kc * xfNum r) = Kc ^ 9 * (xNum r ^ 8 * xfNum r) := by ring
  have hden : (Q ^ 9 : ℕ) * (Q ^ 9) ^ r = Kc ^ 9 * (Nn ^ 9 * Q ^ (9 * r)) := by
    rw [← pow_mul, ← mul_assoc, ← mul_pow]
    rfl
  rw [hnum, ← Nat.cast_mul, hden, Nat.cast_mul, Nat.cast_mul (Kc ^ 9)]
  exact ENNReal.mul_div_mul_left _ _ (by simp [Kc]) (by simp)
end Near
end ClaudeWCT.Numerics.Thinning
end
section
namespace ClaudeWCT.Numerics.Covariance
open ENNReal Finset
open SphincsSecurity.Concrete (uniformWordAverage binomialAverage binomialAverage_succ binomialAverage_mono
  uniformWordAverage_mono uniformWordAverage_sum_square_le)
open SigGolfResearch.Gate6.Moments (finiteAverage uniformWordAverage_succ)
open SigGolfCandidate.T3.BPORS.History (atIndex jointCountAverage uniform_marked_word_joint
  uniform_marked_word_atIndex finiteAverage_constant)
noncomputable def average (rate : ℝ) : Nat → (Nat → ℝ) → ℝ
  | 0, f => f 0
  | steps + 1, f =>
      (1 - rate) * average rate steps f + rate * average rate steps (fun k ↦ f (k + 1))
noncomputable def pairAverage (p q : ℝ) : Nat → (Nat → ℝ) → (Nat → ℝ) → ℝ
  | 0, f, g => f 0 * g 0
  | steps + 1, f, g =>
      (1 - p - q) * pairAverage p q steps f g +
        p * pairAverage p q steps (fun k ↦ f (k + 1)) g +
        q * pairAverage p q steps f (fun k ↦ g (k + 1))
theorem average_mono (rate : ℝ) (hzero : 0 ≤ rate) (hone : rate ≤ 1)
    (steps : Nat) (f g : Nat → ℝ) (hle : ∀ k, f k ≤ g k) :
    average rate steps f ≤ average rate steps g := by
  induction steps generalizing f g
  rotate_left
  rename_i steps ih
  simp only [average]
  exact add_le_add (mul_le_mul_of_nonneg_left (ih f g hle) (sub_nonneg.mpr hone))
    (mul_le_mul_of_nonneg_left (ih _ _ (fun k ↦ hle (k + 1))) hzero)
  exact hle 0
theorem shift_le (rate : ℝ) (hzero : 0 ≤ rate) (hone : rate ≤ 1)
    (steps : Nat) (f : Nat → ℝ) (hf : Monotone f) :
    average rate steps f ≤ average rate steps (fun k ↦ f (k + 1)) := by
  exact average_mono rate hzero hone steps f _ (fun k ↦ hf (Nat.le_succ k))
theorem exclusive_mix (p q a a' b b' : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (ha : a ≤ a') (hb : b ≤ b') :
    (1 - p - q) * (a * b) + p * (a' * b) + q * (a * b') ≤
      ((1 - p) * a + p * a') * ((1 - q) * b + q * b') := by
  have hprod := mul_nonneg (mul_nonneg hp hq) (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb))
  nlinarith only [hprod]
theorem pair_bound (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1)
    (steps : Nat) (f g : Nat → ℝ) (hf : Monotone f) (hg : Monotone g) :
    pairAverage p q steps f g ≤ average p steps f * average q steps g := by
  induction steps generalizing f g
  rotate_left
  rename_i steps ih
  have hpone : p ≤ 1 := (by linarith)
  have hqone : q ≤ 1 := (by linarith)
  have hmiss : 0 ≤ 1 - p - q := (by linarith)
  have hfshift : Monotone (fun k ↦ f (k + 1)) := fun _ _ h ↦ hf (Nat.add_le_add_right h 1)
  have hgshift : Monotone (fun k ↦ g (k + 1)) := fun _ _ h ↦ hg (Nat.add_le_add_right h 1)
  simp only [pairAverage, average]
  refine le_trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (ih f g hf hg) hmiss)
    (mul_le_mul_of_nonneg_left (ih _ g hfshift hg) hp))
    (mul_le_mul_of_nonneg_left (ih f _ hf hgshift) hq)) ?_
  exact exclusive_mix p q _ _ _ _ hp hq (shift_le p hp hpone steps f hf) (shift_le q hq hqone steps g hg)
  exact le_rfl
theorem finiteAverage_two_point {α : Type} [Fintype α] [DecidableEq α] (first second : α)
    (hne : first ≠ second) (c u v : ENNReal) :
    finiteAverage (fun x : α => if x = first then c + u else if x = second then c + v else c) =
      c + (Fintype.card α : ENNReal)⁻¹ * u + (Fintype.card α : ENNReal)⁻¹ * v := by
  have hpt : ∀ x : α, (if x = first then c + u else if x = second then c + v else c) =
      c + (if x = first then u else 0) + (if x = second then v else 0) := by
    intro x
    by_cases h₁ : x = first
    · subst h₁; simp [hne]
    · by_cases h₂ : x = second
      · subst h₂; simp [h₁]
      · simp [h₁, h₂]
  have hcard : (Fintype.card α : ENNReal) ≠ 0 := by
    simpa using (Fintype.card_pos_iff.mpr ⟨first⟩).ne'
  unfold finiteAverage
  simp_rw [hpt]
  rw [sum_add_distrib, sum_add_distrib, sum_const, sum_ite_eq', sum_ite_eq', if_pos (mem_univ _),
    if_pos (mem_univ _), card_univ, nsmul_eq_mul, div_eq_mul_inv, add_mul, add_mul,
    mul_comm (Fintype.card α : ENNReal) c, mul_assoc, ENNReal.mul_inv_cancel hcard (by simp), mul_one,
    mul_comm u, mul_comm v]
theorem joint_pair_bound {α : Type} [Fintype α] [DecidableEq α] (first second : α) (hne : first ≠ second)
    (steps : Nat) (F G : Nat → ENNReal) (hF : Monotone F) (hG : Monotone G) :
    jointCountAverage first second steps (fun i j => F i * G j) ≤
      binomialAverage (Fintype.card α : ENNReal)⁻¹ steps F *
        binomialAverage (Fintype.card α : ENNReal)⁻¹ steps G := by
  set p : ENNReal := (Fintype.card α : ENNReal)⁻¹ with hp
  have hp1 : p ≤ 1 := by
    rw [hp]
    exact ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos_iff.mpr ⟨first⟩)
  induction steps generalizing F G with
  | zero => exact le_rfl
  | succ steps ih =>
    have hFs : Monotone (fun k => F (k + 1)) := fun _ _ h => hF (Nat.add_le_add_right h 1)
    have hGs : Monotone (fun k => G (k + 1)) := fun _ _ h => hG (Nat.add_le_add_right h 1)
    set a := binomialAverage p steps F
    set a' := binomialAverage p steps (fun k => F (k + 1))
    set b := binomialAverage p steps G
    set b' := binomialAverage p steps (fun k => G (k + 1))
    have ha : a ≤ a' := binomialAverage_mono p steps fun k => hF (Nat.le_succ k)
    have hb : b ≤ b' := binomialAverage_mono p steps fun k => hG (Nat.le_succ k)
    obtain ⟨da, hda⟩ := exists_add_of_le ha
    obtain ⟨db, hdb⟩ := exists_add_of_le hb
    calc jointCountAverage first second (steps + 1) (fun i j => F i * G j)
        = finiteAverage fun next : α =>
            if next = first then jointCountAverage first second steps (fun i j => F (i + 1) * G j)
            else if next = second then jointCountAverage first second steps (fun i j => F i * G (j + 1))
            else jointCountAverage first second steps (fun i j => F i * G j) := rfl
      _ ≤ finiteAverage fun next : α =>
            if next = first then a * b + da * b else if next = second then a * b + a * db else a * b := by
          unfold finiteAverage
          refine ENNReal.div_le_div_right (sum_le_sum fun next _ => ?_) _
          split_ifs
          · calc _ ≤ a' * b := ih _ G hFs hG
              _ = a * b + da * b := by rw [hda]; ring
          · calc _ ≤ a * b' := ih F _ hF hGs
              _ = a * b + a * db := by rw [hdb]; ring
          · exact ih F G hF hG
      _ = a * b + p * (da * b) + p * (a * db) := finiteAverage_two_point first second hne _ _ _
      _ ≤ a * b + p * (da * b) + p * (a * db) + p * da * (p * db) := le_self_add
      _ = ((1 - p) * a + p * a') * ((1 - p) * b + p * b') := by
          rw [hda, hdb]
          have h1 : (1 - p) * a + p * (a + da) = a + p * da := by
            rw [mul_add, ← add_assoc, ← add_mul, tsub_add_cancel_of_le hp1, one_mul]
          have h2 : (1 - p) * b + p * (b + db) = b + p * db := by
            rw [mul_add, ← add_assoc, ← add_mul, tsub_add_cancel_of_le hp1, one_mul]
          rw [h1, h2]
          ring
      _ = _ := by rw [binomialAverage_succ, binomialAverage_succ]
theorem uniformWordAverage_steps_mono {β : Type} [Fintype β] [SampleableType β] (f : List β → ENNReal)
    (hf : ∀ a w, f w ≤ f (a :: w)) : Monotone (fun n => uniformWordAverage n f) := by
  refine monotone_nat_of_le_succ fun n => ?_
  show uniformWordAverage n f ≤ uniformWordAverage (n + 1) f
  rw [uniformWordAverage_succ]
  calc uniformWordAverage n f = finiteAverage (fun _ : β => uniformWordAverage n f) :=
        (finiteAverage_constant _).symm
    _ ≤ finiteAverage (fun a : β => uniformWordAverage n (fun w => f (a :: w))) := by
        unfold finiteAverage
        exact ENNReal.div_le_div_right (sum_le_sum fun a _ => uniformWordAverage_mono n (hf a)) _
theorem marked_monotone_negative_correlation {α β : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    [Fintype β] [SampleableType β] (first second : α) (hne : first ≠ second) (steps : Nat)
    (f g : List β → ENNReal) (hf : Monotone (fun n => uniformWordAverage n f))
    (hg : Monotone (fun n => uniformWordAverage n g)) :
    uniformWordAverage steps (fun word : List (α × β) => f (atIndex first word) * g (atIndex second word)) ≤
      uniformWordAverage steps (fun word : List (α × β) => f (atIndex first word)) *
        uniformWordAverage steps (fun word : List (α × β) => g (atIndex second word)) := by
  rw [uniform_marked_word_joint first second hne, uniform_marked_word_atIndex,
    uniform_marked_word_atIndex]
  exact joint_pair_bound first second hne steps _ _ hf hg
theorem marked_cons_negative_correlation {α β : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    [Fintype β] [SampleableType β] (first second : α) (hne : first ≠ second) (steps : Nat)
    (f g : List β → ENNReal) (hf : ∀ a w, f w ≤ f (a :: w)) (hg : ∀ a w, g w ≤ g (a :: w)) :
    uniformWordAverage steps (fun word : List (α × β) => f (atIndex first word) * g (atIndex second word)) ≤
      uniformWordAverage steps (fun word : List (α × β) => f (atIndex first word)) *
        uniformWordAverage steps (fun word : List (α × β) => g (atIndex second word)) :=
  marked_monotone_negative_correlation first second hne steps f g
    (uniformWordAverage_steps_mono f hf) (uniformWordAverage_steps_mono g hg)
section Env
open ClaudeWCT.Numerics.Thinning
variable {c n : ℕ} {β : Type} [Fintype β] {C : Type} [Fintype C] [DecidableEq C]
  [SampleableType (Fin n → C × β)]
theorem env_index_negative_correlation {α : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    (val : β → Fin c → ℕ) (first second : α) (hne : first ≠ second) (steps : Nat) :
    uniformWordAverage steps (fun word : List (α × (Fin n → C × β)) =>
        env val (atIndex first word) * env val (atIndex second word)) ≤
      uniformWordAverage steps (fun word : List (α × (Fin n → C × β)) => env val (atIndex first word)) *
        uniformWordAverage steps (fun word : List (α × (Fin n → C × β)) => env val (atIndex second word)) :=
  marked_cons_negative_correlation first second hne steps _ _ (env_cons_le val) (env_cons_le val)
theorem env_sum_square_le {α : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    (val : β → Fin c → ℕ) (steps : Nat) :
    uniformWordAverage steps (fun word : List (α × (Fin n → C × β)) =>
        (∑ index : α, env val (atIndex index word)) ^ 2) ≤
      (∑ index : α, uniformWordAverage steps (fun word : List (α × (Fin n → C × β)) =>
          env val (atIndex index word))) ^ 2 +
        ∑ index : α, uniformWordAverage steps (fun word : List (α × (Fin n → C × β)) =>
          env val (atIndex index word) ^ 2) :=
  uniformWordAverage_sum_square_le steps (fun index word => env val (atIndex index word))
    (fun first second hne => env_index_negative_correlation val first second hne steps)
theorem env_index_moment {α : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    (val : β → Fin c → ℕ) (index : α) (steps power : Nat) :
    uniformWordAverage steps (fun word : List (α × (Fin n → C × β)) => env val (atIndex index word) ^ power) =
      binomialAverage (Fintype.card α : ENNReal)⁻¹ steps
        (fun r => uniformWordAverage r (fun L => env (n := n) (C := C) val L ^ power)) :=
  uniform_marked_word_atIndex index steps (fun L => env val L ^ power)
end Env
end ClaudeWCT.Numerics.Covariance
end
end
-- ==== merged from ClaudeWCT_Numerics_LawAverage ====
section

namespace ClaudeWCT.Numerics.Law
open ENNReal Finset
open SphincsSecurity.Concrete (uniformWordAverage binomialAverage binomialAverage_succ binomialAverage_mono
  binomialAverage_sum binomialAverage_mul_left binomialAverage_mul_right)
open SigGolfResearch.Gate6.Moments (finiteAverage uniformWordAverage_succ)
open SigGolfCandidate.T3.BPORS.History (atIndex atIndex_cons jointCountAverage)
noncomputable def lawAvg {β : Type} [Fintype β] (v : β → ENNReal) : ℕ → (List β → ENNReal) → ENNReal
  | 0, f => f []
  | n + 1, f => ∑ b, v b * lawAvg v n (fun L => f (b :: L))
section Basic
variable {β : Type} [Fintype β] (v : β → ENNReal)
theorem lawAvg_zero (f : List β → ENNReal) : lawAvg v 0 f = f [] := rfl
theorem lawAvg_succ (n : ℕ) (f : List β → ENNReal) :
    lawAvg v (n + 1) f = ∑ b, v b * lawAvg v n (fun L => f (b :: L)) := rfl
theorem lawAvg_add (n : ℕ) (f g : List β → ENNReal) :
    lawAvg v n (fun L => f L + g L) = lawAvg v n f + lawAvg v n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [lawAvg_succ]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [ih, mul_add]
theorem lawAvg_mul_left (n : ℕ) (c : ENNReal) (f : List β → ENNReal) :
    lawAvg v n (fun L => c * f L) = c * lawAvg v n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [lawAvg_succ, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [ih]; ring
theorem lawAvg_sum {ι : Type*} (n : ℕ) (s : Finset ι) (f : ι → List β → ENNReal) :
    lawAvg v n (fun L => ∑ i ∈ s, f i L) = ∑ i ∈ s, lawAvg v n (f i) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [lawAvg_succ]
    simp_rw [ih, mul_sum]
    exact sum_comm
theorem lawAvg_mono (n : ℕ) {f g : List β → ENNReal} (h : ∀ L, f L ≤ g L) : lawAvg v n f ≤ lawAvg v n g := by
  induction n generalizing f g with
  | zero => exact h []
  | succ n ih => exact sum_le_sum fun b _ => mul_le_mul' le_rfl (ih fun L => h (b :: L))
theorem lawAvg_const (hv : ∑ b, v b = 1) (n : ℕ) (c : ENNReal) : lawAvg v n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [lawAvg_succ]; simp only [ih]; rw [← sum_mul, hv, one_mul]
theorem lawAvg_steps_mono (hv : ∑ b, v b = 1) (f : List β → ENNReal) (hf : ∀ a L, f L ≤ f (a :: L)) :
    Monotone (fun n => lawAvg v n f) := by
  refine monotone_nat_of_le_succ fun n => ?_
  show lawAvg v n f ≤ lawAvg v (n + 1) f
  rw [lawAvg_succ]
  calc lawAvg v n f = ∑ b, v b * lawAvg v n f := by rw [← sum_mul, hv, one_mul]
    _ ≤ ∑ b, v b * lawAvg v n (fun L => f (b :: L)) :=
      sum_le_sum fun b _ => mul_le_mul' le_rfl (lawAvg_mono v n fun L => hf b L)
omit [Fintype β] in
theorem uniformWordAverage_zero' [SampleableType β] (f : List β → ENNReal) : uniformWordAverage 0 f = f [] := by
  simp [uniformWordAverage, SphincsSecurity.Concrete.sampleUniformProposalWord]
theorem lawAvg_le_uniform [SampleableType β] (κ : ENNReal) (hv : ∀ b, v b ≤ κ * (Fintype.card β : ENNReal)⁻¹)
    (n : ℕ) (f : List β → ENNReal) : lawAvg v n f ≤ κ ^ n * uniformWordAverage n f := by
  induction n generalizing f with
  | zero => rw [pow_zero, one_mul, uniformWordAverage_zero']; exact le_rfl
  | succ n ih =>
    rw [lawAvg_succ, uniformWordAverage_succ, finiteAverage]
    calc ∑ b, v b * lawAvg v n (fun L => f (b :: L))
        ≤ ∑ b, κ * (Fintype.card β : ENNReal)⁻¹ * (κ ^ n * uniformWordAverage n (fun L => f (b :: L))) :=
          sum_le_sum fun b _ => mul_le_mul' (hv b) (ih _)
      _ = κ ^ (n + 1) * ((∑ b, uniformWordAverage n (fun L => f (b :: L))) / (Fintype.card β : ENNReal)) := by
          simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
          refine sum_congr rfl fun b _ => ?_
          ring
end Basic
section Marked
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] (v : β → ENNReal)
noncomputable def marked (p : α × β) : ENNReal := (Fintype.card α : ENNReal)⁻¹ * v p.2
theorem sum_marked {α' : Type} [Fintype α'] [DecidableEq α'] (F : α' × β → ENNReal) :
    ∑ p, marked v p * F p = ∑ a, (Fintype.card α' : ENNReal)⁻¹ * ∑ b, v b * F (a, b) := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  simp only [marked]; ring
theorem marked_sum_one [Nonempty α] (hv : ∑ b, v b = 1) : ∑ p, marked (α := α) v p = 1 := by
  have h := sum_marked v (α' := α) (fun _ => (1 : ENNReal))
  simp only [mul_one] at h
  rw [h, hv, mul_one, sum_const, card_univ, nsmul_eq_mul,
    ENNReal.mul_inv_cancel (by simpa using Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]
theorem binomialAverage_lawSum (rate : ENNReal) (T : ℕ) (g : β → ℕ → ENNReal) :
    ∑ b, v b * binomialAverage rate T (g b) = binomialAverage rate T (fun r => ∑ b, v b * g b r) := by
  rw [binomialAverage_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [binomialAverage_mul_left]
omit [Fintype α] [Fintype β] in
theorem atIndex_cons_self (index : α) (b : β) (word : List (α × β)) :
    atIndex index ((index, b) :: word) = b :: atIndex index word := by
  rw [atIndex_cons]; simp
omit [Fintype α] [Fintype β] in
theorem atIndex_cons_ne {index a : α} (h : a ≠ index) (b : β) (word : List (α × β)) :
    atIndex index ((a, b) :: word) = atIndex index word := by
  rw [atIndex_cons]; simp [h]
theorem sum_inv_ite [Nonempty α] (index : α) (X Y : ENNReal) :
    ∑ a : α, (Fintype.card α : ENNReal)⁻¹ * (if a = index then X else Y) =
      (1 - (Fintype.card α : ENNReal)⁻¹) * Y + (Fintype.card α : ENNReal)⁻¹ * X := by
  set p : ENNReal := (Fintype.card α : ENNReal)⁻¹ with hp
  have hc : (Fintype.card α : ENNReal) ≠ 0 := by simpa using Fintype.card_ne_zero
  have hc' : (Fintype.card α : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [← add_sum_erase _ _ (mem_univ index), if_pos rfl]
  have hrest : ∑ a ∈ univ.erase index, p * (if a = index then X else Y) = ((Fintype.card α - 1 : ℕ) : ENNReal) * (p * Y) := by
    rw [sum_congr rfl fun a ha => by rw [if_neg (ne_of_mem_erase ha)], sum_const, card_erase_of_mem (mem_univ _),
      card_univ, nsmul_eq_mul]
  rw [hrest]
  have hk : ((Fintype.card α - 1 : ℕ) : ENNReal) * p = 1 - p := by
    have hpos := Fintype.card_pos (α := α)
    have h1 : ((Fintype.card α - 1 : ℕ) : ENNReal) + 1 = Fintype.card α := by
      norm_cast; omega
    have h2 : ((Fintype.card α - 1 : ℕ) : ENNReal) * p + p = 1 := by
      rw [← add_one_mul, h1, hp, ENNReal.mul_inv_cancel hc hc']
    rw [← h2, ENNReal.add_sub_cancel_right (by simp [hp, hc])]
  rw [← mul_assoc, hk]
  ring
theorem law_marked_atIndex [Nonempty α] (hv : ∑ b, v b = 1) (index : α) (T : ℕ) (payoff : List β → ENNReal) :
    lawAvg (marked (α := α) v) T (fun word : List (α × β) => payoff (atIndex index word)) =
      binomialAverage (Fintype.card α : ENNReal)⁻¹ T (fun r => lawAvg v r payoff) := by
  induction T generalizing payoff with
  | zero => simp [lawAvg_zero, atIndex, binomialAverage]
  | succ T ih =>
    rw [lawAvg_succ, sum_marked, binomialAverage_succ]
    have hrow : ∀ a : α, ∑ b, v b * lawAvg (marked (α := α) v) T
        (fun word => payoff (atIndex index ((a, b) :: word))) =
        if a = index then binomialAverage (Fintype.card α : ENNReal)⁻¹ T (fun r => lawAvg v (r + 1) payoff)
        else binomialAverage (Fintype.card α : ENNReal)⁻¹ T (fun r => lawAvg v r payoff) := by
      intro a
      by_cases ha : a = index
      · rw [if_pos ha]
        subst ha
        simp_rw [atIndex_cons_self]
        have hb : ∀ b, lawAvg (marked (α := α) v) T (fun word => payoff (b :: atIndex a word)) =
            binomialAverage (Fintype.card α : ENNReal)⁻¹ T (fun r => lawAvg v r (fun L => payoff (b :: L))) :=
          fun b => ih (fun L => payoff (b :: L))
        simp_rw [hb]
        rw [binomialAverage_lawSum]
        rfl
      · rw [if_neg ha]
        simp_rw [atIndex_cons_ne ha]
        rw [ih, ← sum_mul, hv, one_mul]
    simp_rw [hrow]
    exact sum_inv_ite index _ _
theorem jca_lawSum (first second : α) (T : ℕ) (P : β → ℕ → ℕ → ENNReal) :
    ∑ b, v b * jointCountAverage first second T (P b) =
      jointCountAverage first second T (fun i j => ∑ b, v b * P b i j) := by
  induction T generalizing P with
  | zero => rfl
  | succ T ih =>
    simp only [jointCountAverage, finiteAverage]
    simp_rw [div_eq_mul_inv, ← mul_assoc, ← sum_mul, mul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    split_ifs
    · exact ih (fun b i j => P b (i + 1) j)
    · exact ih (fun b i j => P b i (j + 1))
    · exact ih P
theorem law_marked_joint [Nonempty α] (hv : ∑ b, v b = 1) (first second : α) (hne : first ≠ second) (T : ℕ)
    (f g : List β → ENNReal) :
    lawAvg (marked (α := α) v) T (fun word : List (α × β) => f (atIndex first word) * g (atIndex second word)) =
      jointCountAverage first second T (fun i j => lawAvg v i f * lawAvg v j g) := by
  induction T generalizing f g with
  | zero => simp [lawAvg_zero, atIndex, jointCountAverage]
  | succ T ih =>
    rw [lawAvg_succ, sum_marked]
    show _ = finiteAverage _
    unfold finiteAverage
    rw [div_eq_mul_inv, sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_comm]
    congr 1
    by_cases hf : a = first
    · subst hf
      rw [if_pos rfl]
      simp_rw [atIndex_cons_self, atIndex_cons_ne hne]
      have hb : ∀ b, lawAvg (marked (α := α) v) T
          (fun word => f (b :: atIndex a word) * g (atIndex second word)) =
          jointCountAverage a second T (fun i j => lawAvg v i (fun L => f (b :: L)) * lawAvg v j g) :=
        fun b => ih (fun L => f (b :: L)) g
      simp_rw [hb]
      rw [jca_lawSum]
      simp_rw [← mul_assoc, ← sum_mul]
      rfl
    · rw [if_neg hf]
      by_cases hs : a = second
      · subst hs
        rw [if_pos rfl]
        simp_rw [atIndex_cons_self, atIndex_cons_ne hf]
        have hb : ∀ b, lawAvg (marked (α := α) v) T
            (fun word => f (atIndex first word) * g (b :: atIndex a word)) =
            jointCountAverage first a T (fun i j => lawAvg v i f * lawAvg v j (fun L => g (b :: L))) :=
          fun b => ih f (fun L => g (b :: L))
        simp_rw [hb]
        rw [jca_lawSum]
        simp_rw [mul_left_comm _ (lawAvg v _ f), ← mul_sum]
        rfl
      · rw [if_neg hs]
        simp_rw [atIndex_cons_ne hf, atIndex_cons_ne hs]
        rw [ih, ← sum_mul, hv, one_mul]
theorem law_marked_negative_correlation [Nonempty α] (hv : ∑ b, v b = 1) (first second : α)
    (hne : first ≠ second) (T : ℕ) (f g : List β → ENNReal) (hf : ∀ a L, f L ≤ f (a :: L))
    (hg : ∀ a L, g L ≤ g (a :: L)) :
    lawAvg (marked (α := α) v) T (fun word : List (α × β) => f (atIndex first word) * g (atIndex second word)) ≤
      lawAvg (marked (α := α) v) T (fun word : List (α × β) => f (atIndex first word)) *
        lawAvg (marked (α := α) v) T (fun word : List (α × β) => g (atIndex second word)) := by
  rw [law_marked_joint v hv first second hne, law_marked_atIndex v hv, law_marked_atIndex v hv]
  exact ClaudeWCT.Numerics.Covariance.joint_pair_bound first second hne T _ _
    (lawAvg_steps_mono v hv f hf) (lawAvg_steps_mono v hv g hg)
end Marked
section Square
variable {γ : Type} [Fintype γ] (w : γ → ENNReal)
theorem lawAvg_sum_square_le {ι : Type} [Fintype ι] [DecidableEq ι] (T : ℕ) (payoff : ι → List γ → ENNReal)
    (hcross : ∀ first second, first ≠ second →
      lawAvg w T (fun word => payoff first word * payoff second word) ≤
        lawAvg w T (payoff first) * lawAvg w T (payoff second)) :
    lawAvg w T (fun word => (∑ index, payoff index word) ^ 2) ≤
      (∑ index, lawAvg w T (payoff index)) ^ 2 + ∑ index, lawAvg w T (fun word => payoff index word ^ 2) := by
  calc
    _ = ∑ first, ∑ second, lawAvg w T (fun word => payoff first word * payoff second word) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [lawAvg_sum]
      simp_rw [lawAvg_sum]
      exact Finset.sum_comm
    _ ≤ ∑ first, ∑ second,
        (lawAvg w T (payoff first) * lawAvg w T (payoff second) +
          if second = first then lawAvg w T (fun word => payoff first word ^ 2) else 0) := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      by_cases heq : first = second
      · subst second
        simp only [↓reduceIte, pow_two]
        exact le_add_self
      · simpa only [if_neg (Ne.symm heq), add_zero] using hcross first second heq
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        pow_two, Finset.sum_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
end Square
section Uniform
variable {β : Type} [Fintype β] [SampleableType β]
theorem lawAvg_uniform (n : ℕ) (f : List β → ENNReal) :
    lawAvg (fun _ => (Fintype.card β : ENNReal)⁻¹) n f = uniformWordAverage n f := by
  induction n generalizing f with
  | zero => rw [lawAvg_zero, uniformWordAverage_zero']
  | succ n ih =>
    rw [lawAvg_succ, uniformWordAverage_succ, finiteAverage, div_eq_mul_inv, sum_mul]
    refine sum_congr rfl fun b _ => ?_
    rw [ih, mul_comm]
end Uniform
end ClaudeWCT.Numerics.Law

namespace ClaudeWCT.Numerics.Law
open ENNReal Finset

/-- The constant and singleton terms in a nonnegative product expansion. -/
theorem prod_linear_terms_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a d : ι → ENNReal) :
    (∏ i ∈ s, a i) + ∑ i ∈ s, d i * ∏ j ∈ s.erase i, a j ≤ ∏ i ∈ s, (a i + d i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    have hterm : ∀ i ∈ s, d i * ∏ j ∈ (insert k s).erase i, a j =
        a k * (d i * ∏ j ∈ s.erase i, a j) := by
      intro i hi
      have hki : k ≠ i := fun h => hk (h ▸ hi)
      rw [Finset.erase_insert_of_ne hki, Finset.prod_insert]
      · ring
      · exact fun h => hk (Finset.mem_of_mem_erase h)
    rw [Finset.prod_insert hk, Finset.sum_insert hk, Finset.erase_insert_eq_erase,
      Finset.erase_eq_of_notMem hk, Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      Finset.prod_insert hk]
    calc
      a k * (∏ i ∈ s, a i) + (d k * (∏ j ∈ s, a j) + a k * ∑ i ∈ s, d i * ∏ j ∈ s.erase i, a j)
          = a k * ((∏ i ∈ s, a i) + ∑ i ∈ s, d i * ∏ j ∈ s.erase i, a j) +
            d k * (∏ j ∈ s, a j) := by ring
      _ ≤ a k * (∏ i ∈ s, (a i + d i)) + d k * (∏ i ∈ s, (a i + d i)) :=
        add_le_add (mul_le_mul' le_rfl ih)
          (mul_le_mul' le_rfl (Finset.prod_le_prod' fun _ _ => le_self_add))
      _ = _ := by ring

/-- Mixing one coordinate at a time is bounded by independent coordinate mixtures. -/
theorem exclusive_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ENNReal) (hp : p ≤ 1) (hcard : (Fintype.card ι : ENNReal) * p = 1)
    (a b : ι → ENNReal) (hab : ∀ i, a i ≤ b i) :
    ∑ i, p * (b i * ∏ j ∈ Finset.univ.erase i, a j) ≤
      ∏ i, ((1 - p) * a i + p * b i) := by
  choose d hd using fun i => exists_add_of_le (hab i)
  have hbase : ∀ i, a i * ∏ j ∈ Finset.univ.erase i, a j = ∏ j, a j :=
    fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have hmix : ∀ i, (1 - p) * a i + p * b i = a i + p * d i := by
    intro i
    rw [hd i, mul_add, ← add_assoc, ← add_mul, tsub_add_cancel_of_le hp, one_mul]
  simp_rw [hmix, hd, add_mul, mul_add, hbase]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, hcard, one_mul]
  simpa only [mul_assoc] using prod_linear_terms_le Finset.univ a (fun i => p * d i)

end ClaudeWCT.Numerics.Law

namespace ClaudeWCT.Numerics.Law
open ENNReal Finset
open SphincsSecurity.Concrete (binomialAverage binomialAverage_succ binomialAverage_mono)
open SigGolfCandidate.T3.BPORS.History (atIndex atIndex_cons)

noncomputable def coordAverage {β : Type} [Fintype β] (p : ENNReal) (v : β → ENNReal)
    (T : ℕ) (f : List β → ENNReal) : ENNReal :=
  binomialAverage p T (fun r => lawAvg v r f)

theorem coordAverage_mono {β : Type} [Fintype β] (p : ENNReal) (v : β → ENNReal)
    (T : ℕ) {f g : List β → ENNReal} (h : ∀ L, f L ≤ g L) :
    coordAverage p v T f ≤ coordAverage p v T g :=
  binomialAverage_mono p T fun r => lawAvg_mono v r h

theorem coordAverage_succ {β : Type} [Fintype β] (p : ENNReal) (v : β → ENNReal)
    (T : ℕ) (f : List β → ENNReal) :
    coordAverage p v (T + 1) f = (1 - p) * coordAverage p v T f +
      p * ∑ b, v b * coordAverage p v T (fun L => f (b :: L)) := by
  unfold coordAverage
  rw [binomialAverage_succ, binomialAverage_lawSum]
  rfl

/-- Product negative dependence for marked buckets.  The insertion condition allows
arbitrary symmetric monotone bucket statistics, including capped coverage prices. -/
theorem law_marked_product_le {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] (v : β → ENNReal) (hv : ∑ b, v b = 1) (T : ℕ)
    (f : α → List β → ENNReal)
    (hf : ∀ i L b R, f i (L ++ R) ≤ f i (L ++ b :: R)) :
    lawAvg (marked (α := α) v) T (fun W => ∏ i, f i (atIndex i W)) ≤
      ∏ i, coordAverage (Fintype.card α : ENNReal)⁻¹ v T (f i) := by
  set p : ENNReal := (Fintype.card α : ENNReal)⁻¹ with hp
  have hp1 : p ≤ 1 := by
    rw [hp]
    exact ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos (α := α))
  have hcard : (Fintype.card α : ENNReal) * p = 1 := by
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)
  induction T generalizing f with
  | zero => simp [lawAvg_zero, coordAverage, binomialAverage, atIndex]
  | succ T ih =>
    let A : α → ENNReal := fun i => coordAverage p v T (f i)
    let B : α → ENNReal := fun i => ∑ b, v b * coordAverage p v T (fun L => f i (b :: L))
    have hAB : ∀ i, A i ≤ B i := by
      intro i
      calc A i = ∑ b, v b * A i := by rw [← Finset.sum_mul, hv, one_mul]
        _ ≤ B i := Finset.sum_le_sum fun b _ => mul_le_mul' le_rfl
          (coordAverage_mono p v T fun L => by simpa using hf i [] b L)
    have hnext : ∀ a b,
        lawAvg (marked (α := α) v) T (fun W => ∏ i, f i (atIndex i ((a, b) :: W))) ≤
          coordAverage p v T (fun L => f a (b :: L)) * ∏ j ∈ Finset.univ.erase a, A j := by
      intro a b
      let g : α → List β → ENNReal := fun i L => if i = a then f i (b :: L) else f i L
      have hg : ∀ i L c R, g i (L ++ R) ≤ g i (L ++ c :: R) := by
        intro i L c R
        by_cases hi : i = a
        · simpa only [g, if_pos hi, List.cons_append] using hf i (b :: L) c R
        · simpa only [g, if_neg hi] using hf i L c R
      have hpoint : (fun W => ∏ i, f i (atIndex i ((a, b) :: W))) =
          (fun W => ∏ i, g i (atIndex i W)) := by
        funext W
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i = a
        · subst i; simp [g, atIndex_cons]
        · simp [g, atIndex_cons, hi, Ne.symm hi]
      rw [hpoint]
      refine (ih g hg).trans_eq ?_
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
      congr 1
      · simp [g]
      · apply Finset.prod_congr rfl
        intro i hi
        simp only [g, if_neg (Finset.ne_of_mem_erase hi)]
        rfl
    rw [lawAvg_succ, sum_marked]
    calc
      (∑ a : α, (Fintype.card α : ENNReal)⁻¹ * ∑ b, v b *
        lawAvg (marked (α := α) v) T (fun W => ∏ i, f i (atIndex i ((a,b) :: W))))
          ≤ ∑ a, p * ∑ b, v b *
            (coordAverage p v T (fun L => f a (b :: L)) * ∏ j ∈ Finset.univ.erase a, A j) :=
        Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl
          (Finset.sum_le_sum fun b _ => mul_le_mul' le_rfl (hnext a b))
      _ = ∑ a, p * (B a * ∏ j ∈ Finset.univ.erase a, A j) := by
        simp only [B, Finset.sum_mul, mul_assoc]
      _ ≤ ∏ i, ((1-p) * A i + p * B i) := exclusive_prod_le p hp1 hcard A B hAB
      _ = ∏ i, coordAverage p v (T+1) (f i) := by
        apply Finset.prod_congr rfl
        intro i _
        exact (coordAverage_succ p v T (f i)).symm

end ClaudeWCT.Numerics.Law

namespace ClaudeWCT.Numerics.Law
open ENNReal Finset
open SphincsSecurity.Concrete (binomialAverage binomialAverage_add binomialAverage_const)

theorem coordAverage_add {β : Type} [Fintype β] (p : ENNReal) (v : β → ENNReal)
    (T : ℕ) (f g : List β → ENNReal) :
    coordAverage p v T (fun L => f L + g L) = coordAverage p v T f + coordAverage p v T g := by
  unfold coordAverage
  simp_rw [lawAvg_add]
  exact binomialAverage_add p T _ _

theorem coordAverage_const {β : Type} [Fintype β] (p : ENNReal) (hp : p ≤ 1)
    (v : β → ENNReal) (hv : ∑ b, v b = 1) (T : ℕ) (c : ENNReal) :
    coordAverage p v T (fun _ => c) = c := by
  unfold coordAverage
  simp_rw [lawAvg_const v hv]
  exact binomialAverage_const hp T c

/-- A convenient exponential-moment consequence of bucket product dependence. -/
theorem law_marked_exp_sum_le {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] (v : β → ENNReal) (hv : ∑ b, v b = 1) (T : ℕ)
    (Y : α → List β → ENNReal)
    (hY : ∀ i L, Y i L ≤ 1)
    (hmono : ∀ i L b R, Y i (L ++ R) ≤ Y i (L ++ b :: R))
    (hinc : (∑ i, coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => ENNReal.ofReal (Real.exp (8 * (Y i L).toReal)) - 1)) ≤ 8) :
    lawAvg (marked (α := α) v) T (fun W =>
      ENNReal.ofReal (Real.exp (8 * (∑ i, Y i (SigGolfCandidate.T3.BPORS.History.atIndex i W)).toReal))) ≤
      ENNReal.ofReal (Real.exp 8) := by
  let p : ENNReal := (Fintype.card α : ENNReal)⁻¹
  have hp : p ≤ 1 := ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos (α := α))
  let F : α → List β → ENNReal := fun i L => ENNReal.ofReal (Real.exp (8 * (Y i L).toReal))
  let M : α → ENNReal := fun i => coordAverage p v T (fun L => F i L - 1)
  have hfin : ∀ i L, Y i L ≠ ⊤ := fun i L => ne_top_of_le_ne_top ENNReal.one_ne_top (hY i L)
  have hF1 : ∀ i L, 1 ≤ F i L := by
    intro i L
    apply ENNReal.one_le_ofReal.mpr
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hFmono : ∀ i L b R, F i (L ++ R) ≤ F i (L ++ b :: R) := by
    intro i L b R
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (hfin i _) (hmono i L b R)) (by norm_num)
  have hM : ∑ i, M i ≤ 8 := hinc
  have hMi : ∀ i, M i ≠ ⊤ := by
    intro i
    exact ne_top_of_le_ne_top (by finiteness)
      ((Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)).trans hM)
  have hMF : ∀ i, coordAverage p v T (F i) = 1 + M i := by
    intro i
    have heq : F i = fun L => 1 + (F i L - 1) := by
      funext L
      exact (add_tsub_cancel_of_le (hF1 i L)).symm
    rw [heq, coordAverage_add, coordAverage_const p hp v hv]
  have hprod : ∏ i, (1 + M i) ≤ ENNReal.ofReal (Real.exp 8) := by
    calc
      (∏ i, (1 + M i)) ≤ ∏ i, ENNReal.ofReal (Real.exp (M i).toReal) := by
        apply Finset.prod_le_prod'
        intro i _
        rw [← ENNReal.ofReal_toReal (hMi i), ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num) ENNReal.toReal_nonneg]
        apply ENNReal.ofReal_le_ofReal
        simpa [add_comm] using Real.add_one_le_exp (M i).toReal
      _ = ENNReal.ofReal (Real.exp ((∑ i, M i).toReal)) := by
        rw [ENNReal.toReal_sum (fun i _ => hMi i), Real.exp_sum,
          ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
      _ ≤ ENNReal.ofReal (Real.exp 8) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        simpa using ENNReal.toReal_mono (by finiteness : (8 : ENNReal) ≠ ⊤) hM
  have heq : (fun W => ENNReal.ofReal (Real.exp
      (8 * (∑ i, Y i (SigGolfCandidate.T3.BPORS.History.atIndex i W)).toReal))) =
      (fun W => ∏ i, F i (SigGolfCandidate.T3.BPORS.History.atIndex i W)) := by
    funext W
    rw [ENNReal.toReal_sum (fun i _ => hfin i _), Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  rw [heq]
  refine (law_marked_product_le v hv T F hFmono).trans ?_
  change (∏ i, coordAverage p v T (F i)) ≤ _
  simpa only [hMF] using hprod

end ClaudeWCT.Numerics.Law

/-! Variable exponential slope and moment budget for paired forest pricing. -/
namespace ClaudeWCT.Numerics.Law
open ENNReal Finset
open SphincsSecurity.Concrete (binomialAverage binomialAverage_add binomialAverage_const)

theorem law_marked_exp_sum_general {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] (v : β → ENNReal) (hv : ∑ b, v b = 1) (T : ℕ)
    (Y : α → List β → ENNReal) (t bound : ℝ)
    (ht : 0 ≤ t) (hbound : 0 ≤ bound)
    (hY : ∀ i L, Y i L ≠ ⊤)
    (hmono : ∀ i L b R, Y i (L ++ R) ≤ Y i (L ++ b :: R))
    (hinc : (∑ i, coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => ENNReal.ofReal (Real.exp (t * (Y i L).toReal)) - 1)) ≤ ENNReal.ofReal bound) :
    lawAvg (marked (α := α) v) T (fun W =>
      ENNReal.ofReal (Real.exp (t * (∑ i, Y i (SigGolfCandidate.T3.BPORS.History.atIndex i W)).toReal))) ≤
      ENNReal.ofReal (Real.exp bound) := by
  let p : ENNReal := (Fintype.card α : ENNReal)⁻¹
  have hp : p ≤ 1 := ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos (α := α))
  let F : α → List β → ENNReal := fun i L => ENNReal.ofReal (Real.exp (t * (Y i L).toReal))
  let M : α → ENNReal := fun i => coordAverage p v T (fun L => F i L - 1)
  have hfin : ∀ i L, Y i L ≠ ⊤ := hY
  have hF1 : ∀ i L, 1 ≤ F i L := by
    intro i L
    apply ENNReal.one_le_ofReal.mpr
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hFmono : ∀ i L b R, F i (L ++ R) ≤ F i (L ++ b :: R) := by
    intro i L b R
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (hfin i _) (hmono i L b R)) ht
  have hM : ∑ i, M i ≤ ENNReal.ofReal bound := hinc
  have hMi : ∀ i, M i ≠ ⊤ := by
    intro i
    exact ne_top_of_le_ne_top (by finiteness)
      ((Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)).trans hM)
  have hMF : ∀ i, coordAverage p v T (F i) = 1 + M i := by
    intro i
    have heq : F i = fun L => 1 + (F i L - 1) := by
      funext L
      exact (add_tsub_cancel_of_le (hF1 i L)).symm
    rw [heq, coordAverage_add, coordAverage_const p hp v hv]
  have hprod : ∏ i, (1 + M i) ≤ ENNReal.ofReal (Real.exp bound) := by
    calc
      (∏ i, (1 + M i)) ≤ ∏ i, ENNReal.ofReal (Real.exp (M i).toReal) := by
        apply Finset.prod_le_prod'
        intro i _
        rw [← ENNReal.ofReal_toReal (hMi i), ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num) ENNReal.toReal_nonneg]
        apply ENNReal.ofReal_le_ofReal
        simpa [add_comm] using Real.add_one_le_exp (M i).toReal
      _ = ENNReal.ofReal (Real.exp ((∑ i, M i).toReal)) := by
        rw [ENNReal.toReal_sum (fun i _ => hMi i), Real.exp_sum,
          ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
      _ ≤ ENNReal.ofReal (Real.exp bound) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        simpa only [ENNReal.toReal_ofReal hbound] using
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hM
  have heq : (fun W => ENNReal.ofReal (Real.exp
      (t * (∑ i, Y i (SigGolfCandidate.T3.BPORS.History.atIndex i W)).toReal))) =
      (fun W => ∏ i, F i (SigGolfCandidate.T3.BPORS.History.atIndex i W)) := by
    funext W
    rw [ENNReal.toReal_sum (fun i _ => hfin i _), Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  rw [heq]
  refine (law_marked_product_le v hv T F hFmono).trans ?_
  change (∏ i, coordAverage p v T (F i)) ≤ _
  simpa only [hMF] using hprod

end ClaudeWCT.Numerics.Law
end
