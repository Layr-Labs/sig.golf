import SigGolfCandidate.ClaudeWCT.Arith.FamilySideChannel
import SigGolfCandidate.ClaudeWCT.Arith.SideChannelComp

/-!
# Family test programs averaged over the family (campaign X1, stage B, item B3)

A test program `tr r` that may depend on the revealed seeds `r` of a uniform family `K` of `n` coefficients and tests the
unrevealed seeds. Averaging over `K`:

* `family_test_le` / `family_test_ge`: the real family and the family with the seed of chain `a` replaced by an
  independent uniform value give the same success probability up to `2 δ K(D) Σ_K amLen`;
* `family_amLen_le`: `Σ_K amLen · (1 - δ₁ D) ≤ Σ_K E[#tests]`.

The sums run over all `K : Fin n → Digest` (unnormalised); grouping by the revealed seeds reduces to
`comp_mass_le` / `amLen_le_enT` with the conditional laws `realLaw` / `hybLaw`.
-/

namespace ClaudeWCT.Arith.SideChannel
open SigGolfCandidate.T3 (Digest)
open Finset

attribute [local instance low] Classical.propDecidable
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

section FamilyTest
variable {C : Type} [Fintype C] [DecidableEq C] (pt : C → ℕ) (Rev : Finset C) {n : ℕ}

/-- The unrevealed seeds of the family `K`. -/
noncomputable def seedsY (K : Fin n → Digest) : Free Rev → Digest :=
  fun i => familyEval (List.ofFn K) (pt i.val)
/-- The revealed seeds of `K` (zero off `Rev`). -/
noncomputable def seedsR (K : Fin n → Digest) : C → Digest :=
  fun c => if c ∈ Rev then familyEval (List.ofFn K) (pt c) else 0
/-- The unrevealed seeds with the seed of chain `a` replaced by `s`. -/
noncomputable def seedsH (a : Free Rev) (K : Fin n → Digest) (s : Digest) : Free Rev → Digest :=
  fun i => if i = a then s else seedsY pt Rev K i

theorem mem_famA_seedsR (K K' : Fin n → Digest) :
    K' ∈ famA n pt Rev (seedsR pt Rev K) ↔ seedsR pt Rev K' = seedsR pt Rev K := by
  unfold famA seedsR
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    funext c
    split_ifs with hc
    · exact (h c hc).trans (if_pos hc)
    · rfl
  · intro h c hc
    have := congrFun h c
    simp only [if_pos hc] at this
    rw [this, if_pos hc]

theorem sum_pushW_mul {Ω ι' : Type} [Fintype ι'] [DecidableEq ι'] (A : Finset Ω) (f : Ω → (ι' → Digest))
    (G : (ι' → Digest) → ℝ) : ∑ y, pushW A f y * G y = (∑ ω ∈ A, G (f ω)) / A.card := by
  unfold pushW
  simp only [div_mul_eq_mul_div, ← sum_div]
  congr 1
  rw [← sum_fiberwise_of_maps_to (s := A) (t := univ) (g := f) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_congr rfl (fun ω hω => by rw [(mem_filter.mp hω).2]), sum_const, nsmul_eq_mul]

theorem famA_seedsR_nonempty (K : Fin n → Digest) : (famA n pt Rev (seedsR pt Rev K)).Nonempty := by
  refine ⟨K, ?_⟩
  rw [mem_famA_seedsR]

/-- Grouping by the revealed seeds: the real family. -/
theorem sum_group_real (H : (C → Digest) → (Free Rev → Digest) → ℝ) :
    ∑ K : Fin n → Digest, H (seedsR pt Rev K) (seedsY pt Rev K) =
      ∑ r ∈ univ.image (seedsR (n := n) pt Rev), ((famA n pt Rev r).card : ℝ) *
        ∑ y, realLaw n pt Rev r y * H r y := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image (seedsR (n := n) pt Rev)) (g := seedsR pt Rev)
    (fun K _ => by simp)]
  refine sum_congr rfl fun r hr => ?_
  rw [mem_image] at hr
  obtain ⟨K0, -, hK0⟩ := hr
  have hfib : univ.filter (fun K => seedsR pt Rev K = r) = famA n pt Rev r := by
    ext K
    rw [← hK0, mem_famA_seedsR, mem_filter]
    simp only [mem_univ, true_and]
  rw [hfib, realLaw, sum_pushW_mul]
  have hpos : (0 : ℝ) < (famA n pt Rev r).card := by
    rw [← hK0]
    exact_mod_cast (famA_seedsR_nonempty pt Rev K0).card_pos
  rw [mul_div_cancel₀ _ hpos.ne']
  refine sum_congr rfl fun K hK => ?_
  rw [← hK0, mem_famA_seedsR] at hK
  rw [hK, hK0]
  rfl

/-- Grouping by the revealed seeds: the hybrid family. -/
theorem sum_group_hyb (a : Free Rev) (H : (C → Digest) → (Free Rev → Digest) → ℝ) :
    ∑ K : Fin n → Digest, (∑ s, H (seedsR pt Rev K) (seedsH pt Rev a K s)) / Fintype.card Digest =
      ∑ r ∈ univ.image (seedsR (n := n) pt Rev), ((famA n pt Rev r).card : ℝ) *
        ∑ y, hybLaw n pt Rev r a y * H r y := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image (seedsR (n := n) pt Rev)) (g := seedsR pt Rev)
    (fun K _ => by simp)]
  refine sum_congr rfl fun r hr => ?_
  rw [mem_image] at hr
  obtain ⟨K0, -, hK0⟩ := hr
  have hfib : univ.filter (fun K => seedsR pt Rev K = r) = famA n pt Rev r := by
    ext K
    rw [← hK0, mem_famA_seedsR, mem_filter]
    simp only [mem_univ, true_and]
  rw [hfib, hybLaw, sum_pushW_mul, card_product, card_univ]
  have hpos : (0 : ℝ) < (famA n pt Rev r).card := by
    rw [← hK0]
    exact_mod_cast (famA_seedsR_nonempty pt Rev K0).card_pos
  have hD : (0 : ℝ) < Fintype.card Digest := by exact_mod_cast Fintype.card_pos
  rw [sum_product, ← sum_div]
  push_cast
  have hBA : ∑ K ∈ famA n pt Rev r, ∑ s, H (seedsR pt Rev K) (seedsH pt Rev a K s) =
      ∑ K ∈ famA n pt Rev r, ∑ s, H r (fun i => if i = a then s else familyEval (List.ofFn K) (pt i.val)) := by
    refine sum_congr rfl fun K hK => ?_
    rw [← hK0, mem_famA_seedsR] at hK
    rw [hK, hK0]
    rfl
  rw [hBA]
  field_simp

variable {pt Rev}
variable (hpt : Function.Injective pt) (hsmall : ∀ c, pt c < 1024) (hRev : Rev.card + 3 ≤ n)
include hpt hsmall hRev

theorem realLaw_sum (r : C → Digest) : ∑ y, realLaw n pt Rev r y = 1 := by
  have h := sum_pushW_mul (famA n pt Rev r) (fun K (i : Free Rev) => familyEval (List.ofFn K) (pt i.val))
    (fun _ => (1 : ℝ))
  simp only [mul_one, sum_const, nsmul_eq_mul, mul_one] at h
  rw [realLaw, h]
  have hc := famA_card (r := r) (n := n) (R := Rev) hpt hsmall (by omega)
  have hpos : (0 : ℝ) < (famA n pt Rev r).card := by rw [hc]; positivity
  exact div_self hpos.ne'

theorem kwise_hyps (r : C → Digest) (a : Free Rev) :
    (∀ S : Finset (Free Rev × Digest), S.card ≤ 2 →
      mass (realLaw n pt Rev r) (fun y => AllHit y S) = mass (hybLaw n pt Rev r a) (fun y => AllHit y S)) ∧
    (∀ S : Finset (Free Rev × Digest), S.card = 3 →
      mass (realLaw n pt Rev r) (fun y => AllHit y S) ≤ ((Fintype.card Digest : ℝ)⁻¹) ^ 3) ∧
    (∀ S : Finset (Free Rev × Digest), S.card = 3 →
      mass (hybLaw n pt Rev r a) (fun y => AllHit y S) ≤ ((Fintype.card Digest : ℝ)⁻¹) ^ 3) := by
  have hkP := realLaw_kwise (r := r) hpt hsmall hRev
  have hkQ := hybLaw_kwise (r := r) hpt hsmall a hRev
  have hP : ∀ y, 0 ≤ realLaw n pt Rev r y := pushW_nonneg _ _
  have hQ : ∀ y, 0 ≤ hybLaw n pt Rev r a y := pushW_nonneg _ _
  refine ⟨fun S hS => ?_, fun S hS => ?_, fun S hS => ?_⟩
  · rw [mass_allHit_of_kwise _ hP (k := 3) hkP S (by omega), mass_allHit_of_kwise _ hQ (k := 3) hkQ S (by omega)]
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
        2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * kconst D * ∑ K : Fin n → Digest, amLen (tr (seedsR pt Rev K)) := by
  rw [sum_group_real pt Rev (fun r y => prT y (A r) (tr r)), sum_group_hyb pt Rev a (fun r y => prT y (A r) (tr r)),
    sum_group_real pt Rev (fun r _ => amLen (tr r)), mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun r _ => ?_
  obtain ⟨h2, h3P, h3Q⟩ := kwise_hyps hpt hsmall hRev r a
  have hc := comp_mass_le (realLaw n pt Rev r) (hybLaw n pt Rev r a) (((Fintype.card Digest : ℝ)⁻¹) ^ 3) (A r)
    (pushW_nonneg _ _) (pushW_nonneg _ _) (by positivity) h2 h3P h3Q D (tr r) (hD r)
  have hm : ∑ y, realLaw n pt Rev r y * amLen (tr r) = amLen (tr r) := by
    rw [← sum_mul, realLaw_sum hpt hsmall hRev, one_mul]
  rw [hm]
  have hcard : (0 : ℝ) ≤ (famA n pt Rev r).card := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hc hcard]

/-- **Family test, hybrid ≤ real.** -/
theorem family_test_ge (a : Free Rev) {α : Type} (A : (C → Digest) → α → Prop)
    (tr : (C → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : ℕ) (hD : ∀ r, tdepth (tr r) ≤ D) :
    ∑ K : Fin n → Digest, (∑ s, prT (seedsH pt Rev a K s) (A (seedsR pt Rev K)) (tr (seedsR pt Rev K))) / Fintype.card Digest ≤
      ∑ K : Fin n → Digest, prT (seedsY pt Rev K) (A (seedsR pt Rev K)) (tr (seedsR pt Rev K)) +
        2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * kconst D * ∑ K : Fin n → Digest, amLen (tr (seedsR pt Rev K)) := by
  rw [sum_group_real pt Rev (fun r y => prT y (A r) (tr r)), sum_group_hyb pt Rev a (fun r y => prT y (A r) (tr r)),
    sum_group_real pt Rev (fun r _ => amLen (tr r)), mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun r _ => ?_
  obtain ⟨h2, h3P, h3Q⟩ := kwise_hyps hpt hsmall hRev r a
  have hc := comp_mass_le (hybLaw n pt Rev r a) (realLaw n pt Rev r) (((Fintype.card Digest : ℝ)⁻¹) ^ 3) (A r)
    (pushW_nonneg _ _) (pushW_nonneg _ _) (by positivity) (fun S hS => (h2 S hS).symm) h3Q h3P D (tr r) (hD r)
  have hm : ∑ y, realLaw n pt Rev r y * amLen (tr r) = amLen (tr r) := by
    rw [← sum_mul, realLaw_sum hpt hsmall hRev, one_mul]
  rw [hm]
  have hcard : (0 : ℝ) ≤ (famA n pt Rev r).card := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hc hcard]

/-- **All-miss length of a family test against the actual number of tests.** -/
theorem family_amLen_le {α : Type} (tr : (C → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : ℕ)
    (hD : ∀ r, tdepth (tr r) ≤ D) :
    (∑ K : Fin n → Digest, amLen (tr (seedsR pt Rev K))) * (1 - (Fintype.card Digest : ℝ)⁻¹ * D) ≤
      ∑ K : Fin n → Digest, enT (seedsY pt Rev K) (tr (seedsR pt Rev K)) := by
  rw [sum_group_real pt Rev (fun r _ => amLen (tr r)), sum_group_real pt Rev (fun r y => enT y (tr r)), sum_mul]
  refine sum_le_sum fun r _ => ?_
  have hkP := realLaw_kwise (r := r) hpt hsmall hRev
  have hP : ∀ y, 0 ≤ realLaw n pt Rev r y := pushW_nonneg _ _
  have hmass : mass (realLaw n pt Rev r) (fun _ => True) = 1 := by
    unfold mass
    simp only [if_true]
    exact realLaw_sum hpt hsmall hRev r
  have h1 : ∀ p : Free Rev × Digest, mass (realLaw n pt Rev r) (fun y => y p.1 = p.2) ≤ (Fintype.card Digest : ℝ)⁻¹ := by
    intro p
    have := hkP {p.1} (fun _ => p.2) (by simp)
    simp only [Finset.card_singleton, pow_one, Finset.mem_singleton, forall_eq] at this
    rw [this]
  have ha := amLen_le_enT (realLaw n pt Rev r) ((Fintype.card Digest : ℝ)⁻¹) hP (by positivity) h1 (tr r)
  rw [hmass] at ha
  have hm : ∑ y, realLaw n pt Rev r y * amLen (tr r) = amLen (tr r) := by
    rw [← sum_mul, realLaw_sum hpt hsmall hRev, one_mul]
  rw [hm]
  have hcard : (0 : ℝ) ≤ (famA n pt Rev r).card := Nat.cast_nonneg _
  have hdD : ((tdepth (tr r) : ℕ) : ℝ) ≤ D := by exact_mod_cast hD r
  have hal := amLen_nonneg (tr r)
  have hδ : (0 : ℝ) ≤ (Fintype.card Digest : ℝ)⁻¹ := by positivity
  have : amLen (tr r) * (1 - (Fintype.card Digest : ℝ)⁻¹ * D) ≤ ∑ y, realLaw n pt Rev r y * enT y (tr r) := by
    refine le_trans ?_ ha
    exact mul_le_mul_of_nonneg_left (by nlinarith) hal
  calc (famA n pt Rev r).card * amLen (tr r) * (1 - (Fintype.card Digest : ℝ)⁻¹ * D)
      = (famA n pt Rev r).card * (amLen (tr r) * (1 - (Fintype.card Digest : ℝ)⁻¹ * D)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hcard

end FamilyTest
end ClaudeWCT.Arith.SideChannel
