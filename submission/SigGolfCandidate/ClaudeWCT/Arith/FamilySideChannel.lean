import SigGolfCandidate.ClaudeWCT.Arith.Family
import SigGolfCandidate.ClaudeWCT.Arith.SideChannel

/-!
# The side channel of one lower seed family (campaign X1, stage B, item B1)

A leaf family `K : Fin n → Digest` (`n = 17` for the lower WOTS families) is uniform conditioned on its values `r`
at the revealed chains `R`. The unrevealed chains form the coordinate type `Free R`.

* `realLaw`: the unrevealed seeds `K(pt c)` of the family.
* `hybLaw a`: the same, except that the seed of chain `a` is replaced by an independent uniform value.

Both laws have uniform 3-wise marginals as soon as `|R| + 3 ≤ n` (`realLaw_kwise`, `hybLaw_kwise`), so an adaptive
equality-test strategy of depth `g` separates them by at most `2 · 2^-384 · C(2g, 3)` (`family_side_channel`).
For the lower families `n = 17` and `|R| ≤ 14` (at most 14 zero digits per lower leaf).
-/

namespace ClaudeWCT.Arith.SideChannel
open SigGolfCandidate.T3 (Digest)
open Finset

attribute [local instance] Classical.propDecidable

/-! ### Laws pushed forward from uniform finite sets -/

section Push
variable {ι V Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- The law of `f ω` for `ω` uniform on `A`. -/
noncomputable def pushW (A : Finset Ω) (f : Ω → (ι → V)) : (ι → V) → ℝ :=
  fun y => ((A.filter fun ω => f ω = y).card : ℝ) / A.card

theorem pushW_nonneg (A : Finset Ω) (f : Ω → (ι → V)) (y : ι → V) : 0 ≤ pushW A f y := by
  unfold pushW; positivity

theorem mass_pushW (A : Finset Ω) (f : Ω → (ι → V)) (E : (ι → V) → Prop) :
    mass (pushW A f) E = ((A.filter fun ω => E (f ω)).card : ℝ) / A.card := by
  unfold mass pushW
  rw [Finset.sum_congr rfl (fun y _ => show (if E y then ((A.filter fun ω => f ω = y).card : ℝ) / A.card else 0) =
      (if E y then ((A.filter fun ω => f ω = y).card : ℝ) else 0) / A.card by split <;> simp), ← Finset.sum_div]
  congr 1
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ.filter E)
    (fun ω hω => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hω).2⟩)]
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : E y
  · rw [if_pos hy, if_pos hy]
    congr 2
    ext ω
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hω, h⟩; exact ⟨⟨hω, h ▸ hy⟩, h⟩
    · rintro ⟨⟨hω, -⟩, h⟩; exact ⟨hω, h⟩
  · rw [if_neg hy, if_neg hy]

end Push

/-! ### The family laws -/

section Family
variable {C : Type} [Fintype C] [DecidableEq C] (n : Nat) (pt : C → Nat) (R : Finset C) (r : C → Digest)

/-- Unrevealed chains. -/
abbrev Free (R : Finset C) := {c : C // c ∉ R}

/-- Families consistent with the revealed values. -/
noncomputable def famA : Finset (Fin n → Digest) :=
  univ.filter fun K => ∀ c ∈ R, familyEval (List.ofFn K) (pt c) = r c

/-- The unrevealed seeds of a family uniform on `famA`. -/
noncomputable def realLaw : (Free R → Digest) → ℝ :=
  pushW (famA n pt R r) fun K i => familyEval (List.ofFn K) (pt i.val)

/-- The same, with the seed of chain `a` replaced by an independent uniform value. -/
noncomputable def hybLaw (a : Free R) : (Free R → Digest) → ℝ :=
  pushW (famA n pt R r ×ˢ (univ : Finset Digest)) fun Ks i =>
    if i = a then Ks.2 else familyEval (List.ofFn Ks.1) (pt i.val)

variable {n pt R r}

/-- Families consistent with `R ↦ r` and with `T ↦ v` on unrevealed chains: `2^(128 (n - |R| - |T|))`. -/
theorem famA_card_extend (hpt : Function.Injective pt) (hsmall : ∀ c, pt c < 1024) (T : Finset (Free R))
    (v : Free R → Digest) (h : R.card + T.card ≤ n) :
    ((famA n pt R r).filter fun K => ∀ i ∈ T, familyEval (List.ofFn K) (pt i.val) = v i).card =
      2 ^ (128 * (n - (R.card + T.card))) := by
  let ι' := {c // c ∈ R} ⊕ {i // i ∈ T}
  let pts : ι' → Nat := fun j => Sum.elim (fun c => pt c.val) (fun i => pt i.val.val) j
  let w : ι' → Digest := fun j => Sum.elim (fun c => r c.val) (fun i => v i.val) j
  have hcard : Fintype.card ι' = R.card + T.card := by
    simp [ι', Fintype.card_sum, Fintype.card_coe]
  have hinj : Function.Injective pts := by
    rintro (⟨c, hc⟩ | ⟨i, hi⟩) (⟨c', hc'⟩ | ⟨i', hi'⟩) he
    · exact congrArg Sum.inl (Subtype.ext (hpt he))
    · exact absurd (hpt he ▸ hc) i'.property
    · exact absurd (hpt he ▸ hc') i.property
    · exact congrArg Sum.inr (Subtype.ext (Subtype.ext (hpt he)))
  have key := familyEval_fiber_card' (n := n) (hcard ▸ h) pts hinj
    (fun j => by rcases j with ⟨c, _⟩ | ⟨i, _⟩ <;> exact hsmall _) w
  rw [hcard] at key
  rw [← key]
  congr 1
  ext K
  simp only [famA, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hR, hT⟩ (⟨c, hc⟩ | ⟨i, hi⟩)
    · exact hR c hc
    · exact hT i hi
  · intro hK
    exact ⟨fun c hc => hK (.inl ⟨c, hc⟩), fun i hi => hK (.inr ⟨i, hi⟩)⟩

theorem famA_card (hpt : Function.Injective pt) (hsmall : ∀ c, pt c < 1024) (h : R.card ≤ n) :
    (famA n pt R r).card = 2 ^ (128 * (n - R.card)) := by
  have := famA_card_extend (r := r) hpt hsmall (∅ : Finset (Free R)) (fun _ => 0) (by simpa using h)
  simpa using this

theorem card_digest' : Fintype.card Digest = 2 ^ 128 := by simp

theorem pow_ratio (a t : Nat) (ht : t ≤ a) :
    (2 : ℝ) ^ (128 * (a - t)) / (2 : ℝ) ^ (128 * a) = ((2 : ℝ) ^ 128)⁻¹ ^ t := by
  have e : (2 : ℝ) ^ (128 * a) = 2 ^ (128 * (a - t)) * ((2 : ℝ) ^ 128) ^ t := by
    rw [← pow_mul, ← pow_add]
    congr 1
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [e, inv_pow]
  field_simp

theorem card_digest_real : (Fintype.card Digest : ℝ) = (2 : ℝ) ^ 128 := by
  have : Fintype.card Digest = 2 ^ 128 := by simp
  exact_mod_cast this

theorem realLaw_kwise (hpt : Function.Injective pt) (hsmall : ∀ c, pt c < 1024) (h : R.card + 3 ≤ n) :
    KWise (realLaw n pt R r) 3 := by
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
    (h : R.card + 3 ≤ n) : KWise (hybLaw n pt R r a) 3 := by
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

/-- **Family side channel.** For a leaf family with `|R| + 3 ≤ n` revealed chains, an adaptive equality-test
strategy of depth `g` on the unrevealed seeds cannot tell the family from the family with an independent seed
for chain `a`, except with advantage `2 · 2^-384 · C(2g, 3)`. -/
theorem family_side_channel (hpt : Function.Injective pt) (hsmall : ∀ c, pt c < 1024) (a : Free R)
    (h : R.card + 3 ≤ n) {α : Type} (T : Tree (Free R) Digest α) (A : α → Prop) :
    mass (realLaw n pt R r) (fun y => A (T.run y)) ≤ mass (hybLaw n pt R r a) (fun y => A (T.run y)) +
      2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ((2 * T.depth).choose 3 : ℝ) := by
  have := tree_mass_le_of_kwise (realLaw n pt R r) (hybLaw n pt R r a) (pushW_nonneg _ _) (pushW_nonneg _ _)
    (realLaw_kwise hpt hsmall h) (hybLaw_kwise hpt hsmall a h) T A
  exact this

/-- `family_side_channel` charged to the all-miss path: `ℓ` tests when nothing hits, depth `≤ D`. -/
theorem family_side_channel_am (hpt : Function.Injective pt) (hsmall : ∀ c, pt c < 1024) (a : Free R)
    (h : R.card + 3 ≤ n) {α : Type} (T : Tree (Free R) Digest α) (D : Nat) (hD : T.depth ≤ D) (A : α → Prop) :
    mass (realLaw n pt R r) (fun y => A (T.run y)) ≤ mass (hybLaw n pt R r a) (fun y => A (T.run y)) +
      2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 *
        ((T.amLen.choose 3 : ℝ) + T.amLen * ((T.amLen + 2 * D).choose 2 : ℝ)) :=
  tree_mass_le_am_of_kwise (realLaw n pt R r) (hybLaw n pt R r a) (pushW_nonneg _ _) (pushW_nonneg _ _)
    (realLaw_kwise hpt hsmall h) (hybLaw_kwise hpt hsmall a h) T D hD A

end Family
end ClaudeWCT.Arith.SideChannel
