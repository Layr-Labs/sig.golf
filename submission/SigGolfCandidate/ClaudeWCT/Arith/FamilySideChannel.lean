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

/-!
# Adjacent-leaf sharing research (not wired into the submitted scheme)

Two B4 leaves reveal at most five step-zero seeds each. Assign their 86
chains distinct points 1..86 and use a common 13-coefficient family. The
union of disclosures has at most ten elements, so the existing 3-wise
posterior and equality-test bounds apply to the JOINT family, not merely
separately to each leaf. This does not prove a new full security game:
its table/router and machine refinements still require implementation.
-/
namespace ClaudeWCT.Arith.SideChannel.AdjacentLeafResearch
open SigGolfCandidate.T3 (Digest)

abbrev JointChain := Fin 2 × Fin 43

def jointPoint (c : JointChain) : Nat := 43 * c.1.val + c.2.val + 1

theorem jointPoint_small (c : JointChain) : jointPoint c < 1024 := by
  have h0 := c.1.isLt
  have h1 := c.2.isLt
  unfold jointPoint
  omega

theorem jointPoint_injective : Function.Injective jointPoint := by
  intro a b h
  have ha := a.2.isLt
  have hb := b.2.isLt
  have h0 : a.1.val = b.1.val := by unfold jointPoint at h; omega
  have h1 : a.2.val = b.2.val := by unfold jointPoint at h; omega
  exact Prod.ext (Fin.ext h0) (Fin.ext h1)

theorem joint_disclosure_bound (R0 R1 : Finset JointChain)
    (h0 : R0.card ≤ 5) (h1 : R1.card ≤ 5) :
    (R0 ∪ R1).card + 3 ≤ 13 := by
  have := Finset.card_union_le R0 R1
  omega

theorem joint_realLaw_kwise (R0 R1 : Finset JointChain)
    (h0 : R0.card ≤ 5) (h1 : R1.card ≤ 5) (r : JointChain → Digest) :
    KWise (realLaw 13 jointPoint (R0 ∪ R1) r) 3 :=
  realLaw_kwise jointPoint_injective jointPoint_small (joint_disclosure_bound R0 R1 h0 h1)

theorem joint_hybLaw_kwise (R0 R1 : Finset JointChain)
    (h0 : R0.card ≤ 5) (h1 : R1.card ≤ 5) (r : JointChain → Digest)
    (a : Free (R0 ∪ R1)) :
    KWise (hybLaw 13 jointPoint (R0 ∪ R1) r a) 3 :=
  hybLaw_kwise jointPoint_injective jointPoint_small a (joint_disclosure_bound R0 R1 h0 h1)

theorem joint_side_channel (R0 R1 : Finset JointChain)
    (h0 : R0.card ≤ 5) (h1 : R1.card ≤ 5) (r : JointChain → Digest)
    (a : Free (R0 ∪ R1)) {α : Type} (T : Tree (Free (R0 ∪ R1)) Digest α) (A : α → Prop) :
    mass (realLaw 13 jointPoint (R0 ∪ R1) r) (fun y => A (T.run y)) ≤
      mass (hybLaw 13 jointPoint (R0 ∪ R1) r a) (fun y => A (T.run y)) +
      2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ((2 * T.depth).choose 3 : ℝ) :=
  family_side_channel jointPoint_injective jointPoint_small a (joint_disclosure_bound R0 R1 h0 h1) T A

/-- 128,64,64 leaves: paired 14-coefficient families save 128 private hashes. -/
theorem fourteen_coefficient_pair_savings :
    (128 + 64 + 64) * 4 - ((128 + 64 + 64) / 2) * 7 = 128 := by decide

/-- With 13 coefficients, packing across an even number of families uses
832 private pairs rather than 1024. Padding each family to 14 loses 64. -/
theorem thirteen_coefficient_packed_savings :
    (128 + 64 + 64) * 4 - ((128 + 64 + 64) / 2) * 13 / 2 = 192 := by decide

theorem savings_exceed_floor_ten_threshold : 122 ≤ 128 ∧ 122 ≤ 192 := by decide

#print axioms joint_side_channel
#print axioms thirteen_coefficient_packed_savings

/-- General grouped-family candidate: at most five disclosures per leaf. -/
abbrev GroupChain (g : Nat) := Fin g × Fin 43

def groupPoint {g : Nat} (c : GroupChain g) : Nat := 43 * c.1.val + c.2.val + 1

theorem groupPoint_injective (g : Nat) : Function.Injective (@groupPoint g) := by
  intro a b h
  have ha := a.2.isLt
  have hb := b.2.isLt
  have h0 : a.1.val = b.1.val := by unfold groupPoint at h; omega
  have h1 : a.2.val = b.2.val := by unfold groupPoint at h; omega
  exact Prod.ext (Fin.ext h0) (Fin.ext h1)

theorem groupPoint_small {g : Nat} (hg : g ≤ 23) (c : GroupChain g) :
    groupPoint c < 1024 := by
  have h0 := c.1.isLt
  have h1 := c.2.isLt
  unfold groupPoint
  omega

/-- The actual representation also reserves 58 chain addresses per leaf;
use stride 58 rather than 43 when replacing the full security router. -/
def routedGroupPoint {g : Nat} (c : Fin g × Fin 58) : Nat :=
  58 * c.1.val + c.2.val + 1

theorem routedGroupPoint_small {g : Nat} (hg : g ≤ 17) (c : Fin g × Fin 58) :
    routedGroupPoint c < 1024 := by
  have h0 := c.1.isLt
  have h1 := c.2.isLt
  unfold routedGroupPoint
  omega

/-- Stride 43 is NOT injective on the full Fin-58 security address space. -/
theorem stride43_router_collision :
    groupPoint ((0 : Fin 2), (0 : Fin 43)) = 1 ∧
    43 * (0 : Nat) + 43 + 1 = 43 * (1 : Nat) + 0 + 1 := by decide

/-- The biUnion bounds joint disclosures, including every sibling's set. -/
theorem group_disclosure_bound (g : Nat) (R : Fin g → Finset (GroupChain g))
    (hR : ∀ i, (R i).card ≤ 5) :
    (Finset.univ.biUnion R).card + 3 ≤ 5 * g + 3 := by
  have hc := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin g)) R 5 (by
    intro i _; exact hR i)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  omega

theorem group_side_channel (g : Nat) (hg : g ≤ 23)
    (R : Fin g → Finset (GroupChain g)) (hR : ∀ i, (R i).card ≤ 5)
    (r : GroupChain g → Digest) (a : Free (Finset.univ.biUnion R))
    {α : Type} (T : Tree (Free (Finset.univ.biUnion R)) Digest α) (A : α → Prop) :
    mass (realLaw (5*g+3) groupPoint (Finset.univ.biUnion R) r) (fun y => A (T.run y)) ≤
      mass (hybLaw (5*g+3) groupPoint (Finset.univ.biUnion R) r a) (fun y => A (T.run y)) +
      2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ((2 * T.depth).choose 3 : ℝ) :=
  family_side_channel (groupPoint_injective g) (groupPoint_small hg) a
    (group_disclosure_bound g R hR) T A

/-- GROUP16 has 83 coefficients, 688 real points, saves 360 with packed
halves or 352 with 84-coefficient padding; these are HASH counts only. -/
theorem group16_savings :
    5*16+3 = 83 ∧ 43*16 = 688 ∧
    1024 - (256/16)*83/2 = 360 ∧ 1024 - (256/16)*42 = 352 := by decide

/-- The inherited lower COEF/spill separation is 288 bytes. 13/14
coefficients fit, but GROUP4 and GROUP16 do not. -/
theorem inherited_buffer_boundary :
    16*14 ≤ 288 ∧ ¬ (16*(5*4+3) ≤ 288) ∧ ¬ (16*83 ≤ 288) := by decide

/-- The full canonical security coefficient index is Fin 58: GROUP16
cannot be installed merely by changing famCount. -/
theorem inherited_coefficient_index_boundary : 5*8+3 < 58 ∧ ¬ (5*16+3 < 58) := by decide

/-- Per-target seed-test accounting must be regrouped too: at most 86
rather than the present 54 chains count a single lower-group test. -/
theorem regrouped_test_multiplicity : 54 < 2*43 ∧ 2*43 = 86 := by decide

/-- Extra conservative Horner bound from replacing 8 coefficients by 13:
159 cycles/coefficient * 5 * 43 chains * 256 leaves = 8,751,360.
This is NOT an accepting-run profile or a termination certificate. -/
theorem pair_horner_bound_delta :
    (6 + (14*10+1) + 12) * (13-8) * 43 * 256 = 8751360 := by decide

#print axioms group_side_channel
#print axioms inherited_buffer_boundary

/-!
Implementation map / remaining obligations:
* WCT9.Core.lowerCoefs, lowerCoefOrdinal, lowerFamilySeed, buildTreeP:
  generate once per group and reuse; lowering privatePair counts alone is unsound.
* WCT9.Correctness.lowerCoef/famOrdinal and Secc.CanonGraph.leafFamily:
  map coefficients to grouped leaves. `famOrdinal_inj` is leaf-injective today.
* LargeResidualRouter.wsplit/Seeds instance: group identity and injective
  stride-58 address points, top/FTS unchanged. CanonGraph has Fin58 coefficients.
* LargeCouplingQuery.DiscLower/FamOK and LargeCouplingTable.discLower_steps:
  union the fixed reference-zero sets of all siblings.
* WotsLeafCore/Defs and WotsLeafSum.sum_NL_le: grouping changes the frozen
  leaf decomposition and the seed-test allocation factor 54 -> 86 for pairs.
  Existing final security pricing MUST NOT be blindly transported.
* Machine.Sign.PackedLeaf.coef_phase and LowerRuns.lower_seed: preserve the
  shared coefficient buffer at sibling entry, return carry across 13-coefficient
  groups, update ordinals/point mapping and full-cycle/termination bounds.
* Producer floor 10 and all numerical/finite-machine acceptance proofs must
  then be installed together; these declarations do none of that wiring.
-/


/-- Full reserved chain-address routing for an adjacent pair. The family
is leaf/2 and the point encodes leaf%2 and all 58 possible chain addresses. -/
def pairRoute (leaf : Fin 4096) (chain : Fin 58) : Nat × Nat :=
  (leaf.val / 2, 58 * (leaf.val % 2) + chain.val + 1)

theorem pairRoute_injective (leaf leaf' : Fin 4096) (chain chain' : Fin 58)
    (h : pairRoute leaf chain = pairRoute leaf' chain') : leaf = leaf' ∧ chain = chain' := by
  have hf := congrArg Prod.fst h
  have hp := congrArg Prod.snd h
  have hc := chain.isLt
  have hc' := chain'.isLt
  have hm := Nat.mod_lt leaf.val (by decide : 0 < 2)
  have hm' := Nat.mod_lt leaf'.val (by decide : 0 < 2)
  simp only [pairRoute] at hf hp
  constructor
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega

theorem pairRoute_point_small (leaf : Fin 4096) (chain : Fin 58) :
    (pairRoute leaf chain).2 ≤ 116 ∧ (pairRoute leaf chain).2 < 1024 := by
  have hc := chain.isLt
  have hm := Nat.mod_lt leaf.val (by decide : 0 < 2)
  simp only [pairRoute]
  omega

/-- Groups of 13 coefficients can use one continuous packed-secret stream.
Each group uses 6 or 7 fresh pair queries depending on its parity, and a
complete even-length stream costs 13 pairs per two groups. -/
def coefficientOrdinal (group j : Nat) : Nat := 13*group+j

theorem coefficientOrdinal_injective {group group' j j' : Nat}
    (hj : j < 13) (hj' : j' < 13)
    (h : coefficientOrdinal group j = coefficientOrdinal group' j') :
    group = group' ∧ j = j' := by
  unfold coefficientOrdinal at h
  constructor <;> omega

theorem paired_coefficient_hash_counts (group : Nat) :
    ((List.range 13).map fun j => if coefficientOrdinal (2*group) j % 2 = 0 then 1 else 0).sum = 7 ∧
    ((List.range 13).map fun j => if coefficientOrdinal (2*group+1) j % 2 = 0 then 1 else 0).sum = 6 := by
  have he (j : Nat) : coefficientOrdinal (2*group) j % 2 = j % 2 := by
    unfold coefficientOrdinal
    omega
  have ho (j : Nat) : coefficientOrdinal (2*group+1) j % 2 = (j+1) % 2 := by
    unfold coefficientOrdinal
    omega
  simp only [he, ho]
  decide

#print axioms pairRoute_injective
#print axioms paired_coefficient_hash_counts

end ClaudeWCT.Arith.SideChannel.AdjacentLeafResearch
