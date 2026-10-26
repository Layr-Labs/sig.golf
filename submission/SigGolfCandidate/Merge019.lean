import VCVio.OracleComp.ProbComp
import SigGolfCandidate.Merge017
import SigGolfCandidate.Merge018

-- ==== merged from ClaudeWCT_Arith_FamilySideChannel ====
section

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


end ClaudeWCT.Arith.SideChannel.AdjacentLeafResearch
end
-- ==== merged from ClaudeWCT_Arith_SideChannelComp ====
section

/-!
# Side channel of test programs with coins (campaign X1, stage B, item B1')

`tree_mass_le` for oracle programs `OracleComp (TSpec ι V) α` that interleave uniform coins (`unifSpec`) and
equality tests on a hidden vector `y : ι → V`. The semantics are given by structural recursion
(`OracleComp.construct`):

* `prT y A p`: probability that `p`, run against `y` (coins uniform), returns a result in `A`;
* `tdepth p`: the largest number of tests on a path;
* `amLen p`: expected number of tests when every test answers "miss" (the all-miss run);
* `enT y p`: expected number of tests in the run against `y`.

Main results (laws `P`, `Q` with uniform 3-wise marginals, `δ = |V|^-3`, `δ₁ = |V|^-1`, `tdepth p ≤ D`):

* `comp_mass_le`: `P(A) ≤ Q(A) + 2 δ K(D) · amLen p` with `K(D) = D²` (one-sided Bonferroni, `comp_ctx_le_am_one`:
  `δ C(2D, 2) ≤ 2 δ D²`; it was `C(3D, 2) + C(D, 2)`);
* `amLen_le_enT`: `amLen p · (1 - δ₁ D) ≤ E_P[number of tests]`.

So the separation is charged to the expected number of tests actually made, which is summable over independent
families (one per lower WOTS leaf).
-/

namespace ClaudeWCT.Arith.SideChannel

open OracleComp OracleSpec Finset

variable {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- Programs with uniform coins and equality tests on `y : ι → V`. -/
abbrev TSpec (ι V : Type) : OracleSpec (ℕ ⊕ (ι × V)) := unifSpec + ((ι × V) →ₒ Bool)

section Semantics
variable {α : Type}

/-- Probability that `p`, run against `y`, returns a result in `A`. -/
noncomputable def prT (y : ι → V) (A : α → Prop) : OracleComp (TSpec ι V) α → ℝ :=
  OracleComp.construct (C := fun _ => ℝ) (fun a => by classical exact if A a then 1 else 0)
    (fun t _ r => match t, r with
      | .inl n, r => (∑ u : Fin (n + 1), r u) / (n + 1)
      | .inr p, r => by classical exact r (decide (y p.1 = p.2)))

/-- Largest number of tests on a path. -/
noncomputable def tdepth : OracleComp (TSpec ι V) α → ℕ :=
  OracleComp.construct (C := fun _ => ℕ) (fun _ => 0)
    (fun t _ r => match t, r with
      | .inl _, r => univ.sup r
      | .inr _, r => max (r true) (r false) + 1)

/-- Expected number of tests when every test answers "miss". -/
noncomputable def amLen : OracleComp (TSpec ι V) α → ℝ :=
  OracleComp.construct (C := fun _ => ℝ) (fun _ => 0)
    (fun t _ r => match t, r with
      | .inl n, r => (∑ u : Fin (n + 1), r u) / (n + 1)
      | .inr _, r => r false + 1)

/-- Expected number of tests in the run against `y`. -/
noncomputable def enT (y : ι → V) : OracleComp (TSpec ι V) α → ℝ :=
  OracleComp.construct (C := fun _ => ℝ) (fun _ => 0)
    (fun t _ r => match t, r with
      | .inl n, r => (∑ u : Fin (n + 1), r u) / (n + 1)
      | .inr p, r => by classical exact r (decide (y p.1 = p.2)) + 1)

/-- Query a coin. -/
def coinQ (n : ℕ) : OracleComp (TSpec ι V) (Fin (n + 1)) := liftM ((TSpec ι V).query (.inl n))
/-- Query a test. -/
def testQ (p : ι × V) : OracleComp (TSpec ι V) Bool := liftM ((TSpec ι V).query (.inr p))

theorem prT_pure (y : ι → V) (A : α → Prop) (a : α) :
    prT y A (pure a : OracleComp (TSpec ι V) α) = by classical exact if A a then 1 else 0 := rfl
theorem prT_coin (y : ι → V) (A : α → Prop) (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    prT y A (coinQ n >>= k) = (∑ u : Fin (n + 1), prT y A (k u)) / (n + 1) := rfl
theorem prT_test (y : ι → V) (A : α → Prop) (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    prT y A (testQ p >>= k) = by classical exact prT y A (k (decide (y p.1 = p.2))) := rfl
theorem tdepth_pure (a : α) : tdepth (pure a : OracleComp (TSpec ι V) α) = 0 := rfl
theorem tdepth_coin (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    tdepth (coinQ n >>= k) = univ.sup fun u => tdepth (k u) := rfl
theorem tdepth_test (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    tdepth (testQ p >>= k) = max (tdepth (k true)) (tdepth (k false)) + 1 := rfl
theorem amLen_pure (a : α) : amLen (pure a : OracleComp (TSpec ι V) α) = 0 := rfl
theorem amLen_coin (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    amLen (coinQ n >>= k) = (∑ u : Fin (n + 1), amLen (k u)) / (n + 1) := rfl
theorem amLen_test (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    amLen (testQ p >>= k) = amLen (k false) + 1 := rfl
theorem enT_pure (y : ι → V) (a : α) : enT y (pure a : OracleComp (TSpec ι V) α) = 0 := rfl
theorem enT_coin (y : ι → V) (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    enT y (coinQ n >>= k) = (∑ u : Fin (n + 1), enT y (k u)) / (n + 1) := rfl
theorem enT_test (y : ι → V) (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    enT y (testQ p >>= k) = by classical exact enT y (k (decide (y p.1 = p.2))) + 1 := rfl

/-- Induction principle splitting queries into coins and tests. -/
theorem tinduction {C : OracleComp (TSpec ι V) α → Prop} (pure : ∀ a, C (pure a))
    (coin : ∀ n (k : Fin (n + 1) → OracleComp (TSpec ι V) α), (∀ u, C (k u)) → C (coinQ n >>= k))
    (test : ∀ p (k : Bool → OracleComp (TSpec ι V) α), (∀ b, C (k b)) → C (testQ p >>= k))
    (oa : OracleComp (TSpec ι V) α) : C oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact pure a
  | query_bind t k ih =>
      rcases t with n | p
      · exact coin n k ih
      · exact test p k ih

theorem prT_nonneg (y : ι → V) (A : α → Prop) (oa : OracleComp (TSpec ι V) α) : 0 ≤ prT y A oa := by
  induction oa using tinduction with
  | pure a => rw [prT_pure]; split <;> norm_num
  | coin n k ih => rw [prT_coin]; exact div_nonneg (sum_nonneg fun u _ => ih u) (by positivity)
  | test p k ih => rw [prT_test]; exact ih _

theorem prT_le_one (y : ι → V) (A : α → Prop) (oa : OracleComp (TSpec ι V) α) : prT y A oa ≤ 1 := by
  induction oa using tinduction with
  | pure a => rw [prT_pure]; split <;> norm_num
  | coin n k ih =>
      rw [prT_coin, div_le_one (by positivity)]
      calc (∑ u : Fin (n + 1), prT y A (k u)) ≤ ∑ _u : Fin (n + 1), (1 : ℝ) := sum_le_sum fun u _ => ih u
        _ = n + 1 := by simp
  | test p k ih => rw [prT_test]; exact ih _

theorem amLen_nonneg (oa : OracleComp (TSpec ι V) α) : 0 ≤ amLen oa := by
  induction oa using tinduction with
  | pure a => rw [amLen_pure]
  | coin n k ih => rw [amLen_coin]; exact div_nonneg (sum_nonneg fun u _ => ih u) (by positivity)
  | test p k ih => rw [amLen_test]; linarith [ih false]

theorem amLen_le_tdepth (oa : OracleComp (TSpec ι V) α) : amLen oa ≤ tdepth oa := by
  induction oa using tinduction with
  | pure a => rw [amLen_pure, tdepth_pure]; simp
  | coin n k ih =>
      rw [amLen_coin, tdepth_coin, div_le_iff₀ (by positivity)]
      calc (∑ u : Fin (n + 1), amLen (k u)) ≤ ∑ _u : Fin (n + 1), ((univ.sup fun u => tdepth (k u) : ℕ) : ℝ) :=
            sum_le_sum fun u _ => (ih u).trans (by exact_mod_cast le_sup (f := fun u => tdepth (k u)) (mem_univ u))
        _ = _ := by simp; ring
  | test p k ih =>
      rw [amLen_test, tdepth_test]
      have h1 := ih false
      have h2 : ((tdepth (k false) + 1 : ℕ) : ℝ) ≤ ((max (tdepth (k true)) (tdepth (k false)) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show tdepth (k false) + 1 ≤ max (tdepth (k true)) (tdepth (k false)) + 1 by omega)
      push_cast at h2 ⊢
      linarith

end Semantics

/-- `C(a, 2) + C(b, 2) ≤ C(a + b, 2)`. -/
theorem choose_two_add_le (a b : ℕ) : a.choose 2 + b.choose 2 ≤ (a + b).choose 2 := by
  have e : ∀ n : ℕ, (n + 1).choose 2 = n + n.choose 2 := fun n => by
    have := Nat.choose_succ_succ' n 1
    simpa [Nat.choose_one_right] using this
  induction b with
  | zero => simp
  | succ b ih =>
      rw [← Nat.add_assoc, e, e]
      omega

/-- The constant of the all-miss bound (r3-lean-seedfam: `D²`, from `δ C(2D, 2) ≤ 2 δ D²`; was
`C(3D, 2) + C(D, 2)`). -/
def kconst (D : ℕ) : ℕ := D * D

theorem choose_two_double_le (D : ℕ) : ((2 * D).choose 2 : ℝ) ≤ 2 * (kconst D : ℝ) := by
  have h : (2 * D).choose 2 ≤ 2 * kconst D := by
    unfold kconst
    rw [Nat.choose_two_right]
    have := Nat.div_le_self (2 * D * (2 * D - 1)) 2
    have h4 : 2 * D * (2 * D - 1) ≤ 2 * D * (2 * D) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have : 2 * D * (2 * D - 1) / 2 ≤ 2 * D * (2 * D) / 2 := Nat.div_le_div_right h4
    have e : 2 * D * (2 * D) / 2 = 2 * (D * D) := by
      rw [show 2 * D * (2 * D) = 2 * (2 * (D * D)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    omega
  exact_mod_cast h

/-! ### Mass of a context times the success probability -/

section Bound
variable (P Q : (ι → V) → ℝ) (δ : ℝ)
variable {α : Type} (A : α → Prop)

/-- `Σ_y R y · 1{Ctx y H M} · prT y A p`. -/
noncomputable def cmass (R : (ι → V) → ℝ) (H M : Finset (ι × V)) (oa : OracleComp (TSpec ι V) α) : ℝ :=
  by classical exact ∑ y, (if Ctx y H M then R y else 0) * prT y A oa

theorem cmass_pure (R : (ι → V) → ℝ) (H M : Finset (ι × V)) (a : α) :
    cmass A R H M (pure a) = by classical exact if A a then mass R (fun y => Ctx y H M) else 0 := by
  classical
  unfold cmass mass
  split_ifs with ha
  · refine sum_congr rfl fun y _ => ?_
    rw [prT_pure, if_pos ha, mul_one]
  · refine sum_eq_zero fun y _ => ?_
    rw [prT_pure, if_neg ha, mul_zero]

theorem cmass_coin (R : (ι → V) → ℝ) (H M : Finset (ι × V)) (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    cmass A R H M (coinQ n >>= k) = (∑ u : Fin (n + 1), cmass A R H M (k u)) / (n + 1) := by
  classical
  unfold cmass
  simp only [prT_coin, mul_div_assoc', ← sum_div, mul_sum]
  rw [sum_comm]

theorem cmass_test (R : (ι → V) → ℝ) (H M : Finset (ι × V)) (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    cmass A R H M (testQ p >>= k) = cmass A R (insert p H) M (k true) + cmass A R H (insert p M) (k false) := by
  classical
  unfold cmass
  rw [← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [prT_test]
  by_cases hy : y p.1 = p.2
  · have h1 : Ctx y (insert p H) M ↔ Ctx y H M := by rw [ctx_insert_hit]; simp [hy]
    have h2 : ¬Ctx y H (insert p M) := by rw [ctx_insert_miss]; simp [hy]
    simp only [hy, decide_true, h1, h2, if_false, zero_mul, add_zero]
  · have h1 : ¬Ctx y (insert p H) M := by rw [ctx_insert_hit]; simp [hy]
    have h2 : Ctx y H (insert p M) ↔ Ctx y H M := by rw [ctx_insert_miss]; simp [hy]
    simp only [hy, decide_false, h1, h2, if_false, zero_mul, zero_add]

theorem cmass_nonneg (R : (ι → V) → ℝ) (hR : ∀ y, 0 ≤ R y) (H M : Finset (ι × V)) (oa : OracleComp (TSpec ι V) α) :
    0 ≤ cmass A R H M oa := by
  classical
  unfold cmass
  exact sum_nonneg fun y _ => mul_nonneg (by split <;> simp [hR y]) (prT_nonneg y A oa)

theorem cmass_le_mass (R : (ι → V) → ℝ) (hR : ∀ y, 0 ≤ R y) (H M : Finset (ι × V)) (oa : OracleComp (TSpec ι V) α) :
    cmass A R H M oa ≤ mass R (fun y => Ctx y H M) := by
  classical
  unfold cmass mass
  refine sum_le_sum fun y _ => ?_
  have h1 := prT_le_one y A oa
  have h0 := prT_nonneg y A oa
  split_ifs
  · nlinarith [hR y]
  · simp

theorem cmass_eq_zero (R : (ι → V) → ℝ) (H M : Finset (ι × V)) (oa : OracleComp (TSpec ι V) α)
    (h : ∀ y, ¬Ctx y H M) : cmass A R H M oa = 0 := by
  classical
  unfold cmass
  exact sum_eq_zero fun y _ => by rw [if_neg (h y), zero_mul]

variable (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y) (hδ : 0 ≤ δ)
  (h2 : ∀ S : Finset (ι × V), S.card ≤ 2 → mass P (fun y => AllHit y S) = mass Q (fun y => AllHit y S))
  (h3P : ∀ S : Finset (ι × V), S.card = 3 → mass P (fun y => AllHit y S) ≤ δ)
  (h3Q : ∀ S : Finset (ι × V), S.card = 3 → mass Q (fun y => AllHit y S) ≤ δ)
include hP hQ hδ h2 h3P h3Q

/-- Depth bound for every context: `2 δ C(|M| + 2 · tdepth, 3 - |H|)`. -/
theorem comp_ctx_le : ∀ (oa : OracleComp (TSpec ι V) α) (H M : Finset (ι × V)),
    cmass A P H M oa ≤ cmass A Q H M oa + 2 * δ * ((M.card + 2 * tdepth oa).choose (3 - H.card) : ℝ) := by
  classical
  have big : ∀ (oa : OracleComp (TSpec ι V) α) (H M : Finset (ι × V)), 3 ≤ H.card →
      cmass A P H M oa ≤ cmass A Q H M oa + 2 * δ * ((M.card + 2 * tdepth oa).choose (3 - H.card) : ℝ) := by
    intro oa H M hH
    obtain ⟨S, hSH, hS⟩ := Finset.exists_subset_card_eq hH
    have hle : cmass A P H M oa ≤ δ :=
      (cmass_le_mass A P hP H M oa).trans ((mass_mono P hP fun y hy p hp => hy.1 p (hSH hp)).trans (h3P S hS))
    have hq := cmass_nonneg A Q hQ H M oa
    rw [show 3 - H.card = 0 by omega, Nat.choose_zero_right, Nat.cast_one, mul_one]
    linarith
  intro oa
  induction oa using tinduction with
  | pure a =>
      intro H M
      by_cases hH : 3 ≤ H.card
      · exact big _ H M hH
      rw [cmass_pure, cmass_pure, tdepth_pure]
      split_ifs with ha
      · simpa using ctx_mass_le P Q δ hP hQ hδ h2 h3P h3Q H M (by omega)
      · have : 0 ≤ 2 * δ * ((M.card + 2 * 0).choose (3 - H.card) : ℝ) := by positivity
        linarith
  | coin n k ih =>
      intro H M
      rw [cmass_coin, cmass_coin, tdepth_coin]
      have hmono : ∀ u, ((M.card + 2 * tdepth (k u)).choose (3 - H.card) : ℝ) ≤
          ((M.card + 2 * univ.sup fun u => tdepth (k u)).choose (3 - H.card) : ℝ) := fun u => by
        exact_mod_cast Nat.choose_le_choose _ (by
          have := le_sup (f := fun u => tdepth (k u)) (mem_univ u); omega)
      rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
      calc (∑ u : Fin (n + 1), cmass A P H M (k u))
          ≤ ∑ u : Fin (n + 1), (cmass A Q H M (k u) + 2 * δ *
              ((M.card + 2 * univ.sup fun u => tdepth (k u)).choose (3 - H.card) : ℝ)) :=
            sum_le_sum fun u _ => (ih u H M).trans (by nlinarith [hmono u])
        _ = _ := by rw [sum_add_distrib]; simp; ring
  | test p k ih =>
      intro H M
      by_cases hH : 3 ≤ H.card
      · exact big _ H M hH
      rw [cmass_test, cmass_test, tdepth_test]
      set d := max (tdepth (k true)) (tdepth (k false))
      have mono : ∀ {a b : ℕ} (c : ℕ), a ≤ b → ((a.choose c : ℕ) : ℝ) ≤ (b.choose c : ℝ) :=
        fun c hab => by exact_mod_cast Nat.choose_le_choose c hab
      have hδ2 : 0 ≤ 2 * δ := by linarith
      have qt := cmass_nonneg A Q hQ (insert p H) M (k true)
      have qf := cmass_nonneg A Q hQ H (insert p M) (k false)
      by_cases hpH : p ∈ H
      · rw [Finset.insert_eq_of_mem hpH] at qt ⊢
        rw [cmass_eq_zero A P H (insert p M) (k false) (fun y hy =>
          ((ctx_insert_miss y H M p).mp hy).2 (hy.1 p hpH))]
        have ht := ih true H M
        have hm := mono (3 - H.card) (show M.card + 2 * tdepth (k true) ≤ M.card + 2 * (d + 1) by omega)
        nlinarith [mul_le_mul_of_nonneg_left hm hδ2]
      by_cases hpM : p ∈ M
      · rw [Finset.insert_eq_of_mem hpM] at qf ⊢
        rw [cmass_eq_zero A P (insert p H) M (k true) (fun y hy =>
          (hy.2 p hpM) ((ctx_insert_hit y H M p).mp hy).2)]
        have hf := ih false H M
        have hm := mono (3 - H.card) (show M.card + 2 * tdepth (k false) ≤ M.card + 2 * (d + 1) by omega)
        nlinarith [mul_le_mul_of_nonneg_left hm hδ2]
      · have ht := ih true (insert p H) M
        have hf := ih false H (insert p M)
        rw [Finset.card_insert_of_notMem hpH] at ht
        rw [Finset.card_insert_of_notMem hpM] at hf
        obtain ⟨j, hj⟩ : ∃ j, 3 - H.card = j + 1 := ⟨3 - H.card - 1, by omega⟩
        rw [show 3 - (H.card + 1) = j by omega] at ht
        rw [hj] at hf ⊢
        have m1 := mono j (show M.card + 2 * tdepth (k true) ≤ M.card + 2 * d by omega)
        have m2 := mono (j + 1) (show M.card + 1 + 2 * tdepth (k false) ≤ M.card + 2 * d + 1 by omega)
        have pascal : ((M.card + 2 * d).choose j : ℝ) + ((M.card + 2 * d + 1).choose (j + 1) : ℝ) ≤
            ((M.card + 2 * (d + 1)).choose (j + 1) : ℝ) := by
          have hn : (M.card + 2 * d).choose j + (M.card + 2 * d + 1).choose (j + 1) ≤
              (M.card + 2 * (d + 1)).choose (j + 1) := by
            rw [show M.card + 2 * (d + 1) = (M.card + 2 * d + 1) + 1 by ring,
              Nat.choose_succ_succ' (M.card + 2 * d + 1) j]
            have : (M.card + 2 * d).choose j ≤ (M.card + 2 * d + 1).choose j := Nat.choose_le_choose j (by omega)
            omega
          exact_mod_cast hn
        have e1 := mul_le_mul_of_nonneg_left m1 hδ2
        have e2 := mul_le_mul_of_nonneg_left m2 hδ2
        have e3 := mul_le_mul_of_nonneg_left pascal hδ2
        nlinarith

/-- One-sided depth bound for every context: `δ C(|M| + 2 · tdepth, 3 - |H|)` (`ctx_mass_le_one`). -/
theorem comp_ctx_le_one : ∀ (oa : OracleComp (TSpec ι V) α) (H M : Finset (ι × V)),
    cmass A P H M oa ≤ cmass A Q H M oa + δ * ((M.card + 2 * tdepth oa).choose (3 - H.card) : ℝ) := by
  classical
  have big : ∀ (oa : OracleComp (TSpec ι V) α) (H M : Finset (ι × V)), 3 ≤ H.card →
      cmass A P H M oa ≤ cmass A Q H M oa + δ * ((M.card + 2 * tdepth oa).choose (3 - H.card) : ℝ) := by
    intro oa H M hH
    obtain ⟨S, hSH, hS⟩ := Finset.exists_subset_card_eq hH
    have hle : cmass A P H M oa ≤ δ :=
      (cmass_le_mass A P hP H M oa).trans ((mass_mono P hP fun y hy p hp => hy.1 p (hSH hp)).trans (h3P S hS))
    have hq := cmass_nonneg A Q hQ H M oa
    rw [show 3 - H.card = 0 by omega, Nat.choose_zero_right, Nat.cast_one, mul_one]
    linarith
  intro oa
  induction oa using tinduction with
  | pure a =>
      intro H M
      by_cases hH : 3 ≤ H.card
      · exact big _ H M hH
      rw [cmass_pure, cmass_pure, tdepth_pure]
      split_ifs with ha
      · simpa using ctx_mass_le_one P Q δ hP hQ hδ h2 h3P h3Q H M (by omega)
      · have : 0 ≤ δ * ((M.card + 2 * 0).choose (3 - H.card) : ℝ) := by positivity
        linarith
  | coin n k ih =>
      intro H M
      rw [cmass_coin, cmass_coin, tdepth_coin]
      have hmono : ∀ u, ((M.card + 2 * tdepth (k u)).choose (3 - H.card) : ℝ) ≤
          ((M.card + 2 * univ.sup fun u => tdepth (k u)).choose (3 - H.card) : ℝ) := fun u => by
        exact_mod_cast Nat.choose_le_choose _ (by
          have := le_sup (f := fun u => tdepth (k u)) (mem_univ u); omega)
      rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
      calc (∑ u : Fin (n + 1), cmass A P H M (k u))
          ≤ ∑ u : Fin (n + 1), (cmass A Q H M (k u) + δ *
              ((M.card + 2 * univ.sup fun u => tdepth (k u)).choose (3 - H.card) : ℝ)) :=
            sum_le_sum fun u _ => (ih u H M).trans (by nlinarith [hmono u])
        _ = _ := by rw [sum_add_distrib]; simp; ring
  | test p k ih =>
      intro H M
      by_cases hH : 3 ≤ H.card
      · exact big _ H M hH
      rw [cmass_test, cmass_test, tdepth_test]
      set d := max (tdepth (k true)) (tdepth (k false))
      have mono : ∀ {a b : ℕ} (c : ℕ), a ≤ b → ((a.choose c : ℕ) : ℝ) ≤ (b.choose c : ℝ) :=
        fun c hab => by exact_mod_cast Nat.choose_le_choose c hab
      have hδ2 : 0 ≤ δ := hδ
      have qt := cmass_nonneg A Q hQ (insert p H) M (k true)
      have qf := cmass_nonneg A Q hQ H (insert p M) (k false)
      by_cases hpH : p ∈ H
      · rw [Finset.insert_eq_of_mem hpH] at qt ⊢
        rw [cmass_eq_zero A P H (insert p M) (k false) (fun y hy =>
          ((ctx_insert_miss y H M p).mp hy).2 (hy.1 p hpH))]
        have ht := ih true H M
        have hm := mono (3 - H.card) (show M.card + 2 * tdepth (k true) ≤ M.card + 2 * (d + 1) by omega)
        nlinarith [mul_le_mul_of_nonneg_left hm hδ2]
      by_cases hpM : p ∈ M
      · rw [Finset.insert_eq_of_mem hpM] at qf ⊢
        rw [cmass_eq_zero A P (insert p H) M (k true) (fun y hy =>
          (hy.2 p hpM) ((ctx_insert_hit y H M p).mp hy).2)]
        have hf := ih false H M
        have hm := mono (3 - H.card) (show M.card + 2 * tdepth (k false) ≤ M.card + 2 * (d + 1) by omega)
        nlinarith [mul_le_mul_of_nonneg_left hm hδ2]
      · have ht := ih true (insert p H) M
        have hf := ih false H (insert p M)
        rw [Finset.card_insert_of_notMem hpH] at ht
        rw [Finset.card_insert_of_notMem hpM] at hf
        obtain ⟨j, hj⟩ : ∃ j, 3 - H.card = j + 1 := ⟨3 - H.card - 1, by omega⟩
        rw [show 3 - (H.card + 1) = j by omega] at ht
        rw [hj] at hf ⊢
        have m1 := mono j (show M.card + 2 * tdepth (k true) ≤ M.card + 2 * d by omega)
        have m2 := mono (j + 1) (show M.card + 1 + 2 * tdepth (k false) ≤ M.card + 2 * d + 1 by omega)
        have pascal : ((M.card + 2 * d).choose j : ℝ) + ((M.card + 2 * d + 1).choose (j + 1) : ℝ) ≤
            ((M.card + 2 * (d + 1)).choose (j + 1) : ℝ) := by
          have hn : (M.card + 2 * d).choose j + (M.card + 2 * d + 1).choose (j + 1) ≤
              (M.card + 2 * (d + 1)).choose (j + 1) := by
            rw [show M.card + 2 * (d + 1) = (M.card + 2 * d + 1) + 1 by ring,
              Nat.choose_succ_succ' (M.card + 2 * d + 1) j]
            have : (M.card + 2 * d).choose j ≤ (M.card + 2 * d + 1).choose j := Nat.choose_le_choose j (by omega)
            omega
          exact_mod_cast hn
        have e1 := mul_le_mul_of_nonneg_left m1 hδ2
        have e2 := mul_le_mul_of_nonneg_left m2 hδ2
        have e3 := mul_le_mul_of_nonneg_left pascal hδ2
        nlinarith

/-- One-sided all-miss bound: `δ (C(|M|, 3) + C(2D, 2) · amLen)` for programs with `|M| + tdepth ≤ D`. Along the
all-miss path a test costs its hit branch `C(|M| + 2 t, 2)` plus the miss-context step `C(|M|, 2)`, and
`|M| + (|M| + 2t) ≤ 2D`. -/
theorem comp_ctx_le_am_one (D : ℕ) : ∀ (oa : OracleComp (TSpec ι V) α) (M : Finset (ι × V)),
    M.card + tdepth oa ≤ D →
    cmass A P ∅ M oa ≤ cmass A Q ∅ M oa + δ * ((M.card.choose 3 : ℝ) + ((2 * D).choose 2 : ℝ) * amLen oa) := by
  classical
  intro oa
  have hK0 : (0 : ℝ) ≤ ((2 * D).choose 2 : ℝ) := Nat.cast_nonneg _
  induction oa using tinduction with
  | pure a =>
      intro M _
      have h := comp_ctx_le_one P Q δ A hP hQ hδ h2 h3P h3Q (pure a) ∅ M
      rw [tdepth_pure] at h
      rw [amLen_pure]
      simpa using h
  | coin n k ih =>
      intro M hD
      rw [cmass_coin, cmass_coin, amLen_coin, tdepth_coin] at *
      have hD' : ∀ u, M.card + tdepth (k u) ≤ D := fun u => by
        have := le_sup (f := fun u => tdepth (k u)) (mem_univ u); omega
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hB : (∑ u : Fin (n + 1), δ * ((M.card.choose 3 : ℝ) + ((2 * D).choose 2 : ℝ) * amLen (k u))) =
          δ * (((n : ℝ) + 1) * (M.card.choose 3 : ℝ) + ((2 * D).choose 2 : ℝ) * ∑ u, amLen (k u)) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum]
        simp [card_univ]
      calc (∑ u : Fin (n + 1), cmass A P ∅ M (k u)) / (n + 1)
          ≤ (∑ u : Fin (n + 1), (cmass A Q ∅ M (k u) +
              δ * ((M.card.choose 3 : ℝ) + ((2 * D).choose 2 : ℝ) * amLen (k u)))) / (n + 1) :=
            div_le_div_of_nonneg_right (sum_le_sum fun u _ => ih u M (hD' u)) hn.le
        _ = _ := by
          rw [sum_add_distrib, add_div, hB]
          congr 1
          field_simp
  | test p k ih =>
      intro M hD
      rw [cmass_test, cmass_test, amLen_test]
      rw [tdepth_test] at hD
      have qt := cmass_nonneg A Q hQ (insert p ∅) M (k true)
      have qf := cmass_nonneg A Q hQ ∅ (insert p M) (k false)
      have hal := amLen_nonneg (k false)
      have hc3 : (0 : ℝ) ≤ (M.card.choose 3 : ℝ) := Nat.cast_nonneg _
      by_cases hpM : p ∈ M
      · rw [Finset.insert_eq_of_mem hpM] at qf ⊢
        rw [cmass_eq_zero A P (insert p ∅) M (k true) (fun y hy =>
          (hy.2 p hpM) ((ctx_insert_hit y ∅ M p).mp hy).2)]
        have hf := ih false M (by omega)
        nlinarith [mul_nonneg hδ hK0]
      · have ht := comp_ctx_le_one P Q δ A hP hQ hδ h2 h3P h3Q (k true) (insert p ∅) M
        have hf := ih false (insert p M) (by rw [Finset.card_insert_of_notMem hpM]; omega)
        rw [Finset.card_insert_of_notMem hpM] at hf
        simp only [Finset.insert_empty, Finset.card_singleton] at ht ⊢
        have hs : ((M.card + 1).choose 3 : ℝ) = (M.card.choose 3 : ℝ) + (M.card.choose 2 : ℝ) := by
          rw [Nat.choose_succ_succ' M.card 2]; push_cast; ring
        have hcomb : (M.card.choose 2 : ℝ) + ((M.card + 2 * tdepth (k true)).choose (3 - 1) : ℝ) ≤
            ((2 * D).choose 2 : ℝ) := by
          have hn : M.card.choose 2 + (M.card + 2 * tdepth (k true)).choose 2 ≤ (2 * D).choose 2 :=
            (choose_two_add_le _ _).trans (Nat.choose_le_choose 2 (by omega))
          exact_mod_cast hn
        rw [hs] at hf
        have e := mul_le_mul_of_nonneg_left hcomb hδ
        nlinarith [mul_nonneg hδ hK0]

/-- **Side channel of test programs** (one-sided constant: `2 δ D²` per all-miss test). -/
theorem comp_mass_le (D : ℕ) (oa : OracleComp (TSpec ι V) α) (hD : tdepth oa ≤ D) :
    (by classical exact ∑ y, P y * prT y A oa) ≤
      (by classical exact ∑ y, Q y * prT y A oa) + 2 * δ * kconst D * amLen oa := by
  classical
  have h := comp_ctx_le_am_one P Q δ A hP hQ hδ h2 h3P h3Q D oa ∅ (by simpa using hD)
  have e : ∀ R : (ι → V) → ℝ, cmass A R ∅ ∅ oa = ∑ y, R y * prT y A oa := fun R => by
    unfold cmass
    refine sum_congr rfl fun y _ => ?_
    rw [if_pos (by simp [Ctx, AllHit])]
  rw [e P, e Q] at h
  have hk := choose_two_double_le D
  have hal := amLen_nonneg oa
  simp only [Finset.card_empty, Nat.choose_zero_succ, Nat.cast_zero, zero_add] at h
  have e2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk hal) hδ
  nlinarith

end Bound

/-! ### The all-miss length against the actual number of tests -/

section Count
variable (P : (ι → V) → ℝ) (δ₁ : ℝ)
variable {α : Type}

/-- `Σ_y P y · 1{Ctx y ∅ M} · enT y p`. -/
noncomputable def cnt (M : Finset (ι × V)) (oa : OracleComp (TSpec ι V) α) : ℝ :=
  by classical exact ∑ y, (if Ctx y ∅ M then P y else 0) * enT y oa

theorem enT_nonneg (y : ι → V) (oa : OracleComp (TSpec ι V) α) : 0 ≤ enT y oa := by
  induction oa using tinduction with
  | pure a => rw [enT_pure]
  | coin n k ih => rw [enT_coin]; exact div_nonneg (sum_nonneg fun u _ => ih u) (by positivity)
  | test p k ih => rw [enT_test]; linarith [ih (decide (y p.1 = p.2))]

variable (hP : ∀ y, 0 ≤ P y) (hδ₁ : 0 ≤ δ₁) (h1 : ∀ p : ι × V, mass P (fun y => y p.1 = p.2) ≤ δ₁)
include hP hδ₁ h1

/-- `cnt M p ≥ amLen p · (mass(Ctx ∅ M) - δ₁ · tdepth p)`. -/
theorem cnt_ge : ∀ (oa : OracleComp (TSpec ι V) α) (M : Finset (ι × V)),
    amLen oa * (mass P (fun y => Ctx y ∅ M) - δ₁ * tdepth oa) ≤ cnt P M oa := by
  classical
  intro oa
  induction oa using tinduction with
  | pure a =>
      intro M
      rw [amLen_pure, zero_mul]
      unfold cnt
      exact sum_nonneg fun y _ => mul_nonneg (by split <;> simp [hP y]) (enT_nonneg y _)
  | coin n k ih =>
      intro M
      have hcnt : cnt P M (coinQ n >>= k) = (∑ u : Fin (n + 1), cnt P M (k u)) / (n + 1) := by
        unfold cnt
        simp only [enT_coin, mul_div_assoc', ← sum_div, mul_sum]
        rw [sum_comm]
      rw [hcnt, amLen_coin, tdepth_coin]
      have hmono : ∀ u, mass P (fun y => Ctx y ∅ M) - δ₁ * ((univ.sup fun u => tdepth (k u) : ℕ) : ℝ) ≤
          mass P (fun y => Ctx y ∅ M) - δ₁ * (tdepth (k u) : ℝ) := fun u => by
        have : (tdepth (k u) : ℝ) ≤ ((univ.sup fun u => tdepth (k u) : ℕ) : ℝ) := by
          exact_mod_cast le_sup (f := fun u => tdepth (k u)) (mem_univ u)
        nlinarith
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity), sum_mul]
      exact sum_le_sum fun u _ => (mul_le_mul_of_nonneg_left (hmono u) (amLen_nonneg (k u))).trans (ih u M)
  | test p k ih =>
      intro M
      have hcnt : cnt P M (testQ p >>= k) ≥ mass P (fun y => Ctx y ∅ M) + cnt P (insert p M) (k false) := by
        unfold cnt mass
        rw [← sum_add_distrib]
        refine sum_le_sum fun y _ => ?_
        rw [enT_test]
        have he := enT_nonneg y (k (decide (y p.1 = p.2)))
        by_cases hy : y p.1 = p.2
        · have h2 : ¬Ctx y ∅ (insert p M) := by rw [ctx_insert_miss]; simp [hy]
          simp only [h2, if_false, zero_mul, add_zero]
          split_ifs
          · nlinarith [hP y]
          · simp
        · have h2 : Ctx y ∅ (insert p M) ↔ Ctx y ∅ M := by rw [ctx_insert_miss]; simp [hy]
          simp only [hy, decide_false, h2]
          split_ifs
          · nlinarith [hP y]
          · simp
      have hmass : mass P (fun y => Ctx y ∅ M) - δ₁ ≤ mass P (fun y => Ctx y ∅ (insert p M)) := by
        have hs := mass_split P (fun y => Ctx y ∅ M) (fun y => y p.1 = p.2)
        have hhit : mass P (fun y => Ctx y ∅ M ∧ y p.1 = p.2) ≤ δ₁ :=
          (mass_mono P hP fun y hy => hy.2).trans (h1 p)
        have hmiss : mass P (fun y => Ctx y ∅ M ∧ ¬y p.1 = p.2) = mass P (fun y => Ctx y ∅ (insert p M)) :=
          mass_congr P fun y => by rw [ctx_insert_miss]
        linarith
      have hf := ih false (insert p M)
      rw [amLen_test, tdepth_test]
      have hal := amLen_nonneg (k false)
      have hdf : ((tdepth (k false) + 1 : ℕ) : ℝ) ≤ ((max (tdepth (k true)) (tdepth (k false)) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show tdepth (k false) + 1 ≤ max (tdepth (k true)) (tdepth (k false)) + 1 by omega)
      set Dp : ℝ := ((max (tdepth (k true)) (tdepth (k false)) + 1 : ℕ) : ℝ)
      set d' : ℝ := (tdepth (k false) : ℝ)
      push_cast at hdf
      have hm0 := mass_nonneg P hP (fun y => Ctx y ∅ M)
      have hD0 : 0 ≤ Dp := by positivity
      have k1 : 0 ≤ amLen (k false) * (mass P (fun y => Ctx y ∅ (insert p M)) - (mass P (fun y => Ctx y ∅ M) - δ₁)) :=
        mul_nonneg hal (by linarith)
      have k2 : 0 ≤ amLen (k false) * (δ₁ * (Dp - d' - 1)) := mul_nonneg hal (mul_nonneg hδ₁ (by linarith))
      have k3 : 0 ≤ δ₁ * Dp := mul_nonneg hδ₁ hD0
      nlinarith

/-- **All-miss length against the actual number of tests:** `amLen p · (mass P - δ₁ · tdepth p) ≤ E_P[#tests]`. -/
theorem amLen_le_enT (oa : OracleComp (TSpec ι V) α) :
    amLen oa * (mass P (fun _ => True) - δ₁ * tdepth oa) ≤ (by classical exact ∑ y, P y * enT y oa) := by
  classical
  have h := cnt_ge P δ₁ hP hδ₁ h1 oa ∅
  have e1 : mass P (fun y => Ctx y ∅ ∅) = mass P (fun _ => True) := mass_congr P fun y => by simp [Ctx, AllHit]
  have e2 : cnt P ∅ oa = ∑ y, P y * enT y oa := by
    unfold cnt
    refine sum_congr rfl fun y _ => ?_
    rw [if_pos (by simp [Ctx, AllHit])]
  rw [e1, e2] at h
  exact h

end Count
end ClaudeWCT.Arith.SideChannel
end
-- ==== merged from ClaudeWCT_Arith_FamilyTest ====
section

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
end
