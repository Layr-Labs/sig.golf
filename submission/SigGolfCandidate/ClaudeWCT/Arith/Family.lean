import SigGolfCandidate.ClaudeWCT.Arith.GF128Field
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Polynomial seed families: uniformity and hazard counts

A family is a coefficient vector `K : Fin n → Digest` (constant term first); its seed at the point `pt` is
`familyEval (List.ofFn K) pt`. Points are naturals `< 1024`, pairwise distinct inside a family.

* `toGF_familyEval`: in `GF`, the seed is `∑ j, K j · pt^j`.
* `famSplit_bijective`: for `t ≤ n` distinct points, `K ↦ (seeds at the points, top n - t coefficients)` is a
  bijection; hence `familyEval_fiber_card` (each value vector has `2^(128(n-t))` preimages) and
  `familyEval_uniform` (the seeds of a uniform `K` are uniform on `Fin t → Digest`).
* Lazy-posterior counts (DESIGN-A-SEC §5): `famAffine known` (vectors consistent with disclosed pairs),
  `famPost known misses` (minus the excluded guesses), `fam_fiber_card`, `fam_hazard`, `fam_pair_hazard`.
-/

namespace ClaudeWCT.Arith
open SigGolfCandidate.T3 OracleComp

/-! ### Horner evaluation in `GF` -/

theorem familyEval_cons (c : Digest) (cs : List Digest) (pt : Nat) :
    familyEval (c :: cs) pt = gfMulPt (familyEval cs pt) pt ^^^ c := rfl

/-- The seed at `pt < 1024` is the polynomial `∑ j, K j · X^j` evaluated at the point, in `GF`. -/
theorem toGF_familyEval {n : Nat} (K : Fin n → Digest) {pt : Nat} (h : pt < 1024) :
    toGF (familyEval (List.ofFn K) pt) = ∑ j : Fin n, toGF (K j) * toGF (BitVec.ofNat 128 pt) ^ (j : ℕ) := by
  induction n with
  | zero => simp only [List.ofFn_zero, Finset.univ_eq_empty, Finset.sum_empty]; exact toGF_zero
  | succ n ih =>
    rw [List.ofFn_succ, familyEval_cons, toGF_xor, toGF_mulPt _ h, ih, Fin.sum_univ_succ, Finset.sum_mul]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, mul_assoc]
    rw [add_comm]

/-- A vector supported on the first `t` coordinates that vanishes at `t` points with unit differences is zero
(the square Vandermonde matrix has a unit determinant). -/
theorem vandermonde_kernel {n t : Nat} (ht : t ≤ n) (x : Fin t → GF)
    (hx : ∀ i j, i ≠ j → IsUnit (x i - x j)) (D : Fin n → GF) (hD : ∀ j : Fin n, t ≤ j.val → D j = 0)
    (h : ∀ i, ∑ j : Fin n, D j * x i ^ (j : ℕ) = 0) : D = 0 := by
  classical
  let D' : Fin t → GF := fun j => D (Fin.castLE ht j)
  have hdet : IsUnit (Matrix.vandermonde x).det := by
    rw [Matrix.det_vandermonde, IsUnit.prod_iff]
    intro i _
    rw [IsUnit.prod_iff]
    intro j hj
    exact hx j i (ne_of_gt (by simpa using hj))
  have hmul : (Matrix.vandermonde x).mulVec D' = 0 := by
    funext i
    rw [Pi.zero_apply, ← h i]
    simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
    refine Fintype.sum_of_injective (Fin.castLE ht) (Fin.castLE_injective ht) _ _ ?_ ?_
    · intro j hj
      have : t ≤ j.val := by
        by_contra hlt
        exact hj ⟨⟨j.val, by omega⟩, rfl⟩
      simp [hD j this]
    · intro j
      simp [D', mul_comm]
  have h0 : D' = 0 := by
    have := congrArg (fun v => (Matrix.vandermonde x)⁻¹.mulVec v) hmul
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet] using this
  funext j
  by_cases hj : t ≤ j.val
  · exact hD j hj
  · exact congrFun h0 ⟨j.val, by omega⟩

/-! ### Seeds at `t ≤ n` distinct points: bijection, fibres, uniformity -/

/-- The seeds at `t` points together with the top `n - t` coefficients. -/
def famSplit {n t : Nat} (pts : Fin t → Nat) (K : Fin n → Digest) :
    (Fin t → Digest) × (Fin (n - t) → Digest) :=
  (fun i => familyEval (List.ofFn K) (pts i), fun j => K ⟨t + j.val, by have := j.isLt; omega⟩)

theorem famSplit_bijective {n t : Nat} (ht : t ≤ n) (pts : Fin t → Nat) (hinj : Function.Injective pts)
    (hsmall : ∀ i, pts i < 1024) : Function.Bijective (famSplit (n := n) pts) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun K K' hKK => ?_, ?_⟩
  · simp only [famSplit, Prod.mk.injEq] at hKK
    obtain ⟨h1, h2⟩ := hKK
    have hD := vandermonde_kernel ht (fun i => toGF (BitVec.ofNat 128 (pts i)))
      (fun i j hij => point_sub_isUnit (hsmall i) (hsmall j) (hinj.ne hij))
      (fun j => toGF (K j) - toGF (K' j)) ?_ ?_
    · funext j
      exact toGF_injective (sub_eq_zero.1 (congrFun hD j))
    · intro j hj
      have e : j = ⟨t + (j.val - t), by omega⟩ := Fin.ext (by simp only; omega)
      have := congrFun h2 ⟨j.val - t, by omega⟩
      simp only at this
      rw [sub_eq_zero, e, this]
    · intro i
      have := congrArg toGF (congrFun h1 i)
      rw [toGF_familyEval _ (hsmall i), toGF_familyEval _ (hsmall i)] at this
      simp only [sub_mul, Finset.sum_sub_distrib, this, sub_self]
  · simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bitVec]
    rw [← pow_add, Nat.add_sub_cancel' ht]

/-- The seeds at `t ≤ n` distinct points `< 1024` take every value vector. -/
theorem familyEval_surjective {n t : Nat} (ht : t ≤ n) (pts : Fin t → Nat) (hinj : Function.Injective pts)
    (hsmall : ∀ i, pts i < 1024) :
    Function.Surjective fun K : Fin n → Digest => fun i => familyEval (List.ofFn K) (pts i) := by
  intro y
  obtain ⟨K, hK⟩ := (famSplit_bijective ht pts hinj hsmall).2 (y, fun _ => 0)
  exact ⟨K, congrArg Prod.fst hK⟩

/-- Each vector of seed values at `t ≤ n` distinct points `< 1024` has exactly `2^(128 (n - t))` coefficient
preimages. -/
theorem familyEval_fiber_card {n t : Nat} (ht : t ≤ n) (pts : Fin t → Nat) (hinj : Function.Injective pts)
    (hsmall : ∀ i, pts i < 1024) (y : Fin t → Digest) :
    (Finset.univ.filter fun K : Fin n → Digest => ∀ i, familyEval (List.ofFn K) (pts i) = y i).card =
      2 ^ (128 * (n - t)) := by
  classical
  let e := Equiv.ofBijective _ (famSplit_bijective ht pts hinj hsmall)
  have hs : (Finset.univ.filter fun K : Fin n → Digest => ∀ i, familyEval (List.ofFn K) (pts i) = y i) =
      Finset.univ.map ⟨fun z => e.symm (y, z), fun z z' h => (Prod.mk.inj (e.symm.injective h)).2⟩ := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hK
      refine ⟨(e K).2, ?_⟩
      show e.symm (y, (e K).2) = K
      rw [Equiv.symm_apply_eq]
      refine Prod.ext ?_ rfl
      funext i
      exact (hK i).symm
    · rintro ⟨z, rfl⟩ i
      exact congrFun (congrArg Prod.fst (e.apply_symm_apply (y, z))) i
  rw [hs, Finset.card_map, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec,
    ← pow_mul]

/-- `familyEval_fiber_card` with the points indexed by any finite type. -/
theorem familyEval_fiber_card' {n : Nat} {ι : Type} [Fintype ι] (hι : Fintype.card ι ≤ n)
    (pts : ι → Nat) (hinj : Function.Injective pts) (hsmall : ∀ i, pts i < 1024) (y : ι → Digest) :
    (Finset.univ.filter fun K : Fin n → Digest => ∀ i, familyEval (List.ofFn K) (pts i) = y i).card =
      2 ^ (128 * (n - Fintype.card ι)) := by
  classical
  let e := Fintype.equivFin ι
  rw [← familyEval_fiber_card hι (pts ∘ e.symm) (hinj.comp e.symm.injective) (fun _ => hsmall _) (y ∘ e.symm)]
  congr 1
  apply Finset.filter_congr
  intro K _
  exact ⟨fun h i => h _, fun h i => by simpa using h (e i)⟩

/-- The seeds of a uniform coefficient vector at `t ≤ n` distinct points `< 1024` are uniform. -/
theorem familyEval_uniform {n t : Nat} (ht : t ≤ n) (pts : Fin t → Nat) (hinj : Function.Injective pts)
    (hsmall : ∀ i, pts i < 1024) :
    𝒮[(fun K : Fin n → Digest => fun i => familyEval (List.ofFn K) (pts i)) <$> ($ᵗ (Fin n → Digest))] =
      𝒮[$ᵗ (Fin t → Digest)] := by
  have hmap : (fun K : Fin n → Digest => fun i => familyEval (List.ofFn K) (pts i)) <$>
      ($ᵗ (Fin n → Digest)) = Prod.fst <$> (famSplit pts <$> ($ᵗ (Fin n → Digest))) := by
    rw [Functor.map_map]; rfl
  have hsplit : 𝒮[famSplit pts <$> ($ᵗ (Fin n → Digest))] =
      𝒮[$ᵗ ((Fin t → Digest) × (Fin (n - t) → Digest))] :=
    evalSPMF_map_bijective_uniform_cross (α := Fin n → Digest)
      (β := (Fin t → Digest) × (Fin (n - t) → Digest)) _ (famSplit_bijective ht pts hinj hsmall)
  rw [hmap, evalSPMF_map, hsplit, ← evalSPMF_map]
  exact evalSPMF_map_fst_uniformSample_prod

/-! ### Lazy posteriors of one family -/

/-- Coefficient vectors consistent with every disclosed `(point, seed)` pair. -/
noncomputable def famAffine {m : Nat} (known : Finset (Nat × Digest)) : Finset (Fin (m + 1) → Digest) :=
  Finset.univ.filter fun K => ∀ p ∈ known, familyEval (List.ofFn K) p.1 = p.2

/-- `famAffine known` minus the vectors hit by a failed guess `(point, value) ∈ misses`. -/
noncomputable def famPost {m : Nat} (known misses : Finset (Nat × Digest)) : Finset (Fin (m + 1) → Digest) :=
  (famAffine known).filter fun K => ∀ p ∈ misses, familyEval (List.ofFn K) p.1 ≠ p.2

/-- Two disclosed pairs on one point with different values leave no consistent vector. -/
theorem famAffine_eq_empty {m : Nat} {known : Finset (Nat × Digest)}
    (h : ¬ Set.InjOn Prod.fst (known : Set (Nat × Digest))) : famAffine (m := m) known = ∅ := by
  ext K
  simp only [famAffine, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro hK
  apply h
  intro p hp q hq hpq
  have h1 := hK p hp
  rw [hpq] at h1
  exact Prod.ext hpq (h1.symm.trans (hK q hq))

/-- With distinct disclosed points `< 1024`, `|famAffine known| = 2^(128 (m + 1 - |known|))`. -/
theorem famAffine_card {m : Nat} {known : Finset (Nat × Digest)} (hm : known.card ≤ m + 1)
    (hinj : Set.InjOn Prod.fst (known : Set (Nat × Digest))) (hpts : ∀ p ∈ known, p.1 < 1024) :
    (famAffine (m := m) known).card = 2 ^ (128 * (m + 1 - known.card)) := by
  classical
  have := familyEval_fiber_card' (n := m + 1) (ι := known) (by simpa using hm) (fun p => p.1.1)
    (fun p q h => Subtype.ext (hinj p.2 q.2 h)) (fun p => hpts _ p.2) (fun p => p.1.2)
  rw [Fintype.card_coe] at this
  rw [← this, famAffine]
  congr 1
  apply Finset.filter_congr
  intro K _
  exact ⟨fun h p => h p.1 p.2, fun h p hp => h ⟨p, hp⟩⟩

/-- Fibre count: with at most `m` disclosed pairs and a fresh point `b < 1024`, every value slice of
`famAffine known` at `b` has `|famAffine known| / 2^128` vectors. -/
theorem fam_fiber_card {m : Nat} {known : Finset (Nat × Digest)} (hm : known.card ≤ m)
    (hpts : ∀ p ∈ known, p.1 < 1024) {b : Nat} (hb1 : b < 1024) (hb : b ∉ known.image Prod.fst)
    (v : Digest) :
    ((famAffine (m := m) known).filter fun K => familyEval (List.ofFn K) b = v).card * 2 ^ 128 =
      (famAffine (m := m) known).card := by
  classical
  by_cases hinj : Set.InjOn Prod.fst (known : Set (Nat × Digest))
  · rw [famAffine_card (by omega) hinj hpts]
    have := familyEval_fiber_card' (n := m + 1) (ι := Option known) (by simp; omega)
      (fun o => o.elim b fun p => p.1.1) ?_ (fun o => by cases o <;> simp [hb1, hpts _ (Subtype.prop _)])
      (fun o => o.elim v fun p => p.1.2)
    · simp only [Fintype.card_option, Fintype.card_coe] at this
      have hfilt : ((famAffine (m := m) known).filter fun K => familyEval (List.ofFn K) b = v) =
          Finset.univ.filter fun K : Fin (m + 1) → Digest => ∀ o : Option known,
            familyEval (List.ofFn K) (o.elim b fun p => p.1.1) = o.elim v fun p => p.1.2 := by
        ext K
        simp only [famAffine, Finset.mem_filter, Finset.mem_univ, true_and, Option.forall, Option.elim]
        exact ⟨fun h => ⟨h.2, fun p => h.1 p.1 p.2⟩, fun h => ⟨fun p hp => h.2 ⟨p, hp⟩, h.1⟩⟩
      rw [hfilt, this, ← pow_add]
      congr 1
      omega
    · rintro (_ | p) (_ | q) h
      · rfl
      · exact absurd (Finset.mem_image.2 ⟨q.1, q.2, h.symm⟩) hb
      · exact absurd (Finset.mem_image.2 ⟨p.1, p.2, h⟩) hb
      · exact congrArg some (Subtype.ext (hinj p.2 q.2 h))
  · rw [famAffine_eq_empty hinj]
    simp

/-- Hazard count: in the posterior `famPost known misses` (at most `m` disclosed pairs, all points `< 1024`),
the slice where the seed at a fresh point `b` equals `v` has at most `|famPost| / (2^128 - |misses|)` vectors,
i.e. a guess hits with probability at most `1 / (2^128 - |misses|)`. -/
theorem fam_hazard {m : Nat} {known misses : Finset (Nat × Digest)} (hm : known.card ≤ m)
    (hpts : ∀ p ∈ known, p.1 < 1024) (hmiss : ∀ p ∈ misses, p.1 < 1024) {b : Nat} (hb1 : b < 1024)
    (hb : b ∉ known.image Prod.fst) (v : Digest) :
    ((famPost (m := m) known misses).filter fun K => familyEval (List.ofFn K) b = v).card *
        (2 ^ 128 - misses.card) ≤ (famPost (m := m) known misses).card := by
  classical
  set A := famAffine (m := m) known
  set P := famPost (m := m) known misses
  set a := (A.filter fun K => familyEval (List.ofFn K) b = v).card
  have ha : a * 2 ^ 128 = A.card := fam_fiber_card hm hpts hb1 hb v
  have hS : (P.filter fun K => familyEval (List.ofFn K) b = v).card ≤ a := by
    apply Finset.card_le_card
    intro K
    simp only [P, famPost, Finset.mem_filter]
    tauto
  rcases P.eq_empty_or_nonempty with hP | ⟨K0, hK0⟩
  · simp [hP]
  have hK0' := Finset.mem_filter.1 hK0
  have hslice : ∀ p ∈ misses, (A.filter fun K => familyEval (List.ofFn K) p.1 = p.2).card ≤ a := by
    intro p hp
    by_cases hpk : p.1 ∈ known.image Prod.fst
    · obtain ⟨q, hq, hqp⟩ := Finset.mem_image.1 hpk
      have hne : q.2 ≠ p.2 := by
        have h1 := (Finset.mem_filter.1 hK0'.1).2 q hq
        rw [hqp] at h1
        exact h1 ▸ hK0'.2 p hp
      have : (A.filter fun K => familyEval (List.ofFn K) p.1 = p.2) = ∅ := by
        ext K
        simp only [A, famAffine, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        intro hK heq
        have h1 := hK q hq
        rw [hqp, heq] at h1
        exact hne h1.symm
      rw [this, Finset.card_empty]
      exact Nat.zero_le _
    · have := fam_fiber_card hm hpts (hmiss p hp) hpk p.2
      exact le_of_eq (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos 128) (this.trans ha.symm))
  have hcover : A ⊆ P ∪ misses.biUnion fun p => A.filter fun K => familyEval (List.ofFn K) p.1 = p.2 := by
    intro K hK
    by_cases hKP : K ∈ P
    · exact Finset.mem_union_left _ hKP
    · apply Finset.mem_union_right
      simp only [P, famPost, Finset.mem_filter, not_and, not_forall, not_not] at hKP
      obtain ⟨p, hp, hpe⟩ := hKP hK
      exact Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_filter.2 ⟨hK, hpe⟩⟩
  have hA : A.card ≤ P.card + misses.card * a :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_biUnion_le_card_mul _ _ _ hslice) _))
  calc _ ≤ a * (2 ^ 128 - misses.card) := Nat.mul_le_mul_right _ hS
    _ = a * 2 ^ 128 - misses.card * a := by rw [Nat.mul_sub, Nat.mul_comm a misses.card]
    _ ≤ P.card := by omega

/-- Disclosing a hit `(b, v)` is the same as conditioning the posterior on it. -/
theorem famPost_insert {m : Nat} (known misses : Finset (Nat × Digest)) (b : Nat) (v : Digest) :
    famPost (m := m) (insert (b, v) known) misses =
      (famPost (m := m) known misses).filter fun K => familyEval (List.ofFn K) b = v := by
  ext K
  simp only [famPost, famAffine, Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert]
  tauto

/-- Recording a failed guess `(b, v)` filters the posterior by `≠`. -/
theorem famPost_insert_miss {m : Nat} (known misses : Finset (Nat × Digest)) (b : Nat) (v : Digest) :
    famPost (m := m) known (insert (b, v) misses) =
      (famPost (m := m) known misses).filter fun K => familyEval (List.ofFn K) b ≠ v := by
  ext K
  simp only [famPost, Finset.mem_filter, Finset.forall_mem_insert]
  tauto

/-- Pair hazard: after one disclosed hit `(b, v)` (with `|known| + 1 ≤ m`), a guess at another fresh point
`b'` still hits with probability at most `1 / (2^128 - |misses|)`. -/
theorem fam_pair_hazard {m : Nat} {known misses : Finset (Nat × Digest)} (hm : known.card + 1 ≤ m)
    (hpts : ∀ p ∈ known, p.1 < 1024) (hmiss : ∀ p ∈ misses, p.1 < 1024) {b b' : Nat} (hb1 : b < 1024)
    (hb1' : b' < 1024) (hb : b ∉ known.image Prod.fst) (hb' : b' ∉ known.image Prod.fst) (hbb : b' ≠ b)
    (v v' : Digest) :
    (((famPost (m := m) known misses).filter fun K => familyEval (List.ofFn K) b = v).filter
        fun K => familyEval (List.ofFn K) b' = v').card * (2 ^ 128 - misses.card) ≤
      ((famPost (m := m) known misses).filter fun K => familyEval (List.ofFn K) b = v).card := by
  classical
  rw [← famPost_insert]
  have hnot : (b, v) ∉ known := fun h => hb (Finset.mem_image.2 ⟨_, h, rfl⟩)
  refine fam_hazard (by rw [Finset.card_insert_of_notMem hnot]; exact hm) ?_ hmiss hb1' ?_ v'
  · intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    exacts [hb1, hpts p hp]
  · rw [Finset.image_insert, Finset.mem_insert]
    rintro (h | h)
    exacts [hbb h, hb' h]

/-- Joint form of the pair hazard: two hits at fresh distinct points cost a factor `(2^128 - |misses|)^2`. -/
theorem fam_pair_hazard_joint {m : Nat} {known misses : Finset (Nat × Digest)} (hm : known.card + 1 ≤ m)
    (hpts : ∀ p ∈ known, p.1 < 1024) (hmiss : ∀ p ∈ misses, p.1 < 1024) {b b' : Nat} (hb1 : b < 1024)
    (hb1' : b' < 1024) (hb : b ∉ known.image Prod.fst) (hb' : b' ∉ known.image Prod.fst) (hbb : b' ≠ b)
    (v v' : Digest) :
    ((famPost (m := m) known misses).filter fun K =>
        familyEval (List.ofFn K) b = v ∧ familyEval (List.ofFn K) b' = v').card *
        (2 ^ 128 - misses.card) ^ 2 ≤ (famPost (m := m) known misses).card := by
  rw [← Finset.filter_filter, pow_two, ← Nat.mul_assoc]
  exact (Nat.mul_le_mul_right _ (fam_pair_hazard hm hpts hmiss hb1 hb1' hb hb' hbb v v')).trans
    (fam_hazard (by omega) hpts hmiss hb1 hb v)

/-! ### Probability forms (uniform draw from a posterior) -/

open ENNReal in
/-- `s · d ≤ p` gives `s / p ≤ 1 / d` in `ℝ≥0∞` (also when `p = 0` or `d = 0`). -/
theorem natCast_div_le_inv_of_mul_le {s p d : Nat} (h : s * d ≤ p) : (s : ℝ≥0∞) / p ≤ (d : ℝ≥0∞)⁻¹ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  apply ENNReal.div_le_of_le_mul
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
  calc (s : ℝ≥0∞) = s * d * (d : ℝ≥0∞)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hd0 (ENNReal.natCast_ne_top d), mul_one]
    _ ≤ p * (d : ℝ≥0∞)⁻¹ := by gcongr; exact_mod_cast h
    _ = (d : ℝ≥0∞)⁻¹ * p := mul_comm _ _

open ENNReal in
/-- `fam_hazard` as a probability: for `K` uniform on the posterior, `Pr[seed at b = v] ≤ 1 / (2^128 - e)` for
any `e ≥ |misses|` (the engines' probe count). -/
theorem fam_hazard_prob {m : Nat} {known misses : Finset (Nat × Digest)} (hm : known.card ≤ m)
    (hpts : ∀ p ∈ known, p.1 < 1024) (hmiss : ∀ p ∈ misses, p.1 < 1024) {b : Nat} (hb1 : b < 1024)
    (hb : b ∉ known.image Prod.fst) (v : Digest) {e : Nat} (he : misses.card ≤ e) :
    (((famPost (m := m) known misses).filter fun K => familyEval (List.ofFn K) b = v).card : ℝ≥0∞) /
        (famPost (m := m) known misses).card ≤ ((2 ^ 128 - e : Nat) : ℝ≥0∞)⁻¹ :=
  natCast_div_le_inv_of_mul_le ((Nat.mul_le_mul_left _ (Nat.sub_le_sub_left he _)).trans
    (fam_hazard hm hpts hmiss hb1 hb v))

open ENNReal in
/-- `fam_pair_hazard` as a conditional probability: given the hit `(b, v)`, a guess `(b', v')` at another fresh
point hits with probability at most `1 / (2^128 - e)`. -/
theorem fam_pair_hazard_prob {m : Nat} {known misses : Finset (Nat × Digest)} (hm : known.card + 1 ≤ m)
    (hpts : ∀ p ∈ known, p.1 < 1024) (hmiss : ∀ p ∈ misses, p.1 < 1024) {b b' : Nat} (hb1 : b < 1024)
    (hb1' : b' < 1024) (hb : b ∉ known.image Prod.fst) (hb' : b' ∉ known.image Prod.fst) (hbb : b' ≠ b)
    (v v' : Digest) {e : Nat} (he : misses.card ≤ e) :
    ((((famPost (m := m) known misses).filter fun K => familyEval (List.ofFn K) b = v).filter
        fun K => familyEval (List.ofFn K) b' = v').card : ℝ≥0∞) /
        ((famPost (m := m) known misses).filter fun K => familyEval (List.ofFn K) b = v).card ≤
      ((2 ^ 128 - e : Nat) : ℝ≥0∞)⁻¹ :=
  natCast_div_le_inv_of_mul_le ((Nat.mul_le_mul_left _ (Nat.sub_le_sub_left he _)).trans
    (fam_pair_hazard hm hpts hmiss hb1 hb1' hb hb' hbb v v'))

end ClaudeWCT.Arith
