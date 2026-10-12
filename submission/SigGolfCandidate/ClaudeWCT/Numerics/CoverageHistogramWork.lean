import SigGolfCandidate.ClaudeWCT.Numerics.N600Cover
import SigGolfCandidate.ClaudeWCT.Numerics.Covariance
import Mathlib.Data.Fintype.BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.Numerics.N600
open Finset
variable {β : Type*} [Fintype β]

def maxWord (val : β → Fin 6 → ℕ) {j : ℕ} (E : Fin j → β) (i : Fin 6) : ℕ :=
  Finset.univ.sup fun k => val (E k) i

theorem maxWord_le (val : β → Fin 6 → ℕ) (h4 : ∀ x i, val x i ≤ 4)
    {j : ℕ} (E : Fin j → β) (i : Fin 6) : maxWord val E i ≤ 4 := by
  exact Finset.sup_le fun k _ => h4 (E k) i

theorem maxWord_lt_iff (val : β → Fin 6 → ℕ) {j : ℕ} (hj : 0 < j)
    (E : Fin j → β) (i : Fin 6) (a : ℕ) : maxWord val E i < a ↔ ∀ k, val (E k) i < a := by
  constructor
  · intro h k
    exact lt_of_le_of_lt (Finset.le_sup (f := fun k => val (E k) i) (Finset.mem_univ k)) h
  · intro h
    have ha : 0 < a := lt_of_le_of_lt (Nat.zero_le _) (h ⟨0, hj⟩)
    exact (Finset.sup_lt_iff ha).mpr (fun k _ => h k)

theorem maxWord_cdf (val : β → Fin 6 → ℕ) {j : ℕ} (hj : 0 < j) (u : Fin 6 → Fin 6) :
    #{E : Fin j → β | ∀ i, maxWord val E i < u i} = (cntU val u) ^ j := by
  classical
  have hset : ({E : Fin j → β | ∀ i, maxWord val E i < u i} : Finset (Fin j → β)) =
      Fintype.piFinset (fun _ : Fin j => {x : β | ∀ i, val x i < u i}) := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    simp only [maxWord_lt_iff val hj]
    exact forall_comm
  rw [hset, Fintype.card_piFinset_const]
  rfl

noncomputable def maxCountTree (j : ℕ) : T6 := dT (mapT (fun z => z ^ j) cntT)

theorem maxCountTree_eq (val : β → Fin 6 → ℕ) (hW : WordsOf val)
    (h4 : ∀ x i, val x i ≤ 4) {j : ℕ} (hj : 0 < j) (u : Fin 6 → Fin 6) :
    lookup (maxCountTree j) (digitsOf u) =
      #{E : Fin j → β | ∀ i, u i ≠ 5 → maxWord val E i = u i} := by
  classical
  have hcdf : ∀ l : List ℕ, l.length = 6 → (∀ v ∈ l, v ≤ 5) →
      lookup (mapT (fun z => z ^ j) cntT) l =
        #{E : Fin j → β | ltB (List.ofFn (maxWord val E)) l} := by
    intro l hl hv
    let u' : Fin 6 → Fin 6 := fun i => ⟨l[i.val]'(by omega), Nat.lt_succ_of_le (hv _ (List.getElem_mem _))⟩
    have he : digitsOf u' = l := by
      apply List.ext_getElem
      · simp [digitsOf, hl]
      · intro i hi hi'
        simp only [digitsOf, List.getElem_ofFn]
        rfl
    rw [← he, lookup_mapT _ 6 cntT _ full_cntT (digitsOf_length u'), cntT_eq hW]
    rw [← maxWord_cdf val hj u']
    congr 1
    ext E
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (ltB_ofFn_iff _ u').symm
  rw [maxCountTree, lookup_dT 6 univ (fun E : Fin j → β => List.ofFn (maxWord val E)) _
    (full_mapT _ 6 cntT full_cntT)
    (fun E _ => ⟨List.length_ofFn, fun v hv => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact maxWord_le val h4 E i⟩)
    hcdf _ (digitsOf_length u) (digitsOf_le u)]
  congr 1
  ext E
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mtB_ofFn_iff _ u

noncomputable def coverCount (val : β → Fin 6 → ℕ) {j : ℕ} (E : Fin j → β) : ℕ :=
  #{x : β | ∀ i, val x i ≤ maxWord val E i}

def gridUp {n : ℕ} (u : Fin n → Fin 5) : Fin n → Fin 6 := fun i => ⟨(u i).val + 1, by omega⟩
def gridCast {n : ℕ} (u : Fin n → Fin 5) : Fin n → Fin 6 := fun i => ⟨(u i).val, by omega⟩
noncomputable def gridCoverage (u : Fin 6 → Fin 5) : ℕ := lookup cntT (digitsOf (gridUp u))
noncomputable def coverageHistogram (j a : ℕ) : ℕ :=
  ∑ u : Fin 6 → Fin 5, if gridCoverage u = a then lookup (maxCountTree j) (digitsOf (gridCast u)) else 0

noncomputable def maxGrid (val : β → Fin 6 → ℕ) (h4 : ∀ x i, val x i ≤ 4)
    {j : ℕ} (E : Fin j → β) : Fin 6 → Fin 5 := fun i => ⟨maxWord val E i, Nat.lt_succ_of_le (maxWord_le val h4 E i)⟩

theorem coverCount_grid (val : β → Fin 6 → ℕ) (hW : WordsOf val)
    (h4 : ∀ x i, val x i ≤ 4) {j : ℕ} (E : Fin j → β) :
    coverCount val E = gridCoverage (maxGrid val h4 E) := by
  classical
  rw [gridCoverage, cntT_eq hW, cntU, coverCount]
  congr 1
  ext x
  simp [gridUp, maxGrid, Nat.lt_succ_iff]

theorem maxGrid_fiber (val : β → Fin 6 → ℕ) (hW : WordsOf val)
    (h4 : ∀ x i, val x i ≤ 4) {j : ℕ} (hj : 0 < j) (u : Fin 6 → Fin 5) :
    #{E : Fin j → β | maxGrid val h4 E = u} = lookup (maxCountTree j) (digitsOf (gridCast u)) := by
  classical
  rw [maxCountTree_eq val hW h4 hj]
  congr 1
  ext E
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have H : ∀ i, gridCast u i ≠ 5 := by
    intro i
    intro h
    have := congrArg Fin.val h
    have := (u i).isLt
    simp [gridCast] at *
    omega
  constructor
  · intro h i _
    exact congrArg Fin.val (congrFun h i)
  · intro h
    funext i
    apply Fin.ext
    exact h i (H i)

theorem coverageHistogram_eq (val : β → Fin 6 → ℕ) (hW : WordsOf val)
    (h4 : ∀ x i, val x i ≤ 4) {j : ℕ} (hj : 0 < j) (a : ℕ) :
    #{E : Fin j → β | coverCount val E = a} = coverageHistogram j a := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := maxGrid val h4)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _), coverageHistogram]
  apply Finset.sum_congr rfl
  intro u _
  by_cases ha : gridCoverage u = a
  · rw [if_pos ha, ← maxGrid_fiber val hW h4 hj u]
    congr 1
    ext E
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by rw [coverCount_grid val hW h4, h, ha], h⟩
  · rw [if_neg ha]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro E h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    apply ha
    rw [← h.2, ← coverCount_grid val hW h4]
    exact h.1

noncomputable def maxHistT (hb : ℕ) (c : T6) : T6 → ℕ :=
  T6.rec (motive := fun _ => T6 → ℕ)
    (fun cv g => T6.casesOn g (fun gv => gv * hb ^ cv) (fun _ _ _ _ _ _ => 0))
    (fun _ _ _ _ _ _ _ r1 r2 r3 r4 r5 g => T6.casesOn g (fun _ => 0)
      (fun g0 g1 g2 g3 g4 _ => r1 g0 + r2 g1 + r3 g2 + r4 g3 + r5 g4)) c

theorem maxHistT_leaf (hb cv gv : ℕ) : maxHistT hb (.leaf cv) (.leaf gv) = gv * hb ^ cv := rfl

theorem maxHistT_node (hb : ℕ) (c0 c1 c2 c3 c4 c5 g0 g1 g2 g3 g4 g5 : T6) :
    maxHistT hb (.node c0 c1 c2 c3 c4 c5) (.node g0 g1 g2 g3 g4 g5) =
      maxHistT hb c1 g0 + maxHistT hb c2 g1 + maxHistT hb c3 g2 + maxHistT hb c4 g3 + maxHistT hb c5 g4 := rfl

theorem sum_fin5_cons {M : Type*} [AddCommMonoid M] {n : ℕ} (F : (Fin (n + 1) → Fin 5) → M) :
    ∑ u, F u = ∑ t : Fin 5, ∑ u : Fin n → Fin 5, F (Fin.cons t u) := by
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  rfl

theorem gridCast_cons {n : ℕ} (t : Fin 5) (u : Fin n → Fin 5) :
    gridCast (Fin.cons t u) = Fin.cons ⟨t.val, by omega⟩ (gridCast u) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

theorem gridUp_cons {n : ℕ} (t : Fin 5) (u : Fin n → Fin 5) :
    gridUp (Fin.cons t u) = Fin.cons ⟨t.val + 1, by omega⟩ (gridUp u) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

theorem maxHistT_eq (hb : ℕ) : ∀ n c g, Full n c → Full n g →
    maxHistT hb c g = ∑ u : Fin n → Fin 5,
      lookup g (digitsOf (gridCast u)) * hb ^ lookup c (digitsOf (gridUp u))
  | 0, .leaf cv, .leaf gv, _, _ => by
    rw [maxHistT_leaf, Fintype.sum_unique]
    rfl
  | n + 1, .node c0 c1 c2 c3 c4 c5, .node g0 g1 g2 g3 g4 g5, hc, hg => by
    have e0 := maxHistT_eq hb n c1 g0 hc.2.1 hg.1
    have e1 := maxHistT_eq hb n c2 g1 hc.2.2.1 hg.2.1
    have e2 := maxHistT_eq hb n c3 g2 hc.2.2.2.1 hg.2.2.1
    have e3 := maxHistT_eq hb n c4 g3 hc.2.2.2.2.1 hg.2.2.2.1
    have e4 := maxHistT_eq hb n c5 g4 hc.2.2.2.2.2 hg.2.2.2.2.1
    rw [sum_fin5_cons, Fin.sum_univ_five, maxHistT_node, e0, e1, e2, e3, e4]
    simp only [gridCast_cons, gridUp_cons, digitsOf_cons, lookup_node_cons]
    rfl

noncomputable def coveragePacked (hb j : ℕ) : ℕ := maxHistT hb cntT (maxCountTree j)

theorem coveragePacked_eq (hb j : ℕ) : coveragePacked hb j =
    ∑ u : Fin 6 → Fin 5,
      lookup (maxCountTree j) (digitsOf (gridCast u)) * hb ^ gridCoverage u := by
  exact maxHistT_eq hb 6 cntT (maxCountTree j) full_cntT
    (full_dT 6 _ (full_mapT _ 6 cntT full_cntT))

open ClaudeWCT.Numerics
noncomputable def coveredTargets (val : β → Fin 6 → ℕ) {j : ℕ} (E : Fin j → β) : ℕ :=
  #{x : β | CoversT val (val x) E}

theorem coversT_maxWord (val : β → Fin 6 → ℕ) {j : ℕ} (hj : 0 < j)
    (E : Fin j → β) (v : Fin 6 → ℕ) : CoversT val v E ↔ ∀ i, v i ≤ maxWord val E i := by
  constructor
  · intro h i
    obtain ⟨k, hk⟩ := h i
    exact le_trans hk (Finset.le_sup (f := fun k => val (E k) i) (Finset.mem_univ k))
  · intro h i
    have hs : (Finset.univ : Finset (Fin j)).Nonempty := ⟨⟨0, hj⟩, Finset.mem_univ _⟩
    obtain ⟨k, _, hk⟩ := Finset.sup_mem_of_nonempty (f := fun k => val (E k) i) hs
    change val (E k) i = maxWord val E i at hk
    exact ⟨k, (h i).trans_eq hk.symm⟩

theorem coveredTargets_pos (val : β → Fin 6 → ℕ) {j : ℕ} (hj : 0 < j) (E : Fin j → β) :
    coveredTargets val E = coverCount val E := by
  classical
  unfold coveredTargets coverCount
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, coversT_maxWord val hj]

theorem coveredTargets_zero (val : β → Fin 6 → ℕ) (E : Fin 0 → β) : coveredTargets val E = 0 := by
  classical
  unfold coveredTargets
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x h
  obtain ⟨i, _⟩ := (Finset.mem_filter.mp h).2 0
  exact i.elim0

noncomputable def coverageLaw (j a : ℕ) : ℕ := if j = 0 then if a = 0 then 1 else 0 else coverageHistogram j a

def FullCoverageHistogram (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) : Prop :=
  ∀ j a, #{E : Fin j → β | coveredTargets val E = a} = H j a

theorem coverageLaw_correct (val : β → Fin 6 → ℕ) (hW : WordsOf val)
    (h4 : ∀ x i, val x i ≤ 4) : FullCoverageHistogram val coverageLaw := by
  intro j a
  classical
  cases j with
  | zero =>
    by_cases ha : a = 0
    · subst a; simp [coverageLaw, coveredTargets_zero]
    · simp [coverageLaw, coveredTargets_zero, ha, Ne.symm ha]
  | succ j =>
    simp only [coverageLaw, Nat.succ_ne_zero, if_false]
    simp_rw [coveredTargets_pos val (Nat.succ_pos j)]
    exact coverageHistogram_eq val hW h4 (Nat.succ_pos j) a

section Occupancy
variable {C : Type*} [Fintype C] [DecidableEq C] {r : ℕ}
noncomputable def fiberIndex (o : Fin r → C) (c : C) : {i : Fin r // o i = c} ≃ Fin (occ o c) :=
  Fintype.equivFinOfCardEq (by simp [occ, Fintype.card_subtype])

noncomputable def splitRanks (o : Fin r → C) : (Fin r → β) ≃ ((c : C) → Fin (occ o c) → β) :=
  Equiv.piCongrFiberwise (fun c => Equiv.piCongrLeft (fun _ => β) (fiberIndex o c))

noncomputable def childCoverage (val : β → Fin 6 → ℕ) (o : Fin r → C) (R : Fin r → β) (c : C) : ℕ :=
  coveredTargets val (splitRanks o R c)

theorem childCoverage_histogram (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ)
    (hH : FullCoverageHistogram val H) (o : Fin r → C) (a : C → ℕ) :
    #{R : Fin r → β | ∀ c, childCoverage val o R c = a c} = ∏ c, H (occ o c) (a c) := by
  classical
  have he : #{R : Fin r → β | ∀ c, childCoverage val o R c = a c} =
      #{S : (c : C) → Fin (occ o c) → β | ∀ c, coveredTargets val (S c) = a c} := by
    refine Finset.card_bij (fun R _ => splitRanks o R) ?_ ?_ ?_
    · intro R hR
      have hp := (Finset.mem_filter.mp hR).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
    · intro R hR S hS heq
      exact (splitRanks o).injective heq
    · intro S hS
      refine ⟨(splitRanks o).symm S, ?_, (splitRanks o).apply_symm_apply S⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro c
      change coveredTargets val ((splitRanks o) ((splitRanks o).symm S) c) = a c
      rw [Equiv.apply_symm_apply]
      exact (Finset.mem_filter.mp hS).2 c
  rw [he]
  have hs : ({S : (c : C) → Fin (occ o c) → β | ∀ c, coveredTargets val (S c) = a c} : Finset _) =
      Fintype.piFinset (fun c => {R : Fin (occ o c) → β | coveredTargets val R = a c}) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  rw [hs, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro c _
  exact hH (occ o c) (a c)

theorem splitRanks_apply (o : Fin r → C) (R : Fin r → β) (c : C) (k : Fin (occ o c)) :
    splitRanks o R c k = R ((fiberIndex o c).symm k).val := by
  simp [splitRanks, Equiv.piCongrLeft_apply]

theorem coversT_splitRanks (val : β → Fin 6 → ℕ) (o : Fin r → C) (R : Fin r → β)
    (c : C) (v : Fin 6 → ℕ) :
    CoversT val v (splitRanks o R c) ↔ Thinning.CovAt val c v (fun i => (o i, R i)) := by
  constructor
  · intro h i
    obtain ⟨k, hk⟩ := h i
    let z := (fiberIndex o c).symm k
    exact ⟨z.val, z.property, by simpa only [splitRanks_apply] using hk⟩
  · intro h i
    obtain ⟨k, hk, hv⟩ := h i
    refine ⟨fiberIndex o c ⟨k, hk⟩, ?_⟩
    simpa only [splitRanks_apply, Equiv.symm_apply_apply] using hv

theorem childCoverage_le (val : β → Fin 6 → ℕ) (o : Fin r → C) (R : Fin r → β) (c : C) :
    childCoverage val o R c ≤ Fintype.card β := Finset.card_filter_le _ _

noncomputable def childCoverageFin (val : β → Fin 6 → ℕ) (o : Fin r → C) (R : Fin r → β) :
    C → Fin (Fintype.card β + 1) := fun c =>
  ⟨childCoverage val o R c, Nat.lt_succ_of_le (childCoverage_le val o R c)⟩

theorem childCoverageFin_histogram (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ)
    (hH : FullCoverageHistogram val H) (o : Fin r → C) (a : C → Fin (Fintype.card β + 1)) :
    #{R : Fin r → β | childCoverageFin val o R = a} = ∏ c, H (occ o c) (a c) := by
  classical
  rw [← childCoverage_histogram val H hH o (fun c => (a c).val)]
  congr 1
  ext R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Fin.ext_iff, childCoverageFin]

theorem sum_childCoverage {M : Type*} [AddCommMonoid M]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (o : Fin r → C) (F : (C → Fin (Fintype.card β + 1)) → M) :
    ∑ R : Fin r → β, F (childCoverageFin val o R) =
      ∑ a : C → Fin (Fintype.card β + 1), (∏ c, H (occ o c) (a c)) • F a := by
  classical
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := childCoverageFin val o)
    (fun _ _ => mem_univ _)]
  apply sum_congr rfl
  intro a _
  rw [sum_congr rfl (g := fun _ => F a) (fun R hR => by rw [(mem_filter.mp hR).2]), sum_const,
    childCoverageFin_histogram val H hH o a]

theorem sum_occupancy_coverage {M : Type*} [AddCommMonoid M]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (F : (C → ℕ) → (C → Fin (Fintype.card β + 1)) → M) :
    ∑ o : Fin r → C, ∑ R : Fin r → β, F (occ o) (childCoverageFin val o R) =
      ∑ k ∈ piAntidiag univ r, Nat.multinomial univ k •
        (∑ a : C → Fin (Fintype.card β + 1), (∏ c, H (k c) (a c)) • F k a) := by
  classical
  calc
    _ = ∑ o : Fin r → C, ∑ a : C → Fin (Fintype.card β + 1),
        (∏ c, H (occ o c) (a c)) • F (occ o) a :=
      sum_congr rfl fun o _ => sum_childCoverage val H hH o (F (occ o))
    _ = _ := sum_occ (α := C) (n := r) (M := M) (fun k =>
      ∑ a : C → Fin (Fintype.card β + 1), (∏ c, H (k c) (a c)) • F k a)
end Occupancy

section Profiles
open ClaudeWCT.Numerics

theorem sum_piAntidiag_bounded {M : Type*} [AddCommMonoid M] (n r : ℕ) (F : (Fin n → ℕ) → M) :
    ∑ k ∈ piAntidiag univ r, F k =
      ∑ u : Fin n → Fin (r + 1), if (∑ i, (u i).val) = r then F (fun i => (u i).val) else 0 := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun u _ => fun i => (u i).val) ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_piAntidiag]
    exact ⟨(Finset.mem_filter.mp hu).2, fun i _ => Finset.mem_univ i⟩
  · intro u hu v hv h
    funext i
    apply Fin.ext
    exact congrFun h i
  · intro k hk
    have hsum := (Finset.mem_piAntidiag.mp hk).1
    have hb : ∀ i, k i < r + 1 := by
      intro i
      have hi : k i ≤ ∑ j, k j := Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
      simpa only [hsum] using Nat.lt_succ_of_le hi
    refine ⟨fun i => ⟨k i, hb i⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsum⟩
  · intro u hu
    rfl

theorem occupancy_profile_sum {R : Type*} [CommSemiring R] (n r : ℕ) (P : ℕ → R) :
    (∑ k ∈ piAntidiag (univ : Finset (Fin n)) r,
      (Nat.multinomial univ k : R) * ∏ i, P (k i)) =
      ∑ m ∈ piAntidiag (univ : Finset (Fin (r + 1))) n,
        if (∑ a, m a * a.val) = r then
          (Nat.multinomial univ m : R) *
            (r.factorial / (∏ a : Fin (r + 1), a.val.factorial ^ m a) : ℕ) *
              ∏ a : Fin (r + 1), P a.val ^ m a
        else 0 := by
  classical
  rw [sum_piAntidiag_bounded n r]
  let Ψ : (Fin (r + 1) → ℕ) → R := fun m =>
    if (∑ a, m a * a.val) = r then
      (r.factorial / (∏ a : Fin (r + 1), a.val.factorial ^ m a) : ℕ) *
        ∏ a : Fin (r + 1), P a.val ^ m a
    else 0
  have ht : ∀ u : Fin n → Fin (r + 1),
      (if (∑ i, (u i).val) = r then
        (Nat.multinomial univ (fun i => (u i).val) : R) * ∏ i, P (u i).val else 0) = Ψ (occ u) := by
    intro u
    dsimp [Ψ]
    rw [← sum_eq_sum_mul_occ (fun a : Fin (r + 1) => a.val) u]
    by_cases hs : (∑ i, (u i).val) = r
    · rw [if_pos hs, if_pos hs, Nat.multinomial, hs,
        prod_eq_prod_pow_occ (fun a : Fin (r + 1) => a.val.factorial) u,
        prod_eq_prod_pow_occ (fun a : Fin (r + 1) => P a.val) u]
    · rw [if_neg hs, if_neg hs]
  rw [Finset.sum_congr rfl (fun u _ => ht u), sum_occ Ψ]
  apply Finset.sum_congr rfl
  intro m hm
  dsimp [Ψ]
  by_cases hs : (∑ a, m a * a.val) = r
  · rw [if_pos hs, if_pos hs]
    simp only [nsmul_eq_mul, Nat.cast_id, mul_assoc]
  · rw [if_neg hs, if_neg hs, smul_zero]
end Profiles

section HistogramReflection
open Polynomial
noncomputable def coveragePoly (j : ℕ) : ℕ[X] :=
  ∑ u : Fin 6 → Fin 5,
    Polynomial.C (lookup (maxCountTree j) (digitsOf (gridCast u))) * Polynomial.X ^ gridCoverage u

noncomputable def naturalDataPoly (d : List (ℕ × ℕ)) : ℕ[X] :=
  (d.map fun e => Polynomial.C e.2 * Polynomial.X ^ e.1).sum

theorem coveragePoly_eval (hb j : ℕ) : (coveragePoly j).eval hb = coveragePacked hb j := by
  simp only [coveragePoly, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, coveragePacked_eq]

theorem coveragePoly_coeff (j a : ℕ) : (coveragePoly j).coeff a = coverageHistogram j a := by
  simp only [coveragePoly, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    coverageHistogram, eq_comm]

theorem coveragePacked_mass (val : β → Fin 6 → ℕ) (hW : WordsOf val)
    (h4 : ∀ x i, val x i ≤ 4) {j : ℕ} (hj : 0 < j) :
    coveragePacked 1 j = Fintype.card β ^ j := by
  classical
  rw [coveragePacked_eq]
  simp only [one_pow, mul_one]
  simp_rw [← maxGrid_fiber val hW h4 hj]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp

theorem naturalDataPoly_eval (d : List (ℕ × ℕ)) (hb : ℕ) :
    (naturalDataPoly d).eval hb = d.foldr (fun e s => e.2 * hb ^ e.1 + s) 0 := by
  induction d with
  | nil => simp [naturalDataPoly]
  | cons e d ih => simp [naturalDataPoly, Polynomial.eval_add] at ih ⊢; exact ih

theorem foldl_add_snd (d : List (ℕ × ℕ)) (n : ℕ) :
    d.foldl (fun s e => s + e.2) n = n + (d.map Prod.snd).sum := by
  induction d generalizing n with
  | nil => simp
  | cons e d ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, Nat.add_assoc]

theorem naturalDataPoly_coeff (d : List (ℕ × ℕ)) (a : ℕ) :
    (naturalDataPoly d).coeff a = (d.filter (fun e => e.1 == a)).foldl (fun s e => s + e.2) 0 := by
  rw [foldl_add_snd, zero_add]
  induction d with
  | nil => simp [naturalDataPoly]
  | cons e d ih =>
    by_cases he : e.1 = a
    · simp [naturalDataPoly, Polynomial.coeff_C_mul_X_pow, he] at ih ⊢
      exact ih
    · simp [naturalDataPoly, Polynomial.coeff_C_mul_X_pow, he, Ne.symm he] at ih ⊢
      exact ih

theorem coverageHistogram_of_packed (j : ℕ)
    (hpacked : coveragePacked (2 ^ 128) j = coverageHPack (2 ^ 128) j)
    (hmass : coveragePacked 1 j < 2 ^ 127)
    (hdmass : coverageHPack 1 j < 2 ^ 127) (a : ℕ) :
    coverageHistogram j a = coverageHAt j a := by
  have hEval : (coveragePoly j).eval (2 ^ 128) = (naturalDataPoly (coverageHData j)).eval (2 ^ 128) := by
    rw [coveragePoly_eval, naturalDataPoly_eval]
    exact hpacked
  have hpol : coveragePoly j = naturalDataPoly (coverageHData j) :=
    ClaudeWCT.Numerics.eq_of_eval_eq (by norm_num [Kernel.HB]) (fun k => Kernel.coeff_lt_of_eval_one (by
      rw [coveragePoly_eval]; exact hmass) k) (fun k => Kernel.coeff_lt_of_eval_one (by
      rw [naturalDataPoly_eval]; exact hdmass) k) hEval
  rw [← coveragePoly_coeff, hpol, naturalDataPoly_coeff]
  rfl
end HistogramReflection

section CoordinateLaw
variable {C : Type*} [Fintype C] [DecidableEq C] {r : ℕ}

noncomputable def atChildCoverage (val : β → Fin 6 → ℕ) (E : Fin r → C × β) (c : C) : ℕ :=
  #{x : β | Thinning.CovAt val c (val x) E}

noncomputable def coordinateCoverage (val : β → Fin 6 → ℕ) (E : Fin r → C × β) : ℕ :=
  #{x : C × β | Thinning.CovAt val x.1 (val x.2) E}

theorem coordinateCoverage_sum (val : β → Fin 6 → ℕ) (E : Fin r → C × β) :
    coordinateCoverage val E = ∑ c, atChildCoverage val E c := by
  classical
  unfold coordinateCoverage atChildCoverage
  rw [Finset.card_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro c _
  rw [Finset.card_filter]

noncomputable def colorWordEquiv (e : C ≃ C) : (Fin r → C × β) ≃ (Fin r → C × β) :=
  Equiv.piCongrRight (fun _ => Equiv.prodCongr e (Equiv.refl β))

theorem covAt_colorWord (val : β → Fin 6 → ℕ) (e : C ≃ C) (E : Fin r → C × β)
    (c : C) (v : Fin 6 → ℕ) :
    Thinning.CovAt val c v (colorWordEquiv e E) ↔ Thinning.CovAt val (e.symm c) v E := by
  unfold Thinning.CovAt
  apply forall_congr'
  intro i
  apply exists_congr
  intro k
  change (e (E k).1 = c ∧ v i ≤ val (E k).2 i) ↔ ((E k).1 = e.symm c ∧ v i ≤ val (E k).2 i)
  rw [Equiv.apply_eq_iff_eq_symm_apply]

theorem atChildCoverage_colorWord (val : β → Fin 6 → ℕ) (e : C ≃ C) (E : Fin r → C × β) (c : C) :
    atChildCoverage val (colorWordEquiv e E) c = atChildCoverage val E (e.symm c) := by
  classical
  unfold atChildCoverage
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, covAt_colorWord]

theorem coordinateCoverage_colorWord (val : β → Fin 6 → ℕ) (e : C ≃ C) (E : Fin r → C × β) :
    coordinateCoverage val (colorWordEquiv e E) = coordinateCoverage val E := by
  rw [coordinateCoverage_sum, coordinateCoverage_sum]
  simp_rw [atChildCoverage_colorWord]
  exact e.symm.sum_comp _

noncomputable def markedCoverageCount (val : β → Fin 6 → ℕ) (r : ℕ) (c : C) (a : ℕ) : ℕ :=
  ∑ E : Fin r → C × β, if coordinateCoverage val E = a then atChildCoverage val E c else 0

theorem markedCoverageCount_color (val : β → Fin 6 → ℕ) (r : ℕ) (c d : C) (a : ℕ) :
    markedCoverageCount val r c a = markedCoverageCount val r d a := by
  classical
  have h := (colorWordEquiv (β := β) (r := r) (Equiv.swap c d)).sum_comp
    (fun E => if coordinateCoverage val E = a then atChildCoverage val E d else 0)
  simp only [coordinateCoverage_colorWord, atChildCoverage_colorWord, Equiv.symm_swap, Equiv.swap_apply_right] at h
  exact h

theorem markedCoverageCount_weighted (val : β → Fin 6 → ℕ) (r : ℕ) (c : C) (a : ℕ) :
    Fintype.card C * markedCoverageCount val r c a =
      a * #{E : Fin r → C × β | coordinateCoverage val E = a} := by
  classical
  calc
    _ = ∑ d : C, markedCoverageCount val r d a := by
      rw [sum_congr rfl (g := fun _ => markedCoverageCount val r c a)
        (fun d _ => markedCoverageCount_color val r d c a), sum_const, card_univ, smul_eq_mul]
    _ = ∑ E : Fin r → C × β, if coordinateCoverage val E = a then coordinateCoverage val E else 0 := by
      unfold markedCoverageCount
      rw [sum_comm]
      apply sum_congr rfl
      intro E _
      by_cases he : coordinateCoverage val E = a
      · simp only [he, if_true, ← coordinateCoverage_sum]
      · simp only [he, if_false, sum_const_zero]
    _ = _ := by
      rw [Finset.card_filter, mul_sum]
      apply sum_congr rfl
      intro E _
      by_cases he : coordinateCoverage val E = a <;> simp [he]

theorem retainedCoverage_weighted (val : β → Fin 6 → ℕ) (r : ℕ) (c : C) (a D : ℕ)
    (hD : D ≤ markedCoverageCount val r c a) :
    Fintype.card C * D ≤ a * #{E : Fin r → C × β | coordinateCoverage val E = a} := by
  rw [← markedCoverageCount_weighted val r c a]
  exact Nat.mul_le_mul_left _ hD
end CoordinateLaw

section ProfileRefinement


theorem multinomial_fin_cons {n : ℕ} (j : ℕ) (k : Fin n → ℕ) :
    Nat.multinomial univ (Fin.cons j k) =
      (j + ∑ i, k i).choose j * Nat.multinomial univ k := by
  rw [Nat.multinomial, Nat.div_eq_iff_eq_mul_left _ (Nat.prod_factorial_dvd_factorial_sum _ _)]
  · simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ]
    rw [Nat.multinomial, mul_assoc, mul_left_comm _ j.factorial,
      Nat.div_mul_cancel (Nat.prod_factorial_dvd_factorial_sum _ _), ← mul_assoc,
      Nat.choose_symm_add, Nat.add_choose_mul_factorial_mul_factorial]
  · positivity

theorem sum_piAntidiag_cons {M : Type*} [AddCommMonoid M] (n r : ℕ)
    (F : (Fin (n+1) → ℕ) → M) :
    ∑ k ∈ piAntidiag univ r, F k =
      ∑ j ∈ range (r+1), ∑ k ∈ piAntidiag univ (r-j), F (Fin.cons j k) := by
  classical
  symm
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hj, hk⟩ := Finset.mem_sigma.mp hp
    have hjr : p.1 ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsum := (Finset.mem_piAntidiag.mp hk).1
    rw [Finset.mem_piAntidiag]
    constructor
    · simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hsum] using
        Nat.add_sub_of_le hjr
    · intro i _
      exact Finset.mem_univ i
  · intro p hp q hq he
    have hj : p.1 = q.1 := by simpa using congrFun he 0
    have hk : p.2 = q.2 := by funext i; simpa using congrFun he i.succ
    exact Sigma.ext hj (heq_of_eq hk)
  · intro k hk
    have hsum := (Finset.mem_piAntidiag.mp hk).1
    have hs : k 0 + ∑ i : Fin n, k i.succ = r := by simpa [Fin.sum_univ_succ] using hsum
    refine ⟨⟨k 0, fun i : Fin n => k i.succ⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      constructor
      · apply Finset.mem_range.mpr
        change k 0 < r + 1
        omega
      · apply Finset.mem_piAntidiag.mpr
        exact ⟨by change (∑ i : Fin n, k i.succ) = r - k 0; omega, fun i _ => Finset.mem_univ i⟩
    · funext i
      exact Fin.cases rfl (fun _ => rfl) i
  · intro p hp
    rfl

variable {β C : Type*} [Fintype β] [Fintype C] [DecidableEq C] {r : ℕ}
theorem sum_childCoverage_product {R : Type*} [CommSemiring R]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (o : Fin r → C) (G : C → Fin (Fintype.card β + 1) → R) :
    (∑ B : Fin r → β, ∏ c, G c (childCoverageFin val o B c)) =
      ∏ c, ∑ a : Fin (Fintype.card β + 1), (H (occ o c) a : R) * G c a := by
  classical
  rw [sum_childCoverage val H hH o (fun a => ∏ c, G c (a c)), Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [nsmul_eq_mul, Nat.cast_prod, Finset.prod_mul_distrib]


noncomputable def atChildCoverageFin (val : β → Fin 6 → ℕ) (E : Fin r → C × β) :
    C → Fin (Fintype.card β + 1) := fun c =>
  ⟨atChildCoverage val E c, Nat.lt_succ_of_le (Finset.card_filter_le _ _)⟩

theorem childCoverage_pair (val : β → Fin 6 → ℕ) (o : Fin r → C) (B : Fin r → β) (c : C) :
    childCoverage val o B c = atChildCoverage val (fun i => (o i, B i)) c := by
  classical
  unfold childCoverage coveredTargets atChildCoverage
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, coversT_splitRanks]

theorem sum_word_product {R : Type*} [CommSemiring R]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (G : C → Fin (Fintype.card β + 1) → R) :
    (∑ E : Fin r → C × β, ∏ c, G c (atChildCoverageFin val E c)) =
      ∑ k ∈ piAntidiag univ r, (Nat.multinomial univ k : R) *
        ∏ c, ∑ a : Fin (Fintype.card β + 1), (H (k c) a : R) * G c a := by
  classical
  let e := Equiv.arrowProdEquivProdArrow (Fin r) (fun _ => C) (fun _ => β)
  calc
    _ = ∑ o : Fin r → C, ∑ B : Fin r → β, ∏ c, G c (childCoverageFin val o B c) := by
      rw [← Fintype.sum_prod_type (fun p : (Fin r → C) × (Fin r → β) =>
        ∏ c, G c (childCoverageFin val p.1 p.2 c))]
      have he := e.symm.sum_comp (fun E => ∏ c, G c (atChildCoverageFin val E c))
      rw [← he]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.prod_congr rfl
      intro c _
      congr 1
      apply Fin.ext
      exact (childCoverage_pair val p.1 p.2 c).symm
    _ = ∑ o : Fin r → C, ∏ c, ∑ a : Fin (Fintype.card β + 1), (H (occ o c) a : R) * G c a :=
      Finset.sum_congr rfl fun o _ => sum_childCoverage_product val H hH o G
    _ = _ := by
      simpa only [nsmul_eq_mul] using sum_occ (α := C) (n := r)
        (fun k => ∏ c, ∑ a : Fin (Fintype.card β + 1), (H (k c) a : R) * G c a)


open Polynomial
noncomputable def coverageProfilePoly (ms : List ℕ) : ℕ[X] :=
  (ms.zipIdx 2).foldr (fun e s => naturalDataPoly (coverageHData e.2) ^ e.1 * s) 1
noncomputable def coverageOtherPoly (n : ℕ) : ℕ[X] :=
  coverageProfiles.foldr (fun ms acc =>
    if coverageProfileUsed ms ≤ n then
      Polynomial.C (coverageProfileCount n ms * 563 ^ (n - coverageProfileUsed ms)) *
        X ^ (n - coverageProfileUsed ms) * coverageProfilePoly ms + acc
    else acc) 0
noncomputable def coverageMarkedPoly (j : ℕ) : ℕ[X] :=
  (coverageHData j).foldr (fun e s => Polynomial.C (e.1 * e.2) * X ^ e.1 + s) 0
noncomputable def retainedCoveragePoly (r : ℕ) : ℕ[X] :=
  (List.range 8).foldr (fun j acc =>
    if j + 1 ≤ r then
      Polynomial.C (Kernel.fact r / (Kernel.fact (j+1) * Kernel.fact (r-(j+1)))) *
        coverageMarkedPoly (j+1) * coverageOtherPoly (r-(j+1)) + acc
    else acc) 0

theorem eval_foldr_sum {α : Type*} (l : List α) (f : α → ℕ[X]) (b : ℕ) :
    Polynomial.eval b (l.foldr (fun e s => f e + s) 0) =
      l.foldr (fun e s => Polynomial.eval b (f e) + s) 0 := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]
theorem eval_foldr_prod {α : Type*} (l : List α) (f : α → ℕ[X]) (b : ℕ) :
    Polynomial.eval b (l.foldr (fun e s => f e * s) 1) =
      l.foldr (fun e s => Polynomial.eval b (f e) * s) 1 := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]
theorem coverageProfilePoly_eval (ms : List ℕ) (b : ℕ) :
    Polynomial.eval b (coverageProfilePoly ms) = coverageProfilePack b ms := by
  unfold coverageProfilePoly coverageProfilePack
  rw [eval_foldr_prod]
  simp only [Polynomial.eval_pow, naturalDataPoly_eval, coverageHPack]
theorem coverageMarkedPoly_eval (j b : ℕ) :
    Polynomial.eval b (coverageMarkedPoly j) = coverageMarkedPack b j := by
  unfold coverageMarkedPoly coverageMarkedPack
  rw [eval_foldr_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
theorem coverageOtherPoly_eval (n b : ℕ) :
    Polynomial.eval b (coverageOtherPoly n) = coverageOtherPack b n := by
  unfold coverageOtherPoly coverageOtherPack
  induction coverageProfiles with
  | nil => simp
  | cons ms xs ih =>
    simp only [List.foldr_cons]
    split_ifs with h
    · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, coverageProfilePoly_eval, ih]
    · exact ih
theorem retainedCoveragePoly_eval (r b : ℕ) :
    Polynomial.eval b (retainedCoveragePoly r) = coverageRetainedPack b r := by
  unfold retainedCoveragePoly coverageRetainedPack
  induction List.range 8 with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldr_cons]
    split_ifs with h
    · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        coverageMarkedPoly_eval, coverageOtherPoly_eval, ih]
    · exact ih


end ProfileRefinement

section MoreProfiles
open Polynomial

variable {β : Type*} [Fintype β]
noncomputable def lawPoly (H : ℕ → ℕ → ℕ) (N j : ℕ) : ℕ[X] :=
  ∑ a : Fin (N+1), Polynomial.C (H j a) * X ^ a.val
noncomputable def markedLawPoly (H : ℕ → ℕ → ℕ) (N j : ℕ) : ℕ[X] :=
  ∑ a : Fin (N+1), Polynomial.C (a.val * H j a) * X ^ a.val
noncomputable def markedFullPoly (val : β → Fin 6 → ℕ) (n r : ℕ) : ℕ[X] :=
  ∑ E : Fin r → Fin (n+1) × β,
    Polynomial.C (atChildCoverage val E 0) * X ^ coordinateCoverage val E

theorem markedFullPoly_coeff (val : β → Fin 6 → ℕ) (n r a : ℕ) :
    (markedFullPoly val n r).coeff a = markedCoverageCount val r (0 : Fin (n+1)) a := by
  classical
  simp only [markedFullPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    markedCoverageCount, eq_comm]

theorem markedFullPoly_eq (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ)
    (hH : FullCoverageHistogram val H) (n r : ℕ) :
    markedFullPoly val n r =
      ∑ k ∈ piAntidiag univ r, (Nat.multinomial univ k : ℕ[X]) *
        markedLawPoly H (Fintype.card β) (k 0) *
          ∏ i : Fin n, lawPoly H (Fintype.card β) (k i.succ) := by
  classical
  let G : Fin (n+1) → Fin (Fintype.card β+1) → ℕ[X] :=
    fun c a => if c = 0 then Polynomial.C a.val * X ^ a.val else X ^ a.val
  have h := sum_word_product (r := r) val H hH G
  have hG (a : Fin (n+1) → Fin (Fintype.card β+1)) :
      (∏ c, G c (a c)) = Polynomial.C (a 0).val * X ^ (∑ c, (a c).val) := by
    simp only [G, Fin.prod_univ_succ, if_pos rfl, Fin.succ_ne_zero, if_false, if_true]
    rw [Finset.prod_pow_eq_pow_sum, mul_assoc, ← pow_add, Fin.sum_univ_succ]
  have hl : (∑ E : Fin r → Fin (n+1) × β, ∏ c, G c (atChildCoverageFin val E c)) =
      markedFullPoly val n r := by
    apply Finset.sum_congr rfl
    intro E _
    rw [hG]
    simp only [atChildCoverageFin, coordinateCoverage_sum]
  rw [hl] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Fin.prod_univ_succ]
  have hm : (∑ a : Fin (Fintype.card β+1), (H (k 0) a : ℕ[X]) * G 0 a) =
      markedLawPoly H (Fintype.card β) (k 0) := by
    apply Finset.sum_congr rfl
    intro a _
    simp only [G, if_pos rfl, markedLawPoly]
    have hc (m : ℕ) : (m : ℕ[X]) = Polynomial.C m := by
      simpa using (Polynomial.C_eq_natCast (R := ℕ) m).symm
    rw [hc, Polynomial.C_mul]
    ring
  rw [hm, ← mul_assoc]
  congr 1

noncomputable def fullOtherPoly (H : ℕ → ℕ → ℕ) (N n r : ℕ) : ℕ[X] :=
  ∑ k ∈ piAntidiag (univ : Finset (Fin n)) r,
    (Nat.multinomial univ k : ℕ[X]) * ∏ i, lawPoly H N (k i)

theorem markedFullPoly_split (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ)
    (hH : FullCoverageHistogram val H) (n r : ℕ) :
    markedFullPoly val n r =
      ∑ j ∈ range (r+1), (r.choose j : ℕ[X]) * markedLawPoly H (Fintype.card β) j *
        fullOtherPoly H (Fintype.card β) n (r-j) := by
  classical
  rw [markedFullPoly_eq val H hH, sum_piAntidiag_cons]
  apply Finset.sum_congr rfl
  intro j hj
  unfold fullOtherPoly
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hs := (Finset.mem_piAntidiag.mp hk).1
  have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [Fin.cons_zero, Fin.cons_succ, multinomial_fin_cons, hs,
    Nat.add_sub_of_le hjr, Nat.cast_mul]
  ring


end MoreProfiles

section MoreProfiles
open Polynomial

theorem sum_piAntidiag_bounded_by {M : Type*} [AddCommMonoid M] (n r b : ℕ) (hr : r ≤ b) (F : (Fin n → ℕ) → M) :
    ∑ k ∈ piAntidiag univ r, F k =
      ∑ u : Fin n → Fin (b + 1), if (∑ i, (u i).val) = r then F (fun i => (u i).val) else 0 := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun u _ => fun i => (u i).val) ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_piAntidiag]
    exact ⟨(Finset.mem_filter.mp hu).2, fun i _ => Finset.mem_univ i⟩
  · intro u hu v hv h
    funext i
    apply Fin.ext
    exact congrFun h i
  · intro k hk
    have hsum := (Finset.mem_piAntidiag.mp hk).1
    have hb : ∀ i, k i < b + 1 := by
      intro i
      have hi : k i ≤ ∑ j, k j := Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
      have hir : k i ≤ r := by simpa only [hsum] using hi
      exact Nat.lt_succ_of_le (hir.trans hr)
    refine ⟨fun i => ⟨k i, hb i⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsum⟩
  · intro u hu
    rfl

theorem occupancy_profile_sum_bounded {R : Type*} [CommSemiring R] (n r b : ℕ) (hr : r ≤ b) (P : ℕ → R) :
    (∑ k ∈ piAntidiag (univ : Finset (Fin n)) r,
      (Nat.multinomial univ k : R) * ∏ i, P (k i)) =
      ∑ m ∈ piAntidiag (univ : Finset (Fin (b + 1))) n,
        if (∑ a, m a * a.val) = r then
          (Nat.multinomial univ m : R) *
            (r.factorial / (∏ a : Fin (b + 1), a.val.factorial ^ m a) : ℕ) *
              ∏ a : Fin (b + 1), P a.val ^ m a
        else 0 := by
  classical
  rw [sum_piAntidiag_bounded_by n r b hr]
  let Ψ : (Fin (b + 1) → ℕ) → R := fun m =>
    if (∑ a, m a * a.val) = r then
      (r.factorial / (∏ a : Fin (b + 1), a.val.factorial ^ m a) : ℕ) *
        ∏ a : Fin (b + 1), P a.val ^ m a
    else 0
  have ht : ∀ u : Fin n → Fin (b + 1),
      (if (∑ i, (u i).val) = r then
        (Nat.multinomial univ (fun i => (u i).val) : R) * ∏ i, P (u i).val else 0) = Ψ (occ u) := by
    intro u
    dsimp [Ψ]
    rw [← sum_eq_sum_mul_occ (fun a : Fin (b + 1) => a.val) u]
    by_cases hs : (∑ i, (u i).val) = r
    · rw [if_pos hs, if_pos hs, Nat.multinomial, hs,
        prod_eq_prod_pow_occ (fun a : Fin (b + 1) => a.val.factorial) u,
        prod_eq_prod_pow_occ (fun a : Fin (b + 1) => P a.val) u]
    · rw [if_neg hs, if_neg hs]
  rw [Finset.sum_congr rfl (fun u _ => ht u), sum_occ Ψ]
  apply Finset.sum_congr rfl
  intro m hm
  dsimp [Ψ]
  by_cases hs : (∑ a, m a * a.val) = r
  · rw [if_pos hs, if_pos hs]
    simp only [nsmul_eq_mul, Nat.cast_id, mul_assoc]
  · rw [if_neg hs, if_neg hs, smul_zero]


end MoreProfiles

section RetainedProfiles

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def retainedProfileList (i : Fin 30) : List ℕ := coverageProfiles[i.val]!
def retainedProfileVector (n : ℕ) (ms : List ℕ) (a : Fin 31) : ℕ :=
  if a.val = 0 then 127 - ((n - coverageProfileUsed ms) + coverageProfileGroups ms)
  else if a.val = 1 then n - coverageProfileUsed ms else ms[a.val - 2]!

theorem retainedProfile_product {R : Type*} [CommMonoid R] (n : ℕ) (ms : List ℕ)
    (hms : ms.length = 6) (P : ℕ → R) :
    (∏ a : Fin 31, P a.val ^ retainedProfileVector n ms a) =
      P 0 ^ (127 - ((n - coverageProfileUsed ms) + coverageProfileGroups ms)) *
        P 1 ^ (n - coverageProfileUsed ms) *
          (ms.zipIdx 2).foldr (fun e s => P e.2 ^ e.1 * s) 1 := by
  cases ms with
  | nil => simp at hms
  | cons a ms =>
    cases ms with
    | nil => simp at hms
    | cons b ms =>
      cases ms with
      | nil => simp at hms
      | cons c ms =>
        cases ms with
        | nil => simp at hms
        | cons d ms =>
          cases ms with
          | nil => simp at hms
          | cons e ms =>
            cases ms with
            | nil => simp at hms
            | cons f ms =>
              have hn : ms = [] := List.eq_nil_of_length_eq_zero (by simpa using hms)
              subst ms
              simp [Fin.prod_univ_succ, retainedProfileVector, coverageProfileUsed,
                coverageProfileGroups, List.zipIdx, mul_assoc]


theorem retainedProfile_factorials (n : ℕ) (ms : List ℕ)
    (hms : ms.length = 6)  :
    (∏ a : Fin 31, (retainedProfileVector n ms a).factorial) =
      (127 - ((n - coverageProfileUsed ms) + coverageProfileGroups ms)).factorial *
        (n - coverageProfileUsed ms).factorial *
          ms.foldr (fun m s => m.factorial * s) 1 := by
  cases ms with
  | nil => simp at hms
  | cons a ms =>
    cases ms with
    | nil => simp at hms
    | cons b ms =>
      cases ms with
      | nil => simp at hms
      | cons c ms =>
        cases ms with
        | nil => simp at hms
        | cons d ms =>
          cases ms with
          | nil => simp at hms
          | cons e ms =>
            cases ms with
            | nil => simp at hms
            | cons f ms =>
              have hn : ms = [] := List.eq_nil_of_length_eq_zero (by simpa using hms)
              subst ms
              simp [Fin.prod_univ_succ, retainedProfileVector, coverageProfileUsed,
                coverageProfileGroups, List.zipIdx, mul_assoc]


theorem retainedProfile_small_checks : ∀ n : Fin 31, ∀ i : Fin 30,
    let ms := retainedProfileList i
    coverageProfileUsed ms ≤ n.val →
      (∑ a, retainedProfileVector n.val ms a) = 127 ∧
      (∑ a, retainedProfileVector n.val ms a * a.val) = n.val := by decide +kernel

theorem retainedProfile_length (i : Fin 30) : (retainedProfileList i).length = 6 := by
  fin_cases i <;> decide +kernel

theorem retainedProfile_checks (n : Fin 31) (i : Fin 30)
    (hu : coverageProfileUsed (retainedProfileList i) ≤ n.val) :
      (∑ a, retainedProfileVector n.val (retainedProfileList i) a) = 127 ∧
      (∑ a, retainedProfileVector n.val (retainedProfileList i) a * a.val) = n.val ∧
      Nat.multinomial univ (retainedProfileVector n.val (retainedProfileList i)) *
        (n.val.factorial / ∏ a : Fin 31, a.val.factorial ^ retainedProfileVector n.val (retainedProfileList i) a) =
          coverageProfileCount n.val (retainedProfileList i) := by
  have hs := retainedProfile_small_checks n i hu
  refine ⟨hs.1, hs.2, ?_⟩
  unfold Nat.multinomial
  rw [hs.1, retainedProfile_factorials n.val _ (retainedProfile_length i),
    retainedProfile_product n.val _ (retainedProfile_length i) Nat.factorial]
  simp only [Nat.factorial_zero, Nat.factorial_one, one_pow, one_mul]
  simp only [coverageProfileCount, coverageProfileMultiplicity, coverageProfilePositions, Kernel.fact_eq]

theorem retainedProfile_injective : ∀ n : Fin 31,
    Function.Injective (fun i : Fin 30 => retainedProfileVector n.val (retainedProfileList i)) := by
  decide +kernel


end RetainedProfiles

section RetainedCountBound
open Polynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
noncomputable def coverageOtherTerm (n : ℕ) (ms : List ℕ) : ℕ[X] :=
  if coverageProfileUsed ms ≤ n then
    Polynomial.C (coverageProfileCount n ms * 563 ^ (n - coverageProfileUsed ms)) *
      X ^ (n - coverageProfileUsed ms) * coverageProfilePoly ms else 0

theorem coverageOtherPoly_eq_sum (n : ℕ) :
    coverageOtherPoly n = ∑ i : Fin 30, coverageOtherTerm n (retainedProfileList i) := by
  have hf (l : List (List ℕ)) :
      l.foldr (fun ms acc => if coverageProfileUsed ms ≤ n then
        Polynomial.C (coverageProfileCount n ms * 563 ^ (n - coverageProfileUsed ms)) *
          X ^ (n - coverageProfileUsed ms) * coverageProfilePoly ms + acc else acc) 0 =
        (l.map (coverageOtherTerm n)).sum := by
    induction l with
    | nil => simp
    | cons ms xs ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons, coverageOtherTerm]
      split_ifs with h <;> rw [ih] <;> simp only [zero_add]
  rw [coverageOtherPoly, hf]
  have hlist : coverageProfiles = List.ofFn retainedProfileList := by decide +kernel
  rw [hlist, List.map_ofFn, List.sum_ofFn]
  rfl

theorem profileLawPoly_eq_data (H : ℕ → ℕ → ℕ) (i : Fin 30)
    (hP : ∀ j, 2 ≤ j → j ≤ 7 → lawPoly H 563 j = naturalDataPoly (coverageHData j)) :
    ((retainedProfileList i).zipIdx 2).foldr (fun e s => lawPoly H 563 e.2 ^ e.1 * s) 1 =
      coverageProfilePoly (retainedProfileList i) := by
  have h2 := hP 2 (by decide) (by decide)
  have h3 := hP 3 (by decide) (by decide)
  have h4 := hP 4 (by decide) (by decide)
  have h5 := hP 5 (by decide) (by decide)
  have h6 := hP 6 (by decide) (by decide)
  have h7 := hP 7 (by decide) (by decide)
  fin_cases i <;> simp [retainedProfileList, coverageProfiles, coverageProfilePoly,
    List.zipIdx, h2, h3, h4, h5, h6, h7]

theorem coverageOtherTerm_profile (H : ℕ → ℕ → ℕ) (n : Fin 31) (i : Fin 30)
    (hu : coverageProfileUsed (retainedProfileList i) ≤ n.val)
    (h0 : lawPoly H 563 0 = 1) (h1 : lawPoly H 563 1 = Polynomial.C 563 * X)
    (hP : ∀ j, 2 ≤ j → j ≤ 7 → lawPoly H 563 j = naturalDataPoly (coverageHData j)) :
    coverageOtherTerm n.val (retainedProfileList i) =
      (Nat.multinomial univ (retainedProfileVector n.val (retainedProfileList i)) : ℕ[X]) *
        (n.val.factorial / ∏ a : Fin 31, a.val.factorial ^
          retainedProfileVector n.val (retainedProfileList i) a : ℕ) *
        ∏ a : Fin 31, lawPoly H 563 a.val ^ retainedProfileVector n.val (retainedProfileList i) a := by
  have hc (m : ℕ) : (m : ℕ[X]) = Polynomial.C m := by
    simpa using (Polynomial.C_eq_natCast (R := ℕ) m).symm
  have hn := (retainedProfile_checks n i hu).2.2
  rw [← Nat.cast_mul, hn, hc,
    retainedProfile_product n.val (retainedProfileList i) (retainedProfile_length i),
    h0, h1, one_pow, one_mul, profileLawPoly_eq_data H i hP]
  simp only [coverageOtherTerm, if_pos hu, Polynomial.C_mul, mul_pow, Polynomial.C_pow]
  ring



def CoeffLE (p q : ℕ[X]) : Prop := ∀ a, p.coeff a ≤ q.coeff a

theorem CoeffLE.refl (p : ℕ[X]) : CoeffLE p p := fun _ => le_rfl

theorem CoeffLE.mul (p p' q q' : ℕ[X]) (hp : CoeffLE p p') (hq : CoeffLE q q') :
    CoeffLE (p*q) (p'*q') := by
  intro a
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_le_sum
  intro ij hij
  exact Nat.mul_le_mul (hp ij.1) (hq ij.2)

theorem CoeffLE.sum {α : Type*} (s : Finset α) (p q : α → ℕ[X])
    (h : ∀ i ∈ s, CoeffLE (p i) (q i)) : CoeffLE (∑ i ∈ s, p i) (∑ i ∈ s, q i) := by
  intro a
  simp only [Polynomial.finsetSum_coeff]
  exact Finset.sum_le_sum fun i hi => h i hi a

theorem coeffSum_subset {α : Type*} [DecidableEq α] (s t : Finset α) (h : s ⊆ t)
    (p : α → ℕ[X]) : CoeffLE (∑ i ∈ s, p i) (∑ i ∈ t, p i) := by
  intro a
  simp only [Polynomial.finsetSum_coeff]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)

theorem coeffSum_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β) (hf : Function.Injective f)
    (ht : ∀ i ∈ s, f i ∈ t) (p : β → ℕ[X]) :
    CoeffLE (∑ i ∈ s, p (f i)) (∑ j ∈ t, p j) := by
  rw [← Finset.sum_image (fun a _ b _ h => hf h)]
  apply coeffSum_subset
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  exact ht a ha


attribute [local irreducible] Finset.piAntidiag

set_option maxHeartbeats 200000 in
theorem coverageOtherPoly_below (H : ℕ → ℕ → ℕ) (n : Fin 31)
    (h0 : lawPoly H 563 0 = 1) (h1 : lawPoly H 563 1 = Polynomial.C 563 * X)
    (hP : ∀ j, 2 ≤ j → j ≤ 7 → lawPoly H 563 j = naturalDataPoly (coverageHData j)) :
    CoeffLE (coverageOtherPoly n.val) (fullOtherPoly H 563 127 n.val) := by
  classical
  let v : Fin 30 → Fin 31 → ℕ := fun i => retainedProfileVector n.val (retainedProfileList i)
  let F : (Fin 31 → ℕ) → ℕ[X] := fun m =>
    if (∑ a, m a * a.val) = n.val then
      (Nat.multinomial univ m : ℕ[X]) *
        (n.val.factorial / ∏ a : Fin 31, a.val.factorial ^ m a : ℕ) *
          ∏ a : Fin 31, lawPoly H 563 a.val ^ m a else 0
  let s : Finset (Fin 30) := univ.filter (fun i => coverageProfileUsed (retainedProfileList i) ≤ n.val)
  run_tac Lean.logInfo "coverageOtherPoly_below: entering hf"
  have hf : fullOtherPoly H 563 127 n.val = ∑ m ∈ piAntidiag univ 127, F m := by
    exact occupancy_profile_sum_bounded 127 n.val 30 (by omega) (lawPoly H 563)
  run_tac Lean.logInfo "coverageOtherPoly_below: entering he"
  have he : coverageOtherPoly n.val = ∑ i ∈ s, F (v i) := by
    rw [coverageOtherPoly_eq_sum]
    dsimp [s]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hu : coverageProfileUsed (retainedProfileList i) ≤ n.val
    · rw [if_pos hu]
      dsimp [F, v]
      rw [if_pos (retainedProfile_checks n i hu).2.1]
      exact coverageOtherTerm_profile H n i hu h0 h1 hP
    · rw [if_neg hu]
      simp only [coverageOtherTerm, if_neg hu]
  run_tac Lean.logInfo "coverageOtherPoly_below: entering final bound"
  have hmem : ∀ i ∈ s, v i ∈ piAntidiag univ 127 := by
    intro i hi
    have hu := (Finset.mem_filter.mp hi).2
    rw [Finset.mem_piAntidiag]
    exact ⟨(retainedProfile_checks n i hu).1, fun _ _ => Finset.mem_univ _⟩
  run_tac Lean.logInfo "coverageOtherPoly_below: membership complete"
  have hinj : Function.Injective v := retainedProfile_injective n
  run_tac Lean.logInfo "coverageOtherPoly_below: injection complete"
  rw [he, hf]
  intro a
  simp only [Polynomial.finsetSum_coeff]
  rw [← Finset.sum_image (f := fun m => (F m).coeff a) (s := s) (g := v) hinj.injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    exact hmem i hi
  · intros
    exact Nat.zero_le _

noncomputable def retainedCoverageTerm (r j : ℕ) : ℕ[X] :=
  if j + 1 ≤ r then
    Polynomial.C (Kernel.fact r / (Kernel.fact (j+1) * Kernel.fact (r-(j+1)))) *
      coverageMarkedPoly (j+1) * coverageOtherPoly (r-(j+1)) else 0

theorem retainedCoveragePoly_eq_sum (r : ℕ) :
    retainedCoveragePoly r = ∑ j : Fin 8, retainedCoverageTerm r j.val := by
  have hf (l : List ℕ) :
      l.foldr (fun j acc => if j + 1 ≤ r then
        Polynomial.C (Kernel.fact r / (Kernel.fact (j+1) * Kernel.fact (r-(j+1)))) *
          coverageMarkedPoly (j+1) * coverageOtherPoly (r-(j+1)) + acc else acc) 0 =
        (l.map (retainedCoverageTerm r)).sum := by
    induction l with
    | nil => simp
    | cons j xs ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons, retainedCoverageTerm]
      split_ifs with h <;> rw [ih] <;> simp only [zero_add]
  rw [retainedCoveragePoly, hf]
  have hlist : List.range 8 = List.ofFn (fun j : Fin 8 => j.val) := by decide +kernel
  rw [hlist, List.map_ofFn, List.sum_ofFn]
  rfl

theorem CoeffLE.trans {p q r : ℕ[X]} (hp : CoeffLE p q) (hq : CoeffLE q r) : CoeffLE p r :=
  fun a => (hp a).trans (hq a)

theorem retainedCoveragePoly_below {β : Type*} [Fintype β]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (hcard : Fintype.card β = 563) (r : Fin 31)
    (h0 : lawPoly H 563 0 = 1) (h1 : lawPoly H 563 1 = Polynomial.C 563 * X)
    (hP : ∀ j, 2 ≤ j → j ≤ 7 → lawPoly H 563 j = naturalDataPoly (coverageHData j))
    (hM : ∀ j, 1 ≤ j → j ≤ 8 → markedLawPoly H 563 j = coverageMarkedPoly j) :
    CoeffLE (retainedCoveragePoly r.val) (markedFullPoly val 127 r.val) := by
  classical
  let F : ℕ → ℕ[X] := fun j => (r.val.choose j : ℕ[X]) * markedLawPoly H 563 j *
    fullOtherPoly H 563 127 (r.val-j)
  let s : Finset (Fin 8) := univ.filter (fun j => j.val + 1 ≤ r.val)
  have he : retainedCoveragePoly r.val = ∑ j ∈ s, retainedCoverageTerm r.val j.val := by
    rw [retainedCoveragePoly_eq_sum]
    dsimp [s]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : j.val + 1 ≤ r.val
    · rw [if_pos h]
    · simp [retainedCoverageTerm, h]
  have ht : ∀ j ∈ s, CoeffLE (retainedCoverageTerm r.val j.val) (F (j.val+1)) := by
    intro j hj
    have hu := (Finset.mem_filter.mp hj).2
    have hn : r.val-(j.val+1) < 31 := lt_of_le_of_lt (Nat.sub_le _ _) r.isLt
    have hm := hM (j.val+1) (by omega) (by omega)
    simp only [retainedCoverageTerm, if_pos hu, Kernel.fact_eq,
      ← Nat.choose_eq_factorial_div_factorial hu]
    have hc (m : ℕ) : (m : ℕ[X]) = Polynomial.C m := by
      simpa using (Polynomial.C_eq_natCast (R := ℕ) m).symm
    dsimp [F]
    rw [hc, hm]
    exact CoeffLE.mul _ _ _ _ (CoeffLE.refl _) (coverageOtherPoly_below H ⟨_, hn⟩ h0 h1 hP)
  rw [he]
  apply (CoeffLE.sum s _ _ ht).trans
  have hinj : Function.Injective (fun j : Fin 8 => j.val+1) := by
    intro a b h
    apply Fin.ext
    change a.val + 1 = b.val + 1 at h
    omega
  have hsub := coeffSum_injective s (range (r.val+1)) (fun j : Fin 8 => j.val+1) hinj
    (fun j hj => Finset.mem_range.mpr (by have h := (Finset.mem_filter.mp hj).2; omega)) F
  have hf : markedFullPoly val 127 r.val = ∑ j ∈ range (r.val+1), F j := by
    simpa only [hcard] using markedFullPoly_split val H hH 127 r.val
  rw [hf]
  exact hsub

theorem retainedCoverage_count_bound {β : Type*} [Fintype β]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (hcard : Fintype.card β = 563) (r : Fin 31)
    (h0 : lawPoly H 563 0 = 1) (h1 : lawPoly H 563 1 = Polynomial.C 563 * X)
    (hP : ∀ j, 2 ≤ j → j ≤ 7 → lawPoly H 563 j = naturalDataPoly (coverageHData j))
    (hM : ∀ j, 1 ≤ j → j ≤ 8 → markedLawPoly H 563 j = coverageMarkedPoly j) (a : ℕ) :
    128 * (retainedCoveragePoly r.val).coeff a ≤
      a * #{E : Fin r.val → Fin 128 × β | coordinateCoverage val E = a} := by
  have h := retainedCoveragePoly_below val H hH hcard r h0 h1 hP hM a
  rw [markedFullPoly_coeff] at h
  exact retainedCoverage_weighted val r.val (0 : Fin 128) a _ h

end RetainedCountBound
end ClaudeWCT.Numerics.N600

open Finset Polynomial
namespace ClaudeWCT.Numerics.N600
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem lawPoly_coeff (H : ℕ → ℕ → ℕ) (N j a : ℕ) :
    (lawPoly H N j).coeff a = if a ≤ N then H j a else 0 := by
  classical
  simp only [lawPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  by_cases ha : a ≤ N
  · rw [if_pos ha]
    let v : Fin (N+1) := ⟨a, by omega⟩
    rw [Finset.sum_eq_single v]
    · simp [v]
    · intro b hb hne
      have hab : a ≠ b.val := fun he => hne (Fin.ext he.symm)
      simp [hab]
    · simp
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro b hb
    have hab : a ≠ b.val := by have := b.isLt; omega
    simp [hab]

theorem markedLawPoly_coeff (H : ℕ → ℕ → ℕ) (N j a : ℕ) :
    (markedLawPoly H N j).coeff a = a * (lawPoly H N j).coeff a := by
  classical
  simp only [markedLawPoly, lawPoly, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases ha : a = b.val <;> simp [ha]

theorem weightedDataPoly_coeff (d : List (ℕ × ℕ)) (a : ℕ) :
    ((d.foldr (fun e s => Polynomial.C (e.1 * e.2) * X ^ e.1 + s) 0 : ℕ[X]).coeff a) =
      a * (naturalDataPoly d).coeff a := by
  induction d with
  | nil => simp [naturalDataPoly]
  | cons e es ih =>
    simp only [List.foldr_cons, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      naturalDataPoly, List.map_cons, List.sum_cons, mul_add]
    rw [ih]
    by_cases ha : a = e.1 <;> simp [ha, naturalDataPoly]

theorem coverageMarkedPoly_coeff (j a : ℕ) :
    (coverageMarkedPoly j).coeff a = a * (naturalDataPoly (coverageHData j)).coeff a :=
  weightedDataPoly_coeff (coverageHData j) a

theorem naturalDataPoly_high_coeff (d : List (ℕ × ℕ)) (N : ℕ)
    (hd : ∀ e ∈ d, e.1 ≤ N) (a : ℕ) (ha : N < a) :
    (naturalDataPoly d).coeff a = 0 := by
  induction d with
  | nil => simp [naturalDataPoly]
  | cons e es ih =>
    have he := hd e (by simp)
    have hne : a ≠ e.1 := by omega
    have hdes : ∀ e ∈ es, e.1 ≤ N := by intro z hz; exact hd z (by simp [hz])
    simp only [naturalDataPoly, List.map_cons, List.sum_cons, Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, if_neg hne, zero_add]
    exact ih hdes

theorem lawPoly_eq_data (H : ℕ → ℕ → ℕ) (N j : ℕ)
    (heq : ∀ a, H j a = coverageHAt j a)
    (hd : ∀ e ∈ coverageHData j, e.1 ≤ N) :
    lawPoly H N j = naturalDataPoly (coverageHData j) := by
  apply Polynomial.ext
  intro a
  rw [lawPoly_coeff]
  by_cases ha : a ≤ N
  · rw [if_pos ha, heq a, naturalDataPoly_coeff]
    rfl
  · rw [if_neg ha, naturalDataPoly_high_coeff _ N hd a (by omega)]

theorem markedLawPoly_eq_data (H : ℕ → ℕ → ℕ) (N j : ℕ)
    (h : lawPoly H N j = naturalDataPoly (coverageHData j)) :
    markedLawPoly H N j = coverageMarkedPoly j := by
  apply Polynomial.ext
  intro a
  rw [markedLawPoly_coeff, coverageMarkedPoly_coeff, h]

theorem coverageHData_bounds : ∀ j : Fin 9, ∀ e ∈ coverageHData j.val, e.1 ≤ 563 := by
  decide +kernel

theorem coverageHData_mass_bounds : ∀ j : Fin 9, coverageHPack 1 j.val < 2^127 := by
  decide +kernel

theorem coverageLaw_zero_poly : lawPoly coverageLaw 563 0 = 1 := by
  apply Polynomial.ext
  intro a
  rw [lawPoly_coeff]
  by_cases ha : a = 0
  · subst a; simp [coverageLaw]
  · simp [coverageLaw, ha, Polynomial.coeff_one]

theorem coverageH1_poly : naturalDataPoly (coverageHData 1) = Polynomial.C 563 * X := by
  simp [coverageHData, coverageH1Data, naturalDataPoly]

theorem coverageLaw_eq_packed {β : Type*} [Fintype β]
    (val : β → Fin 6 → ℕ) (hW : WordsOf val) (h4 : ∀ x i, val x i ≤ 4)
    (hcard : Fintype.card β = 563)
    (hpacked : ∀ j, 1 ≤ j → j ≤ 8 → coveragePacked (2^128) j = coverageHPack (2^128) j)
    (j : ℕ) (hj1 : 1 ≤ j) (hj8 : j ≤ 8) (a : ℕ) :
    coverageLaw j a = coverageHAt j a := by
  rw [coverageLaw, if_neg (by omega)]
  apply coverageHistogram_of_packed j (hpacked j hj1 hj8) ?_ ?_ a
  · rw [coveragePacked_mass val hW h4 (by omega), hcard]
    calc
      563 ^ j ≤ 563 ^ 8 := Nat.pow_le_pow_right (by omega) hj8
      _ < 2^127 := by norm_num
  · exact coverageHData_mass_bounds ⟨j, by omega⟩

theorem retainedCoverage_count_bound_of_packed {β : Type*} [Fintype β]
    (val : β → Fin 6 → ℕ) (hW : WordsOf val) (h4 : ∀ x i, val x i ≤ 4)
    (hcard : Fintype.card β = 563)
    (hpacked : ∀ j, 1 ≤ j → j ≤ 8 → coveragePacked (2^128) j = coverageHPack (2^128) j)
    (r : Fin 31) (a : ℕ) :
    128 * (retainedCoveragePoly r.val).coeff a ≤
      a * #{E : Fin r.val → Fin 128 × β | coordinateCoverage val E = a} := by
  have hpoly (j : ℕ) (hj1 : 1 ≤ j) (hj8 : j ≤ 8) :
      lawPoly coverageLaw 563 j = naturalDataPoly (coverageHData j) :=
    lawPoly_eq_data coverageLaw 563 j (coverageLaw_eq_packed val hW h4 hcard hpacked j hj1 hj8)
      (coverageHData_bounds ⟨j, by omega⟩)
  exact retainedCoverage_count_bound val coverageLaw (coverageLaw_correct val hW h4) hcard r
    coverageLaw_zero_poly ((hpoly 1 (by decide) (by decide)).trans coverageH1_poly)
    (fun j hj1 hj8 => hpoly j (by omega) (by omega))
    (fun j hj1 hj8 => markedLawPoly_eq_data _ _ _ (hpoly j hj1 hj8)) a
end ClaudeWCT.Numerics.N600
