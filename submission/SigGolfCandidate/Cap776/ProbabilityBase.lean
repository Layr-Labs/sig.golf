import SigGolfCandidate.Merge042Head
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

set_option debug.skipKernelTC false
namespace SigGolfResearch.ProbabilityRows
open ClaudeWCT.Numerics
set_option linter.all false
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathCoordinate
open ClaudeWCT.Numerics.SharedPathPair ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

noncomputable def row (r t : Nat) : Nat :=
  let a := SharedPathPacked.product (coordinate 64 t)
  let b := SharedPathPacked.product (coordinate 64 (r-t))
  if t=0 then b.1 else if r-t=0 then a.1 else
    SharedPathPacked.addFirst (a.1,a.1) (b.1,0)

theorem product_prob_digit {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K∈[64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) (j : Nat) :
    digit (2^1024) (SharedPathPacked.product (coordinate K r.val)).1 j =
      ((probPoly K r.val)^2).coeff j := by
  rw [product_polynomial val hβ K hK r hp]
  exact ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j _ (fun i => by
    have h1 := (product_mass val hβ K hK r hp).1
    have h2 := polynomial_coeff_le_mass ((probPoly K r.val)^2) i
    omega)

theorem histogram_left_unique {α β : Type} [Fintype α] [Unique α] [Fintype β]
    (g : β → Prop) (b : β → Nat) :
    CoeffLE (weightedHistogram g b (fun _ => 1))
      (weightedHistogram (fun p : α×β => g p.2) (fun p => b p.2) (fun _ => 1)) := by
  classical
  intro j
  rw [weightedHistogram_coeff, weightedHistogram_coeff, Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  exact le_rfl

theorem histogram_right_unique {α β : Type} [Fintype α] [Fintype β] [Unique β]
    (g : α → Prop) (b : α → Nat) :
    CoeffLE (weightedHistogram g b (fun _ => 1))
      (weightedHistogram (fun p : α×β => g p.1) (fun p => b p.1) (fun _ => 1)) := by
  classical
  intro j
  rw [weightedHistogram_coeff, weightedHistogram_coeff, Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  exact le_rfl

theorem row_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r t : Nat) (hr : r≤20) (ht : t≤r)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    row r t<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024) (row r t) j ≤
        (weightedHistogram (splitGood val t (r-t)) (splitBin val t (r-t)) (fun _ => 1)).coeff j := by
  classical
  have hsize := split_product_size val hβ r t hr ht hp
  have ht' : t<21 := by omega
  have hu' : r-t<21 := by omega
  have hPt := (branch_histogram val hβ 64 (by simp) (⟨t,ht'⟩ : Fin 21) (hp t ht)).1
  have hPu := (branch_histogram val hβ 64 (by simp) (⟨r-t,hu'⟩ : Fin 21) (hp _ (Nat.sub_le ..))).1
  letI : Unique (BranchHistory β 64 0) := {
    default := (Fin.elim0, Fin.elim0)
    uniq := by intro x; apply Prod.ext <;> funext i <;> exact Fin.elim0 i }
  unfold splitGood splitBin
  by_cases h0 : t=0
  · subst t
    simp only [row, if_pos rfl, Nat.sub_zero, ite_true]
    refine ⟨hsize.2.2.1,?_⟩
    intro j hj
    rw [product_prob_digit val hβ 64 (by simp) (⟨r,by omega⟩ : Fin 21) (hp r le_rfl)]
    apply (hPu j).trans
    simpa only [splitGood, splitBin, if_pos rfl, Nat.sub_zero, ite_true] using
      histogram_left_unique (α:=BranchHistory β 64 0)
        (branchGood (K:=64) (r:=r) val) (branchBin val) j
  · by_cases h1 : r-t=0
    · have htr : t=r := by omega
      subst t
      letI : Unique (BranchHistory β 64 (r-r)) := by
        simpa only [Nat.sub_self] using (inferInstance : Unique (BranchHistory β 64 0))
      simp only [row, if_neg h0, Nat.sub_self, if_pos rfl, ite_true]
      refine ⟨hsize.1,?_⟩
      intro j hj
      rw [product_prob_digit val hβ 64 (by simp) (⟨r,by omega⟩ : Fin 21) (hp r le_rfl)]
      apply (hPt j).trans
      simpa only [splitGood, splitBin, if_neg h0, Nat.sub_self, if_pos rfl, ite_true] using
        histogram_right_unique (β:=BranchHistory β 64 (r-r))
          (branchGood (K:=64) (r:=r) val) (branchBin val) j
    · have hmt := product_mass val hβ 64 (by simp) (⟨t,ht'⟩ : Fin 21) (hp t ht)
      have hmu := product_mass val hβ 64 (by simp) (⟨r-t,hu'⟩ : Fin 21) (hp _ (Nat.sub_le ..))
      have hEt := product_polynomial val hβ 64 (by simp) (⟨t,ht'⟩ : Fin 21) (hp t ht)
      have hEu := product_polynomial val hβ 64 (by simp) (⟨r-t,hu'⟩ : Fin 21) (hp _ (Nat.sub_le ..))
      rw [hEt,hEu] at hsize
      have hz : (0 : Nat[X]).eval (2^1024)<(2^1024)^2048 := by simp
      have hzm : (0 : Nat[X]).eval 1*2048<2^1024 := by simp
      have hbf : CoeffLE (0 : Nat[X])
          (weightedHistogram (branchGood (K:=64) (r:=r-t) val) (branchBin val) (fun _ => 0)) :=
        fun _ => by simp only [Polynomial.coeff_zero]; exact Nat.zero_le _
      have hm : Fintype.card (BranchHistory β 64 t)*Fintype.card (BranchHistory β 64 (r-t))*(1+0)<2^1024 :=
        lt_of_le_of_lt (Nat.mul_le_mul_left _ (by decide : 1+0≤(64*563)^2+(64*563)^2))
          (split_branch_mass hβ r t hr ht)
      have h := addFirst_polynomial_histogram_lower
        (branchGood (K:=64) (r:=t) val) (branchGood (K:=64) (r:=r-t) val)
        (branchBin val) (fun _ => 1) (branchBin val) (fun _ => 0)
        ((probPoly 64 t)^2) ((probPoly 64 t)^2) ((probPoly 64 (r-t))^2) 0 1 0
        hsize.1 hsize.1 hsize.2.2.1 hz hmt.1 hmt.1 hmu.1 hzm
        hPt hPt hPu hbf (fun _ => le_rfl) (fun _ => le_rfl) hm
      simpa only [row, if_neg h0, if_neg h1, hEt, hEu, Polynomial.eval_zero,
        splitGood, splitBin, ite_true, Nat.add_zero] using h


noncomputable def pairPoly (r : Nat) : Nat[X] :=
  ∑ t ∈ range (r+1), r.choose t • packedPoly (2^1024) 2048 (row r t)

noncomputable def pairPacked (r : Nat) : Nat :=
  ∑ t ∈ range (r+1), r.choose t * row r t

theorem pair_histogram_split {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (r : Nat) :
    weightedHistogram (pairGood (r:=r) val) (pairBin val) (fun _ => 1) =
      ∑ t ∈ range (r+1), r.choose t • weightedHistogram
        (splitGood val t (r-t)) (splitBin val t (r-t)) (fun _ => 1) := by
  exact weightedHistogram_selector_split r
    (fun t u A B C D => splitGood val t u ((A,B),(C,D)))
    (fun t u A B C D => splitBin val t u ((A,B),(C,D)))
    (fun _ _ _ _ _ _ => 1)

theorem eval_nsmul_nat (P : Nat[X]) (n B : Nat) :
    (n • P).eval B=n*P.eval B := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul,Polynomial.eval_add,ih,Nat.succ_mul]

theorem coeff_nsmul_nat (P : Nat[X]) (n j : Nat) :
    (n • P).coeff j=n*P.coeff j := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul,Polynomial.coeff_add,ih,Nat.succ_mul]

theorem pair_polynomial {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    (pairPoly r).eval (2^1024)=pairPacked r ∧
      CoeffLE (pairPoly r) (weightedHistogram (pairGood (r:=r) val) (pairBin val) (fun _ => 1)) := by
  classical
  constructor
  · unfold pairPoly pairPacked
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [eval_nsmul_nat,
      packedPoly_eval _ _ _ (row_histogram val hβ r t hr (Nat.le_of_lt_succ (Finset.mem_range.mp ht)) hp).1]
  · rw [pair_histogram_split]
    intro j
    simp only [pairPoly, Polynomial.finsetSum_coeff, coeff_nsmul_nat]
    apply Finset.sum_le_sum
    intro t ht
    exact Nat.mul_le_mul_left _
      (packedPoly_below _ _ _ _ (row_histogram val hβ r t hr (Nat.le_of_lt_succ (Finset.mem_range.mp ht)) hp).2 j)

theorem pairPacked_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    pairPacked r<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024) (pairPacked r) j ≤
        (weightedHistogram (pairGood (r:=r) val) (pairBin val) (fun _ => 1)).coeff j := by
  classical
  have h := pair_polynomial val hβ r hr hp
  have hc (j : Nat) : (pairPoly r).coeff j<2^1024 := by
    apply histogram_lower_coeff_lt _ _ _ _ h.2 1 _ (fun _ _ => le_rfl)
    rw [pair_history_card hβ]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (by decide : 1≤2*(64*563)^2)) (pair_mass_small r hr)
  have hz (j : Nat) (hj : 2048≤j) : (pairPoly r).coeff j=0 := by
    simp only [pairPoly, Polynomial.finsetSum_coeff, coeff_nsmul_nat, packedPoly,
      polyOf_coeff, if_neg (by omega : ¬j<2048), Nat.mul_zero, Finset.sum_const_zero]
  rw [←h.1]
  refine ⟨polynomial_eval_lt _ _ _ (by positivity) (fun j _ => hc j) hz,?_⟩
  intro j hj
  rw [digit_polynomial_eval _ _ _ (by positivity) (fun i _ => hc i) hz j hj]
  exact h.2 j


open ClaudeWCT.Numerics.SharedPathForest
open ClaudeWCT.Numerics.SharedMoments (alphabetSize)

noncomputable def forestPoly (r : Nat) : Nat[X] :=
  encodedForestPoly (pairPacked r) (coordinate 128 r).1

noncomputable def forestPacked (r : Nat) : Nat :=
  (SharedPathPacked.spread 11 (pairPacked r))^4 * SharedPathPacked.spread 10 (coordinate 128 r).1

theorem coordinate_prob_digit {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K∈[64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) (j : Nat) :
    digit (2^1024) (coordinate K r.val).1 j = (probPoly K r.val).coeff j := by
  rw [coordinate_polynomial val hβ K hK r hp]
  exact ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j _ (fun i => by
    have h1 := (coordinate_mass val hβ K hK r hp).1
    have h2 := polynomial_coeff_le_mass (probPoly K r.val) i
    have h3 : 2^384<2^1024 := by decide
    exact h2.trans_lt (h1.trans h3))

theorem forest_encoding {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) :
    forestPacked r=(forestPoly r).eval (2^4096) := by
  exact encodedForest_encoding _ _ (pairPacked_histogram val hβ r hr (hp 64 (by simp))).1
    (coordinate_size val hβ 128 (by simp) ⟨r,by omega⟩ (hp 128 (by simp) r le_rfl)).1

theorem forest_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) :
    CoeffLE (forestPoly r) (weightedHistogram (actualGood (r:=r) val) (actualBin (r:=r) val) (fun _ : ForestHistory β r => 1)) := by
  classical
  let P := packedPoly (2^1024) 2048 (pairPacked r)
  let Q := packedPoly (2^1024) 1024 (coordinate 128 r).1
  have hP : CoeffLE P (weightedHistogram (pairGood (r:=r) val) (pairBin val) (fun _ => 1)) :=
    packedPoly_below _ _ _ _ (pairPacked_histogram val hβ r hr (hp 64 (by simp))).2
  have hQ : CoeffLE Q (weightedHistogram (coordinateGood (K:=128) (r:=r) val) (coordinateBin val) (fun _ => 1)) := by
    apply packedPoly_below
    intro j _
    rw [coordinate_prob_digit val hβ 128 (by simp) ⟨r,by omega⟩ (hp 128 (by simp) r le_rfl)]
    exact (coordinate_histogram val hβ 128 (by simp) ⟨r,by omega⟩ (hp 128 (by simp) r le_rfl)).1 j
  have hpi : CoeffLE (P^4)
      (weightedHistogram (fun h : Fin 4 → PairHistory β r => ∀ i, pairGood val (h i))
        (fun h => ∑ i, pairBin val (h i)) (fun _ => 1)) := by
    simpa only [Fin.prod_const, Finset.prod_const_one] using
      weightedHistogram_pi_lower (fun _i : Fin 4 => pairGood (r:=r) val) (fun _ => pairBin val)
        (fun _ => fun _ => 1) (fun _ => P) (fun _ => hP)
  change CoeffLE (P^4*Q) (weightedHistogram
    (fun h : (Fin 4 → PairHistory β r) × (Fin r → Fin 128 × β) =>
      (∀ i, pairGood val (h.1 i)) ∧ coordinateGood val h.2)
    (fun h => (∑ i, pairBin val (h.1 i)) + coordinateBin val h.2)
    (fun _ => 1))
  have h := weightedHistogram_product_lower _ _ _ _ _ _ _ _ hpi hQ
  simp only [Nat.one_mul] at h
  exact h

theorem forest_coeff_small {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) (j : Nat) :
    (forestPoly r).coeff j<2^4096 := by
  classical
  apply histogram_lower_coeff_lt _ _ _ _ (forest_histogram val hβ r hr hp) 1 _ (fun _ _ => le_rfl)
  rw [forest_history_card hβ r]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (by decide : 1≤alphabetSize)) (forest_mass_small r hr)

theorem forest_mass {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) :
    (forestPoly r).eval 1≤alphabetSize^r := by
  classical
  have h := histogram_lower_mass_le (actualGood val) (actualBin val) (fun _ => 1)
    (forestPoly r) (forest_histogram val hβ r hr hp) 1 (fun _ _ => le_rfl)
  simpa only [forest_history_card hβ r, Nat.mul_one] using h

end SigGolfResearch.ProbabilityRows

namespace SigGolfResearch.ProbabilityCache
open ClaudeWCT.Numerics
open Lean Elab Term
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedCoordinate ClaudeWCT.Numerics.SharedGeneratedPair
open SigGolfResearch.ProbabilityRows
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false

certify_coordinate 64 19 Coordinate_64_19 coordinate_64_19_checked
certify_coordinate 128 19 Coordinate_128_19 coordinate_128_19_checked

noncomputable def cache64 (r : Nat) : Cell :=
  if r≤18 then cachedCoordinate 64 r else Coordinate_64_19

theorem cache64_correct (r : Nat) (hr : r≤19) : coordinate 64 r=cache64 r := by
  by_cases h : r≤18
  · simp only [cache64,if_pos h]
    exact cachedCoordinate_correct r h
  · have he : r=19 := by omega
    subst r
    exact coordinate_64_19_checked

end SigGolfResearch.ProbabilityCache
