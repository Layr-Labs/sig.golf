import SigGolfCandidate.ClaudeWCT_Numerics_N600Price_B

set_option Elab.async false
set_option maxRecDepth 100000
open Finset Polynomial



namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem window_eq (a lo hi : Nat) :
    window a lo hi = (a*(2^1024)^lo) % (2^1024)^2048 -
      (a*(2^1024)^(hi+1)) % (2^1024)^2048 := by
  unfold window cutMask
  simp only [Nat.shiftLeft_eq, Nat.one_mul]
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  simp only [pow_mul]

theorem window_digits (a lo hi i : Nat) (hlo : lo ≤ hi) (hi' : i < 2048)
    (hmono : ∀ j k, j ≤ k → k<2048 → digit (2^1024) a j ≤ digit (2^1024) a k) :
    digit (2^1024) (window a lo hi) i =
      (if lo ≤ i then digit (2^1024) a (i-lo) else 0) -
      (if hi+1 ≤ i then digit (2^1024) a (i-(hi+1)) else 0) := by
  let B : Nat := 2^1024
  have hB : 0<B := pow_pos (by decide) _
  have hp : 0<B^2048 := pow_pos hB _
  have hd (k j : Nat) (hj : j<2048) :
      digit B ((a*B^k)%B^2048) j = if k ≤ j then digit B a (j-k) else 0 := by
    rw [digit_low _ _ _ _ hj, digit_shift _ _ _ _ hB]
  have hle (j : Nat) (hj : j<2048) :
      digit B ((a*B^(hi+1))%B^2048) j ≤ digit B ((a*B^lo)%B^2048) j := by
    rw [hd _ _ hj, hd _ _ hj]
    by_cases hh : hi+1 ≤ j
    · have hl : lo ≤ j := by omega
      rw [if_pos hh, if_pos hl]
      exact hmono _ _ (by omega) (by omega)
    · rw [if_neg hh]
      exact Nat.zero_le _
  rw [window_eq]
  change digit B ((a*B^lo)%B^2048 - (a*B^(hi+1))%B^2048) i = _
  rw [digit_sub _ _ _ _ hB (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) hle i hi',
    hd _ _ hi', hd _ _ hi']

#print axioms window_digits
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open scoped BigOperators Polynomial
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem geomPoly_coeff (n i : Nat) : (geomPoly n).coeff i = if i<n then 1 else 0 :=
  polyOf_coeff n (fun _ => 1) i

theorem prefix_poly_coefficient (P : Nat[X]) (n i : Nat) (hi : i<n) :
    (P*geomPoly n).coeff i = ∑ k ∈ range (i+1), P.coeff k := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  rw [geomPoly_coeff, if_pos (by have hk' := mem_range.mp hk; omega), Nat.mul_one]

theorem prefix_poly_monotone (P : Nat[X]) (n j k : Nat) (hj : j≤k) (hk : k<n) :
    (P*geomPoly n).coeff j ≤ (P*geomPoly n).coeff k := by
  rw [prefix_poly_coefficient _ _ _ (by omega), prefix_poly_coefficient _ _ _ hk]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun _ _ _ => Nat.zero_le _)

theorem prefixes_digits_monotone (P : Nat[X])
    (hb : ∀ j, (P*geomPoly 2048).coeff j < 2^1024)
    (j k : Nat) (hj : j≤k) (hk : k<2048) :
    digit (2^1024) (prefixes (P.eval (2^1024))) j ≤
      digit (2^1024) (prefixes (P.eval (2^1024))) k := by
  rw [prefixes_coefficient _ _ (by omega) hb, prefixes_coefficient _ _ hk hb]
  exact prefix_poly_monotone _ _ _ _ hj hk

#print axioms prefixes_digits_monotone
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem hadamard_11_model (a b : Nat)
    (ha : a < (2^1024)^2048) (hb : b < (2^1024)^2048) :
    hadamard 11 a b = packFun (2^1024) 2048
      (fun i => digit (2^1024) a i * digit (2^1024) b i) := by
  have hq : (2:Nat)^11 = 2048 := by decide
  have ha' : a < (2^1024)^(2^11) := by simpa only [hq] using ha
  have hb' : b < (2^1024)^(2^11) := by simpa only [hq] using hb
  rw [hadamard_eq_cross]
  have h := cross_model (2^1024) (pow_pos (by decide) _) 11 a b ha' hb'
  simpa only [hq] using h

theorem window_bound (a lo hi : Nat) : window a lo hi < (2^1024)^2048 := by
  rw [window_eq]
  exact (Nat.sub_le _ _).trans_lt (Nat.mod_lt _ (pow_pos (pow_pos (by decide) _) _))

theorem directedFirst_model (a pref : Cell) (lo hi shift : Nat)
    (haP : a.1 < (2^1024)^2048) (haF : a.2 < (2^1024)^2048) :
    directedFirst a pref lo hi shift =
      (packFun (2^1024) 2048 (fun i =>
        digit (2^1024) a.2 i * digit (2^1024) (window pref.1 lo hi) i +
        digit (2^1024) a.1 i * digit (2^1024) (window pref.2 lo hi) i) *
        (2^1024)^shift) % (2^1024)^2048 := by
  unfold directedFirst
  rw [hadamard_11_model _ _ haF (window_bound _ _ _),
    hadamard_11_model _ _ haP (window_bound _ _ _), ← packFun_add]
  unfold cutMask
  simp only [Nat.shiftLeft_eq, Nat.one_mul]
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  simp only [pow_mul]

#print axioms directedFirst_model
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset
open scoped BigOperators

theorem packFun_const_mul (B n c : Nat) (f : Nat → Nat) :
    packFun B n (fun i => c * f i) = c * packFun B n f := by
  simp only [packFun, Finset.mul_sum, Nat.mul_assoc]

theorem packFun_sum {α : Type} [Fintype α] (B n : Nat) (f : α → Nat → Nat) :
    packFun B n (fun i => ∑ a, f a i) = ∑ a, packFun B n (f a) := by
  simp only [packFun, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem packFun_window (B p n start : Nat) :
    packFun B n (fun i => digit B p (start+i)) = p / B^start % B^n := by
  conv_lhs => arg 3; ext i; rw [← digit_high]
  exact packFun_digits B (p / B^start) n

theorem digit_window_sum {α : Type} [Fintype α] (B n : Nat)
    (p start coeff : α → Nat) (hB : 0 < B)
    (hsmall : ∀ i, i<n → (∑ a, coeff a * digit B (p a) (start a+i)) < B)
    (i : Nat) (hi : i<n) :
    digit B (∑ a, coeff a * (p a / B^(start a) % B^n)) i =
      ∑ a, coeff a * digit B (p a) (start a+i) := by
  have he : (∑ a, coeff a * (p a / B^(start a) % B^n)) =
      packFun B n (fun j => ∑ a, coeff a * digit B (p a) (start a+j)) := by
    rw [packFun_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [packFun_const_mul, packFun_window]
  rw [he]
  exact digit_packFun B n _ hB hsmall i hi
end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.SharedPathList
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def bucketSeries : List Nat → Nat → Nat → Cell
  | [], _, _ => (0,0)
  | b::bs, c, p =>
    let n := p % 2^512
    let v := bucketSeries bs (c+1) (p / 2^512)
    (n*(2^1024)^b+v.1, (c*n)*(2^1024)^b+v.2)

theorem bucketSeries_zero (bs : List Nat) (c : Nat) : bucketSeries bs c 0 = (0,0) := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp [bucketSeries, ih]

theorem bucket_eq_series (bs : List Nat) (c p : Nat) : bucket bs c p = bucketSeries bs c p := by
  induction bs generalizing c p with
  | nil => rfl
  | cons b bs ih =>
    by_cases hp : p=0
    · subst p
      rw [bucketSeries_zero]
      simp only [bucket, if_true]
    · simp only [bucket, if_neg hp, Nat.and_two_pow_sub_one_eq_mod,
        Nat.shiftRight_eq_div_pow, ih]
      dsimp only [bucketSeries]
      split_ifs with hn
      · simp only [hn, Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Prod.mk.eta]
      · simp only [Nat.shiftLeft_eq, pow_mul]

#print axioms bucket_eq_series
end ClaudeWCT.Numerics.SharedPathList

namespace ClaudeWCT.Numerics.CanonicalHistogram
open CanonicalCompression
theorem top_histogram_digits : ∀ c : Fin 205,
    coefficient 136 (packHistogram 136 15 205 topCounts) c.val =
      histogramWeight topCounts (c.val+15) := by decide +kernel

theorem lower_histogram_digits : ∀ c : Fin 128,
    coefficient 132 (packHistogram 132 0 128 lowerCounts) c.val =
      histogramWeight lowerCounts c.val := by decide +kernel
end ClaudeWCT.Numerics.CanonicalHistogram

namespace ClaudeWCT.Numerics.CanonicalCounting
open scoped BigOperators
open Finset

theorem top_card_three : 3 * Fintype.card SigGolfResearch.NonbinaryTop.Codec.Word < 2^136 := by
  norm_num [SigGolfResearch.NonbinaryTop.Codec.Word,
    SigGolfResearch.NonbinaryTop.Codec.Triple8, SigGolfResearch.NonbinaryTop.Codec.Triple5,
    Fintype.card_prod, Fintype.card_fun]

theorem lower_card_seven : 7 * Fintype.card SigGolfResearch.LowerEffectiveCounting.«Word» < 2^132 := by
  let forget : SigGolfResearch.LowerEffectiveCounting.«Word» →
      (Fin 14 → SigGolfResearch.NonbinaryTop.Codec.Triple8) × Fin 8 :=
    fun w => (fun q => (w.1 q).val, w.2)
  have hi : Function.Injective forget := by
    intro a b hab
    apply Prod.ext
    · funext q
      apply Subtype.ext
      exact congrFun (congrArg Prod.fst hab) q
    · change (forget a).2 = (forget b).2
      exact congrArg Prod.snd hab
  have hc := Fintype.card_le_of_injective forget hi
  norm_num [Fintype.card_prod, Fintype.card_fun, SigGolfResearch.NonbinaryTop.Codec.Triple8] at hc ⊢
  omega
end ClaudeWCT.Numerics.CanonicalCounting

namespace ClaudeWCT.Numerics.CanonicalCounting
open Finset
open scoped BigOperators

theorem count_fibers_fin {α : Type} [Fintype α] (g : α → Nat) (P : α → Prop)
    [DecidablePred P] (n : Nat) :
    (∑ j : Fin n, (univ.filter fun a => g a = j.val ∧ P a).card) =
      (univ.filter fun a => g a < n ∧ P a).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : P a
  · simp only [hp, and_true]
    by_cases hg : g a < n
    · let j : Fin n := ⟨g a, hg⟩
      have he (k : Fin n) : g a = k.val ↔ k = j := by
        simp only [j, Fin.ext_iff]
        omega
      simp only [he, if_pos hg]
      simp
    · have he (k : Fin n) : ¬g a = k.val := by
        have := k.isLt
        omega
      simp only [he, if_neg, hg, if_false, Finset.sum_const_zero]
  · simp only [hp, and_false, if_false, Finset.sum_const_zero]

end ClaudeWCT.Numerics.CanonicalCounting


namespace ClaudeWCT.Numerics.SharedPathList
open Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def binnedPoly : List Nat → (Nat → Nat) → Nat[X]
  | [], _ => 0
  | b::bs, f => C (f 0) * X^b + binnedPoly bs (fun j => f (j+1))

theorem quotient_digit (B p j : Nat) :
    (p / B) / B^j % B = p / B^(j+1) % B := by
  rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm B]

theorem bucketSeries_poly (bs : List Nat) (c p : Nat) :
    (bucketSeries bs c p).1 =
      (binnedPoly bs (fun j => (p / (2^512)^j) % 2^512)).eval (2^1024) ∧
    (bucketSeries bs c p).2 =
      (binnedPoly bs (fun j => (c+j) * ((p / (2^512)^j) % 2^512))).eval (2^1024) := by
  induction bs generalizing c p with
  | nil => simp only [bucketSeries, binnedPoly, Polynomial.eval_zero, and_self]
  | cons b bs ih =>
    have h := ih (c+1) (p / 2^512)
    simp only [bucketSeries, binnedPoly, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, pow_zero,
      Nat.div_one, Nat.add_zero]
    constructor
    · rw [h.1]
      congr 2
      apply congrArg (binnedPoly bs)
      funext j
      exact quotient_digit (2^512) p j
    · rw [h.2]
      congr 2
      apply congrArg (binnedPoly bs)
      funext j
      rw [quotient_digit]
      congr 1
      omega

theorem binnedPoly_coeff (bs : List Nat) (f : Nat → Nat) (k : Nat) :
    (binnedPoly bs f).coeff k =
      (bs.mapIdx (fun j b => if b=k then f j else 0)).sum := by
  induction bs generalizing f with
  | nil => simp [binnedPoly]
  | cons b bs ih =>
    simp only [binnedPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, List.mapIdx_cons, List.sum_cons, ih]
    simp only [mul_ite, Nat.mul_one, Nat.mul_zero, eq_comm]

#print axioms bucketSeries_poly
#print axioms binnedPoly_coeff
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset
open scoped BigOperators
open SharedDigitBlock

theorem bits_digit_eq (bits p i : Nat) :
    (p >>> (bits*i)) % 2^bits = digit (2^bits) p i := by
  simp only [digit, Nat.shiftRight_eq_div_pow, pow_mul]

theorem shift_window_eq (bits p start len : Nat) :
    (p >>> (bits*start)) % 2^(bits*len) = p / (2^bits)^start % (2^bits)^len := by
  simp only [Nat.shiftRight_eq_div_pow, pow_mul]

theorem two_window_digits (B len start gateStart p g encoded : Nat) (hB : 0<B)
    (f h : Nat → Nat)
    (hp : ∀ i, i<len → digit B p (start+i) = f i)
    (hg : ∀ i, i<len → digit B g (gateStart+i) = h i)
    (hbound : ∀ i, i<len → f i + 2*h i < B)
    (he : encoded = p / B^start % B^len + 2*(g / B^gateStart % B^len))
    (i : Nat) (hi : i<len) : digit B encoded i = f i + 2*h i := by
  let ps : Fin 2 → Nat := ![p,g]
  let starts : Fin 2 → Nat := ![start,gateStart]
  let coeffs : Fin 2 → Nat := ![1,2]
  have hs (j : Nat) (hj : j<len) :
      (∑ a : Fin 2, coeffs a * digit B (ps a) (starts a+j)) = f j+2*h j := by
    simp only [Fin.sum_univ_two, ps, starts, coeffs, Matrix.cons_val_zero,
      Matrix.cons_val_one, Nat.one_mul, hp j hj, hg j hj]
  have hsmall (j : Nat) (hj : j<len) :
      (∑ a : Fin 2, coeffs a * digit B (ps a) (starts a+j)) < B := by
    rw [hs j hj]
    exact hbound j hj
  have hn : (∑ a : Fin 2, coeffs a * (ps a / B^(starts a) % B^len)) = encoded := by
    simp only [Fin.sum_univ_two, ps, starts, coeffs, Matrix.cons_val_zero,
      Matrix.cons_val_one, Nat.one_mul]
    exact he.symm
  rw [← hn]
  exact (digit_window_sum B len ps starts coeffs hB hsmall i hi).trans (hs i hi)
end ClaudeWCT.Numerics.CanonicalHistogram


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem bucket_polynomial (bs : List Nat) (c : Nat) (P : Nat[X])
    (hP : ∀ i, P.coeff i < 2^512) :
    bucket bs c (P.eval (2^512)) =
      ((binnedPoly bs P.coeff).eval (2^1024),
       (binnedPoly bs (fun j => (c+j)*P.coeff j)).eval (2^1024)) := by
  rw [bucket_eq_series]
  have h := bucketSeries_poly bs c (P.eval (2^512))
  have hd (j : Nat) : P.eval (2^512) / (2^512)^j % 2^512 = P.coeff j :=
    ClaudeWCT.Numerics.eval_div_pow_mod (pow_pos (by decide) _) j P hP
  simp_rw [hd] at h
  exact Prod.ext h.1 h.2

#print axioms bucket_polynomial
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem binnedPoly_eq_sum (bs : List Nat) (f : Nat → Nat) :
    binnedPoly bs f = ∑ i : Fin bs.length, C (f i) * X^(bs[i]) := by
  induction bs generalizing f with
  | nil => simp [binnedPoly]
  | cons b bs ih =>
    rw [binnedPoly]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [Fin.getElem_fin, List.getElem_cons_zero, Fin.val_zero, Fin.val_succ, List.getElem_cons_succ]
    rw [ih]
    simp only [Fin.getElem_fin]

theorem binnedPoly_finite_coeff (bs : List Nat) (f : Nat → Nat) (k : Nat) :
    (binnedPoly bs f).coeff k = ∑ i : Fin bs.length, if bs[i] = k then f i else 0 := by
  rw [binnedPoly_eq_sum]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    mul_ite, Nat.mul_one, Nat.mul_zero, eq_comm]

theorem binnedPoly_mono (bs : List Nat) (f g : Nat → Nat)
    (h : ∀ i, i<bs.length → f i ≤ g i) (k : Nat) :
    (binnedPoly bs f).coeff k ≤ (binnedPoly bs g).coeff k := by
  rw [binnedPoly_finite_coeff, binnedPoly_finite_coeff]
  apply sum_le_sum
  intro i _
  split_ifs
  · exact h i i.isLt
  · rfl

theorem binnedPoly_eval_one (bs : List Nat) (f : Nat → Nat) :
    (binnedPoly bs f).eval 1 = ∑ i : Fin bs.length, f i := by
  rw [binnedPoly_eq_sum, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, one_pow, Nat.mul_one]

#print axioms binnedPoly_eq_sum
#print axioms binnedPoly_mono
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem binnedPoly_fiber_coeff {α : Type} [Fintype α]
    (bs : List Nat) (value weight : α → Nat) (k : Nat) :
    (binnedPoly bs (fun i => ∑ a, if value a=i then weight a else 0)).coeff k =
      ∑ a, if h : value a < bs.length then
        (if bs[value a]'h = k then weight a else 0) else 0 := by
  rw [binnedPoly_finite_coeff]
  have he (i : Fin bs.length) :
      (if bs[i] = k then ∑ a, if value a=i.val then weight a else 0 else 0) =
      ∑ a, if bs[i] = k then (if value a=i.val then weight a else 0) else 0 := by
    by_cases hi : bs[i] = k
    · simp only [if_pos hi]
    · simp only [if_neg hi, Finset.sum_const_zero]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : value a < bs.length
  · rw [dif_pos ha]
    let i : Fin bs.length := ⟨value a, ha⟩
    rw [Finset.sum_eq_single i]
    · simp only [i, Fin.getElem_fin, if_true]
    · intro j _ hji
      have hn : value a ≠ j.val := by
        intro he
        apply hji
        exact Fin.ext he.symm
      simp only [if_neg hn, ite_self]
    · exact fun hi => (hi (Finset.mem_univ _)).elim
  · rw [dif_neg ha]
    apply Finset.sum_eq_zero
    intro i _
    have hn : value a ≠ i.val := by intro he; exact ha (he ▸ i.isLt)
    simp only [if_neg hn, ite_self]

theorem binnedPoly_fiber_lower {α : Type} [Fintype α]
    (bs : List Nat) (value weight : α → Nat) (f : Nat → Nat)
    (hf : ∀ i, i<bs.length → f i ≤ ∑ a, if value a=i then weight a else 0)
    (k : Nat) :
    (binnedPoly bs f).coeff k ≤
      ∑ a, if h : value a < bs.length then
        (if bs[value a]'h = k then weight a else 0) else 0 := by
  rw [← binnedPoly_fiber_coeff]
  exact binnedPoly_mono bs f _ hf k

#print axioms binnedPoly_fiber_coeff
#print axioms binnedPoly_fiber_lower
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem coordinate_coverage_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {K r : Nat} (E : Fin r → Fin K × β) :
    coordinateCoverage val E ≤ K*563 := by
  classical
  unfold coordinateCoverage
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (by simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hβ])

theorem pair_coverage_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {r : Nat} (h : PairHistory β r) :
    pairCoverage val h ≤ 2*(64*563)^2 := by
  have hb (s : Fin 2) : selectorValue (fun _ => coordinateCoverage val)
      h.1 h.2.1 h.2.2 s ≤ (64*563)^2 := by
    unfold selectorValue
    rw [pow_two]
    exact Nat.mul_le_mul (coordinate_coverage_le val hβ _) (coordinate_coverage_le val hβ _)
  unfold pairCoverage
  calc _ ≤ (64*563)^2+(64*563)^2 := Nat.add_le_add (hb 0) (hb 1)
       _ = _ := by omega

theorem forest_coverage_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {r : Nat} (h : ForestHistory β r) : forestCoverage val h ≤ alphabetSize := by
  have hp : (∏ i : Fin 4, pairCoverage val (h.1 i)) ≤ (2*(64*563)^2)^4 := by
    calc _ ≤ ∏ _i : Fin 4, (2*(64*563)^2) :=
          Finset.prod_le_prod' (fun i _ => pair_coverage_le val hβ (h.1 i))
         _ = _ := by rw [Fin.prod_const]
  exact Nat.mul_le_mul hp (coordinate_coverage_le val hβ h.2)

#print axioms forest_coverage_le
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedFees
open ENNReal
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.PoissonReflect
open SphincsSecurity.Concrete
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Thinned Poisson certificate (opus-kappa): rate `kappa*2^-31`, prefactor `13283369e-8 ≥ e^(-2 kappa)`,
parameter `2.018833 ≥ 2 kappa` for the cap-777 paired law. -/
theorem shared_mgf_bound_of_rows (T : Nat) (rate : ENNReal) (hrate : rate ≤ 1)
    (hu : (1-rate)^(T-80) ≤ ((13283369:ℕ):ENNReal)/((100000000:ℕ):ENNReal))
    (κ : ENNReal) (hκ : 1 ≤ κ)
    (hlam : (T : ENNReal) * rate * κ ≤ ((2018833:ℕ):ENNReal)/((1000000:ℕ):ENNReal))
    (g : Nat → ENNReal)
    (hpay : ∀ r ≤ 80, g r ≤ κ^r *
      ((16^r * (certifiedPayoff r).1 : Nat) : ENNReal) /
        ((maxFee*alphabetSize*fieldSize^(9*r) : Nat) : ENNReal))
    (htail : ∀ r, 80<r → g r ≤ 1) :
    ((maxFee*priceScaleTotal : Nat) : ENNReal)/scale *
      binomialAverage rate T g ≤ (6945:ENNReal)/1000 := by
  apply poissonCheckQ_sound_tilt (Qv := fieldSize)
    (f := fun r => 16^r * (certifiedPayoff r).1)
    (dbase := maxFee*alphabetSize) (sn := maxFee*priceScaleTotal)
    (sd := scale) (Mn := 6945) (Md := 1000) (R := 80)
    (show poissonCheckQ _ _ _ _ _ _ _ _ _ _ _ _ = true from shared_mgf_checked)
    (by norm_num [fieldSize]) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num [scale]) (by norm_num)
    hrate κ hκ hlam hu g
  · intro r hr
    simpa only [mul_div_assoc] using hpay r hr
  · exact htail

theorem shared_residual_bound_of_rows (T : Nat) (rate : ENNReal) (hrate : rate ≤ 1)
    (hu : (1-rate)^(T-80) ≤ ((13283369:ℕ):ENNReal)/((100000000:ℕ):ENNReal))
    (κ : ENNReal) (hκ : 1 ≤ κ)
    (hlam : (T : ENNReal) * rate * κ ≤ ((2018833:ℕ):ENNReal)/((1000000:ℕ):ENNReal))
    (g : Nat → ENNReal)
    (hpay : ∀ r ≤ 80, g r ≤ κ^r *
      ((16^r * (certifiedPayoff r).2 : Nat) : ENNReal) /
        ((scale*alphabetSize*fieldSize^(9*r) : Nat) : ENNReal))
    (htail : ∀ r, 80<r → g r ≤ 1) :
    (priceScaleTotal : ENNReal) *
      binomialAverage rate T g ≤ (7831:ENNReal)/10000000 := by
  have h := poissonCheckQ_sound_tilt (Qv := fieldSize)
    (f := fun r => 16^r * (certifiedPayoff r).2)
    (dbase := scale*alphabetSize) (sn := priceScaleTotal)
    (sd := 1) (Mn := 7831) (Md := 10000000) (R := 80)
    (show poissonCheckQ _ _ _ _ _ _ _ _ _ _ _ _ = true from shared_residual_checked)
    (by norm_num [fieldSize]) (by norm_num) (by norm_num)
    (by norm_num [scale, alphabetSize]) (by norm_num) (by norm_num)
    hrate κ hκ hlam hu g
    (fun r hr => by simpa only [mul_div_assoc] using hpay r hr) htail
  simpa only [Nat.cast_one, Nat.cast_ofNat, div_one] using h

#print axioms shared_mgf_bound_of_rows
#print axioms shared_residual_bound_of_rows
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset
open scoped BigOperators
set_option quotPrecheck false

local notation "topCount" credit:arg =>
  (univ.filter fun w : SigGolfResearch.NonbinaryTop.Codec.Word =>
    SigGolfResearch.NonbinaryTop.Counting.weight w = 145 ∧
    SigGolfResearch.NonbinaryTop.EffectiveCounting.score w = credit+12).card

local notation "topGateCount" credit:arg =>
  (univ.filter fun w : SigGolfResearch.NonbinaryTop.Codec.Word =>
    SigGolfResearch.NonbinaryTop.Counting.weight w = 145 ∧
    SigGolfResearch.NonbinaryTop.EffectiveCounting.score w = credit+12 ∧
    SigGolfResearch.NonbinaryTop.EffectiveCounting.gateWord w).card

theorem counting_digit_eq (bits p i : Nat) :
    CanonicalCounting.digit bits p i = SharedDigitBlock.digit (2^bits) p i :=
  bits_digit_eq bits p i

end ClaudeWCT.Numerics.CanonicalHistogram


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open scoped BigOperators Polynomial
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem window_prefix_interval (P : Nat[X])
    (hb : ∀ j, (P*geomPoly 2048).coeff j < 2^1024)
    (lo hi i : Nat) (hlo : lo ≤ hi) (hi' : i<2048) :
    digit (2^1024) (window (prefixes (P.eval (2^1024))) lo hi) i =
      if lo ≤ i then ∑ j ∈ Ico (i-hi) (i-lo+1), P.coeff j else 0 := by
  rw [window_digits _ _ _ _ hlo hi' (prefixes_digits_monotone P hb)]
  by_cases hl : lo ≤ i
  · simp only [if_pos hl]
    rw [prefixes_coefficient _ _ (by omega) hb,
      prefix_poly_coefficient _ _ _ (by omega)]
    by_cases hh : hi+1 ≤ i
    · rw [if_pos hh, prefixes_coefficient _ _ (by omega) hb,
        prefix_poly_coefficient _ _ _ (by omega)]
      have he : i-(hi+1)+1 = i-hi := by omega
      rw [he]
      have hs := Finset.sum_range_add_sum_Ico P.coeff (show i-hi ≤ i-lo+1 by omega)
      omega
    · rw [if_neg hh, Nat.sub_zero]
      have he : i-hi = 0 := by omega
      rw [he, Nat.Ico_zero_eq_range]
  · have hh : ¬hi+1 ≤ i := by omega
    simp only [if_neg hl, if_neg hh, Nat.sub_self]

#print axioms window_prefix_interval
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset CanonicalCompression

end ClaudeWCT.Numerics.CanonicalHistogram


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem coordinate_near_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {K r : Nat} (E : Fin r → Fin K × β) : coordinateNear val E ≤ 6*(K*563) := by
  classical
  unfold coordinateNear
  calc _ ≤ ∑ _i : Fin 6, K*563 := Finset.sum_le_sum (fun i _ =>
          (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
            (by simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hβ]))
       _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

theorem pair_near_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {r : Nat} (h : PairHistory β r) : pairNear val h ≤ 12*(2*(64*563)^2) := by
  have hs (s : Fin 2) : selectorKernel
      (fun _ A B => coordinateNear val A * coordinateCoverage val B +
        coordinateCoverage val A * coordinateNear val B) h.1 h.2.1 h.2.2 s ≤ 12*(64*563)^2 := by
    unfold selectorKernel
    calc _ ≤ (6*(64*563))*(64*563)+(64*563)*(6*(64*563)) :=
          Nat.add_le_add
            (Nat.mul_le_mul (coordinate_near_le val hβ _) (coordinate_coverage_le val hβ _))
            (Nat.mul_le_mul (coordinate_coverage_le val hβ _) (coordinate_near_le val hβ _))
         _ = _ := by ring
  unfold pairNear
  exact (Nat.add_le_add (hs 0) (hs 1)).trans_eq (by ring)

theorem marked_product_const (a b : Nat) (k : Fin 4) :
    (∏ i : Fin 4, if i=k then a else b) = a*b^3 := by
  fin_cases k <;> simp [Fin.prod_univ_succ] <;> ring

theorem forest_near_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {r : Nat} (h : ForestHistory β r) : forestNear val h ≤ 54*alphabetSize := by
  let D : Nat := 2*(64*563)^2
  have hmark (k : Fin 4) :
      (∏ i, if i=k then pairNear val (h.1 i) else pairCoverage val (h.1 i)) ≤ 12*D^4 := by
    calc _ ≤ ∏ i : Fin 4, if i=k then 12*D else D := by
              apply Finset.prod_le_prod'
              intro i _
              split_ifs
              · exact pair_near_le val hβ _
              · exact pair_coverage_le val hβ _
         _ = 12*D^4 := by rw [marked_product_const]; ring
  have hs : (∑ k : Fin 4, ∏ i, if i=k then pairNear val (h.1 i) else
      pairCoverage val (h.1 i)) ≤ 4*(12*D^4) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using
      Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 4))) => hmark k)
  have hp : (∏ i : Fin 4, pairCoverage val (h.1 i)) ≤ D^4 := by
    calc _ ≤ ∏ _i : Fin 4, D := Finset.prod_le_prod' (fun i _ => pair_coverage_le val hβ _)
         _ = _ := by rw [Fin.prod_const]
  unfold forestNear
  calc _ ≤ (4*(12*D^4))*(128*563) + D^4*(6*(128*563)) :=
          Nat.add_le_add
            (Nat.mul_le_mul hs (coordinate_coverage_le val hβ h.2))
            (Nat.mul_le_mul hp (coordinate_near_le val hβ h.2))
       _ = 54*alphabetSize := by unfold alphabetSize D; ring

#print axioms forest_near_le
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedMoments
open ENNReal
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.PoissonReflect
open SphincsSecurity.Concrete
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem first_bound_of_rows (T : Nat) (rate : ENNReal) (hrate : rate ≤ 1)
    (hu : (1-rate)^(T-80) ≤ ((13283369:ℕ):ENNReal)/((100000000:ℕ):ENNReal))
    (κ : ENNReal) (hκ : 1 ≤ κ)
    (hlam : (T : ENNReal) * rate * κ ≤ ((2018833:ℕ):ENNReal)/((1000000:ℕ):ENNReal))
    (g : Nat → ENNReal)
    (hpay : ∀ r ≤ 80, g r ≤ κ^r *
      ((16^r*forestMoment r : Nat) : ENNReal) /
        ((alphabetSize*fieldSize^(9*r) : Nat) : ENNReal))
    (htail : ∀ r, 80<r → g r ≤ 1) :
    (priceScaleTotal : ENNReal)*binomialAverage rate T g ≤ (849:ENNReal)/1000 := by
  have h := poissonCheckQ_sound_tilt (Qv := fieldSize)
    (f := fun r => 16^r*forestMoment r) (dbase := alphabetSize)
    (sn := priceScaleTotal) (sd := 1) (Mn := 849) (Md := 1000) (R := 80)
    first_moment_checked (by norm_num [fieldSize]) (by norm_num) (by norm_num)
    (by norm_num [alphabetSize]) (by norm_num) (by norm_num)
    hrate κ hκ hlam hu g
    (fun r hr => by simpa only [mul_div_assoc] using hpay r hr) htail
  simpa only [Nat.cast_one, Nat.cast_ofNat, div_one] using h

theorem near_bound_of_rows (T : Nat) (rate : ENNReal) (hrate : rate ≤ 1)
    (hu : (1-rate)^(T-80) ≤ ((13283369:ℕ):ENNReal)/((100000000:ℕ):ENNReal))
    (κ : ENNReal) (hκ : 1 ≤ κ)
    (hlam : (T : ENNReal) * rate * κ ≤ ((2018833:ℕ):ENNReal)/((1000000:ℕ):ENNReal))
    (g : Nat → ENNReal)
    (hpay : ∀ r ≤ 80, g r ≤ κ^r *
      ((16^r*forestNearMoment r : Nat) : ENNReal) /
        ((54*alphabetSize*fieldSize^(9*r) : Nat) : ENNReal))
    (htail : ∀ r, 80<r → g r ≤ 1) :
    ((54*priceScaleTotal : Nat) : ENNReal)*binomialAverage rate T g ≤ 351 := by
  have h := poissonCheckQ_sound_tilt (Qv := fieldSize)
    (f := fun r => 16^r*forestNearMoment r) (dbase := 54*alphabetSize)
    (sn := 54*priceScaleTotal) (sd := 1) (Mn := 351) (Md := 1) (R := 80)
    near_moment_checked (by norm_num [fieldSize]) (by norm_num) (by norm_num)
    (by norm_num [alphabetSize]) (by norm_num) (by norm_num)
    hrate κ hκ hlam hu g
    (fun r hr => by simpa only [mul_div_assoc] using hpay r hr) htail
  simpa only [Nat.cast_one, Nat.cast_ofNat, div_one] using h

#print axioms first_bound_of_rows
#print axioms near_bound_of_rows
end ClaudeWCT.Numerics.SharedMoments

namespace ClaudeWCT.Numerics.CanonicalHistogram
open OracleComp OracleSpec ENNReal Finset CanonicalCompression
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.ProducerV5.Canonical

end ClaudeWCT.Numerics.CanonicalHistogram

namespace ClaudeWCT.Numerics.CanonicalCounting
open scoped BigOperators
open Finset
theorem lower_event (zeros credit : Nat) (hc : credit < 128) (w : SigGolfResearch.LowerEffectiveCounting.Word) :
    SigGolfResearch.LowerEffectiveCounting.stat w = 65536*zeros+128*201+credit ↔
      SigGolfResearch.LowerEffectiveCounting.zeros w = zeros ∧
      SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
      SigGolfResearch.LowerEffectiveCounting.score w = credit := by
  rw [SigGolfResearch.LowerEffectiveCounting.stat_eq]
  exact lower_split _ _ _ _ _ (SigGolfResearch.LowerEffectiveCounting.score_le w)
    (SigGolfResearch.LowerEffectiveCounting.weight_le w) hc

attribute [local irreducible] SigGolfResearch.LowerEffectiveCounting.packedAt
set_option maxRecDepth 100000 in
theorem lower_weighted : (∑ w : SigGolfResearch.LowerEffectiveCounting.Word,
    (2^132)^SigGolfResearch.LowerEffectiveCounting.stat w) =
      SigGolfResearch.LowerEffectiveCounting.packed :=
  SigGolfResearch.LowerEffectiveCounting.weighted_words_at (2^132)

end ClaudeWCT.Numerics.CanonicalCounting


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weighted_fiber_count {α : Type} [Fintype α] (value : α → Nat) (c j : Nat) :
    (∑ a, if value a=j then c+value a else 0) =
      (c+j) * (Finset.univ.filter fun a => value a=j).card := by
  classical
  rw [Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : value a=j
  · simp only [ha, if_true, Nat.mul_one]
  · simp only [if_neg ha, Nat.mul_zero]

theorem bucket_retained_lower {α : Type} [Fintype α]
    (value : α → Nat) (bs : List Nat) (c : Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j < 2^512)
    (hcount : ∀ j, P.coeff j ≤ (Finset.univ.filter fun a => value a=j).card)
    (hprob : ∀ j, (binnedPoly bs P.coeff).coeff j < 2^1024)
    (hfirst : ∀ j, (binnedPoly bs (fun j => (c+j)*P.coeff j)).coeff j < 2^1024)
    (k : Nat) :
    ((bucket bs c (P.eval (2^512))).1 / (2^1024)^k % 2^1024 ≤
      ∑ a, if h : value a < bs.length then
        (if bs[value a]'h = k then 1 else 0) else 0) ∧
    ((bucket bs c (P.eval (2^512))).2 / (2^1024)^k % 2^1024 ≤
      ∑ a, if h : value a < bs.length then
        (if bs[value a]'h = k then c+value a else 0) else 0) := by
  classical
  rw [bucket_polynomial bs c P hP]
  constructor
  · rw [ClaudeWCT.Numerics.eval_div_pow_mod (pow_pos (by decide) _) k _ hprob]
    apply binnedPoly_fiber_lower bs value (fun _ => 1) P.coeff
    intro j _
    simpa only [Finset.card_filter] using hcount j
  · rw [ClaudeWCT.Numerics.eval_div_pow_mod (pow_pos (by decide) _) k _ hfirst]
    apply binnedPoly_fiber_lower bs value (fun a => c+value a) (fun j => (c+j)*P.coeff j)
    intro j _
    rw [weighted_fiber_count]
    exact Nat.mul_le_mul_left (c+j) (hcount j)

#print axioms bucket_retained_lower
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def weightedHistogram {α : Type} [Fintype α]
    (good : α → Prop) (bin weight : α → Nat) : Nat[X] := by
  classical
  exact ∑ a, if good a then C (weight a)*X^(bin a) else 0

theorem weightedHistogram_coeff {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat) (k : Nat) :
    (weightedHistogram good bin weight).coeff k =
      ∑ a, if good a ∧ bin a=k then weight a else 0 := by
  classical
  unfold weightedHistogram
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hg : good a
  · simp only [if_pos hg, Polynomial.coeff_C_mul_X_pow, hg, if_true, true_and, eq_comm]
  · simp only [if_neg hg, Polynomial.coeff_zero, hg, false_and, if_false]

theorem weightedHistogram_mul {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) (gb : β → Prop) (ba wa : α → Nat) (bb wb : β → Nat) :
    weightedHistogram ga ba wa * weightedHistogram gb bb wb =
      weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
        (fun p => ba p.1+bb p.2) (fun p => wa p.1*wb p.2) := by
  classical
  unfold weightedHistogram
  rw [Finset.sum_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : ga a <;> by_cases hb : gb b
  · simp only [if_pos ha, if_pos hb, if_pos (And.intro ha hb), Polynomial.C_mul, pow_add]
    ring
  · simp only [if_pos ha, if_neg hb, Nat.cast_id, mul_zero, ha, hb, true_and, if_false]
  · simp only [if_neg ha, zero_mul, ha, false_and, if_false]
  · simp only [if_neg ha, zero_mul, ha, false_and, if_false]

theorem weightedHistogram_product_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) (gb : β → Prop) (ba wa : α → Nat) (bb wb : β → Nat)
    (P Q : Nat[X]) (hP : CoeffLE P (weightedHistogram ga ba wa))
    (hQ : CoeffLE Q (weightedHistogram gb bb wb)) :
    CoeffLE (P*Q) (weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
      (fun p => ba p.1+bb p.2) (fun p => wa p.1*wb p.2)) := by
  rw [← weightedHistogram_mul]
  exact CoeffLE.mul _ _ _ _ hP hQ

#print axioms weightedHistogram_product_lower
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem sum_finite_fibers {α β : Type} [Fintype α] [DecidableEq β]
    (s : Finset β) (good : α → Prop) [DecidablePred good]
    (label : α → β) (weight : α → Nat) :
    (∑ b ∈ s, ∑ a, if good a ∧ label a=b then weight a else 0) =
      ∑ a, if good a ∧ label a∈s then weight a else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hg : good a
  · simp only [hg, true_and]
    by_cases hs : label a∈s
    · rw [if_pos hs, Finset.sum_eq_single (label a)]
      · simp only [if_true]
      · intro b _ hb
        exact if_neg (Ne.symm hb)
      · exact fun hn => (hn hs).elim
    · rw [if_neg hs]
      apply Finset.sum_eq_zero
      intro b hb
      exact if_neg (by intro he; exact hs (he ▸ hb))
  · simp only [hg, false_and, if_false, Finset.sum_const_zero]

theorem product_fiber_sum {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat) (i j : Nat) :
    (∑ p : α×β, if (ga p.1 ∧ ba p.1=i) ∧ (gb p.2 ∧ bb p.2=j)
      then wa p.1*wb p.2 else 0) =
      (∑ a, if ga a ∧ ba a=i then wa a else 0) *
      (∑ b, if gb b ∧ bb b=j then wb b else 0) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : ga a ∧ ba a=i <;> by_cases hb : gb b ∧ bb b=j <;>
    simp only [ha, hb, true_and, false_and, and_true, and_false, if_true, if_false,
      Nat.zero_mul, Nat.mul_zero]

#print axioms sum_finite_fibers
#print axioms product_fiber_sum
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem directedFirst_digit (a pref : Cell) (lo hi shift : Nat)
    (haP : a.1 < (2^1024)^2048) (haF : a.2 < (2^1024)^2048)
    (hsmall : ∀ j, j<2048 →
      digit (2^1024) a.2 j * digit (2^1024) (window pref.1 lo hi) j +
      digit (2^1024) a.1 j * digit (2^1024) (window pref.2 lo hi) j < 2^1024)
    (i : Nat) (hi' : i<2048) :
    digit (2^1024) (directedFirst a pref lo hi shift) i =
      if shift ≤ i then
        digit (2^1024) a.2 (i-shift) * digit (2^1024) (window pref.1 lo hi) (i-shift) +
        digit (2^1024) a.1 (i-shift) * digit (2^1024) (window pref.2 lo hi) (i-shift)
      else 0 := by
  rw [directedFirst_model _ _ _ _ _ haP haF, digit_low _ _ _ _ hi',
    digit_shift _ _ _ _ (pow_pos (by decide) _)]
  by_cases hs : shift ≤ i
  · rw [if_pos hs, if_pos hs]
    exact digit_packFun _ _ _ (pow_pos (by decide) _) hsmall _ (by omega)
  · rw [if_neg hs, if_neg hs]

#print axioms directedFirst_digit
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset
open scoped BigOperators
set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

local notation "lowerCount" credit:arg =>
  (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
    SigGolfResearch.LowerEffectiveCounting.zeros w ≤ 5 ∧
    SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
    SigGolfResearch.LowerEffectiveCounting.score w = credit).card

local notation "lowerFiber" z:arg credit:arg =>
  (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
    SigGolfResearch.LowerEffectiveCounting.zeros w = z ∧
    SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
    SigGolfResearch.LowerEffectiveCounting.score w = credit).card

theorem lower_fibers (credit : Nat) : (∑ z : Fin 6, lowerFiber z.val credit) = lowerCount credit := by
  rw [CanonicalCounting.count_fibers_fin]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  omega

theorem lower_counts_bound (credit : Nat) : 7*lowerCount credit < 2^132 := by
  have h : lowerCount credit ≤ Fintype.card SigGolfResearch.LowerEffectiveCounting.«Word» :=
    Finset.card_filter_le _ _
  have hbound := CanonicalCounting.lower_card_seven
  omega

theorem lower_windows_fold (p : Nat) :
    (List.range 6).foldl (fun s zeros =>
      s + ((p >>> (132*(65536*zeros+128*201))) % 2^(132*128))) 0 =
    ∑ z : Fin 6, p / (2^132)^(65536*z.val+128*201) % (2^132)^128 := by
  have hfold (f : Nat → Nat) : (List.range 6).foldl (fun s z => s+f z) 0 =
      ∑ z : Fin 6, f z.val := by
    simp [List.range_succ, Fin.sum_univ_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hfold]
  apply Finset.sum_congr rfl
  intro z _
  exact shift_window_eq 132 p (65536*z.val+128*201) 128

end ClaudeWCT.Numerics.CanonicalHistogram

namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset CanonicalCompression
set_option maxRecDepth 100000

end ClaudeWCT.Numerics.CanonicalHistogram


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem product_filtered_sum {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (wa : α → Nat) (wb : β → Nat) :
    (∑ p : α×β, if ga p.1 ∧ gb p.2 then wa p.1*wb p.2 else 0) =
      (∑ a, if ga a then wa a else 0)*(∑ b, if gb b then wb b else 0) := by
  simpa only [and_true] using product_fiber_sum ga gb (fun _ => 0) wa (fun _ => 0) wb 0 0

theorem cross_filtered_sum {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (wa : α → Nat) (wb : β → Nat) :
    (∑ p : α×β, if ga p.1 ∧ gb p.2 then wa p.1+wb p.2 else 0) =
      (∑ a, if ga a then wa a else 0)*(∑ b, if gb b then 1 else 0) +
      (∑ a, if ga a then 1 else 0)*(∑ b, if gb b then wb b else 0) := by
  have he (p : α×β) :
      (if ga p.1 ∧ gb p.2 then wa p.1+wb p.2 else 0) =
      (if ga p.1 ∧ gb p.2 then wa p.1*1 else 0) +
      (if ga p.1 ∧ gb p.2 then 1*wb p.2 else 0) := by
    by_cases hp : ga p.1 ∧ gb p.2 <;> simp only [hp, true_and, if_true, if_false, mul_one, one_mul, Nat.zero_add]
  simp_rw [he]
  rw [Finset.sum_add_distrib, product_filtered_sum ga gb wa (fun _ => 1),
    product_filtered_sum ga gb (fun _ => 1) wb]

theorem directed_fiber_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat)
    (ap af bp bf : Nat → Nat)
    (haP : ∀ i, ap i ≤ ∑ a, if ga a ∧ ba a=i then 1 else 0)
    (haF : ∀ i, af i ≤ ∑ a, if ga a ∧ ba a=i then wa a else 0)
    (hbP : ∀ j, bp j ≤ ∑ b, if gb b ∧ bb b=j then 1 else 0)
    (hbF : ∀ j, bf j ≤ ∑ b, if gb b ∧ bb b=j then wb b else 0)
    (i : Nat) (s : Finset Nat) :
    af i*(∑ j ∈ s, bp j) + ap i*(∑ j ∈ s, bf j) ≤
      ∑ p : α×β, if (ga p.1 ∧ ba p.1=i) ∧ (gb p.2 ∧ bb p.2∈s)
        then wa p.1+wb p.2 else 0 := by
  rw [cross_filtered_sum (fun a => ga a ∧ ba a=i) (fun b => gb b ∧ bb b∈s) wa wb]
  apply Nat.add_le_add
  · apply Nat.mul_le_mul (haF i)
    rw [← sum_finite_fibers s gb bb (fun _ => 1)]
    exact Finset.sum_le_sum (fun j _ => hbP j)
  · apply Nat.mul_le_mul (haP i)
    rw [← sum_finite_fibers s gb bb wb]
    exact Finset.sum_le_sum (fun j _ => hbF j)

#print axioms directed_fiber_lower
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open scoped BigOperators Polynomial
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem directed_histogram_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat) (a pref : Cell)
    (bp bf : Nat → Nat) (lo hi shift : Nat)
    (haP : a.1 < (2^1024)^2048) (haF : a.2 < (2^1024)^2048)
    (hsmall : ∀ j, j<2048 →
      digit (2^1024) a.2 j * digit (2^1024) (window pref.1 lo hi) j +
      digit (2^1024) a.1 j * digit (2^1024) (window pref.2 lo hi) j < 2^1024)
    (hwinP : ∀ j, j<2048 → digit (2^1024) (window pref.1 lo hi) j =
      if lo≤j then ∑ t ∈ Ico (j-hi) (j-lo+1), bp t else 0)
    (hwinF : ∀ j, j<2048 → digit (2^1024) (window pref.2 lo hi) j =
      if lo≤j then ∑ t ∈ Ico (j-hi) (j-lo+1), bf t else 0)
    (hap : ∀ i, digit (2^1024) a.1 i ≤ ∑ x, if ga x ∧ ba x=i then 1 else 0)
    (haf : ∀ i, digit (2^1024) a.2 i ≤ ∑ x, if ga x ∧ ba x=i then wa x else 0)
    (hbp : ∀ i, bp i ≤ ∑ y, if gb y ∧ bb y=i then 1 else 0)
    (hbf : ∀ i, bf i ≤ ∑ y, if gb y ∧ bb y=i then wb y else 0)
    (k : Nat) (hk : k<2048) :
    digit (2^1024) (directedFirst a pref lo hi shift) k ≤
      (weightedHistogram
        (fun p : α×β => ga p.1 ∧ gb p.2 ∧ bb p.2≤ba p.1 ∧
          lo≤ba p.1-bb p.2 ∧ ba p.1-bb p.2≤hi)
        (fun p => ba p.1+shift) (fun p => wa p.1+wb p.2)).coeff k := by
  rw [directedFirst_digit _ _ _ _ _ haP haF hsmall _ hk, weightedHistogram_coeff]
  by_cases hs : shift≤k
  · rw [if_pos hs, hwinP _ (by omega), hwinF _ (by omega)]
    by_cases hl : lo≤k-shift
    · simp only [if_pos hl]
      apply (directed_fiber_lower ga gb ba wa bb wb _ _ bp bf hap haf hbp hbf
        (k-shift) (Ico (k-shift-hi) (k-shift-lo+1))).trans
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      simp only [Finset.mem_Ico]
      apply propext
      constructor
      · rintro ⟨⟨hga, hba⟩, hgb, hlo, hhi⟩
        refine ⟨⟨hga,hgb,?_,?_,?_⟩,?_⟩ <;> omega
      · rintro ⟨⟨hga,hgb,hj,hlo,hhi⟩,hba⟩
        exact ⟨⟨hga,by omega⟩,hgb,by omega,by omega⟩
    · simp only [if_neg hl, Nat.mul_zero, Nat.zero_add]
      exact Nat.zero_le _
  · rw [if_neg hs]
    exact Nat.zero_le _

#print axioms directed_histogram_lower
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.CanonicalHistogram
open OracleComp OracleSpec ENNReal Finset CanonicalCompression
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.ProducerV5.Canonical
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

variable (hd : ∀ (z : Fin 6) (i : Nat), i<128 →
  SharedDigitBlock.digit (2^132) SigGolfResearch.LowerEffectiveCounting.packed
    (65536*z.val+128*201+i) =
  (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
    SigGolfResearch.LowerEffectiveCounting.zeros w = z.val ∧
    SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
    SigGolfResearch.LowerEffectiveCounting.score w = i).card)
include hd

end ClaudeWCT.Numerics.CanonicalHistogram


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weightedHistogram_eval_one {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat) :
    (weightedHistogram good bin weight).eval 1 = ∑ a, if good a then weight a else 0 := by
  classical
  unfold weightedHistogram
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : good a
  · simp only [if_pos ha, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, one_pow, Nat.mul_one]
  · simp only [if_neg ha, Polynomial.eval_zero]

theorem weightedHistogram_mass_le {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (M : Nat) (hM : ∀ a, good a → weight a≤M) :
    (weightedHistogram good bin weight).eval 1 ≤ Fintype.card α*M := by
  rw [weightedHistogram_eval_one]
  calc (∑ a, if good a then weight a else 0) ≤ ∑ _a : α, M := by
         apply Finset.sum_le_sum
         intro a _
         split_ifs with ha
         · exact hM a ha
         · exact Nat.zero_le _
       _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem polynomial_coeff_le_mass (P : Nat[X]) (i : Nat) : P.coeff i ≤ P.eval 1 := by
  have h := ClaudeWCT.Numerics.N600.sum_coeff_le_eval_one P {i}
  simpa only [Finset.sum_singleton] using h

theorem polynomial_mass_mono {P Q : Nat[X]} (h : CoeffLE P Q) :
    P.eval 1≤Q.eval 1 := by
  calc P.eval 1 = ∑ i ∈ P.support, P.coeff i := by
         simp [Polynomial.eval_eq_sum, Polynomial.sum_def]
       _ ≤ ∑ i ∈ P.support, Q.coeff i := Finset.sum_le_sum (fun i _ => h i)
       _ ≤ Q.eval 1 := sum_coeff_le_eval_one Q P.support

theorem histogram_lower_mass_le {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (P : Nat[X]) (hP : CoeffLE P (weightedHistogram good bin weight))
    (M : Nat) (hM : ∀ a, good a → weight a≤M) :
    P.eval 1 ≤ Fintype.card α*M :=
  (polynomial_mass_mono hP).trans
    (weightedHistogram_mass_le good bin weight M hM)

theorem histogram_lower_coeff_lt {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (P : Nat[X]) (hP : CoeffLE P (weightedHistogram good bin weight))
    (M B : Nat) (hM : ∀ a, good a → weight a≤M) (hB : Fintype.card α*M<B)
    (i : Nat) : P.coeff i<B :=
  (polynomial_coeff_le_mass P i).trans_lt
    ((histogram_lower_mass_le good bin weight P hP M hM).trans_lt hB)

#print axioms histogram_lower_coeff_lt
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedMoments
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem coordinate_history_card {β : Type} [Fintype β]
    (hβ : Fintype.card β=563) (K r : Nat) :
    Fintype.card (Fin r → Fin K×β) = (K*563)^r := by
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, hβ]

theorem pair_history_card {β : Type} [Fintype β]
    (hβ : Fintype.card β=563) (r : Nat) :
    Fintype.card (PairHistory β r) = (2*(64*563)^2)^r := by
  simp only [PairHistory, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, hβ,
    mul_pow, pow_two, Nat.mul_assoc]

theorem forest_history_card {β : Type} [Fintype β]
    (hβ : Fintype.card β=563) (r : Nat) :
    Fintype.card (ForestHistory β r) = alphabetSize^r := by
  simp only [ForestHistory, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    pair_history_card hβ r, hβ]
  rw [← pow_mul, Nat.mul_comm r 4, pow_mul]
  rw [← mul_pow]
  rfl

theorem coordinate_mass_small (K r : Nat) (hK : K≤128) (hr : r≤20) :
    (K*563)^r*(K*563) < 2^384 := by
  have hbase : K*563≤128*563 := Nat.mul_le_mul_right _ hK
  have hp : (K*563)^r≤(128*563)^20 :=
    (Nat.pow_le_pow_left hbase r).trans (Nat.pow_le_pow_right (by decide) hr)
  exact (Nat.mul_le_mul hp hbase).trans_lt (by decide +kernel)

theorem pair_mass_small (r : Nat) (hr : r≤20) :
    (2*(64*563)^2)^r*(2*(64*563)^2) < 2^1024 := by
  have hp := Nat.pow_le_pow_right (n:=2*(64*563)^2) (by decide : 0<2*(64*563)^2) hr
  exact (Nat.mul_le_mul_right _ hp).trans_lt (by decide +kernel)

theorem forest_mass_small (r : Nat) (hr : r≤20) :
    alphabetSize^r*alphabetSize < 2^4096 := by
  have hp := Nat.pow_le_pow_right (n:=alphabetSize) (by decide : 0<alphabetSize) hr
  exact (Nat.mul_le_mul_right _ hp).trans_lt (by decide +kernel)

#print axioms forest_history_card
#print axioms coordinate_mass_small
#print axioms pair_mass_small
#print axioms forest_mass_small
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset ClaudeWCT.Numerics.N600
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem sum_pair_split {α M : Type*} [Fintype α] [AddCommMonoid M]
    (r : Nat) (F : (t u : Nat) → (Fin t → α) → (Fin t → α) →
      (Fin u → α) → (Fin u → α) → M) :
    (∑ o : Fin r → Fin 2, ∑ A : Fin r → α, ∑ B : Fin r → α,
      F (occ o 0) (occ o 1) (splitRanks o A 0) (splitRanks o B 0)
        (splitRanks o A 1) (splitRanks o B 1)) =
      ∑ t ∈ range (r+1), r.choose t •
        (∑ A₀ : Fin t → α, ∑ B₀ : Fin t → α,
          ∑ A₁ : Fin (r-t) → α, ∑ B₁ : Fin (r-t) → α,
            F t (r-t) A₀ B₀ A₁ B₁) := by
  have hs (o : Fin r → Fin 2) :
      (∑ A : Fin r → α, ∑ B : Fin r → α,
        F (occ o 0) (occ o 1) (splitRanks o A 0) (splitRanks o B 0)
          (splitRanks o A 1) (splitRanks o B 1)) =
        ∑ A₀ : Fin (occ o 0) → α, ∑ B₀ : Fin (occ o 0) → α,
          ∑ A₁ : Fin (occ o 1) → α, ∑ B₁ : Fin (occ o 1) → α,
            F (occ o 0) (occ o 1) A₀ B₀ A₁ B₁ := by
    trans ∑ A : Fin r → α, ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
      F (occ o 0) (occ o 1) (splitRanks o A 0) B₀ (splitRanks o A 1) B₁
    · apply Finset.sum_congr rfl
      intro A _
      exact sum_split_selector o (fun B₀ B₁ =>
        F (occ o 0) (occ o 1) (splitRanks o A 0) B₀ (splitRanks o A 1) B₁)
    · rw [sum_split_selector o (fun A₀ A₁ =>
        ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
          F (occ o 0) (occ o 1) A₀ B₀ A₁ B₁)]
      apply Finset.sum_congr rfl
      intro A₀ _
      rw [Finset.sum_comm]
  simp_rw [hs]
  exact sum_selector_occupancy r (fun t u =>
    ∑ A₀ : Fin t → α, ∑ B₀ : Fin t → α, ∑ A₁ : Fin u → α, ∑ B₁ : Fin u → α,
      F t u A₀ B₀ A₁ B₁)

#print axioms sum_pair_split
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem binnedPoly_histogram_lower {α : Type} [Fintype α]
    (bs : List Nat) (value weight : α → Nat) (f : Nat → Nat)
    (hf : ∀ i, i<bs.length → f i≤∑ a, if value a=i then weight a else 0) :
    CoeffLE (binnedPoly bs f)
      (weightedHistogram (fun a => value a<bs.length)
        (fun a => bs[value a]?.getD 0) weight) := by
  intro k
  have h := binnedPoly_fiber_lower bs value weight f hf k
  rw [weightedHistogram_coeff]
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : value a<bs.length
  · rw [dif_pos ha]
    simp only [ha, true_and, List.getElem?_eq_getElem ha, Option.getD_some]
  · rw [dif_neg ha]
    simp only [ha, false_and, if_false]

#print axioms binnedPoly_histogram_lower
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem packFun_lt (B n : Nat) (f : Nat → Nat) (hB : 0<B)
    (hf : ∀ i, i<n → f i<B) : packFun B n f<B^n := by
  induction n with
  | zero => simp only [packFun, Finset.range_zero, Finset.sum_empty, pow_zero]; exact Nat.zero_lt_one
  | succ n ih =>
    have hp := ih (fun i hi => hf i (by omega))
    have hn : f n+1≤B := hf n (by omega)
    have hm := Nat.mul_le_mul_right (B^n) hn
    simp only [packFun, Finset.sum_range_succ] at hp ⊢
    rw [pow_succ]
    nlinarith

theorem polynomial_eval_packFun (P : Nat[X]) (B n : Nat)
    (hz : ∀ i, n ≤ i → P.coeff i=0) : P.eval B=packFun B n P.coeff := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  unfold packFun
  apply Finset.sum_subset
  · intro i hi
    apply Finset.mem_range.mpr
    have hc := Polynomial.mem_support_iff.mp hi
    by_contra hn
    exact hc (hz i (by omega))
  · intro i _ hi
    have hz : P.coeff i=0 := by
      by_contra hn
      exact hi (Polynomial.mem_support_iff.mpr hn)
    rw [hz, Nat.zero_mul]

theorem polynomial_eval_lt (P : Nat[X]) (B n : Nat) (hB : 0<B)
    (hc : ∀ i, i<n → P.coeff i<B) (hz : ∀ i, n ≤ i → P.coeff i=0) :
    P.eval B<B^n := by
  rw [polynomial_eval_packFun P B n hz]
  exact packFun_lt B n P.coeff hB hc

#print axioms polynomial_eval_lt
end ClaudeWCT.Numerics.SharedDigitBlock

namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem binnedPoly_coeff_zero (bs : List Nat) (f : Nat → Nat) (n : Nat)
    (hb : ∀ i : Fin bs.length, bs[i]<n) (j : Nat) (hj : n≤j) :
    (binnedPoly bs f).coeff j=0 := by
  rw [binnedPoly_finite_coeff]
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (by have h := hb i; omega)

theorem binnedPoly_eval_lt (bs : List Nat) (f : Nat → Nat) (B n : Nat)
    (hB : 0<B) (hb : ∀ i : Fin bs.length, bs[i]<n)
    (hc : ∀ j, (binnedPoly bs f).coeff j<B) : (binnedPoly bs f).eval B<B^n := by
  exact polynomial_eval_lt _ B n hB (fun j _ => hc j) (binnedPoly_coeff_zero bs f n hb)

#print axioms binnedPoly_eval_lt
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem coordinate_histograms_lower {α : Type} [Fintype α]
    (bs : List Nat) (value : α → Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j≤(Finset.univ.filter fun a => value a=j).card) :
    CoeffLE (binnedPoly bs P.coeff)
      (weightedHistogram (fun a => value a<bs.length) (fun a => bs[value a]?.getD 0) (fun _ => 1)) ∧
    CoeffLE (binnedPoly bs (fun j => j*P.coeff j))
      (weightedHistogram (fun a => value a<bs.length) (fun a => bs[value a]?.getD 0) value) := by
  classical
  constructor
  · apply binnedPoly_histogram_lower
    intro j _
    simpa only [Finset.card_filter] using hP j
  · apply binnedPoly_histogram_lower
    intro j _
    have he := weighted_fiber_count value 0 j
    simp only [Nat.zero_add] at he
    rw [he]
    exact Nat.mul_le_mul_left j (hP j)

theorem coordinate_histograms_mass {α : Type} [Fintype α]
    (bs : List Nat) (value : α → Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j≤(Finset.univ.filter fun a => value a=j).card)
    (M : Nat) (hM : ∀ a, value a≤M) :
    (binnedPoly bs P.coeff).eval 1≤Fintype.card α ∧
    (binnedPoly bs (fun j => j*P.coeff j)).eval 1≤Fintype.card α*M := by
  have hp := coordinate_histograms_lower bs value P hP
  constructor
  · have h := histogram_lower_mass_le _ _ _ _ hp.1 1 (fun _ _ => le_rfl)
    simpa only [Nat.mul_one] using h
  · exact histogram_lower_mass_le _ _ _ _ hp.2 M (fun a _ => hM a)

#print axioms coordinate_histograms_lower
#print axioms coordinate_histograms_mass
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weightedHistogram_pi {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ i, Fintype (α i)] (good : (i : ι) → α i → Prop)
    (bin weight : (i : ι) → α i → Nat) :
    (∏ i, weightedHistogram (good i) (bin i) (weight i)) =
      weightedHistogram (fun a : (i : ι) → α i => ∀ i, good i (a i))
        (fun a => ∑ i, bin i (a i)) (fun a => ∏ i, weight i (a i)) := by
  classical
  unfold weightedHistogram
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : ∀ i, good i (a i)
  · rw [if_pos ha]
    simp only [ha, if_true]
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  · rw [if_neg ha]
    obtain ⟨i, hi⟩ := not_forall.mp ha
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

#print axioms weightedHistogram_pi
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem polynomial_prod_mono {ι : Type} [DecidableEq ι] (P Q : ι → Nat[X])
    (h : ∀ i, CoeffLE (P i) (Q i)) (s : Finset ι) :
    CoeffLE (∏ i ∈ s, P i) (∏ i ∈ s, Q i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; intro k; exact le_rfl
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact CoeffLE.mul _ _ _ _ (h i) ih

theorem weightedHistogram_pi_lower {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ i, Fintype (α i)] (good : (i : ι) → α i → Prop)
    (bin weight : (i : ι) → α i → Nat) (P : ι → Nat[X])
    (hP : ∀ i, CoeffLE (P i) (weightedHistogram (good i) (bin i) (weight i))) :
    CoeffLE (∏ i, P i)
      (weightedHistogram (fun a : (i : ι) → α i => ∀ i, good i (a i))
        (fun a => ∑ i, bin i (a i)) (fun a => ∏ i, weight i (a i))) := by
  classical
  rw [← weightedHistogram_pi]
  exact polynomial_prod_mono P _ hP Finset.univ

#print axioms weightedHistogram_pi_lower
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem bucket_no_carry {α : Type} [Fintype α]
    (bs : List Nat) (value : α → Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j≤(Finset.univ.filter fun a => value a=j).card)
    (M : Nat) (hM : ∀ a, value a≤M)
    (hcard : Fintype.card α<2^512) (hmass : Fintype.card α*M<2^1024) :
    bucket bs 0 (P.eval (2^512)) =
      ((binnedPoly bs P.coeff).eval (2^1024),
        (binnedPoly bs (fun j => j*P.coeff j)).eval (2^1024)) ∧
    (∀ j, (binnedPoly bs P.coeff).coeff j<2^1024) ∧
    (∀ j, (binnedPoly bs (fun j => j*P.coeff j)).coeff j<2^1024) := by
  classical
  have hc (j : Nat) : P.coeff j<2^512 := by
    have h := (Finset.card_le_card (Finset.filter_subset (fun a => value a=j) Finset.univ))
    rw [Finset.card_univ] at h
    exact (hP j).trans_lt (h.trans_lt hcard)
  have mass := coordinate_histograms_mass bs value P hP M hM
  refine ⟨?_,?_,?_⟩
  · simpa only [Nat.zero_add] using bucket_polynomial bs 0 P hc
  · intro j
    exact (polynomial_coeff_le_mass _ j).trans_lt
      (mass.1.trans_lt (hcard.trans_le (by decide +kernel)))
  · intro j
    exact (polynomial_coeff_le_mass _ j).trans_lt (mass.2.trans_lt hmass)

theorem bucket_histogram_bounds {α : Type} [Fintype α]
    (bs : List Nat) (value : α → Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j≤(Finset.univ.filter fun a => value a=j).card)
    (M n : Nat) (hM : ∀ a, value a≤M)
    (hcard : Fintype.card α<2^512) (hmass : Fintype.card α*M<2^1024)
    (hbin : ∀ i : Fin bs.length, bs[i]<n) :
    (bucket bs 0 (P.eval (2^512))).1<(2^1024)^n ∧
    (bucket bs 0 (P.eval (2^512))).2<(2^1024)^n := by
  have h := bucket_no_carry bs value P hP M hM hcard hmass
  rw [h.1]
  exact ⟨binnedPoly_eval_lt _ _ _ n (pow_pos (by decide) _) hbin h.2.1,
    binnedPoly_eval_lt _ _ _ n (pow_pos (by decide) _) hbin h.2.2⟩

#print axioms bucket_no_carry
#print axioms bucket_histogram_bounds
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem forest_histogram_lower {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (r : Nat)
    (gp : PairHistory β r → Prop) (bp : PairHistory β r → Nat)
    (gq : (Fin r → Fin 128×β) → Prop) (bq : (Fin r → Fin 128×β) → Nat)
    (P Q : Nat[X])
    (hP : CoeffLE P (weightedHistogram gp bp (pairCoverage val)))
    (hQ : CoeffLE Q (weightedHistogram gq bq (coordinateCoverage val))) :
    CoeffLE (P^4*Q)
      (weightedHistogram (fun h : ForestHistory β r => (∀ i, gp (h.1 i)) ∧ gq h.2)
        (fun h => (∑ i, bp (h.1 i))+bq h.2) (forestCoverage val)) := by
  classical
  have hpi : CoeffLE (P^4)
      (weightedHistogram (fun h : Fin 4 → PairHistory β r => ∀ i, gp (h i))
        (fun h => ∑ i, bp (h i)) (fun h => ∏ i, pairCoverage val (h i))) := by
    simpa only [Fin.prod_const] using
      weightedHistogram_pi_lower (fun _i : Fin 4 => gp) (fun _ => bp)
        (fun _ => pairCoverage val) (fun _ => P) (fun _ => hP)
  exact weightedHistogram_product_lower _ _ _ _ _ _ _ _ hpi hQ

#print axioms forest_histogram_lower
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weightedHistogram_equiv {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (good : β → Prop) (bin weight : β → Nat) :
    weightedHistogram (fun a => good (e a)) (fun a => bin (e a)) (fun a => weight (e a)) =
      weightedHistogram good bin weight := by
  classical
  unfold weightedHistogram
  exact e.sum_comp (fun b => if good b then C (weight b)*X^(bin b) else 0)

theorem weightedHistogram_partition {ι α : Type} [Fintype ι] [Fintype α]
    (piece : ι → α → Prop) (good : α → Prop) (label : ι → α → Nat)
    (bin weight : α → Nat)
    (hgood : ∀ i a, piece i a → good a)
    (hbin : ∀ i a, piece i a → label i a=bin a)
    (huniq : ∀ i j a, piece i a → piece j a → i=j) :
    CoeffLE (∑ i, weightedHistogram (piece i) (label i) weight)
      (weightedHistogram good bin weight) := by
  classical
  intro k
  rw [Polynomial.finsetSum_coeff, weightedHistogram_coeff]
  simp_rw [weightedHistogram_coeff]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases hex : ∃ i, piece i a
  · obtain ⟨i,hi⟩ := hex
    rw [Finset.sum_eq_single i]
    · rw [hbin i a hi]
      simp only [hi, hgood i a hi, true_and]
      exact le_rfl
    · intro j _ hji
      have hj : ¬piece j a := fun h => hji (huniq j i a h hi)
      simp only [hj, false_and, if_false]
    · exact fun hn => (hn (Finset.mem_univ i)).elim
  · have hz : (∑ i, if piece i a ∧ label i a=k then weight a else 0)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : ¬piece i a := fun h => hex ⟨i,h⟩
      simp only [hi, false_and, if_false]
    rw [hz]
    exact Nat.zero_le _

#print axioms weightedHistogram_partition
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.CanonicalCounting
open scoped BigOperators
open Finset

theorem lower_card : Fintype.card SigGolfResearch.LowerEffectiveCounting.«Word» < 2^132 :=
  Nat.lt_of_lt_of_le SigGolfResearch.LowerEffectiveCounting.word_card_small (Nat.sub_le _ _)

theorem lower_digit (zeros credit : Nat) (hc : credit < 128) :
    digit 132 SigGolfResearch.LowerEffectiveCounting.packed
      (65536*zeros+128*201+credit) =
    (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
      SigGolfResearch.LowerEffectiveCounting.zeros w = zeros ∧
      SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
      SigGolfResearch.LowerEffectiveCounting.score w = credit).card := by
  exact digit_histogram_of_weighted _ _ _ _ _ lower_card lower_weighted (lower_event zeros credit hc)
#print axioms lower_digit
end ClaudeWCT.Numerics.CanonicalCounting


namespace ClaudeWCT.Numerics.SharedPathList
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem add_run_bounds (i : Fin addRuns.length) :
    addRuns[i].1 ≤ addRuns[i].2.1 ∧ addRuns[i].2.1<2047 ∧ addRuns[i].2.2 ≤ 70 ∧
    addEndpoint addRuns[i].1 addRuns[i].2.2 ∧ addEndpoint addRuns[i].2.1 addRuns[i].2.2 := by
  have h := List.all_eq_true.mp addRuns_valid addRuns[i] (List.getElem_mem _)
  exact of_decide_eq_true h

theorem add_run_unique (i j : Fin addRuns.length) (d : Nat)
    (hi : addRuns[i].1 ≤ d ∧ d ≤ addRuns[i].2.1)
    (hj : addRuns[j].1 ≤ d ∧ d ≤ addRuns[j].2.1) : i=j := by
  rcases lt_trichotomy i.val j.val with hlt|he|hgt
  · have h := List.pairwise_iff_getElem.mp addRuns_ordered i.val j.val i.isLt j.isLt hlt
    simp only [Fin.getElem_fin] at hi hj
    omega
  · exact Fin.ext he
  · have h := List.pairwise_iff_getElem.mp addRuns_ordered j.val i.val j.isLt i.isLt hgt
    simp only [Fin.getElem_fin] at hi hj
    omega

noncomputable def shiftFor (d : Nat) : Nat :=
  if h : ∃ i : Fin addRuns.length, addRuns[i].1 ≤ d ∧ d ≤ addRuns[i].2.1 then
    addRuns[Classical.choose h].2.2 else 0

theorem shiftFor_eq (i : Fin addRuns.length) (d : Nat)
    (hi : addRuns[i].1 ≤ d ∧ d ≤ addRuns[i].2.1) : shiftFor d=addRuns[i].2.2 := by
  have hex : ∃ i : Fin addRuns.length, addRuns[i].1 ≤ d ∧ d ≤ addRuns[i].2.1 := ⟨i,hi⟩
  rw [shiftFor, dif_pos hex]
  exact congrArg (fun e : Fin addRuns.length => addRuns[e].2.2)
    (add_run_unique (Classical.choose hex) i d (Classical.choose_spec hex) hi)

noncomputable def mergeBin (i j : Nat) : Nat := max i j+shiftFor (i-j+(j-i))

theorem mergeBin_comm (i j : Nat) : mergeBin i j=mergeBin j i := by
  unfold mergeBin
  rw [Nat.max_comm, Nat.add_comm (i-j) (j-i)]

theorem mergeBin_forward (e : Fin addRuns.length) (i j : Nat) (hj : j ≤ i)
    (hlo : addRuns[e].1 ≤ i-j) (hhi : i-j ≤ addRuns[e].2.1) :
    mergeBin i j=i+addRuns[e].2.2 := by
  unfold mergeBin
  rw [Nat.max_eq_left hj, Nat.sub_eq_zero_of_le hj, Nat.add_zero, shiftFor_eq e _ ⟨hlo,hhi⟩]

#print axioms add_run_unique
#print axioms mergeBin_forward
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathReflection
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem addEndpoint_ratio (d b : Nat) (h : addEndpoint d b) :
    (101/100 : ℝ)^b*(100/101) ≤ 1+(100/101 : ℝ)^d ∧
      1+(100/101 : ℝ)^d ≤ (101/100 : ℝ)^b := by
  have hh := geometric_add_interval d b h.1 h.2
  have hn : 0 ≤ (100/101 : ℝ)^d := by positivity
  have he : (101/100 : ℝ)^d*(100/101 : ℝ)^d=1 := by
    rw [← mul_pow]
    norm_num
  have h0 := mul_le_mul_of_nonneg_right hh.1 hn
  have h1 := mul_le_mul_of_nonneg_right hh.2 hn
  have hl : ((101/100 : ℝ)^(b+d)*(100/101))*(100/101 : ℝ)^d =
      (101/100 : ℝ)^b*(100/101) := by
    rw [pow_add]
    calc _ = ((101/100 : ℝ)^b*(100/101))*
        ((101/100 : ℝ)^d*(100/101 : ℝ)^d) := by ring
         _ = _ := by rw [he, mul_one]
  have hu : (101/100 : ℝ)^(b+d)*(100/101 : ℝ)^d=(101/100 : ℝ)^b := by
    rw [pow_add, mul_assoc, he, mul_one]
  rw [hl, add_mul, he, one_mul] at h0
  rw [hu, add_mul, he, one_mul] at h1
  exact ⟨h0,h1⟩

theorem pow_ratio_antitone (a b : Nat) (hab : a ≤ b) :
    (100/101 : ℝ)^b ≤ (100/101 : ℝ)^a := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  have hn : (100/101 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (mul_one _)

theorem add_run_ratio (e : Fin addRuns.length) (d : Nat)
    (hlo : addRuns[e].1 ≤ d) (hhi : d ≤ addRuns[e].2.1) :
    (101/100 : ℝ)^addRuns[e].2.2*(100/101) ≤ 1+(100/101 : ℝ)^d ∧
      1+(100/101 : ℝ)^d ≤ (101/100 : ℝ)^addRuns[e].2.2 := by
  have he := add_run_bounds e
  have hl := (addEndpoint_ratio _ _ he.2.2.2.1).2
  have hh := (addEndpoint_ratio _ _ he.2.2.2.2).1
  exact ⟨hh.trans (add_le_add le_rfl (pow_ratio_antitone _ _ hhi)),
    (add_le_add le_rfl (pow_ratio_antitone _ _ hlo)).trans hl⟩

#print axioms add_run_ratio
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathReflection
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem add_ratio_shift (i j b : Nat) (hj : j ≤ i)
    (h : (101/100 : ℝ)^b*(100/101) ≤ 1+(100/101 : ℝ)^(i-j) ∧
      1+(100/101 : ℝ)^(i-j) ≤ (101/100 : ℝ)^b) :
    (101/100 : ℝ)^(i+b)*(100/101) ≤ (101/100 : ℝ)^i+(101/100 : ℝ)^j ∧
      (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^(i+b) := by
  have he : (101/100 : ℝ)^(i-j)*(100/101 : ℝ)^(i-j)=1 := by
    rw [← mul_pow]
    norm_num
  have hid : (101/100 : ℝ)^i*(100/101 : ℝ)^(i-j)=(101/100 : ℝ)^j := by
    rw [show i=j+(i-j) by omega, pow_add]
    rw [show j+(i-j)-j=i-j by omega, mul_assoc, he, mul_one]
  have hlo := mul_le_mul_of_nonneg_left h.1 (show 0≤(101/100 : ℝ)^i by positivity)
  have hhi := mul_le_mul_of_nonneg_left h.2 (show 0≤(101/100 : ℝ)^i by positivity)
  have hl : (101/100 : ℝ)^i*((101/100 : ℝ)^b*(100/101)) =
      (101/100 : ℝ)^(i+b)*(100/101) := by rw [pow_add]; ring
  rw [hl, mul_add, mul_one, hid] at hlo
  rw [mul_add, mul_one, hid, ← pow_add] at hhi
  exact ⟨hlo,hhi⟩

theorem mergeBin_interval (e : Fin addRuns.length) (i j : Nat) (hj : j ≤ i)
    (hlo : addRuns[e].1 ≤ i-j) (hhi : i-j ≤ addRuns[e].2.1) :
    (101/100 : ℝ)^(mergeBin i j)*(100/101) ≤ (101/100 : ℝ)^i+(101/100 : ℝ)^j ∧
      (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^(mergeBin i j) := by
  rw [mergeBin_forward e i j hj hlo hhi]
  exact add_ratio_shift i j _ hj (add_run_ratio e _ hlo hhi)

#print axioms mergeBin_interval
end ClaudeWCT.Numerics.SharedPathList

namespace ClaudeWCT.Numerics.SharedPathWinsor.Rows18
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- A conservative scalar certificate for gate734/cap788. Its two moment
premises, at most6.9 and0.000772, still require a finite coverage proof. -/
theorem endpoint_middle :
    (3 / 48 : ℝ) * Real.exp (69 / 10 - 6 * (99847 / 50000 - 1 / 1024)) +
      193 / 250000 ≤ 147 / 125000 := by
  let x : ℝ := 6 * (99847 / 50000 - 1 / 1024) - 69 / 10
  have hx : (0 : ℝ) ≤ x := by norm_num [x]
  have he : (155 : ℝ) ≤ Real.exp x := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx 18)
    norm_num [x, Finset.sum_range_succ, Nat.factorial]
  have hi : (Real.exp x)⁻¹ ≤ (155 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) (by norm_num)).2 he
  have hn : 69 / 10 - 6 * (99847 / 50000 - 1 / 1024) = -x := by dsimp [x]; ring
  rw [hn, Real.exp_neg]
  norm_num at hi ⊢
  linarith

theorem endpoint_high :
    (3 / 48 : ℝ) * Real.exp (69 / 10 - 6 * (2 - 6 / 2500 - 1 / 1024)) +
      193 / 250000 ≤ 147 / 125000 := by
  have h := endpoint_middle
  have he := Real.exp_le_exp.mpr (show
      (69 / 10 - 6 * (2 - 6 / 2500 - 1 / 1024) : ℝ) ≤
        69 / 10 - 6 * (99847 / 50000 - 1 / 1024) by norm_num)
  linarith

theorem endpoint_low :
    (3 / 48 : ℝ) * Real.exp (69 / 10 - 6 * (1 - 1 / 1024)) +
      193 / 250000 ≤ 49 / 100 := by
  have hx : (69 / 10 - 6 * (1 - 1 / 1024) : ℝ) ≤ 1 := by norm_num
  have he := (Real.exp_le_exp.mpr hx).trans (le_of_lt Real.exp_one_lt_d9)
  nlinarith

#print axioms endpoint_middle
#print axioms endpoint_high
#print axioms endpoint_low
end ClaudeWCT.Numerics.SharedPathWinsor.Rows18


namespace ClaudeWCT.Numerics.CanonicalCompression
open Finset
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem fold_add_sum {α : Type} (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun s e => s + f e) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

theorem filter_sum {α : Type} (p : α → Prop) [DecidablePred p]
    (f : α → Nat) (xs : List α) :
    ((xs.filter fun a => decide (p a)).map f).sum =
      (xs.map fun a => if p a then f a else 0).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases hp : p x <;> simp [hp, ih]

theorem acceptedMass_sum (hist : List (Nat × Nat)) (floor : Nat) :
    acceptedMass hist floor = (hist.map fun e => if floor ≤ e.1 then e.2 else 0).sum := by
  rw [acceptedMass, fold_add_sum, Nat.zero_add]
  exact filter_sum _ _ _

theorem nextMass_sum (hist : List (Nat × Nat)) (floor residual : Nat) (next : Array Nat) :
    nextMass hist floor residual next =
      (hist.map fun e => if floor ≤ e.1 then e.2 * next[residual-e.1]?.getD 0 else 0).sum := by
  rw [nextMass, fold_add_sum, Nat.zero_add]
  exact filter_sum _ _ _

end ClaudeWCT.Numerics.CanonicalCompression
namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset CanonicalCompression
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem histogramWeight_sum (hist : List (Nat × Nat)) (credit : Nat) :
    histogramWeight hist credit =
      (hist.map fun e => if e.1 = credit then e.2 else 0).sum := by
  have he : (fun (s : Nat) (e : Nat × Nat) => if e.1 = credit then s + e.2 else s) =
      (fun s e => s + if e.1 = credit then e.2 else 0) := by
    funext s e
    split_ifs <;> simp
  rw [histogramWeight, he, fold_add_sum, Nat.zero_add]

theorem histogram_sum_weighted (hist : List (Nat × Nat)) (n : Nat)
    (hbound : ∀ e ∈ hist, e.1 < n) (f : Nat → Nat) :
    ∑ i : Fin n, histogramWeight hist i.val * f i.val =
      (hist.map fun e => e.2 * f e.1).sum := by
  induction hist with
  | nil => simp [histogramWeight_sum]
  | cons e hist ih =>
      have he : e.1 < n := hbound e List.mem_cons_self
      have hh : ∀ x ∈ hist, x.1 < n := fun x hx => hbound x (List.mem_cons_of_mem e hx)
      simp only [histogramWeight_sum, List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
      simp_rw [← histogramWeight_sum]
      rw [ih hh]
      congr 1
      have ht : (fun i : Fin n => (if e.1 = i.val then e.2 else 0) * f i.val) =
          (fun i => if i = (⟨e.1, he⟩ : Fin n) then e.2 * f e.1 else 0) := by
        funext i
        by_cases hc : e.1 = i.val
        · have hi : i = (⟨e.1, he⟩ : Fin n) := Fin.ext hc.symm
          simp only [if_pos hc, if_pos hi]
          rw [hc]
        · have hi : i ≠ (⟨e.1, he⟩ : Fin n) := fun hi => hc (congrArg Fin.val hi).symm
          simp only [if_neg hc, if_neg hi, zero_mul]
      rw [ht]
      simp

theorem acceptedMass_finite (hist : List (Nat × Nat)) (n floor : Nat)
    (hbound : ∀ e ∈ hist, e.1 < n) :
    acceptedMass hist floor = ∑ i : Fin n, if floor ≤ i.val then histogramWeight hist i.val else 0 := by
  have h := histogram_sum_weighted hist n hbound (fun c => if floor ≤ c then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [acceptedMass_sum]
  simpa only [mul_ite, mul_one, mul_zero] using h.symm

theorem nextMass_finite (hist : List (Nat × Nat)) (n floor residual : Nat) (next : Array Nat)
    (hbound : ∀ e ∈ hist, e.1 < n) :
    nextMass hist floor residual next =
      ∑ i : Fin n, if floor ≤ i.val then histogramWeight hist i.val * next[residual-i.val]?.getD 0 else 0 := by
  have h := histogram_sum_weighted hist n hbound
    (fun c => if floor ≤ c then next[residual-c]?.getD 0 else 0)
  simp only [mul_ite, mul_zero] at h
  rw [nextMass_sum]
  exact h.symm

#print axioms acceptedMass_finite
#print axioms nextMass_finite
end ClaudeWCT.Numerics.CanonicalHistogram

namespace ClaudeWCT.Numerics.CanonicalCompression
open ENNReal
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem transition_enn (zn zd den weighted value rejected unit : Nat)
    (hzd : 0 < zd) (hden : 0 < den) (hunit : 0 < unit)
    (hsub : zn * rejected ≤ zd * den)
    (hrow : zn * weighted ≤ value * (zd * den - zn * rejected)) :
    ((zn : ENNReal) / zd) * ((weighted : ENNReal) / (den * unit) +
      ((rejected : ENNReal) / den) * ((value : ENNReal) / unit)) ≤ (value : ENNReal) / unit := by
  have hden0 : (den : ENNReal) ≠ 0 := by exact_mod_cast hden.ne'
  have hzd0 : (zd : ENNReal) ≠ 0 := by exact_mod_cast hzd.ne'
  have hunit0 : (unit : ENNReal) ≠ 0 := by exact_mod_cast hunit.ne'
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_natCast, Nat.cast_mul]
  exact transition_sound zn zd den weighted value rejected unit hzd hden hunit hsub hrow

theorem recurrenceCheck_sound (den : Nat) (hist : List (Nat × Nat))
    (floor residual : Nat) (next : Array Nat) (value : Nat)
    (hden : 0 < den) (hcheck : recurrenceCheck den hist floor residual next value = true) :
    1 ≤ (value : ENNReal) / scale ∧
    ((zNum : ENNReal) / zDen) *
      ((nextMass hist floor residual next : ENNReal) / (den * scale) +
       ((den - acceptedMass hist floor : Nat) : ENNReal) / den * ((value : ENNReal) / scale)) ≤
      (value : ENNReal) / scale := by
  simp only [recurrenceCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hbase, hmass⟩, hnext⟩, hsub⟩, hrow⟩
  have hscale0 : (scale : ENNReal) ≠ 0 := by norm_num [scale]
  constructor
  · apply (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mp
    simp only [ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_natCast]
    apply (le_div_iff₀ (show (0 : ℝ) < scale by norm_num [scale])).2
    simpa using (show (scale : ℝ) ≤ value by exact_mod_cast hbase)
  · exact transition_enn zNum zDen den (nextMass hist floor residual next) value
      (den - acceptedMass hist floor) scale (by norm_num [zDen]) hden (by norm_num [scale])
      hsub.le hrow

#print axioms transition_enn
#print axioms recurrenceCheck_sound
end ClaudeWCT.Numerics.CanonicalCompression


namespace ClaudeWCT.Numerics.SharedPathList
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- A coverage value and its conservatively rounded geometric bin. -/
structure RoundedInterval (loss bin : Nat) (x : ℝ) : Prop where
  nonneg : 0 ≤ x
  lower : (100/101 : ℝ)^loss * (101/100 : ℝ)^bin ≤ x
  upper : x ≤ (101/100 : ℝ)^bin

theorem RoundedInterval.mul {a b i j : Nat} {x y : ℝ}
    (hx : RoundedInterval a i x) (hy : RoundedInterval b j y) :
    RoundedInterval (a+b) (i+j) (x*y) := by
  refine ⟨mul_nonneg hx.nonneg hy.nonneg, ?_, ?_⟩
  · calc
      (100/101 : ℝ)^(a+b) * (101/100 : ℝ)^(i+j) =
          ((100/101 : ℝ)^a * (101/100 : ℝ)^i) *
            ((100/101 : ℝ)^b * (101/100 : ℝ)^j) := by
              rw [pow_add, pow_add]
              ring
      _ ≤ x*y := mul_le_mul hx.lower hy.lower (by positivity) hx.nonneg
  · calc
      x*y ≤ (101/100 : ℝ)^i * (101/100 : ℝ)^j :=
        mul_le_mul hx.upper hy.upper hy.nonneg (by positivity)
      _ = _ := (pow_add _ _ _).symm

theorem RoundedInterval.add {a i j k : Nat} {x y : ℝ}
    (hx : RoundedInterval a i x) (hy : RoundedInterval a j y)
    (hlo : (101/100 : ℝ)^k*(100/101) ≤
      (101/100 : ℝ)^i+(101/100 : ℝ)^j)
    (hhi : (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^k) :
    RoundedInterval (a+1) k (x+y) := by
  refine ⟨add_nonneg hx.nonneg hy.nonneg, ?_, (add_le_add hx.upper hy.upper).trans hhi⟩
  calc
    (100/101 : ℝ)^(a+1) * (101/100 : ℝ)^k =
        (100/101 : ℝ)^a * ((101/100 : ℝ)^k*(100/101)) := by
          rw [pow_succ]
          ring
    _ ≤ (100/101 : ℝ)^a * ((101/100 : ℝ)^i+(101/100 : ℝ)^j) :=
      mul_le_mul_of_nonneg_left hlo (by positivity)
    _ ≤ x+y := by rw [mul_add]; exact add_le_add hx.lower hy.lower

theorem RoundedInterval.prod {ι : Type} [DecidableEq ι]
    (s : Finset ι) (loss bin : ι → Nat) (x : ι → ℝ)
    (hx : ∀ i ∈ s, RoundedInterval (loss i) (bin i) (x i)) :
    RoundedInterval (∑ i ∈ s, loss i) (∑ i ∈ s, bin i) (∏ i ∈ s, x i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; constructor <;> norm_num
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hx i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hx j (Finset.mem_insert_of_mem hj)))

theorem RoundedInterval.forest (bins : Fin 4 → Nat) (xs : Fin 4 → ℝ)
    (bin : Nat) (y : ℝ)
    (hx : ∀ i, RoundedInterval 3 (bins i) (xs i))
    (hy : RoundedInterval 1 bin y) :
    RoundedInterval 13 ((∑ i, bins i)+bin) ((∏ i, xs i)*y) := by
  have hp := RoundedInterval.prod Finset.univ (fun _ : Fin 4 => 3) bins xs
    (fun i _ => hx i)
  have hc : (∑ _i : Fin 4, (3 : Nat)) = 12 := by decide
  rw [hc] at hp
  exact hp.mul hy

theorem RoundedInterval.fee_bounds {bin : Nat} {x : ℝ}
    (hx : RoundedInterval 13 bin x) :
    ClaudeWCT.Numerics.SharedFees.lowerValue bin ≤ (734 : ℝ)/2^66*x ∧
      (734 : ℝ)/2^66*x ≤ ClaudeWCT.Numerics.SharedFees.upperValue bin := by
  simp only [ClaudeWCT.Numerics.SharedFees.lowerValue_power,
    ClaudeWCT.Numerics.SharedFees.upperValue_power]
  constructor
  · have h := mul_le_mul_of_nonneg_left hx.lower (by positivity : (0 : ℝ) ≤ 734/2^66)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  · exact mul_le_mul_of_nonneg_left hx.upper (by positivity)

#print axioms RoundedInterval.forest
#print axioms RoundedInterval.fee_bounds
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedFees
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem finite_bin_rebate {α : Type} [Fintype α]
    (n : Nat) (good : α → Prop) [DecidablePred good] (bin : α → Nat)
    (weight : α → ℝ) (rebate : Nat → ℝ) :
    (∑ j ∈ range n,
      (∑ a, if good a ∧ bin a=j then weight a else 0)*rebate j) =
    ∑ a, if good a ∧ bin a<n then weight a*rebate (bin a) else 0 := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hg : good a
  · simp only [hg, true_and, ite_mul, zero_mul]
    simp [Finset.mem_range, eq_comm]
  · simp [hg]

/-- A lower histogram certifies a rebate from a global cost bound. Histories
omitted by the histogram retain the full global cost. -/
theorem histogram_fee_bound {α : Type} [Fintype α]
    (n : Nat) (good : α → Prop) [DecidablePred good] (bin : α → Nat)
    (weight cost : α → ℝ) (lower fee : Nat → ℝ) (κ G : ℝ)
    (hκ : 0 ≤ κ)
    (hfee : ∀ j, j<n → fee j ≤ G)
    (hlower : ∀ j, j<n → lower j ≤
      ∑ a, if good a ∧ bin a=j then weight a else 0)
    (hglobal : ∀ a, cost a ≤ κ*weight a*G)
    (hlocal : ∀ a, good a → bin a<n → cost a ≤ κ*weight a*fee (bin a)) :
    (∑ a, cost a) + κ*(∑ j ∈ range n, lower j*(G-fee j)) ≤
      κ*(∑ a, weight a)*G := by
  classical
  have hpoint (a : α) : cost a +
      κ*(if good a ∧ bin a<n then weight a*(G-fee (bin a)) else 0) ≤
        κ*weight a*G := by
    by_cases hg : good a ∧ bin a<n
    · rw [if_pos hg]
      nlinarith [hlocal a hg.1 hg.2]
    · rw [if_neg hg, mul_zero, add_zero]
      exact hglobal a
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset α)) (fun a _ => hpoint a)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hs
  have hrebate : (∑ j ∈ range n, lower j*(G-fee j)) ≤
      ∑ a, if good a ∧ bin a<n then weight a*(G-fee (bin a)) else 0 := by
    rw [← finite_bin_rebate n good bin weight (fun j => G-fee j)]
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (hlower j (Finset.mem_range.mp hj))
      (sub_nonneg.mpr (hfee j (Finset.mem_range.mp hj)))
  exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hrebate hκ)).trans hs

#print axioms histogram_fee_bound
end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem packFun_finset_sum {ι : Type} (s : Finset ι) (B n : Nat) (f : ι → Nat → Nat) :
    packFun B n (fun j => ∑ i ∈ s, f i j) = ∑ i ∈ s, packFun B n (f i) := by
  unfold packFun
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

theorem sum_eq_packFun {ι : Type} (s : Finset ι) (B n : Nat) (a : ι → Nat)
    (ha : ∀ i ∈ s, a i < B^n) :
    (∑ i ∈ s, a i) = packFun B n (fun j => ∑ i ∈ s, digit B (a i) j) := by
  rw [packFun_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [packFun_digits, Nat.mod_eq_of_lt (ha i hi)]

theorem digit_sum_of_bound {ι : Type} (s : Finset ι) (B n : Nat) (a : ι → Nat)
    (hB : 0 < B) (ha : ∀ i ∈ s, a i < B^n)
    (hc : ∀ j, j < n → (∑ i ∈ s, digit B (a i) j) < B)
    (j : Nat) (hj : j < n) :
    digit B (∑ i ∈ s, a i) j = ∑ i ∈ s, digit B (a i) j := by
  rw [sum_eq_packFun s B n a ha]
  exact digit_packFun B n _ hB hc j hj

theorem sum_packed_lt {ι : Type} (s : Finset ι) (B n : Nat) (a : ι → Nat)
    (hB : 0 < B) (ha : ∀ i ∈ s, a i < B^n)
    (hc : ∀ j, j < n → (∑ i ∈ s, digit B (a i) j) < B) :
    (∑ i ∈ s, a i) < B^n := by
  rw [sum_eq_packFun s B n a ha]
  exact packFun_lt B n _ hB hc

theorem digit_polynomial_eval (P : Nat[X]) (B n : Nat)
    (hB : 0 < B) (hc : ∀ j, j < n → P.coeff j < B)
    (hz : ∀ j, n ≤ j → P.coeff j = 0)
    (j : Nat) (hj : j < n) : digit B (P.eval B) j = P.coeff j := by
  rw [polynomial_eval_packFun P B n hz]
  exact digit_packFun B n _ hB hc j hj

#print axioms digit_sum_of_bound
#print axioms digit_polynomial_eval
end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weightedHistogram_selector_split {α : Type} [Fintype α] (r : Nat)
    (good : (t u : Nat) → (Fin t → α) → (Fin t → α) →
      (Fin u → α) → (Fin u → α) → Prop)
    (bin weight : (t u : Nat) → (Fin t → α) → (Fin t → α) →
      (Fin u → α) → (Fin u → α) → Nat) :
    weightedHistogram
      (fun h : (Fin r → Fin 2) × (Fin r → α) × (Fin r → α) =>
        good (occ h.1 0) (occ h.1 1)
          (splitRanks h.1 h.2.1 0) (splitRanks h.1 h.2.2 0)
          (splitRanks h.1 h.2.1 1) (splitRanks h.1 h.2.2 1))
      (fun h => bin (occ h.1 0) (occ h.1 1)
          (splitRanks h.1 h.2.1 0) (splitRanks h.1 h.2.2 0)
          (splitRanks h.1 h.2.1 1) (splitRanks h.1 h.2.2 1))
      (fun h => weight (occ h.1 0) (occ h.1 1)
          (splitRanks h.1 h.2.1 0) (splitRanks h.1 h.2.2 0)
          (splitRanks h.1 h.2.1 1) (splitRanks h.1 h.2.2 1)) =
    ∑ t ∈ range (r+1), r.choose t •
      weightedHistogram
        (fun h : ((Fin t → α) × (Fin t → α)) ×
          ((Fin (r-t) → α) × (Fin (r-t) → α)) =>
            good t (r-t) h.1.1 h.1.2 h.2.1 h.2.2)
        (fun h => bin t (r-t) h.1.1 h.1.2 h.2.1 h.2.2)
        (fun h => weight t (r-t) h.1.1 h.1.2 h.2.1 h.2.2) := by
  classical
  unfold weightedHistogram
  simp only [Fintype.sum_prod_type]
  exact sum_pair_split r (fun t u A₀ B₀ A₁ B₁ =>
    if good t u A₀ B₀ A₁ B₁ then
      C (weight t u A₀ B₀ A₁ B₁)*X^(bin t u A₀ B₀ A₁ B₁) else 0)

#print axioms weightedHistogram_selector_split
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

abbrev AddPiece := Fin addRuns.length × Bool

def addPieceGood (e : AddPiece) (i j : Nat) : Prop :=
  if e.2 then i<j ∧ addRuns[e.1].1 ≤ j-i ∧ j-i ≤ addRuns[e.1].2.1
  else j ≤ i ∧ addRuns[e.1].1 ≤ i-j ∧ i-j ≤ addRuns[e.1].2.1

def addPieceBin (e : AddPiece) (i j : Nat) : Nat :=
  (if e.2 then j else i)+addRuns[e.1].2.2

theorem addPiece_unique (e f : AddPiece) (i j : Nat)
    (he : addPieceGood e i j) (hf : addPieceGood f i j) : e=f := by
  rcases e with ⟨e,be⟩
  rcases f with ⟨f,bf⟩
  cases be <;> cases bf <;> simp only [addPieceGood, Bool.false_eq_true, if_false, if_true] at he hf
  · exact Prod.ext (add_run_unique e f (i-j) he.2 hf.2) rfl
  · omega
  · omega
  · exact Prod.ext (add_run_unique e f (j-i) he.2 hf.2) rfl

theorem addPiece_bin (e : AddPiece) (i j : Nat) (he : addPieceGood e i j) :
    addPieceBin e i j=mergeBin i j := by
  rcases e with ⟨e,b⟩
  cases b <;> simp only [addPieceGood, Bool.false_eq_true, if_false, if_true] at he
  · exact (mergeBin_forward e i j he.1 he.2.1 he.2.2).symm
  · rw [mergeBin_comm]
    exact (mergeBin_forward e j i (Nat.le_of_lt he.1) he.2.1 he.2.2).symm

theorem pair_partition_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) (gb : β → Prop) (ba wa : α → Nat) (bb wb : β → Nat) :
    CoeffLE (∑ e : AddPiece,
      weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2 ∧ addPieceGood e (ba p.1) (bb p.2))
        (fun p => addPieceBin e (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2))
      (weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
        (fun p => mergeBin (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2)) := by
  apply weightedHistogram_partition
  · intro e p hp
    exact ⟨hp.1,hp.2.1⟩
  · intro e p hp
    exact addPiece_bin e _ _ hp.2.2
  · intro e f p he hf
    exact addPiece_unique e f _ _ he.2.2 hf.2.2

#print axioms pair_partition_lower
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset ClaudeWCT.Numerics.N600
set_option maxHeartbeats 2000000

theorem coordinate_coverage_pos {β C : Type} [Fintype β] [Fintype C] [DecidableEq C]
    (val : β → Fin 6 → Nat) {r : Nat} (hr : 0<r) (E : Fin r → C×β) :
    0<coordinateCoverage val E := by
  classical
  unfold coordinateCoverage
  apply Finset.card_pos.mpr
  refine ⟨E ⟨0,hr⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  intro i
  exact ⟨⟨0,hr⟩,rfl,le_rfl⟩

#print axioms coordinate_coverage_pos
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem paidPlain_sums (B : Nat) (fs : List (Nat × Nat)) (p : Nat) :
    paidPlain B fs p =
      (∑ i : Fin fs.length, digit B p i.val,
       ∑ i : Fin fs.length, digit B p i.val * fs[i].1,
       ∑ i : Fin fs.length, digit B p i.val * fs[i].2) := by
  induction fs generalizing p with
  | nil => simp only [paidPlain, List.length_nil, Fin.sum_univ_zero]
  | cons e fs ih =>
    rw [paidPlain, ih]
    simp only [List.length_cons, Fin.sum_univ_succ,
      Fin.getElem_fin, List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero, Fin.val_succ,
      digit, Nat.pow_zero, Nat.div_one, Nat.pow_succ,
      Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem paidTree_polynomial (fuel : Nat) (fs : List (Nat × Nat)) (P : Nat[X])
    (hc : ∀ j, P.coeff j < 2^4096) :
    paidTree fuel fs (P.eval (2^4096)) =
      (∑ i : Fin fs.length, P.coeff i.val,
       ∑ i : Fin fs.length, P.coeff i.val * fs[i].1,
       ∑ i : Fin fs.length, P.coeff i.val * fs[i].2) := by
  rw [paidTree_plain, paidPlain_sums]
  have hd (i : Nat) : digit (2^4096) (P.eval (2^4096)) i = P.coeff i :=
    ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) i P hc
  simp only [hd]

theorem paidTree_polynomial_mass (fuel : Nat) (fs : List (Nat × Nat)) (P : Nat[X])
    (hc : ∀ j, P.coeff j < 2^4096) :
    (paidTree fuel fs (P.eval (2^4096))).1 ≤ P.eval 1 := by
  rw [paidTree_polynomial fuel fs P hc]
  dsimp only
  rw [Fin.sum_univ_eq_sum_range]
  exact ClaudeWCT.Numerics.N600.sum_coeff_le_eval_one P (Finset.range fs.length)

#print axioms paidTree_polynomial
#print axioms paidTree_polynomial_mass
end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Disjoint retained pieces may be added in packed form without a carry.
The bound comes from the mass of the actual history space. -/
theorem packed_histogram_sum_lower {ι α : Type} [Fintype ι] [Fintype α]
    (B n M : Nat) (hB : 0<B)
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (p : ι → Nat) (P : ι → Nat[X])
    (hp : ∀ e, p e<B^n)
    (hd : ∀ e j, j<n → digit B (p e) j≤(P e).coeff j)
    (hP : CoeffLE (∑ e, P e) (weightedHistogram good bin weight))
    (hM : ∀ a, good a → weight a≤M) (hmass : Fintype.card α*M<B) :
    (∑ e, p e)<B^n ∧
      ∀ j, j<n → digit B (∑ e, p e) j≤(weightedHistogram good bin weight).coeff j := by
  have hc (j : Nat) (hj : j<n) :
      (∑ e, digit B (p e) j)<B := by
    calc _ ≤ ∑ e, (P e).coeff j := Finset.sum_le_sum (fun e _ => hd e j hj)
         _ = (∑ e, P e).coeff j := (Polynomial.finset_sum_coeff _ _ _).symm
         _ ≤ (weightedHistogram good bin weight).coeff j := hP j
         _ ≤ (weightedHistogram good bin weight).eval 1 := polynomial_coeff_le_mass _ _
         _ ≤ Fintype.card α*M := weightedHistogram_mass_le good bin weight M hM
         _ < B := hmass
  refine ⟨sum_packed_lt univ B n p hB (fun e _ => hp e) hc, ?_⟩
  intro j hj
  rw [digit_sum_of_bound univ B n p hB (fun e _ => hp e) hc j hj]
  calc _ ≤ ∑ e, (P e).coeff j := Finset.sum_le_sum (fun e _ => hd e j hj)
       _ = (∑ e, P e).coeff j := (Polynomial.finset_sum_coeff _ _ _).symm
       _ ≤ _ := hP j

#print axioms packed_histogram_sum_lower
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem directed_cross_small {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat)
    (ap af bp bf : Nat → Nat)
    (haP : ∀ i, ap i ≤ ∑ a, if ga a ∧ ba a=i then 1 else 0)
    (haF : ∀ i, af i ≤ ∑ a, if ga a ∧ ba a=i then wa a else 0)
    (hbP : ∀ j, bp j ≤ ∑ b, if gb b ∧ bb b=j then 1 else 0)
    (hbF : ∀ j, bf j ≤ ∑ b, if gb b ∧ bb b=j then wb b else 0)
    (Ma Mb B : Nat) (hwa : ∀ a, wa a≤Ma) (hwb : ∀ b, wb b≤Mb)
    (hB : Fintype.card α*Fintype.card β*(Ma+Mb)<B)
    (i : Nat) (s : Finset Nat) :
    af i*(∑ j ∈ s, bp j) + ap i*(∑ j ∈ s, bf j)<B := by
  apply (directed_fiber_lower ga gb ba wa bb wb ap af bp bf haP haF hbP hbF i s).trans_lt
  calc (∑ p : α×β, if (ga p.1 ∧ ba p.1=i) ∧ (gb p.2 ∧ bb p.2∈s)
          then wa p.1+wb p.2 else 0) ≤ ∑ _p : α×β, (Ma+Mb) := by
        apply Finset.sum_le_sum
        intro p _
        split_ifs
        · exact Nat.add_le_add (hwa p.1) (hwb p.2)
        · exact Nat.zero_le _
       _ = Fintype.card α*Fintype.card β*(Ma+Mb) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          nsmul_eq_mul, Nat.cast_id]
       _ < B := hB

#print axioms directed_cross_small
end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset
open ClaudeWCT.Numerics.SharedPathList (Cell addRuns)
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem fold_add_pair {α : Type} (xs : List α) (f g : α → Nat) (acc : Nat) :
    xs.foldl (fun s e => s+f e+g e) acc =
      acc+(xs.map (fun e => f e+g e)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons e xs ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

theorem list_sum_fin {α : Type} (xs : List α) (f : α → Nat) :
    (xs.map f).sum = ∑ i : Fin xs.length, f xs[i] := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Fin.sum_univ_succ,
      Fin.getElem_fin, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ]

def addPieceValue (a b : Cell) (e : Fin addRuns.length × Bool) : Nat :=
  if e.2 then
    if addRuns[e.1].2.1=0 then 0 else
      directedFirst b (prefixes a.1, prefixes a.2)
        (max 1 addRuns[e.1].1) addRuns[e.1].2.1 addRuns[e.1].2.2
  else directedFirst a (prefixes b.1, prefixes b.2)
      addRuns[e.1].1 addRuns[e.1].2.1 addRuns[e.1].2.2

theorem addFirst_eq_piece_sum (a b : Cell) :
    addFirst a b = ∑ e : Fin addRuns.length × Bool, addPieceValue a b e := by
  rw [addFirst, fold_add_pair, Nat.zero_add, list_sum_fin]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [addPieceValue, Nat.add_comm]

theorem addPieceValue_bound (a b : Cell) (e : Fin addRuns.length × Bool) :
    addPieceValue a b e < (2^1024)^2048 := by
  have hb (a pref : Cell) (lo hi shift : Nat) :
      directedFirst a pref lo hi shift < (2^1024)^2048 := by
    unfold directedFirst cutMask
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, ←pow_mul]
    exact Nat.mod_lt _ (by positivity)
  unfold addPieceValue
  split_ifs
  · positivity
  · exact hb _ _ _ _ _
  · exact hb _ _ _ _ _

#print axioms addFirst_eq_piece_sum
#print axioms addPieceValue_bound
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem addFirst_histogram_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat) (a b : Cell)
    (Ma Mb : Nat) (hwa : ∀ x, wa x≤Ma) (hwb : ∀ y, wb y≤Mb)
    (hmass : Fintype.card α*Fintype.card β*(Ma+Mb)<2^1024)
    (hpiece : ∀ (e : AddPiece) j, j<2048 →
      digit (2^1024) (addPieceValue a b e) j ≤
        (weightedHistogram
          (fun p : α×β => ga p.1 ∧ gb p.2 ∧ addPieceGood e (ba p.1) (bb p.2))
          (fun p => addPieceBin e (ba p.1) (bb p.2))
          (fun p => wa p.1+wb p.2)).coeff j) :
    addFirst a b<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024) (addFirst a b) j≤
        (weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
          (fun p => mergeBin (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2)).coeff j := by
  classical
  rw [addFirst_eq_piece_sum]
  apply packed_histogram_sum_lower (2^1024) 2048 (Ma+Mb) (by positivity)
    (fun p : α×β => ga p.1 ∧ gb p.2)
    (fun p => mergeBin (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2)
    (addPieceValue a b)
    (fun e => weightedHistogram
      (fun p : α×β => ga p.1 ∧ gb p.2 ∧ addPieceGood e (ba p.1) (bb p.2))
      (fun p => addPieceBin e (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2))
    (addPieceValue_bound a b) hpiece (pair_partition_lower ga gb ba wa bb wb)
  · intro p _
    exact Nat.add_le_add (hwa p.1) (hwb p.2)
  · simpa only [Fintype.card_prod] using hmass

#print axioms addFirst_histogram_lower
end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedFees
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Exact integer accounting of retained fees and omitted first moment. -/
theorem histogram_paid_bound {α : Type} [Fintype α]
    (n : Nat) (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (cost : α → ℝ) (lower fee : Nat → Nat) (κ : ℝ) (G : Nat)
    (hκ : 0≤κ) (hfee : ∀ j, j<n → fee j≤G)
    (hlower : ∀ j, j<n → lower j≤∑ a, if good a ∧ bin a=j then weight a else 0)
    (hmass : (∑ j ∈ range n, lower j)≤∑ a, weight a)
    (hglobal : ∀ a, cost a≤κ*(weight a : ℝ)*G)
    (hlocal : ∀ a, good a → bin a<n → cost a≤κ*(weight a : ℝ)*(fee (bin a) : ℝ)) :
    (∑ a, cost a)≤κ*((((∑ j ∈ range n, lower j*fee j) +
      G*((∑ a, weight a)-(∑ j ∈ range n, lower j)) : Nat) : ℝ)) := by
  classical
  have h := histogram_fee_bound n good bin (fun a => (weight a : ℝ)) cost
    (fun j => (lower j : ℝ)) (fun j => (fee j : ℝ)) κ (G : ℝ) hκ
    (fun j hj => by exact_mod_cast hfee j hj)
    (fun j hj => by exact_mod_cast hlower j hj) hglobal hlocal
  have he : (∑ j ∈ range n, (lower j : ℝ)*((G : ℝ)-(fee j : ℝ))) =
      (G : ℝ)*(∑ j ∈ range n, (lower j : ℝ))-
        ∑ j ∈ range n, (lower j : ℝ)*(fee j : ℝ) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ←Finset.sum_mul]
    ring
  rw [he] at h
  push_cast [Nat.cast_sub hmass]
  nlinarith [h]

#print axioms histogram_paid_bound
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.CanonicalCompression
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem ceilDiv_mul_ge_left (n d : Nat) (hd : 0 < d) : n ≤ d * ceilDiv n d := by
  unfold ceilDiv
  have hrem := Nat.mod_lt (n + d - 1) hd
  have hdiv := Nat.mod_add_div (n + d - 1) d
  omega

theorem mulUp_sound (a b : Nat) :
    (a : ℝ) / scale * ((b : ℝ) / scale) ≤ (mulUp a b : ℝ) / scale := by
  have hs : 0 < scale := by norm_num [scale]
  have hh := ceilDiv_mul_ge_left (a*b) scale hs
  have hc : (a : ℝ) * b ≤ (scale : ℝ) * mulUp a b := by
    exact_mod_cast hh
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos hsR hsR) hsR).2
  nlinarith

/-- The reflected repeated-squaring evaluator rounds every multiplication up. -/
theorem powerUp_sound (base exponent : Nat) :
    ((base : ℝ) / scale) ^ exponent ≤ (powerUp base exponent : ℝ) / scale := by
  induction exponent using Nat.strong_induction_on generalizing base with
  | h exponent ih =>
      rw [powerUp]
      by_cases he : exponent = 0
      · simp [he, scale]
      · rw [if_neg he]
        have hhalf : exponent / 2 < exponent := Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide)
        have hi := ih (exponent / 2) hhalf (mulUp base base)
        have hbase : (0 : ℝ) ≤ (base : ℝ) / scale := by positivity
        have hsq : ((base : ℝ) / scale) ^ 2 ≤ (mulUp base base : ℝ) / scale := by
          simpa only [pow_two] using mulUp_sound base base
        have hh : ((base : ℝ) / scale) ^ (2 * (exponent / 2)) ≤
            (powerUp (mulUp base base) (exponent / 2) : ℝ) / scale := by
          rw [pow_mul]
          exact (pow_le_pow_left₀ (sq_nonneg _) hsq _).trans hi
        split_ifs with hp
        · convert hh using 1
          congr 1
          omega
        · have hm : exponent % 2 = 1 := by omega
          have hrepr : exponent = 1 + 2 * (exponent / 2) := by omega
          conv_lhs => rw [hrepr, pow_add, pow_one]
          exact (mul_le_mul_of_nonneg_left hh hbase).trans
            (mulUp_sound base (powerUp (mulUp base base) (exponent / 2)))

#print axioms ceilDiv_mul_ge_left
#print axioms mulUp_sound
#print axioms powerUp_sound
end ClaudeWCT.Numerics.CanonicalCompression


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def packedPoly (B n p : Nat) : Nat[X] := polyOf n (digit B p)

theorem packedPoly_eval (B n p : Nat) (hp : p<B^n) :
    (packedPoly B n p).eval B=p := by
  rw [packedPoly, polyOf_eval, packFun_digits, Nat.mod_eq_of_lt hp]

theorem packedPoly_coeff_lt (B n p : Nat) (hB : 0<B) (j : Nat) :
    (packedPoly B n p).coeff j<B := by
  rw [packedPoly, polyOf_coeff]
  split_ifs
  · exact Nat.mod_lt _ hB
  · exact hB

theorem packedPoly_below (B n p : Nat) (Q : Nat[X])
    (hd : ∀ j, j<n → digit B p j≤Q.coeff j) :
    CoeffLE (packedPoly B n p) Q := by
  intro j
  rw [packedPoly, polyOf_coeff]
  split_ifs with hj
  · exact hd j hj
  · exact Nat.zero_le _

theorem changeBase_polynomial (B C h p : Nat) (hB : 0<B) (hp : p<B^(2^h)) :
    changeBase B C h p=(packedPoly B (2^h) p).eval C := by
  rw [changeBase_model B C hB h p hp, packedPoly, polyOf_eval]

#print axioms packedPoly_below
#print axioms changeBase_polynomial
end ClaudeWCT.Numerics.SharedDigitBlock

namespace ClaudeWCT.Numerics.SharedPathPacked
open Polynomial ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000

theorem spread_polynomial (h p : Nat) (hp : p<(2^1024)^(2^h)) :
    spread h p=(packedPoly (2^1024) (2^h) p).eval (2^4096) := by
  rw [spread_eq_changeBase]
  exact changeBase_polynomial _ _ h p (by positivity) hp

theorem forest_packed_polynomial (p q : Nat)
    (hp : p<(2^1024)^2048) (hq : q<(2^1024)^1024) :
    (spread 11 p)^4*spread 10 q =
      ((packedPoly (2^1024) 2048 p)^4*packedPoly (2^1024) 1024 q).eval (2^4096) := by
  have hp' : p<(2^1024)^(2^11) := by simpa only [show (2:Nat)^11=2048 from rfl] using hp
  have hq' : q<(2^1024)^(2^10) := by simpa only [show (2:Nat)^10=1024 from rfl] using hq
  rw [spread_polynomial 11 p hp', spread_polynomial 10 q hq']
  simp only [Polynomial.eval_mul, Polynomial.eval_pow,
    show (2:Nat)^11=2048 from rfl, show (2:Nat)^10=1024 from rfl]

#print axioms forest_packed_polynomial
end ClaudeWCT.Numerics.SharedPathPacked
