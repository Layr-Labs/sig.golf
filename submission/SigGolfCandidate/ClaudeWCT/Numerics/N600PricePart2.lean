import SigGolfCandidate.ClaudeWCT.Numerics.N600PricePart1

set_option Elab.async false


/-! Parameterized exponential stop-loss bound for the private shared-path
construction. The finite coverage certificate supplying the moment premises
is separate; these lemmas alone do not certify the changed scheme. -/
namespace ClaudeWCT.Numerics.SharedPathWinsor
open ENNReal Finset ClaudeWCT.Numerics.Law
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem positive_part_exp (x theta t : ℝ) (ht : 0 < t) :
    max 0 (x - theta) ≤ (3 / (8 * t)) * Real.exp (-t * theta) *
      Real.exp (t * x) := by
  have hp := ClaudeWCT.Numerics.Winsor.linear_le_exp (t * (x - theta))
  have he : Real.exp (t * (x - theta)) =
      Real.exp (-t * theta) * Real.exp (t * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hp
  have hden : 8 * t ≠ 0 := ne_of_gt (by positivity)
  have hcancel : t * ((3 / (8 * t)) * Real.exp (-t * theta) * Real.exp (t * x)) =
      (3 / 8) * (Real.exp (-t * theta) * Real.exp (t * x)) := by
    field_simp
    <;> ring
  apply max_le
  · positivity
  · apply (mul_le_mul_iff_right₀ ht).mp
    rw [hcancel]
    exact hp

theorem split_excess (price capped residual theta t : ℝ)
    (ht : 0 < t) (hr : 0 ≤ residual) (hsplit : price ≤ capped + residual) :
    max 0 (price - theta) ≤ residual + (3 / (8 * t)) *
      Real.exp (-t * theta) * Real.exp (t * capped) := by
  have h := positive_part_exp capped theta t ht
  apply max_le
  · positivity
  · have hc := le_max_right 0 (capped - theta)
    linarith

/-- A single capped exponential estimate closes both endpoints of the
continuous large-query envelope and the small-query bank threshold. -/
theorem endpoint_high :
    (3 / 48 : ℝ) * Real.exp (61 / 10 - 6 * (2 - 2 / 1250 - 1 / 1024)) +
      3 / 5000 ≤ 49 / 62500 := by
  let x : ℝ := 6 * (2 - 2 / 1250 - 1 / 1024) - 61 / 10
  have hx : (0 : ℝ) ≤ x := by norm_num [x]
  have he : (340 : ℝ) ≤ Real.exp x := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx 16)
    norm_num [x, Finset.sum_range_succ, Nat.factorial]
  have hi : (Real.exp x)⁻¹ ≤ (340 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) (by norm_num)).2 he
  have hn : 61 / 10 - 6 * (2 - 2 / 1250 - 1 / 1024) = -x := by dsimp [x]; ring
  rw [hn, Real.exp_neg]
  norm_num at hi ⊢
  linarith

theorem endpoint_small :
    (3 / 48 : ℝ) * Real.exp (61 / 10 - 6 * (249 / 125 - 1 / 1024)) +
      3 / 5000 ≤ 1 / 1000 := by
  let x : ℝ := 6 * (249 / 125 - 1 / 1024) - 61 / 10
  have hx : (0 : ℝ) ≤ x := by norm_num [x]
  have he : (200 : ℝ) ≤ Real.exp x := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx 16)
    norm_num [x, Finset.sum_range_succ, Nat.factorial]
  have hi : (Real.exp x)⁻¹ ≤ (200 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) (by norm_num)).2 he
  have hn : 61 / 10 - 6 * (249 / 125 - 1 / 1024) = -x := by dsimp [x]; ring
  rw [hn, Real.exp_neg]
  norm_num at hi ⊢
  linarith

theorem endpoint_low :
    (3 / 48 : ℝ) * Real.exp (61 / 10 - 6 * (1 - 1 / 1024)) +
      3 / 5000 ≤ 49 / 100 := by
  have hx : (61 / 10 - 6 * (1 - 1 / 1024) : ℝ) ≤ 1 := by norm_num
  have he := (Real.exp_le_exp.mpr hx).trans (le_of_lt Real.exp_one_lt_d9)
  nlinarith

end ClaudeWCT.Numerics.SharedPathWinsor

namespace ClaudeWCT.Numerics.SharedPathWinsor
open ENNReal Finset ClaudeWCT.Numerics.Law

theorem cap_exp_majorant_general (c : ENNReal) (hc : c ≠ ⊤)
    (theta t : ℝ) (htheta : 0 ≤ theta) (ht : 0 < t) :
    c ≤ ENNReal.ofReal theta +
      ENNReal.ofReal ((3 / (8 * t)) * Real.exp (-t * theta)) *
        ENNReal.ofReal (Real.exp (t * c.toReal)) := by
  have h := positive_part_exp c.toReal theta t ht
  have hcR : c.toReal ≤ theta + (3 / (8 * t)) *
      Real.exp (-t * theta) * Real.exp (t * c.toReal) := by
    have hm := le_max_right 0 (c.toReal - theta)
    linarith
  calc
    c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hc).symm
    _ ≤ ENNReal.ofReal (theta + (3 / (8 * t)) *
        Real.exp (-t * theta) * Real.exp (t * c.toReal)) := ENNReal.ofReal_le_ofReal hcR
    _ = _ := by rw [ENNReal.ofReal_add htheta (by positivity), ENNReal.ofReal_mul (by positivity)]

/-- Generic bank excess bound from a capped moment and a residual first moment. -/
theorem excess_le_of_capped_exp_general {β : Type} [Fintype β]
    (v : β → ENNReal) (T : ℕ) (price capped residual : List β → ENNReal)
    (theta t bound residualBound resultBound : ℝ)
    (htheta : 0 ≤ theta) (ht : 0 < t) (hresBound : 0 ≤ residualBound)
    (hcapped : ∀ W, capped W ≠ ⊤)
    (hsplit : ∀ W, price W ≤ capped W + residual W)
    (hexp : lawAvg v T (fun W => ENNReal.ofReal (Real.exp (t * (capped W).toReal))) ≤
      ENNReal.ofReal (Real.exp bound))
    (hres : lawAvg v T residual ≤ ENNReal.ofReal residualBound)
    (hscalar : (3 / (8 * t)) * Real.exp (bound - t * theta) + residualBound ≤ resultBound) :
    lawAvg v T (fun W => price W - ENNReal.ofReal theta) ≤ ENNReal.ofReal resultBound := by
  let a : ENNReal := ENNReal.ofReal ((3 / (8 * t)) * Real.exp (-t * theta))
  have hpoint : ∀ W, price W - ENNReal.ofReal theta ≤
      a * ENNReal.ofReal (Real.exp (t * (capped W).toReal)) + residual W := by
    intro W
    apply (tsub_le_iff_right).2
    calc
      price W ≤ capped W + residual W := hsplit W
      _ ≤ (ENNReal.ofReal theta +
          a * ENNReal.ofReal (Real.exp (t * (capped W).toReal))) + residual W :=
        add_le_add (cap_exp_majorant_general (capped W) (hcapped W) theta t htheta ht) le_rfl
      _ = _ := by ac_rfl
  have he : ((3 / (8 * t)) * Real.exp (-t * theta)) * Real.exp bound =
      (3 / (8 * t)) * Real.exp (bound - t * theta) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  calc
    lawAvg v T (fun W => price W - ENNReal.ofReal theta) ≤
        lawAvg v T (fun W => a * ENNReal.ofReal (Real.exp (t * (capped W).toReal)) + residual W) :=
      lawAvg_mono v T hpoint
    _ = a * lawAvg v T (fun W => ENNReal.ofReal (Real.exp (t * (capped W).toReal))) +
        lawAvg v T residual := by rw [lawAvg_add, lawAvg_mul_left]
    _ ≤ a * ENNReal.ofReal (Real.exp bound) + ENNReal.ofReal residualBound :=
      add_le_add (mul_le_mul' le_rfl hexp) hres
    _ = ENNReal.ofReal ((3 / (8 * t)) * Real.exp (bound - t * theta) + residualBound) := by
      dsimp [a]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) hresBound, he]
    _ ≤ ENNReal.ofReal resultBound := ENNReal.ofReal_le_ofReal hscalar

end ClaudeWCT.Numerics.SharedPathWinsor

namespace ClaudeWCT.Numerics.SharedPathWinsor
open ENNReal Finset ClaudeWCT.Numerics.Law
open SigGolfCandidate.T3.BPORS.History (atIndex)

/-- A forest-specific bucket estimate can be inserted here without changing the
negative-dependence argument across independently sampled signing indices. -/
theorem law_bucket_excess_general {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] (v : β → ENNReal) (hv : ∑ b, v b = 1) (T : ℕ)
    (bucket : List β → ENNReal) (cap : ENNReal) (hcap : cap ≠ ⊤)
    (theta t bound residualBound resultBound : ℝ)
    (htheta : 0 ≤ theta) (ht : 0 < t) (hbound : 0 ≤ bound) (hresBound : 0 ≤ residualBound)
    (hmono : ∀ L b R, bucket (L ++ R) ≤ bucket (L ++ b :: R))
    (hmgf : (∑ _i : α, coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => ENNReal.ofReal (Real.exp (t * (min (bucket L) cap).toReal)) - 1)) ≤
        ENNReal.ofReal bound)
    (hres : (∑ _i : α, coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => bucket L - cap)) ≤ ENNReal.ofReal residualBound)
    (hscalar : (3 / (8 * t)) * Real.exp (bound - t * theta) + residualBound ≤ resultBound) :
    lawAvg (marked (α := α) v) T
      (fun W => (∑ i : α, bucket (atIndex i W)) - ENNReal.ofReal theta) ≤
        ENNReal.ofReal resultBound := by
  let capped : List (α × β) → ENNReal := fun W => ∑ i : α, min (bucket (atIndex i W)) cap
  let residual : List (α × β) → ENNReal := fun W => ∑ i : α, (bucket (atIndex i W) - cap)
  apply excess_le_of_capped_exp_general (marked (α := α) v) T
    (fun W => ∑ i : α, bucket (atIndex i W)) capped residual
    theta t bound residualBound resultBound htheta ht hresBound
  · intro W
    exact ENNReal.sum_ne_top.mpr fun i _ => ne_top_of_le_ne_top hcap (min_le_right _ _)
  · intro W
    change (∑ i : α, bucket (atIndex i W)) ≤
      (∑ i : α, min (bucket (atIndex i W)) cap) + ∑ i : α, (bucket (atIndex i W) - cap)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact le_of_eq (by rw [add_comm, tsub_add_min])
  · apply law_marked_exp_sum_general v hv T (fun _ L => min (bucket L) cap) t bound ht.le hbound
    · intro i L
      exact ne_top_of_le_ne_top hcap (min_le_right _ _)
    · intro i L b R
      exact min_le_min (hmono L b R) le_rfl
    · exact hmgf
  · change lawAvg (marked (α := α) v) T
      (fun W => ∑ i : α, (bucket (atIndex i W) - cap)) ≤ _
    rw [lawAvg_sum]
    apply le_trans (le_of_eq (Finset.sum_congr rfl (fun i _ =>
      law_marked_atIndex v hv i T (fun L => bucket L - cap))))
    exact hres
  · exact hscalar

end ClaudeWCT.Numerics.SharedPathWinsor

namespace ClaudeWCT.Numerics.CanonicalCompression

/-- Moment of a truncated rejection loop, given the success-weighted continuation. -/
noncomputable def retryMoment (z good bad : ℝ) : Nat → ℝ
  | 0 => 1
  | fuel + 1 => z * (good + bad * retryMoment z good bad fuel)

theorem retryMoment_le (z good bad value : ℝ) (hz : 0 ≤ z) (hbad : 0 ≤ bad)
    (hbase : 1 ≤ value) (hstep : z * (good + bad * value) ≤ value) :
    ∀ fuel, retryMoment z good bad fuel ≤ value := by
  intro fuel
  induction fuel with
  | zero => exact hbase
  | succ fuel ih =>
      exact (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hbad)) hz).trans hstep

/-- Convert a checked integer row into the real-valued rejection-loop inequality. -/
theorem transition_sound (zn zd den weighted value rejected unit : Nat)
    (hzd : 0 < zd) (hden : 0 < den) (hunit : 0 < unit)
    (hsub : zn * rejected ≤ zd * den)
    (hrow : zn * weighted ≤ value * (zd * den - zn * rejected)) :
    ((zn : ℝ) / zd) * ((weighted : ℝ) / (den * unit) +
        ((rejected : ℝ) / den) * ((value : ℝ) / unit)) ≤ (value : ℝ) / unit := by
  have hcast : (zn : ℝ) * weighted ≤ value * ((zd : ℝ) * den - (zn : ℝ) * rejected) := by
    have h := (Nat.cast_le (α := ℝ)).2 hrow
    push_cast [Nat.cast_sub hsub] at h
    exact h
  have he : ((zn : ℝ) / zd) * ((weighted : ℝ) / (den * unit) +
      ((rejected : ℝ) / den) * ((value : ℝ) / unit)) - (value : ℝ) / unit =
      ((zn : ℝ) * weighted - value * ((zd : ℝ) * den - (zn : ℝ) * rejected)) /
        ((zd : ℝ) * den * unit) := by
    have hz : (zd : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hzd
    have hd : (den : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hden
    have hu : (unit : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hunit
    field_simp
    <;> ring
  rw [← sub_nonpos, he]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcast) (by positivity)

end ClaudeWCT.Numerics.CanonicalCompression

namespace ClaudeWCT.Numerics.SharedPathWinsor.Canonical
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- A conservative scalar certificate for gate734/cap788. Its two moment
premises, at most6.87 and0.00075, still require a finite coverage proof. -/
theorem endpoint_middle :
    (3 / 48 : ℝ) * Real.exp (687 / 100 - 6 * (99847 / 50000 - 1 / 1024)) +
      3 / 4000 ≤ 23 / 20000 := by
  let x : ℝ := 6 * (99847 / 50000 - 1 / 1024) - 687 / 100
  have hx : (0 : ℝ) ≤ x := by norm_num [x]
  have he : (160 : ℝ) ≤ Real.exp x := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx 18)
    norm_num [x, Finset.sum_range_succ, Nat.factorial]
  have hi : (Real.exp x)⁻¹ ≤ (160 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) (by norm_num)).2 he
  have hn : 687 / 100 - 6 * (99847 / 50000 - 1 / 1024) = -x := by dsimp [x]; ring
  rw [hn, Real.exp_neg]
  norm_num at hi ⊢
  linarith

theorem endpoint_high :
    (3 / 48 : ℝ) * Real.exp (687 / 100 - 6 * (2 - 6 / 2500 - 1 / 1024)) +
      3 / 4000 ≤ 147 / 125000 := by
  have h := endpoint_middle
  have he := Real.exp_le_exp.mpr (show
      (687 / 100 - 6 * (2 - 6 / 2500 - 1 / 1024) : ℝ) ≤
        687 / 100 - 6 * (99847 / 50000 - 1 / 1024) by norm_num)
  linarith

theorem endpoint_low :
    (3 / 48 : ℝ) * Real.exp (687 / 100 - 6 * (1 - 1 / 1024)) +
      3 / 4000 ≤ 49 / 100 := by
  have hx : (687 / 100 - 6 * (1 - 1 / 1024) : ℝ) ≤ 1 := by norm_num
  have he := (Real.exp_le_exp.mpr hx).trans (le_of_lt Real.exp_one_lt_d9)
  nlinarith

end ClaudeWCT.Numerics.SharedPathWinsor.Canonical

namespace ClaudeWCT.Numerics.SharedPathWinsor
open Finset
set_option maxHeartbeats 1000000

/-- The exponential cost per unit of retained first moment increases up to
the cap. This avoids losing the entire width of a geometric bin. -/
theorem exp_secant (t x u : ℝ) (hx : 0 ≤ x) (hxu : x ≤ u) (hu : 0 < u) :
    Real.exp (t * x) - 1 ≤ (x / u) * (Real.exp (t * u) - 1) := by
  have hr0 : 0 ≤ x / u := div_nonneg hx hu.le
  have hr1 : x / u ≤ 1 := (div_le_one hu).2 hxu
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (t * u))
    (show 0 ≤ 1 - x / u by linarith) hr0 (show (1 - x / u) + x / u = 1 by ring)
  have he : (1 - x / u) * 0 + (x / u) * (t * u) = t * x := by
    field_simp
    <;> ring
  simp only [smul_eq_mul, Real.exp_zero, mul_one] at hc
  rw [he] at hc
  nlinarith

theorem capped_exp_ratio (t x cap pivot pay : ℝ)
    (ht : 0 ≤ t) (hx : 0 ≤ x) (hc : 0 < cap) (hp : 0 < pivot)
    (hpay : 0 ≤ pay)
    (hbelow : x ≤ cap → x ≤ pivot ∧ pivot ≤ cap)
    (habove : cap ≤ x → cap ≤ pivot ∧ pivot ≤ x)
    (hbound : Real.exp (t * min pivot cap) - 1 ≤ pivot * pay) :
    Real.exp (t * min x cap) - 1 ≤ x * pay := by
  by_cases hxc : x ≤ cap
  · rw [min_eq_left hxc]
    obtain ⟨hxp, hpc⟩ := hbelow hxc
    rw [min_eq_left hpc] at hbound
    have hs := exp_secant t x pivot hx hxp hp
    have hm := mul_le_mul_of_nonneg_left hbound (div_nonneg hx hp.le)
    have he : x / pivot * (pivot * pay) = x * pay := by field_simp
    rw [he] at hm
    exact hs.trans hm
  · have hcx : cap ≤ x := le_of_lt (lt_of_not_ge hxc)
    obtain ⟨hcp, hpx⟩ := habove hcx
    rw [min_eq_right hcx]
    rw [min_eq_right hcp] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right hpx hpay)
end ClaudeWCT.Numerics.SharedPathWinsor

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600

/-- The unmarked occupancy polynomial counts all child/rank histories. -/
theorem fullOtherPoly_model {β : Type*} [Fintype β]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (n r : ℕ) :
    fullOtherPoly H (Fintype.card β) n r =
      ∑ E : Fin r → Fin n × β, (X : ℕ[X]) ^ coordinateCoverage val E := by
  classical
  have h := sum_word_product (C := Fin n) (r := r) val H hH
    (fun _ a => (X : ℕ[X]) ^ a.val)
  symm
  calc
    (∑ E : Fin r → Fin n × β, (X : ℕ[X]) ^ coordinateCoverage val E) =
        ∑ E : Fin r → Fin n × β, ∏ c : Fin n, (X : ℕ[X]) ^ atChildCoverage val E c := by
      apply Finset.sum_congr rfl
      intro E _
      rw [Finset.prod_pow_eq_pow_sum, coordinateCoverage_sum]
    _ = fullOtherPoly H (Fintype.card β) n r := by
      simpa only [atChildCoverageFin, fullOtherPoly, lawPoly, ← Polynomial.C_eq_natCast, Nat.cast_id] using h

theorem fullOtherPoly_coeff {β : Type*} [Fintype β]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (n r c : ℕ) :
    (fullOtherPoly H (Fintype.card β) n r).coeff c =
      #{E : Fin r → Fin n × β | coordinateCoverage val E = c} := by
  classical
  rw [fullOtherPoly_model val H hH]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, Finset.card_filter,
    eq_comm]

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathReflection
open Finset

theorem profileList_get (i : Fin 434) :
    profileList i = profiles[i.val]'(by rw [profile_count]; exact i.isLt) := by
  simp only [profileList, List.getElem?_eq_getElem (by rw [profile_count]; exact i.isLt),
    Option.getD_some]

theorem profile_valid (K : Nat) (hK : K ∈ [64, 128]) (r : Fin 21) (i : Fin 434)
    (hu : used (profileList i) ≤ r.val) :
    (∑ a : Fin 21, profileVector K r.val (profileList i) a) = K ∧
    (∑ a : Fin 21, profileVector K r.val (profileList i) a * a.val) = r.val ∧
    Nat.multinomial univ (profileVector K r.val (profileList i)) *
      (r.val.factorial / ∏ a : Fin 21, a.val.factorial ^ profileVector K r.val (profileList i) a) =
        profileWeight K r.val (profileList i) := by
  have h := List.all_eq_true.mp (show profileChecks = true from profile_checks) K hK
  have h := List.all_eq_true.mp h r.val (List.mem_range.mpr r.isLt)
  have hm : profileList i ∈ profiles := by rw [profileList_get]; exact List.getElem_mem _
  have h := List.all_eq_true.mp h (profileList i) hm
  simpa only [if_pos hu, decide_eq_true_eq] using h

theorem profileVector_injective (K r : Nat) :
    Function.Injective (fun i : Fin 434 => profileVector K r (profileList i)) := by
  intro i j heq
  have hl : profileList i = profileList j := by
    apply List.ext_getElem
    · rw [profile_lengths, profile_lengths]
    · intro a ha hb
      have ha7 : a < 7 := by simpa only [profile_lengths] using ha
      have h := congrFun heq (⟨a+2, by omega⟩ : Fin 21)
      simpa only [profileVector, show ¬a+2=0 by omega, show ¬a+2=1 by omega,
        if_false, Nat.add_sub_cancel, List.getElem?_eq_getElem ha,
        List.getElem?_eq_getElem hb, Option.getD_some] using h
  rw [profileList_get, profileList_get] at hl
  exact Fin.ext (profile_nodup.getElem_inj_iff.mp hl)

end ClaudeWCT.Numerics.SharedPathReflection


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedPathReflection

theorem profile_vector_product {R : Type*} [CommMonoid R] (K r : Nat)
    (ms : List Nat) (hms : ms.length = 7) (P : Nat → R) :
    (∏ a : Fin 21, P a.val ^ profileVector K r ms a) =
      P 0 ^ (K - ((r - used ms) + groups ms)) * P 1 ^ (r - used ms) *
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
              cases ms with
              | nil => simp at hms
              | cons g ms =>
                have hn : ms = [] := List.eq_nil_of_length_eq_zero (by simpa using hms)
                subst ms
                simp [Fin.prod_univ_succ, profileVector, used, groups, List.zipIdx, mul_assoc]

noncomputable def coordinatePoly (K r : Nat) : Nat[X] :=
  ∑ i : Fin 434, if used (profileList i) ≤ r ∧
      r - used (profileList i) + groups (profileList i) ≤ K then
    Polynomial.C (profileWeight K r (profileList i)) *
      (Polynomial.C 563 * X) ^ (r - used (profileList i)) * coverageProfilePoly (profileList i)
    else 0

theorem profile_lawPoly_data (H : Nat → Nat → Nat) (ms : List Nat) (hms : ms.length = 7)
    (hP : ∀ j, 2 ≤ j → j ≤ 8 → lawPoly H 563 j = naturalDataPoly (coverageHData j)) :
    (ms.zipIdx 2).foldr (fun e s => lawPoly H 563 e.2 ^ e.1 * s) 1 =
      coverageProfilePoly ms := by
  have h2 := hP 2 (by decide) (by decide)
  have h3 := hP 3 (by decide) (by decide)
  have h4 := hP 4 (by decide) (by decide)
  have h5 := hP 5 (by decide) (by decide)
  have h6 := hP 6 (by decide) (by decide)
  have h7 := hP 7 (by decide) (by decide)
  have h8 := hP 8 (by decide) (by decide)
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
              cases ms with
              | nil => simp at hms
              | cons g ms =>
                have hn : ms = [] := List.eq_nil_of_length_eq_zero (by simpa using hms)
                subst ms
                simp [List.zipIdx, coverageProfilePoly, h2, h3, h4, h5, h6, h7, h8]

theorem coordinatePoly_below (H : Nat → Nat → Nat) (K : Nat) (hK : K ∈ [64, 128])
    (r : Fin 21) (h0 : lawPoly H 563 0 = 1)
    (h1 : lawPoly H 563 1 = Polynomial.C 563 * X)
    (hP : ∀ j, 2 ≤ j → j ≤ 8 → lawPoly H 563 j = naturalDataPoly (coverageHData j)) :
    CoeffLE (coordinatePoly K r.val) (fullOtherPoly H 563 K r.val) := by
  classical
  let v : Fin 434 → Fin 21 → Nat := fun i => profileVector K r.val (profileList i)
  let F : (Fin 21 → Nat) → Nat[X] := fun m =>
    if (∑ a, m a * a.val) = r.val then
      (Nat.multinomial univ m : Nat[X]) *
        (r.val.factorial / ∏ a : Fin 21, a.val.factorial ^ m a : Nat) *
          ∏ a : Fin 21, lawPoly H 563 a.val ^ m a else 0
  let s : Finset (Fin 434) := univ.filter (fun i => used (profileList i) ≤ r.val ∧
    r.val - used (profileList i) + groups (profileList i) ≤ K)
  have hf : fullOtherPoly H 563 K r.val = ∑ m ∈ piAntidiag univ K, F m :=
    occupancy_profile_sum_bounded K r.val 20 (by omega) (lawPoly H 563)
  have he : coordinatePoly K r.val = ∑ i ∈ s, F (v i) := by
    rw [coordinatePoly, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hu : used (profileList i) ≤ r.val ∧
        r.val - used (profileList i) + groups (profileList i) ≤ K
    · rw [if_pos hu, if_pos hu]
      dsimp [F, v]
      have hcheck := profile_valid K hK r i hu.1
      rw [if_pos hcheck.2.1, ← Nat.cast_mul, hcheck.2.2,
        profile_vector_product K r.val _ (profile_lengths i), h0, h1,
        one_pow, one_mul, profile_lawPoly_data H _ (profile_lengths i) hP]
      simp only [← Polynomial.C_eq_natCast, Nat.cast_id, mul_assoc]
    · simp only [if_neg hu]
  have hmem : ∀ i ∈ s, v i ∈ piAntidiag univ K := by
    intro i hi
    exact Finset.mem_piAntidiag.mpr
      ⟨(profile_valid K hK r i (Finset.mem_filter.mp hi).2.1).1,
        fun _ _ => Finset.mem_univ _⟩
  rw [he, hf]
  exact coeffSum_injective s (piAntidiag univ K) v
    (profileVector_injective K r.val) hmem F

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.Winsor

/-- Reuse the existing Taylor certificate at a rationally rounded argument. -/
theorem rational_exp_upper (S x u bound : Nat)
    (hS : 0 < S) (hxu : x ≤ 8 * u) (hu : u ≤ S)
    (hround : S * taylorNumN S u ^ 8 ≤ bound * taylorDenN S ^ 8) :
    Real.exp ((x : ℝ) / S) ≤ (bound : ℝ) / S := by
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hd : (0 : ℝ) < taylorDenN S := by
    unfold taylorDenN
    norm_num [ClaudeWCT.Numerics.Kernel.fact]
    positivity
  have hx : (x : ℝ) / S ≤ 8 * ((u : ℝ) / S) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hxu) hs.le
  have hur : (u : ℝ) / S ≤ 1 := (div_le_one hs).mpr (by exact_mod_cast hu)
  have he := exp8_le_taylor16 ((u : ℝ) / S) (by positivity) hur
  have ht : taylor16 ((u : ℝ) / S) ^ 8 ≤ (bound : ℝ) / S := by
    rw [← taylorNumN_ratio S u hs.ne', div_pow]
    apply (div_le_div_iff₀ (pow_pos hd 8) hs).mpr
    have hc : (S : ℝ) * (taylorNumN S u : ℝ) ^ 8 ≤
        (bound : ℝ) * (taylorDenN S : ℝ) ^ 8 := by exact_mod_cast hround
    nlinarith
  exact (Real.exp_le_exp.mpr hx).trans (he.trans ht)

end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedPathReflection
/-- Retained unmarked profiles are a subdistribution of true coverage counts. -/
theorem coordinatePoly_coeff_below {β : Type*} [Fintype β]
    (val : β → Fin 6 → Nat) (H : Nat → Nat → Nat)
    (hH : FullCoverageHistogram val H) (hβ : Fintype.card β = 563)
    (K : Nat) (hK : K ∈ [64, 128]) (r : Fin 21)
    (h0 : lawPoly H 563 0 = 1) (h1 : lawPoly H 563 1 = Polynomial.C 563 * X)
    (hP : ∀ j, 2 ≤ j → j ≤ 8 → lawPoly H 563 j = naturalDataPoly (coverageHData j))
    (c : Nat) :
    (coordinatePoly K r.val).coeff c ≤
      #{E : Fin r.val → Fin K × β | coordinateCoverage val E = c} := by
  have h := coordinatePoly_below H K hK r h0 h1 hP c
  rw [← hβ, fullOtherPoly_coeff val H hH] at h
  exact h

end ClaudeWCT.Numerics.SharedCoverage



namespace ClaudeWCT.Numerics.SharedPathReflection

theorem bin_pair_bounds_of_check (hcheck : binRunsCheck = true)
    (c b : Nat) (h : (c, b) ∈ binPairs) :
    1 ≤ c ∧ c * 100 ^ b ≤ 101 ^ b ∧ 100 * 101 ^ b ≤ 101 * c * 100 ^ b := by
  obtain ⟨e, he, hmem⟩ := List.mem_flatMap.mp h
  obtain ⟨a, ha, hpair⟩ := List.mem_map.mp hmem
  have hac : a = c := congrArg Prod.fst hpair
  have heb : e.2.2 = b := congrArg Prod.snd hpair
  subst a
  have hr := List.all_eq_true.mp hcheck e he
  simp only [decide_eq_true_eq] at hr
  have hc := List.mem_range'.mp ha
  rcases hc with ⟨i, hi, hc⟩
  simp only [Nat.one_mul] at hc
  rcases hr with ⟨hlo, hle, hupper, hlower⟩
  have hlow : e.1 ≤ c := by omega
  have hhigh : c ≤ e.2.1 := by omega
  rw [← heb]
  exact ⟨hlo.trans hlow, (Nat.mul_le_mul_right _ hhigh).trans hupper,
    hlower.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hlow))⟩

theorem bin_lookup_pair (hidx : binPairs.map Prod.fst = List.range' 1 11260)
    (c : Nat) (hc : 1 ≤ c) (hC : c ≤ 11260) :
    (c, bins[c]?.getD 0) ∈ binPairs := by
  have hlen : binPairs.length = 11260 := by
    have h := congrArg List.length hidx
    simpa only [List.length_map, List.length_range'] using h
  have hi : c - 1 < binPairs.length := by omega
  have hp : (binPairs[c - 1]).1 = c := by
    have h := congrArg (fun xs : List Nat => xs[c-1]?.getD 0) hidx
    rw [List.getElem?_eq_getElem (show c-1 < (binPairs.map Prod.fst).length by
      simpa only [List.length_map] using hi),
      List.getElem?_eq_getElem (show c-1 < (List.range' 1 11260).length by
        simp only [List.length_range']; omega)] at h
    simp only [List.getElem_map, List.getElem_range', Option.getD_some, Nat.one_mul] at h
    omega
  have hb : bins[c]?.getD 0 = (binPairs[c-1]).2 := by
    simp only [bins, List.getElem?_toArray]
    have he : c = (c-1)+1 := by omega
    conv_lhs => rw [he, List.getElem?_cons_succ]
    rw [List.getElem?_eq_getElem (show c-1 < (binPairs.map Prod.snd).length by
      simpa only [List.length_map] using hi)]
    simp only [List.getElem_map, Option.getD_some]
  have hm : ((binPairs[c-1]).1, (binPairs[c-1]).2) ∈ binPairs := List.getElem_mem hi
  simpa only [hp, ← hb] using hm

theorem bin_lookup_bounds (hcheck : binRunsCheck = true)
    (hidx : binPairs.map Prod.fst = List.range' 1 11260)
    (c : Nat) (hc : 1 ≤ c) (hC : c ≤ 11260) :
    c * 100 ^ (bins[c]?.getD 0) ≤ 101 ^ (bins[c]?.getD 0) ∧
    100 * 101 ^ (bins[c]?.getD 0) ≤ 101 * c * 100 ^ (bins[c]?.getD 0) :=
  (bin_pair_bounds_of_check hcheck c _ (bin_lookup_pair hidx c hc hC)).2

theorem geometric_bin_interval (c b : Nat)
    (hupper : c * 100 ^ b ≤ 101 ^ b)
    (hlower : 100 * 101 ^ b ≤ 101 * c * 100 ^ b) :
    (101 / 100 : ℝ) ^ b * (100 / 101) ≤ (c : ℝ) ∧
      (c : ℝ) ≤ (101 / 100 : ℝ) ^ b := by
  have hp : (0 : ℝ) < 100 ^ b := by positivity
  have hu : (c : ℝ) * 100 ^ b ≤ 101 ^ b := by exact_mod_cast hupper
  have hl : (100 : ℝ) * 101 ^ b ≤ 101 * c * 100 ^ b := by exact_mod_cast hlower
  constructor
  · rw [div_pow, div_mul_div_comm]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 100 ^ b * 101)).mpr
    nlinarith
  · rw [div_pow]
    exact (le_div_iff₀ hp).mpr hu

end ClaudeWCT.Numerics.SharedPathReflection



namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedPathReflection

theorem foldl_weighted_sum {α : Type*} (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun s e => s + f e) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

theorem foldl_weighted_prod {α : Type*} (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun s e => s * f e) a = a * (xs.map f).prod := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_assoc]

theorem foldr_weighted_prod {α : Type*} (xs : List α) (f : α → Nat) :
    xs.foldr (fun e s => f e * s) 1 = (xs.map f).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem profilePacked_eq (bits : Nat) (ms : List Nat) :
    profilePacked bits ms = (coverageProfilePoly ms).eval (2 ^ bits) := by
  rw [coverageProfilePoly_eval]
  simp only [profilePacked, coverageProfilePack, foldl_weighted_prod,
    foldr_weighted_prod, one_mul, coverageHPackBits_eq]

theorem sum_profiles (f : List Nat → Nat) :
    (profiles.map f).sum = ∑ i : Fin 434, f (profileList i) := by
  have h : ∀ (xs : List (List Nat)) (n : Nat) (hn : xs.length = n),
      (xs.map f).sum = ∑ i : Fin n, f (xs[i.val]'(by omega)) := by
    intro xs n hn
    subst hn
    rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]
  rw [h profiles 434 profile_count]
  apply Finset.sum_congr rfl
  intro i _
  rw [profileList_get]

theorem coordinatePacked_eval (bits K r : Nat) :
    coordinatePacked bits K r = (coordinatePoly K r).eval (2 ^ bits) := by
  let f : List Nat → Nat := fun ms =>
    if used ms ≤ r ∧ r - used ms + groups ms ≤ K then
      profileWeight K r ms * 563 ^ (r - used ms) *
        (profilePacked bits ms <<< (bits * (r - used ms))) else 0
  have he : coordinatePacked bits K r = (profiles.map f).sum := by
    have hf : (fun acc ms => if used ms ≤ r ∧ r - used ms + groups ms ≤ K then
        acc + profileWeight K r ms * 563 ^ (r - used ms) *
          (profilePacked bits ms <<< (bits * (r - used ms))) else acc) =
        (fun acc ms => acc + f ms) := by
      funext acc ms
      dsimp [f]
      split_ifs <;> simp
    rw [coordinatePacked, hf, foldl_weighted_sum, Nat.zero_add]
  rw [he, sum_profiles, coordinatePoly, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [f]
  split_ifs with h
  · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Nat.shiftLeft_eq, pow_mul, profilePacked_eq]
    ring
  · simp

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathReflection
open Finset Polynomial

def bucketArray {α : Type*} (xs : List α) (bin weight : α → Nat) (a : Array Nat) : Array Nat :=
  xs.foldl (fun acc x => acc.set! (bin x) (acc[bin x]! + weight x)) a

theorem bucketArray_model {α : Type*} (xs : List α) (bin weight : α → Nat)
    (a : Array Nat) (N : Nat) (ha : a.size = N)
    (hbin : ∀ x ∈ xs, bin x < N) :
    (bucketArray xs bin weight a).size = N ∧
      ∀ i, (bucketArray xs bin weight a)[i]! = a[i]! +
        (xs.map (fun x => if bin x = i then weight x else 0)).sum := by
  induction xs generalizing a with
  | nil => simp [bucketArray, ha]
  | cons x xs ih =>
    let a' := a.set! (bin x) (a[bin x]! + weight x)
    have ha' : a'.size = N := by simp only [a', Array.size_set!, ha]
    have hx : bin x < a.size := by rw [ha]; exact hbin x (by simp)
    have hr := ih a' ha' (fun y hy => hbin y (by simp [hy]))
    refine ⟨hr.1, fun i => ?_⟩
    have hi : a'[i]! = a[i]! + (if bin x = i then weight x else 0) := by
      by_cases h : bin x = i
      · subst i
        calc a'[bin x]! = a[bin x]! + weight x := Array.getElem!_set!_self _ _ _ hx
             _ = _ := by simp
      · simp only [a', Array.getElem!_set!_ne a (bin x) i _ h, if_neg h, Nat.add_zero]
    change (bucketArray xs bin weight a')[i]! = _
    rw [hr.2 i, hi]
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem bucketArray_zero_model {α : Type*} (xs : List α) (bin weight : α → Nat)
    (N : Nat) (hbin : ∀ x ∈ xs, bin x < N) :
    (bucketArray xs bin weight (Array.replicate N 0)).size = N ∧
      ∀ i, (bucketArray xs bin weight (Array.replicate N 0))[i]! =
        (xs.map (fun x => if bin x = i then weight x else 0)).sum := by
  have h := bucketArray_model xs bin weight (Array.replicate N 0) N (by simp) hbin
  refine ⟨h.1, fun i => ?_⟩
  rw [h.2 i]
  have hz : (Array.replicate N (0 : Nat))[i]! = 0 := by
    by_cases hi : i < N <;> simp [getElem!_def, Array.getElem?_replicate, hi]
  simp only [hz, Nat.zero_add]

theorem coupled_bucket_fst {α : Type*} (xs : List α) (bin w₀ w₁ : α → Nat)
    (a : Binned) :
    (xs.foldl (fun acc x =>
      { probability := acc.probability.set! (bin x) (acc.probability[bin x]! + w₀ x)
        first := acc.first.set! (bin x) (acc.first[bin x]! + w₁ x) } :
        Binned → α → Binned) a).probability = bucketArray xs bin w₀ a.probability := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons, bucketArray] using ih _

theorem coupled_bucket_snd {α : Type*} (xs : List α) (bin w₀ w₁ : α → Nat)
    (a : Binned) :
    (xs.foldl (fun acc x =>
      { probability := acc.probability.set! (bin x) (acc.probability[bin x]! + w₀ x)
        first := acc.first.set! (bin x) (acc.first[bin x]! + w₁ x) } :
        Binned → α → Binned) a).first = bucketArray xs bin w₁ a.first := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons, bucketArray] using ih _

end ClaudeWCT.Numerics.SharedPathReflection


namespace ClaudeWCT.Numerics.SharedPathReflection
open Finset Polynomial
open ClaudeWCT.Numerics.N600

noncomputable def listPolynomial : List Nat → Nat[X]
  | [] => 0
  | a :: xs => Polynomial.C a + X * listPolynomial xs

theorem listPolynomial_coeff (xs : List Nat) (i : Nat) :
    (listPolynomial xs).coeff i = xs[i]?.getD 0 := by
  induction xs generalizing i with
  | nil => simp [listPolynomial]
  | cons a xs ih =>
    cases i with
    | zero => simp [listPolynomial]
    | succ i => simp [listPolynomial, ih]

theorem listPolynomial_eval (xs : List Nat) (bits : Nat) :
    (listPolynomial xs).eval (2^bits) =
      xs.foldr (fun a s => a + (s <<< bits)) 0 := by
  induction xs with
  | nil => simp [listPolynomial]
  | cons a xs ih => simp [listPolynomial, ih, Nat.shiftLeft_eq, Nat.mul_comm]

theorem pack_eq_eval (a : Array Nat) (bits : Nat) :
    pack bits a = (listPolynomial a.toList).eval (2^bits) :=
  (listPolynomial_eval a.toList bits).symm

theorem coefficient_eval (P : Nat[X]) (bits : Nat)
    (hcoeff : ∀ i, P.coeff i < 2^bits) (i : Nat) :
    coefficient bits (P.eval (2^bits)) i = P.coeff i := by
  unfold coefficient
  rw [Nat.shiftRight_eq_div_pow, pow_mul]
  exact ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) i P hcoeff

theorem unpack_get (bits length p : Nat) (i : Fin length) :
    (unpack bits length p)[i.val]?.getD 0 = coefficient bits p i.val := by
  simp [unpack, Array.getElem?_eq_getElem, i.isLt]

theorem multiply_get (bits : Nat) (a b : Array Nat)
    (hcoeff : ∀ i, (listPolynomial a.toList * listPolynomial b.toList).coeff i < 2^bits)
    (i : Fin (a.size + b.size - 1)) :
    (multiply bits a b)[i.val]?.getD 0 =
      (listPolynomial a.toList * listPolynomial b.toList).coeff i.val := by
  rw [multiply, unpack_get, pack_eq_eval, pack_eq_eval, ← Polynomial.eval_mul]
  exact coefficient_eval _ bits hcoeff i.val

theorem coefficientLE_eval_one {P Q : Nat[X]} (h : CoeffLE P Q) :
    P.eval 1 ≤ Q.eval 1 := by
  calc P.eval 1 = ∑ i ∈ P.support, P.coeff i := by
         simp [Polynomial.eval_eq_sum, Polynomial.sum_def]
       _ ≤ ∑ i ∈ P.support, Q.coeff i := Finset.sum_le_sum (fun i _ => h i)
       _ ≤ Q.eval 1 := sum_coeff_le_eval_one Q P.support

end ClaudeWCT.Numerics.SharedPathReflection


namespace ClaudeWCT.Numerics.SharedPathReflection

theorem geometric_add_interval (d b : Nat)
    (hu : 100 ^ b * (101 ^ d + 100 ^ d) ≤ 101 ^ (b+d))
    (hl : 100 * 101 ^ (b+d) ≤ 101 * 100 ^ b * (101 ^ d + 100 ^ d)) :
    (101 / 100 : ℝ) ^ (b+d) * (100/101) ≤ (101/100 : ℝ)^d + 1 ∧
      (101/100 : ℝ)^d + 1 ≤ (101/100 : ℝ)^(b+d) := by
  have hu' : (100 : ℝ)^b * (101^d + 100^d) ≤ 101^(b+d) := by exact_mod_cast hu
  have hl' : (100 : ℝ)*101^(b+d) ≤ 101*100^b*(101^d+100^d) := by exact_mod_cast hl
  have hB : (0 : ℝ) < 100^b := by positivity
  have hD : (0 : ℝ) < 100^d := by positivity
  have he : ((101/100 : ℝ)^d + 1) = (101^d+100^d)/100^d := by
    rw [div_pow, add_div, div_self hD.ne']
  rw [he, div_pow, pow_add (100 : ℝ) b d]
  constructor
  · rw [div_mul_div_comm]
    apply (div_le_div_iff₀ (by positivity) hD).mpr
    nlinarith
  · apply (div_le_div_iff₀ hD (by positivity)).mpr
    nlinarith

theorem geometric_add_shift (i j b : Nat) (hji : j ≤ i)
    (h : (101/100 : ℝ)^((i-j)+b)*(100/101) ≤ (101/100 : ℝ)^(i-j)+1 ∧
      (101/100 : ℝ)^(i-j)+1 ≤ (101/100 : ℝ)^((i-j)+b)) :
    (101/100 : ℝ)^(i+b)*(100/101) ≤ (101/100 : ℝ)^i+(101/100 : ℝ)^j ∧
      (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^(i+b) := by
  have hp : (0 : ℝ) ≤ (101/100 : ℝ)^j := by positivity
  have he : j + (i-j) = i := by omega
  have he' : j + ((i-j)+b) = i+b := by omega
  have h₀ := mul_le_mul_of_nonneg_left h.1 hp
  have h₁ := mul_le_mul_of_nonneg_left h.2 hp
  simpa only [mul_add, mul_one, ← mul_assoc, ← pow_add, he, he'] using And.intro h₀ h₁

theorem product_intervals (a c : ℝ) (i j k l : Nat)
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hA : (101/100 : ℝ)^i*(100/101)^k ≤ a ∧ a ≤ (101/100 : ℝ)^i)
    (hC : (101/100 : ℝ)^j*(100/101)^l ≤ c ∧ c ≤ (101/100 : ℝ)^j) :
    (101/100 : ℝ)^(i+j)*(100/101)^(k+l) ≤ a*c ∧
      a*c ≤ (101/100 : ℝ)^(i+j) := by
  constructor
  · have h := mul_le_mul hA.1 hC.1 (by positivity) ha
    calc (101/100 : ℝ)^(i+j)*(100/101)^(k+l) =
        ((101/100 : ℝ)^i*(100/101)^k) * ((101/100 : ℝ)^j*(100/101)^l) := by
          rw [pow_add, pow_add]; ring
         _ ≤ a*c := h
  · rw [pow_add]
    exact mul_le_mul hA.2 hC.2 hc (by positivity)

theorem sum_intervals (a c : ℝ) (i j k out : Nat)
    (hA : (101/100 : ℝ)^i*(100/101)^k ≤ a ∧ a ≤ (101/100 : ℝ)^i)
    (hC : (101/100 : ℝ)^j*(100/101)^k ≤ c ∧ c ≤ (101/100 : ℝ)^j)
    (hOut : (101/100 : ℝ)^out*(100/101) ≤ (101/100 : ℝ)^i+(101/100 : ℝ)^j ∧
      (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^out) :
    (101/100 : ℝ)^out*(100/101)^(k+1) ≤ a+c ∧
      a+c ≤ (101/100 : ℝ)^out := by
  constructor
  · have h := mul_le_mul_of_nonneg_right hOut.1 (show 0 ≤ (100/101 : ℝ)^k by positivity)
    rw [add_mul] at h
    have he : (101/100 : ℝ)^out*(100/101)^(k+1) =
        ((101/100 : ℝ)^out*(100/101))*(100/101)^k := by rw [pow_succ]; ring
    rw [he]
    exact h.trans (add_le_add hA.1 hC.1)
  · exact (add_le_add hA.2 hC.2).trans hOut.2

end ClaudeWCT.Numerics.SharedPathReflection


namespace ClaudeWCT.Numerics.SharedPathReflection
open Finset Polynomial

theorem coordinateBinned_probability (K r : Nat) :
    (coordinateBinned K r).probability =
      bucketArray (List.range (563*r+1)) (fun c => bins[c]?.getD 0)
        (fun c => coefficient 512 (coordinatePacked 512 K r) c) (Array.replicate 1024 0) := by
  unfold coordinateBinned
  exact coupled_bucket_fst _ _ _ _ _

theorem coordinateBinned_first (K r : Nat) :
    (coordinateBinned K r).first =
      bucketArray (List.range (563*r+1)) (fun c => bins[c]?.getD 0)
        (fun c => c * coefficient 512 (coordinatePacked 512 K r) c) (Array.replicate 1024 0) := by
  unfold coordinateBinned
  exact coupled_bucket_snd _ _ _ _ _

theorem coordinateBinned_model (K r : Nat)
    (hbin : ∀ c < 563*r+1, bins[c]?.getD 0 < 1024)
    (P : Nat[X]) (hPacked : coordinatePacked 512 K r = P.eval (2^512))
    (hCoeff : ∀ c, P.coeff c < 2^512) :
    (coordinateBinned K r).probability.size = 1024 ∧
    (coordinateBinned K r).first.size = 1024 ∧
    (∀ b, (coordinateBinned K r).probability[b]! =
      ((List.range (563*r+1)).map (fun c => if bins[c]?.getD 0 = b then P.coeff c else 0)).sum) ∧
    (∀ b, (coordinateBinned K r).first[b]! =
      ((List.range (563*r+1)).map (fun c => if bins[c]?.getD 0 = b then c * P.coeff c else 0)).sum) := by
  have hp := bucketArray_zero_model (List.range (563*r+1)) (fun c => bins[c]?.getD 0)
    (fun c => coefficient 512 (coordinatePacked 512 K r) c) 1024
    (fun c hc => hbin c (List.mem_range.mp hc))
  have hf := bucketArray_zero_model (List.range (563*r+1)) (fun c => bins[c]?.getD 0)
    (fun c => c * coefficient 512 (coordinatePacked 512 K r) c) 1024
    (fun c hc => hbin c (List.mem_range.mp hc))
  rw [coordinateBinned_probability, coordinateBinned_first]
  refine ⟨hp.1, hf.1, ?_, ?_⟩
  · intro b
    simpa only [hPacked, coefficient_eval P 512 hCoeff] using hp.2 b
  · intro b
    simpa only [hPacked, coefficient_eval P 512 hCoeff] using hf.2 b

end ClaudeWCT.Numerics.SharedPathReflection


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.Thinning
open ClaudeWCT.Numerics.Kernel (wpos wneg)

theorem signed_count_to_nat (count K base r : Nat) (d : List (Nat × Int))
    (hK : 0 < K) (he : (count : Int) = K * tmom d base r) :
    count = K * (wpos d base r - wneg d base r) := by
  have hK' : (0 : Int) < K := by exact_mod_cast hK
  have hnonneg : 0 ≤ tmom d base r := by
    have hn := Int.natCast_nonneg count
    nlinarith
  have hw := wpos_sub_wneg d base r
  have hle : wneg d base r ≤ wpos d base r := by omega
  have he' : (count : Int) = (K * (wpos d base r - wneg d base r) : Nat) := by
    rw [Nat.cast_mul, Nat.cast_sub hle, hw]
    exact he
  exact_mod_cast he'

theorem coordinate_first_count {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (K r : Nat) (hK : 0 < K) :
    #{y : (Fin K × β) × (Fin r → Fin K × β) |
      CovAt val y.1.1 (val y.1.2) y.2} = coordinateFormula K r := by
  have h := coord_first (C := Fin K) val w1Data
    (fun p => (hW p).trans (tmom_zero w1Data p).symm) r
  rw [Fintype.card_fin, hβ] at h
  exact signed_count_to_nat _ K ((K-1)*563) r w1Data hK h

theorem coordinate_first_sum {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (K r : Nat) (hK : 0 < K) :
    ∑ E : Fin r → Fin K × β, coordinateCoverage val E = coordinateFormula K r := by
  classical
  have h := coordinate_first_count val hβ hW K r hK
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm] at h
  simpa only [coordinateCoverage, Finset.card_filter] using h

theorem coordinate_near_count {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (i : Fin 6) (hW : WFTable val i) (K r : Nat) (hK : 0 < K) :
    #{y : (Fin K × β) × (Fin r → Fin K × β) |
      CovAtExcept val i y.1.1 (val y.1.2) y.2} =
      K * (wpos (wfData i) ((K-1)*563) r - wneg (wfData i) ((K-1)*563) r) := by
  have h := coord_near (C := Fin K) val i (wfData i)
    (fun p => (hW p).trans (tmom_zero (wfData i) p).symm) r
  rw [Fintype.card_fin, hβ] at h
  exact signed_count_to_nat _ K ((K-1)*563) r (wfData i) hK h

theorem coordinate_near_sum {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : ∀ i, WFTable val i) (K r : Nat) (hK : 0 < K) :
    (∑ i : Fin 6, #{y : (Fin K × β) × (Fin r → Fin K × β) |
      CovAtExcept val i y.1.1 (val y.1.2) y.2}) = coordinateNearFormula K r := by
  simp_rw [coordinate_near_count val hβ _ (hW _) K r hK]
  simp [coordinateNearFormula, Fin.sum_univ_succ, List.range_succ,
    List.foldr_append, mul_add, add_assoc]

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600

theorem coordinate_coefficient_lt {β : Type*} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (K r : Nat) (hK : K ≤ 128) (hr : r ≤ 20) (P : Nat[X])
    (hP : ∀ c, P.coeff c ≤
      #{E : Fin r → Fin K × β | coordinateCoverage val E = c}) :
    ∀ c, P.coeff c < 2^512 := by
  intro c
  have hc : #{E : Fin r → Fin K × β | coordinateCoverage val E = c} ≤
      Fintype.card (Fin r → Fin K × β) :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, hβ] at hc
  calc P.coeff c ≤ (K*563)^r := (hP c).trans hc
       _ ≤ (128*563)^r := Nat.pow_le_pow_left (Nat.mul_le_mul_right 563 hK) r
       _ ≤ (128*563)^20 := Nat.pow_le_pow_right (by decide) hr
       _ < 2^512 := by decide +kernel

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset

theorem sum_selector_occupancy {M : Type*} [AddCommMonoid M]
    (r : Nat) (F : Nat → Nat → M) :
    (∑ o : Fin r → Fin 2, F (occ o 0) (occ o 1)) =
      ∑ t ∈ Finset.range (r+1), r.choose t • F t (r-t) := by
  rw [sum_occ (fun k => F (k 0) (k 1))]
  symm
  refine Finset.sum_bij (fun t _ => ![t, r-t]) ?_ ?_ ?_ ?_
  · intro t ht
    apply Finset.mem_piAntidiag.mpr
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    have ht' := Finset.mem_range.mp ht
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    omega
  · intro t ht u hu he
    simpa using congrArg (fun k : Fin 2 → Nat => k 0) he
  · intro k hk
    have hs := (Finset.mem_piAntidiag.mp hk).1
    simp only [Fin.sum_univ_two] at hs
    refine ⟨k 0, Finset.mem_range.mpr (by omega), ?_⟩
    funext i
    fin_cases i <;> simp <;> omega
  · intro t ht
    have ht' : t ≤ r := by have h := Finset.mem_range.mp ht; omega
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [Nat.multinomial_univ_two, show t+(r-t)=r by omega,
      ← Nat.choose_eq_factorial_div_factorial ht']

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600

theorem sum_split_selector {α M : Type*} [Fintype α] [AddCommMonoid M]
    {r : Nat} (o : Fin r → Fin 2)
    (f : (Fin (occ o 0) → α) → (Fin (occ o 1) → α) → M) :
    (∑ A : Fin r → α, f (splitRanks o A 0) (splitRanks o A 1)) =
      ∑ A₀ : Fin (occ o 0) → α, ∑ A₁ : Fin (occ o 1) → α, f A₀ A₁ := by
  let e := (splitRanks (β := α) o).trans
    (piFinTwoEquiv (fun s => Fin (occ o s) → α))
  have h := e.sum_comp (fun p => f p.1 p.2)
  rw [Fintype.sum_prod_type] at h
  exact h

noncomputable def selectorValue {α : Type*} [Fintype α]
    (coverage : (n : Nat) → (Fin n → α) → Nat) {r : Nat}
    (o : Fin r → Fin 2) (A B : Fin r → α) (s : Fin 2) : Nat :=
  coverage (occ o s) (splitRanks o A s) * coverage (occ o s) (splitRanks o B s)

theorem sum_pair_selector {α M : Type*} [Fintype α] [AddCommMonoid M]
    (coverage : (n : Nat) → (Fin n → α) → Nat) (r : Nat) (F : Nat → Nat → M) :
    (∑ o : Fin r → Fin 2, ∑ A : Fin r → α, ∑ B : Fin r → α,
      F (selectorValue coverage o A B 0) (selectorValue coverage o A B 1)) =
      ∑ t ∈ range (r+1), r.choose t •
        (∑ A₀ : Fin t → α, ∑ A₁ : Fin (r-t) → α,
          ∑ B₀ : Fin t → α, ∑ B₁ : Fin (r-t) → α,
            F (coverage t A₀ * coverage t B₀) (coverage (r-t) A₁ * coverage (r-t) B₁)) := by
  have hs (o : Fin r → Fin 2) :
      (∑ A : Fin r → α, ∑ B : Fin r → α,
        F (selectorValue coverage o A B 0) (selectorValue coverage o A B 1)) =
        ∑ A₀ : Fin (occ o 0) → α, ∑ A₁ : Fin (occ o 1) → α,
          ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
            F (coverage _ A₀ * coverage _ B₀) (coverage _ A₁ * coverage _ B₁) := by
    unfold selectorValue
    trans ∑ A : Fin r → α, ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
      F (coverage _ (splitRanks o A 0) * coverage _ B₀)
        (coverage _ (splitRanks o A 1) * coverage _ B₁)
    · apply Finset.sum_congr rfl
      intro A _
      exact sum_split_selector o (fun B₀ B₁ =>
        F (coverage _ (splitRanks o A 0) * coverage _ B₀)
          (coverage _ (splitRanks o A 1) * coverage _ B₁))
    · exact sum_split_selector o (fun A₀ A₁ =>
        ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
          F (coverage _ A₀ * coverage _ B₀) (coverage _ A₁ * coverage _ B₁))
  simp_rw [hs]
  exact sum_selector_occupancy r (fun t u =>
    ∑ A₀ : Fin t → α, ∑ A₁ : Fin u → α, ∑ B₀ : Fin t → α, ∑ B₁ : Fin u → α,
      F (coverage t A₀ * coverage t B₀) (coverage u A₁ * coverage u B₁))

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600

theorem independent_pair_sum {α β : Type*} [Fintype α] [Fintype β]
    (f : α → Nat) (g : β → Nat) :
    (∑ a : α, ∑ b : β, ∑ c : α, ∑ d : β, (f a * f c + g b * g d)) =
      (∑ a, f a)^2 * (Fintype.card β)^2 + (Fintype.card α)^2 * (∑ b, g b)^2 := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum, Nat.cast_id]
  ring

theorem binomial_reverse_sum (r : Nat) (f : Nat → Nat) :
    (∑ t ∈ range (r+1), r.choose t * f (r-t)) =
      ∑ t ∈ range (r+1), r.choose t * f t := by
  have h := Finset.sum_range_reflect (fun t => r.choose t * f t) (r+1)
  simp only [Nat.add_sub_cancel] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ r := by have h := Finset.mem_range.mp ht; omega
  rw [Nat.choose_symm ht']

theorem pair_first_moment {α : Type*} [Fintype α]
    (coverage : (n : Nat) → (Fin n → α) → Nat) (r : Nat) :
    (∑ o : Fin r → Fin 2, ∑ A : Fin r → α, ∑ B : Fin r → α,
      (selectorValue coverage o A B 0 + selectorValue coverage o A B 1)) =
      2 * ∑ t ∈ range (r+1), r.choose t *
        (∑ A : Fin t → α, coverage t A)^2 * (Fintype.card α)^(2*(r-t)) := by
  rw [sum_pair_selector coverage r (fun x y => x+y)]
  have hi (t : Nat) := independent_pair_sum (coverage t) (coverage (r-t))
  simp_rw [hi]
  simp only [Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
    mul_add, Finset.sum_add_distrib]
  let m := fun t => (∑ A : Fin t → α, coverage t A)
  have hp (t : Nat) : (Fintype.card α ^ t)^2 = Fintype.card α^(2*t) := by
    rw [← pow_mul, Nat.mul_comm t 2]
  simp only [hp]
  have hs : (∑ t ∈ range (r+1), r.choose t * (Fintype.card α^(2*t) * m (r-t)^2)) =
      ∑ t ∈ range (r+1), r.choose t * m t^2 * Fintype.card α^(2*(r-t)) := by
    have he := binomial_reverse_sum r (fun t => m t^2 * Fintype.card α^(2*(r-t)))
    have hl : (∑ t ∈ range (r+1), r.choose t *
        (m (r-t)^2 * Fintype.card α^(2*(r-(r-t))))) =
        ∑ t ∈ range (r+1), r.choose t * (Fintype.card α^(2*t) * m (r-t)^2) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' : t ≤ r := by have h := Finset.mem_range.mp ht; omega
      rw [Nat.sub_sub_self ht']
      ring
    rw [hl] at he
    simpa only [mul_assoc] using he
  change (∑ t ∈ range (r+1), r.choose t * (m t^2 * Fintype.card α^(2*(r-t)))) +
    (∑ t ∈ range (r+1), r.choose t * (Fintype.card α^(2*t) * m (r-t)^2)) = _
  rw [hs]
  dsimp only [m]
  simp only [mul_assoc]
  omega

end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600

noncomputable def selectorKernel {α : Type*} [Fintype α]
    (kernel : (n : Nat) → (Fin n → α) → (Fin n → α) → Nat) {r : Nat}
    (o : Fin r → Fin 2) (A B : Fin r → α) (s : Fin 2) : Nat :=
  kernel (occ o s) (splitRanks o A s) (splitRanks o B s)

theorem sum_pair_kernel {α M : Type*} [Fintype α] [AddCommMonoid M]
    (kernel : (n : Nat) → (Fin n → α) → (Fin n → α) → Nat)
    (r : Nat) (F : Nat → Nat → M) :
    (∑ o : Fin r → Fin 2, ∑ A : Fin r → α, ∑ B : Fin r → α,
      F (selectorKernel kernel o A B 0) (selectorKernel kernel o A B 1)) =
      ∑ t ∈ range (r+1), r.choose t •
        (∑ A₀ : Fin t → α, ∑ A₁ : Fin (r-t) → α,
          ∑ B₀ : Fin t → α, ∑ B₁ : Fin (r-t) → α,
            F (kernel t A₀ B₀) (kernel (r-t) A₁ B₁)) := by
  have hs (o : Fin r → Fin 2) :
      (∑ A : Fin r → α, ∑ B : Fin r → α,
        F (selectorKernel kernel o A B 0) (selectorKernel kernel o A B 1)) =
        ∑ A₀ : Fin (occ o 0) → α, ∑ A₁ : Fin (occ o 1) → α,
          ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
            F (kernel _ A₀ B₀) (kernel _ A₁ B₁) := by
    unfold selectorKernel
    trans ∑ A : Fin r → α, ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
      F (kernel _ (splitRanks o A 0) B₀) (kernel _ (splitRanks o A 1) B₁)
    · apply Finset.sum_congr rfl
      intro A _
      exact sum_split_selector o (fun B₀ B₁ =>
        F (kernel _ (splitRanks o A 0) B₀) (kernel _ (splitRanks o A 1) B₁))
    · exact sum_split_selector o (fun A₀ A₁ =>
        ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
          F (kernel _ A₀ B₀) (kernel _ A₁ B₁))
  simp_rw [hs]
  exact sum_selector_occupancy r (fun t u =>
    ∑ A₀ : Fin t → α, ∑ A₁ : Fin u → α, ∑ B₀ : Fin t → α, ∑ B₁ : Fin u → α,
      F (kernel t A₀ B₀) (kernel u A₁ B₁))

theorem independent_kernel_sum {α β : Type*} [Fintype α] [Fintype β]
    (f : α → α → Nat) (g : β → β → Nat) :
    (∑ a : α, ∑ b : β, ∑ c : α, ∑ d : β, (f a c + g b d)) =
      (∑ a, ∑ c, f a c) * (Fintype.card β)^2 +
      (Fintype.card α)^2 * (∑ b, ∑ d, g b d) := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum, Nat.cast_id]
  ring

theorem pair_kernel_moment {α : Type*} [Fintype α]
    (kernel : (n : Nat) → (Fin n → α) → (Fin n → α) → Nat) (r : Nat) :
    (∑ o : Fin r → Fin 2, ∑ A : Fin r → α, ∑ B : Fin r → α,
      (selectorKernel kernel o A B 0 + selectorKernel kernel o A B 1)) =
      2 * ∑ t ∈ range (r+1), r.choose t *
        (∑ A : Fin t → α, ∑ B : Fin t → α, kernel t A B) *
          (Fintype.card α)^(2*(r-t)) := by
  rw [sum_pair_kernel kernel r (fun x y => x+y)]
  have hi (t : Nat) := independent_kernel_sum (kernel t) (kernel (r-t))
  simp_rw [hi]
  simp only [Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
    mul_add, Finset.sum_add_distrib]
  let m := fun t => (∑ A : Fin t → α, ∑ B : Fin t → α, kernel t A B)
  have hp (t : Nat) : (Fintype.card α ^ t)^2 = Fintype.card α^(2*t) := by
    rw [← pow_mul, Nat.mul_comm t 2]
  simp only [hp]
  have hs : (∑ t ∈ range (r+1), r.choose t * (Fintype.card α^(2*t) * m (r-t))) =
      ∑ t ∈ range (r+1), r.choose t * m t * Fintype.card α^(2*(r-t)) := by
    have he := binomial_reverse_sum r (fun t => m t * Fintype.card α^(2*(r-t)))
    have hl : (∑ t ∈ range (r+1), r.choose t *
        (m (r-t) * Fintype.card α^(2*(r-(r-t))))) =
        ∑ t ∈ range (r+1), r.choose t * (Fintype.card α^(2*t) * m (r-t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' : t ≤ r := by have h := Finset.mem_range.mp ht; omega
      rw [Nat.sub_sub_self ht']
      ring
    rw [hl] at he
    simpa only [mul_assoc] using he
  change (∑ t ∈ range (r+1), r.choose t * (m t * Fintype.card α^(2*(r-t)))) +
    (∑ t ∈ range (r+1), r.choose t * (Fintype.card α^(2*t) * m (r-t))) = _
  rw [hs]
  dsimp only [m]
  simp only [mul_assoc]
  omega

theorem pair_near_moment {α : Type*} [Fintype α]
    (coverage near : (n : Nat) → (Fin n → α) → Nat) (r : Nat) :
    (∑ o : Fin r → Fin 2, ∑ A : Fin r → α, ∑ B : Fin r → α,
      (selectorKernel (fun n A B => near n A * coverage n B + coverage n A * near n B) o A B 0 +
       selectorKernel (fun n A B => near n A * coverage n B + coverage n A * near n B) o A B 1)) =
      4 * ∑ t ∈ range (r+1), r.choose t *
        (∑ A : Fin t → α, coverage t A) * (∑ A : Fin t → α, near t A) *
          (Fintype.card α)^(2*(r-t)) := by
  rw [pair_kernel_moment]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset

theorem independent_forest_first {α β : Type*} [Fintype α] [Fintype β]
    (f : α → Nat) (g : β → Nat) :
    (∑ A : Fin 4 → α, ∑ B : β, (∏ i, f (A i)) * g B) =
      (∑ A, f A)^4 * (∑ B, g B) := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Fintype.sum_pow]

theorem independent_forest_marked {α : Type*} [Fintype α]
    (f near : α → Nat) (k : Fin 4) :
    (∑ A : Fin 4 → α, ∏ i, if i = k then near (A i) else f (A i)) =
      (∑ A, near A) * (∑ A, f A)^3 := by
  classical
  rw [← Fintype.prod_sum (fun (i : Fin 4) (a : α) => if i = k then near a else f a)]
  fin_cases k <;> simp [Fin.prod_univ_succ] <;> ring

theorem independent_forest_near {α β : Type*} [Fintype α] [Fintype β]
    (f near : α → Nat) (g nearG : β → Nat) :
    (∑ A : Fin 4 → α, ∑ B : β,
      ((∑ k : Fin 4, ∏ i, if i = k then near (A i) else f (A i)) * g B +
        (∏ i, f (A i)) * nearG B)) =
      4 * (∑ A, near A) * (∑ A, f A)^3 * (∑ B, g B) +
        (∑ A, f A)^4 * (∑ B, nearG B) := by
  classical
  simp only [Finset.sum_add_distrib]
  rw [independent_forest_first f nearG]
  congr 1
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [independent_forest_marked f near]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedPathWinsor

theorem capped_fee_below (t x cap u E : ℝ)
    (hx : 0 ≤ x) (hxu : x ≤ u) (hu : 0 < u) (huc : u ≤ cap)
    (hE : Real.exp (t*u) ≤ E) :
    Real.exp (t * min x cap) - 1 ≤ x * ((E-1)/u) := by
  rw [min_eq_left (hxu.trans huc)]
  have hs := exp_secant t x u hx hxu hu
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hE 1) (div_nonneg hx hu.le)
  calc
    Real.exp (t*x)-1 ≤ (x/u)*(Real.exp (t*u)-1) := hs
    _ ≤ (x/u)*(E-1) := hm
    _ = x*((E-1)/u) := by ring

theorem capped_fee_above (t x cap l E : ℝ)
    (hcl : cap ≤ l) (hlx : l ≤ x) (hl : 0 < l)
    (hE : Real.exp (t*cap) ≤ E) (h1 : 1 ≤ E) :
    Real.exp (t * min x cap) - 1 ≤ x * ((E-1)/l) := by
  rw [min_eq_right (hcl.trans hlx)]
  have hpay : 0 ≤ (E-1)/l := div_nonneg (by linarith) hl.le
  calc
    Real.exp (t*cap)-1 ≤ E-1 := by linarith
    _ = l*((E-1)/l) := by field_simp
    _ ≤ x*((E-1)/l) := mul_le_mul_of_nonneg_right hlx hpay

theorem capped_fee_global (t x cap E : ℝ)
    (ht : 0 ≤ t) (hx : 0 ≤ x) (hc : 0 < cap)
    (hE : Real.exp (t*cap) ≤ E) :
    Real.exp (t * min x cap) - 1 ≤ x * ((E-1)/cap) := by
  have h1 : 1 ≤ E := (Real.one_le_exp (mul_nonneg ht hc.le)).trans hE
  by_cases hxc : x ≤ cap
  · exact capped_fee_below t x cap cap E hx hxc hc le_rfl hE
  · exact capped_fee_above t x cap cap E le_rfl (le_of_not_ge hxc) hc hE h1

theorem residual_fee_upper (x cap u : ℝ)
    (hx : 0 ≤ x) (hcap : 0 ≤ cap) (hxu : x ≤ u) (hu : 0 < u) :
    max 0 (x-cap) ≤ x * (max 0 (u-cap)/u) := by
  by_cases hxc : x ≤ cap
  · rw [max_eq_left (by linarith : x-cap ≤ 0)]
    positivity
  · have hcx : cap < x := lt_of_not_ge hxc
    have hcu : 0 ≤ u-cap := by linarith
    rw [max_eq_right (by linarith : 0 ≤ x-cap), max_eq_right hcu]
    have hm : cap*x ≤ cap*u := mul_le_mul_of_nonneg_left hxu hcap
    have he : x*((u-cap)/u) = (x*(u-cap))/u := by ring
    rw [he]
    apply (le_div_iff₀ hu).2
    nlinarith

end ClaudeWCT.Numerics.SharedPathWinsor

namespace ClaudeWCT.Numerics.SharedFees

def paidPlain (base : Nat) : List (Nat × Nat) → Nat → Nat × Nat × Nat
  | [], _ => (0,0,0)
  | (m,t)::fs,p =>
    let n := p % base
    let v := paidPlain base fs (p / base)
    (n+v.1,n*m+v.2.1,n*t+v.2.2)

theorem paidPlain_zero (base : Nat) (fs : List (Nat × Nat)) :
    paidPlain base fs 0 = (0,0,0) := by
  induction fs with
  | nil => rfl
  | cons e fs ih => simp [paidPlain, ih]

theorem paidDots_plain (fs : List (Nat × Nat)) (p : Nat) :
    paidDots fs p = paidPlain (2^4096) fs p := by
  induction fs generalizing p with
  | nil => rfl
  | cons e fs ih =>
    rcases e with ⟨m,t⟩
    by_cases hp : p=0
    · simp [hp, paidDots, paidPlain_zero]
    · simp only [paidDots, if_neg hp, paidPlain, ih,
        Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem paidPlain_mod (base : Nat) (fs : List (Nat × Nat)) (p : Nat) :
    paidPlain base fs (p % base^fs.length) = paidPlain base fs p := by
  induction fs generalizing p with
  | nil => rfl
  | cons e fs ih =>
    rcases e with ⟨m,t⟩
    simp only [List.length_cons, Nat.pow_succ, paidPlain,
      Nat.mod_mul_left_mod, Nat.mod_mul_left_div_self, ih]

theorem paidPlain_append (base : Nat) (as bs : List (Nat × Nat)) (p : Nat) :
    paidPlain base (as++bs) p =
      let a := paidPlain base as p
      let b := paidPlain base bs (p / base^as.length)
      (a.1+b.1,a.2.1+b.2.1,a.2.2+b.2.2) := by
  induction as generalizing p with
  | nil => simp [paidPlain]
  | cons e as ih =>
    rcases e with ⟨m,t⟩
    simp only [List.cons_append, List.length_cons, paidPlain, ih, Nat.pow_succ,
      Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm base (base^as.length)]
    simp only [Nat.add_assoc]

theorem paidTree_plain (fuel : Nat) (fs : List (Nat × Nat)) (p : Nat) :
    paidTree fuel fs p = paidPlain (2^4096) fs p := by
  induction fuel generalizing fs p with
  | zero => exact paidDots_plain fs p
  | succ fuel ih =>
    by_cases hp : p=0
    · simp [paidTree, hp, paidPlain_zero]
    · let half := fs.length/2
      have hlen : (fs.take half).length = half := by
        rw [List.length_take, Nat.min_eq_left (Nat.div_le_self _ _)]
      have he := paidPlain_append (2^4096) (fs.take half) (fs.drop half) p
      rw [List.take_append_drop, hlen] at he
      have hlo : paidPlain (2^4096) (fs.take half) (p % (2^4096)^half) =
          paidPlain (2^4096) (fs.take half) p := by
        simpa only [hlen] using paidPlain_mod (2^4096) (fs.take half) p
      dsimp only [half] at hlo he
      simp only [paidTree, if_neg hp, ih, Nat.shiftRight_eq_div_pow, Nat.pow_mul, hlo]
      exact he.symm

theorem paidTree_eq (fuel : Nat) (fs : List (Nat × Nat)) (p : Nat) :
    paidTree fuel fs p = paidDots fs p := by
  rw [paidTree_plain, paidDots_plain]

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.Thinning

abbrev PairHistory (β : Type) (r : Nat) :=
  (Fin r → Fin 2) × (Fin r → Fin 64 × β) × (Fin r → Fin 64 × β)

noncomputable def coordinateNear {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) {K r : Nat} (E : Fin r → Fin K × β) : Nat := by
  classical
  exact ∑ i : Fin 6, #{y : Fin K × β | CovAtExcept val i y.1 (val y.2) E}

theorem coordinate_near_history_sum {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : ∀ i, WFTable val i) (K r : Nat) (hK : 0 < K) :
    (∑ E : Fin r → Fin K × β, coordinateNear val E) = coordinateNearFormula K r := by
  classical
  have he (i : Fin 6) :
      (∑ E : Fin r → Fin K × β, #{y : Fin K × β | CovAtExcept val i y.1 (val y.2) E}) =
        #{y : (Fin K × β) × (Fin r → Fin K × β) |
          CovAtExcept val i y.1.1 (val y.1.2) y.2} := by
    simp only [Finset.card_filter, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_comm]
  unfold coordinateNear
  rw [Finset.sum_comm]
  simp_rw [he]
  exact coordinate_near_sum val hβ hW K r hK

noncomputable def pairCoverage {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) {r : Nat} (h : PairHistory β r) : Nat :=
  selectorValue (fun _ => coordinateCoverage val) h.1 h.2.1 h.2.2 0 +
  selectorValue (fun _ => coordinateCoverage val) h.1 h.2.1 h.2.2 1

noncomputable def pairNear {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) {r : Nat} (h : PairHistory β r) : Nat :=
  selectorKernel (fun _ A B => coordinateNear val A * coordinateCoverage val B +
    coordinateCoverage val A * coordinateNear val B) h.1 h.2.1 h.2.2 0 +
  selectorKernel (fun _ A B => coordinateNear val A * coordinateCoverage val B +
    coordinateCoverage val A * coordinateNear val B) h.1 h.2.1 h.2.2 1

theorem pair_coverage_history_sum {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (r : Nat) :
    (∑ h : PairHistory β r, pairCoverage val h) =
      2 * ∑ t ∈ range (r+1), r.choose t * (coordinateFormula 64 t)^2 *
        (64*563)^(2*(r-t)) := by
  have h := pair_first_moment (fun _ => coordinateCoverage val (C := Fin 64)) r
  simp only [Fintype.card_prod, Fintype.card_fin, hβ,
    coordinate_first_sum val hβ hW 64 _ (by decide)] at h
  simpa only [pairCoverage, Fintype.sum_prod_type] using h

theorem pair_near_history_sum {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (hN : ∀ i, WFTable val i) (r : Nat) :
    (∑ h : PairHistory β r, pairNear val h) =
      4 * ∑ t ∈ range (r+1), r.choose t * (coordinateFormula 64 t) *
        (coordinateNearFormula 64 t) * (64*563)^(2*(r-t)) := by
  have h := pair_near_moment (fun _ => coordinateCoverage val (C := Fin 64))
    (fun _ => coordinateNear val (K := 64)) r
  simp only [Fintype.card_prod, Fintype.card_fin, hβ,
    coordinate_first_sum val hβ hW 64 _ (by decide),
    coordinate_near_history_sum val hβ hN 64 _ (by decide)] at h
  simpa only [pairNear, Fintype.sum_prod_type] using h

end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedMoments
open Finset
open ClaudeWCT.Numerics.PoissonReflect (range_foldr_eq_sum fact_eq)

theorem row_values (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
  coord64[r]?.getD 0 = coordinateFormula 64 r ∧
  coord128[r]?.getD 0 = coordinateFormula 128 r ∧
  near64[r]?.getD 0 = coordinateNearFormula 64 r ∧
  near128[r]?.getD 0 = coordinateNearFormula 128 r ∧
  pairData[r]?.getD 0 = pairFormula r ∧ pairNearData[r]?.getD 0 = pairNearFormula r := by
  have h := List.all_eq_true.mp hrows r (List.mem_range.mpr hr)
  exact of_decide_eq_true h

theorem pairFormula_model (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
    pairFormula r = 2 * ∑ t ∈ range (r+1), r.choose t * (coordinateFormula 64 t)^2 *
      (64*563)^(2*(r-t)) := by
  unfold pairFormula
  rw [range_foldr_eq_sum]
  apply congrArg (fun n : Nat => 2*n)
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ r := by have h := Finset.mem_range.mp ht; omega
  rw [fact_eq, fact_eq, fact_eq, ← Nat.choose_eq_factorial_div_factorial ht',
    (row_values hrows t (by omega)).1]

theorem pairNearFormula_model (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
    pairNearFormula r = 4 * ∑ t ∈ range (r+1), r.choose t * (coordinateFormula 64 t) *
      (coordinateNearFormula 64 t) * (64*563)^(2*(r-t)) := by
  unfold pairNearFormula
  rw [range_foldr_eq_sum]
  apply congrArg (fun n : Nat => 4*n)
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ r := by have h := Finset.mem_range.mp ht; omega
  rw [fact_eq, fact_eq, fact_eq, ← Nat.choose_eq_factorial_div_factorial ht',
    (row_values hrows t (by omega)).1, (row_values hrows t (by omega)).2.2.1]
end ClaudeWCT.Numerics.SharedMoments

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.Thinning

theorem pair_coverage_data {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
    (∑ h : PairHistory β r, pairCoverage val h) = pairData[r]?.getD 0 := by
  rw [(row_values hrows r hr).2.2.2.2.1, pairFormula_model hrows r hr]
  exact pair_coverage_history_sum val hβ hW r

theorem pair_near_data {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (hN : ∀ i, WFTable val i)
    (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
    (∑ h : PairHistory β r, pairNear val h) = pairNearData[r]?.getD 0 := by
  rw [(row_values hrows r hr).2.2.2.2.2, pairNearFormula_model hrows r hr]
  exact pair_near_history_sum val hβ hW hN r

abbrev ForestHistory (β : Type) (r : Nat) :=
  (Fin 4 → PairHistory β r) × (Fin r → Fin 128 × β)

noncomputable def forestCoverage {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) {r : Nat} (h : ForestHistory β r) : Nat :=
  (∏ i, pairCoverage val (h.1 i)) * coordinateCoverage val h.2

noncomputable def forestNear {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) {r : Nat} (h : ForestHistory β r) : Nat :=
  (∑ k : Fin 4, ∏ i, if i = k then pairNear val (h.1 i) else pairCoverage val (h.1 i)) *
    coordinateCoverage val h.2 +
  (∏ i, pairCoverage val (h.1 i)) * coordinateNear val h.2

theorem forest_coverage_data {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
    (∑ h : ForestHistory β r, forestCoverage val h) = forestMoment r := by
  simp only [forestCoverage, Fintype.sum_prod_type]
  rw [independent_forest_first, pair_coverage_data val hβ hW hrows r hr,
    coordinate_first_sum val hβ hW 128 r (by decide), ← (row_values hrows r hr).2.1]
  rfl

theorem forest_near_data {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    (hW : W1Table val) (hN : ∀ i, WFTable val i)
    (hrows : rowChecks = true) (r : Nat) (hr : r < 81) :
    (∑ h : ForestHistory β r, forestNear val h) = forestNearMoment r := by
  simp only [forestNear, Fintype.sum_prod_type]
  rw [independent_forest_near, pair_coverage_data val hβ hW hrows r hr,
    pair_near_data val hβ hW hN hrows r hr,
    coordinate_first_sum val hβ hW 128 r (by decide), ← (row_values hrows r hr).2.1,
    coordinate_near_history_sum val hβ hN 128 r (by decide), ← (row_values hrows r hr).2.2.2.1]
  rfl

end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedMoments

theorem forest_alphabet_card {β : Type} [Fintype β]
    (hβ : Fintype.card β = 563) (r : Nat) :
    Fintype.card (ForestHistory β r) = alphabetSize ^ r := by
  simp only [ForestHistory, PairHistory, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, hβ, alphabetSize]
  simp only [mul_pow, ← pow_mul]
  ring

end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedFees
open ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathWinsor

theorem scale_pos : 0 < scale := by norm_num [scale]

theorem ceil_mul_bound (n d : Nat) (hd : 0 < d) : n ≤ ceilDiv n d * d :=
  winsorCeil_mul_le n d hd

theorem ceil_ratio_bound (n d : Nat) (hd : 0 < d) :
    (n : ℝ)/d ≤ (ceilDiv n d : ℝ) := winsorCeil_ratio_le n d hd

theorem expUpper_sound (x : Nat) (hx : x ≤ 8*scale) :
    Real.exp ((x : ℝ)/scale) ≤ (expUpper x : ℝ)/scale := by
  have hd : 0 < taylorDen scale ^ 8 := by
    have hS := scale_pos
    unfold taylorDen
    norm_num [ClaudeWCT.Numerics.Kernel.fact]
    positivity
  apply rational_exp_upper scale x (ceilDiv x 8) (expUpper x) scale_pos
  · have h := ceil_mul_bound x 8 (by decide)
    omega
  · unfold ceilDiv
    omega
  · exact ceil_mul_bound (scale * taylorNum scale (ceilDiv x 8)^8) (taylorDen scale^8) hd

theorem expUpper_ge (x : Nat) (hx : x ≤ 8*scale) : scale ≤ expUpper x := by
  have he := expUpper_sound x hx
  have hS : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have h1 : 1 ≤ Real.exp ((x : ℝ)/scale) := Real.one_le_exp (by positivity)
  have h := (le_div_iff₀ hS).mp (h1.trans he)
  simpa only [one_mul, Nat.cast_le] using h

theorem cap_argument_bound : ceilDiv (36*scale) 5 ≤ 8*scale := by
  unfold ceilDiv
  have h := scale_pos
  omega

theorem capExp_sound : Real.exp (36/5 : ℝ) ≤ (capExp : ℝ)/scale := by
  have hS : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have hr := ceil_ratio_bound (36*scale) 5 (by decide)
  have he : (36/5 : ℝ) ≤ (ceilDiv (36*scale) 5 : ℝ)/scale := by
    apply (le_div_iff₀ hS).2
    push_cast at hr
    nlinarith
  exact (Real.exp_le_exp.mpr he).trans (expUpper_sound _ cap_argument_bound)

theorem capExp_ge : scale ≤ capExp := expUpper_ge _ cap_argument_bound

theorem maxFee_ratio_bound :
    ((capExp : ℝ)/scale-1)/(6/5) ≤ (maxFee : ℝ)/scale := by
  have hS : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have hm := ceil_mul_bound (5*(capExp-scale)) 6 (by decide)
  change 5*(capExp-scale) ≤ maxFee*6 at hm
  have hmR : (5 : ℝ)*((capExp : ℝ)-scale) ≤ (maxFee : ℝ)*6 := by
    have hc : (5 : ℝ) * ((capExp-scale : Nat) : ℝ) ≤ (maxFee : ℝ)*6 := by exact_mod_cast hm
    simpa only [Nat.cast_sub capExp_ge] using hc
  apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<6/5) hS).2
  have he : ((capExp : ℝ)/scale-1)*scale = (capExp : ℝ)-scale := by
    field_simp
  rw [he]
  linarith

theorem global_fee_sound (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (6 * min x (6/5)) - 1 ≤ x * ((maxFee : ℝ)/scale) := by
  have he := capped_fee_global 6 x (6/5) ((capExp : ℝ)/scale)
    (by norm_num) hx (by norm_num) (by convert capExp_sound using 1 <;> norm_num)
  exact he.trans (mul_le_mul_of_nonneg_left maxFee_ratio_bound hx)

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
open ClaudeWCT.Numerics.SharedPathWinsor

theorem ceil_le (n d k : Nat) (hd : 0 < d) (hn : n ≤ k*d) :
    ceilDiv n d ≤ k := by
  unfold ceilDiv
  apply (Nat.div_le_iff_le_mul hd).2
  omega

theorem rounded_ratio (E u v : Nat) (hE : scale ≤ E) (hu : 0 < u) (hv : 0 < v) :
    ((E : ℝ)/scale-1)/((u : ℝ)/v) ≤
      (ceilDiv ((E-scale)*v) u : ℝ)/scale := by
  have hS : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hc := ceil_mul_bound ((E-scale)*v) u hu
  have hcR : ((E : ℝ)-scale)*v ≤ (ceilDiv ((E-scale)*v) u : ℝ)*u := by
    have := (show ((E-scale : Nat) : ℝ)*v ≤ (ceilDiv ((E-scale)*v) u : ℝ)*u by exact_mod_cast hc)
    simpa only [Nat.cast_sub hE] using this
  apply (div_le_div_iff₀ (div_pos huR hvR) hS).2
  have he : ((E : ℝ)/scale-1)*scale = (E : ℝ)-scale := by field_simp
  rw [he, ← mul_div_assoc]
  exact (le_div_iff₀ hvR).2 hcR

theorem below_fee_sound (u v : Nat) (x : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hcap : 5*u ≤ 6*v) (hx : 0 ≤ x) (hxu : x ≤ (u : ℝ)/v) :
    Real.exp (6 * min x (6/5)) - 1 ≤
      x * ((ceilDiv ((expUpper (ceilDiv (6*scale*u) v)-scale)*v) u : ℝ)/scale) := by
  have hS : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have harg : ceilDiv (6*scale*u) v ≤ 8*scale := by
    apply ceil_le _ _ _ hv
    have hSn := scale_pos
    nlinarith
  have hround := ceil_mul_bound (6*scale*u) v hv
  have hrR : (6 : ℝ)*scale*u ≤ (ceilDiv (6*scale*u) v : ℝ)*v := by exact_mod_cast hround
  have hearg : (6 : ℝ)*((u : ℝ)/v) ≤ (ceilDiv (6*scale*u) v : ℝ)/scale := by
    apply (le_div_iff₀ hS).2
    rw [show (6 : ℝ)*((u : ℝ)/v)*scale = (6*scale*u)/v by ring]
    exact (div_le_iff₀ hvR).2 hrR
  have he := (Real.exp_le_exp.mpr hearg).trans (expUpper_sound _ harg)
  have huc : (u : ℝ)/v ≤ 6/5 := by
    apply (div_le_iff₀ hvR).2
    have hc : (5 : ℝ)*u ≤ 6*v := by exact_mod_cast hcap
    linarith
  have h := capped_fee_below 6 x (6/5) ((u : ℝ)/v)
    ((expUpper (ceilDiv (6*scale*u) v) : ℝ)/scale) hx hxu (div_pos huR hvR) huc he
  exact h.trans (mul_le_mul_of_nonneg_left
    (rounded_ratio _ u v (expUpper_ge _ harg) hu hv) hx)

theorem capped_fee_above_loose (x l E : ℝ) (hl : 0 < l) (hlx : l ≤ x)
    (hE : Real.exp (36/5 : ℝ) ≤ E) (h1 : 1 ≤ E) :
    Real.exp (6*min x (6/5))-1 ≤ x*((E-1)/l) := by
  have he : Real.exp (6*min x (6/5)) ≤ E := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hE
    have := min_le_right x (6/5)
    linarith
  have hp : 0 ≤ (E-1)/l := div_nonneg (by linarith) hl.le
  calc
    Real.exp (6*min x (6/5))-1 ≤ E-1 := by linarith
    _ = l*((E-1)/l) := by field_simp
    _ ≤ x*((E-1)/l) := mul_le_mul_of_nonneg_right hlx hp

theorem above_fee_sound (L : Nat) (x : ℝ) (hL : 0 < L)
    (hlx : (L : ℝ)/scale ≤ x) :
    Real.exp (6*min x (6/5))-1 ≤
      x*((ceilDiv (scale*(capExp-scale)) L : ℝ)/scale) := by
  have hS : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hx : 0 ≤ x := (div_pos hLR hS).le.trans hlx
  have h1 : (1 : ℝ) ≤ (capExp : ℝ)/scale := by
    exact (le_div_iff₀ hS).2 (by exact_mod_cast capExp_ge)
  have h := capped_fee_above_loose x ((L : ℝ)/scale)
    ((capExp : ℝ)/scale) (div_pos hLR hS) hlx capExp_sound h1
  have hr := rounded_ratio capExp L scale capExp_ge hL scale_pos
  rw [Nat.mul_comm (capExp-scale) scale] at hr
  exact h.trans (mul_le_mul_of_nonneg_left hr hx)

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
open ClaudeWCT.Numerics.SharedPathWinsor

theorem residual_round (u v : Nat) (hu : 0 < u) (hv : 0 < v) :
    max 0 ((u : ℝ)/v-6/5)/((u : ℝ)/v) ≤
      (ceilDiv (scale*(u*5-v*6)) (u*5) : ℝ)/scale := by
  have hS : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  by_cases h : v*6 ≤ u*5
  · have hR : (v : ℝ)*6 ≤ (u : ℝ)*5 := by exact_mod_cast h
    have hd : 0 ≤ (u : ℝ)/v-6/5 := by
      have hr : (6/5 : ℝ) ≤ (u : ℝ)/v := (le_div_iff₀ hvR).2 (by linarith)
      linarith
    rw [max_eq_right hd]
    have he : (((u : ℝ)/v)-6/5)/((u : ℝ)/v) = ((u : ℝ)*5-v*6)/((u : ℝ)*5) := by
      field_simp
      <;> ring
    rw [he]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (u : ℝ)*5) hS).2
    have hc := ceil_mul_bound (scale*(u*5-v*6)) (u*5) (by omega)
    have hcR : (scale : ℝ)*((u*5-v*6 : Nat) : ℝ) ≤
        (ceilDiv (scale*(u*5-v*6)) (u*5) : ℝ)*((u : ℝ)*5) := by exact_mod_cast hc
    rw [Nat.cast_sub h] at hcR
    push_cast at hcR
    nlinarith
  · have hR : (u : ℝ)*5 ≤ (v : ℝ)*6 := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge h))
    have hd : (u : ℝ)/v-6/5 ≤ 0 := by
      have hr : (u : ℝ)/v ≤ 6/5 := (div_le_iff₀ hvR).2 (by linarith)
      linarith
    rw [max_eq_left hd, zero_div]
    positivity

theorem residual_fee_sound (u v : Nat) (x : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hx : 0 ≤ x) (hxu : x ≤ (u : ℝ)/v) :
    max 0 (x-6/5) ≤ x*((ceilDiv (scale*(u*5-v*6)) (u*5) : ℝ)/scale) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  exact (residual_fee_upper x (6/5) ((u : ℝ)/v) hx (by norm_num) hxu
    (div_pos huR hvR)).trans (mul_le_mul_of_nonneg_left (residual_round u v hu hv) hx)

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees

theorem floor_ratio_le (n d : Nat) (hd : 0 < d) :
    ((n/d : Nat) : ℝ) ≤ (n : ℝ)/d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  exact (le_div_iff₀ hdR).2 (by exact_mod_cast Nat.div_mul_le_self n d)

theorem scaled_floor_le (n d : Nat) (hd : 0 < d) :
    (((scale*n/d : Nat) : ℝ)/scale) ≤ (n : ℝ)/d := by
  have hS : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have h := floor_ratio_le (scale*n) d hd
  rw [Nat.cast_mul] at h
  apply (div_le_iff₀ hS).2
  rw [show (n : ℝ)/d*(scale : ℝ) = (scale : ℝ)*n/d by ring]
  exact h

theorem scaled_floor_pos (n d : Nat) (hd : 0 < d) (hcap : 6*d ≤ 5*n) :
    0 < scale*n/d := by
  have hS : 1 ≤ scale := scale_pos
  have hnd : d ≤ n := by omega
  have hm : n ≤ scale*n := by nlinarith
  exact Nat.div_pos (hnd.trans hm) hd

theorem expectedRun_sound (lo hi : Nat) (x : ℝ) (hx : 0 ≤ x)
    (hlo : (((734*101^lo*100^13 : Nat) : ℝ)/(2^66*100^lo*101^13 : Nat)) ≤ x)
    (hhi : x ≤ ((734*101^hi : Nat) : ℝ)/(2^66*100^hi : Nat)) :
    Real.exp (6*min x (6/5))-1 ≤ x*((expectedRun lo hi).1 : ℝ)/scale ∧
    max 0 (x-6/5) ≤ x*((expectedRun lo hi).2 : ℝ)/scale := by
  let un := 734*101^hi
  let ud := 2^66*100^hi
  let ln := 734*101^lo
  let ld := 2^66*100^lo
  have hu : 0 < un := by dsimp [un]; positivity
  have hd : 0 < ud := by dsimp [ud]; positivity
  have hld : 0 < ld*101^13 := by dsimp [ld]; positivity
  change x ≤ (un : ℝ)/ud at hhi
  change ((ln*100^13 : Nat) : ℝ)/(ld*101^13 : Nat) ≤ x at hlo
  constructor
  · change Real.exp (6*min x (6/5))-1 ≤
      x*((if un*5 ≤ ud*6 then
        ceilDiv ((expUpper (ceilDiv (6*scale*un) ud)-scale)*ud) un
      else if ln*100^13*5 ≥ ld*101^13*6 then
        ceilDiv (scale*(capExp-scale)) (scale*ln*100^13/(ld*101^13))
      else maxFee : Nat) : ℝ)/scale
    rw [mul_div_assoc]
    split_ifs with hb ha
    · exact below_fee_sound un ud x hu hd (by omega) hx hhi
    · apply above_fee_sound
      · rw [Nat.mul_assoc scale ln]
        apply scaled_floor_pos _ _ hld
        nlinarith [ha]
      · have h := scaled_floor_le (ln*100^13) (ld*101^13) hld
        rw [← Nat.mul_assoc] at h
        exact h.trans hlo
    · exact global_fee_sound x hx
  · change max 0 (x-6/5) ≤
      x*((ceilDiv (scale*(un*5-ud*6)) (un*5) : Nat) : ℝ)/scale
    rw [mul_div_assoc]
    exact residual_fee_sound un ud x hu hd hx hhi

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees

theorem run_valid_of_chunks
    (hsize : feeRuns.size = 1578)
    (hchunks : ∀ block : Nat, block < 25 → feeChunk block = true)
    (i : Nat) (hi : i < feeRuns.size) :
    let e := feeRuns[i]?.getD (0,0,0,0)
    e.1 ≤ e.2.1 ∧ (e.2.2.1,e.2.2.2) = expectedRun e.1 e.2.1 ∧
      e.2.2.1 ≤ maxFee ∧ e.2.2.2 ≤ scale := by
  have hib : i < 1578 := by omega
  have hb := hchunks (i/64) (by omega)
  rw [feeChunk, List.all_eq_true] at hb
  have hj := hb (i%64) (by simp only [List.mem_range]; omega)
  have he : 64*(i/64)+i%64 = i := by omega
  simpa only [he, if_pos hi, decide_eq_true_eq] using hj

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 100000

theorem indexed_list_member {α : Type} (xs : List (Nat × α)) (fallback : α)
    (N : Nat) (hidx : xs.map Prod.fst = List.range N) (i : Nat) (hi : i < N) :
    (i, ((xs.map Prod.snd)[i]?.getD fallback)) ∈ xs := by
  have hlen : xs.length = N := by simpa using congrArg List.length hidx
  have hx : i < xs.length := by omega
  have he : xs[i]?.getD (i,fallback) = xs[i] := by simp [List.getElem?_eq_getElem hx]
  have hfst := congrArg (fun ys : List Nat => ys[i]?.getD 0) hidx
  simp only [List.getElem?_map, List.getElem?_eq_getElem hx, Option.map_some,
    Option.getD_some, List.getElem?_range hi] at hfst
  have hmem : xs[i] ∈ xs := List.mem_of_getElem rfl
  have heq : (i, ((xs.map Prod.snd)[i]?.getD fallback)) = xs[i] := by
    simp only [List.getElem?_map, List.getElem?_eq_getElem hx, Option.map_some, Option.getD_some]
    exact Prod.ext hfst.symm rfl
  rw [heq]
  exact hmem

theorem fee_lookup_member (hidx : feeEntries.map Prod.fst = List.range 7210)
    (i : Nat) (hi : i < 7210) : (i, fees[i]?.getD (0,0)) ∈ feeEntries := by
  simpa only [fees, List.getElem?_toArray] using
    indexed_list_member feeEntries (0,0) 7210 hidx i hi

attribute [local irreducible] feeEntries fees feeRuns

theorem fee_lookup_run (hordered : ∀ e ∈ feeRuns.toList, e.1 ≤ e.2.1)
    (hidx : feeEntries.map Prod.fst = List.range 7210)
    (i : Nat) (hi : i < 7210) :
    ∃ e ∈ feeRuns.toList, e.1 ≤ i ∧ i ≤ e.2.1 ∧ fees[i]?.getD (0,0) = (e.2.2.1,e.2.2.2) := by
  have h := fee_lookup_member hidx i hi
  rw [feeEntries, List.mem_flatMap] at h
  obtain ⟨e, he, hm⟩ := h
  rw [List.mem_map] at hm
  obtain ⟨j, hj, hpair⟩ := hm
  have hji : j = i := congrArg Prod.fst hpair
  subst j
  simp only [List.mem_range'] at hj
  obtain ⟨k, hk, hki⟩ := hj
  have hord := hordered e he
  refine ⟨e, he, by omega, ?_, ?_⟩
  · omega
  · exact (congrArg Prod.snd hpair).symm

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.CanonicalCounting
open scoped BigOperators Polynomial
open Finset
set_option maxHeartbeats 1000000

def digit (bits packed position : Nat) : Nat :=
  (packed >>> (bits*position)) % 2^bits

theorem digit_histogram {α : Type} [Fintype α] (g : α → Nat) (bits : Nat)
    (hc : Fintype.card α < 2^bits) (k : Nat) :
    digit bits (∑ a, (2^bits)^(g a)) k = (univ.filter fun a => g a = k).card := by
  classical
  let P : Nat[X] := ∑ a, Polynomial.monomial (g a) 1
  have hp (j : Nat) : P.coeff j = (univ.filter fun a => g a = j).card := by
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, eq_comm]
  have hb (j : Nat) : P.coeff j < 2^bits := by
    rw [hp]
    exact (card_filter_le _ _).trans_lt (by simpa using hc)
  have he : P.eval (2^bits) = ∑ a, (2^bits)^(g a) := by simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_mul]
  rw [← he]
  unfold digit
  rw [Nat.shiftRight_eq_div_pow, pow_mul]
  exact (ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) k P hb).trans (hp k)


end ClaudeWCT.Numerics.CanonicalCounting

namespace ClaudeWCT.Numerics.SharedFees

noncomputable def upperValue (i : Nat) : ℝ :=
  ((734*101^i : Nat) : ℝ)/(2^66*100^i : Nat)
noncomputable def lowerValue (i : Nat) : ℝ :=
  ((734*101^i*100^13 : Nat) : ℝ)/(2^66*100^i*101^13 : Nat)

theorem upperValue_power (i : Nat) :
    upperValue i = (734 : ℝ)/2^66 * ((101 : ℝ)/100)^i := by
  unfold upperValue
  push_cast
  rw [div_pow]
  ring

theorem lowerValue_power (i : Nat) :
    lowerValue i = upperValue i * ((100 : ℝ)/101)^13 := by
  unfold lowerValue upperValue
  push_cast
  rw [div_pow]
  ring

theorem upperValue_mono {i j : Nat} (hij : i ≤ j) : upperValue i ≤ upperValue j := by
  rw [upperValue_power, upperValue_power]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 101/100) hij

theorem lowerValue_mono {i j : Nat} (hij : i ≤ j) : lowerValue i ≤ lowerValue j := by
  rw [lowerValue_power, lowerValue_power]
  exact mul_le_mul_of_nonneg_right (upperValue_mono hij) (by positivity)

theorem run_contains_fee_sound (lo i hi m r : Nat) (x : ℝ)
    (hloi : lo ≤ i) (hihi : i ≤ hi) (hx : 0 ≤ x)
    (hlo : lowerValue i ≤ x) (hhi : x ≤ upperValue i)
    (hfee : (m,r) = expectedRun lo hi) :
    Real.exp (6*min x (6/5))-1 ≤ x*(m : ℝ)/scale ∧
    max 0 (x-6/5) ≤ x*(r : ℝ)/scale := by
  have h := expectedRun_sound lo hi x hx ((lowerValue_mono hloi).trans hlo)
    (hhi.trans (upperValue_mono hihi))
  rw [← hfee] at h
  exact h

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 100000
attribute [local irreducible] feeEntries fees feeRuns

theorem fee_run_values (hsize : feeRuns.size = 1578)
    (hchunks : ∀ block : Nat, block < 25 → feeChunk block = true)
    (e : Nat × Nat × Nat × Nat) (he : e ∈ feeRuns.toList) :
    e.1 ≤ e.2.1 ∧ (e.2.2.1,e.2.2.2) = expectedRun e.1 e.2.1 ∧
      e.2.2.1 ≤ maxFee ∧ e.2.2.2 ≤ scale := by
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem he
  have hi' : i < feeRuns.size := by simpa using hi
  have hlookup : feeRuns[i]?.getD (0,0,0,0) = e := by
    rw [Array.getElem?_eq_getElem hi', Option.getD_some]
    simpa only [Array.getElem_toList] using hie
  have h := run_valid_of_chunks hsize hchunks i hi'
  rw [hlookup] at h
  exact h

theorem fee_lookup_sound (hsize : feeRuns.size = 1578)
    (hchunks : ∀ block : Nat, block < 25 → feeChunk block = true)
    (hidx : feeEntries.map Prod.fst = List.range 7210)
    (i : Nat) (hi : i < 7210) (x : ℝ) (hx : 0 ≤ x)
    (hlo : lowerValue i ≤ x) (hhi : x ≤ upperValue i) :
    Real.exp (6*min x (6/5))-1 ≤ x*((fees[i]?.getD (0,0)).1 : ℝ)/scale ∧
    max 0 (x-6/5) ≤ x*((fees[i]?.getD (0,0)).2 : ℝ)/scale := by
  have hv := fee_run_values hsize hchunks
  have hord : ∀ e ∈ feeRuns.toList, e.1 ≤ e.2.1 := fun e he => (hv e he).1
  obtain ⟨e, he, hloi, hihi, hfee⟩ := fee_lookup_run hord hidx i hi
  rw [hfee]
  exact run_contains_fee_sound e.1 i e.2.1 e.2.2.1 e.2.2.2 x hloi hihi hx hlo hhi
    (hv e he).2.1

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.CanonicalCounting

theorem eq_of_digits (B : Nat) (hB : 0 < B) (n : Nat) (a b : Nat)
    (ha : a < B^n) (hb : b < B^n)
    (hd : ∀ i : Nat, i < n → a/B^i%B = b/B^i%B) : a = b := by
  induction n generalizing a b with
  | zero => simp only [Nat.pow_zero] at ha hb; omega
  | succ n ih =>
    have ha' : a/B < B^n := by
      apply (Nat.div_lt_iff_lt_mul hB).2
      simpa only [Nat.pow_succ] using ha
    have hb' : b/B < B^n := by
      apply (Nat.div_lt_iff_lt_mul hB).2
      simpa only [Nat.pow_succ] using hb
    have hd' : ∀ i : Nat, i < n → (a/B)/B^i%B = (b/B)/B^i%B := by
      intro i hi
      have h := hd (i+1) (by omega)
      simpa only [Nat.div_div_eq_div_mul, ← Nat.pow_succ'] using h
    have hq := ih (a/B) (b/B) ha' hb' hd'
    have h0 := hd 0 (by omega)
    simp only [Nat.pow_zero, Nat.div_one] at h0
    have ea := Nat.mod_add_div a B
    have eb := Nat.mod_add_div b B
    rw [h0, hq] at ea
    omega

end ClaudeWCT.Numerics.CanonicalCounting

namespace ClaudeWCT.Numerics.SharedFees

theorem chunks_25 {P : Nat → Prop}
    (h0 : P 0)
    (h1 : P 1)
    (h2 : P 2)
    (h3 : P 3)
    (h4 : P 4)
    (h5 : P 5)
    (h6 : P 6)
    (h7 : P 7)
    (h8 : P 8)
    (h9 : P 9)
    (h10 : P 10)
    (h11 : P 11)
    (h12 : P 12)
    (h13 : P 13)
    (h14 : P 14)
    (h15 : P 15)
    (h16 : P 16)
    (h17 : P 17)
    (h18 : P 18)
    (h19 : P 19)
    (h20 : P 20)
    (h21 : P 21)
    (h22 : P 22)
    (h23 : P 23)
    (h24 : P 24) : ∀ i : Nat, i < 25 → P i := by
  intro i hi
  interval_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h24

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees

theorem all_chunks : ∀ block : Nat, block < 25 → feeChunk block = true :=
  chunks_25 (P := fun block => feeChunk block = true)
    first_fee_chunk fee_chunk_1 fee_chunk_2 fee_chunk_3 fee_chunk_4 fee_chunk_5 fee_chunk_6 fee_chunk_7 fee_chunk_8 fee_chunk_9 fee_chunk_10 fee_chunk_11 fee_chunk_12 fee_chunk_13 fee_chunk_14 fee_chunk_15 fee_chunk_16 fee_chunk_17 fee_chunk_18 fee_chunk_19 fee_chunk_20 fee_chunk_21 fee_chunk_22 fee_chunk_23 fee_chunk_24

theorem fees_sound (i : Nat) (hi : i < 7210) (x : ℝ) (hx : 0 ≤ x)
    (hlo : lowerValue i ≤ x) (hhi : x ≤ upperValue i) :
    Real.exp (6*min x (6/5))-1 ≤ x*((fees[i]?.getD (0,0)).1 : ℝ)/scale ∧
    max 0 (x-6/5) ≤ x*((fees[i]?.getD (0,0)).2 : ℝ)/scale :=
  fee_lookup_sound fee_runs_count all_chunks fee_indices i hi x hx hlo hhi

end ClaudeWCT.Numerics.SharedFees
