import SigGolfCandidate.ClaudeWCT_Numerics_N600Price
import SigGolfCandidate.ClaudeWCT_Numerics_LawAverage
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Route C for the marked-index bank excess (R6 campaign, stream RC).

`E (X - θ)⁺` for `X = ∑ⱼ pb Lⱼ` is split pointwise into a clipped background `Y = ∑ min (pb Lⱼ) c₀`
(Chernoff), one large bucket on a short row (paid through the exact one-index conditional law and the
Scarf bound), two or more large buckets (negative correlation), and buckets on long rows (first
moment). All numeric premises are per-bucket moments of the coordinate law; they are discharged from
binned fee certificates elsewhere. -/

namespace ClaudeWCT.Numerics.RouteC
open ENNReal Finset ClaudeWCT.Numerics.Law
open SphincsSecurity.Concrete (binomialAverage binomialAverage_succ binomialAverage_mono
  binomialAverage_sum binomialAverage_mul_left)
open SigGolfCandidate.T3.BPORS.History (atIndex atIndex_cons)

/-! ### The one-index conditional law (RC_SPEC I5 / L2) -/
section Split
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] (v : β → ENNReal)

/-- The draws of a marked word at the indices other than `j`, re-indexed by the subtype. -/
def eraseIdx (j : α) : List (α × β) → List ({i // i ≠ j} × β)
  | [] => []
  | p :: W => if h : p.1 = j then eraseIdx j W else (⟨p.1, h⟩, p.2) :: eraseIdx j W

omit [Fintype α] [Fintype β] in
theorem eraseIdx_cons_self (j : α) (b : β) (W : List (α × β)) :
    eraseIdx j ((j, b) :: W) = eraseIdx j W := by
  simp [eraseIdx]

omit [Fintype α] [Fintype β] in
theorem eraseIdx_cons_ne {j a : α} (h : a ≠ j) (b : β) (W : List (α × β)) :
    eraseIdx j ((a, b) :: W) = (⟨a, h⟩, b) :: eraseIdx j W := by
  simp [eraseIdx, h]

omit [Fintype α] [Fintype β] in
theorem atIndex_eraseIdx (j : α) (i : {i // i ≠ j}) (W : List (α × β)) :
    atIndex i (eraseIdx j W) = atIndex i.1 W := by
  induction W with
  | nil => rfl
  | cons p W ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : a = j
    · subst h
      rw [eraseIdx_cons_self, ih, atIndex_cons_ne (Ne.symm i.2)]
    · rw [eraseIdx_cons_ne h, atIndex_cons, atIndex_cons, ih]
      simp only [Subtype.ext_iff]

theorem binomialAverage_congr (rate : ENNReal) (T : ℕ) {f g : ℕ → ENNReal}
    (h : ∀ r, r ≤ T → f r = g r) : binomialAverage rate T f = binomialAverage rate T g := by
  induction T generalizing f g with
  | zero => exact h 0 le_rfl
  | succ T ih =>
    rw [binomialAverage_succ, binomialAverage_succ, ih (fun r hr => h r (by omega)),
      ih (fun r hr => h (r + 1) (by omega))]

theorem card_ne_subtype (j : α) : Fintype.card {i // i ≠ j} = Fintype.card α - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- Splitting a marked word at one index: the bucket at `j` is a binomial number of coordinate
draws, and given that bucket the other draws form the marked law on the remaining indices. -/
theorem law_marked_split (hv : ∑ b, v b = 1) (j : α) (hcard : 1 < Fintype.card α) (T : ℕ)
    (F : List β → List ({i // i ≠ j} × β) → ENNReal) :
    lawAvg (marked (α := α) v) T (fun W => F (atIndex j W) (eraseIdx j W)) =
      binomialAverage (Fintype.card α : ENNReal)⁻¹ T
        (fun r => lawAvg v r (fun L => lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (F L))) := by
  set p : ENNReal := (Fintype.card α : ENNReal)⁻¹ with hp
  have hc0 : (Fintype.card α : ENNReal) ≠ 0 := by exact_mod_cast (by omega : Fintype.card α ≠ 0)
  have hct : (Fintype.card α : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  set n' : ℕ := Fintype.card {i // i ≠ j} with hn'
  have hn'v : n' = Fintype.card α - 1 := card_ne_subtype j
  have hn'0 : (n' : ENNReal) ≠ 0 := by exact_mod_cast (by omega : n' ≠ 0)
  have hn't : (n' : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hk : (n' : ENNReal) * p = 1 - p := by
    have h1 : (n' : ENNReal) + 1 = Fintype.card α := by
      rw [hn'v]; norm_cast; omega
    have h2 : (n' : ENNReal) * p + p = 1 := by
      rw [← add_one_mul, h1, hp, ENNReal.mul_inv_cancel hc0 hct]
    rw [← h2, ENNReal.add_sub_cancel_right (by simp [hp, hc0])]
  induction T generalizing F with
  | zero =>
    simp [lawAvg_zero, atIndex, eraseIdx, binomialAverage]
  | succ T ih =>
    rw [lawAvg_succ, sum_marked]
    -- the summand for one first draw `(a, b)`
    let A : ENNReal := binomialAverage p T
      (fun r => lawAvg v (r + 1) (fun L => lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (F L)))
    let B : {i // i ≠ j} → ENNReal := fun a' => binomialAverage p T (fun r => lawAvg v r
      (fun L => ∑ b, v b * lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (fun R => F L ((a', b) :: R))))
    have hrow : ∀ a : α, ∑ b, v b * lawAvg (marked (α := α) v) T
        (fun W => F (atIndex j ((a, b) :: W)) (eraseIdx j ((a, b) :: W))) =
        if h : a = j then A else B ⟨a, h⟩ := by
      intro a
      by_cases h : a = j
      · rw [dif_pos h]
        subst h
        simp_rw [atIndex_cons_self, eraseIdx_cons_self]
        have hb : ∀ b, lawAvg (marked (α := α) v) T (fun W => F (b :: atIndex a W) (eraseIdx a W)) =
            binomialAverage p T (fun r => lawAvg v r
              (fun L => lawAvg (marked (α := {i // i ≠ a}) v) (T - r) (F (b :: L)))) :=
          fun b => ih (fun L R => F (b :: L) R)
        simp_rw [hb]
        rw [binomialAverage_lawSum]
        rfl
      · rw [dif_neg h]
        simp_rw [atIndex_cons_ne h, eraseIdx_cons_ne h]
        have hb : ∀ b, lawAvg (marked (α := α) v) T
            (fun W => F (atIndex j W) ((⟨a, h⟩, b) :: eraseIdx j W)) =
            binomialAverage p T (fun r => lawAvg v r (fun L => lawAvg (marked (α := {i // i ≠ j}) v)
              (T - r) (fun R => F L ((⟨a, h⟩, b) :: R)))) :=
          fun b => ih (fun L R => F L ((⟨a, h⟩, b) :: R))
        simp_rw [hb]
        rw [binomialAverage_lawSum]
        congr 1
        funext r
        rw [lawAvg_sum]
        simp_rw [lawAvg_mul_left]
    simp_rw [hrow]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), dif_pos rfl]
    have hrest : ∑ a ∈ univ.erase j, (Fintype.card α : ENNReal)⁻¹ * (if h : a = j then A else B ⟨a, h⟩) =
        ∑ a' : {i // i ≠ j}, p * B a' := by
      rw [Finset.sum_subtype (univ.erase j) (p := fun a => a ≠ j) (fun x => by simp)]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [dif_neg a'.2]
    rw [hrest, ← Finset.mul_sum, binomialAverage_succ]
    -- the `j`-draw term
    have hA : A = binomialAverage p T (fun r => lawAvg v (r + 1)
        (fun L => lawAvg (marked (α := {i // i ≠ j}) v) (T + 1 - (r + 1)) (F L))) := by
      refine binomialAverage_congr p T fun r _ => ?_
      rw [Nat.add_sub_add_right]
    -- the other draws
    have hB : ∑ a', B a' = (n' : ENNReal) * binomialAverage p T (fun r => lawAvg v r
        (fun L => lawAvg (marked (α := {i // i ≠ j}) v) (T + 1 - r) (F L))) := by
      have hsum : ∑ a', B a' = binomialAverage p T (fun r => lawAvg v r (fun L =>
          ∑ a' : {i // i ≠ j}, ∑ b, v b *
            lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (fun R => F L ((a', b) :: R)))) := by
        simp only [B]
        rw [← binomialAverage_sum]
        congr 1
        funext r
        rw [← lawAvg_sum]
      rw [hsum, ← binomialAverage_mul_left]
      refine binomialAverage_congr p T fun r hr => ?_
      rw [← lawAvg_mul_left]
      congr 1
      funext L
      have hs := sum_marked v (α' := {i // i ≠ j})
        (fun x => lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (fun R => F L (x :: R)))
      rw [show T + 1 - r = (T - r) + 1 by omega, lawAvg_succ, hs, ← Finset.mul_sum, ← mul_assoc,
        ENNReal.mul_inv_cancel hn'0 hn't, one_mul]
    rw [hB, ← mul_assoc, mul_comm p (n' : ENNReal), hk, hA]
    ring

#print axioms law_marked_split
end Split

/-! ### The Scarf bound (RC_SPEC I6 / L3) -/
section Scarf

/-- Scarf's stop-loss bound: `E (Z - y)⁺ ≤ scarf y μ V` when `E Z = μ` and `Var Z ≤ V`. -/
noncomputable def scarf (y μ V : ℝ) : ℝ := ((μ - y) + Real.sqrt ((μ - y) ^ 2 + V)) / 2

theorem scarf_mono {y μ μ' V V' : ℝ} (hμ : μ ≤ μ') (hV : V ≤ V') (hV0 : 0 ≤ V) :
    scarf y μ V ≤ scarf y μ' V' := by
  unfold scarf
  have h1 : Real.sqrt ((μ' - y) ^ 2 + V) ≤ Real.sqrt ((μ' - y) ^ 2 + V') :=
    Real.sqrt_le_sqrt (by linarith)
  set u := μ - y with hu_def
  set u' := μ' - y with hu'_def
  have hu : u ≤ u' := by linarith
  set A := Real.sqrt (u ^ 2 + V) with hA_def
  set A' := Real.sqrt (u' ^ 2 + V) with hA'_def
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hA'0 : 0 ≤ A' := Real.sqrt_nonneg _
  have hAs : A ^ 2 = u ^ 2 + V := Real.sq_sqrt (by positivity)
  have hA's : A' ^ 2 = u' ^ 2 + V := Real.sq_sqrt (by positivity)
  have hAu : -u ≤ A := (neg_le_abs u).trans (Real.abs_le_sqrt (by linarith))
  have hA'u : -u' ≤ A' := (neg_le_abs u').trans (Real.abs_le_sqrt (by linarith))
  have h2 : u + A ≤ u' + A' := by
    by_cases hs : A + A' = 0
    · have : A = 0 := by linarith
      have : A' = 0 := by linarith
      linarith
    · have hpos : 0 < A + A' := lt_of_le_of_ne (by positivity) (Ne.symm hs)
      have hmul := mul_le_mul_of_nonneg_left (show -(u + u') ≤ A + A' by linarith)
        (show 0 ≤ u' - u by linarith)
      have key : (A - A') * (A + A') ≤ (u' - u) * (A + A') := by nlinarith
      have := le_of_mul_le_mul_right key hpos
      linarith
  linarith

theorem ofReal_tsub_max (p z : ENNReal) (hp : p ≠ ⊤) (hz : z ≠ ⊤) (θ : ℝ) (hθ : 0 ≤ θ) :
    (p + z) - ENNReal.ofReal θ = ENNReal.ofReal (max 0 (z.toReal - (θ - p.toReal))) := by
  have hpz : p + z = ENNReal.ofReal (p.toReal + z.toReal) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hp, ENNReal.ofReal_toReal hz]
  rw [hpz, ← ENNReal.ofReal_sub _ hθ, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_right zero_le]
  congr 1
  ring

/-- Scarf's bound for a law average, from a mean bound and a second-moment (variance) bound. -/
theorem scarf_law {γ : Type} [Fintype γ] (w : γ → ENNReal) (hw : ∑ c, w c = 1) (T : ℕ)
    (Z : List γ → ENNReal) (hZ : ∀ W, Z W ≠ ⊤) (p : ENNReal) (hp : p ≠ ⊤)
    (θ μ V : ℝ) (hθ : 0 ≤ θ) (hμ : 0 ≤ μ) (hV : 0 ≤ V)
    (hmean : lawAvg w T Z ≤ ENNReal.ofReal μ)
    (hsq : lawAvg w T (fun W => Z W ^ 2) ≤ (lawAvg w T Z) ^ 2 + ENNReal.ofReal V) :
    lawAvg w T (fun W => (p + Z W) - ENNReal.ofReal θ) ≤
      ENNReal.ofReal (scarf (θ - p.toReal) μ V) := by
  set y : ℝ := θ - p.toReal with hy
  set e := lawAvg w T Z with he_def
  set e2 := lawAvg w T (fun W => Z W ^ 2) with he2_def
  set E1 := lawAvg w T (fun W => (p + Z W) - ENNReal.ofReal θ) with hE1_def
  have he : e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmean
  have he2 : e2 ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hsq
  have hE1 : E1 ≠ ⊤ := by
    have h : E1 ≤ lawAvg w T (fun W => p + Z W) := lawAvg_mono w T fun W => tsub_le_self
    rw [lawAvg_add, lawAvg_const w hw] at h
    exact ne_top_of_le_ne_top (by finiteness) h
  have hpt : ∀ W, (p + Z W) - ENNReal.ofReal θ = ENNReal.ofReal (max 0 ((Z W).toReal - y)) :=
    fun W => ofReal_tsub_max p (Z W) hp (hZ W) θ hθ
  have hzW : ∀ W, Z W = ENNReal.ofReal (Z W).toReal := fun W => (ENNReal.ofReal_toReal (hZ W)).symm
  set μ0 := e.toReal with hμ0_def
  set M2 := e2.toReal with hM2_def
  have hμ0 : μ0 ≤ μ := ENNReal.toReal_le_of_le_ofReal hμ hmean
  have hμ00 : 0 ≤ μ0 := ENNReal.toReal_nonneg
  have hM2 : M2 ≤ μ0 ^ 2 + V := by
    have h := ENNReal.toReal_mono (by finiteness) hsq
    rwa [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hV] at h
  -- the quadratic stop-loss majorant at a free slope `s`
  have hquad : ∀ s : ℝ, 0 < s → 4 * s * E1.toReal ≤ (μ0 - y + s) ^ 2 + V := by
    intro s hs
    by_cases hc : s ≤ y
    · set c := y - s with hc_def
      have hc0 : 0 ≤ c := by linarith
      have hpoint : ∀ W, ENNReal.ofReal (4 * s) * ((p + Z W) - ENNReal.ofReal θ) +
          ENNReal.ofReal (2 * c) * Z W ≤ Z W ^ 2 + ENNReal.ofReal (c ^ 2) := by
        intro W
        rw [hpt W, hzW W, ENNReal.toReal_ofReal ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        set z := (Z W).toReal
        have hz : 0 ≤ z := ENNReal.toReal_nonneg
        rcases le_total z y with hzy | hzy
        · rw [max_eq_left (by linarith)]
          nlinarith [sq_nonneg (z - c)]
        · rw [max_eq_right (by linarith)]
          nlinarith [sq_nonneg (z - y - s)]
      have hint := lawAvg_mono w T hpoint
      rw [lawAvg_add, lawAvg_mul_left, lawAvg_mul_left, lawAvg_add, lawAvg_const w hw] at hint
      have h := ENNReal.toReal_mono (by finiteness) hint
      rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_add he2 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at h
      have : μ0 - y + s = μ0 - c := by rw [hc_def]; ring
      rw [this]
      nlinarith
    · set d := s - y with hd_def
      have hd0 : 0 ≤ d := by linarith
      have hpoint : ∀ W, ENNReal.ofReal (4 * s) * ((p + Z W) - ENNReal.ofReal θ) ≤
          Z W ^ 2 + ENNReal.ofReal (2 * d) * Z W + ENNReal.ofReal (d ^ 2) := by
        intro W
        rw [hpt W, hzW W, ENNReal.toReal_ofReal ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        set z := (Z W).toReal
        have hz : 0 ≤ z := ENNReal.toReal_nonneg
        rcases le_total z y with hzy | hzy
        · rw [max_eq_left (by linarith)]
          nlinarith
        · rw [max_eq_right (by linarith)]
          nlinarith [sq_nonneg (z - y - s)]
      have hint := lawAvg_mono w T hpoint
      rw [lawAvg_mul_left, lawAvg_add, lawAvg_add, lawAvg_mul_left, lawAvg_const w hw] at hint
      have h := ENNReal.toReal_mono (by finiteness) hint
      rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
        ENNReal.toReal_add he2 (by finiteness), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_ofReal (by positivity)] at h
      have : μ0 - y + s = μ0 + d := by rw [hd_def]; ring
      rw [this]
      nlinarith
  -- optimise the slope
  have hE1r : E1.toReal ≤ scarf y μ0 V := by
    set s0 := Real.sqrt ((μ0 - y) ^ 2 + V) with hs0_def
    have hs00 : 0 ≤ s0 := Real.sqrt_nonneg _
    have hs0sq : s0 ^ 2 = (μ0 - y) ^ 2 + V := Real.sq_sqrt (by positivity)
    unfold scarf
    rw [← hs0_def]
    rcases eq_or_lt_of_le hs00 with h0 | hpos
    · -- degenerate law: `V = 0` and `μ0 = y`
      have hV0 : V = 0 := by nlinarith [sq_nonneg (μ0 - y)]
      have hμy : μ0 - y = 0 := by nlinarith [sq_nonneg (μ0 - y)]
      rw [← h0, hμy]
      norm_num
      by_contra hneg
      push Not at hneg
      have hq := hquad (E1.toReal) hneg
      rw [hμy, hV0] at hq
      nlinarith
    · have hq := hquad s0 hpos
      have : (μ0 - y + s0) ^ 2 + V = 2 * s0 * (s0 + (μ0 - y)) := by nlinarith
      rw [this] at hq
      nlinarith
  calc E1 = ENNReal.ofReal E1.toReal := (ENNReal.ofReal_toReal hE1).symm
    _ ≤ ENNReal.ofReal (scarf y μ0 V) := ENNReal.ofReal_le_ofReal hE1r
    _ ≤ ENNReal.ofReal (scarf y μ V) := ENNReal.ofReal_le_ofReal (scarf_mono hμ0 le_rfl hV)

#print axioms scarf_law
end Scarf

/-! ### The pointwise split (RC_SPEC I1 + I2 / L1) -/
section Pointwise
variable {α : Type} [Fintype α] [DecidableEq α]

/-- `(∑ xᵢ - θ)⁺` is paid by the clipped background, one large short-row bucket on top of the
clipped others, the excess of every large bucket when another bucket is large, and long rows. -/
theorem split_finset (x : α → ENNReal) (short : α → Prop) [DecidablePred short] (c θ : ENNReal) :
    (∑ i, x i) - θ ≤
      ((∑ i, min (x i) c) - θ) +
      ∑ j, (if short j ∧ c < x j then (x j + ∑ i ∈ univ.erase j, min (x i) c) - θ else 0) +
      ∑ j, (x j - c) * ∑ i ∈ univ.erase j, (if c < x i then (1 : ENNReal) else 0) +
      ∑ j, (if short j then 0 else x j) := by
  classical
  set vv : α → ENNReal := fun i => if short i then x i else 0 with hvv
  set tt : α → ENNReal := fun i => if short i then 0 else x i with htt
  set Y : ENNReal := ∑ i, min (x i) c with hY
  set K1 : ENNReal := ∑ j, (if short j ∧ c < x j then (x j + ∑ i ∈ univ.erase j, min (x i) c) - θ else 0)
  set K2 : ENNReal := ∑ j, (x j - c) * ∑ i ∈ univ.erase j, (if c < x i then (1 : ENNReal) else 0)
  have hsplit : (∑ i, x i) = (∑ i, vv i) + ∑ i, tt i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hvv, htt]
    split_ifs <;> simp
  have hstep : (∑ i, x i) - θ ≤ ((∑ i, vv i) - θ) + ∑ i, tt i := by
    rw [hsplit]
    exact tsub_le_iff_right.mpr (by
      calc (∑ i, vv i) + ∑ i, tt i ≤ (((∑ i, vv i) - θ) + θ) + ∑ i, tt i :=
            add_le_add le_tsub_add le_rfl
        _ = _ := by ring)
  have hsmall : ∀ i, ¬(short i ∧ c < x i) → vv i ≤ min (x i) c := by
    intro i hi
    simp only [hvv]
    split_ifs with hs
    · have : x i ≤ c := not_lt.mp (fun h => hi ⟨hs, h⟩)
      exact le_min le_rfl this
    · exact zero_le
  have hcore : (∑ i, vv i) - θ ≤ (Y - θ) + K1 + K2 := by
    by_cases hnone : ∀ j, ¬(short j ∧ c < x j)
    · have : (∑ i, vv i) ≤ Y := Finset.sum_le_sum fun i _ => hsmall i (hnone i)
      calc (∑ i, vv i) - θ ≤ Y - θ := tsub_le_tsub_right this θ
        _ ≤ (Y - θ) + K1 + K2 := by rw [add_assoc]; exact le_self_add
    · push Not at hnone
      obtain ⟨j0, hj0⟩ := hnone
      by_cases hone : ∀ i ∈ univ.erase j0, ¬(short i ∧ c < x i)
      · have hv0 : vv j0 = x j0 := by simp only [hvv, if_pos hj0.1]
        have hle : (∑ i, vv i) ≤ x j0 + ∑ i ∈ univ.erase j0, min (x i) c := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), hv0]
          exact add_le_add le_rfl (Finset.sum_le_sum fun i hi => hsmall i (hone i hi))
        have hterm : (x j0 + ∑ i ∈ univ.erase j0, min (x i) c) - θ ≤ K1 := by
          have := Finset.single_le_sum (f := fun j => if short j ∧ c < x j then
            (x j + ∑ i ∈ univ.erase j, min (x i) c) - θ else 0) (fun j _ => zero_le) (Finset.mem_univ j0)
          simpa only [if_pos hj0] using this
        calc (∑ i, vv i) - θ ≤ (x j0 + ∑ i ∈ univ.erase j0, min (x i) c) - θ := tsub_le_tsub_right hle θ
          _ ≤ K1 := hterm
          _ ≤ (Y - θ) + K1 + K2 := by
            rw [add_assoc]; exact le_add_left (le_self_add)
      · push Not at hone
        obtain ⟨j1, hj1m, hj1⟩ := hone
        have hj10 : j1 ≠ j0 := Finset.ne_of_mem_erase hj1m
        have hper : ∀ i, vv i ≤ min (x i) c +
            (x i - c) * ∑ k ∈ univ.erase i, (if c < x k then (1 : ENNReal) else 0) := by
          intro i
          by_cases hbig : short i ∧ c < x i
          · have hvi : vv i = x i := by simp only [hvv, if_pos hbig.1]
            have hmin : min (x i) c = c := min_eq_right hbig.2.le
            have hone' : (1 : ENNReal) ≤ ∑ k ∈ univ.erase i, (if c < x k then (1 : ENNReal) else 0) := by
              by_cases hi0 : i = j0
              · have hm : j1 ∈ univ.erase i := Finset.mem_erase.mpr ⟨by rw [hi0]; exact hj10, mem_univ _⟩
                have := Finset.single_le_sum (f := fun k => if c < x k then (1 : ENNReal) else 0)
                  (fun k _ => zero_le) hm
                simpa only [if_pos hj1.2] using this
              · have hm : j0 ∈ univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hi0, mem_univ _⟩
                have := Finset.single_le_sum (f := fun k => if c < x k then (1 : ENNReal) else 0)
                  (fun k _ => zero_le) hm
                simpa only [if_pos hj0.2] using this
            rw [hvi, hmin]
            calc x i = c + (x i - c) := (add_tsub_cancel_of_le hbig.2.le).symm
              _ ≤ c + (x i - c) * ∑ k ∈ univ.erase i, (if c < x k then (1 : ENNReal) else 0) := by
                gcongr
                exact le_mul_of_one_le_right' hone'
          · exact (hsmall i hbig).trans le_self_add
        have hle : (∑ i, vv i) ≤ Y + K2 := by
          rw [hY, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun i _ => hper i
        calc (∑ i, vv i) - θ ≤ (Y + K2) - θ := tsub_le_tsub_right hle θ
          _ ≤ (Y - θ) + K2 := by
            apply tsub_le_iff_right.mpr
            calc Y + K2 ≤ ((Y - θ) + θ) + K2 := add_le_add le_tsub_add le_rfl
              _ = _ := by ring
          _ ≤ (Y - θ) + K1 + K2 := add_le_add (le_self_add) le_rfl
  calc (∑ i, x i) - θ ≤ ((∑ i, vv i) - θ) + ∑ i, tt i := hstep
    _ ≤ ((Y - θ) + K1 + K2) + ∑ i, tt i := add_le_add hcore le_rfl

#print axioms split_finset
end Pointwise

/-! ### Assembly (RC_SPEC L5 + L6) -/
section Assembly
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] (v : β → ENNReal)

omit [Fintype α] [DecidableEq α] in
theorem lawAvg_mono_length (r : ℕ) {f g : List β → ENNReal}
    (h : ∀ L, L.length = r → f L ≤ g L) : lawAvg v r f ≤ lawAvg v r g := by
  induction r generalizing f g with
  | zero => exact h [] rfl
  | succ r ih =>
    rw [lawAvg_succ, lawAvg_succ]
    exact Finset.sum_le_sum fun b _ =>
      mul_le_mul' le_rfl (ih fun L hL => h (b :: L) (by simp [hL]))

omit [Fintype α] [DecidableEq α] in
theorem lawAvg_zero_fun (r : ℕ) : lawAvg v r (fun _ => (0 : ENNReal)) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [lawAvg_succ, ih]

theorem law_marked_sum' [Nonempty α] (hv : ∑ b, v b = 1) (T : ℕ) (f : List β → ENNReal) :
    lawAvg (marked (α := α) v) T (fun W => ∑ i : α, f (atIndex i W)) =
      (Fintype.card α : ENNReal) * coordAverage (Fintype.card α : ENNReal)⁻¹ v T f := by
  rw [lawAvg_sum]
  simp only [law_marked_atIndex v hv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rfl

theorem exp_majorant (x θ a : ℝ) (ha : 0 < a) :
    max 0 (x - θ) ≤ (3 / (8 * a)) * (Real.exp (-a * θ) * Real.exp (a * x)) := by
  have he := Real.exp_one_gt_d9
  set E := Real.exp (-a * θ) * Real.exp (a * x) with hE
  have hEpos : 0 < E := by positivity
  have hu := Real.add_one_le_exp (a * (x - θ) - 1)
  have h1 : Real.exp (a * (x - θ) - 1) = E / Real.exp 1 := by
    rw [Real.exp_sub, show a * (x - θ) = -a * θ + a * x by ring, Real.exp_add]
  have h2 : a * (x - θ) ≤ E / Real.exp 1 := by linarith
  have h3 : E / Real.exp 1 ≤ (3 / 8) * E := by
    rw [div_le_iff₀ (Real.exp_pos 1)]
    nlinarith
  apply max_le (by positivity)
  have h4 : a * (x - θ) ≤ a * ((3 / (8 * a)) * E) := by
    have : a * ((3 / (8 * a)) * E) = (3 / 8) * E := by field_simp
    rw [this]
    linarith
  exact le_of_mul_le_mul_left h4 ha

/-- The clipped background (RC_SPEC I3 + I4): Chernoff bound through bucket product dependence. -/
theorem clipped_excess [Nonempty α] (hv : ∑ b, v b = 1) (T : ℕ) (Y : List β → ENNReal)
    (hY : ∀ L, Y L ≠ ⊤) (hmono : ∀ L b R, Y (L ++ R) ≤ Y (L ++ b :: R))
    (θ a B : ℝ) (hθ : 0 ≤ θ) (ha : 0 < a) (hB : 0 ≤ B)
    (hmgf : (∑ _i : α, coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => ENNReal.ofReal (Real.exp (a * (Y L).toReal)) - 1)) ≤ ENNReal.ofReal B) :
    lawAvg (marked (α := α) v) T (fun W => (∑ i, Y (atIndex i W)) - ENNReal.ofReal θ) ≤
      ENNReal.ofReal ((3 / (8 * a)) * Real.exp (B - a * θ)) := by
  have hexp := law_marked_exp_sum_general v hv T (fun _ L => Y L) a B ha.le hB
    (fun _ L => hY L) (fun _ L b R => hmono L b R) hmgf
  set k := ENNReal.ofReal ((3 / (8 * a)) * Real.exp (-a * θ)) with hk
  have hpoint : ∀ W : List (α × β), (∑ i : α, Y (atIndex i W)) - ENNReal.ofReal θ ≤
      k * ENNReal.ofReal (Real.exp (a * (∑ i : α, Y (atIndex i W)).toReal)) := by
    intro W
    set s := ∑ i : α, Y (atIndex i W)
    have hs : s ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hY _
    have hrw : s - ENNReal.ofReal θ = ENNReal.ofReal (max 0 (s.toReal - θ)) := by
      rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_right zero_le, ENNReal.ofReal_sub _ hθ,
        ENNReal.ofReal_toReal hs]
    rw [hrw, hk, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := exp_majorant s.toReal θ a ha
    linarith
  calc lawAvg (marked (α := α) v) T (fun W => (∑ i, Y (atIndex i W)) - ENNReal.ofReal θ)
      ≤ lawAvg (marked (α := α) v) T
          (fun W => k * ENNReal.ofReal (Real.exp (a * (∑ i, Y (atIndex i W)).toReal))) :=
        lawAvg_mono _ _ hpoint
    _ = k * lawAvg (marked (α := α) v) T
          (fun W => ENNReal.ofReal (Real.exp (a * (∑ i, Y (atIndex i W)).toReal))) := lawAvg_mul_left _ _ _ _
    _ ≤ k * ENNReal.ofReal (Real.exp B) := mul_le_mul' le_rfl hexp
    _ = ENNReal.ofReal ((3 / (8 * a)) * Real.exp (B - a * θ)) := by
      rw [hk, ← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
      congr 3
      ring

/-- One large bucket on a short row (RC_SPEC I5-I7): exact conditional law and the Scarf bound. -/
theorem large_index_bound [Nonempty α] (hv : ∑ b, v b = 1) (hcard : 1 < Fintype.card α) (j : α)
    (T rows : ℕ) (pb : List β → ENNReal) (hpb : ∀ L, pb L ≠ ⊤)
    (hmono : ∀ L b R, pb (L ++ R) ≤ pb (L ++ b :: R))
    (c0 θ m vv : ℝ) (hθ : 0 ≤ θ) (hm0 : 0 ≤ m) (hvv0 : 0 ≤ vv)
    (hempty : pb [] ≤ ENNReal.ofReal c0)
    (hmean : ∀ r, 1 ≤ r → r ≤ rows →
      ((Fintype.card α - 1 : ℕ) : ENNReal) * coordAverage ((Fintype.card α - 1 : ℕ) : ENNReal)⁻¹ v (T - r)
        (fun L => min (pb L) (ENNReal.ofReal c0)) ≤ ENNReal.ofReal m)
    (hsecond : ∀ r, 1 ≤ r → r ≤ rows →
      ((Fintype.card α - 1 : ℕ) : ENNReal) * coordAverage ((Fintype.card α - 1 : ℕ) : ENNReal)⁻¹ v (T - r)
        (fun L => min (pb L) (ENNReal.ofReal c0) ^ 2) ≤ ENNReal.ofReal vv) :
    lawAvg (marked (α := α) v) T (fun W =>
      if (atIndex j W).length ≤ rows ∧ ENNReal.ofReal c0 < pb (atIndex j W) then
        (pb (atIndex j W) + ∑ i ∈ univ.erase j, min (pb (atIndex i W)) (ENNReal.ofReal c0)) -
          ENNReal.ofReal θ
      else 0) ≤
    coordAverage (Fintype.card α : ENNReal)⁻¹ v T (fun L =>
      if L.length ≤ rows ∧ ENNReal.ofReal c0 < pb L then
        ENNReal.ofReal (scarf (θ - (pb L).toReal) m vv) else 0) := by
  set c := ENNReal.ofReal c0 with hc
  set Y : List β → ENNReal := fun L => min (pb L) c with hYdef
  have hYtop : ∀ L, Y L ≠ ⊤ := fun L => ne_top_of_le_ne_top (hpb L) (min_le_left _ _)
  have hYcons : ∀ a L, Y L ≤ Y (a :: L) := fun a L =>
    min_le_min (by simpa using hmono [] a L) le_rfl
  set F : List β → List ({i // i ≠ j} × β) → ENNReal := fun L R =>
    if L.length ≤ rows ∧ c < pb L then (pb L + ∑ i' : {i // i ≠ j}, Y (atIndex i' R)) - ENNReal.ofReal θ
    else 0 with hF
  have hrw : (fun W : List (α × β) =>
      if (atIndex j W).length ≤ rows ∧ c < pb (atIndex j W) then
        (pb (atIndex j W) + ∑ i ∈ univ.erase j, min (pb (atIndex i W)) c) - ENNReal.ofReal θ
      else 0) = fun W => F (atIndex j W) (eraseIdx j W) := by
    funext W
    have hs : ∑ i ∈ univ.erase j, min (pb (atIndex i W)) c =
        ∑ i' : {i // i ≠ j}, Y (atIndex i' (eraseIdx j W)) := by
      rw [Finset.sum_subtype (univ.erase j) (p := fun a => a ≠ j) (fun x => by simp)]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [atIndex_eraseIdx]
    simp only [hF, hs]
  rw [hrw, law_marked_split v hv j hcard T F]
  unfold coordAverage
  apply binomialAverage_mono
  intro r
  apply lawAvg_mono_length v r
  intro L hL
  simp only [hF]
  split_ifs with hbig
  · have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · exfalso
        rw [h0, List.length_eq_zero_iff] at hL
        rw [hL] at hbig
        exact absurd hempty (not_le.mpr hbig.2)
      · exact h0
    have hrr : r ≤ rows := hL ▸ hbig.1
    obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card hcard j
    haveI : Nonempty {i // i ≠ j} := ⟨⟨k, hk⟩⟩
    have hcardj : (Fintype.card {i // i ≠ j} : ENNReal) = ((Fintype.card α - 1 : ℕ) : ENNReal) := by
      rw [card_ne_subtype]
    have hmeanL : lawAvg (marked (α := {i // i ≠ j}) v) (T - r)
        (fun R => ∑ i' : {i // i ≠ j}, Y (atIndex i' R)) ≤ ENNReal.ofReal m := by
      rw [law_marked_sum' v hv, hcardj]
      exact hmean r hr1 hrr
    have hsqL : lawAvg (marked (α := {i // i ≠ j}) v) (T - r)
        (fun R => (∑ i' : {i // i ≠ j}, Y (atIndex i' R)) ^ 2) ≤
        (lawAvg (marked (α := {i // i ≠ j}) v) (T - r)
          (fun R => ∑ i' : {i // i ≠ j}, Y (atIndex i' R))) ^ 2 + ENNReal.ofReal vv := by
      have hcross : ∀ first second : {i // i ≠ j}, first ≠ second →
          lawAvg (marked (α := {i // i ≠ j}) v) (T - r)
            (fun R => Y (atIndex first R) * Y (atIndex second R)) ≤
          lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (fun R => Y (atIndex first R)) *
            lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (fun R => Y (atIndex second R)) :=
        fun first second hne => law_marked_negative_correlation v hv first second hne (T - r) Y Y
          hYcons hYcons
      have h := lawAvg_sum_square_le (marked (α := {i // i ≠ j}) v) (T - r)
        (fun i' R => Y (atIndex i' R)) hcross
      have hsq : ∑ i' : {i // i ≠ j}, lawAvg (marked (α := {i // i ≠ j}) v) (T - r)
          (fun R => Y (atIndex i' R) ^ 2) ≤ ENNReal.ofReal vv := by
        have := (lawAvg_sum (marked (α := {i // i ≠ j}) v) (T - r) univ
          (fun i' R => Y (atIndex i' R) ^ 2)).symm.trans
          (law_marked_sum' v hv (T - r) (fun L => Y L ^ 2))
        rw [this, hcardj]
        exact hsecond r hr1 hrr
      calc _ ≤ _ := h
        _ ≤ (lawAvg (marked (α := {i // i ≠ j}) v) (T - r)
              (fun R => ∑ i' : {i // i ≠ j}, Y (atIndex i' R))) ^ 2 + ENNReal.ofReal vv := by
          rw [← lawAvg_sum]
          exact add_le_add le_rfl hsq
    exact scarf_law (marked (α := {i // i ≠ j}) v) (marked_sum_one v hv) (T - r)
      (fun R => ∑ i' : {i // i ≠ j}, Y (atIndex i' R))
      (fun R => ENNReal.sum_ne_top.mpr fun i' _ => hYtop _) (pb L) (hpb L) θ m vv hθ hm0 hvv0
      hmeanL hsqL
  · exact (lawAvg_zero_fun _ _).le

/-- Route C excess bound for a marked-index bank: the generic statement (RC_SPEC TOTAL). -/
theorem excess_route_c [Nonempty α] (hv : ∑ b, v b = 1) (hcard : 1 < Fintype.card α)
    (T rows : ℕ) (pb : List β → ENNReal) (hpb : ∀ L, pb L ≠ ⊤)
    (hmono : ∀ L b R, pb (L ++ R) ≤ pb (L ++ b :: R))
    (c0 θ a B m vv K1 O Λ tF : ℝ) (hθ : 0 ≤ θ) (ha : 0 < a) (hB : 0 ≤ B) (hm0 : 0 ≤ m)
    (hvv0 : 0 ≤ vv) (hK10 : 0 ≤ K1) (hO0 : 0 ≤ O) (hΛ0 : 0 ≤ Λ) (htF0 : 0 ≤ tF)
    (hempty : pb [] ≤ ENNReal.ofReal c0)
    (hmgf : (∑ _i : α, coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => ENNReal.ofReal (Real.exp (a * (min (pb L) (ENNReal.ofReal c0)).toReal)) - 1)) ≤
        ENNReal.ofReal B)
    (hmean : ∀ r, 1 ≤ r → r ≤ rows →
      ((Fintype.card α - 1 : ℕ) : ENNReal) * coordAverage ((Fintype.card α - 1 : ℕ) : ENNReal)⁻¹ v (T - r)
        (fun L => min (pb L) (ENNReal.ofReal c0)) ≤ ENNReal.ofReal m)
    (hsecond : ∀ r, 1 ≤ r → r ≤ rows →
      ((Fintype.card α - 1 : ℕ) : ENNReal) * coordAverage ((Fintype.card α - 1 : ℕ) : ENNReal)⁻¹ v (T - r)
        (fun L => min (pb L) (ENNReal.ofReal c0) ^ 2) ≤ ENNReal.ofReal vv)
    (hK1 : (Fintype.card α : ENNReal) * coordAverage (Fintype.card α : ENNReal)⁻¹ v T (fun L =>
      if L.length ≤ rows ∧ ENNReal.ofReal c0 < pb L then
        ENNReal.ofReal (scarf (θ - (pb L).toReal) m vv) else 0) ≤ ENNReal.ofReal K1)
    (hover : (Fintype.card α : ENNReal) * coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => pb L - ENNReal.ofReal c0) ≤ ENNReal.ofReal O)
    (hcount : (Fintype.card α : ENNReal) * coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => if ENNReal.ofReal c0 < pb L then 1 else 0) ≤ ENNReal.ofReal Λ)
    (htail : (Fintype.card α : ENNReal) * coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => if rows < L.length then pb L else 0) ≤ ENNReal.ofReal tF) :
    lawAvg (marked (α := α) v) T (fun W => (∑ i, pb (atIndex i W)) - ENNReal.ofReal θ) ≤
      ENNReal.ofReal ((3 / (8 * a)) * Real.exp (B - a * θ) + K1 + O * Λ + tF) := by
  set c := ENNReal.ofReal c0 with hc
  set n := (Fintype.card α : ENNReal) with hn
  have hpoint : ∀ W : List (α × β), (∑ i, pb (atIndex i W)) - ENNReal.ofReal θ ≤
      ((∑ i, min (pb (atIndex i W)) c) - ENNReal.ofReal θ) +
      ∑ j, (if (atIndex j W).length ≤ rows ∧ c < pb (atIndex j W) then
        (pb (atIndex j W) + ∑ i ∈ univ.erase j, min (pb (atIndex i W)) c) - ENNReal.ofReal θ else 0) +
      ∑ j, (pb (atIndex j W) - c) * ∑ i ∈ univ.erase j, (if c < pb (atIndex i W) then (1 : ENNReal) else 0) +
      ∑ j, (if rows < (atIndex j W).length then pb (atIndex j W) else 0) := by
    intro W
    have h := split_finset (fun i => pb (atIndex i W)) (fun i => (atIndex i W).length ≤ rows) c
      (ENNReal.ofReal θ)
    have ht : ∀ j, (if (atIndex j W).length ≤ rows then 0 else pb (atIndex j W)) =
        (if rows < (atIndex j W).length then pb (atIndex j W) else 0) := by
      intro j
      split_ifs with h1 h2 h2 <;> first | rfl | omega
    simpa only [ht] using h
  refine (lawAvg_mono _ _ hpoint).trans ?_
  rw [lawAvg_add, lawAvg_add, lawAvg_add, lawAvg_sum, lawAvg_sum, lawAvg_sum]
  -- the clipped background
  have h0 := clipped_excess v hv T (fun L => min (pb L) c)
    (fun L => ne_top_of_le_ne_top (hpb L) (min_le_left _ _))
    (fun L b R => min_le_min (hmono L b R) le_rfl) θ a B hθ ha hB hmgf
  -- one large bucket
  have h1 : (∑ j, lawAvg (marked (α := α) v) T (fun W =>
      if (atIndex j W).length ≤ rows ∧ c < pb (atIndex j W) then
        (pb (atIndex j W) + ∑ i ∈ univ.erase j, min (pb (atIndex i W)) c) - ENNReal.ofReal θ else 0)) ≤
      ENNReal.ofReal K1 := by
    refine (Finset.sum_le_sum fun j _ =>
      large_index_bound v hv hcard j T rows pb hpb hmono c0 θ m vv hθ hm0 hvv0 hempty hmean hsecond).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact hK1
  -- two large buckets
  have hfcons : ∀ a L, pb L - c ≤ pb (a :: L) - c := fun a L =>
    tsub_le_tsub_right (by simpa using hmono [] a L) c
  have hgcons : ∀ a L, (if c < pb L then (1 : ENNReal) else 0) ≤ (if c < pb (a :: L) then 1 else 0) := by
    intro a L
    by_cases h : c < pb L
    · rw [if_pos h, if_pos (lt_of_lt_of_le h (by simpa using hmono [] a L))]
    · rw [if_neg h]; exact zero_le
  have h2 : (∑ j, lawAvg (marked (α := α) v) T (fun W =>
      (pb (atIndex j W) - c) * ∑ i ∈ univ.erase j, (if c < pb (atIndex i W) then (1 : ENNReal) else 0))) ≤
      ENNReal.ofReal O * ENNReal.ofReal Λ := by
    have hj : ∀ j, lawAvg (marked (α := α) v) T (fun W =>
        (pb (atIndex j W) - c) * ∑ i ∈ univ.erase j, (if c < pb (atIndex i W) then (1 : ENNReal) else 0)) ≤
        ∑ _i : α, coordAverage n⁻¹ v T (fun L => pb L - c) *
          coordAverage n⁻¹ v T (fun L => if c < pb L then 1 else 0) := by
      intro j
      simp_rw [Finset.mul_sum]
      rw [lawAvg_sum]
      refine (Finset.sum_le_sum fun i hi => ?_).trans
        (Finset.sum_le_sum_of_subset (Finset.erase_subset j univ))
      have hne : j ≠ i := Ne.symm (Finset.ne_of_mem_erase hi)
      refine (law_marked_negative_correlation v hv j i hne T (fun L => pb L - c)
        (fun L => if c < pb L then 1 else 0) hfcons hgcons).trans_eq ?_
      rw [law_marked_atIndex v hv j T (fun L => pb L - c),
        law_marked_atIndex v hv i T (fun L => if c < pb L then 1 else 0)]
      rfl
    calc _ ≤ ∑ _j : α, ∑ _i : α, coordAverage n⁻¹ v T (fun L => pb L - c) *
          coordAverage n⁻¹ v T (fun L => if c < pb L then 1 else 0) := Finset.sum_le_sum fun j _ => hj j
      _ = (n * coordAverage n⁻¹ v T (fun L => pb L - c)) *
          (n * coordAverage n⁻¹ v T (fun L => if c < pb L then 1 else 0)) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
        ring
      _ ≤ ENNReal.ofReal O * ENNReal.ofReal Λ := mul_le_mul' hover hcount
  -- long rows
  have h3 : (∑ j, lawAvg (marked (α := α) v) T (fun W =>
      if rows < (atIndex j W).length then pb (atIndex j W) else 0)) ≤ ENNReal.ofReal tF := by
    have := (lawAvg_sum (marked (α := α) v) T univ (fun j W =>
      if rows < (atIndex j W).length then pb (atIndex j W) else 0)).symm.trans
      (law_marked_sum' v hv T (fun L => if rows < L.length then pb L else 0))
    rw [this]
    exact htail
  calc _ ≤ ENNReal.ofReal ((3 / (8 * a)) * Real.exp (B - a * θ)) + ENNReal.ofReal K1 +
        ENNReal.ofReal O * ENNReal.ofReal Λ + ENNReal.ofReal tF :=
      add_le_add (add_le_add (add_le_add h0 h1) h2) h3
    _ = _ := by
      rw [← ENNReal.ofReal_mul hO0, ← ENNReal.ofReal_add (by positivity) hK10,
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) htF0]

#print axioms excess_route_c
end Assembly

end ClaudeWCT.Numerics.RouteC

/-! Route C fee vectors (R6 campaign, stream RC, RC_SPEC L7).

A fee vector is a list of runs `(lo, hi, fee)` over the 7210 forest bins of `SharedFees`. A run is
sound for a cost `f` when `f x ≤ x * fee / feeScale` for every price `x` in the run's bin range
`[lowerQ g lo, upperQ g hi]` (bin `j` holds prices `g/2^66 * coverage` in
`[g/2^66 * (100/101)^13 * (101/100)^j, g/2^66 * (101/100)^j]`). Each `*Ok` below is a decidable
run check, and `*Ok_sound` proves it sound. The six route-C costs are the clipped mean, clipped
square, large-bucket count, excess over the clip, clipped exponential, and the Scarf payment. -/

namespace ClaudeWCT.Numerics.RouteCFees
open ClaudeWCT.Numerics.RouteC (scarf)

/-- Fee scale: fees are stored as `feeScale * (cost / price)`. -/
def feeScale : ℕ := 2 ^ 64

/-- Route C parameters: gate, clip `c0`, Chernoff slope `a`, threshold `θ`, certified conditional
mean `m`, variance `vv`, and `sv ≥ √vv`. -/
structure Par where
  g : ℕ
  c0 : ℚ
  a : ℚ
  θ : ℚ
  m : ℚ
  vv : ℚ
  sv : ℚ

/-- Upper price of bin `j` at gate `g`. -/
def upperQ (g j : ℕ) : ℚ := mkRat (g * 101 ^ j) (2 ^ 66 * 100 ^ j)
/-- Lower price of bin `j` at gate `g` (13 roundings below the upper price). -/
def lowerQ (g j : ℕ) : ℚ := mkRat (g * 101 ^ j * 100 ^ 13) (2 ^ 66 * 100 ^ j * 101 ^ 13)

/-! ### Run checks -/

def meanOk (P : Par) (L _U : ℚ) (fee : ℕ) : Bool :=
  decide ((feeScale : ℚ) ≤ fee) || (decide (P.c0 ≤ L) && decide ((feeScale : ℚ) * P.c0 ≤ fee * L))

def secOk (P : Par) (L U : ℚ) (fee : ℕ) : Bool :=
  decide ((feeScale : ℚ) * P.c0 ≤ fee) || (decide (U ≤ P.c0) && decide ((feeScale : ℚ) * U ≤ fee)) ||
    (decide (P.c0 ≤ L) && decide ((feeScale : ℚ) * (P.c0 * P.c0) ≤ fee * L))

def countOk (P : Par) (L U : ℚ) (fee : ℕ) : Bool :=
  decide (U ≤ P.c0) || decide ((feeScale : ℚ) ≤ fee * P.c0) || decide ((feeScale : ℚ) ≤ fee * L)

def overOk (P : Par) (_L U : ℚ) (fee : ℕ) : Bool :=
  decide (U ≤ P.c0) || decide ((feeScale : ℚ) ≤ fee) || (decide (0 < U) && decide ((feeScale : ℚ) * (U - P.c0) ≤ fee * U))

/-- `expUpper` argument for `a * x` (`SharedFees.scale` units, rounded up). -/
def expArg (a x : ℚ) : ℕ := ⌈a * x * (ClaudeWCT.Numerics.SharedFees.scale : ℚ)⌉.toNat

/-- Upper bound of `exp (a * x) - 1` as a rational. -/
def expm1Up (a x : ℚ) : ℚ :=
  ((ClaudeWCT.Numerics.SharedFees.expUpper (expArg a x) : ℚ) - ClaudeWCT.Numerics.SharedFees.scale) /
    ClaudeWCT.Numerics.SharedFees.scale

def mgfOk (P : Par) (L U : ℚ) (fee : ℕ) : Bool :=
  decide ((feeScale : ℚ) * expm1Up P.a P.c0 ≤ fee * P.c0) ||
    (decide (U ≤ P.c0) && decide (0 < U) &&
      decide (expArg P.a U ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale) &&
      decide ((feeScale : ℚ) * expm1Up P.a U ≤ fee * U)) ||
    (decide (P.c0 ≤ L) && decide ((feeScale : ℚ) * expm1Up P.a P.c0 ≤ fee * L))

/-- `scarf (θ - x) m vv ≤ x * fee / feeScale`, in rational arithmetic without square roots. -/
def scarfPointOk (P : Par) (x : ℚ) (fee : ℕ) : Bool :=
  let w := P.m - P.θ + x
  let t := 2 * x * fee / feeScale - w
  decide (0 ≤ t) && decide (w * w + P.vv ≤ t * t)

def scarfOk (P : Par) (L U : ℚ) (fee : ℕ) : Bool :=
  decide (U ≤ P.c0) || (scarfPointOk P (max L P.c0) fee && scarfPointOk P U fee && decide (max L P.c0 ≤ U))

/-! ### Costs -/

noncomputable def costMean (P : Par) (x : ℝ) : ℝ := min x P.c0
noncomputable def costSec (P : Par) (x : ℝ) : ℝ := min x P.c0 ^ 2
noncomputable def costCount (P : Par) (x : ℝ) : ℝ := if (P.c0 : ℝ) < x then 1 else 0
noncomputable def costOver (P : Par) (x : ℝ) : ℝ := max 0 (x - P.c0)
noncomputable def costMgf (P : Par) (x : ℝ) : ℝ := Real.exp (P.a * min x P.c0) - 1
noncomputable def costScarf (P : Par) (x : ℝ) : ℝ :=
  if (P.c0 : ℝ) < x then scarf (P.θ - x) P.m P.vv else 0

/-! ### Soundness of the run checks -/

theorem feeScale_pos : (0 : ℝ) < feeScale := by norm_num [feeScale]

theorem div_fee_mono {x y fee : ℝ} (hxy : x ≤ y) (hfee : 0 ≤ fee) :
    x * fee / feeScale ≤ y * fee / feeScale := by
  have := feeScale_pos
  gcongr

theorem meanOk_sound (P : Par) (hc : 0 ≤ (P.c0 : ℝ)) (L U : ℚ) (fee : ℕ) (h : meanOk P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hL : (L : ℝ) ≤ x) : costMean P x ≤ x * fee / feeScale := by
  have hS := feeScale_pos
  unfold meanOk at h
  unfold costMean
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨h1, h2⟩
  · have h' : (feeScale : ℝ) ≤ fee := by exact_mod_cast h
    calc min x P.c0 ≤ x := min_le_left _ _
      _ ≤ x * fee / feeScale := by rw [le_div_iff₀ hS]; nlinarith
  · have h1' : (P.c0 : ℝ) ≤ L := by exact_mod_cast h1
    have h2' : (feeScale : ℝ) * P.c0 ≤ fee * L := by exact_mod_cast h2
    calc min x P.c0 ≤ P.c0 := min_le_right _ _
      _ ≤ L * fee / feeScale := by rw [le_div_iff₀ hS]; linarith
      _ ≤ x * fee / feeScale := div_fee_mono hL (Nat.cast_nonneg _)

theorem secOk_sound (P : Par) (hc : 0 ≤ (P.c0 : ℝ)) (L U : ℚ) (fee : ℕ) (h : secOk P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hL : (L : ℝ) ≤ x) (hU : x ≤ (U : ℝ)) : costSec P x ≤ x * fee / feeScale := by
  have hS := feeScale_pos
  unfold secOk at h
  unfold costSec
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have hmin0 : 0 ≤ min x (P.c0 : ℝ) := le_min hx hc
  rcases h with (h | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · have h' : (feeScale : ℝ) * P.c0 ≤ fee := by exact_mod_cast h
    have hsq : min x (P.c0 : ℝ) ^ 2 ≤ x * P.c0 := by
      rcases le_total x P.c0 with hxc | hxc
      · rw [min_eq_left hxc]; nlinarith
      · rw [min_eq_right hxc]; nlinarith
    calc min x (P.c0 : ℝ) ^ 2 ≤ x * P.c0 := hsq
      _ ≤ x * fee / feeScale := by rw [le_div_iff₀ hS]; nlinarith
  · have h1' : (U : ℝ) ≤ P.c0 := by exact_mod_cast h1
    have h2' : (feeScale : ℝ) * U ≤ fee := by exact_mod_cast h2
    rw [min_eq_left (hU.trans h1')]
    rw [le_div_iff₀ hS]
    have h3 : x * (feeScale : ℝ) ≤ fee := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hx]
  · have h1' : (P.c0 : ℝ) ≤ L := by exact_mod_cast h1
    have h2' : (feeScale : ℝ) * (P.c0 * P.c0) ≤ fee * L := by exact_mod_cast h2
    rw [min_eq_right (h1'.trans hL)]
    calc (P.c0 : ℝ) ^ 2 ≤ L * fee / feeScale := by rw [le_div_iff₀ hS]; nlinarith
      _ ≤ x * fee / feeScale := div_fee_mono hL (Nat.cast_nonneg _)

theorem countOk_sound (P : Par) (L U : ℚ) (fee : ℕ) (h : countOk P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hL : (L : ℝ) ≤ x) (hU : x ≤ (U : ℝ)) : costCount P x ≤ x * fee / feeScale := by
  have hS := feeScale_pos
  unfold countOk at h
  unfold costCount
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  have hpos : 0 ≤ x * fee / feeScale := by positivity
  split_ifs with hcx
  · rcases h with (h | h) | h
    · have h' : (U : ℝ) ≤ P.c0 := by exact_mod_cast h
      linarith
    · have h' : (feeScale : ℝ) ≤ fee * P.c0 := by exact_mod_cast h
      rw [le_div_iff₀ hS]
      nlinarith [mul_le_mul_of_nonneg_left hcx.le (Nat.cast_nonneg fee : (0 : ℝ) ≤ fee)]
    · have h' : (feeScale : ℝ) ≤ fee * L := by exact_mod_cast h
      rw [le_div_iff₀ hS]
      nlinarith [mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg fee : (0 : ℝ) ≤ fee)]
  · exact hpos

theorem overOk_sound (P : Par) (hc : 0 ≤ (P.c0 : ℝ)) (L U : ℚ) (fee : ℕ) (h : overOk P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hU : x ≤ (U : ℝ)) : costOver P x ≤ x * fee / feeScale := by
  have hS := feeScale_pos
  unfold overOk at h
  unfold costOver
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have hpos : 0 ≤ x * fee / feeScale := by positivity
  apply max_le hpos
  rcases h with (h | h) | ⟨h0, h⟩
  · have h' : (U : ℝ) ≤ P.c0 := by exact_mod_cast h
    linarith
  · have h' : (feeScale : ℝ) ≤ fee := by exact_mod_cast h
    rw [le_div_iff₀ hS]
    nlinarith
  · have h0' : (0 : ℝ) < U := by exact_mod_cast h0
    have h' : (feeScale : ℝ) * (U - P.c0) ≤ fee * U := by exact_mod_cast h
    rw [le_div_iff₀ hS]
    -- (x - c0) * U ≤ x * (U - c0) and x * (U - c0) * S ≤ x * fee * U
    have h1 : (x - P.c0) * U ≤ x * (U - P.c0) := by nlinarith
    have h2 : x * ((feeScale : ℝ) * (U - P.c0)) ≤ x * (fee * U) := mul_le_mul_of_nonneg_left h' hx
    nlinarith

theorem expm1Up_sound (a x : ℚ) (hax : 0 ≤ a * x)
    (h8 : expArg a x ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale) :
    Real.exp ((a : ℝ) * x) - 1 ≤ (expm1Up a x : ℝ) := by
  have hS : (0 : ℝ) < ClaudeWCT.Numerics.SharedFees.scale := by
    exact_mod_cast ClaudeWCT.Numerics.SharedFees.scale_pos
  set X := expArg a x with hX
  have hceil : (a : ℝ) * x * ClaudeWCT.Numerics.SharedFees.scale ≤ X := by
    have h1 : a * x * (ClaudeWCT.Numerics.SharedFees.scale : ℚ) ≤ ⌈a * x * (ClaudeWCT.Numerics.SharedFees.scale : ℚ)⌉ :=
      Int.le_ceil _
    have h0 : 0 ≤ ⌈a * x * (ClaudeWCT.Numerics.SharedFees.scale : ℚ)⌉ :=
      Int.ceil_nonneg (by positivity)
    have h2 : ((X : ℤ) : ℚ) = ⌈a * x * (ClaudeWCT.Numerics.SharedFees.scale : ℚ)⌉ := by
      rw [hX, expArg, Int.toNat_of_nonneg h0]
    have h3 := h1.trans_eq h2.symm
    have h4 : a * x * (ClaudeWCT.Numerics.SharedFees.scale : ℚ) ≤ (X : ℚ) := by exact_mod_cast h3
    exact_mod_cast h4
  have he := ClaudeWCT.Numerics.SharedFees.expUpper_sound X h8
  have hmono : Real.exp ((a : ℝ) * x) ≤ Real.exp ((X : ℝ) / ClaudeWCT.Numerics.SharedFees.scale) := by
    apply Real.exp_le_exp.mpr
    rw [le_div_iff₀ hS]
    exact hceil
  have hcast : (expm1Up a x : ℝ) =
      ((ClaudeWCT.Numerics.SharedFees.expUpper X : ℝ) - ClaudeWCT.Numerics.SharedFees.scale) /
        ClaudeWCT.Numerics.SharedFees.scale := by
    simp only [expm1Up, ← hX]
    push_cast
    ring
  rw [hcast, sub_div, div_self hS.ne']
  linarith

theorem expm1Up_nonneg (a x : ℚ) (hax : 0 ≤ a * x)
    (h8 : expArg a x ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale) : 0 ≤ (expm1Up a x : ℝ) := by
  have h := expm1Up_sound a x hax h8
  have : 0 ≤ Real.exp ((a : ℝ) * x) - 1 := by
    have : (0 : ℝ) ≤ (a : ℝ) * x := by exact_mod_cast hax
    linarith [Real.add_one_le_exp ((a : ℝ) * x)]
  linarith

/-- The clipped exponential cost per unit price, below and above the clip. -/
theorem mgf_ratio (P : Par) (hc : 0 < (P.c0 : ℝ)) (ha : 0 ≤ (P.a : ℝ))
    (h8c : expArg P.a P.c0 ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale) (x : ℝ) (hx : 0 ≤ x) :
    costMgf P x ≤ x * (expm1Up P.a P.c0 : ℝ) / P.c0 := by
  have hac : 0 ≤ P.a * P.c0 := by
    have : (0 : ℝ) ≤ (P.a : ℝ) * P.c0 := mul_nonneg ha hc.le
    exact_mod_cast this
  have hE := expm1Up_sound P.a P.c0 hac h8c
  have hE0 := expm1Up_nonneg P.a P.c0 hac h8c
  unfold costMgf
  rcases le_total x P.c0 with hxc | hxc
  · rw [min_eq_left hxc]
    have hs := ClaudeWCT.Numerics.SharedPathWinsor.exp_secant (P.a : ℝ) x P.c0 hx hxc hc
    calc Real.exp (P.a * x) - 1 ≤ (x / P.c0) * (Real.exp (P.a * P.c0) - 1) := hs
      _ ≤ (x / P.c0) * (expm1Up P.a P.c0 : ℝ) := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = x * (expm1Up P.a P.c0 : ℝ) / P.c0 := by ring
  · rw [min_eq_right hxc]
    calc Real.exp (P.a * P.c0) - 1 ≤ (expm1Up P.a P.c0 : ℝ) := hE
      _ ≤ x * (expm1Up P.a P.c0 : ℝ) / P.c0 := by
        rw [le_div_iff₀ hc]; nlinarith

theorem mgfOk_sound (P : Par) (hc : 0 < (P.c0 : ℝ)) (ha : 0 ≤ (P.a : ℝ))
    (h8c : expArg P.a P.c0 ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale)
    (L U : ℚ) (fee : ℕ) (h : mgfOk P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hL : (L : ℝ) ≤ x) (hU : x ≤ (U : ℝ)) : costMgf P x ≤ x * fee / feeScale := by
  have hS := feeScale_pos
  have hac : 0 ≤ P.a * P.c0 := by
    have : (0 : ℝ) ≤ (P.a : ℝ) * P.c0 := mul_nonneg ha hc.le
    exact_mod_cast this
  have hE := expm1Up_sound P.a P.c0 hac h8c
  have hE0 := expm1Up_nonneg P.a P.c0 hac h8c
  unfold mgfOk at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (h | ⟨⟨⟨h1, h0⟩, h8⟩, h2⟩) | ⟨h1, h2⟩
  · have h' : (feeScale : ℝ) * (expm1Up P.a P.c0 : ℝ) ≤ fee * P.c0 := by exact_mod_cast h
    refine (mgf_ratio P hc ha h8c x hx).trans ?_
    rw [div_le_div_iff₀ hc hS]
    nlinarith [mul_le_mul_of_nonneg_left h' hx]
  · have h1' : (U : ℝ) ≤ P.c0 := by exact_mod_cast h1
    have h0' : (0 : ℝ) < U := by exact_mod_cast h0
    have h2' : (feeScale : ℝ) * (expm1Up P.a U : ℝ) ≤ fee * U := by exact_mod_cast h2
    have haU : 0 ≤ P.a * U := by
      have : (0 : ℝ) ≤ (P.a : ℝ) * U := mul_nonneg ha h0'.le
      exact_mod_cast this
    have hEU := expm1Up_sound P.a U haU h8
    unfold costMgf
    rw [min_eq_left (hU.trans h1')]
    have hs := ClaudeWCT.Numerics.SharedPathWinsor.exp_secant (P.a : ℝ) x U hx hU h0'
    calc Real.exp (P.a * x) - 1 ≤ (x / U) * (Real.exp (P.a * U) - 1) := hs
      _ ≤ (x / U) * (expm1Up P.a U : ℝ) := mul_le_mul_of_nonneg_left hEU (by positivity)
      _ ≤ x * fee / feeScale := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ h0' hS]
        nlinarith [mul_le_mul_of_nonneg_left h2' hx]
  · have h1' : (P.c0 : ℝ) ≤ L := by exact_mod_cast h1
    have h2' : (feeScale : ℝ) * (expm1Up P.a P.c0 : ℝ) ≤ fee * L := by exact_mod_cast h2
    unfold costMgf
    rw [min_eq_right (h1'.trans hL)]
    calc Real.exp (P.a * P.c0) - 1 ≤ (expm1Up P.a P.c0 : ℝ) := hE
      _ ≤ L * fee / feeScale := by rw [le_div_iff₀ hS]; linarith
      _ ≤ x * fee / feeScale := div_fee_mono hL (Nat.cast_nonneg _)

/-! ### Scarf payments -/

theorem sqrt_convex (u1 u2 v t : ℝ) (hv : 0 ≤ v) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.sqrt (((1 - t) * u1 + t * u2) ^ 2 + v) ≤
      (1 - t) * Real.sqrt (u1 ^ 2 + v) + t * Real.sqrt (u2 ^ 2 + v) := by
  set A1 := Real.sqrt (u1 ^ 2 + v)
  set A2 := Real.sqrt (u2 ^ 2 + v)
  have hA1 : 0 ≤ A1 := Real.sqrt_nonneg _
  have hA2 : 0 ≤ A2 := Real.sqrt_nonneg _
  have hA1s : A1 ^ 2 = u1 ^ 2 + v := Real.sq_sqrt (by positivity)
  have hA2s : A2 ^ 2 = u2 ^ 2 + v := Real.sq_sqrt (by positivity)
  have hprod : u1 * u2 + v ≤ A1 * A2 := by
    have hsq : (u1 * u2 + v) ^ 2 ≤ (A1 * A2) ^ 2 := by
      rw [mul_pow, hA1s, hA2s]
      nlinarith [sq_nonneg (u1 - u2), mul_nonneg hv (sq_nonneg (u1 - u2))]
    by_contra hcon
    push Not at hcon
    have h0 : 0 ≤ A1 * A2 := mul_nonneg hA1 hA2
    nlinarith
  have hR : 0 ≤ (1 - t) * A1 + t * A2 := by
    have : 0 ≤ 1 - t := by linarith
    positivity
  rw [Real.sqrt_le_left hR]
  have h1t : 0 ≤ (1 - t) * t := mul_nonneg (by linarith) ht0
  nlinarith [mul_le_mul_of_nonneg_left hprod h1t]

theorem scarf_affine (θ m vv x1 x2 t : ℝ) (hvv : 0 ≤ vv) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    scarf (θ - ((1 - t) * x1 + t * x2)) m vv ≤ (1 - t) * scarf (θ - x1) m vv + t * scarf (θ - x2) m vv := by
  unfold scarf
  have hw : m - (θ - ((1 - t) * x1 + t * x2)) = (1 - t) * (m - (θ - x1)) + t * (m - (θ - x2)) := by ring
  rw [hw]
  have := sqrt_convex (m - (θ - x1)) (m - (θ - x2)) vv t hvv ht0 ht1
  linarith

theorem scarfPointOk_sound (P : Par) (x0 : ℚ) (fee : ℕ) (h : scarfPointOk P x0 fee = true) :
    scarf (P.θ - x0) P.m P.vv ≤ x0 * fee / feeScale := by
  unfold scarfPointOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨ht, hsq⟩ := h
  set w : ℚ := P.m - P.θ + x0
  set t : ℚ := 2 * x0 * fee / feeScale - w
  have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht
  have hsq' : (w : ℝ) * w + P.vv ≤ (t : ℝ) * t := by exact_mod_cast hsq
  have hsqrt : Real.sqrt ((w : ℝ) ^ 2 + P.vv) ≤ t := by
    rw [Real.sqrt_le_left ht']
    nlinarith
  have hwc : ((P.m : ℝ) - (P.θ - x0)) = w := by simp only [w]; push_cast; ring
  have htc : (t : ℝ) = 2 * x0 * fee / feeScale - w := by simp only [t, feeScale]; push_cast; ring
  unfold scarf
  rw [hwc]
  have := feeScale_pos
  rw [htc] at hsqrt
  have : (2 : ℝ) * x0 * fee / feeScale = 2 * (x0 * fee / feeScale) := by ring
  linarith

theorem scarf_interp (θ m vv F x1 x2 x : ℝ) (hvv : 0 ≤ vv)
    (h1 : scarf (θ - x1) m vv ≤ x1 * F) (h2 : scarf (θ - x2) m vv ≤ x2 * F)
    (hx1 : x1 ≤ x) (hx2 : x ≤ x2) : scarf (θ - x) m vv ≤ x * F := by
  rcases eq_or_lt_of_le (hx1.trans hx2) with heq | hlt
  · have : x = x1 := le_antisymm (heq ▸ hx2) hx1
    rw [this]; exact h1
  · set t := (x - x1) / (x2 - x1) with ht
    have hd : 0 < x2 - x1 := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
    have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
    have hx : x = (1 - t) * x1 + t * x2 := by
      rw [ht]; field_simp; ring
    rw [hx]
    have ha := scarf_affine θ m vv x1 x2 t hvv ht0 ht1
    have hb := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 - t by linarith)
    have hc := mul_le_mul_of_nonneg_left h2 ht0
    nlinarith

theorem scarfOk_sound (P : Par) (hvv : 0 ≤ (P.vv : ℝ)) (L U : ℚ) (fee : ℕ) (h : scarfOk P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hL : (L : ℝ) ≤ x) (hU : x ≤ (U : ℝ)) : costScarf P x ≤ x * fee / feeScale := by
  have hS := feeScale_pos
  have hpos : 0 ≤ x * fee / feeScale := by positivity
  unfold costScarf
  split_ifs with hcx
  · unfold scarfOk at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨⟨h1, h2⟩, h3⟩
    · have h' : (U : ℝ) ≤ P.c0 := by exact_mod_cast h
      linarith
    · have p1 := scarfPointOk_sound P (max L P.c0) fee h1
      have p2 := scarfPointOk_sound P U fee h2
      have hcast : ((max L P.c0 : ℚ) : ℝ) = max (L : ℝ) (P.c0 : ℝ) := Rat.cast_max L P.c0
      rw [hcast] at p1
      have hF : ∀ y : ℝ, y * fee / feeScale = y * ((fee : ℝ) / feeScale) := fun y => by ring
      rw [hF] at p1 p2 ⊢
      exact scarf_interp P.θ P.m P.vv _ _ _ x hvv p1 p2 (max_le hL hcx.le) hU
  · exact hpos

/-! ### Global (unbinned) fees -/


theorem sec_global (P : Par) (hc : 0 ≤ (P.c0 : ℝ)) (G : ℕ) (hG : (feeScale : ℚ) * P.c0 ≤ G)
    (x : ℝ) (hx : 0 ≤ x) : costSec P x ≤ x * G / feeScale := by
  have hS := feeScale_pos
  have h' : (feeScale : ℝ) * P.c0 ≤ G := by exact_mod_cast hG
  have hsq : min x (P.c0 : ℝ) ^ 2 ≤ x * P.c0 := by
    rcases le_total x P.c0 with hxc | hxc
    · rw [min_eq_left hxc]; nlinarith
    · rw [min_eq_right hxc]; nlinarith
  unfold costSec
  calc min x (P.c0 : ℝ) ^ 2 ≤ x * P.c0 := hsq
    _ ≤ x * G / feeScale := by rw [le_div_iff₀ hS]; nlinarith

theorem count_global (P : Par) (hc : 0 < (P.c0 : ℝ)) (G : ℕ) (hG : (feeScale : ℚ) ≤ G * P.c0)
    (x : ℝ) (hx : 0 ≤ x) : costCount P x ≤ x * G / feeScale := by
  have hS := feeScale_pos
  have h' : (feeScale : ℝ) ≤ G * P.c0 := by exact_mod_cast hG
  unfold costCount
  split_ifs with hcx
  · rw [le_div_iff₀ hS]
    nlinarith [mul_le_mul_of_nonneg_left hcx.le (Nat.cast_nonneg G : (0 : ℝ) ≤ G)]
  · positivity

theorem over_global (P : Par) (hc : 0 ≤ (P.c0 : ℝ)) (G : ℕ) (hG : (feeScale : ℚ) ≤ G)
    (x : ℝ) (hx : 0 ≤ x) : costOver P x ≤ x * G / feeScale := by
  have hS := feeScale_pos
  have h' : (feeScale : ℝ) ≤ G := by exact_mod_cast hG
  unfold costOver
  apply max_le (by positivity)
  rw [le_div_iff₀ hS]
  nlinarith

theorem mgf_global (P : Par) (hc : 0 < (P.c0 : ℝ)) (ha : 0 ≤ (P.a : ℝ))
    (h8c : expArg P.a P.c0 ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale) (G : ℕ)
    (hG : (feeScale : ℚ) * expm1Up P.a P.c0 ≤ G * P.c0)
    (x : ℝ) (hx : 0 ≤ x) : costMgf P x ≤ x * G / feeScale := by
  have hS := feeScale_pos
  have h' : (feeScale : ℝ) * (expm1Up P.a P.c0 : ℝ) ≤ G * P.c0 := by exact_mod_cast hG
  refine (mgf_ratio P hc ha h8c x hx).trans ?_
  rw [div_le_div_iff₀ hc hS]
  nlinarith [mul_le_mul_of_nonneg_left h' hx]

theorem scarf_global (P : Par) (hc : 0 < (P.c0 : ℝ)) (hmθ : (P.m : ℝ) ≤ P.θ) (hsv : 0 ≤ (P.sv : ℝ))
    (hsv2 : (P.vv : ℝ) ≤ (P.sv : ℝ) ^ 2) (hvv : 0 ≤ (P.vv : ℝ)) (G : ℕ)
    (hG : (feeScale : ℚ) * (1 + P.sv / (2 * P.c0)) ≤ G)
    (x : ℝ) (hx : 0 ≤ x) : costScarf P x ≤ x * G / feeScale := by
  have hS := feeScale_pos
  have h' : (feeScale : ℝ) * (1 + P.sv / (2 * P.c0)) ≤ G := by exact_mod_cast hG
  unfold costScarf
  split_ifs with hcx
  · unfold scarf
    set w : ℝ := P.m - (P.θ - x)
    have hw : w ≤ x := by simp only [w]; linarith
    have hsq : Real.sqrt (w ^ 2 + P.vv) ≤ |w| + P.sv := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [sq_abs w, abs_nonneg w]
    have hb : (w + Real.sqrt (w ^ 2 + P.vv)) / 2 ≤ x + P.sv / 2 := by
      rcases le_total 0 w with h0 | h0
      · rw [abs_of_nonneg h0] at hsq; linarith
      · rw [abs_of_nonpos h0] at hsq; linarith
    have hc2 : x + (P.sv : ℝ) / 2 ≤ x * (1 + P.sv / (2 * P.c0)) := by
      have : (P.sv : ℝ) / 2 ≤ x * (P.sv / (2 * P.c0)) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    calc (w + Real.sqrt (w ^ 2 + P.vv)) / 2 ≤ x * (1 + P.sv / (2 * P.c0)) := hb.trans hc2
      _ ≤ x * G / feeScale := by
        rw [le_div_iff₀ hS]
        nlinarith [mul_le_mul_of_nonneg_left h' hx]
  · positivity

/-! ### The six kinds, uniformly -/

/-- Run check of kind `k` (0 mean, 1 second moment, 2 count, 3 over, 4 clipped mgf, 5 Scarf). -/
def okOf : ℕ → Par → ℚ → ℚ → ℕ → Bool
  | 0 => meanOk | 1 => secOk | 2 => countOk | 3 => overOk | 4 => mgfOk | _ => scarfOk

noncomputable def costOf : ℕ → Par → ℝ → ℝ
  | 0 => costMean | 1 => costSec | 2 => costCount | 3 => costOver | 4 => costMgf | _ => costScarf

/-- Global (all prices) fee check of kind `k`. -/
def globOk (k : ℕ) (P : Par) (G : ℕ) : Bool :=
  match k with
  | 0 => decide ((feeScale : ℚ) ≤ G)
  | 1 => decide ((feeScale : ℚ) * P.c0 ≤ G)
  | 2 => decide ((feeScale : ℚ) ≤ G * P.c0)
  | 3 => decide ((feeScale : ℚ) ≤ G)
  | 4 => decide ((feeScale : ℚ) * expm1Up P.a P.c0 ≤ G * P.c0)
  | _ => decide ((feeScale : ℚ) * (1 + P.sv / (2 * P.c0)) ≤ G)

/-- Admissible route-C parameters. -/
def parOk (P : Par) : Bool :=
  decide (0 < P.c0) && decide (0 ≤ P.a) &&
    decide (expArg P.a P.c0 ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale) &&
    decide (0 ≤ P.vv) && decide (0 ≤ P.sv) && decide (P.vv ≤ P.sv ^ 2) && decide (P.m ≤ P.θ) &&
    decide (0 ≤ P.m)

structure ParFacts (P : Par) : Prop where
  c0 : 0 < (P.c0 : ℝ)
  a : 0 ≤ (P.a : ℝ)
  h8 : expArg P.a P.c0 ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale
  vv : 0 ≤ (P.vv : ℝ)
  sv : 0 ≤ (P.sv : ℝ)
  svsq : (P.vv : ℝ) ≤ (P.sv : ℝ) ^ 2
  mθ : (P.m : ℝ) ≤ P.θ
  m : 0 ≤ (P.m : ℝ)

theorem parFacts_of_ok (P : Par) (h : parOk P = true) : ParFacts P := by
  unfold parOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, h3, by exact_mod_cast h4, by exact_mod_cast h5,
    by exact_mod_cast h6, by exact_mod_cast h7, by exact_mod_cast h8⟩

theorem ok_sound (k : ℕ) (P : Par) (hP : ParFacts P) (L U : ℚ) (fee : ℕ) (h : okOf k P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hL : (L : ℝ) ≤ x) (hU : x ≤ (U : ℝ)) : costOf k P x ≤ x * fee / feeScale := by
  match k, h with
  | 0, h => exact meanOk_sound P hP.c0.le L U fee h x hx hL
  | 1, h => exact secOk_sound P hP.c0.le L U fee h x hx hL hU
  | 2, h => exact countOk_sound P L U fee h x hx hL hU
  | 3, h => exact overOk_sound P hP.c0.le L U fee h x hx hU
  | 4, h => exact mgfOk_sound P hP.c0 hP.a hP.h8 L U fee h x hx hL hU
  | k + 5, h => exact scarfOk_sound P hP.vv L U fee h x hx hL hU

theorem glob_sound (k : ℕ) (P : Par) (hP : ParFacts P) (G : ℕ) (h : globOk k P G = true)
    (x : ℝ) (hx : 0 ≤ x) : costOf k P x ≤ x * G / feeScale := by
  have hS := feeScale_pos
  match k, h with
  | 0, h =>
    have h' : (feeScale : ℝ) ≤ G := by
      have := of_decide_eq_true h; exact_mod_cast this
    show min x (P.c0 : ℝ) ≤ _
    rw [le_div_iff₀ hS]
    nlinarith [min_le_left x (P.c0 : ℝ), min_le_right x (P.c0 : ℝ), le_min hx hP.c0.le]
  | 1, h => exact sec_global P hP.c0.le G (of_decide_eq_true h) x hx
  | 2, h => exact count_global P hP.c0 G (of_decide_eq_true h) x hx
  | 3, h => exact over_global P hP.c0.le G (of_decide_eq_true h) x hx
  | 4, h => exact mgf_global P hP.c0 hP.a hP.h8 G (of_decide_eq_true h) x hx
  | k + 5, h => exact scarf_global P hP.c0 hP.mθ hP.sv hP.svsq hP.vv G (of_decide_eq_true h) x hx

theorem costOf_nonneg (k : ℕ) (P : Par) (hP : ParFacts P) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ costOf k P x := by
  match k with
  | 0 => exact le_min hx hP.c0.le
  | 1 => exact sq_nonneg _
  | 2 => show 0 ≤ (if (P.c0 : ℝ) < x then (1 : ℝ) else 0); split_ifs <;> norm_num
  | 3 => exact le_max_left _ _
  | 4 =>
    show 0 ≤ Real.exp (P.a * min x P.c0) - 1
    have : 0 ≤ (P.a : ℝ) * min x P.c0 := mul_nonneg hP.a (le_min hx hP.c0.le)
    linarith [Real.add_one_le_exp ((P.a : ℝ) * min x P.c0)]
  | k + 5 =>
    show 0 ≤ (if (P.c0 : ℝ) < x then scarf (P.θ - x) P.m P.vv else 0)
    split_ifs
    · unfold scarf
      have h1 : |(P.m : ℝ) - (P.θ - x)| ≤ Real.sqrt (((P.m : ℝ) - (P.θ - x)) ^ 2 + P.vv) :=
        Real.abs_le_sqrt (by linarith [hP.vv])
      have h2 := neg_abs_le ((P.m : ℝ) - (P.θ - x))
      linarith
    · exact le_rfl

theorem scarf_shift (θ m vv z : ℝ) : scarf (θ - z) m vv = scarf θ (m + z) vv := by
  unfold scarf; ring_nf

/-- Every route-C cost is monotone in the bucket price (needed for the cap-777 thinning). -/
theorem costOf_mono (k : ℕ) (P : Par) (hP : ParFacts P) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    costOf k P x ≤ costOf k P y := by
  match k with
  | 0 => exact min_le_min hxy le_rfl
  | 1 => exact pow_le_pow_left₀ (le_min hx hP.c0.le) (min_le_min hxy le_rfl) 2
  | 2 =>
    show (if (P.c0 : ℝ) < x then (1 : ℝ) else 0) ≤ (if (P.c0 : ℝ) < y then (1 : ℝ) else 0)
    by_cases h : (P.c0 : ℝ) < x
    · rw [if_pos h, if_pos (lt_of_lt_of_le h hxy)]
    · rw [if_neg h]; split_ifs <;> norm_num
  | 3 => exact max_le_max le_rfl (sub_le_sub_right hxy _)
  | 4 =>
    show Real.exp (P.a * min x P.c0) - 1 ≤ Real.exp (P.a * min y P.c0) - 1
    exact sub_le_sub_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (min_le_min hxy le_rfl) hP.a)) 1
  | k + 5 =>
    show (if (P.c0 : ℝ) < x then scarf (P.θ - x) P.m P.vv else 0) ≤
      (if (P.c0 : ℝ) < y then scarf (P.θ - y) P.m P.vv else 0)
    by_cases h : (P.c0 : ℝ) < x
    · rw [if_pos h, if_pos (lt_of_lt_of_le h hxy), scarf_shift, scarf_shift]
      exact RouteC.scarf_mono (by linarith) le_rfl hP.vv
    · rw [if_neg h]
      exact costOf_nonneg (k + 5) P hP y (hx.trans hxy)

/-! ### Bins at a general gate -/

theorem upperQ_real (g j : ℕ) : (upperQ g j : ℝ) = (g : ℝ) / 2 ^ 66 * ((101 : ℝ) / 100) ^ j := by
  unfold upperQ
  rw [Rat.mkRat_eq_div]
  push_cast
  rw [div_pow]
  ring

theorem lowerQ_real (g j : ℕ) :
    (lowerQ g j : ℝ) = (g : ℝ) / 2 ^ 66 * (((100 : ℝ) / 101) ^ 13 * ((101 : ℝ) / 100) ^ j) := by
  unfold lowerQ
  rw [Rat.mkRat_eq_div]
  push_cast
  rw [div_pow, div_pow]
  ring

theorem upperQ_mono (g : ℕ) {i j : ℕ} (hij : i ≤ j) : (upperQ g i : ℝ) ≤ upperQ g j := by
  rw [upperQ_real, upperQ_real]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 101 / 100) hij

theorem lowerQ_mono (g : ℕ) {i j : ℕ} (hij : i ≤ j) : (lowerQ g i : ℝ) ≤ lowerQ g j := by
  rw [lowerQ_real, lowerQ_real]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 101 / 100) hij

theorem bin_bounds (g : ℕ) {bin : ℕ} {cov : ℝ}
    (h : ClaudeWCT.Numerics.SharedPathList.RoundedInterval 13 bin cov) :
    (lowerQ g bin : ℝ) ≤ (g : ℝ) / 2 ^ 66 * cov ∧ (g : ℝ) / 2 ^ 66 * cov ≤ upperQ g bin := by
  rw [lowerQ_real, upperQ_real]
  have hg : (0 : ℝ) ≤ (g : ℝ) / 2 ^ 66 := by positivity
  exact ⟨mul_le_mul_of_nonneg_left h.lower hg, mul_le_mul_of_nonneg_left h.upper hg⟩

/-! ### Run tables -/

/-- The bins of each run, with the run fee. -/
def runEntries (runs : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ) :=
  runs.flatMap fun e => (List.range' e.1 (e.2.1 - e.1 + 1)).map fun i => (i, e.2.2)

/-- The fee of bin `j` in a run table. -/
def runFee (runs : List (ℕ × ℕ × ℕ)) (j : ℕ) : ℕ := ((runEntries runs)[j]?.map Prod.snd).getD 0

/-- The runs tile `[s, n)` consecutively, each with `start ≤ end` (a linear check that replaces
comparing the expanded 7210-entry list with `List.range 7210` in the kernel). -/
def runsContig : List (ℕ × ℕ × ℕ) → ℕ → ℕ → Bool
  | [], s, n => s == n
  | e :: rest, s, n => e.1 == s && decide (e.1 ≤ e.2.1) && runsContig rest (e.2.1 + 1) n

theorem runsContig_le : ∀ (runs : List (ℕ × ℕ × ℕ)) (s n : ℕ), runsContig runs s n = true → s ≤ n
  | [], s, n, h => by simp only [runsContig, beq_iff_eq] at h; omega
  | e :: rest, s, n, h => by
      simp only [runsContig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      have := runsContig_le rest (e.2.1 + 1) n h.2
      omega

theorem runsContig_entries : ∀ (runs : List (ℕ × ℕ × ℕ)) (s n : ℕ), runsContig runs s n = true →
    (runEntries runs).map Prod.fst = List.range' s (n - s)
  | [], s, n, h => by
      simp only [runsContig, beq_iff_eq] at h
      subst h
      simp [runEntries]
  | e :: rest, s, n, h => by
      simp only [runsContig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have ih := runsContig_entries rest (e.2.1 + 1) n h3
      have hle := runsContig_le rest (e.2.1 + 1) n h3
      have hcons : runEntries (e :: rest) =
          (List.range' e.1 (e.2.1 - e.1 + 1)).map (fun i => (i, e.2.2)) ++ runEntries rest := by
        simp [runEntries, List.flatMap_cons]
      rw [hcons, List.map_append, ih, List.map_map]
      have hid : (Prod.fst ∘ fun i => (i, e.2.2)) = (id : ℕ → ℕ) := rfl
      rw [hid, List.map_id, h1]
      have hs : e.2.1 + 1 = s + (e.2.1 - s + 1) := by omega
      rw [hs, List.range'_append_1]
      congr 1
      omega

theorem entries_of_contig (runs : List (ℕ × ℕ × ℕ)) (h : runsContig runs 0 7210 = true) :
    (runEntries runs).map Prod.fst = List.range 7210 := by
  rw [runsContig_entries runs 0 7210 h, List.range_eq_range']

theorem runFee_lookup (runs : List (ℕ × ℕ × ℕ)) (n : ℕ) (hord : ∀ e ∈ runs, e.1 ≤ e.2.1)
    (hidx : (runEntries runs).map Prod.fst = List.range n) (j : ℕ) (hj : j < n) :
    ∃ e ∈ runs, e.1 ≤ j ∧ j ≤ e.2.1 ∧ runFee runs j = e.2.2 := by
  have hlen : (runEntries runs).length = n := by
    have := congrArg List.length hidx
    simpa using this
  have hjl : j < (runEntries runs).length := by omega
  set p := (runEntries runs)[j] with hp
  have hfst : p.1 = j := by
    have h1 : ((runEntries runs).map Prod.fst)[j]'(by simpa using hjl) = p.1 := by
      simp [hp]
    rw [← h1]
    simp [hidx]
  have hmem : p ∈ runEntries runs := List.getElem_mem hjl
  unfold runEntries at hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨e, he, hm⟩ := hmem
  rw [List.mem_map] at hm
  obtain ⟨i, hi, hpi⟩ := hm
  rw [List.mem_range'] at hi
  obtain ⟨k, hk, hik⟩ := hi
  have hij : i = j := by rw [← hfst, ← hpi]
  have hoe := hord e he
  refine ⟨e, he, by omega, by omega, ?_⟩
  unfold runFee
  rw [List.getElem?_eq_getElem hjl, ← hp, ← hpi]
  rfl

end ClaudeWCT.Numerics.RouteCFees
