import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import SigGolfCandidate.Merge003
import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge032
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge039
import SigGolfCandidate.Merge040
import SigGolfCandidate.Merge042
import SigGolfCandidate.Merge043
import SigGolfCandidate.Merge044

-- ==== merged from ClaudeWCT_Numerics_N600PriceCanonical ====
section

/-! ### Configuration (1)+(2), e7b: exact selected-credit laws for the restricted top choice and the
path-aware lower credit, from the packed generating polynomials. -/
namespace ClaudeWCT.Numerics.CanonicalHistogram
open OracleComp OracleSpec ENNReal Finset CanonicalCompression
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.ProducerV5.Canonical
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option quotPrecheck false

theorem histogramWeight_append (a b : List (Nat × Nat)) (x : Nat) :
    histogramWeight (a ++ b) x = histogramWeight a x + histogramWeight b x := by
  rw [histogramWeight_sum, histogramWeight_sum, histogramWeight_sum, List.map_append, List.sum_append]

theorem histogramWeight_split (h : List (Nat × Nat)) (k a b x : Nat) :
    histogramWeight (h.flatMap fun e => [(e.1 + k, e.2 * a), (e.1, e.2 * b)]) x =
      (if k ≤ x then histogramWeight h (x - k) * a else 0) + histogramWeight h x * b := by
  induction h with
  | nil => simp [histogramWeight]
  | cons e t ih =>
      rw [List.flatMap_cons, histogramWeight_append, ih]
      have h1 : histogramWeight (e :: t) (x - k) = (if e.1 = x - k then e.2 else 0) + histogramWeight t (x - k) := by
        rw [histogramWeight_sum, histogramWeight_sum]; simp
      have h2 : histogramWeight (e :: t) x = (if e.1 = x then e.2 else 0) + histogramWeight t x := by
        rw [histogramWeight_sum, histogramWeight_sum]; simp
      have h3 : histogramWeight [(e.1 + k, e.2 * a), (e.1, e.2 * b)] x =
          (if e.1 + k = x then e.2 * a else 0) + (if e.1 = x then e.2 * b else 0) := by
        rw [histogramWeight_sum]; simp
      rw [h1, h2, h3]
      have key : (if e.1 + k = x then e.2 * a else 0) =
          (if k ≤ x then (if e.1 = x - k then e.2 else 0) * a else 0) := by
        by_cases hk : k ≤ x
        · rw [if_pos hk]
          by_cases he : e.1 + k = x
          · rw [if_pos he, if_pos (by omega)]
          · rw [if_neg he, if_neg (by omega), Nat.zero_mul]
        · rw [if_neg hk, if_neg (by omega)]
      rw [key]
      by_cases hk : k ≤ x
      · simp only [if_pos hk]
        split_ifs <;> ring
      · simp only [if_neg hk]
        split_ifs <;> ring

/-- Campaign T51: the model histogram weight is the packet's `histogramWeight`. -/
theorem histW_eq_histogramWeight (h : List (Nat × Nat)) (c : Nat) :
    SigGolfResearch.T51Top.histW h c = histogramWeight h c := by
  rw [histogramWeight_sum]; rfl

theorem topWordCount_eq_hist (r : Nat) (h12 : 12 ≤ r) : topWordCount r = histogramWeight TopZero.topCounts r := by
  rw [topWordCount_eq r h12, histW_eq_histogramWeight]; rfl

theorem topHighWeight_eq : topHighWeight = TopZero.topHighW := rfl

/-- The d6b top selection law at the canonical floor 14 (T51), with the top producer zero cap 7. -/
theorem selected_top_histogram_card (c : Nat) (hc : 14 ≤ c) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 14 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c).card =
      histogramWeight TopZero.topAcceptedHistogram c := by
  rw [selected_top_path_card 14 c le_rfl hc, TopZero.topAcceptedHistogram, histogramWeight_split,
    if_pos (by omega : 2 ≤ c), topWordCount_eq_hist (c - 2) (by omega), topWordCount_eq_hist c (by omega),
    topHighWeight_eq]
  ring

theorem selected_top_histogram_probability (c : Nat) (hc : 14 ≤ c) :
    Pr[fun answer => ∃ dl, CanonicalPolicy.producerDecodeOut 0 14 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (histogramWeight TopZero.topAcceptedHistogram c : ENNReal) / topDen := by
  classical
  rw [probEvent_uniformSample]
  rw [show (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 14 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c) = _ from rfl, selected_top_histogram_card c hc]
  simp only [Fintype.card_bitVec, topDen, Nat.cast_pow, Nat.cast_ofNat]

local notation "lowerCountN" credit:arg =>
  (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
    SigGolfResearch.LowerEffectiveCounting.zeros w ≤ 5 ∧
    SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
    SigGolfResearch.LowerEffectiveCounting.score w = credit).card

local notation "lowerFiberN" z:arg credit:arg =>
  (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
    SigGolfResearch.LowerEffectiveCounting.zeros w = z ∧
    SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
    SigGolfResearch.LowerEffectiveCounting.score w = credit).card

theorem lower_counts_from_digits (p encoded : Nat)
    (hd : ∀ (z : Fin 6) (i : Nat), i<128 →
      SharedDigitBlock.digit (2^132) p (65536*z.val+128*201+i) = lowerFiberN z.val i)
    (he : encoded = (List.range 6).foldl (fun s zeros =>
      s + ((p >>> (132*(65536*zeros+128*201))) % 2^(132*128))) 0)
    (i : Nat) (hi : i<128) : coefficient 132 encoded i = lowerCountN i := by
  have hsum (j : Nat) (hj : j<128) :
      (∑ z : Fin 6, 1*SharedDigitBlock.digit (2^132) p (65536*z.val+128*201+j)) = lowerCountN j := by
    simp only [Nat.one_mul]
    rw [← lower_fibers j]
    apply Finset.sum_congr rfl
    intro z _
    exact hd z j hj
  have he' : encoded = ∑ z : Fin 6, 1*(p / (2^132)^(65536*z.val+128*201) % (2^132)^128) := by
    rw [he, lower_windows_fold]
    simp only [Nat.one_mul]
  rw [coefficient, bits_digit_eq, he']
  exact (SharedDigitBlock.digit_window_sum (2^132) 128 (fun _ : Fin 6 => p)
    (fun z => 65536*z.val+128*201) (fun _ => 1) (by positivity)
    (fun j hj => by
      rw [hsum j hj]
      have := lower_counts_bound j
      omega) i hi).trans (hsum i hi)

theorem lower_counts_of_check
    (hd : ∀ (z : Fin 6) (i : Nat), i<128 →
      SharedDigitBlock.digit (2^132) SigGolfResearch.LowerEffectiveCounting.packed
        (65536*z.val+128*201+i) = lowerFiberN z.val i)
    (hcheck : lowerHistogramCheck = true) (c : Fin 128) :
    lowerWordCount c.val = histogramWeight lowerCounts c.val := by
  have he : packHistogram 132 0 128 lowerCounts =
      (List.range 6).foldl (fun s zeros => s +
        ((SigGolfResearch.LowerEffectiveCounting.packed >>> (132*(65536*zeros+128*201))) % 2^(132*128))) 0 :=
    by simpa only [lowerHistogramCheck, decide_eq_true_eq] using hcheck
  exact (lower_counts_from_digits _ _ hd he c.val c.isLt).symm.trans (lower_histogram_digits c)

/-- The path-aware lower selection law. -/
theorem selected_lower_histogram_card
    (hd : ∀ (z : Fin 6) (i : Nat), i<128 →
      SharedDigitBlock.digit (2^132) SigGolfResearch.LowerEffectiveCounting.packed
        (65536*z.val+128*201+i) = lowerFiberN z.val i)
    (hcheck : lowerHistogramCheck = true)
    (lay : Layer) (hl : lay ≠ 0) (floor c : Nat) (hf : floor ≤ c) (hc : c < 128) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut lay floor answer = some dl ∧
        CanonicalPolicy.credit lay dl.2 dl.1 = c).card = histogramWeight lowerHistogram c * 2^126 := by
  rw [selected_lower_path_card lay hl floor c hf, lowerHistogram, pathSplit, histogramWeight_split,
    lower_counts_of_check hd hcheck ⟨c, hc⟩]
  by_cases h4 : 4 ≤ c
  · rw [if_pos h4, if_pos h4, lower_counts_of_check hd hcheck ⟨c - 4, by omega⟩]
    ring
  · rw [if_neg h4, if_neg h4]
    ring

theorem selected_lower_histogram_probability
    (hd : ∀ (z : Fin 6) (i : Nat), i<128 →
      SharedDigitBlock.digit (2^132) SigGolfResearch.LowerEffectiveCounting.packed
        (65536*z.val+128*201+i) = lowerFiberN z.val i)
    (hcheck : lowerHistogramCheck = true)
    (lay : Layer) (hl : lay ≠ 0) (floor c : Nat) (hf : floor ≤ c) (hc : c < 128) :
    Pr[fun answer => ∃ dl, CanonicalPolicy.producerDecodeOut lay floor answer = some dl ∧
        CanonicalPolicy.credit lay dl.2 dl.1 = c | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (histogramWeight lowerHistogram c : ENNReal) / lowerDen := by
  classical
  rw [probEvent_uniformSample]
  rw [show (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut lay floor answer = some dl ∧
        CanonicalPolicy.credit lay dl.2 dl.1 = c) = _ from rfl,
    selected_lower_histogram_card hd hcheck lay hl floor c hf hc]
  simp only [Fintype.card_bitVec, lowerDen, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ENNReal)^256 = (4*2^128)*2^126 by norm_num]
  exact ENNReal.mul_div_mul_right _ _ (by simp) (by simp)

end ClaudeWCT.Numerics.CanonicalHistogram
end
-- ==== merged from ClaudeWCT_Numerics_RouteCFees ====
section

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
end
-- ==== merged from ClaudeWCT_Numerics_RouteCData ====
section

/-! Route C data at the installed gate (generated by rc938/lean-notes/gen/rcgen938.py; RC938, cap-777 thinned envelope). -/

namespace ClaudeWCT.Numerics.RouteCData
open ClaudeWCT.Numerics.RouteCFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def rcPar : Par := ⟨791, (27 / 50 : ℚ), (52 / 5 : ℚ), (6386827 / 3200000 : ℚ), (94187 / 100000 : ℚ), (77593 / 10000000 : ℚ), (880869 / 10000000 : ℚ)⟩

def runs0 : List (ℕ × ℕ × ℕ) := [(0, 3878, 18446744073709551616), (3879, 3879, 18267775634496672967), (3880, 3880, 18086906568808587096), (3881, 3881, 17907828285949096135), (3882, 3882, 17730523055395144688), (3883, 3883, 17554973322173410582), (3884, 3884, 17381161705122188695), (3885, 3885, 17209070995170483857), (3886, 3886, 17038684153634142433), (3887, 3887, 16869984310528853894), (3888, 3888, 16702954762899855340), (3889, 3889, 16537578973168173604), (3890, 3890, 16373840567493241192), (3891, 3891, 16211723334151723953), (3892, 3892, 16051211221932399953), (3893, 3893, 15892288338546930647), (3894, 3894, 15734938949056366977), (3895, 3895, 15579147474313234631), (3896, 3896, 15424898489419044189), (3897, 3897, 15272176722197073454), (3898, 3898, 15120967051680270747), (3899, 3899, 14971254506614129452), (3900, 3900, 14823024263974385596), (3901, 3901, 14676261647499391680), (3902, 3902, 14530952126237021465), (3903, 3903, 14387081313105961846), (3904, 3904, 14244634963471249353), (3905, 3905, 14103598973733910250), (3906, 3906, 13963959379934564604), (3907, 3907, 13825702356370856044), (3908, 3908, 13688814214228570341), (3909, 3909, 13553281400226307268), (3910, 3910, 13419090495273571552), (3911, 3911, 13286228213142150052), (3912, 3912, 13154681399150643616), (3913, 3913, 13024437028862023382), (3914, 3914, 12895482206794082556), (3915, 3915, 12767804165142655996), (3916, 3916, 12641390262517481184), (3917, 3917, 12516227982690575430), (3918, 3918, 12392304933357005376), (3919, 3919, 12269608844907926115), (3920, 3920, 12148127569215768431), (3921, 3921, 12027849078431453892), (3922, 3922, 11908761463793518705), (3923, 3923, 11790852934449028421), (3924, 3924, 11674111816286166753), (3925, 3925, 11558526550778382924), (3926, 3926, 11444085693839983093), (3927, 3927, 11330777914693052567), (3928, 3928, 11218591994745596601), (3929, 3929, 11107516826480788714), (3930, 3930, 10997541412357216549), (3931, 3931, 10888654863720016385), (3932, 3932, 10780846399722788500), (3933, 3933, 10674105346260186634), (3934, 3934, 10568421134911075875), (3935, 3935, 10463783301892154332), (3936, 3936, 10360181487021934982), (3937, 3937, 10257605432694985130), (3938, 3938, 10156044982866321911), (3939, 3939, 10055490082045863279), (3940, 3940, 9955930774302834929), (3941, 3941, 9857357202280034583), (3942, 3942, 9759759606217856023), (3943, 3943, 9663128322987976261), (3944, 3944, 9567453785136610159), (3945, 3945, 9472726519937237781), (3946, 3946, 9378937148452710675), (3947, 3947, 9286076384606644232), (3948, 3948, 9194135034264004190), (3949, 3949, 9103103994320796228), (3950, 3950, 9012974251802768543), (3951, 3951, 8923736882973038161), (3952, 3952, 8835383052448552635), (3953, 3953, 8747904012325299638), (3954, 3954, 8661291101312177860), (3955, 3955, 8575535743873443425), (3956, 3956, 8490629449379646956), (3957, 3957, 8406563811266977184), (3958, 3958, 8323330506204927905), (3959, 3959, 8240921293272205847), (3960, 3960, 8159328013140797868), (3961, 3961, 8078542587268116701), (3962, 3962, 7998557017097145248), (3963, 3963, 7919363383264500246), (3964, 3964, 7840953844816336877), (3965, 3965, 7763320638432016710), (3966, 3966, 7686456077655462089), (3967, 3967, 7610352552134120880), (3968, 3968, 7535002526865466218), (3969, 3969, 7460398541450956652), (3970, 3970, 7386533209357382823), (3971, 3971, 7313399217185527548), (3972, 3972, 7240989323946066879), (3973, 3973, 7169296360342640474), (3974, 3974, 7098313228062020272), (3975, 3975, 7028032899071307200), (3976, 3976, 6958448414922086336), (3977, 3977, 6889552886061471620), (3978, 3978, 6821339491149971901), (3979, 3979, 6753801476386110793), (3980, 3980, 6686932154837733459), (3981, 3981, 6620724905779934118), (3982, 3982, 6555173174039538730), (3983, 3983, 6490270469346077951), (3984, 3984, 6426010365689186090), (3985, 3985, 6362386500682362465), (3986, 3986, 6299392574933032144), (3987, 3987, 6237022351418843707), (3988, 3988, 6175269654870142284), (3989, 3989, 6114128371158556717), (3990, 3990, 6053592446691640314), (3991, 3991, 5993655887813505261), (3992, 3992, 5934312760211391347), (3993, 3993, 5875557188328110245), (3994, 3994, 5817383354780307173), (3995, 3995, 5759785499782482350), (3996, 3996, 5702757920576715198), (3997, 3997, 5646294970868034849), (3998, 3998, 5590391060265381039), (3999, 3999, 5535040653728100039), (4000, 4000, 5480238271017920830), (4001, 4001, 5425978486156357258), (4002, 4002, 5372255926887482433), (4003, 4003, 5319065274146022211), (4004, 4004, 5266401261530715061), (4005, 4005, 5214258674782886199), (4006, 4006, 5162632351270184355), (4007, 4007, 5111517179475430055), (4008, 4008, 5060908098490524807), (4009, 4009, 5010800097515371096), (4010, 4010, 4961188215361753560), (4011, 4011, 4912067539962132238), (4012, 4012, 4863433207883299245), (4013, 4013, 4815280403844850738), (4014, 4014, 4767604360242426473), (4015, 4015, 4720400356675669775), (4016, 4016, 4673663719480861164), (4017, 4017, 4627389821268179370), (4018, 4018, 4581574080463543931), (4019, 4019, 4536211960854993991), (4020, 4020, 4491298971143558407), (4021, 4021, 4446830664498572680), (4022, 4022, 4402802638117398693), (4023, 4023, 4359210532789503656), (4024, 4024, 4316050032464855105), (4025, 4025, 4273316863826589213), (4026, 4026, 4231006795867910112), (4027, 4027, 4189115639473178329), (4028, 4028, 4147639247003146860), (4029, 4029, 4106573511884303822), (4030, 4030, 4065914368202281012), (4031, 4031, 4025657790299288131), (4032, 4032, 3985799792375532803), (4033, 4033, 3946336428094586933), (4034, 4034, 3907263790192660330), (4035, 4035, 3868578010091742901), (4036, 4036, 3830275257516577130), (4037, 4037, 3792351740115422901), (4038, 4038, 3754803703084577129), (4039, 4039, 3717627428796611019), (4040, 4040, 3680819236432288138), (4041, 4041, 3644375481616126869), (4042, 4042, 3608292556055571158), (4043, 4043, 3572566887183733819), (4044, 4044, 3537194937805677049), (4045, 4045, 3502173205748195098), (4046, 4046, 3467498223513064453), (4047, 4047, 3433166557933727182), (4048, 4048, 3399174809835373447), (4049, 4049, 3365519613698389552), (4050, 4050, 3332197637325138170), (4051, 4051, 3299205581510037792), (4052, 4052, 3266540179712908705), (4053, 4053, 3234198197735553173), (4054, 4054, 3202176433401537795), (4055, 4055, 3170471716239146332), (4056, 4056, 3139080907167471616), (4057, 4057, 3108000898185615461), (4058, 4058, 3077228612064965803), (4059, 4059, 3046761002044520597), (4060, 4060, 3016595051529228314), (4061, 4061, 2986727773791315162), (4062, 4062, 2957156211674569468), (4063, 4063, 2927877437301553929), (4064, 4064, 2898888551783716761), (4065, 4065, 2870186684934373031), (4066, 4066, 2841768994984527753), (4067, 4067, 2813632668301512627), (4068, 4068, 2785774919110408541), (4069, 4069, 2758192989218226279), (4070, 4070, 2730884147740818098), (4071, 4071, 2703845690832493166), (4072, 4072, 2677074941418310065), (4073, 4073, 2650569248929019867), (4074, 4074, 2624325989038633531), (4075, 4075, 2598342563404587655), (4076, 4076, 2572616399410482827), (4077, 4077, 2547144949911369135), (4078, 4078, 2521925692981553599), (4079, 4079, 2496956131664904554), (4080, 4080, 2472233793727628271), (4081, 4081, 2447756231413493338), (4082, 4082, 2423521021201478552), (4083, 4083, 2399525763565820349), (4084, 4084, 2375768082738435989), (4085, 4085, 2352245626473698999), (4086, 4086, 2328956065815543563), (4087, 4087, 2305897094866874815), (4088, 4088, 2283066430561262193), (4089, 4089, 2260461812436893260), (4090, 4090, 2238081002412765604), (4091, 4091, 2215921784567094658), (4092, 4092, 2193981964917915503), (4093, 4093, 2172259371205856934), (4094, 4094, 2150751852679066271), (4095, 4095, 2129457279880263634), (4096, 4096, 2108373544435904589), (4097, 4097, 2087498558847430286), (4098, 4098, 2066830256284584441), (4099, 4099, 2046366590380776675), (4100, 4100, 2026105535030471955), (4101, 4101, 2006045084188586094), (4102, 4102, 1986183251671867420), (4103, 4103, 1966518070962244970), (4104, 4104, 1947047595012123733), (4105, 4105, 1927769896051607656), (4106, 4106, 1908683065397631343), (4107, 4107, 1889785213264981528), (4108, 4108, 1871074468579189631), (4109, 4109, 1852548978791276863), (4110, 4110, 1834206909694333527), (4111, 4111, 1816046445241914384), (4112, 4112, 1798065787368232063), (4113, 4113, 1780263155810130755), (4114, 4114, 1762636787930822530), (4115, 4115, 1745184938545368842), (4116, 4116, 1727905879747889942), (4117, 4117, 1710797900740485091), (4118, 4118, 1693859307663846625), (4119, 4119, 1677088423429551114), (4120, 4120, 1660483587554011004), (4121, 4121, 1644043155994070301), (4122, 4122, 1627765500984228021), (4123, 4123, 1611649010875473288), (4124, 4124, 1595692089975716127), (4125, 4125, 1579893158391798145), (4126, 4126, 1564250651873067470), (4127, 4127, 1548763021656502446), (4128, 4128, 1533428734313368758), (4129, 4129, 1518246271597394810), (4130, 4130, 1503214130294450307), (4131, 4131, 1488330822073713176), (4132, 4132, 1473594873340310075), (4133, 4133, 1459004825089415916), (4134, 4134, 1444559232761797936), (4135, 4135, 1430256666100790036), (4136, 4136, 1416095709010683204), (4137, 4137, 1402074959416518024), (4138, 4138, 1388193029125265370), (4139, 4139, 1374448543688381554), (4140, 4140, 1360840142265724311), (4141, 4141, 1347366477490816150), (4142, 4142, 1334026215337441733), (4143, 4143, 1320818034987566072), (4144, 4144, 1307740628700560467), (4145, 4145, 1294792701683723235), (4146, 4146, 1281972971964082411), (4147, 4147, 1269280170261467733), (4148, 4148, 1256713039862839340), (4149, 4149, 1244270336497860733), (4150, 4150, 1231950828215703696), (4151, 4151, 1219753295263072966), (4152, 4152, 1207676529963438580), (4153, 4153, 1195719336597463941), (4154, 4154, 1183880531284617763), (4155, 4155, 1172158941865958181), (4156, 4156, 1160553407788077407), (4157, 4157, 1149062779988195453), (4158, 4158, 1137685920780391537), (4159, 4159, 1126421703742961918), (4160, 4160, 1115269013606892988), (4161, 4161, 1104226746145438602), (4162, 4162, 1093293808064790695), (4163, 4163, 1082469116895832372), (4164, 4164, 1071751600886962744), (4165, 4165, 1061140198897982915), (4166, 4166, 1050633860295032589), (4167, 4167, 1040231544846566920), (4168, 4168, 1029932222620363287), (4169, 4169, 1019734873881547809), (4170, 4170, 1009638488991631494), (4171, 4171, 999642068308546034), (4172, 4172, 989744622087669340), (4173, 4173, 979945170383831030), (4174, 4174, 970242742954288149), (4175, 4175, 960636379162661533), (4176, 4176, 951125127883823300), (4177, 4177, 941708047409726040), (4178, 4178, 932384205356164396), (4179, 4179, 923152678570459798), (4180, 4180, 914012553040059206), (4181, 4181, 904962923802038818), (4182, 4182, 896002894853503780), (4183, 4183, 887131579062875030), (4184, 4184, 878348098082054485), (4185, 4185, 869651582259459886), (4186, 4186, 861041170553920679), (4187, 4187, 852516010449426415), (4188, 4188, 844075257870719223), (4189, 4189, 835718077099722003), (4190, 4190, 827443640692794062), (4191, 4191, 819251129398806002), (4192, 4192, 811139732078025745), (4193, 4193, 803108645621807668), (4194, 4194, 795157074873076899), (4195, 4195, 787284232547600890), (4196, 4196, 779489339156040485), (4197, 4197, 771771622926772758), (4198, 4198, 764130319729477978), (4199, 4199, 756564672999483147), (4200, 4200, 749073933662854601), (4201, 4201, 741657360062232278), (4202, 4202, 734314217883398295), (4203, 4203, 727043780082572569), (4204, 4204, 719845326814428286), (4205, 4205, 712718145360820085), (4206, 4206, 705661530060217906), (4207, 4207, 698674782237839511), (4208, 4208, 691757210136474764), (4209, 4209, 684908128847994815), (4210, 4210, 678126860245539421), (4211, 4211, 671412732916375665), (4212, 4212, 664765082095421450), (4213, 4213, 658183249599427178), (4214, 4214, 651666583761809087), (4215, 4215, 645214439368127809), (4216, 4216, 638826177592205752), (4217, 4217, 632501165932876982), (4218, 4218, 626238778151363349), (4219, 4219, 620038394209270642), (4220, 4220, 613899400207198656), (4221, 4221, 607821188323959065), (4222, 4222, 601803156756395114), (4223, 4223, 595844709659797142), (4224, 4224, 589945257088908062), (4225, 4225, 584104214939512932), (4226, 4226, 578321004890606864), (4227, 4227, 572595054347135509), (4228, 4228, 566925796383302484), (4229, 4229, 561312669686438103), (4230, 4230, 555755118501423864), (4231, 4231, 550252592575667192), (4232, 4232, 544804547104620983), (4233, 4233, 539410442677842557), (4234, 4234, 534069745225586690), (4235, 4235, 528781925965927416), (4236, 4236, 523546461352403382), (4237, 4237, 518362833022181566), (4238, 4238, 513230527744734224), (4239, 4239, 508149037371023984), (4240, 4240, 503117858783192064), (4241, 4241, 498136493844744618), (4242, 4242, 493204449351232295), (4243, 4243, 488321236981418113), (4244, 4244, 483486373248928825), (4245, 4245, 478699379454384975), (4246, 4246, 473959781638004926), (4247, 4247, 469267110532678145), (4248, 4248, 464620901517503114), (4249, 4249, 460020694571785261), (4250, 4250, 455466034229490357), (4251, 4251, 450956469534148869), (4252, 4252, 446491553994206801), (4253, 4253, 442070845538818615), (4254, 4254, 437693906474077836), (4255, 4255, 433360303439681026), (4256, 4256, 429069607366020818), (4257, 4257, 424821393431703780), (4258, 4258, 420615241021488891), (4259, 4259, 416450733684642466), (4260, 4260, 412327459093705412), (4261, 4261, 408245009003668725), (4262, 4262, 404202979211553193), (4263, 4263, 400200969516389300), (4264, 4264, 396238583679593367), (4265, 4265, 392315429385736006), (4266, 4266, 388431118203699016), (4267, 4267, 384585265548216848), (4268, 4268, 380777490641798859), (4269, 4269, 377007416477028574), (4270, 4270, 373274669779236211), (4271, 4271, 369578880969540803), (4272, 4272, 365919684128258221), (4273, 4273, 362296716958671506), (4274, 4274, 358709620751159907), (4275, 4275, 355158040347683076), (4276, 4276, 351641624106616907), (4277, 4277, 348160023867937532), (4278, 4278, 344712894918750032), (4279, 4279, 341299895959158447), (4280, 4280, 337920689068473710), (4281, 4281, 334574939671756149), (4282, 4282, 331262316506689256), (4283, 4283, 327982491590781442), (4284, 4284, 324735140188892516), (4285, 4285, 321519940781081699), (4286, 4286, 318336575030773960), (4287, 4287, 315184727753241544), (4288, 4288, 312064086884397569), (4289, 4289, 308974343449898583), (4290, 4290, 305915191534553052), (4291, 4291, 302886328252032725), (4292, 4292, 299887453714883886), (4293, 4293, 296918271004835531), (4294, 4294, 293978486143401516), (4295, 4295, 291067808062773778), (4296, 4296, 288185948577003741), (4297, 4297, 285332622353469050), (4298, 4298, 282507546884622822), (4299, 4299, 279710442460022596), (4300, 4300, 276941032138636234), (4301, 4301, 274199041721422014), (4302, 4302, 271484199724180211), (4303, 4303, 268796237350673477), (4304, 4304, 266134888466013343), (4305, 4305, 263499889570310241), (4306, 4306, 260890979772584397), (4307, 4307, 258307900764935046), (4308, 4308, 255750396796965392), (4309, 4309, 253218214650460785), (4310, 4310, 250711103614317609), (4311, 4311, 248228815459720405), (4312, 4312, 245771104415564757), (4313, 4313, 243337727144123522), (4314, 4314, 240928442716953982), (4315, 4315, 238543012591043546), (4316, 4316, 236181200585191630), (4317, 4317, 233842772856625376), (4318, 4318, 231527497877846907), (4319, 4319, 229235146413709809), (4320, 4320, 226965491498722583), (4321, 4321, 224718308414576815), (4322, 4322, 222493374667897837), (4323, 4323, 220290469968215680), (4324, 4324, 218109376206154139), (4325, 4325, 215949877431835781), (4326, 4326, 213811759833500773), (4327, 4327, 211694811716337399), (4328, 4328, 209598823481522177), (4329, 4329, 207523587605467502), (4330, 4330, 205468898619274755), (4331, 4331, 203434553088390846), (4332, 4332, 201420349592466185), (4333, 4333, 199426088705412064), (4334, 4334, 197451572975655509), (4335, 4335, 195496606906589613), (4336, 4336, 193560996937217438), (4337, 4337, 191644551422987563), (4338, 4338, 189747080616819369), (4339, 4339, 187868396650316207), (4340, 4340, 186008313515164561), (4341, 4341, 184166647044717388), (4342, 4342, 182343214895759790), (4343, 4343, 180537836530455237), (4344, 4344, 178750333198470532), (4345, 4345, 176980527919277754), (4346, 4346, 175228245464631440), (4347, 4347, 173493312341219248), (4348, 4348, 171775556773484404), (4349, 4349, 170074808686618221), (4350, 4350, 168390899689721011), (4351, 4351, 166723663059129714), (4352, 7209, 165072933721910608)]

def glob0 : ℕ := 18446744073709551616

def runs1 : List (ℕ × ℕ × ℕ) := [(0, 3000, 1820697685370222), (3001, 3001, 1838904662223924), (3002, 3002, 1857293708846164), (3003, 3003, 1875866645934625), (3004, 3004, 1894625312393971), (3005, 3005, 1913571565517911), (3006, 3006, 1932707281173090), (3007, 3007, 1952034353984821), (3008, 3008, 1971554697524669), (3009, 3009, 1991270244499916), (3010, 3010, 2011182946944915), (3011, 3011, 2031294776414364), (3012, 3012, 2051607724178508), (3013, 3013, 2072123801420293), (3014, 3014, 2092845039434496), (3015, 3015, 2113773489828841), (3016, 3016, 2134911224727129), (3017, 3017, 2156260336974401), (3018, 3018, 2177822940344145), (3019, 3019, 2199601169747586), (3020, 3020, 2221597181445062), (3021, 3021, 2243813153259513), (3022, 3022, 2266251284792108), (3023, 3023, 2288913797640029), (3024, 3024, 2311802935616429), (3025, 3025, 2334920964972593), (3026, 3026, 2358270174622319), (3027, 3027, 2381852876368542), (3028, 3028, 2405671405132228), (3029, 3029, 2429728119183550), (3030, 3030, 2454025400375386), (3031, 3031, 2478565654379139), (3032, 3032, 2503351310922931), (3033, 3033, 2528384824032160), (3034, 3034, 2553668672272482), (3035, 3035, 2579205358995207), (3036, 3036, 2604997412585159), (3037, 3037, 2631047386711010), (3038, 3038, 2657357860578120), (3039, 3039, 2683931439183902), (3040, 3040, 2710770753575741), (3041, 3041, 2737878461111498), (3042, 3042, 2765257245722613), (3043, 3043, 2792909818179839), (3044, 3044, 2820838916361637), (3045, 3045, 2849047305525254), (3046, 3046, 2877537778580506), (3047, 3047, 2906313156366311), (3048, 3048, 2935376287929974), (3049, 3049, 2964730050809274), (3050, 3050, 2994377351317367), (3051, 3051, 3024321124830541), (3052, 3052, 3054564336078846), (3053, 3053, 3085109979439634), (3054, 3054, 3115961079234031), (3055, 3055, 3147120690026371), (3056, 3056, 3178591896926635), (3057, 3057, 3210377815895901), (3058, 3058, 3242481594054860), (3059, 3059, 3274906409995409), (3060, 3060, 3307655474095363), (3061, 3061, 3340732028836316), (3062, 3062, 3374139349124680), (3063, 3063, 3407880742615926), (3064, 3064, 3441959550042086), (3065, 3065, 3476379145542507), (3066, 3066, 3511142936997932), (3067, 3067, 3546254366367911), (3068, 3068, 3581716910031590), (3069, 3069, 3617534079131906), (3070, 3070, 3653709419923225), (3071, 3071, 3690246514122457), (3072, 3072, 3727148979263682), (3073, 3073, 3764420469056319), (3074, 3074, 3802064673746882), (3075, 3075, 3840085320484351), (3076, 3076, 3878486173689194), (3077, 3077, 3917271035426086), (3078, 3078, 3956443745780347), (3079, 3079, 3996008183238150), (3080, 3080, 4035968265070532), (3081, 3081, 4076327947721237), (3082, 3082, 4117091227198450), (3083, 3083, 4158262139470434), (3084, 3084, 4199844760865138), (3085, 3085, 4241843208473790), (3086, 3086, 4284261640558528), (3087, 3087, 4327104256964113), (3088, 3088, 4370375299533754), (3089, 3089, 4414079052529092), (3090, 3090, 4458219843054382), (3091, 3091, 4502802041484926), (3092, 3092, 4547830061899776), (3093, 3093, 4593308362518773), (3094, 3094, 4639241446143961), (3095, 3095, 4685633860605401), (3096, 3096, 4732490199211455), (3097, 3097, 4779815101203569), (3098, 3098, 4827613252215605), (3099, 3099, 4875889384737761), (3100, 3100, 4924648278585138), (3101, 3101, 4973894761370990), (3102, 3102, 5023633708984700), (3103, 3103, 5073870046074547), (3104, 3104, 5124608746535292), (3105, 3105, 5175854834000645), (3106, 3106, 5227613382340652), (3107, 3107, 5279889516164058), (3108, 3108, 5332688411325699), (3109, 3109, 5386015295438956), (3110, 3110, 5439875448393345), (3111, 3111, 5494274202877279), (3112, 3112, 5549216944906051), (3113, 3113, 5604709114355112), (3114, 3114, 5660756205498663), (3115, 3115, 5717363767553650), (3116, 3116, 5774537405229186), (3117, 3117, 5832282779281478), (3118, 3118, 5890605607074293), (3119, 3119, 5949511663145036), (3120, 3120, 6009006779776486), (3121, 3121, 6069096847574251), (3122, 3122, 6129787816049993), (3123, 3123, 6191085694210493), (3124, 3124, 6252996551152598), (3125, 3125, 6315526516664124), (3126, 3126, 6378681781830766), (3127, 3127, 6442468599649073), (3128, 3128, 6506893285645564), (3129, 3129, 6571962218502020), (3130, 3130, 6637681840687040), (3131, 3131, 6704058659093910), (3132, 3132, 6771099245684849), (3133, 3133, 6838810238141698), (3134, 3134, 6907198340523115), (3135, 3135, 6976270323928346), (3136, 3136, 7046033027167629), (3137, 3137, 7116493357439306), (3138, 3138, 7187658291013699), (3139, 3139, 7259534873923836), (3140, 3140, 7332130222663074), (3141, 3141, 7405451524889705), (3142, 3142, 7479506040138602), (3143, 3143, 7554301100539988), (3144, 3144, 7629844111545388), (3145, 3145, 7706142552660841), (3146, 3146, 7783203978187450), (3147, 3147, 7861036017969324), (3148, 3148, 7939646378149018), (3149, 3149, 8019042841930508), (3150, 3150, 8099233270349813), (3151, 3151, 8180225603053311), (3152, 3152, 8262027859083844), (3153, 3153, 8344648137674683), (3154, 3154, 8428094619051429), (3155, 3155, 8512375565241944), (3156, 3156, 8597499320894363), (3157, 3157, 8683474314103307), (3158, 3158, 8770309057244340), (3159, 3159, 8858012147816783), (3160, 3160, 8946592269294951), (3161, 3161, 9036058191987900), (3162, 3162, 9126418773907779), (3163, 3163, 9217682961646857), (3164, 3164, 9309859791263326), (3165, 3165, 9402958389175959), (3166, 3166, 9496987973067719), (3167, 3167, 9591957852798396), (3168, 3168, 9687877431326380), (3169, 3169, 9784756205639644), (3170, 3170, 9882603767696040), (3171, 3171, 9981429805373000), (3172, 3172, 10081244103426730), (3173, 3173, 10182056544460998), (3174, 3174, 10283877109905608), (3175, 3175, 10386715881004664), (3176, 3176, 10490583039814710), (3177, 3177, 10595488870212857), (3178, 3178, 10701443758914986), (3179, 3179, 10808458196504136), (3180, 3180, 10916542778469177), (3181, 3181, 11025708206253869), (3182, 3182, 11135965288316408), (3183, 3183, 11247324941199572), (3184, 3184, 11359798190611568), (3185, 3185, 11473396172517683), (3186, 3186, 11588130134242860), (3187, 3187, 11704011435585289), (3188, 3188, 11821051549941141), (3189, 3189, 11939262065440553), (3190, 3190, 12058654686094958), (3191, 3191, 12179241232955908), (3192, 3192, 12301033645285467), (3193, 3193, 12424043981738322), (3194, 3194, 12548284421555705), (3195, 3195, 12673767265771262), (3196, 3196, 12800504938428975), (3197, 3197, 12928509987813264), (3198, 3198, 13057795087691397), (3199, 3199, 13188373038568311), (3200, 3200, 13320256768953994), (3201, 3201, 13453459336643534), (3202, 3202, 13587993930009969), (3203, 3203, 13723873869310069), (3204, 3204, 13861112608003170), (3205, 3205, 13999723734083201), (3206, 3206, 14139720971424033), (3207, 3207, 14281118181138274), (3208, 3208, 14423929362949656), (3209, 3209, 14568168656579153), (3210, 3210, 14713850343144945), (3211, 3211, 14860988846576394), (3212, 3212, 15009598735042158), (3213, 3213, 15159694722392579), (3214, 3214, 15311291669616505), (3215, 3215, 15464404586312670), (3216, 3216, 15619048632175797), (3217, 3217, 15775239118497555), (3218, 3218, 15932991509682531), (3219, 3219, 16092321424779356), (3220, 3220, 16253244639027149), (3221, 3221, 16415777085417421), (3222, 3222, 16579934856271595), (3223, 3223, 16745734204834311), (3224, 3224, 16913191546882654), (3225, 3225, 17082323462351481), (3226, 3226, 17253146696974995), (3227, 3227, 17425678163944745), (3228, 3228, 17599934945584193), (3229, 3229, 17775934295040035), (3230, 3230, 17953693637990435), (3231, 3231, 18133230574370339), (3232, 3232, 18314562880114043), (3233, 3233, 18497708508915183), (3234, 3234, 18682685594004335), (3235, 3235, 18869512449944378), (3236, 3236, 19058207574443822), (3237, 3237, 19248789650188260), (3238, 3238, 19441277546690143), (3239, 3239, 19635690322157045), (3240, 3240, 19832047225378615), (3241, 3241, 20030367697632401), (3242, 3242, 20230671374608725), (3243, 3243, 20432978088354812), (3244, 3244, 20637307869238360), (3245, 3245, 20843680947930744), (3246, 3246, 21052117757410051), (3247, 3247, 21262638934984152), (3248, 3248, 21475265324333994), (3249, 3249, 21690017977577333), (3250, 3250, 21906918157353107), (3251, 3251, 22125987338926638), (3252, 3252, 22347247212315904), (3253, 3253, 22570719684439063), (3254, 3254, 22796426881283454), (3255, 3255, 23024391150096288), (3256, 3256, 23254635061597251), (3257, 3257, 23487181412213224), (3258, 3258, 23722053226335356), (3259, 3259, 23959273758598710), (3260, 3260, 24198866496184697), (3261, 3261, 24440855161146544), (3262, 3262, 24685263712758009), (3263, 3263, 24932116349885589), (3264, 3264, 25181437513384445), (3265, 3265, 25433251888518289), (3266, 3266, 25687584407403472), (3267, 3267, 25944460251477507), (3268, 3268, 26203904853992282), (3269, 3269, 26465943902532205), (3270, 3270, 26730603341557527), (3271, 3271, 26997909374973102), (3272, 3272, 27267888468722833), (3273, 3273, 27540567353410062), (3274, 3274, 27815973026944162), (3275, 3275, 28094132757213604), (3276, 3276, 28375074084785740), (3277, 3277, 28658824825633597), (3278, 3278, 28945413073889933), (3279, 3279, 29234867204628833), (3280, 3280, 29527215876675121), (3281, 3281, 29822488035441872), (3282, 3282, 30120712915796291), (3283, 3283, 30421920044954254), (3284, 3284, 30726139245403796), (3285, 3285, 31033400637857834), (3286, 3286, 31343734644236413), (3287, 3287, 31657171990678777), (3288, 3288, 31973743710585564), (3289, 3289, 32293481147691420), (3290, 3290, 32616415959168334), (3291, 3291, 32942580118760018), (3292, 3292, 33272005919947618), (3293, 3293, 33604725979147094), (3294, 3294, 33940773238938565), (3295, 3295, 34280180971327951), (3296, 3296, 34622982781041230), (3297, 3297, 34969212608851642), (3298, 3298, 35318904734940159), (3299, 3299, 35672093782289560), (3300, 3300, 36028814720112456), (3301, 3301, 36389102867313580), (3302, 3302, 36752993895986716), (3303, 3303, 37120523834946583), (3304, 3304, 37491729073296049), (3305, 3305, 37866646364029010), (3306, 3306, 38245312827669300), (3307, 3307, 38627765955945993), (3308, 3308, 39014043615505453), (3309, 3309, 39404184051660507), (3310, 3310, 39798225892177112), (3311, 3311, 40196208151098883), (3312, 3312, 40598170232609872), (3313, 3313, 41004151934935971), (3314, 3314, 41414193454285331), (3315, 3315, 41828335388828184), (3316, 3316, 42246618742716466), (3317, 3317, 42669084930143631), (3318, 3318, 43095775779445067), (3319, 3319, 43526733537239517), (3320, 3320, 43962000872611913), (3321, 3321, 44401620881338032), (3322, 3322, 44845637090151412), (3323, 3323, 45294093461052926), (3324, 3324, 45747034395663455), (3325, 3325, 46204504739620090), (3326, 3326, 46666549787016291), (3327, 3327, 47133215284886454), (3328, 3328, 47604547437735318), (3329, 3329, 48080592912112672), (3330, 3330, 48561398841233798), (3331, 3331, 49047012829646136), (3332, 3332, 49537482957942598), (3333, 3333, 50032857787522024), (3334, 3334, 50533186365397244), (3335, 3335, 51038518229051216), (3336, 3336, 51548903411341728), (3337, 3337, 52064392445455146), (3338, 3338, 52585036369909697), (3339, 3339, 53110886733608794), (3340, 3340, 53641995600944882), (3341, 3341, 54178415556954331), (3342, 3342, 54720199712523874), (3343, 3343, 55267401709649113), (3344, 3344, 55820075726745604), (3345, 3345, 56378276484013060), (3346, 3346, 56942059248853191), (3347, 3347, 57511479841341723), (3348, 3348, 58086594639755140), (3349, 3349, 58667460586152691), (3350, 3350, 59254135192014218), (3351, 3351, 59846676543934360), (3352, 3352, 60445143309373704), (3353, 3353, 61049594742467441), (3354, 3354, 61660090689892115), (3355, 3355, 62276691596791036), (3356, 3356, 62899458512758947), (3357, 3357, 63528453097886536), (3358, 3358, 64163737628865402), (3359, 3359, 64805375005154056), (3360, 3360, 65453428755205596), (3361, 3361, 66107963042757652), (3362, 3362, 66769042673185229), (3363, 3363, 67436733099917081), (3364, 3364, 68111100430916252), (3365, 3365, 68792211435225414), (3366, 3366, 69480133549577668), (3367, 3367, 70174934885073445), (3368, 3368, 70876684233924179), (3369, 3369, 71585451076263421), (3370, 3370, 72301305587026055), (3371, 3371, 73024318642896316), (3372, 3372, 73754561829325279), (3373, 3373, 74492107447618532), (3374, 3374, 75237028522094717), (3375, 3375, 75989398807315664), (3376, 3376, 76749292795388821), (3377, 3377, 77516785723342709), (3378, 3378, 78291953580576136), (3379, 3379, 79074873116381898), (3380, 3380, 79865621847545717), (3381, 3381, 80664278066021174), (3382, 3382, 81470920846681386), (3383, 3383, 82285630055148199), (3384, 3384, 83108486355699681), (3385, 3385, 83939571219256678), (3386, 3386, 84778966931449245), (3387, 3387, 85626756600763737), (3388, 3388, 86483024166771375), (3389, 3389, 87347854408439089), (3390, 3390, 88221332952523479), (3391, 3391, 89103546282048714), (3392, 3392, 89994581744869201), (3393, 3393, 90894527562317893), (3394, 3394, 91803472837941072), (3395, 3395, 92721507566320483), (3396, 3396, 93648722641983688), (3397, 3397, 94585209868403525), (3398, 3398, 95531061967087560), (3399, 3399, 96486372586758436), (3400, 3400, 97451236312626020), (3401, 3401, 98425748675752280), (3402, 3402, 99410006162509803), (3403, 3403, 100404106224134901), (3404, 3404, 101408147286376250), (3405, 3405, 102422228759240012), (3406, 3406, 103446451046832413), (3407, 3407, 104480915557300737), (3408, 3408, 105525724712873744), (3409, 3409, 106580981960002481), (3410, 3410, 107646791779602506), (3411, 3411, 108723259697398531), (3412, 3412, 109810492294372517), (3413, 3413, 110908597217316242), (3414, 3414, 112017683189489404), (3415, 3415, 113137860021384298), (3416, 3416, 114269238621598141), (3417, 3417, 115411931007814123), (3418, 3418, 116566050317892264), (3419, 3419, 117731710821071186), (3420, 3420, 118909027929281898), (3421, 3421, 120098118208574717), (3422, 3422, 121299099390660465), (3423, 3423, 122512090384567069), (3424, 3424, 123737211288412740), (3425, 3425, 124974583401296867), (3426, 3426, 126224329235309836), (3427, 3427, 127486572527662934), (3428, 3428, 128761438252939564), (3429, 3429, 130049052635468959), (3430, 3430, 131349543161823649), (3431, 3431, 132663038593441885), (3432, 3432, 133989668979376304), (3433, 3433, 135329565669170067), (3434, 3434, 136682861325861768), (3435, 3435, 138049689939120386), (3436, 3436, 139430186838511589), (3437, 3437, 140824488706896705), (3438, 3438, 142232733593965672), (3439, 3439, 143655060929905329), (3440, 3440, 145091611539204382), (3441, 3441, 146542527654596426), (3442, 3442, 148007952931142390), (3443, 3443, 149488032460453814), (3444, 3444, 150982912785058352), (3445, 3445, 152492741912908936), (3446, 3446, 154017669332038025), (3447, 3447, 155557846025358406), (3448, 3448, 157113424485611990), (3449, 3449, 158684558730468109), (3450, 3450, 160271404317772791), (3451, 3451, 161874118360950518), (3452, 3452, 163492859544560024), (3453, 3453, 165127788140005624), (3454, 3454, 166779066021405680), (3455, 3455, 168446856681619737), (3456, 3456, 170131325248435934), (3457, 3457, 171832638500920294), (3458, 3458, 173550964885929497), (3459, 3459, 175286474534788791), (3460, 3460, 177039339280136679), (3461, 3461, 178809732672938046), (3462, 3462, 180597829999667427), (3463, 3463, 182403808299664101), (3464, 3464, 184227846382660742), (3465, 3465, 186070124846487349), (3466, 3466, 187930826094952223), (3467, 3467, 189810134355901745), (3468, 3468, 191708235699460762), (3469, 3469, 193625318056455370), (3470, 3470, 195561571237019924), (3471, 3471, 197517186949390123), (3472, 3472, 199492358818884024), (3473, 3473, 201487282407072864), (3474, 3474, 203502155231143593), (3475, 3475, 205537176783455029), (3476, 3476, 207592548551289579), (3477, 3477, 209668474036802475), (3478, 3478, 211765158777170500), (3479, 3479, 213882810364942205), (3480, 3480, 216021638468591627), (3481, 3481, 218181854853277543), (3482, 3482, 220363673401810319), (3483, 3483, 222567310135828422), (3484, 3484, 224792983237186706), (3485, 3485, 227040913069558573), (3486, 3486, 229311322200254159), (3487, 3487, 231604435422256700), (3488, 3488, 233920479776479267), (3489, 3489, 236259684574244060), (3490, 3490, 238622281419986501), (3491, 3491, 241008504234186366), (3492, 3492, 243418589276528229), (3493, 3493, 245852775169293512), (3494, 3494, 248311302920986447), (3495, 3495, 250794415950196311), (3496, 3496, 253302360109698274), (3497, 3497, 255835383710795257), (3498, 3498, 258393737547903210), (3499, 3499, 260977674923382242), (3500, 3500, 263587451672616064), (3501, 3501, 266223326189342225), (3502, 3502, 268885559451235647), (3503, 3503, 271574415045748003), (3504, 3504, 274290159196205483), (3505, 3505, 277033060788167538), (3506, 3506, 279803391396049214), (3507, 3507, 282601425310009706), (3508, 3508, 285427439563109803), (3509, 3509, 288281713958740901), (3510, 3510, 291164531098328310), (3511, 3511, 294076176409311593), (3512, 3512, 297016938173404709), (3513, 3513, 299987107555138756), (3514, 3514, 302986978630690143), (3515, 3515, 306016848416997045), (3516, 3516, 309077016901167015), (3517, 3517, 312167787070178686), (3518, 3518, 315289464940880472), (3519, 3519, 318442359590289277), (3520, 3520, 321626783186192170), (3521, 3521, 324843051018054092), (3522, 3522, 328091481528234632), (3523, 3523, 331372396343516979), (3524, 3524, 334686120306952149), (3525, 3525, 338032981510021670), (3526, 3526, 341413311325121887), (3527, 3527, 344827444438373106), (3528, 3528, 348275718882756837), (3529, 3529, 351758476071584405), (3530, 3530, 355276060832300249), (3531, 3531, 358828821440623252), (3532, 3532, 362417109655029484), (3533, 3533, 366041280751579779), (3534, 3534, 369701693559095577), (3535, 3535, 373398710494686532), (3536, 3536, 377132697599633398), (3537, 3537, 380904024575629732), (3538, 3538, 384713064821386029), (3539, 3539, 388560195469599889), (3540, 3540, 392445797424295888), (3541, 3541, 396370255398538847), (3542, 3542, 400333957952524236), (3543, 3543, 404337297532049478), (3544, 3544, 408380670507369973), (3545, 3545, 412464477212443672), (3546, 3546, 416589121984568109), (3547, 3547, 420755013204413790), (3548, 3548, 424962563336457928), (3549, 3549, 429212188969822507), (3550, 3550, 433504310859520732), (3551, 3551, 437839353968115940), (3552, 3552, 442217747507797099), (3553, 3553, 446639924982875070), (3554, 3554, 451106324232703821), (3555, 3555, 455617387475030859), (3556, 3556, 460173561349781168), (3557, 3557, 464775296963278979), (3558, 3558, 469423049932911769), (3559, 3559, 474117280432240887), (3560, 3560, 478858453236563296), (3561, 3561, 483647037768928929), (3562, 3562, 488483508146618218), (3563, 3563, 493368343228084400), (3564, 3564, 498302026660365244), (3565, 3565, 503285046926968896), (3566, 3566, 508317897396238585), (3567, 3567, 513401076370200971), (3568, 3568, 518535087133902981), (3569, 3569, 523720438005242011), (3570, 3570, 528957642385294431), (3571, 3571, 534247218809147375), (3572, 3572, 539589690997238849), (3573, 3573, 544985587907211237), (3574, 3574, 550435443786283350), (3575, 3575, 555939798224146183), (3576, 3576, 561499196206387645), (3577, 3577, 567114188168451522), (3578, 3578, 572785330050136037), (3579, 3579, 578513183350637397), (3580, 3580, 584298315184143771), (3581, 3581, 590141298335985209), (3582, 3582, 596042711319345061), (3583, 3583, 602003138432538512), (3584, 3584, 608023169816863897), (3585, 3585, 614103401515032536), (3586, 3586, 620244435530182861), (3587, 3587, 626446879885484690), (3588, 3588, 632711348684339536), (3589, 3589, 639038462171182932), (3590, 3590, 645428846792894761), (3591, 3591, 651883135260823709), (3592, 3592, 658401966613431946), (3593, 3593, 664985986279566265), (3594, 3594, 671635846142361928), (3595, 3595, 678352204603785547), (3596, 3596, 685135726649823403), (3597, 3597, 691987083916321637), (3598, 3598, 698906954755484853), (3599, 3599, 705896024303039702), (3600, 3600, 712954984546070099), (3601, 3601, 720084534391530800), (3602, 3602, 727285379735446108), (3603, 3603, 734558233532800569), (3604, 3604, 741903815868128574), (3605, 3605, 749322854026809860), (3606, 3606, 756816082567077959), (3607, 3607, 764384243392748738), (3608, 3608, 772028085826676226), (3609, 3609, 779748366684942988), (3610, 3610, 787545850351792418), (3611, 3611, 795421308855310342), (3612, 3612, 803375521943863445), (3613, 3613, 811409277163302080), (3614, 3614, 819523369934935101), (3615, 3615, 827718603634284452), (3616, 3616, 835995789670627296), (3617, 3617, 844355747567333569), (3618, 3618, 852799305043006905), (3619, 3619, 861327298093436974), (3620, 3620, 869940571074371343), (3621, 3621, 878639976785115057), (3622, 3622, 887426376552966207), (3623, 3623, 896300640318495869), (3624, 3624, 905263646721680828), (3625, 3625, 914316283188897636), (3626, 3626, 923459446020786613), (3627, 3627, 932694040480994479), (3628, 3628, 942020980885804424), (3629, 3629, 951441190694662468), (3630, 3630, 960955602601609093), (3631, 3631, 970565158627625184), (3632, 3632, 980270810213901435), (3633, 3633, 990073518316040450), (3634, 3634, 999974253499200854), (3635, 3635, 1009973996034192863), (3636, 3636, 1020073735994534791), (3637, 3637, 1030274473354480139), (3638, 3638, 1040577218088024941), (3639, 3639, 1050982990268905190), (3640, 3640, 1061492820171594242), (3641, 3641, 1072107748373310184), (3642, 3642, 1082828825857043286), (3643, 3643, 1093657114115613719), (3644, 3644, 1104593685256769856), (3645, 3645, 1115639622109337555), (3646, 3646, 1126796018330430930), (3647, 3647, 1138063978513735240), (3648, 3648, 1149444618298872592), (3649, 3649, 1160939064481861318), (3650, 3650, 1172548455126679931), (3651, 3651, 1184273939677946730), (3652, 3652, 1196116679074726198), (3653, 3653, 1208077845865473460), (3654, 3654, 1220158624324128194), (3655, 3655, 1232360210567369476), (3656, 3656, 1244683812673043171), (3657, 3657, 1257130650799773603), (3658, 3658, 1269701957307771339), (3659, 3659, 1282398976880849052), (3660, 3660, 1295222966649657543), (3661, 3661, 1308175196316154118), (3662, 3662, 1321256948279315659), (3663, 3663, 1334469517762108816), (3664, 3664, 1347814212939729904), (3665, 3665, 1361292355069127203), (3666, 3666, 1374905278619818475), (3667, 3667, 1388654331406016660), (3668, 3668, 1402540874720076826), (3669, 3669, 1416566283467277595), (3670, 3670, 1430731946301950371), (3671, 3671, 1445039265764969874), (3672, 3672, 1459489658422619573), (3673, 3673, 1474084555006845769), (3674, 3674, 1488825400556914226), (3675, 3675, 1503713654562483369), (3676, 3676, 1518750791108108202), (3677, 3677, 1533938299019189284), (3678, 3678, 1549277682009381177), (3679, 3679, 1564770458829474989), (3680, 3680, 1580418163417769739), (3681, 3681, 1596222345051947436), (3682, 3682, 1612184568502466911), (3683, 3683, 1628306414187491580), (3684, 3684, 1644589478329366496), (3685, 3685, 1661035373112660160), (3686, 3686, 1677645726843786762), (3687, 3687, 1694422184112224630), (3688, 3688, 1711366405953346876), (3689, 3689, 1728480070012880345), (3690, 3690, 1745764870713009148), (3691, 3691, 1763222519420139240), (3692, 3692, 1780854744614340632), (3693, 3693, 1798663292060484038), (3694, 3694, 1816649924981088879), (3695, 3695, 1834816424230899768), (3696, 3696, 1853164588473208765), (3697, 3697, 1871696234357940853), (3698, 3698, 1890413196701520261), (3699, 3699, 1909317328668535464), (3700, 3700, 1928410501955220819), (3701, 3701, 1947694606974773027), (3702, 3702, 1967171553044520757), (3703, 3703, 1986843268574965965), (3704, 3704, 2006711701260715624), (3705, 3705, 2026778818273322780), (3706, 3706, 2047046606456056008), (3707, 3707, 2067517072520616568), (3708, 3708, 2088192243245822734), (3709, 3709, 2109074165678280961), (3710, 3710, 2130164907335063771), (3711, 3711, 2151466556408414409), (3712, 3712, 2172981221972498553), (3713, 3713, 2194711034192223538), (3714, 3714, 2216658144534145774), (3715, 3715, 2238824725979487231), (3716, 3716, 2261212973239282104), (3717, 3717, 2283825102971674925), (3718, 3718, 2306663354001391674), (3719, 3719, 2329729987541405591), (3720, 3720, 2353027287416819647), (3721, 3721, 2376557560290987843), (3722, 3722, 2400323135893897722), (3723, 3723, 2424326367252836699), (3724, 3724, 2448569630925365066), (3725, 3725, 2473055327234618716), (3726, 3726, 2497785880506964904), (3727, 3727, 2522763739312034553), (3728, 3728, 2547991376705154898), (3729, 3729, 2573471290472206447), (3730, 3730, 2599206003376928512), (3731, 3731, 2625198063410697797), (3732, 3732, 2651450044044804775), (3733, 3733, 2677964544485252822), (3734, 3734, 2704744189930105351), (3735, 3735, 2731791631829406404), (3736, 3736, 2759109548147700468), (3737, 3737, 2786700643629177473), (3738, 3738, 2814567650065469247), (3739, 3739, 2842713326566123940), (3740, 3740, 2871140459831785179), (3741, 3741, 2899851864430103031), (3742, 3742, 2928850383074404061), (3743, 3743, 2958138886905148102), (3744, 3744, 2987720275774199583), (3745, 3745, 3017597478531941579), (3746, 3746, 3047773453317260995), (3747, 3747, 3078251187850433605), (3748, 3748, 3109033699728937941), (3749, 3749, 3140124036726227320), (3750, 3750, 3171525277093489593), (3751, 3751, 3203240529864424489), (3752, 3752, 3235272935163068734), (3753, 3753, 3267625664514699421), (3754, 3754, 3300301921159846416), (3755, 3755, 3333304940371444880), (3756, 3756, 3366637989775159329), (3757, 3757, 3400304369672910922), (3758, 3758, 3434307413369640031), (3759, 3759, 3468650487503336431), (3760, 3760, 3503336992378369796), (3761, 3761, 3538370362302153494), (3762, 3762, 3573754065925175029), (3763, 3763, 3609491606584426779), (3764, 3764, 3645586522650271047), (3765, 3765, 3682042387876773757), (3766, 3766, 3718862811755541495), (3767, 3767, 3756051439873096910), (3768, 3768, 3793611954271827879), (3769, 3769, 3831548073814546157), (3770, 3770, 3869863554552691619), (3771, 3771, 3908562190098218535), (3772, 3772, 3947647811999200721), (3773, 3773, 3987124290119192728), (3774, 3774, 4026995533020384655), (3775, 3775, 4067265488350588502), (3776, 3776, 4107938143234094387), (3777, 3777, 4149017524666435330), (3778, 3778, 4190507699913099684), (3779, 3779, 4232412776912230681), (3780, 3780, 4274736904681352987), (3781, 3781, 4317484273728166517), (3782, 3782, 4360659116465448182), (3783, 3783, 4404265707630102664), (3784, 3784, 4448308364706403691), (3785, 3785, 4492791448353467728), (3786, 3786, 4537719362837002405), (3787, 3787, 4583096556465372429), (3788, 3788, 4628927522030026153), (3789, 3789, 4675216797250326415), (3790, 3790, 4721968965222829679), (3791, 3791, 4769188654875057976), (3792, 3792, 4816880541423808556), (3793, 3793, 4865049346838046641), (3794, 3794, 4913699840306427108), (3795, 3795, 4962836838709491379), (3796, 3796, 5012465207096586292), (3797, 3797, 5062589859167552155), (3798, 3798, 5113215757759227677), (3799, 3799, 5164347915336819954), (3800, 3800, 5215991394490188153), (3801, 3801, 5268151308435090035), (3802, 3802, 5320832821519440935), (3803, 3803, 5374041149734635344), (3804, 3804, 5427781561231981698), (3805, 3805, 5482059376844301515), (3806, 3806, 5536879970612744530), (3807, 3807, 5592248770318871975), (3808, 3808, 5648171258022060695), (3809, 3809, 5704652970602281302), (3810, 3810, 5761699500308304115), (3811, 3811, 5819316495311387156), (3812, 3812, 5877509660264501028), (3813, 3813, 5936284756867146038), (3814, 3814, 5995647604435817498), (3815, 3815, 6055604080480175673), (3816, 3816, 6116160121284977430), (3817, 3817, 6177321722497827204), (3818, 3818, 6239094939722805476), (3819, 3819, 6301485889120033531), (3820, 3820, 6364500748011233866), (3821, 3821, 6428145755491346205), (3822, 3822, 6492427213046259667), (3823, 3823, 6557351485176722264), (3824, 3824, 6622925000028489486), (3825, 3825, 6689154250028774381), (3826, 3826, 6756045792529062125), (3827, 3827, 6823606250454352746), (3828, 3828, 6891842312958896274), (3829, 3829, 6960760736088485236), (3830, 3830, 7030368343449370089), (3831, 3831, 7100672026883863790), (3832, 3832, 7171678747152702428), (3833, 3833, 7243395534624229452), (3834, 3834, 7315829489970471746), (3835, 3835, 7388987784870176464), (3836, 3836, 7462877662718878228), (3837, 3837, 7537506439346067011), (3838, 3838, 7612881503739527681), (3839, 3839, 7689010318776922958), (3840, 3840, 7765900421964692187), (3841, 3841, 7843559426184339109), (3842, 3842, 7921995020446182500), (3843, 3843, 8001214970650644325), (3844, 3844, 8081227120357150768), (3845, 3845, 8162039391560722276), (3846, 3846, 8243659785476329499), (3847, 3847, 8326096383331092794), (3848, 3848, 8409357347164403722), (3849, 3849, 8493450920636047759), (3850, 3850, 8578385429842408237), (3851, 3851, 8664169284140832319), (3852, 3852, 8750810976982240642), (3853, 3853, 8838319086752063049), (3854, 3854, 8926702277619583679), (3855, 3855, 9015969300395779516), (3856, 3856, 9106128993399737311), (3857, 3857, 9197190283333734684), (3858, 3858, 9289162186167072031), (3859, 3859, 9382053808028742751), (3860, 3860, 9475874346109030179), (3861, 3861, 9570633089570120480), (3862, 3862, 9666339420465821685), (3863, 3863, 9763002814670479902), (3864, 3864, 9860632842817184701), (3865, 3865, 9959239171245356548), (3866, 3878, 9961241799803157873), (3879, 3879, 9864598842628203403), (3880, 3880, 9766929547156637032), (3881, 3881, 9670227274412511913), (3882, 3882, 9574482449913378132), (3883, 3883, 9479685593973641715), (3884, 3884, 9385827320765981896), (3885, 3885, 9292898337392061283), (3886, 3886, 9200889442962436914), (3887, 3887, 9109791527685581103), (3888, 3888, 9019595571965921884), (3889, 3889, 8930292645510813746), (3890, 3890, 8841873906446350244), (3891, 3891, 8754330600441930935), (3892, 3892, 8667654059843495975), (3893, 3893, 8581835702815342549), (3894, 3894, 8496867032490438168), (3895, 3895, 8412739636129146701), (3896, 3896, 8329445184286283862), (3897, 3897, 8246975429986419666), (3898, 3898, 8165322207907346203), (3899, 3899, 8084477433571629904), (3900, 3900, 8004433102546168222), (3901, 3901, 7925181289649671507), (3902, 3902, 7846714148167991591), (3903, 3903, 7769023909077219397), (3904, 3904, 7692102880274474651), (3905, 3905, 7615943445816311535), (3906, 3906, 7540538065164664887), (3907, 3907, 7465879272440262264), (3908, 3908, 7391959675683427984), (3909, 3909, 7318771956122205925), (3910, 3910, 7246308867447728638), (3911, 3911, 7174563235096761028), (3912, 3912, 7103527955541347553), (3913, 3913, 7033195995585492626), (3914, 3914, 6963560391668804581), (3915, 3915, 6894614249177034238), (3916, 3916, 6826350741759439840), (3917, 3917, 6758763110652910733), (3918, 3918, 6691844664012782904), (3919, 3919, 6625588776250280102), (3920, 3920, 6559988887376514953), (3921, 3921, 6495038502352985102), (3922, 3922, 6430731190448500101), (3923, 3923, 6367060584602475347), (3924, 3924, 6304020380794530047), (3925, 3925, 6241604337420326779), (3926, 3926, 6179806274673590871), (3927, 3927, 6118620073934248387), (3928, 3928, 6058039677162622165), (3929, 3929, 5998059086299625906), (3930, 3930, 5938672362672896937), (3931, 3931, 5879873626408808848), (3932, 3932, 5821657055850305790), (3933, 3933, 5764016886980500782), (3934, 3934, 5706947412851980973), (3935, 3935, 5650442983021763339), (3936, 3936, 5594498002991844890), (3937, 3937, 5539106933655291971), (3938, 3938, 5484264290747813832), (3939, 3939, 5429964644304766171), (3940, 3940, 5376202618123530862), (3941, 3941, 5322972889231218675), (3942, 3942, 5270270187357642253), (3943, 3943, 5218089294413507181), (3944, 3944, 5166425043973769486), (3945, 3945, 5115272320766108402), (3946, 3946, 5064626060164463764), (3947, 3947, 5014481247687587886), (3948, 3948, 4964832918502562263), (3949, 3949, 4915676156933229963), (3950, 3950, 4867006095973495013), (3951, 3951, 4818817916805440607), (3952, 3952, 4771106848322218423), (3953, 3953, 4723868166655661805), (3954, 3954, 4677097194708576044), (3955, 3955, 4630789301691659450), (3956, 3956, 4584939902665009356), (3957, 3957, 4539544458084167680), (3958, 3958, 4494598473350661069), (3959, 3959, 4450097498366991157), (3960, 3960, 4406037127096030849), (3961, 3961, 4362412997124783019), (3962, 3962, 4319220789232458434), (3963, 3963, 4276456226962830133), (3964, 3964, 4234115076200821914), (3965, 3965, 4192193144753289024), (3966, 3966, 4150686281933949528), (3967, 3967, 4109590378152425276), (3968, 3968, 4068901364507351758), (3969, 3969, 4028615212383516592), (3970, 3970, 3988727933052986725), (3971, 3971, 3949235577280184876), (3972, 3972, 3910134234930876115), (3973, 3973, 3871420034585025856), (3974, 3974, 3833089143153490947), (3975, 3975, 3795137765498505888), (3976, 3976, 3757562144057926622), (3977, 3977, 3720358558473194675), (3978, 3978, 3683523325220984827), (3979, 3979, 3647052797248499829), (3980, 3980, 3610943363612376068), (3981, 3981, 3575191449121164424), (3982, 3982, 3539793513981350915), (3983, 3983, 3504746053446882094), (3984, 3984, 3470045597472160489), (3985, 3985, 3435688710368475731), (3986, 3986, 3401671990463837358), (3987, 3987, 3367992069766175602), (3988, 3988, 3334645613629876834), (3989, 3989, 3301629320425620627), (3990, 3990, 3268939921213485770), (3991, 3991, 3236574179419292841), (3992, 3992, 3204528890514151328), (3993, 3993, 3172800881697179533), (3994, 3994, 3141387011581365874), (3995, 3995, 3110284169882540469), (3996, 3996, 3079489277111426207), (3997, 3997, 3048999284268738819), (3998, 3998, 3018811172543305761), (3999, 3999, 2988921953013174021), (4000, 4000, 2959328666349677249), (4001, 4001, 2930028382524432919), (4002, 4002, 2901018200519240514), (4003, 4003, 2872295248038851994), (4004, 4004, 2843856681226586133), (4005, 4005, 2815699684382758548), (4006, 4006, 2787821469685899552), (4007, 4007, 2760219276916732230), (4008, 4008, 2732890373184883396), (4009, 4009, 2705832052658300392), (4010, 4010, 2679041636295346923), (4011, 4011, 2652516471579551409), (4012, 4012, 2626253932256981593), (4013, 4013, 2600251418076219399), (4014, 4014, 2574506354530910296), (4015, 4015, 2549016192604861679), (4016, 4016, 2523778408519665029), (4017, 4017, 2498790503484816860), (4018, 4018, 2474050003450313723), (4019, 4019, 2449554458861696755), (4020, 4020, 2425301444417521540), (4021, 4021, 2401288558829229247), (4022, 4022, 2377513424583395294), (4023, 4023, 2353973687706331975), (4024, 4024, 2330667017531021757), (4025, 4025, 2307591106466358175), (4026, 4026, 2284743669768671461), (4027, 4027, 2262122445315516298), (4028, 4028, 2239725193381699305), (4029, 4029, 2217549696417524064), (4030, 4030, 2195593758829231747), (4031, 4031, 2173855206761615591), (4032, 4032, 2152331887882787714), (4033, 4033, 2131021671171076944), (4034, 4034, 2109922446704036578), (4035, 4035, 2089032125449541167), (4036, 4036, 2068348639058951650), (4037, 4037, 2047869939662328367), (4038, 4038, 2027593999665671650), (4039, 4039, 2007518811550169951), (4040, 4040, 1987642387673435595), (4041, 4041, 1967962760072708510), (4042, 4042, 1948477980270008425), (4043, 4043, 1929186119079216263), (4044, 4044, 1910085266415065607), (4045, 4045, 1891173531104025353), (4046, 4046, 1872449040697054805), (4047, 4047, 1853909941284212678), (4048, 4048, 1835554397311101662), (4049, 4049, 1817380591397130358), (4050, 4050, 1799386724155574612), (4051, 4051, 1781571014015420408), (4052, 4052, 1763931697044970701), (4053, 4053, 1746467026777198714), (4054, 4054, 1729175274036830410), (4055, 4055, 1712054726769139020), (4056, 4056, 1695103689870434673), (4057, 4057, 1678320485020232349), (4058, 4058, 1661703450515081534), (4059, 4059, 1645250941104041123), (4060, 4060, 1628961327825783290), (4061, 4061, 1612832997847310188), (4062, 4062, 1596864354304267513), (4063, 4063, 1581053816142839122), (4064, 4064, 1565399817963207051), (4065, 4065, 1549900809864561437), (4066, 4066, 1534555257291644987), (4067, 4067, 1519361640882816819), (4068, 4068, 1504318456319620613), (4069, 4069, 1489424214177842191), (4070, 4070, 1474677439780041773), (4071, 4071, 1460076673049546310), (4072, 4072, 1445620468365887436), (4073, 4073, 1431307394421670728), (4074, 4074, 1417136034080862107), (4075, 4075, 1403104984238477334), (4076, 4076, 1389212855681660727), (4077, 4077, 1375458272952139333), (4078, 4078, 1361839874210038944), (4079, 4079, 1348356311099048459), (4080, 4080, 1335006248612919267), (4081, 4081, 1321788364963286403), (4082, 4082, 1308701351448798418), (4083, 4083, 1295743912325542989), (4084, 4084, 1282914764678755434), (4085, 4085, 1270212638295797460), (4086, 4086, 1257636275540393524), (4087, 4087, 1245184431228112400), (4088, 4088, 1232855872503081584), (4089, 4089, 1220649378715922361), (4090, 4090, 1208563741302893427), (4091, 4091, 1196597763666231115), (4092, 4092, 1184750261055674372), (4093, 4093, 1173020060451162744), (4094, 4094, 1161406000446695786), (4095, 4095, 1149906931135342363), (4096, 4096, 1138521713995388478), (4097, 4097, 1127249221777612355), (4098, 4098, 1116088338393675599), (4099, 4099, 1105037958805619405), (4100, 4100, 1094096988916454856), (4101, 4101, 1083264345461836491), (4102, 4102, 1072538955902808407), (4103, 4103, 1061919758319612284), (4104, 4104, 1051405701306546816), (4105, 4105, 1040995743867868135), (4106, 4106, 1030688855314720925), (4107, 4107, 1020484015163090025), (4108, 4108, 1010380213032762401), (4109, 4109, 1000376448547289506), (4110, 4110, 990471731234940105), (4111, 4111, 980665080430633767), (4112, 4112, 970955525178845314), (4113, 4113, 961342104137470608), (4114, 4114, 951823865482644167), (4115, 4115, 942399866814499175), (4116, 4116, 933069175063860569), (4117, 4117, 923830866399861950), (4118, 4118, 914684026138477178), (4119, 4119, 905627748651957602), (4120, 4120, 896661137279165942), (4121, 4121, 887783304236797963), (4122, 4122, 878993370531483131), (4123, 4123, 870290465872755576), (4124, 4124, 861673728586886709), (4125, 4125, 853142305531570999), (4126, 4126, 844695352011456434), (4127, 4127, 836332031694511321), (4128, 4128, 828051516529219130), (4129, 4129, 819852986662593198), (4130, 4130, 811735630359003166), (4131, 4131, 803698643919805115), (4132, 4132, 795741231603767441), (4133, 4133, 787862605548284595), (4134, 4134, 780061985691370886), (4135, 4135, 772338599694426620), (4136, 4136, 764691682865768930), (4137, 4137, 757120478084919733), (4138, 4138, 749624235727643300), (4139, 4139, 742202213591726040), (4140, 4140, 734853676823491128), (4141, 4141, 727577897845040721), (4142, 4142, 720374156282218536), (4143, 4143, 713241738893285679), (4144, 4144, 706179939498302652), (4145, 4145, 699188058909210547), (4146, 4146, 692265404860604502), (4147, 4147, 685411291941192576), (4148, 4148, 678625041525933244), (4149, 4149, 671905981708844796), (4150, 4150, 665253447236479996), (4151, 4151, 658666779442059402), (4152, 4152, 652145326180256834), (4153, 4153, 645688441762630528), (4154, 4154, 639295486893693592), (4155, 4155, 632965828607617418), (4156, 4156, 626698840205561800), (4157, 4157, 620493901193625545), (4158, 4158, 614350397221411430), (4159, 4159, 608267720021199436), (4160, 4160, 602245267347722214), (4161, 4161, 596282442918536846), (4162, 4162, 590378656354986976), (4163, 4163, 584533323123749481), (4164, 4164, 578745864478959882), (4165, 4165, 573015707404910774), (4166, 4166, 567342284559317598), (4167, 4167, 561725034217146137), (4168, 4168, 556163400214996175), (4169, 4169, 550656831896035817), (4170, 4170, 545204784055481007), (4171, 4171, 539806716886614858), (4172, 4172, 534462095927341444), (4173, 4173, 529170392007268756), (4174, 4174, 523931081195315600), (4175, 4175, 518743644747837228), (4176, 4176, 513607569057264582), (4177, 4177, 508522345601252062), (4178, 4178, 503487470892328774), (4179, 4179, 498502446428048291), (4180, 4180, 493566778641631971), (4181, 4181, 488679978853100962), (4182, 4182, 483841563220892041), (4183, 4183, 479051052693952516), (4184, 4184, 474307972964309422), (4185, 4185, 469611854420108339), (4186, 4186, 464962232099117167), (4187, 4187, 460358645642690264), (4188, 4188, 455800639250188381), (4189, 4189, 451287761633849882), (4190, 4190, 446819565974108794), (4191, 4191, 442395609875355241), (4192, 4192, 438015455322133902), (4193, 4193, 433678668635776141), (4194, 4194, 429384820431461526), (4195, 4195, 425133485575704481), (4196, 4196, 420924243144261862), (4197, 4197, 416756676380457289), (4198, 4198, 412630372653918108), (4199, 4199, 408544923419720899), (4200, 4200, 404499924177941485), (4201, 4201, 400494974433605430), (4202, 4202, 396529677657035079), (4203, 4203, 392603641244589188), (4204, 4204, 388716476479791275), (4205, 4205, 384867798494842846), (4206, 4206, 381057226232517670), (4207, 4207, 377284382408433336), (4208, 4208, 373548893473696373), (4209, 4209, 369850389577917201), (4210, 4210, 366188504532591288), (4211, 4211, 362562875774842859), (4212, 4212, 358973144331527583), (4213, 4213, 355418954783690677), (4214, 4214, 351899955231376907), (4215, 4215, 348415797258789017), (4216, 4216, 344966135899791106), (4217, 4217, 341550629603753571), (4218, 4218, 338168940201736208), (4219, 4219, 334820732873006147), (4220, 4220, 331505676111887274), (4221, 4221, 328223441694937895), (4222, 4222, 324973704648453362), (4223, 4223, 321756143216290457), (4224, 4224, 318570438828010354), (4225, 4225, 315416276067336984), (4226, 4226, 312293342640927707), (4227, 4227, 309201329347453175), (4228, 4228, 306139930046983342), (4229, 4229, 303108841630676576), (4230, 4230, 300107763990768887), (4231, 4231, 297136399990860284), (4232, 4232, 294194455436495331), (4233, 4233, 291281639046034981), (4234, 4234, 288397662421816813), (4235, 4235, 285542240021600805), (4236, 4236, 282715089130297827), (4237, 4237, 279915929831978046), (4238, 4238, 277144484982156481), (4239, 4239, 274400480180352952), (4240, 4240, 271683643742923715), (4241, 4241, 268993706676162094), (4242, 4242, 266330402649665439), (4243, 4243, 263693467969965782), (4244, 4244, 261082641554421566), (4245, 4245, 258497664905367887), (4246, 4246, 255938282084522660), (4247, 4247, 253404239687646198), (4248, 4248, 250895286819451682), (4249, 4249, 248411175068764041), (4250, 4250, 245951658483924793), (4251, 4251, 243516493548440389), (4252, 4252, 241105439156871673), (4253, 4253, 238718256590962052), (4254, 4254, 236354709496002032), (4255, 4255, 234014563857427754), (4256, 4256, 231697587977651242), (4257, 4257, 229403552453120041), (4258, 4258, 227132230151604001), (4259, 4259, 224883396189706932), (4260, 4260, 222656827910600923), (4261, 4261, 220452304861981112), (4262, 4262, 218269608774238725), (4263, 4263, 216108523538850222), (4264, 4264, 213968835186980418), (4265, 4265, 211850331868297444), (4266, 4266, 209752803829997469), (4267, 4267, 207676043396037098), (4268, 4268, 205619844946571384), (4269, 4269, 203584004897595430), (4270, 4270, 201568321680787554), (4271, 4271, 199572595723552034), (4272, 4272, 197596629429259440), (4273, 4273, 195640227157682614), (4274, 4274, 193703195205626350), (4275, 4275, 191785341787748861), (4276, 4276, 189886477017573130), (4277, 4277, 188006412888686267), (4278, 4278, 186144963256125017), (4279, 4279, 184301943817945562), (4280, 4280, 182477172096975804), (4281, 4281, 180670467422748320), (4282, 4282, 178881650913612198), (4283, 4283, 177110545459021979), (4284, 4284, 175356975702001959), (4285, 4285, 173620768021784118), (4286, 4286, 171901750516617939), (4287, 4287, 170199752986750434), (4288, 4288, 168514606917574687), (4289, 4289, 166846145462945235), (4290, 4290, 165194203428658649), (4291, 4291, 163558617256097672), (4292, 4292, 161939225006037299), (4293, 4293, 160335866342611187), (4294, 4294, 158748382517436819), (4295, 4295, 157176616353897840), (4296, 4296, 155620412231582020), (4297, 4297, 154079616070873287), (4298, 4298, 152554075317696324), (4299, 4299, 151043638928412202), (4300, 4300, 149548157354863566), (4301, 4301, 148067482529567888), (4302, 4302, 146601467851057314), (4303, 4303, 145149968169363678), (4304, 4304, 143712839771647206), (4305, 4305, 142289940367967530), (4306, 4306, 140881129077195575), (4307, 4307, 139486266413064925), (4308, 4308, 138105214270361312), (4309, 4309, 136737835911248824), (4310, 4310, 135383995951731509), (4311, 4311, 134043560348249019), (4312, 4312, 132716396384404969), (4313, 4313, 131402372657826702), (4314, 4314, 130101359067155150), (4315, 4315, 128813226799163515), (4316, 4316, 127537848316003481), (4317, 4317, 126275097342577703), (4318, 4318, 125024848854037330), (4319, 4319, 123786979063403297), (4320, 4320, 122561365409310195), (4321, 4321, 121347886543871480), (4322, 4322, 120146422320664832), (4323, 4323, 118956853782836467), (4324, 4324, 117779063151323235), (4325, 4325, 116612933813191322), (4326, 4326, 115458350310090418), (4327, 4327, 114315198326822196), (4328, 4328, 113183364680021976), (4329, 4329, 112062737306952452), (4330, 4330, 110953205254408368), (4331, 4331, 109854658667731057), (4332, 4332, 108766988779931740), (4333, 4333, 107690087900922515), (4334, 4334, 106623849406853975), (4335, 4335, 105568167729558391), (4336, 4336, 104522938346097417), (4337, 4337, 103488057768413284), (4338, 4338, 102463423533082460), (4339, 4339, 101448934191170752), (4340, 4340, 100444489298188863), (4341, 4341, 99449989404147389), (4342, 4342, 98465336043710287), (4343, 4343, 97490431726445828), (4344, 4344, 96525179927174087), (4345, 4345, 95569485076409988), (4346, 4346, 94623252550900978), (4347, 4347, 93686388664258394), (4348, 4348, 92758800657681578), (4349, 4349, 91840396690773840), (4350, 4350, 90931085832449346), (4351, 4351, 90030778051930046), (4352, 7209, 89139384209831729)]

def glob1 : ℕ := 9961241799803157873

def runs2 : List (ℕ × ℕ × ℕ) := [(0, 3865, 0), (3866, 3878, 34160637173536206697), (3879, 3879, 33829214137956801791), (3880, 3880, 33494271423719605734), (3881, 3881, 33162644973979807657), (3882, 3882, 32834301954435453126), (3883, 3883, 32509209855876686263), (3884, 3884, 32187336490967016102), (3885, 3885, 31868649991056451586), (3886, 3886, 31553118803026189689), (3887, 3887, 31240711686164544247), (3888, 3888, 30931397709073806185), (3889, 3889, 30625146246607728896), (3890, 3890, 30321926976839335541), (3891, 3891, 30021709878058748060), (3892, 3892, 29724465225800740654), (3893, 3893, 29430163589901723419), (3894, 3894, 29138775831585864772), (3895, 3895, 28850273100580064130), (3896, 3896, 28564626832257489238), (3897, 3897, 28281808744809395285), (3898, 3898, 28001790836444945827), (3899, 3899, 27724545382618758245), (3900, 3900, 27450044933285899252), (3901, 3901, 27178262310184058665), (3902, 3902, 26909170604142632342), (3903, 3903, 26642743172418447863), (3904, 3904, 26378953636057869172), (3905, 3905, 26117775877285018982), (3906, 3906, 25859184036915860378), (3907, 3907, 25603152511797881562), (3908, 3908, 25349655952275130260), (3909, 3909, 25098669259678346792), (3910, 3910, 24850167583839947319), (3911, 3911, 24604126320633611207), (3912, 3912, 24360521109538228917), (3913, 3913, 24119327831225969225), (3914, 3914, 23880522605174226956), (3915, 3915, 23644081787301214808), (3916, 3916, 23409981967624965156), (3917, 3917, 23178199967945510056), (3918, 3918, 22948712839550009956), (3919, 3919, 22721497860940603917), (3920, 3920, 22496532535584756353), (3921, 3921, 22273794589687877577), (3922, 3922, 22053261969987997601), (3923, 3923, 21834912841572274853), (3924, 3924, 21618725585715123617), (3925, 3925, 21404678797737746155), (3926, 3926, 21192751284888857579), (3927, 3927, 20982922064246393643), (3928, 3928, 20775170360639993706), (3929, 3929, 20569475604594053174), (3930, 3930, 20365817430291141757), (3931, 3931, 20164175673555585898), (3932, 3932, 19964530369857015740), (3933, 3933, 19766861752333678951), (3934, 3934, 19571150249835325694), (3935, 3935, 19377376484985470984), (3936, 3936, 19185521272262842558), (3937, 3937, 18995565616101824315), (3938, 3938, 18807490709011707243), (3939, 3939, 18621277929714561627), (3940, 3940, 18436908841301546165), (3941, 3941, 18254365189407471450), (3942, 3942, 18073628900403437080), (3943, 3943, 17894682079607363445), (3944, 3944, 17717507009512241035), (3945, 3945, 17542086148031921817), (3946, 3946, 17368402126764279026), (3947, 3947, 17196437749271563393), (3948, 3948, 17026175989377785537), (3949, 3949, 16857599989482955977), (3950, 3950, 16690693058894015819), (3951, 3951, 16525438672172292890), (3952, 3952, 16361820467497319693), (3953, 3953, 16199822245046851182), (3954, 3954, 16039427965392921962), (3955, 3955, 15880621747913784121), (3956, 3956, 15723387869221568436), (3957, 3957, 15567710761605513303), (3958, 3958, 15413575011490607231), (3959, 3959, 15260965357911492308), (3960, 3960, 15109866691001477533), (3961, 3961, 14960264050496512409), (3962, 3962, 14812142624253972682), (3963, 3963, 14665487746786111566), (3964, 3964, 14520284897808031254), (3965, 3965, 14376519700800030944), (3966, 3966, 14234177921584189054), (3967, 3967, 14093245466915038667), (3968, 3968, 13953708383084196700), (3969, 3969, 13815552854538808614), (3970, 3970, 13678765202513671895), (3971, 3971, 13543331883676902866), (3972, 3972, 13409239488789012739), (3973, 3973, 13276474741375260137), (3974, 3974, 13145024496411148651), (3975, 3975, 13014875739020939258), (3976, 3976, 12886015583189048771), (3977, 3977, 12758431270484206704), (3978, 3978, 12632110168796244261), (3979, 3979, 12507039771085390357), (3980, 3980, 12383207694143950849), (3981, 3981, 12260601677370248365), (3982, 3982, 12139209581554701352), (3983, 3983, 12019019387677922131), (3984, 3984, 11900019195720714981), (3985, 3985, 11782197223485856417), (3986, 3986, 11665541805431541007), (3987, 3987, 11550041391516377234), (3988, 3988, 11435684546055819044), (3989, 3989, 11322459946589919845), (3990, 3990, 11210356382762296877), (3991, 3991, 11099362755210194927), (3992, 3992, 10989468074465539532), (3993, 3993, 10880661459866870824), (3994, 3994, 10772932138482050321), (3995, 3995, 10666269444041633981), (3996, 3996, 10560662815882805922), (3997, 3997, 10456101797903768239), (3998, 3998, 10352576037528483405), (3999, 3999, 10250075284681666738), (4000, 4000, 10148589390773927463), (4001, 4001, 10048108307696957884), (4002, 4002, 9948622086828671173), (4003, 4003, 9850120878048189280), (4004, 4004, 9752594928760583445), (4005, 4005, 9656034582931270738), (4006, 4006, 9560430280129971028), (4007, 4007, 9465772554584129730), (4008, 4008, 9372052034241712604), (4009, 4009, 9279259439843279806), (4010, 4010, 9187385584003247333), (4011, 4011, 9096421370300244884), (4012, 4012, 9006357792376480083), (4013, 4013, 8917185933046019884), (4014, 4014, 8828896963411900876), (4015, 4015, 8741482141991981065), (4016, 4016, 8654932813853446599), (4017, 4017, 8569240409755887722), (4018, 4018, 8484396445302859131), (4019, 4019, 8400392520101840723), (4020, 4020, 8317220316932515568), (4021, 4021, 8234871600923282740), (4022, 4022, 8153338218735923505), (4023, 4023, 8072612097758340104), (4024, 4024, 7992685245305287232), (4025, 4025, 7913549747827017061), (4026, 4026, 7835197770125759467), (4027, 4027, 7757621554579959868), (4028, 4028, 7680813420376197889), (4029, 4029, 7604765762748710781), (4030, 4030, 7529471052226446318), (4031, 4031, 7454921833887570612), (4032, 4032, 7381110726621357041), (4033, 4033, 7308030422397383209), (4034, 4034, 7235673685541963574), (4035, 4035, 7164033352021746113), (4036, 4036, 7093102328734402092), (4037, 4037, 7022873592806338705), (4038, 4038, 6953340190897365054), (4039, 4039, 6884495238512242628), (4040, 4040, 6816331919319052107), (4041, 4041, 6748843484474309017), (4042, 4042, 6682023251954761403), (4043, 4043, 6615864605895803369), (4044, 4044, 6550360995936438979), (4045, 4045, 6485505936570731662), (4046, 4046, 6421293006505674913), (4047, 4047, 6357715848025420706), (4048, 4048, 6294768166361802679), (4049, 4049, 6232443729071091762), (4050, 4050, 6170736365416922537), (4051, 4051, 6109639965759329244), (4052, 4052, 6049148480949830935), (4053, 4053, 5989255921732505876), (4054, 4054, 5929956358150995917), (4055, 4055, 5871243918961382096), (4056, 4056, 5813112791050873362), (4057, 4057, 5755557218862250854), (4058, 4058, 5698571503824010746), (4059, 4059, 5642150003786149254), (4060, 4060, 5586287132461533915), (4061, 4061, 5530977358872805856), (4062, 4062, 5476215206804758273), (4063, 4063, 5421995254262136904), (4064, 4064, 5368312132932808816), (4065, 4065, 5315160527656246353), (4066, 4066, 5262535175897273616), (4067, 4067, 5210430867225023383), (4068, 4068, 5158842442797052854), (4069, 4069, 5107764794848567182), (4070, 4070, 5057192866186700180), (4071, 4071, 5007121649689802159), (4072, 4072, 4957546187811685306), (4073, 4073, 4908461572090777531), (4074, 4074, 4859862942664136169), (4075, 4075, 4811745487786273434), (4076, 4076, 4764104443352745975), (4077, 4077, 4716935092428461361), (4078, 4078, 4670232764780654813), (4079, 4079, 4623992836416489914), (4080, 4080, 4578210729125237539), (4081, 4081, 4532881910024987662), (4082, 4082, 4488001891113849170), (4083, 4083, 4443566228825593238), (4084, 4084, 4399570523589696275), (4085, 4085, 4356010419395738886), (4086, 4086, 4312881603362117709), (4087, 4087, 4270179805309027435), (4088, 4088, 4227900797335670728), (4089, 4089, 4186040393401654186), (4090, 4090, 4144594448912528897), (4091, 4091, 4103558860309434551), (4092, 4092, 4062929564662806486), (4093, 4093, 4022702539270105432), (4094, 4094, 3982873801257530131), (4095, 4095, 3943439407185673397), (4096, 4096, 3904395452659082571), (4097, 4097, 3865738071939685714), (4098, 4098, 3827463437564045261), (4099, 4099, 3789567759964401249), (4100, 4100, 3752047287093466583), (4101, 4101, 3714898304052937211), (4102, 4102, 3678117132725680407), (4103, 4103, 3641700131411564759), (4104, 4104, 3605643694466895801), (4105, 4105, 3569944251947421585), (4106, 4106, 3534598269254872857), (4107, 4107, 3499602246787002829), (4108, 4108, 3464952719591091909), (4109, 4109, 3430646257020883079), (4110, 4110, 3396679462396913939), (4111, 4111, 3363048972670211821), (4112, 4112, 3329751458089318635), (4113, 4113, 3296783621870612510), (4114, 4114, 3264142199871893574), (4115, 4115, 3231823960269201558), (4116, 4116, 3199825703236833226), (4117, 4117, 3168144260630527947), (4118, 4118, 3136776495673790046), (4119, 4119, 3105719302647316877), (4120, 4120, 3074969606581501859), (4121, 4121, 3044524362951982038), (4122, 4122, 3014380557378200038), (4123, 4123, 2984535205324950533), (4124, 4124, 2954985351806881716), (4125, 4125, 2925728071095922491), (4126, 4126, 2896760466431606426), (4127, 4127, 2868079669734263789), (4128, 4128, 2839682841321053256), (4129, 4129, 2811567169624805204), (4130, 4130, 2783729870915648717), (4131, 4131, 2756168189025394769), (4132, 4132, 2728879395074648286), (4133, 4133, 2701860787202622066), (4134, 4134, 2675109690299625808), (4135, 4135, 2648623455742203770), (4136, 4136, 2622399461130894822), (4137, 4137, 2596435110030588932), (4138, 4138, 2570727831713454388), (4139, 4139, 2545275080904410286), (4140, 4140, 2520074337529119095), (4141, 4141, 2495123106464474351), (4142, 4142, 2470418917291558763), (4143, 4143, 2445959324051048281), (4144, 4144, 2421741905001037902), (4145, 4145, 2397764262377265249), (4146, 4146, 2374024022155708168), (4147, 4147, 2350518833817532839), (4148, 4148, 2327246370116369148), (4149, 4149, 2304204326847890245), (4150, 4150, 2281390422621673510), (4151, 4151, 2258802398635320307), (4152, 4152, 2236438018450812185), (4153, 4153, 2214295067773081371), (4154, 4154, 2192371354230773635), (4155, 4155, 2170664707159181817), (4156, 4156, 2149172977385328532), (4157, 4157, 2127894037015176764), (4158, 4158, 2106825779222947291), (4159, 4159, 2085966118042522070), (4160, 4160, 2065312988160912941), (4161, 4161, 2044864344713775189), (4162, 4162, 2024618163082945732), (4163, 4163, 2004572438695985873), (4164, 4164, 1984725186827708785), (4165, 4165, 1965074442403672065), (4166, 4166, 1945618259805615906), (4167, 4167, 1926354712678827629), (4168, 4168, 1907281893741413494), (4169, 4169, 1888397914595458905), (4170, 4170, 1869700905540058322), (4171, 4171, 1851189015386196358), (4172, 4172, 1832860411273461741), (4173, 4173, 1814713278488575981), (4174, 4174, 1796745820285718793), (4175, 4175, 1778956257708632469), (4176, 4176, 1761342829414487593), (4177, 4177, 1743903791499492666), (4178, 4178, 1726637417326230362), (4179, 4179, 1709541997352703329), (4180, 4180, 1692615838963072603), (4181, 4181, 1675857266300071884), (4182, 4182, 1659264620099081074), (4183, 4183, 1642836257523842647), (4184, 4184, 1626570552003804601), (4185, 4185, 1610465893073073862), (4186, 4186, 1594520686210964220), (4187, 4187, 1578733352684122990), (4188, 4188, 1563102329390220783), (4189, 4189, 1547626068703188894), (4190, 4190, 1532303038319989004), (4191, 4191, 1517131721108900004), (4192, 4192, 1502110614959306934), (4193, 4193, 1487238232632977163), (4194, 4194, 1472513101616809072), (4195, 4195, 1457933763977038685), (4196, 4196, 1443498776214889787), (4197, 4197, 1429206709123653255), (4198, 4198, 1415056147647181440), (4199, 4199, 1401045690739783604), (4200, 4200, 1387173951227508519), (4201, 4201, 1373439555670800514), (4202, 4202, 1359841144228515360), (4203, 4203, 1346377370523282535), (4204, 4204, 1333046901508200530), (4205, 4205, 1319848417334852010), (4206, 4206, 1306780611222625752), (4207, 4207, 1293842189329332428), (4208, 4208, 1281031870623101414), (4209, 4209, 1268348386755545954), (4210, 4210, 1255790481936184113), (4211, 4211, 1243356912808103082), (4212, 4212, 1231046448324854537), (4213, 4213, 1218857869628568848), (4214, 4214, 1206789969929276087), (4215, 4215, 1194841554385421869), (4216, 4216, 1183011439985566207), (4217, 4217, 1171298455431253670), (4218, 4218, 1159701441021043238), (4219, 4219, 1148219248535686374), (4220, 4220, 1136850741124441954), (4221, 4221, 1125594793192516787), (4222, 4222, 1114450290289620581), (4223, 4223, 1103416128999624337), (4224, 4224, 1092491216831311225), (4225, 4225, 1081674472110209134), (4226, 4226, 1070964823871494192), (4227, 4227, 1060361211753954645), (4228, 4228, 1049862585895004599), (4229, 4229, 1039467906826737227), (4230, 4230, 1029176145373007156), (4231, 4231, 1018986282547531837), (4232, 4232, 1008897309453001819), (4233, 4233, 998908227181189920), (4234, 4234, 989018046714049426), (4235, 4235, 979225788825791511), (4236, 4236, 969530483985932189), (4237, 4237, 959931172263299197), (4238, 4238, 950426903230989304), (4239, 4239, 941016735872266637), (4240, 4240, 931699738487392710), (4241, 4241, 922474988601378921), (4242, 4242, 913341572872652397), (4243, 4243, 904298587002626136), (4244, 4244, 895345135646164491), (4245, 4245, 886480332322935139), (4246, 4246, 877703299329638752), (4247, 4247, 869013167653107675), (4248, 4248, 860409076884265025), (4249, 4249, 851890175132935668), (4250, 4250, 843455618943500662), (4251, 4251, 835104573211386794), (4252, 4252, 826836211100382964), (4253, 4253, 818649713960775212), (4254, 4254, 810544271248292289), (4255, 4255, 802519080443853751), (4256, 4256, 794573346974112625), (4257, 4257, 786706284132784777), (4258, 4258, 778917113002757205), (4259, 4259, 771205062378967530), (4260, 4260, 763569368692047060), (4261, 4261, 756009275932719861), (4262, 4262, 748524035576950357), (4263, 4263, 741112906511832037), (4264, 4264, 733775154962209938), (4265, 4265, 726510054418029641), (4266, 4266, 719316885562405585), (4267, 4267, 712194936200401570), (4268, 4268, 705143501188516406), (4269, 4269, 698161882364867728), (4270, 4270, 691249388480067058), (4271, 4271, 684405335128779265), (4272, 4272, 677629044681959668), (4273, 4273, 670919846219762048), (4274, 4274, 664277075465110939), (4275, 4275, 657700074717931622), (4276, 4276, 651188192790031309), (4277, 4277, 644740784940625059), (4278, 4278, 638357212812500058), (4279, 4279, 632036844368811939), (4280, 4280, 625779053830506870), (4281, 4281, 619583221614363238), (4282, 4282, 613448734271646770), (4283, 4283, 607374984427373040), (4284, 4284, 601361370720171326), (4285, 4285, 595407297742743887), (4286, 4286, 589512175982914740), (4287, 4287, 583675421765262119), (4288, 4288, 577896457193328831), (4289, 4289, 572174710092404783), (4290, 4290, 566509613952876023), (4291, 4291, 560900607874134676), (4292, 4292, 555347136509044233), (4293, 4293, 549848650008954687), (4294, 4294, 544404603969262066), (4295, 4295, 539014459375506996), (4296, 4296, 533677682550006927), (4297, 4297, 528393745099016759), (4298, 4298, 523162123860412633), (4299, 4299, 517982300851893696), (4300, 4300, 512853763219696729), (4301, 4301, 507776003187818543), (4302, 4302, 502748518007741132), (4303, 4303, 497770809908654586), (4304, 4304, 492842386048172857), (4305, 4305, 487962758463537483), (4306, 4306, 483131444023304438), (4307, 4307, 478347964379509345), (4308, 4308, 473611845920306282), (4309, 4309, 468922619723075527), (4310, 4310, 464279821507995571), (4311, 4311, 459682991592074823), (4312, 4312, 455131674843638438), (4313, 4313, 450625420637265781), (4314, 4314, 446163782809174040), (4315, 4315, 441746319613043604), (4316, 4316, 437372593676280796), (4317, 4317, 433042171956713660), (4318, 4318, 428754625699716495), (4319, 4319, 424509530395758906), (4320, 4320, 420306465738375154), (4321, 4321, 416145015582549658), (4322, 4322, 412024767903514512), (4323, 4323, 407945314755954963), (4324, 4324, 403906252233618775), (4325, 4325, 399907180429325520), (4326, 4326, 395947703395371802), (4327, 4327, 392027429104328517), (4328, 4328, 388145969410226254), (4329, 4329, 384302940010125004), (4330, 4330, 380497960406064360), (4331, 4331, 376730653867390456), (4332, 4332, 373000647393455897), (4333, 4333, 369307571676689007), (4334, 4334, 365651061066028720), (4335, 4335, 362030753530721505), (4336, 4336, 358446290624476737), (4337, 4337, 354897317449976968), (4338, 4338, 351383482623739572), (4339, 4339, 347904438241326309), (4340, 4340, 344459839842897335), (4341, 4341, 341049346379106273), (4342, 4342, 337672620177332943), (4343, 4343, 334329326908250439), (4344, 4344, 331019135552723207), (4345, 4345, 327741718369032878), (4346, 4346, 324496750860428592), (4347, 4347, 321283911742998606), (4348, 4348, 318102882913860006), (4349, 4349, 314953349419663372), (4350, 4350, 311834999425409280), (4351, 4351, 308747524183573544), (4352, 7209, 305690618003538163)]

def glob2 : ℕ := 34160637173536206697

def runs3 : List (ℕ × ℕ × ℕ) := [(0, 3865, 0), (3866, 3866, 178968439212878650), (3867, 3867, 359837504900964521), (3868, 3868, 538915787760455482), (3869, 3869, 716221018314406929), (3870, 3870, 891770751536141035), (3871, 3871, 1065582368587362922), (3872, 3872, 1237673078539067760), (3873, 3873, 1408059920075409184), (3874, 3874, 1576759763180697723), (3875, 3875, 1743789310809696277), (3876, 3876, 1909165100541378013), (3877, 3877, 2072903506216310425), (3878, 3878, 2235020739557827664), (3879, 3879, 2395532851777151664), (3880, 3880, 2554455735162620970), (3881, 3881, 2711805124653184640), (3882, 3882, 2867596599396316986), (3883, 3883, 3021845584290507428), (3884, 3884, 3174567351512478163), (3885, 3885, 3325777022029280870), (3886, 3886, 3475489567095422165), (3887, 3887, 3623719809735166021), (3888, 3888, 3770482426210159937), (3889, 3889, 3915791947472530152), (3890, 3890, 4059662760603589771), (3891, 3891, 4202109110238302264), (3892, 3892, 4343145099975641367), (3893, 3893, 4482784693774987013), (3894, 3894, 4621041717338695573), (3895, 3895, 4757929859480981276), (3896, 3896, 4893462673483244349), (3897, 3897, 5027653578435980065), (3898, 3898, 5160515860567401565), (3899, 3899, 5292062674558908001), (3900, 3900, 5422307044847528235), (3901, 3901, 5551261866915469061), (3902, 3902, 5678939908566895621), (3903, 3903, 5805353811192070433), (3904, 3904, 5930516091018976187), (3905, 3905, 6054439140352546241), (3906, 3906, 6177135228801625502), (3907, 3907, 6298616504493783186), (3908, 3908, 6418894995278097725), (3909, 3909, 6537982609916032912), (3910, 3910, 6655891139260523196), (3911, 3911, 6772632257423384864), (3912, 3912, 6888217522931168693), (3913, 3913, 7002658379869568524), (3914, 3914, 7115966159016499050), (3915, 3915, 7228152078963955016), (3916, 3916, 7339227247228762903), (3917, 3917, 7449202661352335068), (3918, 3918, 7558089209989535232), (3919, 3919, 7665897673986763117), (3920, 3920, 7772638727449364983), (3921, 3921, 7878322938798475742), (3922, 3922, 7982960771817397285), (3923, 3923, 8086562586687616635), (3924, 3924, 8189138641014566487), (3925, 3925, 8290699090843229706), (3926, 3926, 8391253991663688338), (3927, 3927, 8490813299406716688), (3928, 3928, 8589386871429517034), (3929, 3929, 8686984467491695594), (3930, 3930, 8783615750721575356), (3931, 3931, 8879290288572941458), (3932, 3932, 8974017553772313836), (3933, 3933, 9067806925256840942), (3934, 3934, 9160667689102907385), (3935, 3935, 9252609039445547427), (3936, 3936, 9343640079388755389), (3937, 3937, 9433769821906783074), (3938, 3938, 9523007190736513456), (3939, 3939, 9611361021260998982), (3940, 3940, 9698840061384251979), (3941, 3941, 9785452972397373757), (3942, 3942, 9871208329836108192), (3943, 3943, 9956114624329904661), (3944, 3944, 10040180262442574433), (3945, 3945, 10123413567504623712), (3946, 3946, 10205822780437345770), (3947, 3947, 10287416060568753749), (3948, 3948, 10368201486441434916), (3949, 3949, 10448187056612406369), (3950, 3950, 10527380690445051371), (3951, 3951, 10605790228893214740), (3952, 3952, 10683423435277534907), (3953, 3953, 10760287996054089528), (3954, 3954, 10836391521575430737), (3955, 3955, 10911741546844085399), (3956, 3956, 10986345532258594965), (3957, 3957, 11060210864352168794), (3958, 3958, 11133344856524024069), (3959, 3959, 11205754749763484738), (3960, 3960, 11277447713366911143), (3961, 3961, 11348430845647531345), (3962, 3962, 11418711174638244417), (3963, 3963, 11488295658787465281), (3964, 3964, 11557191187648079997), (3965, 3965, 11625404582559579716), (3966, 3966, 11692942597323440824), (3967, 3967, 11759811918871818158), (3968, 3968, 11826019167929617499), (3969, 3969, 11891570899670012887), (3970, 3970, 11956473604363473666), (3971, 3971, 12020733708020365527), (3972, 3972, 12084357573027189152), (3973, 3973, 12147351498776519473), (3974, 3974, 12209721722290707910), (3975, 3975, 12271474418839409333), (3976, 3976, 12332615702550994900), (3977, 3977, 12393151627017911303), (3978, 3978, 12453088185896046356), (3979, 3979, 12512431313498160270), (3980, 3980, 12571186885381441372), (3981, 3981, 12629360718929244444), (3982, 3982, 12686958573927069267), (3983, 3983, 12743986153132836419), (3984, 3984, 12800449102841516768), (3985, 3985, 12856353013444170578), (3986, 3986, 12911703419981451578), (3987, 3987, 12966505802691630787), (3988, 3988, 13020765587553194359), (3989, 3989, 13074488146822069184), (3990, 3990, 13127678799563529406), (3991, 3991, 13180342812178836556), (3992, 3992, 13232485398926665418), (3993, 3993, 13284111722439367262), (3994, 3994, 13335226894234121562), (3995, 3995, 13385835975219026810), (3996, 3996, 13435943976194180521), (3997, 3997, 13485555858347798057), (3998, 3998, 13534676533747419379), (3999, 3999, 13583310865826252372), (4000, 4000, 13631463669864700879), (4001, 4001, 13679139713467125144), (4002, 4002, 13726343717033881842), (4003, 4003, 13773080354228690453), (4004, 4004, 13819354252441372247), (4005, 4005, 13865169993246007686), (4006, 4006, 13910532112854557626), (4007, 4007, 13955445102565993210), (4008, 4008, 13999913409210978937), (4009, 4009, 14043941435592152924), (4010, 4010, 14087533540920047961), (4011, 4011, 14130694041244696512), (4012, 4012, 14173427209882962404), (4013, 4013, 14215737277841641505), (4014, 4014, 14257628434236373288), (4015, 4015, 14299104826706404757), (4016, 4016, 14340170561825247795), (4017, 4017, 14380829705507270605), (4018, 4018, 14421086283410263486), (4019, 4019, 14460944281334018814), (4020, 4020, 14500407645614964684), (4021, 4021, 14539480283516891287), (4022, 4022, 14578166063617808716), (4023, 4023, 14616468816192974487), (4024, 4024, 14654392333594128716), (4025, 4025, 14691940370624974488), (4026, 4026, 14729116644912940598), (4027, 4027, 14765924837277263479), (4028, 4028, 14802368592093424748), (4029, 4029, 14838451517653980459), (4030, 4030, 14874177186525817798), (4031, 4031, 14909549135903874568), (4032, 4032, 14944570867961356519), (4033, 4033, 14979245850196487164), (4034, 4034, 15013577515775824435), (4035, 4035, 15047569263874178170), (4036, 4036, 15081224460011162065), (4037, 4037, 15114546436384413447), (4038, 4038, 15147538492199513825), (4039, 4039, 15180203893996642912), (4040, 4040, 15212545875973998444), (4041, 4041, 15244567640308013822), (4042, 4042, 15276272357470405285), (4043, 4043, 15307663166542080001), (4044, 4044, 15338743175523936156), (4045, 4045, 15369515461644585814), (4046, 4046, 15399983071665031020), (4047, 4047, 15430149022180323303), (4048, 4048, 15460016299918236455), (4049, 4049, 15489587862034982149), (4050, 4050, 15518866636407997688), (4051, 4051, 15547855521925834856), (4052, 4052, 15576557388775178586), (4053, 4053, 15604975078725023864), (4054, 4054, 15633111405408038990), (4055, 4055, 15660969154599143076), (4056, 4056, 15688551084491325338), (4057, 4057, 15715859925968733519), (4058, 4058, 15742898382877058451), (4059, 4059, 15769669132291241552), (4060, 4060, 15796174824780531750), (4061, 4061, 15822418084670918086), (4062, 4062, 15848401510304963962), (4063, 4063, 15874127674299068790), (4064, 4064, 15899599123798182482), (4065, 4065, 15924818380727998018), (4066, 4066, 15949787942044647063), (4067, 4067, 15974510279981923346), (4068, 4068, 15998987842296058279), (4069, 4069, 16023223052508073065), (4070, 4070, 16047218310143731268), (4071, 4071, 16070975990971115628), (4072, 4072, 16094498447235852618), (4073, 4073, 16117788007894008054), (4074, 4074, 16140846978842676802), (4075, 4075, 16163677643148289424), (4076, 4076, 16186282261272658357), (4077, 4077, 16208663071296786013), (4078, 4078, 16230822289142456959), (4079, 4079, 16252762108791636114), (4080, 4080, 16274484702503694683), (4081, 4081, 16295992221030485346), (4082, 4082, 16317286793829287983), (4083, 4083, 16338370529273647028), (4084, 4084, 16359245514862121331), (4085, 4085, 16379913817424967176), (4086, 4086, 16400377483328774942), (4087, 4087, 16420638538679079662), (4088, 4088, 16440698989520965523), (4089, 4089, 16460560822037684197), (4090, 4090, 16480226002747306647), (4091, 4091, 16499696478697427884), (4092, 4092, 16518974177657943961), (4093, 4093, 16538061008311920274), (4094, 4094, 16556958860444570089), (4095, 4095, 16575669605130361986), (4096, 4096, 16594195094918274754), (4097, 4097, 16612537164015218090), (4098, 4098, 16630697628467637233), (4099, 4099, 16648678286341319554), (4100, 4100, 16666480917899420862), (4101, 4101, 16684107285778729087), (4102, 4102, 16701559135164182775), (4103, 4103, 16718838193961661675), (4104, 4104, 16735946172969066526), (4105, 4105, 16752884766045704992), (4106, 4106, 16769655650280000503), (4107, 4107, 16786260486155540613), (4108, 4108, 16802700917715481316), (4109, 4109, 16818978572725323596), (4110, 4110, 16835095062834078329), (4111, 4111, 16851051983733835490), (4112, 4112, 16866850915317753472), (4113, 4113, 16882493421836484147), (4114, 4114, 16897981052053049171), (4115, 4115, 16913315339396182859), (4116, 4116, 16928497802112156807), (4117, 4117, 16943529943415101310), (4118, 4118, 16958413251635838441), (4119, 4119, 16973149200369241542), (4120, 4120, 16987739248620135701), (4121, 4121, 17002184840947753681), (4122, 4122, 17016487407608761581), (4123, 4123, 17030648364698868413), (4124, 4124, 17044669114293033593), (4125, 4125, 17058551044584286247), (4126, 4126, 17072295530021170063), (4127, 4127, 17085903931443827306), (4128, 4128, 17099377596218735467), (4129, 4129, 17112717858372109884), (4130, 4130, 17125926038721985545), (4131, 4131, 17139003445008991150), (4132, 4132, 17151951372025828382), (4133, 4133, 17164771101745469206), (4134, 4134, 17177463903448083884), (4135, 4135, 17190031033846712277), (4136, 4136, 17202473737211690884), (4137, 4137, 17214793245493847921), (4138, 4138, 17226990778446478651), (4139, 4139, 17239067543746113037), (4140, 4140, 17251024737112087676), (4141, 4141, 17262863542424933854), (4142, 4142, 17274585131843593436), (4143, 4143, 17286190665921474210), (4144, 4144, 17297681293721356164), (4145, 4145, 17309058152929160080), (4146, 4146, 17320322369966589699), (4147, 4147, 17331475060102658629), (4148, 4148, 17342517327564113015), (4149, 4149, 17353450265644760922), (4150, 4150, 17364274956813719245), (4151, 4151, 17374992472822588873), (4152, 4152, 17385603874811568702), (4153, 4153, 17396110213414519028), (4154, 4154, 17406512528862984697), (4155, 4155, 17416811851089188330), (4156, 4156, 17427009199828003808), (4157, 4157, 17437105584717920123), (4158, 4158, 17447102005401005583), (4159, 4159, 17456999451621882277), (4160, 4160, 17466798903325720587), (4161, 4161, 17476501330755263468), (4162, 4162, 17486107694546890084), (4163, 4163, 17495618945825728317), (4164, 4164, 17505036026299825577), (4165, 4165, 17514359868353387221), (4166, 4166, 17523591395139091819), (4167, 4167, 17532731520669492411), (4168, 4168, 17541781149907512799), (4169, 4169, 17550741178856047837), (4170, 4170, 17559612494646676587), (4171, 4171, 17568395975627497132), (4172, 4172, 17577092491450091731), (4173, 4173, 17585702903155630938), (4174, 4174, 17594228063260125202), (4175, 4175, 17602668815838832394), (4176, 4176, 17611025996609829614), (4177, 4177, 17619300433016757555), (4178, 4178, 17627492944310745615), (4179, 4179, 17635604341631525872), (4180, 4180, 17643635428087743949), (4181, 4181, 17651586998836474718), (4182, 4182, 17659459841161950727), (4183, 4183, 17667254734553511132), (4184, 4184, 17674972450782778859), (4185, 4185, 17682613753980073639), (4186, 4186, 17690179400710068470), (4187, 4187, 17697670140046697016), (4188, 4188, 17705086713647319339), (4189, 4189, 17712429855826153322), (4190, 4190, 17719700293626979048), (4191, 4191, 17726898746895123331), (4192, 4192, 17734025928348731532), (4193, 4193, 17741082543649333711), (4194, 4194, 17748069291471712106), (4195, 4195, 17754986863573076853), (4196, 4196, 17761835944861556802), (4197, 4197, 17768617213464012196), (4198, 4198, 17775331340793175952), (4199, 4199, 17781978991614130167), (4200, 4200, 17788560824110124439), (4201, 4201, 17795077489947742530), (4202, 4202, 17801529634341423808), (4203, 4203, 17807917896117345865), (4204, 4204, 17814242907776674635), (4205, 4205, 17820505295558188268), (4206, 4206, 17826705679500280975), (4207, 4207, 17832844673502352961), (4208, 4208, 17838922885385592552), (4209, 4209, 17844940916953156503), (4210, 4210, 17850899364049754475), (4211, 4211, 17856798816620643555), (4212, 4212, 17862639858770038685), (4213, 4213, 17868423068818944753), (4214, 4214, 17874149019362416108), (4215, 4215, 17879818277326249133), (4216, 4216, 17885431404023113514), (4217, 4217, 17890988955208127753), (4218, 4218, 17896491481133884425), (4219, 4219, 17901939526604930634), (4220, 4220, 17907333631031709060), (4221, 4221, 17912674328483964927), (4222, 4222, 17917962147743624201), (4223, 4223, 17923197612357148235), (4224, 4224, 17928381240687370051), (4225, 4225, 17933513545964817393), (4226, 4226, 17938595036338527633), (4227, 4227, 17943626214926359553), (4228, 4228, 17948607579864806999), (4229, 4229, 17953539624358319322), (4230, 4230, 17958422836728133504), (4231, 4231, 17963257700460622792), (4232, 4232, 17968044694255166642), (4233, 4233, 17972784292071546691), (4234, 4234, 17977476963176873472), (4235, 4235, 17982123172192048503), (4236, 4236, 17986723379137766356), (4237, 4237, 17991278039480061260), (4238, 4238, 17995787604175402748), (4239, 4239, 18000252519715344816), (4240, 4240, 18004673228170733002), (4241, 4241, 18009050167235473781), (4242, 4242, 18013383770269870591), (4243, 4243, 18017674466343530799), (4244, 4244, 18021922680277847837), (4245, 4245, 18026128832688062726), (4246, 4246, 18030293340024909151), (4247, 4247, 18034416614615846205), (4248, 4248, 18038499064705882892), (4249, 4249, 18042541094497998424), (4250, 4250, 18046543104193162317), (4251, 4251, 18050505490029958250), (4252, 4252, 18054428644323815611), (4253, 4253, 18058312955505852601), (4254, 4254, 18062158808161334769), (4255, 4255, 18065966583067752758), (4256, 4256, 18069736657232523043), (4257, 4257, 18073469403930315406), (4258, 4258, 18077165192740010814), (4259, 4259, 18080824389581293396), (4260, 4260, 18084447356750880111), (4261, 4261, 18088034452958391710), (4262, 4262, 18091586033361868541), (4263, 4263, 18095102449602934710), (4264, 4264, 18098584049841614085), (4265, 4265, 18102031178790801585), (4266, 4266, 18105444177750393170), (4267, 4267, 18108823384641077907), (4268, 4268, 18112169134037795468), (4269, 4269, 18115481757202862361), (4270, 4270, 18118761582118770175), (4271, 4271, 18122008933520659101), (4272, 4272, 18125224132928469918), (4273, 4273, 18128407498678777657), (4274, 4274, 18131559345956310073), (4275, 4275, 18134679986825154048), (4276, 4276, 18137769730259653034), (4277, 4277, 18140828882174998565), (4278, 4278, 18143857745457518892), (4279, 4279, 18146856619994667731), (4280, 4280, 18149825802704716086), (4281, 4281, 18152765587566150101), (4282, 4282, 18155676265646777839), (4283, 4283, 18158558125132547876), (4284, 4284, 18161411451356082567), (4285, 4285, 18164236526824928795), (4286, 4286, 18167033631249529021), (4287, 4287, 18169803041570915383), (4288, 4288, 18172545031988129603), (4289, 4289, 18175259873985371406), (4290, 4290, 18177947836358878140), (4291, 4291, 18180609185243538274), (4292, 4292, 18183244184139241376), (4293, 4293, 18185853093936967220), (4294, 4294, 18188436172944616571), (4295, 4295, 18190993676912586225), (4296, 4296, 18193525859059090832), (4297, 4297, 18196032970095234008), (4298, 4298, 18198515258249831212), (4299, 4299, 18200972969293986860), (4300, 4300, 18203406346565428095), (4301, 4301, 18205815630992597635), (4302, 4302, 18208201061118508071), (4303, 4303, 18210562873124359987), (4304, 4304, 18212901300852926241), (4305, 4305, 18215216575831704710), (4306, 4306, 18217508927295841808), (4307, 4307, 18219778582210829034), (4308, 4308, 18222025765294974802), (4309, 4309, 18224250699041653780), (4310, 4310, 18226453603741335937), (4311, 4311, 18228634697503397478), (4312, 4312, 18230794196277715836), (4313, 4313, 18232932313876050844), (4314, 4314, 18235049261993214218), (4315, 4315, 18237145250228029440), (4316, 4316, 18239220486104084115), (4317, 4317, 18241275175090276862), (4318, 4318, 18243309520621160771), (4319, 4319, 18245323724117085432), (4320, 4320, 18247317985004139553), (4321, 4321, 18249292500733896108), (4322, 4322, 18251247466802962004), (4323, 4323, 18253183076772334179), (4324, 4324, 18255099522286564054), (4325, 4325, 18256996993092732248), (4326, 4326, 18258875677059235410), (4327, 4327, 18260735760194387056), (4328, 4328, 18262577426664834229), (4329, 4329, 18264400858813791827), (4330, 4330, 18266206237179096380), (4331, 4331, 18267993740511081085), (4332, 4332, 18269763545790273863), (4333, 4333, 18271515828244920177), (4334, 4334, 18273250761368332369), (4335, 4335, 18274968516936067213), (4336, 4336, 18276669265022933396), (4337, 4337, 18278353174019830606), (4338, 4338, 18280020410650421903), (4339, 4339, 18281671139987641009), (4340, 4340, 18283305525470036164), (4341, 4341, 18284923728917952158), (4342, 4342, 18286525910549552153), (4343, 4343, 18288112228996680860), (4344, 4344, 18289682841320570670), (4345, 4345, 18291237903027392263), (4346, 4346, 18292777568083651267), (4347, 4347, 18294301988931432458), (4348, 4348, 18295811316503493044), (4349, 4349, 18297305700238206495), (4350, 4350, 18298785288094358427), (4351, 4351, 18300250226565795984), (4352, 7209, 18446744073709486253)]

def glob3 : ℕ := 18446744073709551616

def runs4 : List (ℕ × ℕ × ℕ) := [(0, 3000, 191944635396339683939), (3001, 3001, 191945620707084766600), (3002, 3002, 191946615877782085960), (3003, 3003, 191947621007168798877), (3004, 3004, 191948636194972201881), (3005, 3005, 191949661541919688251), (3006, 3006, 191950697149748805799), (3007, 3007, 191951743121217416362), (3008, 3008, 191952799560113958068), (3009, 3009, 191953866571267811405), (3010, 3010, 191954944260559770166), (3011, 3011, 191956032734932618347), (3012, 3012, 191957132102401814074), (3013, 3013, 191958242472066281656), (3014, 3014, 191959363954119312876), (3015, 3015, 191960496659859578637), (3016, 3016, 191961640701702252087), (3017, 3017, 191962796193190244382), (3018, 3018, 191963963249005554217), (3019, 3019, 191965141984980732315), (3020, 3020, 191966332518110462039), (3021, 3021, 191967534966563257321), (3022, 3022, 191968749449693279116), (3023, 3023, 191969976088052271589), (3024, 3024, 191971215003401619273), (3025, 3025, 191972466318724526432), (3026, 3026, 191973730158238319895), (3027, 3027, 191975006647406876610), (3028, 3028, 191976295912953177225), (3029, 3029, 191977598082871986969), (3030, 3030, 191978913286442665158), (3031, 3031, 191980241654242104631), (3032, 3032, 191981583318157802476), (3033, 3033, 191982938411401063376), (3034, 3034, 191984307068520336945), (3035, 3035, 191985689425414690446), (3036, 3036, 191987085619347418267), (3037, 3037, 191988495788959789576), (3038, 3038, 191989920074284935571), (3039, 3039, 191991358616761877773), (3040, 3040, 191992811559249698805), (3041, 3041, 191994279046041857134), (3042, 3042, 191995761222880647260), (3043, 3043, 191997258236971806850), (3044, 3044, 191998770236999272337), (3045, 3045, 192000297373140084512), (3046, 3046, 192001839797079445668), (3047, 3047, 192003397662025929846), (3048, 3048, 192004971122726847782), (3049, 3049, 192006560335483768143), (3050, 3050, 192008165458168196673), (3051, 3051, 192009786650237414881), (3052, 3052, 192011424072750479921), (3053, 3053, 192013077888384387335), (3054, 3054, 192014748261450398345), (3055, 3055, 192016435357910533394), (3056, 3056, 192018139345394233663), (3057, 3057, 192019860393215192309), (3058, 3058, 192021598672388357171), (3059, 3059, 192023354355647106736), (3060, 3060, 192025127617460601152), (3061, 3061, 192026918634051310119), (3062, 3062, 192028727583412719470), (3063, 3063, 192030554645327218330), (3064, 3064, 192032400001384168702), (3065, 3065, 192034263834998159390), (3066, 3066, 192036146331427446173), (3067, 3067, 192038047677792580165), (3068, 3068, 192039968063095226325), (3069, 3069, 192041907678237174089), (3070, 3070, 192043866716039542131), (3071, 3071, 192045845371262179270), (3072, 3072, 192047843840623263571), (3073, 3073, 192049862322819101711), (3074, 3074, 192051901018544130682), (3075, 3075, 192053960130511123964), (3076, 3076, 192056039863471604285), (3077, 3077, 192058140424236465135), (3078, 3078, 192060262021696803214), (3079, 3079, 192062404866844964009), (3080, 3080, 192064569172795802746), (3081, 3081, 192066755154808162952), (3082, 3082, 192068963030306574914), (3083, 3083, 192071193018903176340), (3084, 3084, 192073445342419857533), (3085, 3085, 192075720224910633457), (3086, 3086, 192078017892684245042), (3087, 3087, 192080338574326992163), (3088, 3088, 192082682500725800700), (3089, 3089, 192085049905091526149), (3090, 3090, 192087441022982496261), (3091, 3091, 192089856092328295230), (3092, 3092, 192092295353453791954), (3093, 3093, 192094759049103414956), (3094, 3094, 192097247424465676538), (3095, 3095, 192099760727197948805), (3096, 3096, 192102299207451494218), (3097, 3097, 192104863117896753331), (3098, 3098, 192107452713748892460), (3099, 3099, 192110068252793613990), (3100, 3100, 192112709995413232120), (3101, 3101, 192115378204613016825), (3102, 3102, 192118073146047808890), (3103, 3103, 192120795088048908861), (3104, 3104, 192123544301651242822), (3105, 3105, 192126321060620807923), (3106, 3106, 192129125641482400617), (3107, 3107, 192131958323547630606), (3108, 3108, 192134819388943223518), (3109, 3109, 192137709122639615374), (3110, 3110, 192140627812479841957), (3111, 3111, 192143575749208726182), (3112, 3112, 192146553226502366665), (3113, 3113, 192149560540997930665), (3114, 3114, 192152597992323754654), (3115, 3115, 192155665883129755768), (3116, 3116, 192158764519118157471), (3117, 3117, 192161894209074532756), (3118, 3118, 192165055264899168275), (3119, 3119, 192168248001638752832), (3120, 3120, 192171472737518393673), (3121, 3121, 192174729793973964095), (3122, 3122, 192178019495684785904), (3123, 3123, 192181342170606650301), (3124, 3124, 192184698150005180810), (3125, 3125, 192188087768489541918), (3126, 3126, 192191511364046497122), (3127, 3127, 192194969278074820130), (3128, 3128, 192198461855420062992), (3129, 3129, 192201989444409685008), (3130, 3130, 192205552396888546267), (3131, 3131, 192209151068254769745), (3132, 3132, 192212785817495975921), (3133, 3133, 192216457007225893914), (3134, 3134, 192220165003721353195), (3135, 3135, 192223910176959659979), (3136, 3136, 192227692900656362428), (3137, 3137, 192231513552303408876), (3138, 3138, 192235372513207703300), (3139, 3139, 192239270168530062339), (3140, 3140, 192243206907324578198), (3141, 3141, 192247183122578391818), (3142, 3142, 192251199211251880768), (3143, 3143, 192255255574319266329), (3144, 3144, 192259352616809644336), (3145, 3145, 192263490747848444349), (3146, 3146, 192267670380699321832), (3147, 3147, 192271891932806488006), (3148, 3148, 192276155825837482168), (3149, 3149, 192280462485726391270), (3150, 3150, 192284812342717521623), (3151, 3151, 192289205831409527669), (3152, 3152, 192293643390800002788), (3153, 3153, 192298125464330537189), (3154, 3154, 192302652499932247981), (3155, 3155, 192307224950071786587), (3156, 3156, 192311843271797828721), (3157, 3157, 192316507926788052209), (3158, 3158, 192321219381396607996), (3159, 3159, 192325978106702089751), (3160, 3160, 192330784578556007531), (3161, 3161, 192335639277631771055), (3162, 3162, 192340542689474188165), (3163, 3163, 192345495304549484169), (3164, 3164, 192350497618295847775), (3165, 3165, 192355550131174509432), (3166, 3166, 192360653348721357944), (3167, 3167, 192365807781599101303), (3168, 3168, 192371013945649977744), (3169, 3169, 192376272361949023109), (3170, 3170, 192381583556857900684), (3171, 3171, 192386948062079299725), (3172, 3172, 192392366414711908988), (3173, 3173, 192397839157305971636), (3174, 3174, 192403366837919427983), (3175, 3175, 192408950010174652615), (3176, 3176, 192414589233315792485), (3177, 3177, 192420285072266712693), (3178, 3178, 192426038097689556712), (3179, 3179, 192431848886043927926), (3180, 3180, 192437718019646699404), (3181, 3181, 192443646086732458954), (3182, 3182, 192449633681514596545), (3183, 3183, 192455681404247041303), (3184, 3184, 192461789861286655364), (3185, 3185, 192467959665156291948), (3186, 3186, 192474191434608525129), (3187, 3187, 192480485794690058839), (3188, 3188, 192486843376806822756), (3189, 3189, 192493264818789762834), (3190, 3190, 192499750764961334271), (3191, 3191, 192506301866202704895), (3192, 3192, 192512918780021676952), (3193, 3193, 192519602170621335455), (3194, 3194, 192526352708969431314), (3195, 3195, 192533171072868507571), (3196, 3196, 192540057947026777190), (3197, 3197, 192547014023129760920), (3198, 3198, 192554039999912693910), (3199, 3199, 192561136583233709786), (3200, 3200, 192568304486147811100), (3201, 3201, 192575544428981635085), (3202, 3202, 192582857139409023833), (3203, 3203, 192590243352527408078), (3204, 3204, 192597703810935013913), (3205, 3205, 192605239264808901862), (3206, 3206, 192612850471983847875), (3207, 3207, 192620538198032075910), (3208, 3208, 192628303216343851906), (3209, 3209, 192636146308208949055), (3210, 3210, 192644068262898994438), (3211, 3211, 192652069877750707183), (3212, 3212, 192660151958250038466), (3213, 3213, 192668315318117223771), (3214, 3214, 192676560779392757997), (3215, 3215, 192684889172524304112), (3216, 3216, 192693301336454546190), (3217, 3217, 192701798118709997818), (3218, 3218, 192710380375490777003), (3219, 3219, 192719048971761358829), (3220, 3220, 192727804781342317300), (3221, 3221, 192736648687003067906), (3222, 3222, 192745581580555622643), (3223, 3223, 192754604362949369334), (3224, 3224, 192763717944366887277), (3225, 3225, 192772923244320811396), (3226, 3226, 192782221191751757218), (3227, 3227, 192791612725127319185), (3228, 3228, 192801098792542154944), (3229, 3229, 192810680351819168449), (3230, 3230, 192820358370611804876), (3231, 3231, 192830133826507470495), (3232, 3232, 192840007707132090857), (3233, 3233, 192849981010255820807), (3234, 3234, 192860054743899920011), (3235, 3235, 192870229926444807881), (3236, 3236, 192880507586739311957), (3237, 3237, 192890888764211123997), (3238, 3238, 192901374508978478210), (3239, 3239, 192911965881963066270), (3240, 3240, 192922663955004203934), (3241, 3241, 192933469810974264299), (3242, 3242, 192944384543895392925), (3243, 3243, 192955409259057520259), (3244, 3244, 192966545073137687006), (3245, 3245, 192977793114320698305), (3246, 3246, 192989154522421122777), (3247, 3247, 193000630449006652746), (3248, 3248, 193012222057522842125), (3249, 3249, 193023930523419238728), (3250, 3250, 193035757034276927954), (3251, 3251, 193047702789937505061), (3252, 3252, 193059769002633493439), (3253, 3253, 193071956897120226588), (3254, 3254, 193084267710809211689), (3255, 3255, 193096702693902992957), (3256, 3256, 193109263109531533177), (3257, 3257, 193121950233890132104), (3258, 3258, 193134765356378900656), (3259, 3259, 193147709779743810095), (3260, 3260, 193160784820219335660), (3261, 3261, 193173991807672714381), (3262, 3262, 193187332085749837099), (3263, 3263, 193200807012022794968), (3264, 3264, 193214417958139101029), (3265, 3265, 193228166309972607712), (3266, 3266, 193242053467776141443), (3267, 3267, 193256080846335875799), (3268, 3268, 193270249875127465000), (3269, 3269, 193284561998473959780), (3270, 3270, 193299018675705528068), (3271, 3271, 193313621381321003147), (3272, 3272, 193328371605151282350), (3273, 3273, 193343270852524599653), (3274, 3274, 193358320644433695851), (3275, 3275, 193373522517704910366), (3276, 3276, 193388878025169219076), (3277, 3277, 193404388735835242896), (3278, 3278, 193420056235064252208), (3279, 3279, 193435882124747192604), (3280, 3280, 193451868023483757770), (3281, 3281, 193468015566763535721), (3282, 3282, 193484326407149254968), (3283, 3283, 193500802214462157605), (3284, 3284, 193517444675969526684), (3285, 3285, 193534255496574395655), (3286, 3286, 193551236399007468057), (3287, 3287, 193568389124021276060), (3288, 3288, 193585715430586606879), (3289, 3289, 193603217096091226518), (3290, 3290, 193620895916540930731), (3291, 3291, 193638753706762953543), (3292, 3292, 193656792300611764104), (3293, 3293, 193675013551177283145), (3294, 3294, 193693419330995550734), (3295, 3295, 193712011532261877534), (3296, 3296, 193730792067046512239), (3297, 3297, 193749762867512858357), (3298, 3298, 193768925886138274003), (3299, 3299, 193788283095937488901), (3300, 3300, 193807836490688673267), (3301, 3301, 193827588085162193827), (3302, 3302, 193847539915352092715), (3303, 3303, 193867694038710325569), (3304, 3304, 193888052534383795686), (3305, 3305, 193908617503454221673), (3306, 3306, 193929391069180876594), (3307, 3307, 193950375377246237215), (3308, 3308, 193971572596004582522), (3309, 3309, 193992984916733581317), (3310, 3310, 194014614553888909305), (3311, 3311, 194036463745361936702), (3312, 3312, 194058534752740528057), (3313, 3313, 194080829861572996606), (3314, 3314, 194103351381635256163), (3315, 3315, 194126101647201214207), (3316, 3316, 194149083017316450517), (3317, 3317, 194172297876075226423), (3318, 3318, 194195748632900870413), (3319, 3319, 194219437722829586606), (3320, 3320, 194243367606797733301), (3321, 3321, 194267540771932619588), (3322, 3322, 194291959731846868757), (3323, 3323, 194316627026936398019), (3324, 3324, 194341545224682064858), (3325, 3325, 194366716919955031132), (3326, 3326, 194392144735325896846), (3327, 3327, 194417831321377656401), (3328, 3328, 194443779357022530918), (3329, 3329, 194469991549822731153), (3330, 3330, 194496470636315206376), (3331, 3331, 194523219382340435493), (3332, 3332, 194550240583375317609), (3333, 3333, 194577537064870220162), (3334, 3334, 194605111682590243712), (3335, 3335, 194632967322960763437), (3336, 3336, 194661106903417308366), (3337, 3337, 194689533372759840410), (3338, 3338, 194718249711511496239), (3339, 3339, 194747258932281856131), (3340, 3340, 194776564080134804969), (3341, 3341, 194806168232961051636), (3342, 3342, 194836074501855374183), (3343, 3343, 194866286031498659249), (3344, 3344, 194896806000544805373), (3345, 3345, 194927637622012561005), (3346, 3346, 194958784143682369195), (3347, 3347, 194990248848498292190), (3348, 3348, 195022035054975090362), (3349, 3349, 195054146117610531179), (3350, 3350, 195086585427303005212), (3351, 3351, 195119356411774527468), (3352, 3352, 195152462535999203686), (3353, 3353, 195185907302637242583), (3354, 3354, 195219694252474596445), (3355, 3355, 195253826964868313830), (3356, 3356, 195288309058197689648), (3357, 3357, 195323144190321299292), (3358, 3358, 195358336059040005054), (3359, 3359, 195393888402566024521), (3360, 3360, 195429804999998152270), (3361, 3361, 195466089671803227716), (3362, 3362, 195502746280303943614), (3363, 3363, 195539778730173091369), (3364, 3364, 195577190968934340966), (3365, 3365, 195614986987469655093), (3366, 3366, 195653170820533438729), (3367, 3367, 195691746547273527305), (3368, 3368, 195730718291759118333), (3369, 3369, 195770090223515753280), (3370, 3370, 195809866558067458335), (3371, 3371, 195850051557486154686), (3372, 3372, 195890649530948450853), (3373, 3373, 195931664835299931683), (3374, 3374, 195973101875627060620), (3375, 3375, 196014965105836814002), (3376, 3376, 196057259029244168230), (3377, 3377, 196099988199167562879), (3378, 3378, 196143157219532465008), (3379, 3379, 196186770745483162221), (3380, 3380, 196230833484002914346), (3381, 3381, 196275350194542595938), (3382, 3382, 196320325689657964268), (3383, 3383, 196365764835655689891), (3384, 3384, 196411672553248289394), (3385, 3385, 196458053818218102535), (3386, 3386, 196504913662090458541), (3387, 3387, 196552257172816179055), (3388, 3388, 196600089495463567936), (3389, 3389, 196648415832920040879), (3390, 3390, 196697241446603550703), (3391, 3391, 196746571657183967033), (3392, 3392, 196796411845314572068), (3393, 3393, 196846767452373837164), (3394, 3394, 196897643981217648040), (3395, 3395, 196949046996942149572), (3396, 3396, 197000982127657384370), (3397, 3397, 197053455065271902610), (3398, 3398, 197106471566288523960), (3399, 3399, 197160037452611435867), (3400, 3400, 197214158612364815991), (3401, 3401, 197268841000723170112), (3402, 3402, 197324090640753580542), (3403, 3403, 197379913624270063773), (3404, 3404, 197436316112700239914), (3405, 3405, 197493304337964520376), (3406, 3406, 197550884603368024230), (3407, 3407, 197609063284505437736), (3408, 3408, 197667846830179035714), (3409, 3409, 197727241763330087618), (3410, 3410, 197787254681983875593), (3411, 3411, 197847892260208556139), (3412, 3412, 197909161249088101611), (3413, 3413, 197971068477709562350), (3414, 3414, 198033620854164895021), (3415, 3415, 198096825366567607518), (3416, 3416, 198160689084084475782), (3417, 3417, 198225219157982592890), (3418, 3418, 198290422822692015953), (3419, 3419, 198356307396884281635), (3420, 3420, 198422880284567066478), (3421, 3421, 198490148976195273769), (3422, 3422, 198558121049798834263), (3423, 3423, 198626804172127513904), (3424, 3424, 198696206099813027513), (3425, 3425, 198766334680548763477), (3426, 3426, 198837197854287430612), (3427, 3427, 198908803654456944680), (3428, 3428, 198981160209194878459), (3429, 3429, 199054275742601805882), (3430, 3430, 199128158576013877457), (3431, 3431, 199202817129294971105), (3432, 3432, 199278259922148769570), (3433, 3433, 199354495575451122768), (3434, 3434, 199431532812603060819), (3435, 3435, 199509380460904831041), (3436, 3436, 199588047452951339890), (3437, 3437, 199667542828049388729), (3438, 3438, 199747875733657100390), (3439, 3439, 199829055426845941719), (3440, 3440, 199911091275785755797), (3441, 3441, 199993992761253226114), (3442, 3442, 200077769478164203890), (3443, 3443, 200162431137130338723), (3444, 3444, 200247987566040462076), (3445, 3445, 200334448711667182546), (3446, 3446, 200421824641299161597), (3447, 3447, 200510125544399548366), (3448, 3448, 200599361734291062314), (3449, 3449, 200689543649868222918), (3450, 3450, 200780681857337236245), (3451, 3451, 200872787051984059167), (3452, 3452, 200965870059971173141), (3453, 3453, 201059941840163610924), (3454, 3454, 201155013485984791294), (3455, 3455, 201251096227302728838), (3456, 3456, 201348201432347198164), (3457, 3457, 201446340609658444440), (3458, 3458, 201545525410068045076), (3459, 3459, 201645767628712540524), (3460, 3460, 201747079207080465692), (3461, 3461, 201849472235093427319), (3462, 3462, 201952958953221886806), (3463, 3463, 202057551754636322543), (3464, 3464, 202163263187394460633), (3465, 3465, 202270105956665278151), (3466, 3466, 202378092926990498720), (3467, 3467, 202487237124584316133), (3468, 3468, 202597551739672098205), (3469, 3469, 202709050128868839784), (3470, 3470, 202821745817598151111), (3471, 3471, 202935652502552585320), (3472, 3472, 203050784054196127007), (3473, 3473, 203167154519309682270), (3474, 3474, 203284778123580429672), (3475, 3475, 203403669274235911029), (3476, 3476, 203523842562723760902), (3477, 3477, 203645312767437994123), (3478, 3478, 203768094856492791699), (3479, 3479, 203892203990544746931), (3480, 3480, 204017655525664555656), (3481, 3481, 204144465016259157150), (3482, 3482, 204272648218045355417), (3483, 3483, 204402221091075974410), (3484, 3484, 204533199802819625096), (3485, 3485, 204665600731295187342), (3486, 3486, 204799440468262135261), (3487, 3487, 204934735822467860979), (3488, 3488, 205071503822953178838), (3489, 3489, 205209761722417219738), (3490, 3490, 205349527000642953762), (3491, 3491, 205490817367984608440), (3492, 3492, 205633650768918279905), (3493, 3493, 205778045385657064963), (3494, 3494, 205924019641832073593), (3495, 3495, 206071592206240713791), (3496, 3496, 206220781996663673854), (3497, 3497, 206371608183752061319), (3498, 3498, 206524090194986192761), (3499, 3499, 206678247718707564557), (3500, 3500, 206834100708225571658), (3501, 3501, 206991669386000579207), (3502, 3502, 207150974247904990802), (3503, 3503, 207312036067563997041), (3504, 3504, 207474875900777729057), (3505, 3505, 207639515090026583813), (3506, 3506, 207805975269061531157), (3507, 3507, 207974278367581257094), (3508, 3508, 208144446615998043293), (3509, 3509, 208316502550294329754), (3510, 3510, 208490469016971955653), (3511, 3511, 208666369178096122890), (3512, 3512, 208844226516436177618), (3513, 3513, 209024064840705357294), (3514, 3514, 209205908290901704396), (3515, 3515, 209389781343752403120), (3516, 3516, 209575708818263851998), (3517, 3517, 209763715881379843633), (3518, 3518, 209953828053750282589), (3519, 3519, 210146071215612934002), (3520, 3520, 210340471612790758733), (3521, 3521, 210537055862807455905), (3522, 3522, 210735850961123900509), (3523, 3523, 210936884287498232522), (3524, 3524, 211140183612472424636), (3525, 3525, 211345777103988228432), (3526, 3526, 211553693334135473525), (3527, 3527, 211763961286035771143), (3528, 3528, 211976610360864752667), (3529, 3529, 212191670385016054997), (3530, 3530, 212409171617410348322), (3531, 3531, 212629144756952787937), (3532, 3532, 212851620950142360356), (3533, 3533, 213076631798836685122), (3534, 3534, 213304209368175927474), (3535, 3535, 213534386194669573615), (3536, 3536, 213767195294449919600), (3537, 3537, 214002670171696227181), (3538, 3538, 214240844827233605133), (3539, 3539, 214481753767310782994), (3540, 3540, 214725432012561055628), (3541, 3541, 214971915107150791944), (3542, 3542, 215221239128120019271), (3543, 3543, 215473440694919716718), (3544, 3544, 215728556979150576223), (3545, 3545, 215986625714508119125), (3546, 3546, 216247685206939189165), (3547, 3547, 216511774345014979766), (3548, 3548, 216778932610525894678), (3549, 3549, 217049200089303686415), (3550, 3550, 217322617482276466790), (3551, 3551, 217599226116762338207), (3552, 3552, 217879067958007553460), (3553, 3553, 218162185620975275747), (3554, 3554, 218448622382391179562), (3555, 3555, 218738422193052307308), (3556, 3556, 219031629690405776015), (3557, 3557, 219328290211404113594), (3558, 3558, 219628449805644194930), (3559, 3559, 219932155248796944825), (3560, 3560, 220239454056335177692), (3561, 3561, 220550394497567153152), (3562, 3562, 220865025609983642416), (3563, 3563, 221183397213926522946), (3564, 3564, 221505559927587148435), (3565, 3565, 221831565182342978001), (3566, 3566, 222161465238441192802), (3567, 3567, 222495313201038280442), (3568, 3568, 222833163036604827623), (3569, 3569, 223175069589705030018), (3570, 3570, 223521088600160705371), (3571, 3571, 223871276720609881852), (3572, 3572, 224225691534470328868), (3573, 3573, 224584391574318702303), (3574, 3574, 224947436340696290803), (3575, 3575, 225314886321352674584), (3576, 3576, 225686803010938943723), (3577, 3577, 226063248931162469346), (3578, 3578, 226444287651415578944), (3579, 3579, 226829983809890856641), (3580, 3580, 227220403135196171060), (3581, 3581, 227615612468482927824), (3582, 3582, 228015679786101451335), (3583, 3583, 228420674222797821502), (3584, 3584, 228830666095466926339), (3585, 3585, 229245726927476941039), (3586, 3586, 229665929473580909064), (3587, 3587, 230091347745431581247), (3588, 3588, 230522057037716165746), (3589, 3589, 230958133954928155267), (3590, 3590, 231399656438793929066), (3591, 3591, 231846703796372376431), (3592, 3592, 232299356728846356363), (3593, 3593, 232757697361025395595), (3594, 3594, 233221809271579634840), (3595, 3595, 233691777524025661810), (3596, 3596, 234167688698485519991), (3597, 3597, 234649630924240855209), (3598, 3598, 235137693913104858522), (3599, 3599, 235631968993635384774), (3600, 3600, 236132549146213372288), (3601, 3601, 236639529039011461470), (3602, 3602, 237153005064878509702), (3603, 3603, 237673075379166527774), (3604, 3604, 238199839938527420324), (3605, 3605, 238733400540707800567), (3606, 3606, 239273860865371069048), (3607, 3607, 239821326515976898571), (3608, 3608, 240375905062749254109), (3609, 3609, 240937706086765098716), (3610, 3610, 241506841225196995619), (3611, 3611, 242083424217743914315), (3612, 3612, 242667570954285685995), (3613, 3613, 243259399523797732752), (3614, 3614, 243859030264563917243), (3615, 3615, 244466585815726626681), (3616, 3616, 245082191170214518880), (3617, 3617, 245705973729089720562), (3618, 3618, 246338063357357681097), (3619, 3619, 246978592441284350456), (3620, 3620, 247627695947266870437), (3621, 3621, 248285511482305545462), (3622, 3622, 248952179356126495760), (3623, 3623, 249627842645006093925), (3624, 3624, 250312647257350048275), (3625, 3625, 251006742001081825740), (3626, 3626, 251710278652897005917), (3627, 3627, 252423412029442129411), (3628, 3628, 253146300060478650569), (3629, 3629, 253879103864094730407), (3630, 3630, 254621987824029813232), (3631, 3631, 255375119669179223554), (3632, 3632, 256138670555348402064), (3633, 3633, 256912815149328874389), (3634, 3634, 257697731715370618031), (3635, 3635, 258493602204128165436), (3636, 3636, 259300612344160558834), (3637, 3637, 260118951736068159851), (3638, 3638, 260948813949352318639), (3639, 3639, 261790396622087028278), (3640, 3640, 262643901563494935756), (3641, 3641, 263509534859523456171), (3642, 3642, 264387506981520247714), (3643, 3643, 265278032898110957347), (3644, 3644, 266181332190385947063), (3645, 3645, 267097629170506664757), (3646, 3646, 268027153003846438817), (3647, 3647, 268970137834784758677), (3648, 3648, 269926822916278562250), (3649, 3649, 270897452743338693204), (3650, 3650, 271882277190544524643), (3651, 3651, 272881551653734779502), (3652, 3652, 273895537196017820899), (3653, 3653, 274924500698250147247), (3654, 3654, 275968715014137516990), (3655, 3655, 277028459130119056888), (3656, 3656, 278104018330200886575), (3657, 3657, 279195684365912232323), (3658, 3658, 280303755631563716312), (3659, 3659, 281428537344994507098), (3660, 3660, 282570341734002315397), (3661, 3661, 283729488228657830794), (3662, 3662, 284906303659713134118), (3663, 3663, 286101122463321902202), (3664, 3664, 287314286892297862864), (3665, 3665, 288546147234146974904), (3666, 3666, 289797062036118218612), (3667, 3667, 291067398337527705400), (3668, 3668, 292357531909621070181), (3669, 3669, 293667847503249817899), (3670, 3670, 294998739104648477602), (3671, 3671, 296350610199611096691), (3672, 3672, 297723874046377808283), (3673, 3673, 299118953957554951380), (3674, 3674, 300536283591405543228), (3675, 3675, 301976307252860823865), (3676, 3676, 303439480204618143823), (3677, 3677, 304926268988705678206), (3678, 3678, 306437151758910356648), (3679, 3679, 307972618624482033105), (3680, 3680, 309533172005544318508), (3681, 3681, 311119327000660700857), (3682, 3682, 312731611767023621727), (3683, 3683, 314370567913754107622), (3684, 3684, 316036750908820413785), (3685, 3685, 317730730500105974046), (3686, 3686, 319453091151179812561), (3687, 3687, 321204432492346514344), (3688, 3688, 322985369787577926316), (3689, 3689, 324796534417955027599), (3690, 3690, 326638574382275928275), (3691, 3691, 328512154815514794745), (3692, 3692, 330417958525846725613), (3693, 3693, 332356686550985286909), (3694, 3694, 334329058734612635914), (3695, 3695, 336335814323716999397), (3696, 3696, 338377712587688809957), (3697, 3697, 340455533460065133417), (3698, 3698, 342570078203852235995), (3699, 3699, 344722170101398342831), (3700, 3700, 346912655169832935796), (3701, 3701, 349142402903135440780), (3702, 3702, 351412307041944981836), (3703, 3703, 353723286372274157552), (3704, 3704, 356076285554343657004), (3705, 3705, 358472275982811119600), (3706, 3706, 360912256679727104335), (3707, 3707, 363397255221613527475), (3708, 3708, 365928328702125620827), (3709, 3709, 368506564731827532898), (3710, 3710, 371133082476684330235), (3711, 3711, 373809033736949555176), (3712, 3712, 376535604068207870185), (3713, 3713, 379314013946416891673), (3714, 3714, 382145519978881324990), (3715, 3715, 385031416163186208826), (3716, 3716, 387973035196214728635), (3717, 3717, 390971749835479948263), (3718, 3718, 394028974315109237493), (3719, 3719, 397146165818935460097), (3720, 3720, 400324826013270471247), (3721, 3721, 403566502642064514979), (3722, 3722, 406872791187290094547), (3723, 3723, 410245336597531217393), (3724, 3724, 413685835087909024487), (3725, 3725, 417196036014633160262), (3726, 3726, 420777743827635312982), (3727, 3727, 424432820104917675787), (3728, 3728, 428163185672435198780), (3729, 3729, 431970822813527010725), (3730, 3730, 435857777572119911468), (3731, 3731, 439826162154146039885), (3732, 3732, 443878157431848417050), (3733, 3733, 448016015555892806761), (3734, 3734, 452242062680463031489), (3735, 3735, 456558701806790390006), (3736, 3736, 460968415750857059062), (3737, 3737, 465473770241319301535), (3738, 3738, 470077417154019988909), (3739, 3739, 474782097889802487214), (3740, 3740, 479590646902700538142), (3741, 3741, 484505995385962656003), (3742, 3742, 489531175123776107136), (3743, 3743, 494669322516986183947), (3744, 3744, 499923682791562771646), (3745, 3745, 505297614399049778479), (3746, 3746, 510794593618745619519), (3747, 3747, 516418219371906491021), (3748, 3748, 522172218258840658826), (3749, 3749, 528060449830373562137), (3750, 3750, 534086912105812505662), (3751, 3751, 540255747350228542861), (3752, 3752, 546571248124604478851), (3753, 3753, 553037863623174568597), (3754, 3754, 559660206313106480217), (3755, 3755, 566443058892552677098), (3756, 3756, 573391381584030020959), (3757, 3757, 580510319781076836770), (3758, 3758, 587805212067189904707), (3759, 3759, 595281598627164140097), (3760, 3760, 602945230072149688370), (3761, 3761, 610802076701009734627), (3762, 3762, 618858338221912806458), (3763, 3763, 627120453959531426106), (3764, 3764, 635595113574750759150), (3765, 3765, 644289268325422983196), (3766, 3766, 653210142898442525889), (3767, 3767, 662365247845271693513), (3768, 3768, 671762392655023700455), (3769, 3769, 681409699501319508012), (3770, 3770, 691315617701385651500), (3771, 3771, 701488938928262565963), (3772, 3772, 711938813219557786438), (3773, 3773, 722674765828917620884), (3774, 3774, 733706714969317213623), (3775, 3775, 745044990500396070150), (3776, 3776, 756700353615408913275), (3777, 3777, 768684017586936165607), (3778, 3778, 781007669634321648779), (3779, 3779, 793683493979895871010), (3780, 3780, 806724196165421643727), (3781, 3781, 820143028704886440271), (3782, 3782, 833953818154786350572), (3783, 3783, 848170993688425061053), (3784, 3784, 862809617266515428279), (3785, 3785, 877885415502550589605), (3786, 3786, 893414813328038272391), (3787, 3787, 909414969569800782344), (3788, 3788, 925903814559171709556), (3789, 3789, 942900089901109460575), (3790, 3790, 960423390540041491062), (3791, 3791, 978494209268699475376), (3792, 3792, 997133983836356552394), (3793, 3793, 1016365146823789585143), (3794, 3794, 1036211178464023225679), (3795, 3795, 1056696662600534887010), (3796, 3796, 1077847345988182608796), (3797, 3797, 1099690201156739620463), (3798, 3798, 1122253493072665323576), (3799, 3799, 1145566849851705043954), (3800, 3800, 1169661337793190981366), (3801, 3801, 1194569541026623934911), (3802, 3802, 1220325646082368946019), (3803, 3803, 1246965531721227949246), (3804, 3804, 1274526864382400457840), (3805, 3805, 1303049199636063577936), (3806, 3806, 1332574090055663535200), (3807, 3807, 1363145199956195991965), (3808, 3808, 1394808427478462071953), (3809, 3809, 1427612034535739915277), (3810, 3810, 1461606785178746647266), (3811, 3811, 1496846092977443887129), (3812, 3812, 1533386178064446682740), (3813, 3813, 1571286234534843080413), (3814, 3814, 1610608608951460823306), (3815, 3815, 1651418990763402598678), (3816, 3816, 1693786615509421013735), (3817, 3817, 1737784481746867347160), (3818, 3818, 1783489582722015409490), (3819, 3819, 1830983153879072270166), (3820, 3820, 1880350937393732142740), (3821, 3821, 1931683465013356946593), (3822, 3822, 1985076360590489124737), (3823, 3823, 2040630663810201480634), (3824, 3824, 2098453176735624846459), (3825, 3825, 2158656834930812623867), (3826, 3826, 2221361105066941535606), (3827, 3827, 2286692411077854765897), (3828, 3828, 2354784591105387229484), (3829, 3829, 2425779387665161249701), (3830, 3830, 2499826973671134538529), (3831, 3831, 2577086517183808307403), (3832, 3832, 2657726787994523067418), (3833, 3833, 2741926809428737905193), (3834, 3834, 2829876559046874881063), (3835, 3835, 2921777722244720902627), (3836, 3836, 3017844503109286662910), (3837, 3837, 3118304497273491625631), (3838, 3838, 3223399631937468090694), (3839, 3839, 3333387178689412267561), (3840, 3840, 3448540845268917071300), (3841, 3841, 3569151952975212029328), (3842, 3842, 3695530707036824785194), (3843, 3843, 3828007567933541108674), (3844, 3844, 3966934732402476139104), (3845, 3845, 4112687733674576739774), (3846, 3846, 4265667171383730719621), (3847, 3847, 4426300582576511755132), (3848, 3848, 4595044466336061613368), (3849, 3849, 4772386475729415990236), (3850, 3850, 4958847792105649151125), (3851, 3851, 5154985698225844321450), (3852, 3852, 5361396368309921723638), (3853, 3853, 5578717894856322186048), (3854, 3854, 5807633574046926601372), (3855, 3855, 6048875473712029465768), (3856, 3856, 6303228310221748823889), (3857, 3857, 6571533663316748874283), (3858, 3858, 6854694560821453385696), (3859, 3859, 7153680468429376551591), (3860, 3860, 7469532723349029026423), (3861, 3861, 7803370454590699059243), (3862, 3862, 8156397037104843553644), (3863, 3863, 8529907131903022619310), (3864, 3864, 8925294369759756119646), (3865, 3865, 9344059742172985329388), (3866, 3878, 9352773551086494571776), (3879, 3879, 9262033891119344659751), (3880, 3880, 9170330585266677880942), (3881, 3881, 9079535232937304832616), (3882, 3882, 8989638844492381022392), (3883, 3883, 8900632519299387150883), (3884, 3884, 8812507444850878367211), (3885, 3885, 8725254895891958779417), (3886, 3886, 8638866233556394831106), (3887, 3887, 8553332904511282010996), (3888, 3888, 8468646440110180208906), (3889, 3889, 8384798455554633870204), (3890, 3890, 8301780649063993930896), (3891, 3891, 8219584801053459337520), (3892, 3892, 8138202773320256769822), (3893, 3893, 8057626508237877989923), (3894, 3894, 7977848027958295039528), (3895, 3895, 7898859433622074296562), (3896, 3896, 7820652904576311184715), (3897, 3897, 7743220697600308103678), (3898, 3898, 7666555146138918914533), (3899, 3899, 7590648659543484073795), (3900, 3900, 7515493722320281261183), (3901, 3901, 7441082893386417090280), (3902, 3902, 7367408805333086228000), (3903, 3903, 7294464163696124978218), (3904, 3904, 7222241746233787107147), (3905, 3905, 7150734402211670403115), (3906, 3906, 7079935051694723171401), (3907, 3907, 7009836684846260565744), (3908, 3908, 6940432361233921352222), (3909, 3909, 6871715209142496388338), (3910, 3910, 6803678424893560780533), (3911, 3911, 6736315272171842356963), (3912, 3912, 6669619081358259759370), (3913, 3913, 6603583248869564118188), (3914, 3914, 6538201236504518928899), (3915, 3915, 6473466570796553394949), (3916, 3916, 6409372842372825143514), (3917, 3917, 6345913705319628854965), (3918, 3918, 6283082876554087975212), (3919, 3919, 6220874135202067302191), (3920, 3920, 6159281321982244853654), (3921, 3921, 6098298338596282033321), (3922, 3922, 6037919147125031716159), (3923, 3923, 5978137769430724471445), (3924, 3924, 5918948286565073734104), (3925, 3925, 5860344838183241320895), (3926, 3926, 5802321621963605268213), (3927, 3927, 5744872893033272542785), (3928, 3928, 5687992963399279745332), (3929, 3929, 5631676201385425490427), (3930, 3930, 5575917031074678703393), (3931, 3931, 5520709931757107627122), (3932, 3932, 5466049437383274878339), (3933, 3933, 5411930136023044433999), (3934, 3934, 5358346669329746964355), (3935, 3935, 5305293732009650459758), (3936, 3936, 5252766071296683623522), (3937, 3937, 5200758486432360023290), (3938, 3938, 5149265828150851508207), (3939, 3939, 5098282998169159909116), (3940, 3940, 5047804948682336543680), (3941, 3941, 4997826681863699548198), (3942, 3942, 4948343249369999552671), (3943, 3943, 4899349751851484705615), (3944, 3944, 4850841338466816540213), (3945, 3945, 4802813206402788653676), (3946, 3946, 4755260600398800647204), (3947, 3947, 4708178812276040244756), (3948, 3948, 4661563180471326975006), (3949, 3949, 4615409089575571262382), (3950, 3950, 4569711969876803230082), (3951, 3951, 4524467296907725970378), (3952, 3952, 4479670590997748485523), (3953, 3953, 4435317416829453946062), (3954, 3954, 4391403382999459352537), (3955, 3955, 4347924141583623121323), (3956, 3956, 4304875387706557545865), (3957, 3957, 4262252859115403510757), (3958, 3958, 4220052335757825258175), (3959, 3959, 4178269639364183423936), (3960, 3960, 4136900633033844974194), (3961, 3961, 4095941220825589083361), (3962, 3962, 4055387347352068399367), (3963, 3963, 4015234997378285543928), (3964, 3964, 3975480195424045092998), (3965, 3965, 3936119005370341676235), (3966, 3966, 3897147530069645223995), (3967, 3967, 3858561910960044776233), (3968, 3968, 3820358327683212649736), (3969, 3969, 3782532997706151138352), (3970, 3970, 3745082175946684295398), (3971, 3971, 3708002154402657718216), (3972, 3972, 3671289261784809621996), (3973, 3973, 3634939863153276853461), (3974, 3974, 3598950359557699854912), (3975, 3975, 3563317187680890945458), (3976, 3976, 3528036819486030639067), (3977, 3977, 3493105761867357068383), (3978, 3978, 3458520556304313929092), (3979, 3979, 3424277778519122702072), (3980, 3980, 3390374038137745249576), (3981, 3981, 3356805978354203217402), (3982, 3982, 3323570275598221007329), (3983, 3983, 3290663639206159413197), (3984, 3984, 3258082811095207339799), (3985, 3985, 3225824565440799346335), (3986, 3986, 3193885708357227075579), (3987, 3987, 3162263077581412946118), (3988, 3988, 3130953542159814798137), (3989, 3989, 3099954002138430493205), (3990, 3990, 3069261388255871775450), (3991, 3991, 3038872661639477005396), (3992, 3992, 3008784813504432678610), (3993, 3993, 2978994864855873939218), (3994, 3994, 2949499866193934593285), (3995, 3995, 2920296897221717419094), (3996, 3996, 2891383066556155860489), (3997, 3997, 2862755511441738475732), (3998, 3998, 2834411397467067797755), (3999, 3999, 2806347918284225542331), (4000, 4000, 2778562295330916378546), (4001, 4001, 2751051777555362751036), (4002, 4002, 2723813641143923515877), (4003, 4003, 2696845189251409421660), (4004, 4004, 2670143751734068734317), (4005, 4005, 2643706684885216568631), (4006, 4006, 2617531371173481751120), (4007, 4007, 2591615218983645298138), (4008, 4008, 2565955662360044849642), (4009, 4009, 2540550160752519653111), (4010, 4010, 2515396198764870943674), (4011, 4011, 2490491285905812815519), (4012, 4012, 2465832956342388926256), (4013, 4013, 2441418768655830620056), (4014, 4014, 2417246305599832297085), (4015, 4015, 2393313173861220096124), (4016, 4016, 2369617003822990194182), (4017, 4017, 2346155449329693261566), (4018, 4018, 2322926187455141843135), (4019, 4019, 2299926918272417666470), (4020, 4020, 2277155364626156105416), (4021, 4021, 2254609271907085252887), (4022, 4022, 2232286407828797280086), (4023, 4023, 2210184562206729980283), (4024, 4024, 2188301546739336614142), (4025, 4025, 2166635194791422390240), (4026, 4026, 2145183361179626128950), (4027, 4027, 2123943921960025870248), (4028, 4028, 2102914774217847396285), (4029, 4029, 2082093835859254847807), (4030, 4030, 2061479045405202819611), (4031, 4031, 2041068361787329524367), (4032, 4032, 2020859764145870816205), (4033, 4033, 2000851251629575065549), (4034, 4034, 1981040843197599074801), (4035, 4035, 1961426577423365420595), (4036, 4036, 1942006512300361802570), (4037, 4037, 1922778725049863170861), (4038, 4038, 1903741311930557594912), (4039, 4039, 1884892388050057024665), (4040, 4040, 1866230087178274281847), (4041, 4041, 1847752561562647803809), (4042, 4042, 1829457981745195845355), (4043, 4043, 1811344536381382025104), (4044, 4044, 1793410432060774282281), (4045, 4045, 1775653893129479487407), (4046, 4046, 1758073161514336126146), (4047, 4047, 1740666496548847649649), (4048, 4048, 1723432174800839257079), (4049, 4049, 1706368489901821046612), (4050, 4050, 1689473752378040640210), (4051, 4051, 1672746289483208554664), (4052, 4052, 1656184445032879757093), (4053, 4053, 1639786579240475007023), (4054, 4054, 1623551068554925749527), (4055, 4055, 1607476305499926484681), (4056, 4056, 1591560698514778697703), (4057, 4057, 1575802671796810591786), (4058, 4058, 1560200665145357021570), (4059, 4059, 1544753133807284179772), (4060, 4060, 1529458548324043742349), (4061, 4061, 1514315394380241329058), (4062, 4062, 1499322172653704286196), (4063, 4063, 1484477398667033946729), (4064, 4064, 1469779602640627670029), (4065, 4065, 1455227329347156108939), (4066, 4066, 1440819137967481295979), (4067, 4067, 1426553601948001283148), (4068, 4068, 1412429308859407211038), (4069, 4069, 1398444860256838822810), (4070, 4070, 1384598871541424577039), (4071, 4071, 1370889971823192650534), (4072, 4072, 1357316803785339257954), (4073, 4073, 1343878023549840849460), (4074, 4074, 1330572300544396880653), (4075, 4075, 1317398317370689980845), (4076, 4076, 1304354769673950476084), (4077, 4077, 1291440366013812352558), (4078, 4078, 1278653827736447873820), (4079, 4079, 1265993888847968191901), (4080, 4080, 1253459295889077417724), (4081, 4081, 1241048807810967740321), (4082, 4082, 1228761195852443307248), (4083, 4083, 1216595243418260700246), (4084, 4084, 1204549745958673960639), (4085, 4085, 1192623510850172238257), (4086, 4086, 1180815357277398255700), (4087, 4087, 1169124116116235896732), (4088, 4088, 1157548629818055343299), (4089, 4089, 1146087752295104300297), (4090, 4090, 1134740348807033960690), (4091, 4091, 1123505295848548475930), (4092, 4092, 1112381481038166807852), (4093, 4093, 1101367803008085948368), (4094, 4094, 1090463171295134602345), (4095, 4095, 1079666506232806536975), (4096, 4096, 1068976738844362907896), (4097, 4097, 1058392810736992978115), (4098, 4098, 1047913673997022750609), (4099, 4099, 1037538291086161139217), (4100, 4100, 1027265634738773405165), (4101, 4101, 1017094687860171688282), (4102, 4102, 1007024443425912562656), (4103, 4103, 997053904382091646194), (4104, 4104, 987182083546625392271), (4105, 4105, 977408003511510289377), (4106, 4106, 967730696546049791463), (4107, 4107, 958149204501039397488), (4108, 4108, 948662578713900393552), (4109, 4109, 939269879914752864903), (4110, 4110, 929970178133418678122), (4111, 4111, 920762552607345225863), (4112, 4112, 911646091690440817686), (4113, 4113, 902619892762812690779), (4114, 4114, 893683062141398703741), (4115, 4115, 884834714991483865090), (4116, 4116, 876073975239092935733), (4117, 4117, 867399975484250431419), (4118, 4118, 858811856915099437048), (4119, 4119, 850308769222870729751), (4120, 4120, 841889870517693791833), (4121, 4121, 833554327245241378052), (4122, 4122, 825301314104199384210), (4123, 4123, 817130013964553845752), (4124, 4124, 809039617786686975993), (4125, 4125, 801029324541274233656), (4126, 4126, 793098341129974488768), (4127, 4127, 785245882306905434424), (4128, 4128, 777471170600896469727), (4129, 4129, 769773436238511356165), (4130, 4130, 762151917067833025906), (4131, 4131, 754605858483002995947), (4132, 4132, 747134513349507916779), (4133, 4133, 739737141930205858197), (4134, 4134, 732413011812085008116), (4135, 4135, 725161397833747532788), (4136, 4136, 717981582013611418602), (4137, 4137, 710872853478823186734), (4138, 4138, 703834508394874442311), (4139, 4139, 696865849895915289417), (4140, 4140, 689966188015757712294), (4141, 4141, 683134839619562091380), (4142, 4142, 676371128336200090476), (4143, 4143, 669674384491287218293), (4144, 4144, 663043945040878433953), (4145, 4145, 656479153505820231637), (4146, 4146, 649979359906752704591), (4147, 4147, 643543920699755153060), (4148, 4148, 637172198712628864416), (4149, 4149, 630863563081810756848), (4150, 4150, 624617389189911640443), (4151, 4151, 618433058603872911330), (4152, 4152, 612309959013735555772), (4153, 4153, 606247484172015401755), (4154, 4154, 600245033833678615599), (4155, 4155, 594302013696711500593), (4156, 4156, 588417835343278713458), (4157, 4157, 582591916181464072731), (4158, 4158, 576823679387588190823), (4159, 4159, 571112553849097218636), (4160, 4160, 565457974108017048155), (4161, 4161, 559859380304967374411), (4162, 4162, 554316218123730073674), (4163, 4163, 548827938736366409578), (4164, 4164, 543393998748877633246), (4165, 4165, 538013860147403597273), (4166, 4166, 532686990244954056706), (4167, 4167, 527412861628667382877), (4168, 4168, 522190952107591468195), (4169, 4169, 517020744660981651679), (4170, 4170, 511901727387110546216), (4171, 4171, 506833393452584699224), (4172, 4172, 501815241042163068539), (4173, 4173, 496846773309072345088), (4174, 4174, 491927498325814203057), (4175, 4175, 487056929035459606987), (4176, 4176, 482234583203425353453), (4177, 4177, 477459983369728072726), (4178, 4178, 472732656801710963095), (4179, 4179, 468052135447238577322), (4180, 4180, 463417955888355027051), (4181, 4181, 458829659295401016882), (4182, 4182, 454286791381585165230), (4183, 4183, 449788902358005114089), (4184, 4184, 445335546889113974346), (4185, 4185, 440926284048627697372), (4186, 4186, 436560677275869007299), (4187, 4187, 432238294332543571583), (4188, 4188, 427958707259944130280), (4189, 4189, 423721492336578346812), (4190, 4190, 419526230036216184963), (4191, 4191, 415372504986352658379), (4192, 4192, 411259905927081839979), (4193, 4193, 407188025670378059385), (4194, 4194, 403156461059780256817), (4195, 4195, 399164812930475501799), (4196, 4196, 395212686069777724553), (4197, 4197, 391299689177997747083), (4198, 4198, 387425434829700739686), (4199, 4199, 383589539435347267016), (4200, 4200, 379791623203314125758), (4201, 4201, 376031310102291213622), (4202, 4202, 372308227824050706556), (4203, 4203, 368622007746584857976), (4204, 4204, 364972284897608770274), (4205, 4205, 361358697918424525024), (4206, 4206, 357780889028143094083), (4207, 4207, 354238503988260489191), (4208, 4208, 350731192067584642763), (4209, 4209, 347258606007509547290), (4210, 4210, 343820401987633215139), (4211, 4211, 340416239591716054593), (4212, 4212, 337045781773976291676), (4213, 4213, 333708694825719100670), (4214, 4214, 330404648342296139277), (4215, 4215, 327133315190392217106), (4216, 4216, 323894371475635858521), (4217, 4217, 320687496510530552991), (4218, 4218, 317512372782703517812), (4219, 4219, 314368685923468829517), (4220, 4220, 311256124676701811403), (4221, 4221, 308174380868021595449), (4222, 4222, 305123149374278807375), (4223, 4223, 302102128093345353837), (4224, 4224, 299111017914203320630), (4225, 4225, 296149522687330020426), (4226, 4226, 293217349195376257848), (4227, 4227, 290314207124134908760), (4228, 4228, 287439809033796939366), (4229, 4229, 284593870330492019175), (4230, 4230, 281776109238110910074), (4231, 4231, 278986246770406841657), (4232, 4232, 276224006703373110552), (4233, 4233, 273489115547894168863), (4234, 4234, 270781302522667493924), (4235, 4235, 268100299527393558341), (4236, 4236, 265445841116231245882), (4237, 4237, 262817664471516085031), (4238, 4238, 260215509377738698051), (4239, 4239, 257639118195780889159), (4240, 4240, 255088235837406820950), (4241, 4241, 252562609740006753416), (4242, 4242, 250061989841590844966), (4243, 4243, 247586128556030539570), (4244, 4244, 245134780748545088684), (4245, 4245, 242707703711430780875), (4246, 4246, 240304657140030476114), (4247, 4247, 237925403108941065459), (4248, 4248, 235569706048456500455), (4249, 4249, 233237332721244059856), (4250, 4250, 230928052199251544412), (4251, 4251, 228641635840843113279), (4252, 4252, 226377857268161498296), (4253, 4253, 224136492344714354749), (4254, 4254, 221917319153182529454), (4255, 4255, 219720117973448048964), (4256, 4256, 217544671260839652440), (4257, 4257, 215390763624593715287), (4258, 4258, 213258181806528430977), (4259, 4259, 211146714659929139582), (4260, 4260, 209056153128642712457), (4261, 4261, 206986290226378923225), (4262, 4262, 204936921016216755668), (4263, 4263, 202907842590313619473), (4264, 4264, 200898854049815464825), (4265, 4265, 198909756484965806758), (4266, 4266, 196940352955411689859), (4267, 4267, 194990448470704643425), (4268, 4268, 193059849970994696460), (4269, 4269, 191148366307915541050), (4270, 4270, 189255808225658951534), (4271, 4271, 187381988342236585678), (4272, 4272, 185526721130927312552), (4273, 4273, 183689822901908230250), (4274, 4274, 181871111784067554703), (4275, 4275, 180070407706997578913), (4276, 4276, 178287532383165919716), (4277, 4277, 176522309290263286848), (4278, 4278, 174774563653726026582), (4279, 4279, 173044122429431709487), (4280, 4280, 171330814286566048997), (4281, 4281, 169634469590659454453), (4282, 4282, 167954920386791539062), (4283, 4283, 166292000382961919863), (4284, 4284, 164645544933625663231), (4285, 4285, 163015391023391745773), (4286, 4286, 161401377250882916607), (4287, 4287, 159803343812755362978), (4288, 4288, 158221132487876597007), (4289, 4289, 156654586621659997037), (4290, 4290, 155103551110554452512), (4291, 4291, 153567872386687576745), (4292, 4292, 152047398402660967074), (4293, 4293, 150541978616496007004), (4294, 4294, 149051463976728719806), (4295, 4295, 147575706907652197827), (4296, 4296, 146114561294705146364), (4297, 4297, 144667882470005095410), (4298, 4298, 143235527198024846940), (4299, 4299, 141817353661410739545), (4300, 4300, 140413221446941326282), (4301, 4301, 139022991531625075527), (4302, 4302, 137646526268935718343), (4303, 4303, 136283689375183879548), (4304, 4304, 134934345916023643117), (4305, 4305, 133598362293092715957), (4306, 4306, 132275606230784867284), (4307, 4307, 130965946763153333945), (4308, 4308, 129669254220943894995), (4309, 4309, 128385400218756331678), (4310, 4310, 127114257642333001662), (4311, 4311, 125855700635973268972), (4312, 4312, 124609604590072543536), (4313, 4313, 123375846128784696571), (4314, 4314, 122154303097806630268), (4315, 4315, 120944854552283792345), (4316, 4316, 119747380744835437965), (4317, 4317, 118561763113698453431), (4318, 4318, 117387884270988567753), (4319, 4319, 116225627991077789855), (4320, 4320, 115074879199086920648), (4321, 4321, 113935523959492000642), (4322, 4322, 112807449464843564992), (4323, 4323, 111690544024597589101), (4324, 4324, 110584697054057018912), (4325, 4325, 109489799063422791002), (4326, 4326, 108405741646953258418), (4327, 4327, 107332417472230948928), (4328, 4328, 106269720269535592998), (4329, 4329, 105217544821322369305), (4330, 4330, 104175786951804326045), (4331, 4331, 103144343516637946579), (4332, 4332, 102123112392710838197), (4333, 4333, 101111992468030532868), (4334, 4334, 100110883631713398880), (4335, 4335, 99119686764072672158), (4336, 4336, 98138303726804625899), (4337, 4337, 97166637353271906831), (4338, 4338, 96204591438883076070), (4339, 4339, 95252070731567402050), (4340, 4340, 94308980922343962425), (4341, 4341, 93375228635984121213), (4342, 4342, 92450721421766456647), (4343, 4343, 91535367744323224403), (4344, 4344, 90629076974577449904), (4345, 4345, 89731759380769752380), (4346, 4346, 88843326119574012257), (4347, 4347, 87963689227301002235), (4348, 4348, 87092761611189111124), (4349, 4349, 86230457040781298142), (4350, 4350, 85376690139387423903), (4351, 4351, 84531376375631112775), (4352, 7209, 83694432055080309679)]

def glob4 : ℕ := 9352773551086494571776

def runs5 : List (ℕ × ℕ × ℕ) := [(0, 3865, 0), (3866, 3866, 128042389219751056), (3867, 3867, 128127776999133552), (3868, 3868, 128241441107956668), (3869, 3869, 128384350019300277), (3870, 3870, 128557537049408221), (3871, 3871, 128762105423404345), (3872, 3872, 128999233826794903), (3873, 3873, 129270182497621050), (3874, 3874, 129576299921283493), (3875, 3875, 129919030198281418), (3876, 3876, 130299921164566390), (3877, 3877, 130720633355118408), (3878, 3878, 131182949913954499), (3879, 3879, 131688787568376413), (3880, 3880, 132240208802206793), (3881, 3881, 132839435382476070), (3882, 3882, 133488863417013426), (3883, 3883, 134191080147276246), (3884, 3884, 134948882712261854), (3885, 3885, 135765299156376979), (3886, 3886, 136643611997779732), (3887, 3887, 137587384725278009), (3888, 3888, 138600491652982478), (3889, 3889, 139687151634551759), (3890, 3890, 140851966225467047), (3891, 3891, 142099962985337920), (3892, 3892, 143436644736490568), (3893, 3893, 144868045744646363), (3894, 3894, 146400795968125585), (3895, 3895, 148042194740919864), (3896, 3896, 149800295521223913), (3897, 3897, 151684003662017585), (3898, 3898, 153703189558483064), (3899, 3899, 155868820016761855), (3900, 3900, 158193111293159109), (3901, 3901, 160689708002250032), (3902, 3902, 163373893024736108), (3903, 3903, 166262834710614597), (3904, 3904, 169375879133830941), (3905, 3905, 172734896993264040), (3906, 3906, 176364697078062304), (3907, 3907, 180293521160870106), (3908, 3908, 184553638928841179), (3909, 3909, 189182066339980542), (3910, 3910, 194221436897252394), (3911, 3911, 199721063141550508), (3912, 3912, 205738235648507533), (3913, 3913, 212339819548185552), (3914, 3914, 219604224740921331), (3915, 3915, 227623846273522037), (3916, 3916, 236508096397221542), (3917, 3917, 246387179890542664), (3918, 3918, 257416798508169483), (3919, 3919, 269784005842690447), (3920, 3920, 283714462742103197), (3921, 3921, 299481349058524092), (3922, 3922, 317416136971060485), (3923, 3923, 337921263574787493), (3924, 3924, 361484351247534493), (3925, 3925, 388692850381678124), (3926, 3926, 420246605251484897), (3927, 3927, 456963682452769710), (3928, 3928, 499771942574254474), (3929, 3929, 549676168533232526), (3930, 3930, 607690443743319989), (3931, 3931, 674731695948761121), (3932, 3932, 751485685468935165), (3933, 3933, 838277560295044100), (3934, 3934, 934991836076026001), (3935, 3935, 1041075840853981833), (3936, 3936, 1155626937020430017), (3937, 3937, 1277529347638586002), (3938, 3938, 1405594376513496613), (3939, 3939, 1538670424219278757), (3940, 3940, 1675711047808603196), (3941, 3941, 1815805756696977373), (3942, 3942, 1958184931652967939), (3943, 3943, 2102210034336850496), (3944, 3944, 2247357268522445426), (3945, 3945, 2393199667011765170), (3946, 3946, 2539390193019570555), (3947, 3947, 2685646950039689451), (3948, 3948, 2831740769960806761), (3949, 3949, 2977485049197646994), (3950, 3950, 3122727542630230839), (3951, 3951, 3267343788670533861), (3952, 3952, 3411231859118329185), (3953, 3953, 3554308169288377106), (3954, 3954, 3696504129860164386), (3955, 3955, 3837763464386637826), (3956, 3956, 3978040052690130799), (3957, 3957, 4117296190091955669), (3958, 3958, 4255501176172954568), (3959, 3959, 4392630165475696423), (3960, 3960, 4528663227184751054), (3961, 3961, 4663584572205484030), (3962, 3962, 4797381914909577420), (3963, 3963, 4930045943694345623), (3964, 3964, 5061569879859513969), (3965, 3965, 5191949108486602022), (3966, 3966, 5321180868280223695), (3967, 3967, 5449263989903294975), (3968, 3968, 5576198674367241280), (3969, 3969, 5701986304644990853), (3970, 3970, 5826629284951918873), (3971, 3971, 5950130903159633869), (3972, 3972, 6072495212624888852), (3973, 3973, 6193726930373780944), (3974, 3974, 6313831349113043614), (3975, 3975, 6432814260971569902), (3976, 3976, 6550681891226626067), (3977, 3977, 6667440840556460400), (3978, 3978, 6783098034596745897), (3979, 3979, 6897660679772461306), (3980, 3980, 7011136224537310794), (3981, 3981, 7123532325285905931), (3982, 3982, 7234856816314724518), (3983, 3983, 7345117683300367343), (3984, 3984, 7454323039841119088), (3985, 3985, 7562481106672923255), (3986, 3986, 7669600193225745464), (3987, 3987, 7775688681232670106), (3988, 3988, 7880755010143377824), (3989, 3989, 7984807664127054713), (3990, 3990, 8087855160478249555), (3991, 3991, 8189906039263515862), (3992, 3992, 8290968854067506706), (3993, 3993, 8391052163715076778), (3994, 3994, 8490164524861340363), (3995, 3995, 8588314485354914129), (3996, 3996, 8685510578291055572), (3997, 3997, 8781761316681357047), (3998, 3998, 8877075188675294429), (3999, 3999, 8971460653276446487), (4000, 4000, 9064926136502755130), (4001, 4001, 9157480027945922084), (4002, 4002, 9249130677690048806), (4003, 4003, 9339886393554020617), (4004, 4004, 9429755438625996150), (4005, 4005, 9518746029061760118), (4006, 4006, 9606866332121691836), (4007, 4007, 9694124464423745949), (4008, 4008, 9780528490392180288), (4009, 4009, 9866086420883837219), (4010, 4010, 9950806211975622705), (4011, 4011, 10034695763898460235), (4012, 4012, 10117762920104449922), (4013, 4013, 10200015466455257978), (4014, 4014, 10281461130520917340), (4015, 4015, 10362107580979252859), (4016, 4016, 10441962427107068473), (4017, 4017, 10521033218355061641), (4018, 4018, 10599327443999173072), (4019, 4019, 10676852532861746888), (4020, 4020, 10753615853096476349), (4021, 4021, 10829624712031650508), (4022, 4022, 10904886356066704130), (4023, 4023, 10979407970617512745), (4024, 4024, 11053196680106271756), (4025, 4025, 11126259547992157707), (4026, 4026, 11198603576839294981), (4027, 4027, 11270235708418845953), (4028, 4028, 11341162823842310056), (4029, 4029, 11411391743723360073), (4030, 4030, 11480929228365764770), (4031, 4031, 11549781977975147914), (4032, 4032, 11617956632892516687), (4033, 4033, 11685459773847659359), (4034, 4034, 11752297922230664286), (4035, 4035, 11818477540379951313), (4036, 4036, 11884005031885333749), (4037, 4037, 11948886741904745281), (4038, 4038, 12013128957493372660), (4039, 4039, 12076737907944032469), (4040, 4040, 12139719765137719720), (4041, 4041, 12202080643903338087), (4042, 4042, 12263826602385696946), (4043, 4043, 12324963642420929649), (4044, 4044, 12385497709918551180), (4045, 4045, 12445434695249431959), (4046, 4046, 12504780433639018575), (4047, 4047, 12563540705565181997), (4048, 4048, 12621721237160119693), (4049, 4049, 12679327700615780477), (4050, 4050, 12736365714592319990), (4051, 4051, 12792840844629130878), (4052, 4052, 12848758603558025131), (4053, 4053, 12904124451918176963), (4054, 4054, 12958943798372463223), (4055, 4055, 13013222000124864820), (4056, 4056, 13066964363338617194), (4057, 4057, 13120176143554820631), (4058, 4058, 13172862546111242337), (4059, 4059, 13225028726561061765), (4060, 4060, 13276679791091328909), (4061, 4061, 13327820796940922146), (4062, 4062, 13378456752817807953), (4063, 4063, 13428592619315419392), (4064, 4064, 13478233309327983871), (4065, 4065, 13527383688464643317), (4066, 4066, 13576048575462221670), (4067, 4067, 13624232742596505564), (4068, 4068, 13671940916091914281), (4069, 4069, 13719177776529444575), (4070, 4070, 13765947959252784849), (4071, 4071, 13812256054772501423), (4072, 4072, 13858106609168207378), (4073, 4073, 13903504124488631655), (4074, 4074, 13948453059149512815), (4075, 4075, 13992957828329248149), (4076, 4076, 14037022804362234705), (4077, 4077, 14080652317129844263), (4078, 4078, 14123850654448979429), (4079, 4079, 14166622062458162806), (4080, 4080, 14208970746001115650), (4081, 4081, 14250900869007786661), (4082, 4082, 14292416554872795405), (4083, 4083, 14333521886831258586), (4084, 4084, 14374220908331970765), (4085, 4085, 14414517623407914370), (4086, 4086, 14454415997044076795), (4087, 4087, 14493919955542555234), (4088, 4088, 14533033386884932492), (4089, 4089, 14571760141091909482), (4090, 4090, 14610104030580182423), (4091, 4091, 14648068830516554896), (4092, 4092, 14685658279169276928), (4093, 4093, 14722876078256605164), (4094, 4094, 14759725893292579955), (4095, 4095, 14796211353930016812), (4096, 4096, 14832336054300711260), (4097, 4097, 14868103553352857521), (4098, 4098, 14903517375185682848), (4099, 4099, 14938581009381300561), (4100, 4100, 14973297911333786023), (4101, 4101, 15007671502575480899), (4102, 4102, 15041705171100532065), (4103, 4103, 15075402271685672487), (4104, 4104, 15108766126208252292), (4105, 4105, 15141800023961529086), (4106, 4106, 15174507221967227343), (4107, 4107, 15206890945285377421), (4108, 4108, 15238954387321445438), (4109, 4109, 15270700710130765846), (4110, 4110, 15302133044720289150), (4111, 4111, 15333254491347657740), (4112, 4112, 15364068119817623309), (4113, 4113, 15394576969775819796), (4114, 4114, 15424784050999906216), (4115, 4115, 15454692343688094139), (4116, 4116, 15484304798745074940), (4117, 4117, 15513624338065362286), (4118, 4118, 15542653854814065613), (4119, 4119, 15571396213705110661), (4120, 4120, 15599854251276923351), (4121, 4121, 15628030776165593569), (4122, 4122, 15655928569375535585), (4123, 4123, 15683550384547662074), (4124, 4124, 15710898948225088840), (4125, 4125, 15737976960116387535), (4126, 4126, 15764787093356403761), (4127, 4127, 15791331994764658117), (4128, 4128, 15817614285101347801), (4129, 4129, 15843636559320966526), (4130, 4130, 15869401386823560544), (4131, 4131, 15894911311703638660), (4132, 4132, 15920168852996754176), (4133, 4133, 15945176504923776722), (4134, 4134, 15969936737132872010), (4135, 4135, 15994451994939207506), (4136, 4136, 16018724699562402096), (4137, 4137, 16042757248361737769), (4138, 4138, 16066552015069151380), (4139, 4139, 16090111350020024507), (4140, 4140, 16113437580381789429), (4141, 4141, 16136533010380369201), (4142, 4142, 16159399921524469789), (4143, 4143, 16182040572827742173), (4144, 4144, 16204457201028832289), (4145, 4145, 16226652020809336635), (4146, 4146, 16248627225009681306), (4147, 4147, 16270384984842942160), (4148, 4148, 16291927450106623765), (4149, 4149, 16313256749392414685), (4150, 4150, 16334374990293936633), (4151, 4151, 16355284259612504891), (4152, 4152, 16375986623560917358), (4153, 4153, 16396484127965289491), (4154, 4154, 16416778798464952310), (4155, 4155, 16436872640710430565), (4156, 4156, 16456767640559518067), (4157, 4157, 16476465764271467083), (4158, 4158, 16495968958699308620), (4159, 4159, 16515279151480320297), (4160, 4160, 16534398251224658439), (4161, 4161, 16553328147702170895), (4162, 4162, 16572070712027407001), (4163, 4163, 16590627796842840995), (4164, 4164, 16609001236500325085), (4165, 4165, 16627192847240788274), (4166, 4166, 16645204427372196926), (4167, 4167, 16663037757445792960), (4168, 4168, 16680694600430625438), (4169, 4169, 16698176701886391213), (4170, 4170, 16715485790134600190), (4171, 4171, 16732623576428080630), (4172, 4172, 16749591755118839835), (4173, 4173, 16766392003824295420), (4174, 4174, 16783025983591892279), (4175, 4175, 16799495339062120227), (4176, 4176, 16815801698629947198), (4177, 4177, 16831946674604682759), (4178, 4178, 16847931863368286577), (4179, 4179, 16863758845532136383), (4180, 4180, 16879429186092269848), (4181, 4181, 16894944434583114667), (4182, 4182, 16910306125229721052), (4183, 4183, 16925515777098510699), (4184, 4184, 16940574894246556205), (4185, 4185, 16955484965869404762), (4186, 4186, 16970247466447459885), (4187, 4187, 16984863855890934779), (4188, 4188, 16999335579683390865), (4189, 4189, 17013664069023874848), (4190, 4190, 17027850740967667626), (4191, 4191, 17041896998565658197), (4192, 4192, 17055804231002355635), (4193, 4193, 17069573813732552076), (4194, 4194, 17083207108616649555), (4195, 4195, 17096705464054663428), (4196, 4196, 17110070215118914990), (4197, 4197, 17123302683685425790), (4198, 4198, 17136404178564026070), (4199, 4199, 17149375995627189592), (4200, 4200, 17162219417937607053), (4201, 4201, 17174935715874510163), (4202, 4202, 17187526147258758352), (4203, 4203, 17199991957476699978), (4204, 4204, 17212334379602819797), (4205, 4205, 17224554634521184338), (4206, 4206, 17236653931045696753), (4207, 4207, 17248633466039172572), (4208, 4208, 17260494424531247718), (4209, 4209, 17272237979835130034), (4210, 4210, 17283865293663205434), (4211, 4211, 17295377516241509757), (4212, 4212, 17306775786423077239), (4213, 4213, 17318061231800176448), (4214, 4214, 17329234968815444438), (4215, 4215, 17340298102871929750), (4216, 4216, 17351251728442054822), (4217, 4217, 17362096929175508245), (4218, 4218, 17372834778006077234), (4219, 4219, 17383466337257430567), (4220, 4220, 17393992658747862146), (4221, 4221, 17404414783894005278), (4222, 4222, 17414733743813527628), (4223, 4223, 17424950559426816743), (4224, 4224, 17435066241557665941), (4225, 4225, 17445081791032970257), (4226, 4226, 17454998198781442082), (4227, 4227, 17464816445931355983), (4228, 4228, 17474537503907332177), (4229, 4229, 17484162334526167977), (4230, 4230, 17493691890091726477), (4231, 4231, 17503127113488891649), (4232, 4232, 17512468938276598946), (4233, 4233, 17521718288779950389), (4234, 4234, 17530876080181423078), (4235, 4235, 17539943218611179940), (4236, 4236, 17548920601236491478), (4237, 4237, 17557809116350277174), (4238, 4238, 17566609643458775136), (4239, 4239, 17575323053368348492), (4240, 4240, 17583950208271436949), (4241, 4241, 17592491961831661870), (4242, 4242, 17600949159268093112), (4243, 4243, 17609322637438685835), (4244, 4244, 17617613224922895367), (4245, 4245, 17625821742103478173), (4246, 4246, 17633949001247486860), (4247, 4247, 17641995806586467119), (4248, 4248, 17649962954395864393), (4249, 4249, 17657851233073647994), (4250, 4250, 17665661423218160340), (4251, 4251, 17673394297705198878), (4252, 4252, 17681050621764338206), (4253, 4253, 17688631153054499832), (4254, 4254, 17696136641738776938), (4255, 4255, 17703567830558521430), (4256, 4256, 17710925454906700521), (4257, 4257, 17718210242900529979), (4258, 4258, 17725422915453391146), (4259, 4259, 17732564186346038725), (4260, 4260, 17739634762297106318), (4261, 4261, 17746635343032916556), (4262, 4262, 17753566621356602685), (4263, 4263, 17760429283216548316), (4264, 4264, 17767224007774152067), (4265, 4265, 17773951467470923683), (4266, 4266, 17780612328094918218), (4267, 4267, 17787207248846514765), (4268, 4268, 17793736882403546162), (4269, 4269, 17800201874985786050), (4270, 4270, 17806602866418799599), (4271, 4271, 17812940490197164127), (4272, 4272, 17819215373547065823), (4273, 4273, 17825428137488278692), (4274, 4274, 17831579396895531783), (4275, 4275, 17837669760559270725), (4276, 4276, 17843699831245819500), (4277, 4277, 17849670205756948373), (4278, 4278, 17855581474988853790), (4279, 4279, 17861434223990556038), (4280, 4280, 17867229032021720388), (4281, 4281, 17872966472609907383), (4282, 4282, 17878647113607257891), (4283, 4283, 17884271517246618474), (4284, 4284, 17889840240197112585), (4285, 4285, 17895353833619163033), (4286, 4286, 17900812843218971126), (4287, 4287, 17906217809302457821), (4288, 4288, 17911569266828672195), (4289, 4289, 17916867745462672456), (4290, 4290, 17922113769627884699), (4291, 4291, 17927307858557944541), (4292, 4292, 17932450526348026724), (4293, 4293, 17937542282005667736), (4294, 4294, 17942583629501086417), (4295, 4295, 17947575067817007524), (4296, 4296, 17952517090997993121), (4297, 4297, 17957410188199286656), (4298, 4298, 17962254843735174518), (4299, 4299, 17967051537126869830), (4300, 4300, 17971800743149923175), (4301, 4301, 17976502931881164927), (4302, 4302, 17981158568745183788), (4303, 4303, 17985768114560346112), (4304, 4304, 17990332025584360530), (4305, 4305, 17994850753559392363), (4306, 4306, 17999324745756732253), (4307, 4307, 18003754445021023417), (4308, 4308, 18008140289814051856), (4309, 4309, 18012482714258103837), (4310, 4310, 18016782148178894920), (4311, 4311, 18021039017148074732), (4312, 4312, 18025253742525311696), (4313, 4313, 18029426741499961831), (4314, 4314, 18033558427132325747), (4315, 4315, 18037649208394497873), (4316, 4316, 18041699490210811956), (4317, 4317, 18045709673497886807), (4318, 4318, 18049680155204276225), (4319, 4319, 18053611328349727020), (4320, 4320, 18057503582064048992), (4321, 4321, 18061357301625600690), (4322, 4322, 18065172868499394741), (4323, 4323, 18068950660374826517), (4324, 4324, 18072691051203029824), (4325, 4325, 18076394411233863331), (4326, 4326, 18080061107052531348), (4327, 4327, 18083691501615842585), (4328, 4328, 18087285954288110445), (4329, 4329, 18090844820876698406), (4330, 4330, 18094368453667213977), (4331, 4331, 18097857201458354708), (4332, 4332, 18101311409596409684), (4333, 4333, 18104731420009419901), (4334, 4334, 18108117571241000891), (4335, 4335, 18111470198483830934), (4336, 4336, 18114789633612808150), (4337, 4337, 18118076205217879749), (4338, 4338, 18121330238636546662), (4339, 4339, 18124552055986046777), (4340, 4340, 18127741976195219928), (4341, 4341, 18130900315036057801), (4342, 4342, 18134027385154941853), (4343, 4343, 18137123496103572336), (4344, 4344, 18140188954369591463), (4345, 4345, 18143224063406903747), (4346, 4346, 18146229123665696495), (4347, 4347, 18149204432622163426), (4348, 4348, 18152150284807934337), (4349, 4349, 18155066971839213723), (4350, 4350, 18157954782445631226), (4351, 4351, 18160814002498806761), (4352, 7209, 18446744073709424036)]

def glob5 : ℕ := 19951296389030334859

/-- Every run of kind `k` is ordered, sound and below the global fee. -/
def runsOk (k : ℕ) (runs : List (ℕ × ℕ × ℕ)) (G : ℕ) : Bool :=
  runs.all fun e => decide (e.1 ≤ e.2.1) && okOf k rcPar (lowerQ rcPar.g e.1) (upperQ rcPar.g e.2.1) e.2.2 &&
    decide (e.2.2 ≤ G)

theorem runs0_ok : runsOk 0 runs0 glob0 = true := by decide +kernel
theorem runs1_ok : runsOk 1 runs1 glob1 = true := by decide +kernel
theorem runs2_ok : runsOk 2 runs2 glob2 = true := by decide +kernel
theorem runs3_ok : runsOk 3 runs3 glob3 = true := by decide +kernel
theorem runs4_ok : runsOk 4 runs4 glob4 = true := by decide +kernel
theorem runs5_ok : runsOk 5 runs5 glob5 = true := by decide +kernel

theorem entries0 : (runEntries runs0).map Prod.fst = List.range 7210 :=
  entries_of_contig runs0 (by decide +kernel)
theorem entries1 : (runEntries runs1).map Prod.fst = List.range 7210 :=
  entries_of_contig runs1 (by decide +kernel)
theorem entries2 : (runEntries runs2).map Prod.fst = List.range 7210 :=
  entries_of_contig runs2 (by decide +kernel)
theorem entries3 : (runEntries runs3).map Prod.fst = List.range 7210 :=
  entries_of_contig runs3 (by decide +kernel)
theorem entries4 : (runEntries runs4).map Prod.fst = List.range 7210 :=
  entries_of_contig runs4 (by decide +kernel)
theorem entries5 : (runEntries runs5).map Prod.fst = List.range 7210 :=
  entries_of_contig runs5 (by decide +kernel)

theorem par_ok : parOk rcPar = true := by decide +kernel
theorem glob0_ok : globOk 0 rcPar glob0 = true := by decide +kernel
theorem glob1_ok : globOk 1 rcPar glob1 = true := by decide +kernel
theorem glob2_ok : globOk 2 rcPar glob2 = true := by decide +kernel
theorem glob3_ok : globOk 3 rcPar glob3 = true := by decide +kernel
theorem glob4_ok : globOk 4 rcPar glob4 = true := by decide +kernel
theorem glob5_ok : globOk 5 rcPar glob5 = true := by decide +kernel

/-- The packed (reversed, 4096-bit limbs) fee vector of a run table. -/
def packRuns (runs : List (ℕ × ℕ × ℕ)) : ℕ :=
  ClaudeWCT.Numerics.SharedFees.packList 4096 13 ((runEntries runs).map Prod.snd).reverse

open Lean Elab in
elab "rc_pack% " k:num : term => do
  let v := match k.getNat with
    | 0 => packRuns runs0 | 1 => packRuns runs1 | 2 => packRuns runs2
    | 3 => packRuns runs3 | 4 => packRuns runs4 | _ => packRuns runs5
  return ClaudeWCT.Numerics.SharedGeneratedCoordinate.limbExpr v

section ChunkPack
open Finset

/-- Horner packing of a short list: `∑ i, xs[i] * (2^bits)^i`. -/
def hornerPack (bits : ℕ) (xs : List ℕ) : ℕ := xs.foldr (fun x acc => x + (acc <<< bits)) 0

/-- Chunked packing (`k` chunks of `c` entries, Horner inside a chunk): the same value as
`SharedFees.packList`, with far fewer kernel list steps. -/
def chunkPack (bits c : ℕ) : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | k+1, xs => hornerPack bits (xs.take c) + (chunkPack bits c k (xs.drop c) <<< (bits * c))

theorem hornerPack_sum (bits : ℕ) : ∀ (xs : List ℕ) (n : ℕ), xs.length ≤ n →
    hornerPack bits xs = ∑ i ∈ range n, (xs[i]?.getD 0) * (2 ^ bits) ^ i
  | [], n, _ => by simp [hornerPack]
  | x :: xs, n, h => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at h; omega⟩
      have ih := hornerPack_sum bits xs m (by simp at h; omega)
      have hstep : hornerPack bits (x :: xs) = x + hornerPack bits xs * 2 ^ bits := by
        simp only [hornerPack, List.foldr_cons, Nat.shiftLeft_eq]
      rw [hstep, ih, Finset.sum_range_succ', Finset.sum_mul]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, pow_zero, mul_one,
        pow_succ, ← mul_assoc]
      ring

theorem sum_extend (B : ℕ) (xs : List ℕ) (n N : ℕ) (hl : xs.length ≤ n) (hN : n ≤ N) :
    ∑ i ∈ range N, (xs[i]?.getD 0) * B ^ i = ∑ i ∈ range n, (xs[i]?.getD 0) * B ^ i := by
  obtain ⟨d, rfl⟩ : ∃ d, N = n + d := ⟨N - n, by omega⟩
  rw [Finset.sum_range_add]
  have : ∑ j ∈ range d, (xs[n + j]?.getD 0) * B ^ (n + j) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [List.getElem?_eq_none (by omega)]
    simp
  rw [this, Nat.add_zero]

theorem chunkPack_sum (bits c : ℕ) : ∀ (k : ℕ) (xs : List ℕ), xs.length ≤ c * k →
    chunkPack bits c k xs = ∑ i ∈ range (c * k), (xs[i]?.getD 0) * (2 ^ bits) ^ i
  | 0, xs, _ => by simp [chunkPack]
  | k+1, xs, h => by
      have ih := chunkPack_sum bits c k (xs.drop c) (by simp; rw [Nat.mul_succ] at h; omega)
      have hh := hornerPack_sum bits (xs.take c) c (by simp)
      simp only [chunkPack]
      rw [ih, hh, Nat.shiftLeft_eq, show c * (k + 1) = c + c * k by ring, Finset.sum_range_add,
        Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [List.getElem?_take, if_pos (Finset.mem_range.mp hi)]
      · apply Finset.sum_congr rfl
        intro i _
        rw [List.getElem?_drop, pow_add, pow_mul]
        ring

theorem packList_sum (bits h : ℕ) (xs : List ℕ) :
    SharedFees.packList bits h xs = ∑ i ∈ range (2 ^ h), (xs[i]?.getD 0) * (2 ^ bits) ^ i := by
  rw [SharedFees.packList_eq_tree, SharedFees.packTree_sum]
  simp only [Nat.zero_add]

theorem packRuns_eq_chunk (runs : List (ℕ × ℕ × ℕ))
    (hidx : (runEntries runs).map Prod.fst = List.range 7210) :
    packRuns runs = chunkPack 4096 64 113 ((runEntries runs).map Prod.snd).reverse := by
  have hlen : (((runEntries runs).map Prod.snd).reverse).length = 7210 := by
    have := congrArg List.length hidx
    simpa using this
  rw [packRuns, packList_sum, chunkPack_sum _ _ _ _ (by omega),
    sum_extend _ _ (64 * 113) (2 ^ 13) (by omega) (by norm_num)]

end ChunkPack

noncomputable def Pack0 : ℕ := rc_pack% 0
noncomputable def Pack1 : ℕ := rc_pack% 1
noncomputable def Pack2 : ℕ := rc_pack% 2
noncomputable def Pack3 : ℕ := rc_pack% 3
noncomputable def Pack4 : ℕ := rc_pack% 4
noncomputable def Pack5 : ℕ := rc_pack% 5
theorem pack0_eq : packRuns runs0 = Pack0 :=
  (packRuns_eq_chunk runs0 entries0).trans (by decide +kernel)
theorem pack1_eq : packRuns runs1 = Pack1 :=
  (packRuns_eq_chunk runs1 entries1).trans (by decide +kernel)
theorem pack2_eq : packRuns runs2 = Pack2 :=
  (packRuns_eq_chunk runs2 entries2).trans (by decide +kernel)
theorem pack3_eq : packRuns runs3 = Pack3 :=
  (packRuns_eq_chunk runs3 entries3).trans (by decide +kernel)
theorem pack4_eq : packRuns runs4 = Pack4 :=
  (packRuns_eq_chunk runs4 entries4).trans (by decide +kernel)
theorem pack5_eq : packRuns runs5 = Pack5 :=
  (packRuns_eq_chunk runs5 entries5).trans (by decide +kernel)

end ClaudeWCT.Numerics.RouteCData
end
-- ==== merged from ClaudeWCT_Numerics_RouteCRows ====
section

/-! Route C row dot products and Poisson-envelope certificates at the installed gate (RC938: #938's
cap-777 law through the binomial thinning, so the envelope is `u = 13283369e-8`, `λ = 2018833e-6` on uniform
rows; generated by rc938/lean-notes/gen/rcgen938.py; R6 campaign stream RC, RC_SPEC L7 + L8). The forest numerals of rows 1..4 and the binned masses of rows 1..18
are cached once below, so the six envelope checks do not each re-evaluate them in the kernel. -/

namespace ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData
open ClaudeWCT.Numerics.SharedMoments (forestMoment fieldSize alphabetSize)
open ClaudeWCT.Numerics.N600 (poissonCheckQ)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open Lean Elab Term ClaudeWCT.Numerics.SharedGeneratedCoordinate in
/-- Proposes the packed forest numeral of a small row (evaluated by the elaborator; the kernel
re-checks it in `forest_small_k`). -/
elab "rc_small_forest% " r:num : term => do
  return limbExpr (ClaudeWCT.Numerics.SharedPathPacked.forestFast r.getNat)

/-- Packed forest numerals of rows 1..4 (rows 5..18 are main's `SharedGeneratedForest.Forest_k`). -/
noncomputable def Forest_1 : ℕ := rc_small_forest% 1
noncomputable def Forest_2 : ℕ := rc_small_forest% 2
noncomputable def Forest_3 : ℕ := rc_small_forest% 3
noncomputable def Forest_4 : ℕ := rc_small_forest% 4

theorem forest_small_1 : SharedPathPacked.forest 1 = Forest_1 := by
  rw [SharedPathPacked.forest_eq_fast]; decide +kernel
theorem forest_small_2 : SharedPathPacked.forest 2 = Forest_2 := by
  rw [SharedPathPacked.forest_eq_fast]; decide +kernel
theorem forest_small_3 : SharedPathPacked.forest 3 = Forest_3 := by
  rw [SharedPathPacked.forest_eq_fast]; decide +kernel
theorem forest_small_4 : SharedPathPacked.forest 4 = Forest_4 := by
  rw [SharedPathPacked.forest_eq_fast]; decide +kernel

/-- Packed forest polynomial of row `r` (cached numerals for rows 1..18). -/
noncomputable def forestN (r : ℕ) : ℕ :=
  match r with
  | 1 => Forest_1
  | 2 => Forest_2
  | 3 => Forest_3
  | 4 => Forest_4
  | 5 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_5
  | 6 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_6
  | 7 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_7
  | 8 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_8
  | 9 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_9
  | 10 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_10
  | 11 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_11
  | 12 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_12
  | 13 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_13
  | 14 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_14
  | 15 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_15
  | 16 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_16
  | 17 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_17
  | 18 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_18
  | r => ClaudeWCT.Numerics.SharedPathPacked.forestFast r

/-- Row dot product: binned first moments times fees, plus the global fee on the unbinned mass. -/
noncomputable def dotRow (pack G r F : ℕ) : ℕ :=
  ClaudeWCT.Numerics.SharedFees.packedDot F pack +
    G * (forestMoment r - ClaudeWCT.Numerics.SharedFees.packedDot F
      ClaudeWCT.Numerics.SharedGeneratedFeeVector.MassFee)

open Lean Elab Term ClaudeWCT.Numerics.SharedGeneratedCoordinate in
/-- Proposes the binned mass `packedDot (forestN r) MassFee` of row `r` (re-checked by `mass_checked`). -/
elab "rc_mass% " r:num : term => do
  let k := r.getNat
  let fname := if k ≤ 4 then s!"ClaudeWCT.Numerics.RouteCRows.Forest_{k}"
    else s!"ClaudeWCT.Numerics.SharedGeneratedForest.Forest_{k}"
  let fInfo ← getConstInfo fname.toName
  let mInfo ← getConstInfo ``ClaudeWCT.Numerics.SharedGeneratedFeeVector.MassFee
  match limbValue? fInfo.value!, limbValue? mInfo.value! with
  | some f, some m => return limbExpr (ClaudeWCT.Numerics.SharedFees.packedDot f m)
  | _, _ => throwError "forest or mass vector is not a Nat literal"

/-- Binned masses of rows 1..18. -/
noncomputable def massN (r : ℕ) : ℕ :=
  match r with
  | 1 => rc_mass% 1
  | 2 => rc_mass% 2
  | 3 => rc_mass% 3
  | 4 => rc_mass% 4
  | 5 => rc_mass% 5
  | 6 => rc_mass% 6
  | 7 => rc_mass% 7
  | 8 => rc_mass% 8
  | 9 => rc_mass% 9
  | 10 => rc_mass% 10
  | 11 => rc_mass% 11
  | 12 => rc_mass% 12
  | 13 => rc_mass% 13
  | 14 => rc_mass% 14
  | 15 => rc_mass% 15
  | 16 => rc_mass% 16
  | 17 => rc_mass% 17
  | 18 => rc_mass% 18
  | r => ClaudeWCT.Numerics.SharedFees.packedDot (forestN r) ClaudeWCT.Numerics.SharedGeneratedFeeVector.MassFee

theorem mass_checked : ∀ r, r < 19 →
    ClaudeWCT.Numerics.SharedFees.packedDot (forestN r) ClaudeWCT.Numerics.SharedGeneratedFeeVector.MassFee =
      massN r := by
  decide +kernel

/-- `dotRow` with the cached binned mass. -/
noncomputable def dotRowC (pack G r : ℕ) : ℕ :=
  ClaudeWCT.Numerics.SharedFees.packedDot (forestN r) pack + G * (forestMoment r - massN r)

theorem dotRowC_eq (pack G r : ℕ) (h18 : r ≤ 18) : dotRowC pack G r = dotRow pack G r (forestN r) := by
  unfold dotRowC dotRow
  rw [mass_checked r (by omega)]

noncomputable def rowAll (pack G r : ℕ) : ℕ :=
  if 1 ≤ r ∧ r ≤ 18 then dotRowC pack G r else G * forestMoment r
def rowLong (r : ℕ) : ℕ := if 80 < r then feeScale * forestMoment r else 0

/-- Bank price scale at the gate: `2^31 * gate/2^66 * alphabetSize`. -/
def pst : ℕ := rcPar.g * 2 ^ 24 * 563 ^ 9

def meanN : ℕ := 94187
def meanD : ℕ := 100000
def secN : ℕ := 77593
def secD : ℕ := 10000000
def countN : ℕ := 52297
def countD : ℕ := 10000000
def overN : ℕ := 23496
def overD : ℕ := 10000000
def mgfN : ℕ := 12262
def mgfD : ℕ := 1000
def scarfN : ℕ := 11541
def scarfD : ℕ := 10000000
def longN : ℕ := 1
def longD : ℕ := 100000000000000000000000000000000000000000000000000

theorem env_mean : poissonCheckQ fieldSize 13167581 100000000 2027792 1000000
    (fun r => 16 ^ r * rowAll Pack0 glob0 r) (glob0 * alphabetSize) (glob0 * pst) feeScale meanN meanD 80 = true := by
  decide +kernel
theorem env_sec : poissonCheckQ fieldSize 13167581 100000000 2027792 1000000
    (fun r => 16 ^ r * rowAll Pack1 glob1 r) (glob1 * alphabetSize) (glob1 * pst) feeScale secN secD 80 = true := by
  decide +kernel
theorem env_count : poissonCheckQ fieldSize 13167581 100000000 2027792 1000000
    (fun r => 16 ^ r * rowAll Pack2 glob2 r) (glob2 * alphabetSize) (glob2 * pst) feeScale countN countD 80 = true := by
  decide +kernel
theorem env_over : poissonCheckQ fieldSize 13167581 100000000 2027792 1000000
    (fun r => 16 ^ r * rowAll Pack3 glob3 r) (glob3 * alphabetSize) (glob3 * pst) feeScale overN overD 80 = true := by
  decide +kernel
theorem env_mgf : poissonCheckQ fieldSize 13167581 100000000 2027792 1000000
    (fun r => 16 ^ r * rowAll Pack4 glob4 r) (glob4 * alphabetSize) (glob4 * pst) feeScale mgfN mgfD 80 = true := by
  decide +kernel
theorem env_scarf : poissonCheckQ fieldSize 13167581 100000000 2027792 1000000
    (fun r => 16 ^ r * rowAll Pack5 glob5 r) (glob5 * alphabetSize) (glob5 * pst) feeScale scarfN scarfD 80 = true := by
  decide +kernel
theorem env_long : poissonCheckQ fieldSize 13167581 100000000 2027792 1000000
    (fun r => 16 ^ r * rowLong r) (feeScale * alphabetSize) (feeScale * pst) feeScale longN longD 80 = true := by
  decide +kernel

/-! ### Parameter values and the route-C totals (generated) -/

theorem rc_c0 : (rcPar.c0 : ℝ) = (27 / 50 : ℝ) := by norm_num [rcPar]
theorem rc_a : (rcPar.a : ℝ) = (52 / 5 : ℝ) := by norm_num [rcPar]
theorem rc_θ : (rcPar.θ : ℝ) = 99843 / 50000 - 1 / 1024 := by norm_num [rcPar]
theorem rc_m : (rcPar.m : ℝ) = (meanN : ℝ) / meanD := by norm_num [rcPar, meanN, meanD]
theorem rc_vv : (rcPar.vv : ℝ) = (secN : ℝ) / secD := by norm_num [rcPar, secN, secD]

/-- `exp (B - a θ_mid) ≤ (449 / 2500000 : ℝ)` from the Taylor lower bound of `exp (a θ_mid - B)`. -/
theorem rc_exp_mid : Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) ≤ (2045 / 10000000 : ℝ) := by
  have hx : (mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ ≤ -(1699 / 200 : ℝ) := by norm_num [rcPar, mgfN, mgfD]
  have h0 : (0 : ℝ) ≤ (1699 / 200 : ℝ) := by norm_num
  have he := Real.sum_le_exp_of_nonneg h0 30
  have hs : (10000000 / 2045 : ℝ) ≤ ∑ i ∈ Finset.range 30, (1699 / 200 : ℝ) ^ i / (Nat.factorial i) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  refine (Real.exp_le_exp.mpr hx).trans ?_
  rw [Real.exp_neg, show (2045 / 10000000 : ℝ) = ((10000000 / 2045 : ℝ))⁻¹ by norm_num]
  exact inv_anti₀ (by norm_num) (hs.trans he)

/-- Route-C total at the middle threshold: `K0 + K1 + O Λ + tF ≤ (1153 / 1000000 : ℝ)`. -/
theorem rc_total_mid :
    3 / (8 * (rcPar.a : ℝ)) * Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (1174 / 1000000 : ℝ) := by
  have hk : (0 : ℝ) ≤ 3 / (8 * (rcPar.a : ℝ)) := by rw [rc_a]; norm_num
  have h1 := mul_le_mul_of_nonneg_left rc_exp_mid hk
  have h2 : 3 / (8 * (rcPar.a : ℝ)) * (2045 / 10000000 : ℝ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (1174 / 1000000 : ℝ) := by
    rw [rc_a]; norm_num [scarfN, scarfD, overN, overD, countN, countD, longN, longD]
  linarith

/-- Low threshold: `3/(8a) exp (B - a (1 - 1/1024)) + O ≤ 49/100`. -/
theorem rc_total_low :
    3 / (8 * (rcPar.a : ℝ)) * Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * (1 - 1 / 1024)) + (overN : ℝ) / overD ≤
      49 / 100 := by
  have hy : (mgfN : ℝ) / mgfD - rcPar.a * (1 - 1 / 1024) ≤ 2 := by norm_num [rcPar, mgfN, mgfD]
  have he : Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * (1 - 1 / 1024)) ≤ (2.7182818286 : ℝ) ^ 2 := by
    refine (Real.exp_le_exp.mpr hy).trans ?_
    have hp : Real.exp (2 : ℝ) = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [hp]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le _
  have hk : (0 : ℝ) ≤ 3 / (8 * (rcPar.a : ℝ)) := by rw [rc_a]; norm_num
  have h1 := mul_le_mul_of_nonneg_left he hk
  have h2 : 3 / (8 * (rcPar.a : ℝ)) * (2.7182818286 : ℝ) ^ 2 + (overN : ℝ) / overD ≤ 49 / 100 := by
    rw [rc_a]; norm_num [overN, overD]
  linarith

end ClaudeWCT.Numerics.RouteCRows
end
-- ==== merged from ClaudeWCT_Numerics_V6Budgets ====
section

/-! # img-v6 keygen and expand moment certificates (opus-crumbs PORT v6 D, E; requests N1, N2 of the top-bytes porter)

* **N1 (keygen).** `z = 2^(1/2^20)`. For heights `h = 1..11` (`p_h = 2^-h`) the explicit rationals `m_h = keygenM (h-1)/2^128`
  satisfy `z·(p_h + (1 - p_h)·m_h) ≤ m_h` and `z ≤ m_h`, and `z^1003010 · Π_h m_h^(2^(12-h)) ≤ 2` (value 1.9993336;
  exact 1.99933317 with `m_h = z p/(1 - z(1-p))`; 1,003,010 = 1,007,104 − 4,094 first trials folded into `m_h`).
* **N2 (expand excess, max-of-two form).** `w = 2^((8/7)/2^20) = 2^(1/917504)`:
  `w^427665 · 2^-38 · Σ_{a,b<2^19} w^max(a,b) ≤ 2` (value ≈ 1.806; certified through 64 blocks of `2^13`, 1.8121).
Both are fixed-point certificates (`CanonicalCompression.powerUp`/`mulUp`, scale `2^128`): bounded literals only. -/

namespace ClaudeWCT.Numerics.V6Budgets
open CanonicalCompression Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## Generic fixed-point products -/

/-- `Π (b/scale)^e` over a list, rounded up. -/
def prodUp : List (Nat × Nat) → Nat
  | [] => scale
  | e :: es => mulUp (powerUp e.1 e.2) (prodUp es)

theorem prodUp_ratio_ge (l : List (Nat × Nat)) :
    (l.map fun e => ((e.1:ℝ)/scale)^e.2).prod ≤ (prodUp l:ℝ)/scale := by
  induction l with
  | nil => simp [prodUp, scale]
  | cons e es ih =>
    simp only [List.map_cons, List.prod_cons, prodUp]
    have hs : (0:ℝ) ≤ (powerUp e.1 e.2:ℝ)/scale := by positivity
    calc ((e.1:ℝ)/scale)^e.2 * (es.map fun e => ((e.1:ℝ)/scale)^e.2).prod
        ≤ ((powerUp e.1 e.2:ℝ)/scale) * ((prodUp es:ℝ)/scale) :=
          mul_le_mul (powerUp_ratio_ge _ _) ih (List.prod_nonneg (fun x hx => by
            obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx; positivity)) hs
      _ ≤ _ := mulUp_ratio_ge _ _

/-! ## N1: keygen -/

def keygenZNum : Nat := 10000000000 * 2^20
def keygenZDen : Nat := 10000000000 * 2^20 - 6931471808

theorem keygen_z_le : (2:ℝ)^(1/((2^20:ℕ):ℝ)) ≤ (keygenZNum:ℝ)/keygenZDen := by
  refine (SigGolfCandidate.Budget.rpow_two_inv_le (2^20) (by norm_num)).trans_eq ?_
  norm_num [keygenZNum, keygenZDen]

/-- `ceil(zK·2^128)` for `zK = keygenZNum/keygenZDen`. -/
def keygenZFix : Nat := 340282591860207742199512195861285667957

theorem keygenZ_fix : (keygenZNum:ℝ)/keygenZDen ≤ (keygenZFix:ℝ)/scale := by
  rw [div_le_div_iff₀ (by norm_num [keygenZDen]) (by norm_num [scale])]
  norm_num [keygenZNum, keygenZDen, keygenZFix, scale]

/-- Numerators (over `2^128`) of `m_h`, `h = 1..11`. -/
def keygenM (i : Fin 11) : Nat := [340282816799774407537068188648745253159, 340283266679799900375442987250372351646, 340284166443419551218384362561208825066, 340285965984933645675468342432275971788, 340289565125062062546873124227847124433, 340296763633728263433442488925276359072, 340311161564765781666276742203532247926, 340339961082202552920555136142458666879, 340397574742854560594048527114301253582, 340512860601946649704814937144529402626, 340743666749029370512803021620717668290].getD i.val 0

theorem keygen_step_zK : ∀ i : Fin 11,
    (keygenZNum:ℝ)/keygenZDen * (1/2^(i.val+1) + (1 - 1/2^(i.val+1)) * ((keygenM i:ℝ)/2^128)) ≤
      (keygenM i:ℝ)/2^128 ∧ (keygenZNum:ℝ)/keygenZDen ≤ (keygenM i:ℝ)/2^128 := by
  intro i
  fin_cases i <;> norm_num [keygenM, keygenZNum, keygenZDen]

/-- `m_h` is a geometric retry bound for every `0 ≤ z ≤ zK` (in particular `z = 2^(1/2^20)`). -/
theorem keygen_step (i : Fin 11) (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ (keygenZNum:ℝ)/keygenZDen) :
    z * (1/2^(i.val+1) + (1 - 1/2^(i.val+1)) * ((keygenM i:ℝ)/2^128)) ≤ (keygenM i:ℝ)/2^128 ∧
      z ≤ (keygenM i:ℝ)/2^128 := by
  obtain ⟨h1, h2⟩ := keygen_step_zK i
  have hq : (1:ℝ)/2^(i.val+1) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hp : 0 ≤ (1:ℝ)/2^(i.val+1) + (1 - 1/2^(i.val+1)) * ((keygenM i:ℝ)/2^128) := by
    have : 0 ≤ 1 - (1:ℝ)/2^(i.val+1) := by linarith
    positivity
  exact ⟨(mul_le_mul_of_nonneg_right hz hp).trans h1, hz.trans h2⟩

def keygenList : List (Nat × Nat) := [(keygenZFix,1003010),(340282816799774407537068188648745253159,2048),(340283266679799900375442987250372351646,1024),(340284166443419551218384362561208825066,512),(340285965984933645675468342432275971788,256),(340289565125062062546873124227847124433,128),(340296763633728263433442488925276359072,64),(340311161564765781666276742203532247926,32),(340339961082202552920555136142458666879,16),(340397574742854560594048527114301253582,8),(340512860601946649704814937144529402626,4),(340743666749029370512803021620717668290,2)]

theorem keygen_list_checked : prodUp keygenList * 100000 < 199934 * scale := by decide +kernel

attribute [irreducible] prodUp

theorem keygen_list_prod (x : ℝ) (m : Fin 11 → ℝ) (hm : ∀ i, m i = ((keygenM i:ℝ)/scale)) :
    (keygenList.map fun e => ((e.1:ℝ)/scale)^e.2).prod =
      ((keygenZFix:ℝ)/scale)^1003010 * ∏ i : Fin 11, (m i)^(2^(11-i.val)) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, hm]
  simp only [keygenList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, keygenM]
  norm_num

theorem keygen_moment (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ (keygenZNum:ℝ)/keygenZDen) :
    z^1003010 * ∏ i : Fin 11, ((keygenM i:ℝ)/2^128)^(2^(11-i.val)) ≤ 2 := by
  have hs : (scale:ℝ) = 2^128 := by norm_num [scale]
  have hzf := hz.trans keygenZ_fix
  have hprod := prodUp_ratio_ge keygenList
  rw [keygen_list_prod 0 (fun i => (keygenM i:ℝ)/scale) (fun _ => rfl)] at hprod
  have hnum : (prodUp keygenList:ℝ)/scale < 199934/100000 := by
    have h := keygen_list_checked
    have h' : (prodUp keygenList:ℝ)*100000 < 199934*(scale:ℝ) := by exact_mod_cast h
    have hs0 : (0:ℝ) < scale := by norm_num [scale]
    generalize (prodUp keygenList:ℝ) = P at h' ⊢
    generalize (scale:ℝ) = S at h' hs0 ⊢
    rw [div_lt_iff₀ hs0]; linarith
  have hstep : z^1003010 * ∏ i : Fin 11, ((keygenM i:ℝ)/2^128)^(2^(11-i.val)) ≤
      ((keygenZFix:ℝ)/scale)^1003010 * ∏ i : Fin 11, ((keygenM i:ℝ)/scale)^(2^(11-i.val)) := by
    rw [hs] at hzf ⊢
    gcongr
  linarith


/-! ## N2: expand excess (max of two uniform 19-bit candidates) -/

def expandWNum : Nat := 10000000000 * 917504
def expandWDen : Nat := 10000000000 * 917504 - 6931471808

/-- `(8/7)/2^20 = 1/917504`. -/
theorem expand_w_le : (2:ℝ)^(1/((917504:ℕ):ℝ)) ≤ (expandWNum:ℝ)/expandWDen := by
  refine (SigGolfCandidate.Budget.rpow_two_inv_le 917504 (by norm_num)).trans_eq ?_
  norm_num [expandWNum, expandWDen]

def expandWFix : Nat := 340282623994413344176749661942838553419

theorem expandW_fix : (expandWNum:ℝ)/expandWDen ≤ (expandWFix:ℝ)/scale := by
  rw [div_le_div_iff₀ (by norm_num [expandWDen]) (by norm_num [scale])]
  norm_num [expandWNum, expandWDen, expandWFix, scale]

/-- `pw k ≥ (w^8192)^k · scale` (iterated rounded-up products). -/
def blockV : Nat := powerUp expandWFix 8192
def pw : Nat → Nat
  | 0 => scale
  | k + 1 => mulUp blockV (pw k)

theorem pw_ratio_ge (k : Nat) : (((blockV:ℝ)/scale))^k ≤ (pw k:ℝ)/scale := by
  induction k with
  | zero => simp [pw, scale]
  | succ k ih =>
    rw [pow_succ', pw]
    exact (mul_le_mul_of_nonneg_left ih (by positivity)).trans (mulUp_ratio_ge _ _)

def blockSum : Nat := ∑ i ∈ range 64, ∑ j ∈ range 64, pw (max i j + 1)

theorem expand_block_checked : mulUp (powerUp expandWFix 427665) blockSum * 100000 <
    181213 * scale * 4096 := by decide +kernel

theorem blockV_eq : blockV = powerUp expandWFix 8192 := rfl

attribute [irreducible] blockSum blockV

theorem sum_range_mul_div (F : ℕ → ℝ) (J L : ℕ) (hL : 0 < L) :
    ∑ a ∈ range (J*L), F (a / L) = L * ∑ i ∈ range J, F i := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    have h : ∀ x ∈ range L, F ((J*L + x) / L) = F J := by
      intro x hx
      congr 1
      rw [Finset.mem_range] at hx
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hx, Nat.zero_add]
    rw [Finset.sum_congr rfl h]
    simp

theorem max_block_le (a b L : ℕ) (hL : 0 < L) : max a b ≤ L * (max (a/L) (b/L) + 1) := by
  have ha := Nat.lt_mul_div_succ a hL
  have hb := Nat.lt_mul_div_succ b hL
  have h1 : L * (a/L + 1) ≤ L * (max (a/L) (b/L) + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : L * (b/L + 1) ≤ L * (max (a/L) (b/L) + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem expand_excess_moment (w : ℝ) (hw1 : 1 ≤ w) (hw : w ≤ (expandWNum:ℝ)/expandWDen) :
    w^427665 * ((1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)) ≤ 2 := by
  have hwf := hw.trans expandW_fix
  have hw0 : 0 ≤ w := by linarith
  set v : ℝ := w^8192 with hv
  -- blocks: w^max a b ≤ v^(max (a/L) (b/L) + 1)
  have hpt : ∀ a b : ℕ, w^(max a b) ≤ v^(max (a/8192) (b/8192) + 1) := by
    intro a b
    rw [hv, ← pow_mul]
    exact pow_le_pow_right₀ hw1 (max_block_le a b 8192 (by norm_num))
  have hR : (2:ℕ)^19 = 64 * 8192 := by norm_num
  have hsum : ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b) ≤
      (8192:ℝ) * (8192 * ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)) := by
    calc ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)
        ≤ ∑ a ∈ range (64*8192), ∑ b ∈ range (64*8192), v^(max (a/8192) (b/8192) + 1) := by
          rw [hR]; exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
      _ = (8192:ℝ) * ∑ i ∈ range 64, ∑ b ∈ range (64*8192), v^(max i (b/8192) + 1) :=
          sum_range_mul_div (fun i => ∑ b ∈ range (64*8192), v^(max i (b/8192) + 1)) 64 8192 (by norm_num)
      _ = (8192:ℝ) * (8192 * ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)) := by
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ =>
            sum_range_mul_div (fun j => v^(max i j + 1)) 64 8192 (by norm_num)
  -- fixed point: v ≤ blockV/scale, v^k ≤ pw k/scale
  have hvb : v ≤ (blockV:ℝ)/scale := by
    rw [hv]
    rw [blockV_eq]
    exact (pow_le_pow_left₀ hw0 hwf 8192).trans (powerUp_ratio_ge _ _)
  have hv0 : 0 ≤ v := by positivity
  have hterm : ∀ i j : ℕ, v^(max i j + 1) ≤ (pw (max i j + 1):ℝ)/scale := fun i j =>
    (pow_le_pow_left₀ hv0 hvb _).trans (pw_ratio_ge _)
  have hblock : ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1) ≤ (blockSum:ℝ)/scale := by
    calc ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)
        ≤ ∑ i ∈ range 64, ∑ j ∈ range 64, (pw (max i j + 1):ℝ)/scale :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = (blockSum:ℝ)/scale := by
          simp only [blockSum, Nat.cast_sum, Finset.sum_div]
  have hK : w^427665 ≤ (powerUp expandWFix 427665:ℝ)/scale :=
    (pow_le_pow_left₀ hw0 hwf _).trans (powerUp_ratio_ge _ _)
  have hcheck : (mulUp (powerUp expandWFix 427665) blockSum:ℝ) * 100000 <
      181213 * (scale:ℝ) * 4096 := by exact_mod_cast expand_block_checked
  have hmul := mulUp_ratio_ge (powerUp expandWFix 427665) blockSum
  have hs : (0:ℝ) < scale := by norm_num [scale]
  have hS : (1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b) ≤
      ((blockSum:ℝ)/scale) / 4096 := by
    have h2 : (1:ℝ)/2^38 * ((8192:ℝ) * (8192 * ((blockSum:ℝ)/scale))) = ((blockSum:ℝ)/scale) / 4096 := by
      generalize ((blockSum:ℝ)/scale) = B
      norm_num; ring
    rw [← h2]
    have h3 : (8192:ℝ) * (8192 * ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)) ≤
        (8192:ℝ) * (8192 * ((blockSum:ℝ)/scale)) := by
      gcongr
    have h4 := hsum.trans h3
    have h5 : (0:ℝ) ≤ 1/2^38 := by positivity
    exact mul_le_mul_of_nonneg_left h4 h5
  have hB : w^427665 * ((1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)) ≤
      ((powerUp expandWFix 427665:ℝ)/scale) * (((blockSum:ℝ)/scale) / 4096) :=
    mul_le_mul hK hS
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => pow_nonneg hw0 _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hC : ((powerUp expandWFix 427665:ℝ)/scale) * (((blockSum:ℝ)/scale) / 4096) ≤
      ((mulUp (powerUp expandWFix 427665) blockSum:ℝ)/scale) / 4096 := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hmul (by norm_num)
  have hD : ((mulUp (powerUp expandWFix 427665) blockSum:ℝ)/scale) / 4096 ≤ 2 := by
    have hs0 : (0:ℝ) < scale := by norm_num [scale]
    generalize (mulUp (powerUp expandWFix 427665) blockSum:ℝ) = P at hcheck ⊢
    generalize (scale:ℝ) = S at hcheck hs0 ⊢
    rw [div_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith


/-! ## N2b in the top-bytes porter's exact form (drop-in for `SharedExpansionV6.ExpandExcessNumeric`)
`avgF φ = Σ_{c<2^19} (2^19)⁻¹·φ c` and `excessWeight c = 2^((8/7)·(427665 + c)/2^20)` in `ℝ≥0∞`
(`expandReplayExtra = 1900 + 425765 = 427665`). -/

noncomputable def avgF19 (φ : Nat → ENNReal) : ENNReal := ∑ c ∈ range (2 ^ 19), ((2 : ENNReal) ^ 19)⁻¹ * φ c

noncomputable def excessWeightV6 (c : Nat) : ENNReal :=
  (2 : ENNReal) ^ ((8 / 7 : ℝ) * ((427665 + c : ℕ) : ℝ) / 1048576)

theorem avgF19_ofReal (ψ : Nat → ℝ) (hψ : ∀ c, 0 ≤ ψ c) :
    avgF19 (fun c => ENNReal.ofReal (ψ c)) = ENNReal.ofReal (∑ c ∈ range (2^19), (1/2^19) * ψ c) := by
  unfold avgF19
  rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => mul_nonneg (by positivity) (hψ c))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, one_div]
  norm_num

theorem excessWeightV6_eq (c : Nat) :
    excessWeightV6 c = ENNReal.ofReal (((2:ℝ)^(1/((917504:ℕ):ℝ)))^(427665 + c)) := by
  unfold excessWeightV6
  rw [show (2:ENNReal) = ENNReal.ofReal 2 by norm_num, ENNReal.ofReal_rpow_of_pos (by norm_num)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  push_cast
  ring

/-- **N2b** (drop-in for `SigGolfCandidate.Research.SharedExpansionV6.expandExcessNumeric_holds`). -/
theorem expand_excess_numeric :
    avgF19 (fun c2 => avgF19 (fun c3 => excessWeightV6 (max c2 c3))) ≤ 2 := by
  set w : ℝ := (2:ℝ)^(1/((917504:ℕ):ℝ)) with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow (by norm_num) (by positivity)
  have hw0 : 0 ≤ w := by linarith
  have hin : ∀ c2, avgF19 (fun c3 => excessWeightV6 (max c2 c3)) =
      ENNReal.ofReal (∑ c3 ∈ range (2^19), (1/2^19) * w^(427665 + max c2 c3)) := by
    intro c2
    simp_rw [excessWeightV6_eq]
    exact avgF19_ofReal (fun c3 => w^(427665 + max c2 c3)) (fun _ => pow_nonneg hw0 _)
  simp_rw [hin]
  rw [avgF19_ofReal _ (fun _ => Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (pow_nonneg hw0 _))]
  have hreal : ∑ c2 ∈ range (2^19), (1/2^19) * ∑ c3 ∈ range (2^19), (1/2^19) * w^(427665 + max c2 c3) =
      w^427665 * ((1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)) := by
    simp only [pow_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hreal]
  have h := expand_excess_moment w hw1 (by rw [hw]; exact expand_w_le)
  calc ENNReal.ofReal _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal h
    _ = 2 := by norm_num

end ClaudeWCT.Numerics.V6Budgets
end
-- ==== merged from ClaudeWCT_Numerics_WCTEnvelope ====
section

namespace ClaudeWCT.Numerics.WCTEnvelope
open Finset ENNReal
open ClaudeWCT.Numerics.Thinning (env ListCov)
open SigGolfResearch.Gate6.Moments (finiteAverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open ClaudeWCT.Bank.WCT (WProposal proposal outIdx CoveredP scoreP price)
open ClaudeWCT.WCT9 (wordDigit Coord Child Rank)
theorem codeWords_eq : ClaudeWCT.WCT9.codeWords = N600.words := by decide +kernel
set_option maxRecDepth 100000 in
theorem ofFn_wordDigit_list :
    List.ofFn (fun r : Fin 563 => List.ofFn (wordDigit r)) = N600.words := by
  rw [← codeWords_eq]
  apply List.ext_getElem
  · exact (List.length_ofFn).trans ClaudeWCT.WCT9.codeWords_length.symm
  · intro i hi hj
    have hi' : i < 563 := by rwa [List.length_ofFn] at hi
    rw [List.getElem_ofFn]
    have h := ClaudeWCT.WCT9.ofFn_wordDigit ⟨i, hi'⟩
    rw [ClaudeWCT.WCT9.codeword_embed] at h
    exact h
theorem wordsOf_wordDigit : N600.WordsOf wordDigit := by
  unfold N600.WordsOf
  rw [Fin.univ_val_map, ofFn_wordDigit_list]
theorem w1Table_wordDigit : N600.W1Table wordDigit :=
  fun p => N600.w1_table wordsOf_wordDigit ClaudeWCT.WCT9.wordDigit_le_four p
theorem w2Table_wordDigit : N600.W2Table wordDigit :=
  fun p => N600.w2_table wordsOf_wordDigit ClaudeWCT.WCT9.wordDigit_le_four p
theorem wfTable_wordDigit (i : Fin 6) : N600.WFTable wordDigit i :=
  fun p => N600.wf_table wordsOf_wordDigit ClaudeWCT.WCT9.wordDigit_le_four i p
theorem card_rank : Fintype.card Rank = 563 := Fintype.card_fin 563
theorem card_child : Fintype.card Child = 128 := Fintype.card_fin 128
abbrev Coords := Coord → Child × Rank
theorem card_coords : Fintype.card Coords = N600.Q ^ 9 :=
  N600.card_table card_rank card_child
theorem mem_atIndex {α β : Type} [DecidableEq α] (index : α) (e : β) (W : List (α × β)) :
    e ∈ atIndex index W ↔ (index, e) ∈ W := by
  unfold atIndex
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨i, e'⟩, hmem, h⟩
    by_cases hi : i = index
    · simp only [hi, if_true, Option.some.injEq] at h
      rw [← hi, ← h]
      exact hmem
    · simp [hi] at h
  · intro h
    exact ⟨(index, e), h, by simp⟩
theorem coveredP_iff (W : List WProposal) (N : SigGolfCandidate.T3.HashOutput) :
    CoveredP W N ↔ ListCov wordDigit (atIndex (outIdx N) W) (proposal N).2 := by
  unfold CoveredP ClaudeWCT.Bank.WCT.SlotCoveredP ListCov
  refine forall_congr' fun k => forall_congr' fun t => ?_
  constructor
  · rintro ⟨p, hp, h1, h2, h3⟩
    refine ⟨p.2, (mem_atIndex _ _ _).mpr ?_, h2, h3⟩
    rw [← h1]
    exact hp
  · rintro ⟨e, he, h2, h3⟩
    exact ⟨(outIdx N, e), (mem_atIndex _ _ _).mp he, rfl, h2, h3⟩
theorem price_scale :
    (2 : ENNReal) ^ 128 * ((1353 * 2 ^ 58 : ℕ) : ENNReal) * ((N600.Q ^ 9 : ℕ) : ENNReal) *
        ((2 ^ 256 : ℕ) : ENNReal)⁻¹ = N600.priceScale := by
  rw [← div_eq_mul_inv]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by unfold N600.priceScale; finiteness)).mp
  unfold N600.priceScale
  norm_num [N600.Q, ENNReal.toReal_mul, ENNReal.toReal_div]
theorem price_eq (W : List WProposal) : price W = N600.priceN wordDigit W := by
  classical
  set g : WProposal → ENNReal := fun p => if ListCov wordDigit (atIndex p.1 W) p.2 then 1 else 0 with hg
  have hs : ∀ N, scoreP W N = if ClaudeWCT.WCT9.admissible N = true then g (proposal N) else 0 := by
    intro N
    unfold scoreP
    by_cases hadm : ClaudeWCT.WCT9.admissible N = true
    · simp only [hadm, true_and, if_true, hg]
      exact if_congr (coveredP_iff W N) rfl rfl
    · simp [hadm]
  have hsum : ∑ p, g p = ((N600.Q ^ 9 : ℕ) : ENNReal) *
      ∑ index : Fin (2 ^ 31), env (n := 9) wordDigit (atIndex index W) := by
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun index _ => ?_
    unfold env finiteAverage
    rw [card_coords, ENNReal.mul_div_cancel (by simp [N600.Q]) (by simp)]
  unfold price SigGolfCandidate.T3.BPORS.finiteAverage
  simp_rw [hs]
  rw [ClaudeWCT.Bank.WCT.sum_admissible g, hsum, Fintype.card_bitVec, N600.priceN, ← price_scale]
  unfold ClaudeWCT.WCT9.gateLimit
  simp only [div_eq_mul_inv]
  ring
end ClaudeWCT.Numerics.WCTEnvelope

namespace ClaudeWCT.Bank.Paired
open Finset ClaudeWCT.Numerics ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
abbrev PairChoice (β : Type) := Fin 2 × (Fin 64 × β) × (Fin 64 × β)
abbrev ForestChoice (β : Type) := (Fin 4 → PairChoice β) × (Fin 128 × β)

def choice {β : Type} (a : AlphabetOf β) : ForestChoice β :=
  (fun p => ((a.1.1 p).1,
    ((a.1.1 p).2.1,a.2 ⟨2*p.val,by omega⟩),
    ((a.1.1 p).2.2,a.2 ⟨2*p.val+1,by omega⟩)),(a.1.2,a.2 8))
def unchoice {β : Type} (a : ForestChoice β) : AlphabetOf β :=
  ((fun p => ((a.1 p).1,(a.1 p).2.1.1,(a.1 p).2.2.1),a.2.1),
    fun k => if hk : k.val<8 then
      if k.val%2=0 then (a.1 ⟨k.val/2,by omega⟩).2.1.2
      else (a.1 ⟨k.val/2,by omega⟩).2.2.2
    else a.2.2)
def choiceEquiv (β : Type) : AlphabetOf β ≃ ForestChoice β where
  toFun := choice
  invFun := unchoice
  left_inv a := by
    apply Prod.ext
    · rfl
    · funext k; fin_cases k <;> rfl
  right_inv a := by
    apply Prod.ext
    · funext p
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · apply Prod.ext
          · rfl
          · fin_cases p <;> rfl
        · apply Prod.ext
          · rfl
          · fin_cases p <;> rfl
    · rfl

theorem covAt_splitRanks {β : Type} [Fintype β] {r : Nat}
    (val : β → Fin 6 → Nat) (o : Fin r → Fin 2) (A : Fin r → Fin 64 × β)
    (s : Fin 2) (target : Fin 64 × β) :
    CovAt val target.1 (val target.2) (splitRanks o A s) ↔
      ∀ t, ∃ j, o j=s ∧ (A j).1=target.1 ∧ val target.2 t ≤ val (A j).2 t := by
  constructor
  · intro h t
    obtain ⟨j,hj,hv⟩ := h t
    let z := (fiberIndex o s).symm j
    exact ⟨z.val,z.property,by simpa only [splitRanks_apply] using hj,
      by simpa only [splitRanks_apply] using hv⟩
  · intro h t
    obtain ⟨j,hj,hc,hv⟩ := h t
    refine ⟨fiberIndex o s ⟨j,hj⟩,?_,?_⟩
    · simpa only [splitRanks_apply, Equiv.symm_apply_apply] using hc
    · simpa only [splitRanks_apply, Equiv.symm_apply_apply] using hv

def PairCovered {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) (a : PairChoice β) : Prop :=
  CovAt val a.2.1.1 (val a.2.1.2) (splitRanks h.1 h.2.1 a.1) ∧
  CovAt val a.2.2.1 (val a.2.2.2) (splitRanks h.1 h.2.2 a.1)
def ForestCovered {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) (a : ForestChoice β) : Prop :=
  (∀ p, PairCovered val (h.1 p) (a.1 p)) ∧ CovAt val a.2.1 (val a.2.2) h.2

theorem card_and_prod {α β : Type} [Fintype α] [Fintype β] (p : α → Prop) (q : β → Prop) :
    #{a : α × β | p a.1 ∧ q a.2} = #{a : α | p a} * #{b : β | q b} := by
  classical
  simp only [card_filter, Fintype.sum_prod_type]
  rw [sum_mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases hp : p a <;> by_cases hq : q b <;> simp [hp,hq]

noncomputable def pairCoveredEquiv {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) :
    {a : PairChoice β // PairCovered val h a} ≃
      (s : Fin 2) × {a : Fin 64 × β // CovAt val a.1 (val a.2) (splitRanks h.1 h.2.1 s)} ×
        {b : Fin 64 × β // CovAt val b.1 (val b.2) (splitRanks h.1 h.2.2 s)} where
  toFun a := ⟨a.val.1, ⟨a.val.2.1,a.property.1⟩,⟨a.val.2.2,a.property.2⟩⟩
  invFun a := ⟨(a.1,a.2.1.val,a.2.2.val),a.2.1.property,a.2.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem pairCovered_card {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) : #{a : PairChoice β | PairCovered val h a} = pairCoverage val h := by
  have he := Fintype.card_congr (pairCoveredEquiv val h)
  simp only [Fintype.card_subtype,Fintype.card_sigma,Fintype.card_prod] at he
  calc
    _ = ∑ s : Fin 2, coordinateCoverage val (splitRanks h.1 h.2.1 s) *
      coordinateCoverage val (splitRanks h.1 h.2.2 s) := he
    _ = _ := by rw [Fin.sum_univ_two]; rfl

noncomputable def forestCoveredEquiv {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) :
    {a : ForestChoice β // ForestCovered val h a} ≃
      ((p : Fin 4) → {a : PairChoice β // PairCovered val (h.1 p) a}) ×
        {b : Fin 128 × β // CovAt val b.1 (val b.2) h.2} where
  toFun a := (fun p => ⟨a.val.1 p,a.property.1 p⟩,⟨a.val.2,a.property.2⟩)
  invFun a := ⟨(fun p => (a.1 p).val,a.2.val),(fun p => (a.1 p).property),a.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem forestCovered_card {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) : #{a : ForestChoice β | ForestCovered val h a} = forestCoverage val h := by
  have he := Fintype.card_congr (forestCoveredEquiv val h)
  simp only [Fintype.card_subtype,Fintype.card_prod,Fintype.card_pi] at he
  calc
    _ = (∏ p, #{a : PairChoice β | PairCovered val (h.1 p) a}) * coordinateCoverage val h.2 := he
    _ = _ := by simp only [pairCovered_card]; rfl

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ClaudeWCT.Numerics ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

theorem rawChild_first (s : Selectors) (p : Fin 4) :
    (rawChild s ⟨2*p.val,by omega⟩).val = 64*(s.1 p).1.val+(s.1 p).2.1.val := by
  fin_cases p <;> rfl

theorem rawChild_second (s : Selectors) (p : Fin 4) :
    (rawChild s ⟨2*p.val+1,by omega⟩).val = 2*(s.1 p).2.2.val+(s.1 p).1.val := by
  fin_cases p <;> rfl

theorem rawChild_first_eq (s u : Selectors) (p : Fin 4) :
    rawChild s ⟨2*p.val,by omega⟩ = rawChild u ⟨2*p.val,by omega⟩ ↔
      (s.1 p).1=(u.1 p).1 ∧ (s.1 p).2.1=(u.1 p).2.1 := by
  rw [Fin.ext_iff, rawChild_first, rawChild_first]
  have ha := (s.1 p).2.1.isLt
  have hb := (u.1 p).2.1.isLt
  simp only [Fin.ext_iff]
  omega

theorem rawChild_second_eq (s u : Selectors) (p : Fin 4) :
    rawChild s ⟨2*p.val+1,by omega⟩ = rawChild u ⟨2*p.val+1,by omega⟩ ↔
      (s.1 p).1=(u.1 p).1 ∧ (s.1 p).2.2=(u.1 p).2.2 := by
  rw [Fin.ext_iff, rawChild_second, rawChild_second]
  have ha := (s.1 p).1.isLt
  have hb := (u.1 p).1.isLt
  simp only [Fin.ext_iff]
  omega

def AlphabetCovered {β : Type} (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (a : AlphabetOf β) : Prop :=
  ∀ k : Fin 9, ∀ t : Fin 6, ∃ j,
    rawChild (h j).1 k = rawChild a.1 k ∧ val (a.2 k) t ≤ val ((h j).2 k) t

theorem forestCovered_choice {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (a : AlphabetOf β) :
    ForestCovered val (splitHistory h) (choice a) ↔ AlphabetCovered val h a := by
  have hfirst (p : Fin 4) :
      CovAt val ((choice a).1 p).2.1.1 (val ((choice a).1 p).2.1.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.1 ((choice a).1 p).1) ↔
      ∀ t : Fin 6, ∃ j, rawChild (h j).1 ⟨2*p.val,by omega⟩ = rawChild a.1 ⟨2*p.val,by omega⟩ ∧
        val (a.2 ⟨2*p.val,by omega⟩) t ≤ val ((h j).2 ⟨2*p.val,by omega⟩) t := by
    rw [covAt_splitRanks]
    simp only [splitHistory, choice, rawChild_first_eq, and_assoc]
  have hsecond (p : Fin 4) :
      CovAt val ((choice a).1 p).2.2.1 (val ((choice a).1 p).2.2.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.2 ((choice a).1 p).1) ↔
      ∀ t : Fin 6, ∃ j, rawChild (h j).1 ⟨2*p.val+1,by omega⟩ = rawChild a.1 ⟨2*p.val+1,by omega⟩ ∧
        val (a.2 ⟨2*p.val+1,by omega⟩) t ≤ val ((h j).2 ⟨2*p.val+1,by omega⟩) t := by
    rw [covAt_splitRanks]
    simp only [splitHistory, choice, rawChild_second_eq, and_assoc]
  constructor
  · rintro ⟨hp,hs⟩ k t
    have hA : ∀ p : Fin 4, ∃ j, rawChild (h j).1 ⟨2*p.val,by omega⟩ = rawChild a.1 ⟨2*p.val,by omega⟩ ∧
        val (a.2 ⟨2*p.val,by omega⟩) t ≤ val ((h j).2 ⟨2*p.val,by omega⟩) t :=
      fun p => ((hfirst p).mp (hp p).1) t
    have hB : ∀ p : Fin 4, ∃ j, rawChild (h j).1 ⟨2*p.val+1,by omega⟩ = rawChild a.1 ⟨2*p.val+1,by omega⟩ ∧
        val (a.2 ⟨2*p.val+1,by omega⟩) t ≤ val ((h j).2 ⟨2*p.val+1,by omega⟩) t :=
      fun p => ((hsecond p).mp (hp p).2) t
    fin_cases k
    · exact hA 0
    · exact hB 0
    · exact hA 1
    · exact hB 1
    · exact hA 2
    · exact hB 2
    · exact hA 3
    · exact hB 3
    · exact hs t
  · intro hc
    refine ⟨fun p => ⟨(hfirst p).mpr ?_,(hsecond p).mpr ?_⟩,?_⟩
    · exact hc ⟨2*p.val,by omega⟩
    · exact hc ⟨2*p.val+1,by omega⟩
    · exact hc 8

theorem alphabetCovered_card {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) :
    (Finset.univ.filter fun a => AlphabetCovered val h a).card = forestCoverage val (splitHistory h) := by
  classical
  have e := (choiceEquiv β).subtypeEquiv (fun a => (forestCovered_choice val h a).symm)
  have hc := Fintype.card_congr e
  simp only [Fintype.card_subtype] at hc
  exact hc.trans (forestCovered_card val (splitHistory h))

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open SigGolfResearch.Gate6.Moments (finiteAverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def ListAlphabetCovered {β : Type} (val : β → Fin 6 → Nat)
    (W : List (AlphabetOf β)) (a : AlphabetOf β) : Prop :=
  ∀ k : Fin 9, ∀ t : Fin 6, ∃ e ∈ W,
    rawChild e.1 k = rawChild a.1 k ∧ val (a.2 k) t ≤ val (e.2 k) t
noncomputable def bucketEnv {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (W : List (AlphabetOf β)) : ENNReal :=
  finiteAverage (fun a => if ListAlphabetCovered val W a then 1 else 0)

theorem listAlphabetCovered_ofFn {β : Type} (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (a : AlphabetOf β) :
    ListAlphabetCovered val (List.ofFn h) a ↔ AlphabetCovered val h a := by
  simp only [ListAlphabetCovered, AlphabetCovered, List.mem_ofFn]
  refine forall_congr' fun k => forall_congr' fun t => ?_
  constructor
  · rintro ⟨e, ⟨j,rfl⟩, he⟩
    exact ⟨j,he⟩
  · rintro ⟨j,hj⟩
    exact ⟨h j,⟨j,rfl⟩,hj⟩

theorem bucketEnv_ofFn {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) :
    bucketEnv val (List.ofFn h) =
      (SharedCoverage.forestCoverage val (splitHistory h) : ENNReal)/Fintype.card (AlphabetOf β) := by
  unfold bucketEnv finiteAverage
  simp_rw [listAlphabetCovered_ofFn]
  rw [← natCast_card_filter, alphabetCovered_card]

theorem bucketEnv_mono {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (a : AlphabetOf β) (W : List (AlphabetOf β)) : bucketEnv val W ≤ bucketEnv val (a::W) := by
  unfold bucketEnv finiteAverage
  apply ENNReal.div_le_div_right
  apply sum_le_sum
  intro target _
  split_ifs with h1 h2
  · exact le_rfl
  · apply False.elim
    apply h2
    intro k t
    obtain ⟨e,he,hc⟩ := h1 k t
    exact ⟨e,List.mem_cons_of_mem a he,hc⟩
  · exact zero_le_one
  · exact le_rfl

theorem coveredP_bucket (W : List Proposal) (N : SigGolfCandidate.T3.HashOutput) :
    CoveredP W N ↔ ListAlphabetCovered ClaudeWCT.WCT9.wordDigit
      (atIndex (proposal N).1 W) (proposal N).2 := by
  unfold CoveredP SlotCoveredP ListAlphabetCovered
  refine forall_congr' fun k => forall_congr' fun t => ?_
  constructor
  · rintro ⟨p,hp,h1,h2,h3⟩
    refine ⟨p.2,(WCTEnvelope.mem_atIndex _ _ _).mpr ?_,h2,h3⟩
    rw [← h1]
    exact hp
  · rintro ⟨a,ha,h2,h3⟩
    exact ⟨((proposal N).1,a),(WCTEnvelope.mem_atIndex _ _ _).mp ha,rfl,h2,h3⟩

theorem price_scale :
    (2:ENNReal)^128 * ((791*2^62:Nat):ENNReal) *
      (SharedMoments.alphabetSize:ENNReal) * ((2^256:Nat):ENNReal)⁻¹ =
      (SharedMoments.priceScaleTotal:ENNReal)/(2^31) := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [SharedMoments.alphabetSize,SharedMoments.priceScaleTotal,ENNReal.toReal_mul,
    ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow]

theorem price_eq_buckets (W : List Proposal) :
    price W = (SharedMoments.priceScaleTotal:ENNReal)/(2^31) *
      ∑ index : Fin (2^31), bucketEnv ClaudeWCT.WCT9.wordDigit (atIndex index W) := by
  let g : Proposal → ENNReal := fun p =>
    if ListAlphabetCovered ClaudeWCT.WCT9.wordDigit (atIndex p.1 W) p.2 then 1 else 0
  have hs (N : SigGolfCandidate.T3.HashOutput) : scoreP W N =
      if admissible N=true then g (proposal N) else 0 := by
    unfold scoreP
    by_cases ha : admissible N=true
    · simp only [ha,true_and,if_true,g]
      exact if_congr (coveredP_bucket W N) rfl rfl
    · simp [ha]
  have hc : Fintype.card Alphabet=SharedMoments.alphabetSize := alphabet_card (Fintype.card_fin 563)
  have hsum : (∑ p,g p) = (SharedMoments.alphabetSize:ENNReal)*
      ∑ index : Fin (2^31), bucketEnv ClaudeWCT.WCT9.wordDigit (atIndex index W) := by
    rw [Fintype.sum_prod_type,mul_sum]
    apply sum_congr rfl
    intro index _
    unfold bucketEnv finiteAverage
    rw [hc,ENNReal.mul_div_cancel (by norm_num [SharedMoments.alphabetSize]) (by simp)]
  unfold price SigGolfCandidate.T3.BPORS.finiteAverage
  simp_rw [hs]
  rw [sum_admissible g,hsum,Fintype.card_bitVec,← price_scale]
  simp only [div_eq_mul_inv]
  ring

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open SigGolfCandidate.T3.BPORS.History (atIndex)
open SphincsSecurity.Concrete (binomialAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

/-- The actual cap-conditioned bucket law is bounded by the finite paired
history model, for any nonnegative payoff, including capped MGF and residual. -/
theorem law_bucket_payoff_le (r : Nat) (f : ENNReal → ENNReal) :
    Law.lawAvg honestCoordLaw r (fun W => f (bucketEnv ClaudeWCT.WCT9.wordDigit W)) ≤
      kappa^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f ((SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h : ENNReal)/
          SharedMoments.alphabetSize))/(SharedMoments.alphabetSize:ENNReal)^r) := by
  have hc : Fintype.card (AlphabetOf (Fin 563)) = SharedMoments.alphabetSize :=
    alphabet_card (Fintype.card_fin 563)
  have hf (h : Fin r → Alphabet) :
      f (bucketEnv ClaudeWCT.WCT9.wordDigit (List.ofFn h)) =
        f ((SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h) : ENNReal)/
          SharedMoments.alphabetSize) :=
    congrArg f ((bucketEnv_ofFn ClaudeWCT.WCT9.wordDigit h).trans
      (congrArg (fun n : Nat =>
        (SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h) : ENNReal)/(n:ENNReal)) hc))
  exact law_history_le r (fun W => f (bucketEnv ClaudeWCT.WCT9.wordDigit W))
    (fun h => f ((SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h : ENNReal)/
      SharedMoments.alphabetSize)) hf


end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SigGolfCandidate.T3.BPORS.History (atIndex)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

noncomputable def priceBucket (W : List Alphabet) : ENNReal :=
  (SharedMoments.priceScaleTotal : ENNReal)/(2^31) * bucketEnv ClaudeWCT.WCT9.wordDigit W

theorem price_eq_sum (W : List Proposal) :
    price W = ∑ index : Fin (2^31), priceBucket (atIndex index W) := by
  rw [price_eq_buckets]
  exact Finset.mul_sum ..

theorem bucketEnv_sublist {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {W V : List (AlphabetOf β)} (hWV : ∀ x ∈ W, x ∈ V) : bucketEnv val W ≤ bucketEnv val V := by
  unfold bucketEnv SigGolfResearch.Gate6.Moments.finiteAverage
  apply ENNReal.div_le_div_right
  apply sum_le_sum
  intro target _
  split_ifs with hW hV
  · exact le_rfl
  · apply False.elim
    apply hV
    intro k t
    obtain ⟨e,he,hc⟩ := hW k t
    exact ⟨e,hWV e he,hc⟩
  · exact zero_le_one
  · exact le_rfl

theorem priceBucket_insert (L R : List Alphabet) (a : Alphabet) :
    priceBucket (L++R) ≤ priceBucket (L++a::R) := by
  apply mul_le_mul' le_rfl
  apply bucketEnv_sublist
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact List.mem_append_left _ hx
  · exact List.mem_append_right _ (List.mem_cons_of_mem a hx)

/-- The actual paired price has the marked-index bank excess bound once its
single-bucket capped exponential and residual moments have been certified. -/
theorem price_excess_of_bucket_bounds (T : Nat) (cap : ENNReal) (hcap : cap ≠ ⊤)
    (theta slope bound residualBound resultBound : ℝ)
    (htheta : 0 ≤ theta) (hslope : 0 < slope) (hbound : 0 ≤ bound) (hresBound : 0 ≤ residualBound)
    (hmgf : (2^31:ENNReal) * Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T
      (fun L => ENNReal.ofReal (Real.exp (slope*(min (priceBucket L) cap).toReal))-1) ≤
        ENNReal.ofReal bound)
    (hres : (2^31:ENNReal) * Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T
      (fun L => priceBucket L-cap) ≤ ENNReal.ofReal residualBound)
    (hscalar : (3/(8*slope))*Real.exp (bound-slope*theta)+residualBound ≤ resultBound) :
    Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal theta) ≤ ENNReal.ofReal resultBound := by
  have hm : (∑ _i : Fin (2^31), Law.coordAverage (Fintype.card (Fin (2^31)):ENNReal)⁻¹
      honestCoordLaw T
      (fun L => ENNReal.ofReal (Real.exp (slope*(min (priceBucket L) cap).toReal))-1)) ≤
        ENNReal.ofReal bound := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_pow,Nat.cast_ofNat] using hmgf
  have hr : (∑ _i : Fin (2^31), Law.coordAverage (Fintype.card (Fin (2^31)):ENNReal)⁻¹
      honestCoordLaw T (fun L => priceBucket L-cap)) ≤ ENNReal.ofReal residualBound := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_pow,Nat.cast_ofNat] using hres
  have he : (fun W : List Proposal => price W-ENNReal.ofReal theta) =
      (fun W => (∑ i : Fin (2^31), priceBucket (atIndex i W))-ENNReal.ofReal theta) := by
    funext W
    rw [price_eq_sum]
  rw [he]
  exact SharedPathWinsor.law_bucket_excess_general honestCoordLaw honestCoordLaw_sum T
    priceBucket cap hcap theta slope bound residualBound resultBound htheta hslope hbound hresBound
    (fun L a R => priceBucket_insert L R a) hm hr hscalar

end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Bank.Paired
open ENNReal
 theorem normalize_row_arithmetic (a S M D κ fee : ENNReal) (r : Nat)
    (ha0 : a ≠ 0) (hat : a ≠ ⊤) (hS0 : S ≠ 0) (hSt : S ≠ ⊤)
    (hM0 : M ≠ 0) (hMt : M ≠ ⊤) (hD0 : D ≠ 0) (hDt : D ≠ ⊤) :
    (κ^r*((a/S)*fee)/D^r)/(M*a*D/S) = κ^r*fee/(M*D^(r+1)) := by
  have hMD : (M*D^r*D)⁻¹ = M⁻¹*(D^r)⁻¹*D⁻¹ := by
    rw [ENNReal.mul_inv (Or.inr hDt) (Or.inr hD0),
      ENNReal.mul_inv (Or.inl hM0) (Or.inl hMt)]
  have hMAD : (M*a*D*S⁻¹)⁻¹ = M⁻¹*a⁻¹*D⁻¹*S := by
    rw [ENNReal.mul_inv (Or.inr (by simp [hS0])) (Or.inr (by simp [hSt])),
      ENNReal.mul_inv (Or.inr hDt) (Or.inr hD0),
      ENNReal.mul_inv (Or.inl hM0) (Or.inl hMt), inv_inv]
  simp only [div_eq_mul_inv, pow_succ]
  rw [hMAD, ← mul_assoc M (D^r) D, hMD]
  calc
    _ = κ^r*fee*M⁻¹*(D^r)⁻¹*D⁻¹*(a*a⁻¹)*(S*S⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel ha0 hat, ENNReal.mul_inv_cancel hS0 hSt]; ring

end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] Finset.univ

noncomputable def feeCoefficient : ENNReal := 791/2^66

theorem price_coefficient :
    (SharedMoments.priceScaleTotal:ENNReal)/(2^31)/(SharedMoments.alphabetSize:ENNReal) = feeCoefficient := by
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold SharedMoments.alphabetSize; finiteness)
    (by unfold feeCoefficient; finiteness)).mp
  norm_num [SharedMoments.priceScaleTotal,SharedMoments.alphabetSize,feeCoefficient,
    ENNReal.toReal_div]

theorem priceBucket_ofFn {r : Nat} (h : Fin r → Alphabet) :
    priceBucket (List.ofFn h) = feeCoefficient *
      (SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal) := by
  have hc : Fintype.card (AlphabetOf (Fin 563)) = SharedMoments.alphabetSize :=
    alphabet_card (Fintype.card_fin 563)
  have hb := (bucketEnv_ofFn ClaudeWCT.WCT9.wordDigit h).trans
    (congrArg (fun n : Nat =>
      (SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal)/(n:ENNReal)) hc)
  change (SharedMoments.priceScaleTotal:ENNReal)/(2^31)*_ = _
  rw [hb, ← price_coefficient]
  simp only [div_eq_mul_inv]
  ring

theorem law_priceBucket_payoff_le (r : Nat) (f : ENNReal → ENNReal) :
    Law.lawAvg honestCoordLaw r (fun W => f (priceBucket W)) ≤
      kappa^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))/
        (SharedMoments.alphabetSize:ENNReal)^r) :=
  law_history_le r (fun W => f (priceBucket W))
    (fun h => f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))
    (fun h => congrArg f (priceBucket_ofFn h))

theorem lawAvg_div {β : Type} [Fintype β] (v : β → ENNReal) (r : Nat)
    (f : List β → ENNReal) (C : ENNReal) :
    Law.lawAvg v r (fun W => f W/C) = Law.lawAvg v r f/C := by
  simpa only [div_eq_mul_inv,mul_comm] using Law.lawAvg_mul_left v r C⁻¹ f

theorem law_normalized_fee_row (r : Nat) (f : ENNReal → ENNReal)
    (S M fee : ENNReal) (hS0 : S ≠ 0) (hSt : S ≠ ⊤) (hM0 : M ≠ 0) (hMt : M ≠ ⊤)
    (hfee : (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/S*fee) :
    Law.lawAvg honestCoordLaw r
      (fun W => f (priceBucket W)/(M*feeCoefficient*SharedMoments.alphabetSize/S)) ≤
        kappa^r*fee/(M*(SharedMoments.alphabetSize:ENNReal)^(r+1)) := by
  rw [lawAvg_div]
  calc
    _ ≤ (kappa^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))/
        (SharedMoments.alphabetSize:ENNReal)^r))/(M*feeCoefficient*SharedMoments.alphabetSize/S) :=
      ENNReal.div_le_div_right (law_priceBucket_payoff_le r f) _
    _ ≤ (kappa^r*((feeCoefficient/S)*fee)/(SharedMoments.alphabetSize:ENNReal)^r)/
        (M*feeCoefficient*SharedMoments.alphabetSize/S) := by
      apply ENNReal.div_le_div_right
      rw [mul_div_assoc]
      exact mul_le_mul' le_rfl (ENNReal.div_le_div_right hfee _)
    _ = _ := normalize_row_arithmetic feeCoefficient S M SharedMoments.alphabetSize kappa fee r
      (by norm_num [feeCoefficient]) (by unfold feeCoefficient; finiteness)
      hS0 hSt hM0 hMt (by norm_num [SharedMoments.alphabetSize]) (by finiteness)

end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem alphabet_power (r : Nat) :
    SharedMoments.alphabetSize^r * 16^r = SharedMoments.fieldSize^(9*r) := by
  rw [← mul_pow]
  have h : SharedMoments.alphabetSize*16=SharedMoments.fieldSize^9 := by
    norm_num [SharedMoments.alphabetSize,SharedMoments.fieldSize]
  rw [h,pow_mul]

 theorem normalized_denominator (r M fee : Nat) (hM : 0<M) (κ : ENNReal) :
    κ^r*(fee:ENNReal)/((M:ENNReal)*(SharedMoments.alphabetSize:ENNReal)^(r+1)) =
      κ^r*((16^r*fee:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) := by
  have hD : (0:ENNReal)<SharedMoments.alphabetSize := by norm_num [SharedMoments.alphabetSize]
  have hF : (0:ENNReal)<SharedMoments.fieldSize := by norm_num [SharedMoments.fieldSize]
  have hb0 : (M:ENNReal)*(SharedMoments.alphabetSize:ENNReal)^(r+1) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hM.ne') (pow_ne_zero _ hD.ne')
  have hbt : (M:ENNReal)*(SharedMoments.alphabetSize:ENNReal)^(r+1) ≠ ⊤ := by finiteness
  have hd0 : ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.mul_pos hM (by decide +kernel : 0<SharedMoments.alphabetSize))
      (Nat.pow_pos (by decide +kernel : 0<SharedMoments.fieldSize))).ne'
  have hdt : ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.div_eq_div_iff hd0 hdt hb0 hbt).2
  simp only [Nat.cast_mul,Nat.cast_pow,pow_succ]
  have hp : (SharedMoments.fieldSize:ENNReal)^(9*r) =
      (SharedMoments.alphabetSize:ENNReal)^r*(16:ENNReal)^r := by
    exact_mod_cast (alphabet_power r).symm
  rw [hp]
  ring

 theorem law_normalized_fee_row_fields (r M S fee : Nat) (hM : 0<M) (hS : 0<S)
    (f : ENNReal → ENNReal)
    (hfee : (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/(S:ENNReal)*(fee:ENNReal)) :
    Law.lawAvg honestCoordLaw r
      (fun W => f (priceBucket W)/((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)) ≤
      kappa^r*((16^r*fee:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) := by
  rw [← normalized_denominator r M fee hM kappa]
  exact law_normalized_fee_row r f S M fee (by positivity) (by finiteness)
    (by positivity) (by finiteness) hfee

 theorem law_normalized_le_one (r : Nat) (f : List Alphabet → ENNReal) (C : ENNReal)
    (hC0 : C ≠ 0) (hCt : C ≠ ⊤) (hbound : ∀ W, f W≤C) :
    Law.lawAvg honestCoordLaw r (fun W => f W/C) ≤ 1 := by
  calc
    _ ≤ Law.lawAvg honestCoordLaw r (fun _ => (1:ENNReal)) :=
      Law.lawAvg_mono honestCoordLaw r (fun W =>
        (ENNReal.div_le_div_right (hbound W) C).trans_eq (ENNReal.div_self hC0 hCt))
    _ = 1 := Law.lawAvg_const honestCoordLaw honestCoordLaw_sum r 1

 theorem coordAverage_div {β : Type} [Fintype β] (v : β → ENNReal) (T : Nat)
    (f : List β → ENNReal) (C p : ENNReal) :
    Law.coordAverage p v T (fun W => f W/C) = Law.coordAverage p v T f/C := by
  unfold Law.coordAverage
  simp_rw [lawAvg_div,div_eq_mul_inv]
  exact binomialAverage_mul_right p C⁻¹ T (fun r => Law.lawAvg v r f)

 theorem coordAverage_scaled {β : Type} [Fintype β] (v : β → ENNReal) (T : Nat)
    (f : List β → ENNReal) (C I p : ENNReal) (hC0 : C≠0) (hCt : C≠⊤) :
    (I*C)*Law.coordAverage p v T (fun W => f W/C) = I*Law.coordAverage p v T f := by
  rw [coordAverage_div]
  simp only [div_eq_mul_inv]
  calc
    _ = I*Law.coordAverage p v T f*(C*C⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hC0 hCt,mul_one]

end ClaudeWCT.Bank.Paired

/-! ## Binomial thinning (opus-kappa)

The honest cap-conditioned coordinate law satisfies `vA ≤ kappa·vU`. For every statistic that is monotone
under insertion of one letter, `coordAverage p vA T f ≤ coordAverage (kappa·p) vU T f`: the honest
`Bin(T,p)` stream of accepted letters is the accepted part of a `Bin(T,kappa·p)` stream of uniform letters.
This replaces the `kappa^r` tilt by the Poisson weight `e^(-2 kappa) (2 kappa)^r / r!`. -/
namespace ClaudeWCT.Numerics.Law
open ENNReal Finset

theorem coordAverage_thin {β : Type} [Fintype β] (p κ : ENNReal) (vA vU : β → ENNReal)
    (hA : ∑ b, vA b = 1) (hU : ∑ b, vU b = 1) (hdens : ∀ b, vA b ≤ κ * vU b)
    (hκ : 1 ≤ κ) (hκp : κ * p ≤ 1) (T : ℕ) (f : List β → ENNReal)
    (hf : ∀ L b R, f (L ++ R) ≤ f (L ++ b :: R)) :
    coordAverage p vA T f ≤ coordAverage (κ * p) vU T f := by
  have hp1 : p ≤ κ * p := le_mul_of_one_le_left' hκ
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (hp1.trans hκp)
  have hsumd : ∑ b, (κ * vU b - vA b) = κ - 1 := by
    have h : ∑ b, (κ * vU b - vA b) + ∑ b, vA b = κ := by
      rw [← sum_add_distrib]
      simp_rw [tsub_add_cancel_of_le (hdens _)]
      rw [← mul_sum, hU, mul_one]
    rw [hA] at h
    exact ENNReal.eq_sub_of_add_eq one_ne_top h
  have hsplit : 1 - p = (1 - κ * p) + p * (κ - 1) := by
    rw [ENNReal.mul_sub (fun _ _ => hpt), mul_one, mul_comm p κ]
    exact (tsub_add_tsub_cancel hκp hp1).symm
  induction T generalizing f with
  | zero => exact le_rfl
  | succ T ih =>
    rw [coordAverage_succ, coordAverage_succ]
    have hf' : ∀ b : β, ∀ L c R, f (b :: (L ++ R)) ≤ f (b :: (L ++ c :: R)) :=
      fun b L c R => by simpa using hf (b :: L) c R
    set X := coordAverage (κ * p) vU T f with hXdef
    set Y : β → ENNReal := fun b => coordAverage (κ * p) vU T (fun L => f (b :: L)) with hYdef
    have hXY : ∀ b, X ≤ Y b := fun b =>
      coordAverage_mono _ _ _ fun L => by simpa using hf [] b L
    have h1 : coordAverage p vA T f ≤ X := ih f hf
    have h2 : ∀ b, coordAverage p vA T (fun L => f (b :: L)) ≤ Y b :=
      fun b => ih _ (fun L c R => hf' b L c R)
    calc (1 - p) * coordAverage p vA T f + p * ∑ b, vA b * coordAverage p vA T (fun L => f (b :: L))
        ≤ (1 - p) * X + p * ∑ b, vA b * Y b :=
          add_le_add (mul_le_mul' le_rfl h1)
            (mul_le_mul' le_rfl (sum_le_sum fun b _ => mul_le_mul' le_rfl (h2 b)))
      _ = (1 - κ * p) * X + p * ∑ b, ((κ * vU b - vA b) * X + vA b * Y b) := by
          rw [sum_add_distrib, ← sum_mul, hsumd, hsplit]
          ring
      _ ≤ (1 - κ * p) * X + p * ∑ b, ((κ * vU b - vA b) * Y b + vA b * Y b) := by
          gcongr with b
          exact hXY b
      _ = (1 - κ * p) * X + κ * p * ∑ b, vU b * Y b := by
          congr 1
          simp_rw [← add_mul, tsub_add_cancel_of_le (hdens _)]
          rw [mul_sum, mul_sum]
          exact sum_congr rfl fun b _ => by ring

end ClaudeWCT.Numerics.Law

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

noncomputable def uniformCoordLaw (_ : Alphabet) : ENNReal := (Fintype.card Alphabet : ENNReal)⁻¹

theorem uniformCoordLaw_sum : ∑ a, uniformCoordLaw a = 1 := by
  simp only [uniformCoordLaw, sum_const, card_univ, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

theorem uniformCoordLaw_density (a : Alphabet) :
    uniformCoordLaw a ≤ 1 * (Fintype.card Alphabet : ENNReal)⁻¹ := by
  simp [uniformCoordLaw]

theorem kappa_mul_rate_le_one : kappa * (2^31 : ENNReal)⁻¹ ≤ 1 := by
  rw [kappa_exact]
  have hc : (ClaudeWCT.Numerics.SharedFtsCount.count : ENNReal) ≠ 0 := by
    norm_num [ClaudeWCT.Numerics.SharedFtsCount.count]
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hc)
    (by simp)) (by finiteness)).mp
  norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- The honest per-instance law is the thinning of the uniform law at rate `kappa * 2^-31`. -/
theorem coordAverage_honest_thin (T : ℕ) (f : List Alphabet → ENNReal)
    (hf : ∀ L b R, f (L ++ R) ≤ f (L ++ b :: R)) :
    Law.coordAverage (2^31 : ENNReal)⁻¹ honestCoordLaw T f ≤
      Law.coordAverage (kappa * (2^31 : ENNReal)⁻¹) uniformCoordLaw T f :=
  Law.coordAverage_thin _ _ _ _ honestCoordLaw_sum uniformCoordLaw_sum
    honestCoordLaw_density kappa_one_le kappa_mul_rate_le_one T f hf

theorem uniform_priceBucket_payoff_le (r : Nat) (f : ENNReal → ENNReal) :
    Law.lawAvg uniformCoordLaw r (fun W => f (priceBucket W)) ≤
      1^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))/
        (SharedMoments.alphabetSize:ENNReal)^r) := by
  have h := Law.lawAvg_le_uniform uniformCoordLaw 1 uniformCoordLaw_density r
    (fun W => f (priceBucket W))
  rw [uniform_history_average r (fun W => f (priceBucket W))
    (fun h => f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))
    (fun h => congrArg f (priceBucket_ofFn h))] at h
  have hc : Fintype.card Alphabet = SharedMoments.alphabetSize := alphabet_card rfl
  simpa only [hc] using h

theorem uniform_normalized_fee_row_fields (r M S fee : Nat) (hM : 0<M) (hS : 0<S)
    (f : ENNReal → ENNReal)
    (hfee : (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/(S:ENNReal)*(fee:ENNReal)) :
    Law.lawAvg uniformCoordLaw r
      (fun W => f (priceBucket W)/((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)) ≤
      1^r*((16^r*fee:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) := by
  rw [← normalized_denominator r M fee hM 1, lawAvg_div]
  calc
    _ ≤ (1^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))/
        (SharedMoments.alphabetSize:ENNReal)^r))/((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) :=
      ENNReal.div_le_div_right (uniform_priceBucket_payoff_le r f) _
    _ ≤ (1^r*((feeCoefficient/(S:ENNReal))*(fee:ENNReal))/(SharedMoments.alphabetSize:ENNReal)^r)/
        ((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) := by
      apply ENNReal.div_le_div_right
      rw [mul_div_assoc]
      exact mul_le_mul' le_rfl (ENNReal.div_le_div_right hfee _)
    _ = _ := normalize_row_arithmetic feeCoefficient S M SharedMoments.alphabetSize 1 fee r
      (by norm_num [feeCoefficient]) (by unfold feeCoefficient; finiteness)
      (by positivity) (by finiteness) (by positivity) (by finiteness)
      (by norm_num [SharedMoments.alphabetSize]) (by finiteness)

theorem uniform_normalized_le_one (r : Nat) (f : List Alphabet → ENNReal) (C : ENNReal)
    (hC0 : C ≠ 0) (hCt : C ≠ ⊤) (hbound : ∀ W, f W≤C) :
    Law.lawAvg uniformCoordLaw r (fun W => f W/C) ≤ 1 := by
  calc
    _ ≤ Law.lawAvg uniformCoordLaw r (fun _ => (1:ENNReal)) :=
      Law.lawAvg_mono uniformCoordLaw r (fun W =>
        (ENNReal.div_le_div_right (hbound W) C).trans_eq (ENNReal.div_self hC0 hCt))
    _ = 1 := Law.lawAvg_const uniformCoordLaw uniformCoordLaw_sum r 1

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SigGolfResearch.Gate6.Moments (finiteAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem bucketEnv_le_one {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (W : List (AlphabetOf β)) : bucketEnv val W ≤ 1 := by
  classical
  unfold bucketEnv finiteAverage
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  calc
    _ ≤ ∑ _a : AlphabetOf β, (1:ENNReal) := Finset.sum_le_sum (fun a _ => by split_ifs <;> simp)
    _ = _ := by simp

 theorem fee_price_scale : feeCoefficient*(SharedMoments.alphabetSize:ENNReal) =
    (SharedMoments.priceScaleTotal:ENNReal)/(2^31) := by
  rw [← price_coefficient]
  exact ENNReal.div_mul_cancel (by norm_num [SharedMoments.alphabetSize]) (by finiteness)

 theorem priceBucket_le (W : List Alphabet) :
    priceBucket W ≤ feeCoefficient*(SharedMoments.alphabetSize:ENNReal) := by
  rw [fee_price_scale]
  exact (mul_le_mul' le_rfl (bucketEnv_le_one ClaudeWCT.WCT9.wordDigit W)).trans_eq (mul_one _)

 theorem priceBucket_ne_top (W : List Alphabet) : priceBucket W ≠ ⊤ :=
  ne_top_of_le_ne_top (by unfold feeCoefficient; finiteness) (priceBucket_le W)

 noncomputable def cappedIncrement (x : ENNReal) : ENNReal :=
  ENNReal.ofReal (Real.exp (6*(min x ((6:ENNReal)/5)).toReal))-1
 noncomputable def cappedResidual (x : ENNReal) : ENNReal := x-(6:ENNReal)/5

 theorem cappedIncrement_real (x : ENNReal) (hx : x ≠ ⊤) :
    cappedIncrement x = ENNReal.ofReal (Real.exp (6*min x.toReal (6/5))-1) := by
  rw [cappedIncrement,ENNReal.toReal_min hx (by finiteness),ENNReal.toReal_div]
  norm_num only [ENNReal.toReal_ofNat]
  rw [ENNReal.ofReal_sub _ (by norm_num),ENNReal.ofReal_one]

 theorem cappedResidual_real (x : ENNReal) (hx : x ≠ ⊤) :
    cappedResidual x = ENNReal.ofReal (max 0 (x.toReal-6/5)) := by
  rw [ENNReal.ofReal_max,ENNReal.ofReal_zero,max_eq_right (by positivity),
    ENNReal.ofReal_sub _ (by norm_num),ENNReal.ofReal_toReal hx]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<5)]
  norm_num [cappedResidual]

 theorem feeCoefficient_real : feeCoefficient.toReal = (791:ℝ)/2^66 := by
  norm_num [feeCoefficient,ENNReal.toReal_div]

 theorem cappedIncrement_nat (n : Nat) :
    cappedIncrement (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (Real.exp (6*min ((791:ℝ)/2^66*(n:ℝ)) (6/5))-1) := by
  rw [cappedIncrement_real _ (by unfold feeCoefficient; finiteness),
    ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast]

 theorem cappedResidual_nat (n : Nat) :
    cappedResidual (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (max 0 ((791:ℝ)/2^66*(n:ℝ)-6/5)) := by
  rw [cappedResidual_real _ (by unfold feeCoefficient; finiteness),
    ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast]

 theorem cappedResidual_bound (W : List Alphabet) :
    cappedResidual (priceBucket W) ≤ feeCoefficient*SharedMoments.alphabetSize :=
  (tsub_le_self).trans (priceBucket_le W)

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem normalizer_scale (M S : Nat) :
    (2^31:ENNReal)*((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) =
      ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S := by
  have he : (2^31:ENNReal)*(feeCoefficient*SharedMoments.alphabetSize) =
      (SharedMoments.priceScaleTotal:ENNReal) := by
    rw [fee_price_scale]
    simp only [div_eq_mul_inv]
    calc
      _ = (SharedMoments.priceScaleTotal:ENNReal)*((2^31:ENNReal)*(2^31:ENNReal)⁻¹) := by ring
      _ = _ := by rw [ENNReal.mul_inv_cancel (by norm_num) (by finiteness),mul_one]
  simp only [div_eq_mul_inv,Nat.cast_mul]
  calc
    _ = (M:ENNReal)*((2^31:ENNReal)*(feeCoefficient*SharedMoments.alphabetSize))*(S:ENNReal)⁻¹ := by ring
    _ = _ := by rw [he]

 theorem uniform_coordAverage_bound_of_rows (T M S : Nat) (hM : 0<M) (hS : 0<S)
    (f : ENNReal → ENNReal) (fees : Nat → Nat) (bound : ENNReal)
    (hfees : ∀ r≤80, (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/(S:ENNReal)*(fees r:ENNReal))
    (hpoint : ∀ W, f (priceBucket W) ≤
      (M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)
    (hcheck : ∀ g : Nat → ENNReal,
      (∀ r≤80, g r ≤ 1^r*((16^r*fees r:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal)) →
      (∀ r,80 < r → g r ≤ 1) →
      ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        binomialAverage (kappa*(2^31:ENNReal)⁻¹) T g ≤ bound) :
    (2^31:ENNReal)*Law.coordAverage (kappa*(2^31:ENNReal)⁻¹) uniformCoordLaw T
      (fun W => f (priceBucket W)) ≤ bound := by
  let C : ENNReal := (M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S
  have hC0 : C≠0 := by
    have hMc : (M:ENNReal) ≠ 0 := by exact_mod_cast hM.ne'
    have hfc : feeCoefficient ≠ 0 := by norm_num [feeCoefficient]
    have hDc : (SharedMoments.alphabetSize:ENNReal) ≠ 0 := by norm_num [SharedMoments.alphabetSize]
    exact ENNReal.div_ne_zero.mpr ⟨mul_ne_zero (mul_ne_zero hMc hfc) hDc, ENNReal.natCast_ne_top S⟩
  have hCt : C≠⊤ := by dsimp [C,feeCoefficient]; finiteness
  let g : Nat → ENNReal := fun r => Law.lawAvg uniformCoordLaw r (fun W => f (priceBucket W)/C)
  have hg := hcheck g (fun r hr => uniform_normalized_fee_row_fields r M S (fees r) hM hS f (hfees r hr))
    (fun r _ => uniform_normalized_le_one r (fun W => f (priceBucket W)) C hC0 hCt hpoint)
  calc
    _ = ((2^31:ENNReal)*C)*Law.coordAverage (kappa*(2^31:ENNReal)⁻¹) uniformCoordLaw T
      (fun W => f (priceBucket W)/C) :=
      (coordAverage_scaled uniformCoordLaw T (fun W => f (priceBucket W)) C (2^31) _ hC0 hCt).symm
    _ = ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        binomialAverage (kappa*(2^31:ENNReal)⁻¹) T g := by
      rw [show (2^31:ENNReal)*C=((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S from normalizer_scale M S]
      rfl
    _ ≤ bound := hg

/-- Thinned row certificate for the honest law: any payoff `f` monotone in the bucket price is
bounded through `coordAverage_honest_thin` and the uniform rows (no `kappa^r` tilt). -/
 theorem coordAverage_bound_of_rows (T M S : Nat) (hM : 0<M) (hS : 0<S)
    (f : ENNReal → ENNReal) (fees : Nat → Nat) (bound : ENNReal)
    (hmono : ∀ x y, x ≤ y → f x ≤ f y)
    (hfees : ∀ r≤80, (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/(S:ENNReal)*(fees r:ENNReal))
    (hpoint : ∀ W, f (priceBucket W) ≤
      (M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)
    (hcheck : ∀ g : Nat → ENNReal,
      (∀ r≤80, g r ≤ 1^r*((16^r*fees r:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal)) →
      (∀ r,80 < r → g r ≤ 1) →
      ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        binomialAverage (kappa*(2^31:ENNReal)⁻¹) T g ≤ bound) :
    (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T
      (fun W => f (priceBucket W)) ≤ bound :=
  (mul_le_mul' le_rfl (coordAverage_honest_thin T (fun W => f (priceBucket W))
    (fun L b R => hmono _ _ (priceBucket_insert L R b)))).trans
    (uniform_coordAverage_bound_of_rows T M S hM hS f fees bound hfees hpoint hcheck)

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SharedFees SharedMoments
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem cappedIncrement_bound (W : List Alphabet) :
    cappedIncrement (priceBucket W) ≤
      (maxFee:ENNReal)*feeCoefficient*alphabetSize/scale := by
  have hx := ENNReal.toReal_mono (by unfold feeCoefficient; finiteness) (priceBucket_le W)
  rw [ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast] at hx
  have h := (capped_payoff_of_coverage_bound (priceBucket W).toReal
    ((791:ℝ)/2^66) (alphabetSize:ℝ) ENNReal.toReal_nonneg hx).1
  rw [cappedIncrement_real _ (priceBucket_ne_top W)]
  calc
    _ ≤ ENNReal.ofReal ((maxFee:ℝ)*((791:ℝ)/2^66)*(alphabetSize:ℝ)/scale) :=
      ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast scale_pos : (0:ℝ)<scale),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      simp only [ENNReal.ofReal_natCast]
      rw [← feeCoefficient_real, ENNReal.ofReal_toReal (by unfold feeCoefficient; finiteness)]

 theorem residual_normalizer :
    (scale:ENNReal)*feeCoefficient*alphabetSize/scale = feeCoefficient*alphabetSize := by
  have hs0 : (scale:ENNReal) ≠ 0 := by exact_mod_cast scale_pos.ne'
  have hst : (scale:ENNReal) ≠ ⊤ := by finiteness
  simp only [div_eq_mul_inv]
  calc _ = (feeCoefficient*alphabetSize)*((scale:ENNReal)*(scale:ENNReal)⁻¹) := by ring
       _ = _ := by rw [ENNReal.mul_inv_cancel hs0 hst,mul_one]

 theorem cappedResidual_normalized_bound (W : List Alphabet) :
    cappedResidual (priceBucket W) ≤
      (scale:ENNReal)*feeCoefficient*alphabetSize/scale := by
  rw [residual_normalizer]
  exact cappedResidual_bound W

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SharedFees SharedMoments SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- The finite coverage certificate still to be supplied by the paired
histogram calculation. All sampling and conditioning factors are outside it. -/
def FiniteFeeBound : Prop := ∀ r≤80,
  (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
    cappedIncrement (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
      feeCoefficient/(scale:ENNReal)*((certifiedPayoff r).1:ENNReal) ∧
  (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
    cappedResidual (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
      feeCoefficient/(scale:ENNReal)*((certifiedPayoff r).2:ENNReal)

 theorem fee_positive : 0 < maxFee := by
  by_contra hn
  have hz : maxFee=0 := Nat.eq_zero_of_not_pos hn
  have h := (capped_payoff_of_coverage_bound 1 1 1 (by norm_num) (by norm_num)).1
  rw [hz] at h
  norm_num at h

 theorem cappedIncrement_mono {x y : ENNReal} (h : x ≤ y) : cappedIncrement x ≤ cappedIncrement y := by
  unfold cappedIncrement
  apply tsub_le_tsub_right
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num))
    (min_le_right _ _)) (min_le_min h le_rfl)

 theorem cappedResidual_mono {x y : ENNReal} (h : x ≤ y) : cappedResidual x ≤ cappedResidual y :=
  tsub_le_tsub_right h _

 theorem kappa_toReal : kappa.toReal =
    (ClaudeWCT.Numerics.SharedFtsCount.total : ℝ) / ClaudeWCT.Numerics.SharedFtsCount.count := by
  rw [kappa_exact, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-- Window for the thinned rate `kappa * 2^-31` (rejection_ennreal style, tangent line of exp at 2):
`(1 - kappa 2^-31)^(T-80) ≤ 13167581e-8` for the cap-777 `kappa`. -/
 theorem thin_window (T : ℕ) (hT : 2 ^ 32 ≤ T) :
    (1 - kappa * (2^31 : ENNReal)⁻¹) ^ (T - 80) ≤
      ((13167581 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal) := by
  have hq1 := kappa_mul_rate_le_one
  have hfin : (1 - kappa * (2^31 : ENNReal)⁻¹) ^ (T - 80) ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  apply (ENNReal.toReal_le_toReal hfin (by finiteness)).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hq1 ENNReal.one_ne_top, ENNReal.toReal_mul,
    kappa_toReal, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  simp only [ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  set k : ℝ := (ClaudeWCT.Numerics.SharedFtsCount.total : ℝ) / ClaudeWCT.Numerics.SharedFtsCount.count with hk
  have hkv : k = 52416169542617085727767971710947931910569984 / 51697785130018558464839655637843407521710080 := by
    rw [hk]; norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count]
  set n := T - 80 with hn
  have hn0 : (2:ℝ)^32 - 80 ≤ n := by
    have : 2^32 - 80 ≤ n := by omega
    have h' : ((2^32 - 80 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    norm_num at h' ⊢; linarith
  have h0 : (0 : ℝ) ≤ 1 - k * (2^31)⁻¹ := by rw [hkv]; norm_num
  have hp : (1 - k * (2^31)⁻¹ : ℝ) ≤ Real.exp (-(k * (2^31)⁻¹)) := Real.one_sub_le_exp_neg _
  have hpow : (1 - k * (2^31)⁻¹ : ℝ) ^ n ≤ Real.exp (-(n * (k * (2^31)⁻¹))) := by
    calc (1 - k * (2^31)⁻¹ : ℝ) ^ n ≤ Real.exp (-(k * (2^31)⁻¹)) ^ n := pow_le_pow_left₀ h0 hp n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  set a0 : ℝ := ((2:ℝ)^32 - 80) * (k * (2^31)⁻¹) with ha0
  have ha : a0 ≤ n * (k * (2^31)⁻¹) :=
    mul_le_mul_of_nonneg_right hn0 (by rw [hkv]; norm_num)
  have hlow : (100000000 : ℝ) / 13167581 ≤ (2.7182818283 : ℝ) ^ 2 * (a0 - 1) := by
    rw [ha0, hkv]; norm_num
  have hexp : (100000000 : ℝ) / 13167581 ≤ Real.exp (n * (k * (2^31)⁻¹)) :=
    hlow.trans ((ClaudeWCT.Numerics.PoissonReflect.exp_lower a0).trans (Real.exp_le_exp.mpr ha))
  refine hpow.trans ?_
  rw [Real.exp_neg]
  have hpos : (0:ℝ) < 100000000 / 13167581 := by norm_num
  calc (Real.exp (n * (k * (2^31)⁻¹)))⁻¹ ≤ ((100000000 : ℝ) / 13167581)⁻¹ :=
        inv_anti₀ hpos hexp
    _ = ((13167581 : ℕ) : ℝ) / ((100000000 : ℕ) : ℝ) := by norm_num

/-- Thinned Poisson parameter: `2^32 · kappa · 2^-31 = 2 kappa ≤ 2.018833` (cap 777). -/
 theorem thin_lambda :
    ((2^32 : ℕ) : ENNReal) * (kappa * (2^31 : ENNReal)⁻¹) * 1 ≤
      ((2027792 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal) := by
  rw [mul_one, kappa_exact]
  have hc : (ClaudeWCT.Numerics.SharedFtsCount.count : ENNReal) ≠ 0 := by
    norm_num [ClaudeWCT.Numerics.SharedFtsCount.count]
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.mul_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hc) (by simp))) (by finiteness)).mp
  norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]

end ClaudeWCT.Bank.Paired

/-! Scalar endpoints for the cap-777 thinned certificate (shared MGF `6.945`, residual `7831e-7`). -/
namespace ClaudeWCT.Numerics.SharedPathWinsor.Rows18Thin
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

end ClaudeWCT.Numerics.SharedPathWinsor.Rows18Thin

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem tsub_convex (x theta eta a b : ENNReal) (hab : a+b=1) :
    x-(a*theta+b*eta) ≤ a*(x-theta)+b*(x-eta) := by
  apply (tsub_le_iff_right).2
  calc x = a*x+b*x := by rw [← add_mul,hab,one_mul]
       _ ≤ a*(theta+(x-theta))+b*(eta+(x-eta)) :=
         add_le_add (mul_le_mul' le_rfl le_add_tsub) (mul_le_mul' le_rfl le_add_tsub)
       _ = _ := by ring

 theorem price_excess_affine (T : Nat) (theta eta A B t : ℝ)
    (htheta : 0 ≤ theta) (heta : 0 ≤ eta) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hfirst : Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal theta) ≤ ENNReal.ofReal A)
    (hsecond : Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal eta) ≤ ENNReal.ofReal B) :
    Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal ((1-t)*theta+t*eta)) ≤
      ENNReal.ofReal ((1-t)*A+t*B) := by
  have ha0 : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have hab : ENNReal.ofReal (1-t)+ENNReal.ofReal t=1 := by
    rw [←ENNReal.ofReal_add ha0 ht0]
    ring_nf
    exact ENNReal.ofReal_one
  have harg : ENNReal.ofReal ((1-t)*theta+t*eta) =
      ENNReal.ofReal (1-t)*ENNReal.ofReal theta+ENNReal.ofReal t*ENNReal.ofReal eta := by
    rw [ENNReal.ofReal_add (mul_nonneg ha0 htheta) (mul_nonneg ht0 heta),
      ENNReal.ofReal_mul ha0, ENNReal.ofReal_mul ht0]
  rw [harg]
  calc
    _ ≤ Law.lawAvg honestLaw T (fun W =>
      ENNReal.ofReal (1-t)*(price W-ENNReal.ofReal theta)+
      ENNReal.ofReal t*(price W-ENNReal.ofReal eta)) :=
        Law.lawAvg_mono _ _ (fun W => tsub_convex _ _ _ _ _ hab)
    _ = ENNReal.ofReal (1-t)*Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal theta)+
        ENNReal.ofReal t*Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal eta) := by
      rw [Law.lawAvg_add,Law.lawAvg_mul_left,Law.lawAvg_mul_left]
    _ ≤ ENNReal.ofReal (1-t)*ENNReal.ofReal A+ENNReal.ofReal t*ENNReal.ofReal B :=
      add_le_add (mul_le_mul' le_rfl hfirst) (mul_le_mul' le_rfl hsecond)
    _ = _ := by
      rw [←ENNReal.ofReal_mul ha0,←ENNReal.ofReal_mul ht0,
        ←ENNReal.ofReal_add (mul_nonneg ha0 hA) (mul_nonneg ht0 hB)]

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SharedMoments SphincsSecurity.Concrete
open SigGolfCandidate.T3.BPORS.History (atIndex)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem law_marked_sum {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β]
    (v : β → ENNReal) (hv : ∑ b,v b=1) (T : Nat) (f : List β → ENNReal) :
    Law.lawAvg (Law.marked (α:=α) v) T (fun W => ∑ i:α,f (atIndex i W)) =
      (Fintype.card α:ENNReal)*Law.coordAverage (Fintype.card α:ENNReal)⁻¹ v T f := by
  rw [Law.lawAvg_sum]
  simp only [Law.law_marked_atIndex v hv, Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rfl

 theorem law_price_coordAverage (T : Nat) :
    Law.lawAvg honestLaw T price =
      (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T priceBucket := by
  have he : price = fun W => ∑ i : Fin (2^31),priceBucket (atIndex i W) := funext price_eq_sum
  rw [he]
  have h := law_marked_sum (α:=Fin (2^31)) honestCoordLaw honestCoordLaw_sum T priceBucket
  simpa only [honestLaw,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using h

 theorem first_finite_row (r : Nat) (hr : r≤80) :
    (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)) =
        feeCoefficient*(forestMoment r:ENNReal) := by
  rw [← Finset.mul_sum,←Nat.cast_sum]
  have h := SharedCoverage.forest_coverage_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
    WCTEnvelope.w1Table_wordDigit rows_checked r (by omega)
  exact congrArg (fun n : Nat => feeCoefficient*(n:ENNReal)) h

 theorem law_price_mean_bound : Law.lawAvg honestLaw (2^32) price ≤ (944:ENNReal)/1000 := by
  rw [law_price_coordAverage]
  apply coordAverage_bound_of_rows (2^32) 1 1 (by norm_num) (by norm_num)
    id forestMoment (944/1000) (fun _ _ h => h)
  · intro r hr
    simpa only [id_eq,Nat.cast_one,div_one] using (first_finite_row r hr).le
  · intro W
    simpa only [id_eq,Nat.cast_one,one_mul,div_one] using priceBucket_le W
  · intro g hp ht
    have h := first_bound_of_rows (2^32) _ kappa_mul_rate_le_one (thin_window _ le_rfl)
      1 le_rfl thin_lambda g (by simpa only [Nat.one_mul] using hp) ht
    simpa only [Nat.one_mul,Nat.cast_one,div_one] using h

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem uniform_history_le_of_le (r : Nat) (f : List Alphabet → ENNReal)
    (g : SharedCoverage.ForestHistory (Fin 563) r → ENNReal)
    (hfg : ∀ h : Fin r → Alphabet,f (List.ofFn h) ≤ g (splitHistory h)) :
    Law.lawAvg uniformCoordLaw r f ≤ 1^r *
      ((∑ h,g h)/(SharedMoments.alphabetSize:ENNReal)^r) := by
  have hu : SphincsSecurity.Concrete.uniformWordAverage r f ≤
      (∑ h,g h)/(SharedMoments.alphabetSize:ENNReal)^r := by
    rw [SigGolfResearch.Gate6.Moments.word_array_average]
    unfold SigGolfResearch.Gate6.Moments.finiteAverage
    have hc : Fintype.card Alphabet=SharedMoments.alphabetSize := alphabet_card rfl
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,hc]
    rw [←sum_history]
    exact ENNReal.div_le_div_right (Finset.sum_le_sum (fun h _ => hfg h)) _
  exact (Law.lawAvg_le_uniform uniformCoordLaw 1 uniformCoordLaw_density r f).trans
    (mul_le_mul' le_rfl hu)

 theorem uniform_normalized_history_row (r M S fee : Nat) (hM : 0<M) (hS : 0<S)
    (f : List Alphabet → ENNReal) (g : SharedCoverage.ForestHistory (Fin 563) r → ENNReal)
    (hfg : ∀ h : Fin r → Alphabet,f (List.ofFn h) ≤ g (splitHistory h))
    (hfee : (∑ h,g h) ≤ feeCoefficient/(S:ENNReal)*(fee:ENNReal)) :
    Law.lawAvg uniformCoordLaw r
      (fun W => f W/((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)) ≤
      1^r*((16^r*fee:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) := by
  rw [←normalized_denominator r M fee hM 1,lawAvg_div]
  calc
    _ ≤ (1^r*((∑ h,g h)/(SharedMoments.alphabetSize:ENNReal)^r))/
        ((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) :=
      ENNReal.div_le_div_right (uniform_history_le_of_le r f g hfg) _
    _ ≤ (1^r*((feeCoefficient/(S:ENNReal))*(fee:ENNReal))/(SharedMoments.alphabetSize:ENNReal)^r)/
        ((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) := by
      apply ENNReal.div_le_div_right
      rw [mul_div_assoc]
      exact mul_le_mul' le_rfl (ENNReal.div_le_div_right hfee _)
    _ = _ := normalize_row_arithmetic feeCoefficient S M SharedMoments.alphabetSize 1 fee r
      (by norm_num [feeCoefficient]) (by unfold feeCoefficient; finiteness)
      (by positivity) (by finiteness) (by positivity) (by finiteness)
      (by norm_num [SharedMoments.alphabetSize]) (by finiteness)

/-- Thinned history certificate: an insertion-monotone `f` is bounded through
`coordAverage_honest_thin` and uniform history rows (no `kappa^r` tilt). -/
 theorem coordAverage_history_bound (T M S : Nat) (hM : 0<M) (hS : 0<S)
    (f : List Alphabet → ENNReal)
    (g : (r : Nat) → SharedCoverage.ForestHistory (Fin 563) r → ENNReal)
    (fees : Nat → Nat) (bound : ENNReal)
    (hins : ∀ L b R,f (L++R) ≤ f (L++b::R))
    (hfg : ∀ r≤80,∀ h : Fin r → Alphabet,f (List.ofFn h) ≤ g r (splitHistory h))
    (hfees : ∀ r≤80,(∑ h,g r h) ≤ feeCoefficient/(S:ENNReal)*(fees r:ENNReal))
    (hpoint : ∀ W,f W≤(M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)
    (hcheck : ∀ v : Nat → ENNReal,
      (∀ r≤80,v r≤1^r*((16^r*fees r:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal)) →
      (∀ r,80 < r → v r≤1) →
      ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        SphincsSecurity.Concrete.binomialAverage (kappa*(2^31:ENNReal)⁻¹) T v ≤ bound) :
    (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T f ≤ bound := by
  refine (mul_le_mul' le_rfl (coordAverage_honest_thin T f hins)).trans ?_
  let C : ENNReal := (M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S
  have hC0 : C≠0 := by
    have hMc : (M:ENNReal)≠0 := by exact_mod_cast hM.ne'
    have hfc : feeCoefficient≠0 := by norm_num [feeCoefficient]
    have hDc : (SharedMoments.alphabetSize:ENNReal)≠0 := by norm_num [SharedMoments.alphabetSize]
    exact ENNReal.div_ne_zero.mpr ⟨mul_ne_zero (mul_ne_zero hMc hfc) hDc,ENNReal.natCast_ne_top S⟩
  have hCt : C≠⊤ := by dsimp [C,feeCoefficient]; finiteness
  let v : Nat → ENNReal := fun r => Law.lawAvg uniformCoordLaw r (fun W => f W/C)
  have hv := hcheck v
    (fun r hr => uniform_normalized_history_row r M S (fees r) hM hS f (g r) (hfg r hr) (hfees r hr))
    (fun r _ => uniform_normalized_le_one r f C hC0 hCt hpoint)
  calc
    _ = ((2^31:ENNReal)*C)*Law.coordAverage (kappa*(2^31:ENNReal)⁻¹) uniformCoordLaw T (fun W => f W/C) :=
      (coordAverage_scaled uniformCoordLaw T f C (2^31) (kappa*(2^31:ENNReal)⁻¹) hC0 hCt).symm
    _ = ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        SphincsSecurity.Concrete.binomialAverage (kappa*(2^31:ENNReal)⁻¹) T v := by
      rw [show (2^31:ENNReal)*C=((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S from normalizer_scale M S]
      rfl
    _ ≤ bound := hv

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ClaudeWCT.Numerics ClaudeWCT.Numerics.N600
open SharedCoverage Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

 theorem card_filter_congr_any {α : Type} [Fintype α] (P Q : α → Prop)
    (dP : DecidablePred P) (dQ : DecidablePred Q) (h : ∀ a,P a↔Q a) :
    (@Finset.filter α P dP Finset.univ).card = (@Finset.filter α Q dQ Finset.univ).card := by
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_filter]
  exact and_congr Iff.rfl (h a)

def PairNearAt {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) (side : Fin 2) (t : Fin 6) (a : PairChoice β) : Prop :=
  if side=0 then
    CovAtExcept val t a.2.1.1 (val a.2.1.2) (splitRanks h.1 h.2.1 a.1) ∧
    CovAt val a.2.2.1 (val a.2.2.2) (splitRanks h.1 h.2.2 a.1)
  else
    CovAt val a.2.1.1 (val a.2.1.2) (splitRanks h.1 h.2.1 a.1) ∧
    CovAtExcept val t a.2.2.1 (val a.2.2.2) (splitRanks h.1 h.2.2 a.1)

 theorem pairPredicate_card {β : Type} [Fintype β]
    (P Q : Fin 2 → Fin 64 × β → Prop) :
    #{a : PairChoice β | P a.1 a.2.1 ∧ Q a.1 a.2.2} =
      ∑ s : Fin 2, #{a | P s a} * #{b | Q s b} := by
  let e : {a : PairChoice β // P a.1 a.2.1 ∧ Q a.1 a.2.2} ≃
      (s : Fin 2) × {a : Fin 64 × β // P s a} × {b : Fin 64 × β // Q s b} :=
    { toFun := fun a => ⟨a.val.1,⟨a.val.2.1,a.property.1⟩,⟨a.val.2.2,a.property.2⟩⟩
      invFun := fun a => ⟨(a.1,a.2.1.val,a.2.2.val),a.2.1.property,a.2.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Fintype.card_congr e
  simpa only [Fintype.card_subtype,Fintype.card_sigma,Fintype.card_prod] using he

 theorem pairNearAt_sum {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) :
    (∑ side : Fin 2, ∑ t : Fin 6, #{a : PairChoice β | PairNearAt val h side t a}) =
      pairNear val h := by
  have hleft (t : Fin 6) : #{a : PairChoice β | PairNearAt val h 0 t a} =
      ∑ s : Fin 2, #{a : Fin 64 × β | CovAtExcept val t a.1 (val a.2) (splitRanks h.1 h.2.1 s)} *
        coordinateCoverage val (splitRanks h.1 h.2.2 s) := by
    have hh := pairPredicate_card
      (fun s a => CovAtExcept val t a.1 (val a.2) (splitRanks h.1 h.2.1 s))
      (fun s a => CovAt val a.1 (val a.2) (splitRanks h.1 h.2.2 s))
    convert hh using 1
    · apply card_filter_congr_any; intro a; simp only [PairNearAt,ite_true]
    · apply Finset.sum_congr rfl
      intro z _
      apply congrArg₂ Nat.mul
      · apply card_filter_congr_any; intro a; rfl
      · unfold coordinateCoverage
        apply card_filter_congr_any; intro a; rfl
  have hright (t : Fin 6) : #{a : PairChoice β | PairNearAt val h 1 t a} =
      ∑ s : Fin 2, coordinateCoverage val (splitRanks h.1 h.2.1 s) *
        #{a : Fin 64 × β | CovAtExcept val t a.1 (val a.2) (splitRanks h.1 h.2.2 s)} := by
    have hh := pairPredicate_card
      (fun s a => CovAt val a.1 (val a.2) (splitRanks h.1 h.2.1 s))
      (fun s a => CovAtExcept val t a.1 (val a.2) (splitRanks h.1 h.2.2 s))
    convert hh using 1
    · apply card_filter_congr_any; intro a; simp only [PairNearAt,show (1:Fin 2)≠0 by decide,ite_false]
    · apply Finset.sum_congr rfl
      intro z _
      apply congrArg₂ Nat.mul
      · unfold coordinateCoverage
        apply card_filter_congr_any; intro a; rfl
      · apply card_filter_congr_any; intro a; rfl
  rw [Fin.sum_univ_two]
  simp_rw [hleft,hright]
  simp only [Fin.sum_univ_two,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum]
  unfold pairNear selectorKernel coordinateNear coordinateCoverage
  ring

abbrev ForestHole := (Fin 4 × Fin 2 × Fin 6) ⊕ Fin 6

def ForestNearAt {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) (hole : ForestHole) (a : ForestChoice β) : Prop :=
  match hole with
  | .inl v => (∀ p, if p=v.1 then PairNearAt val (h.1 p) v.2.1 v.2.2 (a.1 p)
                    else PairCovered val (h.1 p) (a.1 p)) ∧ CovAt val a.2.1 (val a.2.2) h.2
  | .inr t => (∀ p, PairCovered val (h.1 p) (a.1 p)) ∧ CovAtExcept val t a.2.1 (val a.2.2) h.2

 theorem forestPredicate_card {β : Type} [Fintype β]
    (P : Fin 4 → PairChoice β → Prop) (Q : Fin 128 × β → Prop) :
    #{a : ForestChoice β | (∀ p, P p (a.1 p)) ∧ Q a.2} =
      (∏ p, #{a | P p a}) * #{b | Q b} := by
  let e : {a : ForestChoice β // (∀ p,P p (a.1 p)) ∧ Q a.2} ≃
      ((p:Fin 4) → {a : PairChoice β // P p a}) × {b : Fin 128 × β // Q b} :=
    { toFun := fun a => (fun p => ⟨a.val.1 p,a.property.1 p⟩,⟨a.val.2,a.property.2⟩)
      invFun := fun a => ⟨(fun p => (a.1 p).val,a.2.val),(fun p => (a.1 p).property),a.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Fintype.card_congr e
  simpa only [Fintype.card_subtype,Fintype.card_prod,Fintype.card_pi] using he

 theorem sum_prod_replace {δ : Type} [Fintype δ] (p : Fin 4)
    (f : δ → Fin 4 → Nat) (g : Fin 4 → Nat) :
    (∑ d, ∏ i : Fin 4, if i=p then f d i else g i) =
      ∏ i : Fin 4, if i=p then ∑ d,f d i else g i := by
  fin_cases p <;> simp [Fin.prod_univ_succ,←Finset.sum_mul,←Finset.mul_sum]

 theorem forestNearAt_sum {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) :
    (∑ hole : ForestHole, #{a : ForestChoice β | ForestNearAt val h hole a}) =
      forestNear val h := by
  have hleft (k : Fin 4) (side : Fin 2) (t : Fin 6) :
      #{a : ForestChoice β | ForestNearAt val h (.inl (k,side,t)) a} =
      (∏ p : Fin 4, #{a : PairChoice β | if p=k then PairNearAt val (h.1 p) side t a
        else PairCovered val (h.1 p) a}) * coordinateCoverage val h.2 := by
    have hh := forestPredicate_card
      (fun p a => if p=k then PairNearAt val (h.1 p) side t a else PairCovered val (h.1 p) a)
      (fun a => CovAt val a.1 (val a.2) h.2)
    convert hh using 1
    · apply card_filter_congr_any; intro a; rfl
    · apply congrArg₂ Nat.mul
      · apply Finset.prod_congr rfl
        intro p _
        apply card_filter_congr_any; intro a; rfl
      · unfold coordinateCoverage
        apply card_filter_congr_any; intro a; rfl
  have hright (t : Fin 6) :
      #{a : ForestChoice β | ForestNearAt val h (.inr t) a} =
      (∏ p : Fin 4, pairCoverage val (h.1 p)) *
        #{a : Fin 128 × β | CovAtExcept val t a.1 (val a.2) h.2} := by
    have hh := forestPredicate_card (fun p a => PairCovered val (h.1 p) a)
      (fun a => CovAtExcept val t a.1 (val a.2) h.2)
    simp only [pairCovered_card] at hh
    convert hh using 1
    · apply card_filter_congr_any; intro a; rfl
    · apply congrArg₂ Nat.mul
      · rfl
      · apply card_filter_congr_any; intro a; rfl
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  simp_rw [hleft,hright]
  have hcard (p k : Fin 4) (side : Fin 2) (t : Fin 6) :
      #{a : PairChoice β | if p=k then PairNearAt val (h.1 p) side t a else PairCovered val (h.1 p) a} =
        if p=k then #{a : PairChoice β | PairNearAt val (h.1 p) side t a} else pairCoverage val (h.1 p) := by
    by_cases hp : p=k <;> simp only [hp,ite_true,ite_false,pairCovered_card]
  simp_rw [hcard]
  simp only [←Finset.sum_mul,←Finset.mul_sum]
  have hsum (k : Fin 4) :
      (∑ side : Fin 2, ∑ t : Fin 6, ∏ p : Fin 4,
        if p=k then #{a : PairChoice β | PairNearAt val (h.1 p) side t a} else pairCoverage val (h.1 p)) =
      ∏ p : Fin 4, if p=k then pairNear val (h.1 p) else pairCoverage val (h.1 p) := by
    simp_rw [sum_prod_replace]
    simp only [sum_prod_replace,pairNearAt_sum]
  simp_rw [hsum]
  rfl

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ClaudeWCT.Numerics ClaudeWCT.Numerics.N600
open SharedCoverage Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def pairCoord (p : Fin 4) (side : Fin 2) : Fin 9 := ⟨2*p.val+side.val,by omega⟩
def holeCoord : ForestHole → Fin 9 × Fin 6
  | .inl v => (pairCoord v.1 v.2.1,v.2.2)
  | .inr t => (8,t)
def coordHole (c : Fin 9 × Fin 6) : ForestHole :=
  if hc : c.1.val<8 then .inl (⟨c.1.val/2,by omega⟩,⟨c.1.val%2,by omega⟩,c.2)
  else .inr c.2

def holeEquiv : ForestHole ≃ Fin 9 × Fin 6 where
  toFun := holeCoord
  invFun := coordHole
  left_inv h := by
    rcases h with ⟨p,s,t⟩|t
    · fin_cases p <;> fin_cases s <;> simp [coordHole,holeCoord,pairCoord]
    · rfl
  right_inv c := by
    rcases c with ⟨k,t⟩
    fin_cases k <;> simp [coordHole,holeCoord,pairCoord]

 theorem pairCoord_inj (p q : Fin 4) (s t : Fin 2) :
    pairCoord p s=pairCoord q t ↔ p=q ∧ s=t := by
  simp only [pairCoord,Fin.ext_iff]
  have hs := s.isLt
  have ht := t.isLt
  omega

 theorem pairCoord_ne_singleton (p : Fin 4) (s : Fin 2) : pairCoord p s ≠ 8 := by
  intro he
  have hh := congrArg Fin.val he
  have hp := p.isLt
  have hs := s.isLt
  change 2*p.val+s.val=8 at hh
  omega

 theorem covAtExcept_splitRanks {β : Type} [Fintype β] {r : Nat}
    (val : β → Fin 6 → Nat) (o : Fin r → Fin 2) (A : Fin r → Fin 64 × β)
    (s : Fin 2) (target : Fin 64 × β) (t : Fin 6) :
    CovAtExcept val t target.1 (val target.2) (splitRanks o A s) ↔
      ∀ u,u≠t → ∃ j,o j=s ∧ (A j).1=target.1 ∧ val target.2 u≤val (A j).2 u := by
  constructor
  · intro h u hu
    obtain ⟨j,hj,hv⟩ := h u hu
    let z := (fiberIndex o s).symm j
    exact ⟨z.val,z.property,by simpa only [splitRanks_apply] using hj,
      by simpa only [splitRanks_apply] using hv⟩
  · intro h u hu
    obtain ⟨j,hj,hc,hv⟩ := h u hu
    refine ⟨fiberIndex o s ⟨j,hj⟩,?_,?_⟩
    · simpa only [splitRanks_apply,Equiv.symm_apply_apply] using hc
    · simpa only [splitRanks_apply,Equiv.symm_apply_apply] using hv

def AlphabetNearAt {β : Type} (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (hole : ForestHole) (a : AlphabetOf β) : Prop :=
  ∀ k : Fin 9, ∀ t : Fin 6, (k,t)≠holeCoord hole → ∃ j,
    rawChild (h j).1 k=rawChild a.1 k ∧ val (a.2 k) t≤val ((h j).2 k) t

 theorem alphabetNear_forest {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (hole : ForestHole) (a : AlphabetOf β)
    (hn : AlphabetNearAt val h hole a) : ForestNearAt val (splitHistory h) hole (choice a) := by
  let P : Fin 9 → Fin 6 → Prop := fun k t => ∃ j,
    rawChild (h j).1 k=rawChild a.1 k ∧ val (a.2 k) t≤val ((h j).2 k) t
  have hfirst (p : Fin 4) :
      CovAt val ((choice a).1 p).2.1.1 (val ((choice a).1 p).2.1.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.1 ((choice a).1 p).1) ↔
      ∀ t,P (pairCoord p 0) t := by
    rw [covAt_splitRanks]
    simp only [P,pairCoord,Fin.val_zero,Nat.add_zero]
    simp only [splitHistory,choice,rawChild_first_eq,and_assoc]
  have hsecond (p : Fin 4) :
      CovAt val ((choice a).1 p).2.2.1 (val ((choice a).1 p).2.2.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.2 ((choice a).1 p).1) ↔
      ∀ t,P (pairCoord p 1) t := by
    rw [covAt_splitRanks]
    simp only [P,pairCoord,Fin.val_one]
    simp only [splitHistory,choice,rawChild_second_eq,and_assoc]
  have hfirstE (p : Fin 4) (t : Fin 6) :
      CovAtExcept val t ((choice a).1 p).2.1.1 (val ((choice a).1 p).2.1.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.1 ((choice a).1 p).1) ↔
      ∀ u,u≠t → P (pairCoord p 0) u := by
    rw [covAtExcept_splitRanks]
    simp only [P,pairCoord,Fin.val_zero,Nat.add_zero]
    simp only [splitHistory,choice,rawChild_first_eq,and_assoc]
  have hsecondE (p : Fin 4) (t : Fin 6) :
      CovAtExcept val t ((choice a).1 p).2.2.1 (val ((choice a).1 p).2.2.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.2 ((choice a).1 p).1) ↔
      ∀ u,u≠t → P (pairCoord p 1) u := by
    rw [covAtExcept_splitRanks]
    simp only [P,pairCoord,Fin.val_one]
    simp only [splitHistory,choice,rawChild_second_eq,and_assoc]
  rcases hole with ⟨p,s,t⟩|t
  · refine ⟨?_,?_⟩
    · intro q
      by_cases hq:q=p
      · subst q
        rw [if_pos rfl]
        fin_cases s
        · refine ⟨(hfirstE p t).mpr ?_,(hsecond p).mpr ?_⟩
          · intro u hu
            exact hn _ _ (fun he => hu (congrArg Prod.snd he))
          · intro u
            apply hn
            intro he
            have hc := (pairCoord_inj p p 1 0).mp (congrArg Prod.fst he)
            exact (by decide : (1:Fin 2)≠0) hc.2
        · refine ⟨(hfirst p).mpr ?_,(hsecondE p t).mpr ?_⟩
          · intro u
            apply hn
            intro he
            have hc := (pairCoord_inj p p 0 1).mp (congrArg Prod.fst he)
            exact (by decide : (0:Fin 2)≠1) hc.2
          · intro u hu
            exact hn _ _ (fun he => hu (congrArg Prod.snd he))
      · rw [if_neg hq]
        refine ⟨(hfirst q).mpr ?_,(hsecond q).mpr ?_⟩ <;> intro u <;> apply hn <;> intro he
        · exact hq ((pairCoord_inj q p 0 s).mp (congrArg Prod.fst he)).1
        · exact hq ((pairCoord_inj q p 1 s).mp (congrArg Prod.fst he)).1
    · intro u
      exact hn 8 u (fun he => pairCoord_ne_singleton p s (congrArg Prod.fst he).symm)
  · refine ⟨?_,?_⟩
    · intro p
      refine ⟨(hfirst p).mpr ?_,(hsecond p).mpr ?_⟩ <;> intro u <;> apply hn <;> intro he
      · exact pairCoord_ne_singleton p 0 (congrArg Prod.fst he)
      · exact pairCoord_ne_singleton p 1 (congrArg Prod.fst he)
    · intro u hu
      exact hn 8 u (fun he => hu (congrArg Prod.snd he))

 theorem alphabetNear_sum_le {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) :
    (∑ hole : ForestHole, #{a : AlphabetOf β | AlphabetNearAt val h hole a}) ≤
      forestNear val (splitHistory h) := by
  rw [←forestNearAt_sum]
  apply Finset.sum_le_sum
  intro hole _
  let e : {a : AlphabetOf β // AlphabetNearAt val h hole a} ≃
      {a : ForestChoice β // AlphabetNearAt val h hole ((choiceEquiv β).symm a)} :=
    (choiceEquiv β).subtypeEquiv (fun a => by rw [(choiceEquiv β).symm_apply_apply a])
  have he := Fintype.card_congr e
  simp only [Fintype.card_subtype] at he
  rw [he]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨_,ha⟩ := Finset.mem_filter.mp ha
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  have hh := alphabetNear_forest val h hole ((choiceEquiv β).symm a) ha
  simpa only [show choice ((choiceEquiv β).symm a)=a from (choiceEquiv β).apply_symm_apply a] using hh

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open SigGolfResearch.Gate6.Moments (finiteAverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def ListAlphabetNear {β : Type} (val : β → Fin 6 → Nat)
    (W : List (AlphabetOf β)) (a : AlphabetOf β) (hole : Fin 9 × Fin 6) : Prop :=
  ∀ k : Fin 9,∀ t : Fin 6,(k,t)≠hole → ∃ e∈W,
    rawChild e.1 k=rawChild a.1 k ∧ val (a.2 k) t≤val (e.2 k) t
noncomputable def nearBucket (W : List Alphabet) : ENNReal :=
  (SharedMoments.priceScaleTotal:ENNReal)/(2^31) *
    finiteAverage (fun a => ∑ hole : Fin 9 × Fin 6,
      if ListAlphabetNear ClaudeWCT.WCT9.wordDigit W a hole then 1 else 0)

def NearCoveredAtP (W : List Proposal) (N : SigGolfCandidate.T3.HashOutput)
    (hole : Fin 9 × Fin 6) : Prop :=
  ∀ k t,(k,t)≠hole → SlotCoveredP W N k t
noncomputable def nearScoreP (W : List Proposal) (N : SigGolfCandidate.T3.HashOutput) : ENNReal :=
  if admissible N=true then ∑ hole : Fin 9 × Fin 6,if NearCoveredAtP W N hole then 1 else 0 else 0
noncomputable def nearPrice (W : List Proposal) : ENNReal :=
  (2:ENNReal)^128 * SigGolfCandidate.T3.BPORS.finiteAverage (nearScoreP W)

 theorem listAlphabetNear_ofFn {β : Type} (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (a : AlphabetOf β) (hole : ForestHole) :
    ListAlphabetNear val (List.ofFn h) a (holeCoord hole) ↔ AlphabetNearAt val h hole a := by
  simp only [ListAlphabetNear,AlphabetNearAt,List.mem_ofFn]
  refine forall_congr' fun k => forall_congr' fun t => forall_congr' fun ht => ?_
  constructor
  · rintro ⟨e,⟨j,rfl⟩,he⟩
    exact ⟨j,he⟩
  · rintro ⟨j,hj⟩
    exact ⟨h j,⟨j,rfl⟩,hj⟩

 theorem nearBucket_ofFn_le {r : Nat} (h : Fin r → Alphabet) :
    nearBucket (List.ofFn h) ≤ feeCoefficient*
      (SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal) := by
  have hc : Fintype.card Alphabet=SharedMoments.alphabetSize := alphabet_card (Fintype.card_fin 563)
  have hs : (∑ a : Alphabet,∑ hole : Fin 9 × Fin 6,
      if ListAlphabetNear ClaudeWCT.WCT9.wordDigit (List.ofFn h) a hole then (1:ENNReal) else 0) ≤
      (SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal) := by
    rw [sum_comm]
    conv_lhs => rw [←Equiv.sum_comp holeEquiv]
    change (∑ hole : ForestHole,∑ a : Alphabet,if ListAlphabetNear ClaudeWCT.WCT9.wordDigit (List.ofFn h) a (holeCoord hole) then (1:ENNReal) else 0) ≤ _
    simp_rw [listAlphabetNear_ofFn,←natCast_card_filter]
    rw [←Nat.cast_sum]
    exact_mod_cast alphabetNear_sum_le ClaudeWCT.WCT9.wordDigit h
  unfold nearBucket finiteAverage
  rw [hc,←fee_price_scale]
  calc
    _ ≤ (feeCoefficient*SharedMoments.alphabetSize)*
        ((SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal)/
          SharedMoments.alphabetSize) := mul_le_mul' le_rfl (ENNReal.div_le_div_right hs _)
    _ = _ := by
      rw [mul_assoc,ENNReal.mul_div_cancel
        (by norm_num [SharedMoments.alphabetSize]) (by simp)]

 theorem nearBucket_bound (W : List Alphabet) :
    nearBucket W ≤ (54:ENNReal)*feeCoefficient*SharedMoments.alphabetSize := by
  unfold nearBucket finiteAverage
  have hsum : (∑ a : Alphabet,∑ hole : Fin 9 × Fin 6,
      if ListAlphabetNear ClaudeWCT.WCT9.wordDigit W a hole then (1:ENNReal) else 0) ≤
      (Fintype.card Alphabet:ENNReal)*54 := by
    calc
      _ ≤ ∑ _ : Alphabet,∑ _ : Fin 9 × Fin 6,(1:ENNReal) := by
        apply sum_le_sum;intro a _;apply sum_le_sum;intro hole _;split_ifs <;> simp
      _ = _ := by simp
  have hc : Fintype.card Alphabet≠0 := Fintype.card_ne_zero
  have he := ENNReal.div_le_div_right hsum (Fintype.card Alphabet:ENNReal)
  rw [mul_div_assoc,ENNReal.mul_div_cancel (by exact_mod_cast hc) (by simp)] at he
  calc
    _ ≤ (SharedMoments.priceScaleTotal:ENNReal)/(2^31)*54 := mul_le_mul' le_rfl he
    _ = _ := by rw [←fee_price_scale];ring

 theorem nearCoveredAtP_bucket (W : List Proposal) (N : SigGolfCandidate.T3.HashOutput)
    (hole : Fin 9 × Fin 6) :
    NearCoveredAtP W N hole ↔ ListAlphabetNear ClaudeWCT.WCT9.wordDigit
      (atIndex (proposal N).1 W) (proposal N).2 hole := by
  unfold NearCoveredAtP SlotCoveredP ListAlphabetNear
  refine forall_congr' fun k => forall_congr' fun t => forall_congr' fun ht => ?_
  constructor
  · rintro ⟨p,hp,h1,h2,h3⟩
    refine ⟨p.2,(WCTEnvelope.mem_atIndex _ _ _).mpr ?_,h2,h3⟩
    rw [←h1];exact hp
  · rintro ⟨a,ha,h2,h3⟩
    exact ⟨((proposal N).1,a),(WCTEnvelope.mem_atIndex _ _ _).mp ha,rfl,h2,h3⟩

 theorem nearPrice_eq_sum (W : List Proposal) : nearPrice W =
    ∑ index : Fin (2^31),nearBucket (atIndex index W) := by
  let g : Proposal → ENNReal := fun p => ∑ hole : Fin 9 × Fin 6,
    if ListAlphabetNear ClaudeWCT.WCT9.wordDigit (atIndex p.1 W) p.2 hole then 1 else 0
  have hs (N : SigGolfCandidate.T3.HashOutput) : nearScoreP W N =
      if admissible N=true then g (proposal N) else 0 := by
    unfold nearScoreP
    congr 1
    apply sum_congr rfl
    intro hole _
    exact if_congr (nearCoveredAtP_bucket W N hole) rfl rfl
  have hc : Fintype.card Alphabet=SharedMoments.alphabetSize := alphabet_card (Fintype.card_fin 563)
  have hsum : (∑ p,g p) = (SharedMoments.alphabetSize:ENNReal)*
      ∑ index : Fin (2^31),finiteAverage (fun a => g (index,a)) := by
    rw [Fintype.sum_prod_type,mul_sum]
    apply sum_congr rfl;intro index _
    unfold finiteAverage
    rw [hc,ENNReal.mul_div_cancel (by norm_num [SharedMoments.alphabetSize]) (by simp)]
  unfold nearPrice SigGolfCandidate.T3.BPORS.finiteAverage
  simp_rw [hs]
  rw [sum_admissible g,hsum,Fintype.card_bitVec]
  unfold nearBucket
  rw [←mul_sum,←price_scale]
  simp only [div_eq_mul_inv]
  ring

 theorem nearBucket_insert (L R : List Alphabet) (b : Alphabet) :
    nearBucket (L++R) ≤ nearBucket (L++b::R) := by
  unfold nearBucket finiteAverage
  apply mul_le_mul' le_rfl
  apply ENNReal.div_le_div_right
  apply sum_le_sum
  intro a _
  apply sum_le_sum
  intro hole _
  by_cases h1 : ListAlphabetNear ClaudeWCT.WCT9.wordDigit (L++R) a hole
  · have h2 : ListAlphabetNear ClaudeWCT.WCT9.wordDigit (L++b::R) a hole := by
      intro k t hne
      obtain ⟨e,he,hc⟩ := h1 k t hne
      refine ⟨e,?_,hc⟩
      rcases List.mem_append.mp he with he|he
      · exact List.mem_append_left _ he
      · exact List.mem_append_right _ (List.mem_cons_of_mem b he)
    simp only [if_pos h1,if_pos h2,le_refl]
  · simp only [if_neg h1]
    exact zero_le

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics ClaudeWCT.Numerics.SharedMoments
open SigGolfCandidate.T3.BPORS.History (atIndex)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem law_nearPrice_coordAverage (T : Nat) :
    Law.lawAvg honestLaw T nearPrice =
      (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T nearBucket := by
  have he : nearPrice = fun W => ∑ i : Fin (2^31),nearBucket (atIndex i W) := funext nearPrice_eq_sum
  rw [he]
  have h := law_marked_sum (α:=Fin (2^31)) honestCoordLaw honestCoordLaw_sum T nearBucket
  simpa only [honestLaw,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using h

 theorem near_finite_row (r : Nat) (hr : r≤80) :
    (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      feeCoefficient*(SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit h:ENNReal)) =
        feeCoefficient*(forestNearMoment r:ENNReal) := by
  rw [←Finset.mul_sum,←Nat.cast_sum]
  have h := SharedCoverage.forest_near_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
    WCTEnvelope.w1Table_wordDigit WCTEnvelope.wfTable_wordDigit rows_checked r (by omega)
  exact congrArg (fun n : Nat => feeCoefficient*(n:ENNReal)) h

 theorem law_nearPrice_mean_bound : Law.lawAvg honestLaw (2^32) nearPrice ≤ (19493/50) := by
  rw [law_nearPrice_coordAverage]
  apply coordAverage_history_bound (2^32) 54 1 (by norm_num) (by norm_num)
    nearBucket (fun _ h => feeCoefficient*(SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit h:ENNReal))
    forestNearMoment (19493/50) (fun L b R => nearBucket_insert L R b)
  · intro r _ h
    exact nearBucket_ofFn_le h
  · intro r hr
    simpa only [Nat.cast_one,div_one] using (near_finite_row r hr).le
  · intro W
    simpa only [Nat.cast_one,Nat.cast_ofNat,div_one] using nearBucket_bound W
  · intro g hp ht
    have h := near_bound_of_rows (2^32) _ kappa_mul_rate_le_one (thin_window _ le_rfl)
      1 le_rfl thin_lambda g hp ht
    simpa only [Nat.cast_one,div_one] using h

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleComp.EvalDist ENNReal Finset ClaudeWCT.Numerics
open SigGolfCandidate.T3 SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 def NearCovered (X : List HashOutput) (N : HashOutput) : Prop :=
  ∃ hole,NearCoveredAtP (X.map proposal) N hole
noncomputable def nearScore (X : List HashOutput) (N : HashOutput) : ENNReal :=
  nearScoreP (X.map proposal) N

 theorem nearCoveredAtP_source (X : List HashOutput) (N : HashOutput) (hole : Fin 9 × Fin 6) :
    NearCoveredAtP (X.map proposal) N hole ↔
      ∀ k t,(k,t)≠hole → ∃ output∈X,ClaudeWCT.WCT9.digestIndex output=ClaudeWCT.WCT9.digestIndex N ∧
        SharedForest.rawChildFromOutput output k=SharedForest.rawChildFromOutput N k ∧
        ClaudeWCT.WCT9.wordDigit (SharedForest.forestRank N k.val) t≤
          ClaudeWCT.WCT9.wordDigit (SharedForest.forestRank output k.val) t := by
  unfold NearCoveredAtP
  exact forall_congr' fun k => forall_congr' fun t => imp_congr_right fun _ => slotCoveredP_source X N k t

 theorem nearCoveredAtP_append (W V : List Proposal) (N : HashOutput) (hole : Fin 9 × Fin 6)
    (h : NearCoveredAtP W N hole) : NearCoveredAtP (W++V) N hole := by
  intro k t hne
  obtain ⟨p,hp,h1,h2,h3⟩ := h k t hne
  exact ⟨p,List.mem_append_left V hp,h1,h2,h3⟩

 theorem nearScore_append_mono (X Y : List HashOutput) (N : HashOutput) :
    nearScore X N≤nearScore (X++Y) N := by
  unfold nearScore nearScoreP
  rw [List.map_append]
  split_ifs with ha
  · apply sum_le_sum
    intro hole _
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (nearCoveredAtP_append _ _ N hole h1) h2
    · exact zero_le_one
    · exact le_rfl
  · exact le_rfl

 theorem one_le_nearScore (X : List HashOutput) (N : HashOutput)
    (ha : admissible N=true) (h : NearCovered X N) : 1≤nearScore X N := by
  obtain ⟨hole,hh⟩ := h
  unfold nearScore nearScoreP
  rw [if_pos ha]
  have hs := Finset.single_le_sum (s:=Finset.univ) (a:=hole)
    (f:=fun h => if NearCoveredAtP (X.map proposal) N h then (1:ENNReal) else 0)
    (fun _ _ => zero_le) (mem_univ hole)
  simpa only [if_pos hh] using hs

 theorem average_nearScore (X : List HashOutput) :
    BPORS.finiteAverage (nearScore X) = nearPrice (X.map proposal)/2^128 := by
  unfold nearPrice nearScore
  rw [mul_comm,ENNReal.mul_div_cancel_right (by positivity) (by finiteness)]

noncomputable def withCoverage {P : Type} [Fintype P] [SampleableType P]
    (S : FtsBankSpec P) (score : List HashOutput → HashOutput → ENNReal)
    (covered : List HashOutput → HashOutput → Prop)
    (hscore : ∀ X N,S.admissible N=true → covered X N → 1 ≤ score X N)
    (hmono : ∀ X Y N,score X N ≤ score (X++Y) N)
    (price : List P → ENNReal)
    (havg : ∀ X,BPORS.finiteAverage (score X)=price (X.map S.proposal)/2^128)
    (rate : ENNReal)
    (hrate : Law.lawAvg S.law S.horizon (fun W => price W-S.specTheta)≤rate) : FtsBankSpec P :=
  { S with
    score := score
    covered := covered
    one_le_score := hscore
    score_append_mono := hmono
    price := price
    average_score := havg
    excessRate := rate
    excess_le := hrate }

noncomputable def nearLawSpec : FtsBankSpec Proposal :=
  withCoverage lawSpec nearScore NearCovered one_le_nearScore nearScore_append_mono
    nearPrice average_nearScore (19493/50)
    ((Law.lawAvg_mono honestLaw (2^32) (fun _ => tsub_le_self)).trans law_nearPrice_mean_bound)

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.WCTEnvelope
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

theorem wordDigit_coordinate_coeff (K : Nat) (hK : K ∈ [64,128])
    (r : Nat) (hr : r ≤ 20) (c : Nat) :
    (coordinatePoly K r).coeff c ≤
      (univ.filter fun E : Fin r → Fin K × Fin 563 =>
        coordinateCoverage ClaudeWCT.WCT9.wordDigit E=c).card := by
  have hpoly (j : Nat) (hj1 : 1 ≤ j) (hj8 : j ≤ 8) :
      lawPoly coverageLaw 563 j = naturalDataPoly (coverageHData j) :=
    lawPoly_eq_data coverageLaw 563 j
      (coverageLaw_eq_packed ClaudeWCT.WCT9.wordDigit wordsOf_wordDigit
        ClaudeWCT.WCT9.wordDigit_le_four (Fintype.card_fin 563)
        coverageH_packed j hj1 hj8)
      (coverageHData_bounds ⟨j, by omega⟩)
  exact coordinatePoly_coeff_below ClaudeWCT.WCT9.wordDigit coverageLaw
    (coverageLaw_correct ClaudeWCT.WCT9.wordDigit wordsOf_wordDigit
      ClaudeWCT.WCT9.wordDigit_le_four)
    (Fintype.card_fin 563) K hK ⟨r, by omega⟩ coverageLaw_zero_poly
    ((hpoly 1 (by decide) (by decide)).trans coverageH1_poly)
    (fun j hj1 hj8 => hpoly j (by omega) hj8) c

end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedFees
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.WCTEnvelope
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.SharedPathForest
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

theorem wordDigit_rowDots_convolution (r : Nat) (hr : r≤20) :
    rowDots r=convolutionDots r (SharedPathPacked.forest r) := by
  have hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K × Fin 563 =>
        coordinateCoverage ClaudeWCT.WCT9.wordDigit E=j).card :=
    fun K hK u hu j => wordDigit_coordinate_coeff K hK u (by omega) j
  exact rowDots_convolution r hr (actualPoly r)
    (actual_encoding ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r hr hp)
    (actual_coeff_small ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r hr hp)
    ((actual_mass_le ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r hr hp).trans
      (forest_mass_3072 r hr))

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem smallRows_checked (r : Nat) (hr : r≤4) : rowDots r=certifiedPayoff r := by
  interval_cases r
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4

theorem wordDigit_rows_of_convolutions
    (hconv : ∀ r, 5≤r → r≤18 →
      convolutionDots r (SharedPathPacked.forest r)=certifiedPayoff r)
    (r : Nat) (hlo : 1≤r) (hhi : r≤18) : rowDots r=certifiedPayoff r := by
  by_cases hs : r≤4
  · exact smallRows_checked r hs
  · exact (wordDigit_rowDots_convolution r (by omega)).trans (hconv r (by omega) hhi)

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Bank.Paired
open ClaudeWCT.Numerics

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

end ClaudeWCT.Bank.Paired
end
-- ==== merged from ClaudeWCT_Numerics_WCTPrice ====
section

/-! Route C for the FTS bank on #938's cap-777 law (RC938; R6 campaign stream RC, sec-rc/RC_SPEC.txt): binned
row bounds, thinned envelope moments, and the route-C excess theorems that replace the winsorized-Chernoff
certificate (removed). Every route-C moment is an insertion-monotone payoff, so #938's binomial thinning
(`Law.coordAverage_thin`: honest at rate `p` ≤ uniform at rate `kappa * p`) applies to all of them; the Scarf
payment of the one-large-bucket term is bounded by its monotone majorant `costOf 5`. The route-C split is
at rows `≤ 80`, so the long-row term is the `poissonCheckQ` tail only. The theorems
`excess_{middle,high,low,large,tiny}_certified` keep their installed names; their fee premise is gone. -/

namespace ClaudeWCT.Numerics.RouteCBank
open Finset Polynomial
open ClaudeWCT.Numerics ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData
open ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.SharedMoments (forestMoment alphabetSize fieldSize)
open ClaudeWCT.Numerics.SharedCoverage (ForestHistory forestCoverage)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem forestN_eq (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ 18) : forestN r = SharedPathPacked.forest r := by
  interval_cases r
  · exact forest_small_1.symm
  · exact forest_small_2.symm
  · exact forest_small_3.symm
  · exact forest_small_4.symm
  · exact SharedGeneratedForest.forest_5_checked.symm
  · exact SharedGeneratedForest.forest_6_checked.symm
  · exact SharedGeneratedForest.forest_7_checked.symm
  · exact SharedGeneratedForest.forest_8_checked.symm
  · exact SharedGeneratedForest.forest_9_checked.symm
  · exact SharedGeneratedForest.forest_10_checked.symm
  · exact SharedGeneratedForest.forest_11_checked.symm
  · exact SharedGeneratedForest.forest_12_checked.symm
  · exact SharedGeneratedForest.forest_13_checked.symm
  · exact SharedGeneratedForest.forest_14_checked.symm
  · exact SharedGeneratedForest.forest_15_checked.symm
  · exact SharedGeneratedForest.forest_16_checked.symm
  · exact SharedGeneratedForest.forest_17_checked.symm
  · exact SharedGeneratedForest.forest_18_checked.symm

theorem runEntries_length (runs : List (ℕ × ℕ × ℕ))
    (hidx : (runEntries runs).map Prod.fst = List.range 7210) : (runEntries runs).length = 7210 := by
  have := congrArg List.length hidx
  simpa using this

theorem packRuns_tree (runs : List (ℕ × ℕ × ℕ)) (hlen : (runEntries runs).length = 7210) :
    packRuns runs = SharedFees.packTree 4096 13 0
      (fun i => if i < 7210 then runFee runs (7209 - i) else 0) := by
  rw [packRuns, SharedFees.packList_eq_tree]
  apply SharedFees.packTree_congr
  intro i hi
  simp only [Nat.zero_add]
  have hl : ((runEntries runs).map Prod.snd).length = 7210 := by simp [hlen]
  by_cases h : i < 7210
  · rw [List.getElem?_reverse (by rw [hl]; exact h), hl, if_pos h]
    simp only [runFee, List.getElem?_map]
  · have hh : ((runEntries runs).map Prod.snd).reverse.length ≤ i := by
      rw [List.length_reverse, hl]; omega
    rw [List.getElem?_eq_none hh, if_neg h]
    rfl

theorem packedDot_runs (P : ℕ[X]) (runs : List (ℕ × ℕ × ℕ)) (hlen : (runEntries runs).length = 7210)
    (G : ℕ) (hfee : ∀ i, i < 7210 → runFee runs i ≤ G) (hG : G ≤ 2 ^ 900) (hmass : P.eval 1 ≤ 2 ^ 3072) :
    SharedFees.packedDot (P.eval (2 ^ 4096)) (packRuns runs) =
      ∑ i ∈ range 7210, P.coeff i * runFee runs i := by
  rw [packRuns_tree runs hlen]
  unfold SharedFees.packedDot
  rw [SharedFees.packTree_reversed 4096 13 7210 (runFee runs) (by decide)]
  have hs : (∑ i ∈ range 7210, runFee runs i) ≤ 7210 * 2 ^ 900 := by
    calc (∑ i ∈ range 7210, runFee runs i) ≤ ∑ _i ∈ range 7210, 2 ^ 900 :=
          Finset.sum_le_sum fun i hi => (hfee i (Finset.mem_range.mp hi)).trans hG
      _ = 7210 * 2 ^ 900 := by simp
  have hm : P.eval 1 * (∑ i ∈ range 7210, runFee runs i) < 2 ^ 4096 :=
    (Nat.mul_le_mul hmass hs).trans_lt (by decide +kernel)
  exact SharedFees.convolution_shift P 4096 7210 (runFee runs) hm

theorem massDot (P : ℕ[X]) (hmass : P.eval 1 ≤ 2 ^ 3072) :
    SharedFees.packedDot (P.eval (2 ^ 4096)) SharedGeneratedFeeVector.MassFee =
      ∑ i ∈ range 7210, P.coeff i := by
  rw [← SharedGeneratedFeeVector.packedFee_0_checked]
  have hs : (∑ i ∈ range 7210, SharedFees.feeValue 0 i) = 7210 := by
    simp [SharedFees.feeValue]
  rw [SharedFees.packedDot_fee P _ 0 rfl (by rw [hs]; exact (Nat.mul_le_mul_right _ hmass).trans_lt (by decide +kernel))]
  simp [SharedFees.feeValue]

theorem runsOk_mem {k : ℕ} {runs : List (ℕ × ℕ × ℕ)} {G : ℕ} (h : runsOk k runs G = true)
    (e : ℕ × ℕ × ℕ) (he : e ∈ runs) :
    e.1 ≤ e.2.1 ∧ okOf k rcPar (lowerQ rcPar.g e.1) (upperQ rcPar.g e.2.1) e.2.2 = true ∧ e.2.2 ≤ G := by
  unfold runsOk at h
  have := List.all_eq_true.mp h e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- Binned row bound of kind `k`: the cost summed over the histories of row `r` is paid by the row
dot product. -/
theorem row_bound (k : ℕ) (runs : List (ℕ × ℕ × ℕ)) (G : ℕ) (hP : ParFacts rcPar)
    (hidx : (runEntries runs).map Prod.fst = List.range 7210) (hruns : runsOk k runs G = true)
    (hglob : globOk k rcPar G = true) (hG : G ≤ 2 ^ 900) (r : ℕ) (h1 : 1 ≤ r) (h18 : r ≤ 18) :
    (∑ h : ForestHistory (Fin 563) r, ENNReal.ofReal
      (costOf k rcPar ((rcPar.g : ℝ) / 2 ^ 66 * (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)))) ≤
      ENNReal.ofReal ((rcPar.g : ℝ) / 2 ^ 66) / (feeScale : ENNReal) *
        (dotRow (packRuns runs) G r (forestN r) : ENNReal) := by
  classical
  have hord : ∀ e ∈ runs, e.1 ≤ e.2.1 := fun e he => (runsOk_mem hruns e he).1
  have hlen := runEntries_length runs hidx
  have hp : ∀ K, K ∈ [64, 128] → ∀ u, u ≤ r → ∀ j, (SharedCoverage.coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K × Fin 563 =>
        N600.coordinateCoverage ClaudeWCT.WCT9.wordDigit E = j).card :=
    fun K hK u hu j => SharedCoverage.wordDigit_coordinate_coeff K hK u (by omega) j
  set P := SharedPathForest.actualPoly r with hPdef
  have henc : SharedPathPacked.forest r = P.eval (2 ^ 4096) :=
    SharedPathForest.actual_encoding ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r (by omega) hp
  have hmass : P.eval 1 ≤ 2 ^ 3072 :=
    (SharedPathForest.actual_mass_le ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r (by omega) hp).trans
      (SharedFees.forest_mass_3072 r (by omega))
  have hfeeG : ∀ j, j < 7210 → runFee runs j ≤ G := by
    intro j hj
    obtain ⟨e, he, _, _, hf⟩ := runFee_lookup runs 7210 hord hidx j hj
    rw [hf]; exact (runsOk_mem hruns e he).2.2
  rw [forestN_eq r h1 h18, henc]
  unfold dotRow
  rw [packedDot_runs P runs hlen G hfeeG hG hmass, massDot P hmass]
  have hκ : (0 : ℝ) ≤ (rcPar.g : ℝ) / 2 ^ 66 := by positivity
  have hS := feeScale_pos
  apply SharedFees.ofReal_sum_nat_bound _ _ _ feeScale hκ (by norm_num [feeScale])
    (fun h => costOf_nonneg k rcPar hP _ (by positivity))
  have hreal := SharedFees.histogram_moment_bound 7210 (forestMoment r) G
    (SharedPathForest.actualGood ClaudeWCT.WCT9.wordDigit) (SharedPathForest.actualBin ClaudeWCT.WCT9.wordDigit)
    (forestCoverage ClaudeWCT.WCT9.wordDigit) P
    (SharedPathForest.actual_histogram ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r (by omega) hp)
    (SharedCoverage.forest_coverage_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
      WCTEnvelope.w1Table_wordDigit SharedMoments.rows_checked r (by omega))
    (fun h => costOf k rcPar ((rcPar.g : ℝ) / 2 ^ 66 * (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)))
    (runFee runs) ((rcPar.g : ℝ) / 2 ^ 66 / feeScale) (by positivity) hfeeG
    (fun h => by
      have := glob_sound k rcPar hP G hglob _ (by positivity : (0 : ℝ) ≤ (rcPar.g : ℝ) / 2 ^ 66 *
        (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ))
      calc _ ≤ _ := this
        _ = _ := by ring)
    (fun h hg hb => by
      obtain ⟨e, he, hlo, hhi, hf⟩ := runFee_lookup runs 7210 hord hidx _ hb
      obtain ⟨_, hok, _⟩ := runsOk_mem hruns e he
      have hb' := bin_bounds rcPar.g (SharedPathForest.actual_interval ClaudeWCT.WCT9.wordDigit
        (by omega) h hg)
      have hx0 : (0 : ℝ) ≤ (rcPar.g : ℝ) / 2 ^ 66 * (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ) := by
        positivity
      have := ok_sound k rcPar hP _ _ e.2.2 hok _ hx0 ((lowerQ_mono rcPar.g hlo).trans hb'.1)
        (hb'.2.trans (upperQ_mono rcPar.g hhi))
      rw [hf]
      calc _ ≤ _ := this
        _ = _ := by ring)
  simpa only [mul_comm] using hreal

end ClaudeWCT.Numerics.RouteCBank

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.RouteCBank
open ClaudeWCT.Numerics.SharedMoments (forestMoment alphabetSize fieldSize priceScaleTotal)
open ClaudeWCT.Numerics.SharedCoverage (ForestHistory forestCoverage)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The installed price coefficient is the route-C data gate. -/
theorem rc_coef_real : feeCoefficient.toReal = (rcPar.g : ℝ) / 2 ^ 66 := by
  rw [feeCoefficient_real]; rfl

theorem rc_coef : ENNReal.ofReal ((rcPar.g : ℝ) / 2 ^ 66) = feeCoefficient := by
  rw [← rc_coef_real, ENNReal.ofReal_toReal (by unfold feeCoefficient; finiteness)]

theorem rc_pst : priceScaleTotal = pst := rfl

/-- Thinned envelope bound for a coordinate average at a general rate and horizon (the conditional law
uses rate `(2^31-1)⁻¹` and horizon `2^32 - r`): the honest law at rate `p` is bounded by the uniform law at
rate `kappa * p` (cap-777 thinning), whose rows are checked by `poissonCheckQ` with `u = 13167581e-8` and
`λ = 2027792e-6`. -/
theorem rc_envelope_thin (rate : ENNReal) (hrate : kappa * rate ≤ 1) (T : ℕ)
    (hlam : (T : ENNReal) * (kappa * rate) * 1 ≤ ((2027792 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal))
    (hu : (1 - kappa * rate) ^ (T - 80) ≤ ((13167581 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal))
    (G : ℕ) (hG0 : 0 < G) (row : ℕ → ℕ) (f : List Alphabet → ENNReal)
    (hmono : ∀ L b R, f (L ++ R) ≤ f (L ++ b :: R))
    (g : (r : ℕ) → ForestHistory (Fin 563) r → ENNReal)
    (hfg : ∀ r ≤ 80, ∀ h : Fin r → Alphabet, f (List.ofFn h) ≤ g r (splitHistory h))
    (hfees : ∀ r ≤ 80, (∑ h, g r h) ≤ feeCoefficient / (feeScale : ENNReal) * (row r : ENNReal))
    (hpoint : ∀ W, f W ≤ (G : ENNReal) * feeCoefficient * alphabetSize / (feeScale : ENNReal))
    (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : N600.poissonCheckQ fieldSize 13167581 100000000 2027792 1000000 (fun r => 16 ^ r * row r)
      (G * alphabetSize) (G * priceScaleTotal) feeScale Mn Md 80 = true) :
    (2 ^ 31 : ENNReal) * Law.coordAverage rate honestCoordLaw T f ≤ (Mn : ENNReal) / Md := by
  have hS : 0 < feeScale := by norm_num [feeScale]
  refine (mul_le_mul' le_rfl (Law.coordAverage_thin rate kappa honestCoordLaw uniformCoordLaw
    honestCoordLaw_sum uniformCoordLaw_sum honestCoordLaw_density kappa_one_le hrate T f hmono)).trans ?_
  let C : ENNReal := (G : ENNReal) * feeCoefficient * alphabetSize / (feeScale : ENNReal)
  have hC0 : C ≠ 0 := by
    have hMc : (G : ENNReal) ≠ 0 := by exact_mod_cast hG0.ne'
    have hfc : feeCoefficient ≠ 0 := by norm_num [feeCoefficient]
    have hDc : (alphabetSize : ENNReal) ≠ 0 := by norm_num [alphabetSize]
    exact ENNReal.div_ne_zero.mpr ⟨mul_ne_zero (mul_ne_zero hMc hfc) hDc, ENNReal.natCast_ne_top _⟩
  have hCt : C ≠ ⊤ := by dsimp [C, feeCoefficient]; finiteness
  let v : ℕ → ENNReal := fun r => Law.lawAvg uniformCoordLaw r (fun W => f W / C)
  have hv1 : ∀ r ≤ 80, v r ≤ 1 ^ r * (((16 ^ r * row r : ℕ) : ENNReal) /
      ((G * alphabetSize * fieldSize ^ (9 * r) : ℕ) : ENNReal)) := by
    intro r hr
    have h := uniform_normalized_history_row r G feeScale (row r) hG0 hS f (g r) (hfg r hr) (hfees r hr)
    exact h.trans_eq (mul_div_assoc _ _ _)
  have hv2 : ∀ r, 80 < r → v r ≤ 1 := fun r _ => uniform_normalized_le_one r f C hC0 hCt hpoint
  have hkey := N600.poissonCheckQ_sound_tilt hcheck (by norm_num [fieldSize]) (by norm_num) (by norm_num)
    (Nat.mul_pos hG0 (by norm_num [alphabetSize])) (by norm_num [feeScale]) hMd hrate 1 le_rfl hlam hu v
    hv1 hv2
  calc (2 ^ 31 : ENNReal) * Law.coordAverage (kappa * rate) uniformCoordLaw T f =
      ((2 ^ 31 : ENNReal) * C) * Law.coordAverage (kappa * rate) uniformCoordLaw T (fun W => f W / C) :=
        (coordAverage_scaled uniformCoordLaw T f C (2 ^ 31) (kappa * rate) hC0 hCt).symm
    _ = ((G * priceScaleTotal : ℕ) : ENNReal) / (feeScale : ENNReal) *
        SphincsSecurity.Concrete.binomialAverage (kappa * rate) T v := by
      rw [show (2 ^ 31 : ENNReal) * C = ((G * priceScaleTotal : ℕ) : ENNReal) / (feeScale : ENNReal) from
        normalizer_scale G feeScale]
      rfl
    _ ≤ (Mn : ENNReal) / Md := hkey

theorem rc_price_real {r : ℕ} (h : Fin r → Alphabet) :
    (priceBucket (List.ofFn h)).toReal =
      (rcPar.g : ℝ) / 2 ^ 66 * (forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h) : ℝ) := by
  rw [priceBucket_ofFn, ENNReal.toReal_mul, rc_coef_real, ENNReal.toReal_natCast]

theorem rc_price_bound (W : List Alphabet) :
    (priceBucket W).toReal ≤ (rcPar.g : ℝ) / 2 ^ 66 * alphabetSize := by
  have h := ENNReal.toReal_mono (by unfold feeCoefficient; finiteness) (priceBucket_le W)
  rwa [ENNReal.toReal_mul, rc_coef_real, ENNReal.toReal_natCast] at h

/-- Global fee row: every row is paid at the global fee on its first moment. -/
theorem rc_global_row (k : ℕ) (hP : ParFacts rcPar) (G : ℕ) (hglob : globOk k rcPar G = true)
    (r : ℕ) (hr : r ≤ 80) :
    (∑ h : ForestHistory (Fin 563) r, ENNReal.ofReal
      (costOf k rcPar ((rcPar.g : ℝ) / 2 ^ 66 * (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)))) ≤
      ENNReal.ofReal ((rcPar.g : ℝ) / 2 ^ 66) / (feeScale : ENNReal) * ((G * forestMoment r : ℕ) : ENNReal) := by
  have hκ : (0 : ℝ) ≤ (rcPar.g : ℝ) / 2 ^ 66 := by positivity
  have hS := feeScale_pos
  apply SharedFees.ofReal_sum_nat_bound _ _ _ feeScale hκ (by norm_num [feeScale])
    (fun h => costOf_nonneg k rcPar hP _ (by positivity))
  have htot := SharedCoverage.forest_coverage_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
    WCTEnvelope.w1Table_wordDigit SharedMoments.rows_checked r (by omega)
  have htotR : (∑ h : ForestHistory (Fin 563) r, (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)) =
      (forestMoment r : ℝ) := by exact_mod_cast htot
  calc _ ≤ ∑ h : ForestHistory (Fin 563) r, (rcPar.g : ℝ) / 2 ^ 66 *
        (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ) * G / feeScale :=
      Finset.sum_le_sum fun h _ => glob_sound k rcPar hP G hglob _ (by positivity)
    _ = _ := by
      rw [← Finset.sum_div, ← Finset.sum_mul, ← Finset.mul_sum, htotR]
      push_cast
      ring

theorem rc_point (k : ℕ) (hP : ParFacts rcPar) (G : ℕ) (hglob : globOk k rcPar G = true) (W : List Alphabet) :
    ENNReal.ofReal (costOf k rcPar (priceBucket W).toReal) ≤
      (G : ENNReal) * feeCoefficient * alphabetSize / (feeScale : ENNReal) := by
  have hS := feeScale_pos
  have h1 := glob_sound k rcPar hP G hglob (priceBucket W).toReal ENNReal.toReal_nonneg
  have h2 : (priceBucket W).toReal * G / feeScale ≤ (rcPar.g : ℝ) / 2 ^ 66 * alphabetSize * G / feeScale := by
    gcongr; exact rc_price_bound W
  calc ENNReal.ofReal (costOf k rcPar (priceBucket W).toReal)
      ≤ ENNReal.ofReal ((rcPar.g : ℝ) / 2 ^ 66 * alphabetSize * G / feeScale) :=
        ENNReal.ofReal_le_ofReal (h1.trans h2)
    _ = _ := by
      rw [← rc_coef, ENNReal.ofReal_div_of_pos hS, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]
      ring

/-- Route-C costs of the bucket price are insertion-monotone. -/
theorem rc_cost_insert (k : ℕ) (hP : ParFacts rcPar) (L R : List Alphabet) (b : Alphabet) :
    ENNReal.ofReal (costOf k rcPar (priceBucket (L ++ R)).toReal) ≤
      ENNReal.ofReal (costOf k rcPar (priceBucket (L ++ b :: R)).toReal) :=
  ENNReal.ofReal_le_ofReal (costOf_mono k rcPar hP ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (priceBucket_ne_top _) (priceBucket_insert L R b)))

/-- A route-C moment of kind `k` (0 mean, 1 second moment, 2 count, 3 over, 4 clipped mgf, 5 Scarf). -/
theorem rc_kind_all (k : ℕ) (runs : List (ℕ × ℕ × ℕ)) (G pack : ℕ) (hpack : packRuns runs = pack)
    (hP : ParFacts rcPar) (hidx : (runEntries runs).map Prod.fst = List.range 7210)
    (hruns : runsOk k runs G = true) (hglob : globOk k rcPar G = true) (hG : G ≤ 2 ^ 900) (hG0 : 0 < G)
    (rate : ENNReal) (hrate : kappa * rate ≤ 1) (T : ℕ)
    (hlam : (T : ENNReal) * (kappa * rate) * 1 ≤ ((2027792 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal))
    (hu : (1 - kappa * rate) ^ (T - 80) ≤ ((13167581 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal))
    (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : N600.poissonCheckQ fieldSize 13167581 100000000 2027792 1000000 (fun r => 16 ^ r * rowAll pack G r)
      (G * alphabetSize) (G * pst) feeScale Mn Md 80 = true) :
    (2 ^ 31 : ENNReal) * Law.coordAverage rate honestCoordLaw T
      (fun L => ENNReal.ofReal (costOf k rcPar (priceBucket L).toReal)) ≤ (Mn : ENNReal) / Md := by
  apply rc_envelope_thin rate hrate T hlam hu G hG0 (rowAll pack G) _ (fun L b R => rc_cost_insert k hP L R b)
    (fun r h => ENNReal.ofReal (costOf k rcPar ((rcPar.g : ℝ) / 2 ^ 66 *
      (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)))) _ _ (rc_point k hP G hglob) Mn Md hMd
    (by rw [rc_pst]; exact hcheck)
  · intro r _ h
    rw [rc_price_real]
  · intro r hr
    by_cases hrow : 1 ≤ r ∧ r ≤ 18
    · have h := row_bound k runs G hP hidx hruns hglob hG r hrow.1 hrow.2
      rw [hpack, rc_coef] at h
      unfold rowAll
      rwa [if_pos hrow, dotRowC_eq _ _ _ hrow.2]
    · have h := rc_global_row k hP G hglob r hr
      rw [rc_coef] at h
      unfold rowAll
      rwa [if_neg hrow]

/-- The long-row first moment (bucket price on rows above 80: the `poissonCheckQ` tail term). -/
theorem rc_long (rate : ENNReal) (hrate : kappa * rate ≤ 1) (T : ℕ)
    (hlam : (T : ENNReal) * (kappa * rate) * 1 ≤ ((2027792 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal))
    (hu : (1 - kappa * rate) ^ (T - 80) ≤ ((13167581 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal))
    (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : N600.poissonCheckQ fieldSize 13167581 100000000 2027792 1000000 (fun r => 16 ^ r * rowLong r)
      (feeScale * alphabetSize) (feeScale * pst) feeScale Mn Md 80 = true) :
    (2 ^ 31 : ENNReal) * Law.coordAverage rate honestCoordLaw T
      (fun L => if 80 < L.length then priceBucket L else 0) ≤ (Mn : ENNReal) / Md := by
  have hS : (0 : ENNReal) < feeScale := by norm_num [feeScale]
  have hSt : (feeScale : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  apply rc_envelope_thin rate hrate T hlam hu feeScale (by norm_num [feeScale]) rowLong _ _
    (fun r h => if 80 < r then feeCoefficient * (forestCoverage ClaudeWCT.WCT9.wordDigit h : ENNReal) else 0)
    _ _ _ Mn Md hMd (by rw [rc_pst]; exact hcheck)
  · intro L b R
    by_cases h : 80 < (L ++ R).length
    · have h' : 80 < (L ++ b :: R).length := by simp at h ⊢; omega
      rw [if_pos h, if_pos h']
      exact priceBucket_insert L R b
    · rw [if_neg h]; exact zero_le
  · intro r _ h
    simp only [List.length_ofFn, priceBucket_ofFn]
    exact le_rfl
  · intro r hr
    unfold rowLong
    split_ifs with h80
    · omega
    · rw [Finset.sum_const_zero]
      exact zero_le
  · intro W
    split_ifs
    · rw [mul_assoc, mul_comm, mul_div_assoc, ENNReal.div_self hS.ne' hSt, mul_one]
      calc priceBucket W ≤ feeCoefficient * alphabetSize := priceBucket_le W
        _ = _ := by ring
    · exact zero_le

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
set_option maxHeartbeats 4000000

/-! ### Thinned envelope rates (RC_SPEC E3 / L4): unconditional and one-index conditional laws -/

theorem rc_rate_uncond : kappa * (2 ^ 31 : ENNReal)⁻¹ ≤ 1 := kappa_mul_rate_le_one

theorem rc_lam_uncond : ((2 ^ 32 : ℕ) : ENNReal) * (kappa * (2 ^ 31 : ENNReal)⁻¹) * 1 ≤
    ((2027792 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal) := thin_lambda

theorem rc_u_uncond : (1 - kappa * (2 ^ 31 : ENNReal)⁻¹) ^ (2 ^ 32 - 80) ≤
    ((13167581 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal) := thin_window (2 ^ 32) le_rfl

theorem rc_rate_cond : kappa * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹ ≤ 1 := by
  rw [kappa_exact]
  have hc : (ClaudeWCT.Numerics.SharedFtsCount.count : ENNReal) ≠ 0 := by
    norm_num [ClaudeWCT.Numerics.SharedFtsCount.count]
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hc)
    (by simp)) (by finiteness)).mp
  norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]

theorem rc_lam_cond (r : ℕ) (hr : 1 ≤ r) :
    ((2 ^ 32 - r : ℕ) : ENNReal) * (kappa * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) * 1 ≤
      ((2027792 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal) := by
  have hle : ((2 ^ 32 - r : ℕ) : ENNReal) ≤ ((2 ^ 32 - 1 : ℕ) : ENNReal) := by
    exact_mod_cast Nat.sub_le_sub_left hr _
  refine le_trans (mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl) ?_
  rw [mul_one, kappa_exact]
  have hc : (ClaudeWCT.Numerics.SharedFtsCount.count : ENNReal) ≠ 0 := by
    norm_num [ClaudeWCT.Numerics.SharedFtsCount.count]
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.mul_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hc) (by simp))) (by finiteness)).mp
  norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- Conditional thinned window: `(1 - kappa/(2^31-1))^(2^32 - r - 80) ≤ 13167581e-8` for `r ≤ 80`
(tangent line of `exp` at 2, as `thin_window`). -/
theorem rc_u_cond (r : ℕ) (hr : r ≤ 80) :
    (1 - kappa * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) ^ (2 ^ 32 - r - 80) ≤
      ((13167581 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal) := by
  have hq1 := rc_rate_cond
  have hmono : (1 - kappa * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) ^ (2 ^ 32 - r - 80) ≤
      (1 - kappa * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) ^ (2 ^ 32 - 160) :=
    pow_le_pow_right_of_le_one' tsub_le_self (by omega)
  refine hmono.trans ?_
  have hfin : (1 - kappa * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) ^ (2 ^ 32 - 160) ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  apply (ENNReal.toReal_le_toReal hfin (by finiteness)).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hq1 ENNReal.one_ne_top, ENNReal.toReal_mul,
    kappa_toReal, ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  simp only [ENNReal.toReal_one]
  set k : ℝ := (ClaudeWCT.Numerics.SharedFtsCount.total : ℝ) / ClaudeWCT.Numerics.SharedFtsCount.count with hk
  have hkv : k = 52416169542617085727767971710947931910569984 / 51697785130018558464839655637843407521710080 := by
    rw [hk]; norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count]
  set n := 2 ^ 32 - 160 with hn
  have hn0 : ((2 ^ 32 - 160 : ℕ) : ℝ) = (2 : ℝ) ^ 32 - 160 := by norm_num
  have hq : (((2 ^ 31 - 1 : ℕ) : ℝ))⁻¹ = ((2 : ℝ) ^ 31 - 1)⁻¹ := by norm_num
  rw [hq]
  have h0 : (0 : ℝ) ≤ 1 - k * ((2 : ℝ) ^ 31 - 1)⁻¹ := by rw [hkv]; norm_num
  have hp : (1 - k * ((2 : ℝ) ^ 31 - 1)⁻¹ : ℝ) ≤ Real.exp (-(k * ((2 : ℝ) ^ 31 - 1)⁻¹)) :=
    Real.one_sub_le_exp_neg _
  have hpow : (1 - k * ((2 : ℝ) ^ 31 - 1)⁻¹ : ℝ) ^ n ≤ Real.exp (-(n * (k * ((2 : ℝ) ^ 31 - 1)⁻¹))) := by
    calc (1 - k * ((2 : ℝ) ^ 31 - 1)⁻¹ : ℝ) ^ n ≤ Real.exp (-(k * ((2 : ℝ) ^ 31 - 1)⁻¹)) ^ n :=
          pow_le_pow_left₀ h0 hp n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  set a0 : ℝ := ((2 : ℝ) ^ 32 - 160) * (k * ((2 : ℝ) ^ 31 - 1)⁻¹) with ha0
  have ha : a0 ≤ n * (k * ((2 : ℝ) ^ 31 - 1)⁻¹) := by rw [hn, hn0]
  have hlow : (100000000 : ℝ) / 13167581 ≤ (2.7182818283 : ℝ) ^ 2 * (a0 - 1) := by
    rw [ha0, hkv]; norm_num
  have hexp : (100000000 : ℝ) / 13167581 ≤ Real.exp (n * (k * ((2 : ℝ) ^ 31 - 1)⁻¹)) :=
    hlow.trans ((ClaudeWCT.Numerics.PoissonReflect.exp_lower a0).trans (Real.exp_le_exp.mpr ha))
  refine hpow.trans ?_
  rw [Real.exp_neg]
  have hpos : (0 : ℝ) < 100000000 / 13167581 := by norm_num
  calc (Real.exp (n * (k * ((2 : ℝ) ^ 31 - 1)⁻¹)))⁻¹ ≤ ((100000000 : ℝ) / 13167581)⁻¹ :=
        inv_anti₀ hpos hexp
    _ = ((13167581 : ℕ) : ℝ) / ((100000000 : ℕ) : ℝ) := by norm_num

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.RouteCBank
open ClaudeWCT.Numerics.SharedMoments (forestMoment alphabetSize fieldSize priceScaleTotal)
open ClaudeWCT.Numerics.SharedCoverage (ForestHistory forestCoverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem forestMoment_zero : forestMoment 0 = 0 := by decide +kernel

theorem rc_frac (n d : ℕ) (hd : 0 < d) : ENNReal.ofReal ((n : ℝ) / d) = (n : ENNReal) / d := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hd), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

theorem priceBucket_nil : priceBucket [] = 0 := by
  have htot := SharedCoverage.forest_coverage_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
    WCTEnvelope.w1Table_wordDigit SharedMoments.rows_checked 0 (by norm_num)
  rw [forestMoment_zero] at htot
  let h0 : Fin 0 → Alphabet := Fin.elim0
  have hc : forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h0) = 0 :=
    (Finset.sum_eq_zero_iff.mp htot) _ (Finset.mem_univ _)
  have hl : List.ofFn h0 = [] := List.ofFn_zero
  have := priceBucket_ofFn h0
  rw [hl, hc] at this
  simpa using this

theorem rc_conv_mean (L : List Alphabet) :
    min (priceBucket L) (ENNReal.ofReal rcPar.c0) = ENNReal.ofReal (costOf 0 rcPar (priceBucket L).toReal) := by
  show _ = ENNReal.ofReal (min (priceBucket L).toReal rcPar.c0)
  have hc : (0 : ℝ) ≤ rcPar.c0 := by rw [rc_c0]; norm_num
  rw [← ENNReal.toReal_ofReal hc, ← ENNReal.toReal_min (priceBucket_ne_top L) ENNReal.ofReal_ne_top,
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top (priceBucket_ne_top L) (min_le_left _ _)), ENNReal.toReal_ofReal hc]

theorem rc_conv_sec (L : List Alphabet) :
    min (priceBucket L) (ENNReal.ofReal rcPar.c0) ^ 2 = ENNReal.ofReal (costOf 1 rcPar (priceBucket L).toReal) := by
  show _ = ENNReal.ofReal (min (priceBucket L).toReal rcPar.c0 ^ 2)
  have hc : (0 : ℝ) ≤ rcPar.c0 := by rw [rc_c0]; norm_num
  rw [ENNReal.ofReal_pow (le_min ENNReal.toReal_nonneg hc)]
  exact congrArg (· ^ 2) (rc_conv_mean L)

theorem rc_conv_count (L : List Alphabet) :
    (if ENNReal.ofReal rcPar.c0 < priceBucket L then (1 : ENNReal) else 0) =
      ENNReal.ofReal (costOf 2 rcPar (priceBucket L).toReal) := by
  show _ = ENNReal.ofReal (if (rcPar.c0 : ℝ) < (priceBucket L).toReal then 1 else 0)
  have hc : (0 : ℝ) ≤ rcPar.c0 := by rw [rc_c0]; norm_num
  have hiff : ENNReal.ofReal rcPar.c0 < priceBucket L ↔ (rcPar.c0 : ℝ) < (priceBucket L).toReal :=
    ENNReal.ofReal_lt_iff_lt_toReal hc (priceBucket_ne_top L)
  by_cases h : (rcPar.c0 : ℝ) < (priceBucket L).toReal
  · rw [if_pos (hiff.mpr h), if_pos h, ENNReal.ofReal_one]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, ENNReal.ofReal_zero]

theorem rc_conv_over (L : List Alphabet) :
    priceBucket L - ENNReal.ofReal rcPar.c0 = ENNReal.ofReal (costOf 3 rcPar (priceBucket L).toReal) := by
  show _ = ENNReal.ofReal (max 0 ((priceBucket L).toReal - rcPar.c0))
  have hc : (0 : ℝ) ≤ rcPar.c0 := by rw [rc_c0]; norm_num
  rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_right zero_le, ENNReal.ofReal_sub _ hc,
    ENNReal.ofReal_toReal (priceBucket_ne_top L)]

theorem rc_conv_mgf (L : List Alphabet) :
    ENNReal.ofReal (Real.exp (rcPar.a * (min (priceBucket L) (ENNReal.ofReal rcPar.c0)).toReal)) - 1 =
      ENNReal.ofReal (costOf 4 rcPar (priceBucket L).toReal) := by
  show _ = ENNReal.ofReal (Real.exp (rcPar.a * min (priceBucket L).toReal rcPar.c0) - 1)
  have hc : (0 : ℝ) ≤ rcPar.c0 := by rw [rc_c0]; norm_num
  rw [ENNReal.toReal_min (priceBucket_ne_top L) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc,
    ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_one]

/-- The Scarf payment of a short-row large bucket is below its monotone majorant `costOf 5`. -/
theorem rc_scarf_major (L : List Alphabet) :
    (if L.length ≤ 80 ∧ ENNReal.ofReal rcPar.c0 < priceBucket L then
      ENNReal.ofReal (RouteC.scarf ((rcPar.θ : ℝ) - (priceBucket L).toReal) rcPar.m rcPar.vv) else 0) ≤
    ENNReal.ofReal (costOf 5 rcPar (priceBucket L).toReal) := by
  have hc : (0 : ℝ) ≤ rcPar.c0 := (parFacts_of_ok rcPar par_ok).c0.le
  have hiff : ENNReal.ofReal rcPar.c0 < priceBucket L ↔ (rcPar.c0 : ℝ) < (priceBucket L).toReal :=
    ENNReal.ofReal_lt_iff_lt_toReal hc (priceBucket_ne_top L)
  show _ ≤ ENNReal.ofReal (if (rcPar.c0 : ℝ) < (priceBucket L).toReal then
    RouteC.scarf (rcPar.θ - (priceBucket L).toReal) rcPar.m rcPar.vv else 0)
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (hiff.mp h1.2) h2
  · exact zero_le
  · exact zero_le

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.RouteCBank
open ClaudeWCT.Numerics.SharedMoments (forestMoment alphabetSize fieldSize priceScaleTotal)
open SigGolfCandidate.T3.BPORS.History (atIndex)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem rc_card : (Fintype.card (Fin (2 ^ 31)) : ENNReal) = 2 ^ 31 := by
  rw [Fintype.card_fin]; norm_num

theorem rc_cardm1 : Fintype.card (Fin (2 ^ 31)) - 1 = 2 ^ 31 - 1 := by rw [Fintype.card_fin]

theorem rc_prefactor (X : ENNReal) :
    ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal) * X ≤ (2 ^ 31 : ENNReal) * X := by
  rw [rc_cardm1]
  exact mul_le_mul' (by norm_num) le_rfl

/-- Route C bank excess at the middle threshold (thinned cap-777 envelope, `rcPar`). -/
theorem rc_excess_middle :
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((99843 : ℝ) / 50000 - 1 / 1024)) ≤
      ENNReal.ofReal ((1174 : ℝ) / 1000000) := by
  have hP := parFacts_of_ok rcPar par_ok
  have he : (fun W : List Proposal => price W - ENNReal.ofReal ((99843 : ℝ) / 50000 - 1 / 1024)) =
      fun W => (∑ i : Fin (2 ^ 31), priceBucket (atIndex i W)) - ENNReal.ofReal (rcPar.θ : ℝ) := by
    funext W; rw [price_eq_sum, rc_θ]
  rw [he]
  have hcard : 1 < Fintype.card (Fin (2 ^ 31)) := by rw [Fintype.card_fin]; norm_num
  have hθ0 : (0 : ℝ) ≤ (rcPar.θ : ℝ) := by rw [rc_θ]; norm_num
  have ha0 : (0 : ℝ) < (rcPar.a : ℝ) := by rw [rc_a]; norm_num
  have hnil : priceBucket [] ≤ ENNReal.ofReal (rcPar.c0 : ℝ) := by rw [priceBucket_nil]; exact zero_le
  -- the seven envelope moments
  have hmgf : (∑ _i : Fin (2 ^ 31), Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹ honestCoordLaw
      (2 ^ 32) (fun L => ENNReal.ofReal (Real.exp (rcPar.a * (min (priceBucket L)
        (ENNReal.ofReal rcPar.c0)).toReal)) - 1)) ≤ ENNReal.ofReal ((mgfN : ℝ) / mgfD) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, rc_card]
    simp_rw [rc_conv_mgf]
    rw [rc_frac _ _ (by norm_num [mgfD])]
    exact rc_kind_all 4 runs4 glob4 Pack4 pack4_eq hP entries4 runs4_ok glob4_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [mgfD]) env_mgf
  have hmean : ∀ r, 1 ≤ r → r ≤ 80 →
      ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal) * Law.coordAverage
        ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal)⁻¹ honestCoordLaw (2 ^ 32 - r)
        (fun L => min (priceBucket L) (ENNReal.ofReal rcPar.c0)) ≤ ENNReal.ofReal (rcPar.m : ℝ) := by
    intro r h1 h80
    simp_rw [rc_conv_mean]
    refine (rc_prefactor _).trans ?_
    rw [rc_m, rc_frac _ _ (by norm_num [meanD])]
    rw [rc_cardm1]
    exact rc_kind_all 0 runs0 glob0 Pack0 pack0_eq hP entries0 runs0_ok glob0_ok (by decide +kernel)
      (by decide +kernel) _ rc_rate_cond (2 ^ 32 - r) (rc_lam_cond r h1) (rc_u_cond r h80) _ _
      (by norm_num [meanD]) env_mean
  have hsecond : ∀ r, 1 ≤ r → r ≤ 80 →
      ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal) * Law.coordAverage
        ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal)⁻¹ honestCoordLaw (2 ^ 32 - r)
        (fun L => min (priceBucket L) (ENNReal.ofReal rcPar.c0) ^ 2) ≤ ENNReal.ofReal (rcPar.vv : ℝ) := by
    intro r h1 h80
    simp_rw [rc_conv_sec]
    refine (rc_prefactor _).trans ?_
    rw [rc_vv, rc_frac _ _ (by norm_num [secD])]
    rw [rc_cardm1]
    exact rc_kind_all 1 runs1 glob1 Pack1 pack1_eq hP entries1 runs1_ok glob1_ok (by decide +kernel)
      (by decide +kernel) _ rc_rate_cond (2 ^ 32 - r) (rc_lam_cond r h1) (rc_u_cond r h80) _ _
      (by norm_num [secD]) env_sec
  have hK1 : (Fintype.card (Fin (2 ^ 31)) : ENNReal) * Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹
      honestCoordLaw (2 ^ 32) (fun L => if L.length ≤ 80 ∧ ENNReal.ofReal rcPar.c0 < priceBucket L then
        ENNReal.ofReal (RouteC.scarf ((rcPar.θ : ℝ) - (priceBucket L).toReal) rcPar.m rcPar.vv) else 0) ≤
      ENNReal.ofReal ((scarfN : ℝ) / scarfD) := by
    rw [rc_card, rc_frac _ _ (by norm_num [scarfD])]
    refine (mul_le_mul' le_rfl (Law.coordAverage_mono _ _ _ rc_scarf_major)).trans ?_
    exact rc_kind_all 5 runs5 glob5 Pack5 pack5_eq hP entries5 runs5_ok glob5_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [scarfD]) env_scarf
  have hover : (Fintype.card (Fin (2 ^ 31)) : ENNReal) * Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹
      honestCoordLaw (2 ^ 32) (fun L => priceBucket L - ENNReal.ofReal rcPar.c0) ≤
      ENNReal.ofReal ((overN : ℝ) / overD) := by
    simp_rw [rc_conv_over]
    rw [rc_card, rc_frac _ _ (by norm_num [overD])]
    exact rc_kind_all 3 runs3 glob3 Pack3 pack3_eq hP entries3 runs3_ok glob3_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [overD]) env_over
  have hcount : (Fintype.card (Fin (2 ^ 31)) : ENNReal) * Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹
      honestCoordLaw (2 ^ 32) (fun L => if ENNReal.ofReal rcPar.c0 < priceBucket L then 1 else 0) ≤
      ENNReal.ofReal ((countN : ℝ) / countD) := by
    simp_rw [rc_conv_count]
    rw [rc_card, rc_frac _ _ (by norm_num [countD])]
    exact rc_kind_all 2 runs2 glob2 Pack2 pack2_eq hP entries2 runs2_ok glob2_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [countD]) env_count
  have htail : (Fintype.card (Fin (2 ^ 31)) : ENNReal) * Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹
      honestCoordLaw (2 ^ 32) (fun L => if 80 < L.length then priceBucket L else 0) ≤
      ENNReal.ofReal ((longN : ℝ) / longD) := by
    rw [rc_card, rc_frac _ _ (by norm_num [longD])]
    exact rc_long (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [longD]) env_long
  have key := RouteC.excess_route_c honestCoordLaw honestCoordLaw_sum hcard (2 ^ 32) 80 priceBucket
    priceBucket_ne_top (fun L b R => priceBucket_insert L R b) (rcPar.c0 : ℝ) (rcPar.θ : ℝ) (rcPar.a : ℝ)
    ((mgfN : ℝ) / mgfD) (rcPar.m : ℝ) (rcPar.vv : ℝ) ((scarfN : ℝ) / scarfD)
    ((overN : ℝ) / overD) ((countN : ℝ) / countD) ((longN : ℝ) / longD)
    hθ0 ha0 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hP.m hP.vv
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    hnil hmgf hmean hsecond hK1 hover hcount htail
  exact key.trans (ENNReal.ofReal_le_ofReal rc_total_mid)

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.RouteCBank
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The low threshold through the clipped Chernoff bound plus the excess over the clip. -/
theorem rc_excess_low :
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((1 : ℝ) - 1 / 1024)) ≤
      ENNReal.ofReal ((49 : ℝ) / 100) := by
  have hP := parFacts_of_ok rcPar par_ok
  apply price_excess_of_bucket_bounds (2 ^ 32) (ENNReal.ofReal rcPar.c0) ENNReal.ofReal_ne_top
    (1 - 1 / 1024) (rcPar.a : ℝ) ((mgfN : ℝ) / mgfD) ((overN : ℝ) / overD) (49 / 100)
    (by norm_num) (by rw [rc_a]; norm_num) (by positivity) (by positivity)
  · simp_rw [rc_conv_mgf]
    rw [rc_frac _ _ (by norm_num [mgfD])]
    exact rc_kind_all 4 runs4 glob4 Pack4 pack4_eq hP entries4 runs4_ok glob4_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [mgfD]) env_mgf
  · simp_rw [rc_conv_over]
    rw [rc_frac _ _ (by norm_num [overD])]
    exact rc_kind_all 3 runs3 glob3 Pack3 pack3_eq hP entries3 runs3_ok glob3_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [overD]) env_over
  · exact rc_total_low

/-! Installed names (now proved by route C). -/

theorem excess_middle_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((99843:ℝ)/50000-1/1024)) ≤
        ENNReal.ofReal ((1174 : ℝ) / 1000000) := rc_excess_middle

theorem excess_high_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((2:ℝ)-149/62500-1/1024)) ≤
        ENNReal.ofReal ((3690879:ℝ)/3125000000) :=
  (Law.lawAvg_mono _ _ (fun W => tsub_le_tsub_left
    (ENNReal.ofReal_le_ofReal (by norm_num : (99843 : ℝ) / 50000 - 1 / 1024 ≤ 2 - 149 / 62500 - 1 / 1024)) _)).trans
    (rc_excess_middle.trans (ENNReal.ofReal_le_ofReal (by norm_num)))

theorem excess_low_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((1:ℝ)-1/1024)) ≤
        ENNReal.ofReal ((49:ℝ)/100) := rc_excess_low

/-- Large queries: the cap-777 envelope `(993/1000) y` from the high and low endpoints (as in #938). -/
theorem excess_large_certified (y : ℝ)
    (hy0 : 149/125000 ≤ y) (hy1 : y ≤ 1/2) :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal (2-2*y-1/1024)) ≤
        ENNReal.ofReal ((24771/25000)*y) := by
  let t : ℝ := (y-149/125000)/(1/2-149/125000)
  have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hy0) (by norm_num)
  have ht1 : t≤1 := (div_le_one (by norm_num : (0:ℝ)<1/2-149/125000)).2 (by linarith)
  have h := price_excess_affine (2^32) (2-149/62500-1/1024) (1-1/1024)
    (3690879/3125000000) (49/100) t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ht0 ht1 excess_high_certified excess_low_certified
  have harg : (1-t)*(2-149/62500-1/1024)+t*(1-1/1024) = 2-2*y-1/1024 := by
    dsimp [t]; ring
  rw [harg] at h
  have hgap : (24771/25000)*y-((1-t)*(3690879/3125000000)+t*(49/100)) = t*(271/50000) := by
    dsimp [t]; ring
  have hval : (1-t)*(3690879/3125000000)+t*(49/100) ≤ (24771/25000)*y := by nlinarith
  exact h.trans (ENNReal.ofReal_le_ofReal hval)

/-- Tiny queries: affine interpolation between the middle and low endpoints. -/
theorem excess_tiny_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W=>price W-ENNReal.ofReal ((249:ℝ)/125-1/1024)) ≤
        ENNReal.ofReal ((18:ℝ)/5000) := by
  have h := price_excess_affine (2^32) ((99843:ℝ)/50000-1/1024) (1-1/1024)
    (1174/1000000) (49/100) (243/49843) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) excess_middle_certified excess_low_certified
  have harg : (1-(243:ℝ)/49843)*((99843:ℝ)/50000-1/1024)+243/49843*(1-1/1024) = 249/125-1/1024 := by
    norm_num
  rw [harg] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (by norm_num))
end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Numerics.WCTPrice
open Finset ENNReal
open ClaudeWCT.Numerics.Law (lawAvg marked)
open SphincsSecurity.Concrete (uniformWordAverage)
open ClaudeWCT.Bank.WCT (WProposal price ExcessBound)
open ClaudeWCT.WCT9 (wordDigit Coord Child Rank)
open ClaudeWCT.Numerics.WCTEnvelope
theorem theta_eq : SigGolfCandidate.T3.Security.CaseC.theta = 63 / 64 := rfl
theorem price_fun_eq : price = N600.priceN wordDigit := funext price_eq
section Window
variable {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32)
include hT1 hT2
theorem wct_price_mean_law {law : (Coord → Child × Rank) → ENNReal} {κ : ENNReal} (hlaw : N600.LawOK law κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) law) T price ≤ 675 / 1000 := by
  rw [price_fun_eq]
  exact N600.law_price_mean_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit hlaw
theorem wct_price_excess_law {law : (Coord → Child × Rank) → ENNReal} {κ : ENNReal} (hlaw : N600.LawOK law κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) law) T (fun W : List WProposal => price W - 1023 / 1024) ≤
      247 / 100000 := by
  rw [price_fun_eq]
  exact N600.law_price_excess_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit w2Table_wordDigit hlaw
theorem wct_near_law {law : (Coord → Child × Rank) → ENNReal} {κ : ENNReal} (hlaw : N600.LawOK law κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) law) T (N600.nearPriceN (C := Child) wordDigit) ≤ 300 - 1 / 16 :=
  (N600.law_nearPrice_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit wfTable_wordDigit hlaw).trans
    N600.near_le_sub
theorem wct_price_mean_bound_window : uniformWordAverage T price ≤ 675 / 1000 := by
  rw [price_fun_eq]
  exact N600.uniform_price_mean_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit
theorem wct_price_mean_bound_window' : uniformWordAverage T price ≤ 94 / 100 := by
  refine (wct_price_mean_bound_window hT1 hT2).trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]
theorem wct_excessBound_window : ExcessBound T (247 / 100000) :=
  ClaudeWCT.Bank.WCT.excessBound_of_honest (wct_price_excess_law hT1 hT2 N600Cap.lawOK_honest)
end Window
abbrev wctHorizon : ℕ := 2 ^ 32
theorem wctHorizon_eq : wctHorizon = 2 ^ 32 := rfl
theorem wctHorizon_ge : 2 ^ 32 ≤ wctHorizon := wctHorizon_eq.ge
theorem wctHorizon_le : wctHorizon ≤ 2 ^ 32 := wctHorizon_eq.le
theorem wct_excessBound_forall :
    ∀ T : ℕ, 2 ^ 32 ≤ T → T ≤ 2 ^ 32 → ExcessBound T (247 / 100000) :=
  fun _ h1 h2 => wct_excessBound_window h1 h2
theorem wct_excessBound : ExcessBound wctHorizon (247 / 100000) :=
  wct_excessBound_window wctHorizon_ge wctHorizon_le
theorem wct_excessBound_2_32 : ExcessBound (2 ^ 32) (247 / 100000) :=
  wct_excessBound_window le_rfl (by norm_num)
theorem wct_excess_honest_2_32 :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) (2 ^ 32)
      (fun W : List WProposal => price W - 1023 / 1024) ≤ 247 / 100000 :=
  wct_price_excess_law le_rfl (by norm_num) N600Cap.lawOK_honest
theorem wct_excess_honest :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) wctHorizon
      (fun W : List WProposal => price W - 1023 / 1024) ≤ 247 / 100000 :=
  wct_price_excess_law wctHorizon_ge wctHorizon_le N600Cap.lawOK_honest
theorem wct_near_honest_2_32 :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) (2 ^ 32) (N600.nearPriceN (C := Child) wordDigit) ≤
      300 - 1 / 16 :=
  wct_near_law le_rfl (by norm_num) N600Cap.lawOK_honest
theorem wct_near_honest :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) wctHorizon (N600.nearPriceN (C := Child) wordDigit) ≤
      300 - 1 / 16 :=
  wct_near_law wctHorizon_ge wctHorizon_le N600Cap.lawOK_honest
end ClaudeWCT.Numerics.WCTPrice
end
-- ==== merged from ClaudeWCT_W9_T3_Proofs ====
section

namespace ClaudeWCT.W9.T3.Security
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
abbrev Requests := Request →ₒ Option Signature
def signingOracle : QueryImpl Requests (WriterT (QueryLog Requests) M) :=
  QueryImpl.withLogging fun request => liftM (sign request.cache request.message)
end ClaudeWCT.W9.T3.Security
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeGame ====
section

section
namespace ClaudeWCT.W9.T3.Security.LazyPrivate
open OracleComp OracleSpec
abbrev Interaction := SphincsSecurity.OracleWorld + Requests
end ClaudeWCT.W9.T3.Security.LazyPrivate
end
section
namespace ClaudeWCT.W9.T3.Security.RequestHop
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.RequestHop
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {State : Type}
abbrev Signer (State : Type) := Request → StateT State ProbComp (Option Signature)
noncomputable def run {α : Type} (world : Public State) (signer : Signer State)
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    ProbComp ((α × QueryLog Requests) × State) :=
  OracleComp.recOn program (fun value state => pure ((value,[]),state))
    (fun input _ ih state => match input with
      | .inl input => do
          let result ← (world input).run state
          ih result.1 result.2
      | .inr request => do
          let result ← (signer request).run state
          (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$> ih result.1 result.2) state
theorem run_pure {α : Type} (world : Public State) (signer : Signer State)
    (value : α) (state : State) : run world signer (pure value) state=pure ((value,[]),state) := rfl
theorem run_public {α : Type} (world : Public State) (signer : Signer State)
    (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp LazyPrivate.Interaction α)
    (state : State) :
    run world signer (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) state=
      (do let result ← (world input).run state; run world signer (next result.1) result.2) := rfl
theorem run_request {α : Type} (world : Public State) (signer : Signer State)
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α)
    (state : State) :
    run world signer (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) state=
      (do
        let result ← (signer request).run state
        (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$>
          run world signer (next result.1) result.2) := rfl
theorem erasure {α : Type} (world : Public State) (signer : Signer State)
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    (fun result => (result.1.1,result.2)) <$> run world signer program state=
      (simulateQ (world+signer) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [run_public,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [run_request,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          apply bind_congr
          intro result
          simpa only [Functor.map_map,Function.comp_def] using ih result.1 result.2
end ClaudeWCT.W9.T3.Security.RequestHop
end
section
namespace ClaudeWCT.W9.SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
open _root_.SiggolfT3Mac4 _root_.SiggolfT3Mac4.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev WSignature := ClaudeWCT.W9.T3.Security.Signature
noncomputable def sign (payload : Request T3Message → T3M (Option WSignature))
    (request : Request T3Message) : T3M (Option WSignature) := do
  let tag ← privateMac request.cache.region
  if tag = request.cache.tag then payload request else pure none
end ClaudeWCT.W9.SiggolfT3Mac4.Source
end
section
namespace ClaudeWCT.W9.SiggolfT3Mac4.Source
open OracleComp OracleSpec
open _root_.SiggolfT3Mac4 _root_.SiggolfT3Mac4.Source
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def corePayload (request : Request T3Message) : T3M (Option WSignature) :=
  ClaudeWCT.W9.T3.Security.signPayload (toCoreCache request.cache) request.message
theorem corePayload_nonMac (request : Request T3Message) :
    AllQueriesSatisfy (corePayload request) NonMac :=
  ClaudeWCT.W9.T3.Security.Signer.signPayload_nonMac _ _
theorem core_sign_eq (cache : _root_.SiggolfT3Mac4.Cache) (message : T3Message) :
    ClaudeWCT.W9.T3.Security.sign (toCoreCache cache) message = sign corePayload ⟨message,cache⟩ := by
  rw [ClaudeWCT.W9.T3.Security.sign_eq]
  unfold SigGolfCandidate.T3.privateMac sign _root_.SiggolfT3Mac4.Source.privateMac
  rw [privateMacKey_eq_core]
  simp only [bind_assoc,pure_bind,toCoreCache,tagRegion,regionBytes]
  apply congrArg (fun k => SigGolfCandidate.T3.privateMacKey >>= k)
  funext key
  by_cases h : macTag key (List.ofFn cache.region)=cache.tag
  · simp only [h,ne_eq,not_true_eq_false,ite_false,ite_true,corePayload,toCoreCache]
  · have he : encodeTag (macTag key (List.ofFn cache.region)) ≠ encodeTag cache.tag :=
      fun hx => h (encodeTag_injective hx)
    rw [if_pos he, if_neg h]
end ClaudeWCT.W9.SiggolfT3Mac4.Source
end
section
namespace ClaudeWCT.W9.SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal
open _root_.SiggolfT3Mac4 _root_.SiggolfT3Mac4.Source
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev CoreRequests := ClaudeWCT.W9.T3.Security.Requests
abbrev CoreInteraction := ClaudeWCT.W9.T3.Security.LazyPrivate.Interaction
theorem entry_roundtrip (request : CoreRequest) (answer : Option WSignature) :
    (⟨toCoreRequest (fromCoreRequest request),answer⟩ :
      (input : CoreRequests.Domain) × CoreRequests.Range input)=⟨request,answer⟩ := by
  exact Sigma.ext (toCoreRequest_fromCoreRequest request) HEq.rfl
def toCoreLog (log : QueryLog (Requests T3Message WSignature)) : QueryLog CoreRequests :=
  log.map fun entry => ⟨toCoreRequest entry.1,entry.2⟩
theorem toCoreLog_length (log : QueryLog (Requests T3Message WSignature)) :
    (toCoreLog log).length=log.length := by simp [toCoreLog]
noncomputable def interactionMap : QueryImpl CoreInteraction
    (OracleComp (Interaction T3Message WSignature))
  | .inl input => liftM ((Interaction T3Message WSignature).query (.inl input))
  | .inr request => liftM ((Interaction T3Message WSignature).query (.inr (fromCoreRequest request)))
noncomputable def transport {α : Type} (program : OracleComp CoreInteraction α) :
    OracleComp (Interaction T3Message WSignature) α := simulateQ interactionMap program
def restore {α State : Type}
    (result : (α × QueryLog (Requests T3Message WSignature)) × State) :
    (α × QueryLog CoreRequests) × State := ((result.1.1,toCoreLog result.1.2),result.2)
theorem run_transport {α State : Type} (world : SigGolfCandidate.T3.Security.RequestHop.Public State)
    (signer : ClaudeWCT.W9.T3.Security.RequestHop.Signer State)
    (program : OracleComp CoreInteraction α) (state : State) :
    ClaudeWCT.W9.T3.Security.RequestHop.run world signer program state =
      restore <$> Adaptive.run world (fun request => signer (toCoreRequest request))
        (transport program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [transport,simulateQ_bind,simulateQ_spec_query,interactionMap]
          rw [ClaudeWCT.W9.T3.Security.RequestHop.run_public,Adaptive.run_public,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          simp only [transport,simulateQ_bind,simulateQ_spec_query,interactionMap]
          rw [ClaudeWCT.W9.T3.Security.RequestHop.run_request,Adaptive.run_request,map_bind,
            toCoreRequest_fromCoreRequest]
          apply bind_congr
          intro head
          rw [ih]
          simp only [Functor.map_map,Function.comp_def,restore,toCoreLog,List.map_cons,
            toCoreRequest_fromCoreRequest,entry_roundtrip]
          rfl
theorem run_transport_bind {α β State : Type} (world : SigGolfCandidate.T3.Security.RequestHop.Public State)
    (signer : ClaudeWCT.W9.T3.Security.RequestHop.Signer State)
    (program : OracleComp CoreInteraction α) (state : State)
    (cont : ((α × QueryLog CoreRequests) × State) → ProbComp β) :
    ClaudeWCT.W9.T3.Security.RequestHop.run world signer program state >>= cont =
      Adaptive.run world (fun request => signer (toCoreRequest request))
        (transport program) state >>= fun result => cont (restore result) := by
  rw [run_transport,bind_map_left]
end ClaudeWCT.W9.SiggolfT3Mac4.Source
end
section
namespace ClaudeWCT.W9.T3.Security.MacGame
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.CacheAuthentication
open SigGolfCandidate.T3.Security.MacGame
open _root_.SiggolfT3Mac4 (MacKey encodeTag decodeTag tagRegion)
open _root_.SiggolfT3Mac4.Adaptive (retagRegion)
open _root_.SiggolfT3Mac4.Source (keyCoordinate toCoreCache fromCoreCache toCoreRequest fromCoreRequest)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType MacTable := macTableSampler
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
variable {State : Type}
theorem payload_no_mac (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (signPayload cache message) NonMac :=
  Signer.signPayload_nonMac cache message
noncomputable def realSigner (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (key : MacTable) : RequestHop.Signer State := fun request =>
  _root_.SiggolfT3Mac4.Adaptive.realSigner (fun _ => overhead base)
    (fun request => simulateQ base (ClaudeWCT.W9.SiggolfT3Mac4.Source.corePayload request)) key
    (fromCoreRequest request)
noncomputable def idealSigner (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (published : SigGolfCandidate.T3.Cache) : RequestHop.Signer State := fun request =>
  _root_.SiggolfT3Mac4.Adaptive.idealSigner (fun _ => overhead base)
    (fun request => simulateQ base (ClaudeWCT.W9.SiggolfT3Mac4.Source.corePayload request))
    (fromCoreCache published) (fromCoreRequest request)
theorem source_signer_eq (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (key : MacTable) (request : Request) :
    simulateQ (sourceHandler base key) (sign request.cache request.message)=realSigner base key request := by
  rw [← _root_.SiggolfT3Mac4.Source.toCoreCache_fromCoreCache request.cache,
    ClaudeWCT.W9.SiggolfT3Mac4.Source.core_sign_eq]
  unfold ClaudeWCT.W9.SiggolfT3Mac4.Source.sign _root_.SiggolfT3Mac4.Source.privateMac
  rw [_root_.SiggolfT3Mac4.Source.privateMacKey_eq_core]
  simp only [bind_assoc,pure_bind,simulateQ_bind,source_key_eq,bind_assoc,pure_bind]
  change (overhead base >>= fun _ => _)=_
  unfold realSigner _root_.SiggolfT3Mac4.Adaptive.realSigner
  apply congrArg (fun next => overhead base >>= next)
  funext ignored
  simp only [_root_.SiggolfT3Mac4.Source.toCoreCache_fromCoreCache,
    fromCoreRequest,fromCoreCache]
  split_ifs
  · exact simulate_no_mac base key _ (ClaudeWCT.W9.SiggolfT3Mac4.Source.corePayload_nonMac _)
  · rfl
theorem authentication_hop {α β : Type} (world : SigGolfCandidate.T3.Security.RequestHop.Public State)
    (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp)) (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α) (limit : Nat) (state : State)
    (cont : ((α × QueryLog Requests) × State) → ProbComp β) (event : β → Prop)
    (hlong : ∀ result,limit < result.1.2.length → Pr[event | cont result]=0) :
    Pr[event | ($ᵗ MacTable : ProbComp _) >>= fun key =>
      RequestHop.run world (realSigner base (retag key published)) program state >>= cont] ≤
      Pr[event | RequestHop.run world (idealSigner base published) program state >>= cont]+
        limit*((2 : ENNReal)^184)⁻¹ := by
  have hr := @ClaudeWCT.W9.SiggolfT3Mac4.Source.run_transport_bind α β State
  simp only [hr]
  simp only [realSigner,idealSigner,retag,_root_.SiggolfT3Mac4.Source.fromCoreRequest_toCoreRequest]
  exact _root_.SiggolfT3Mac4.Adaptive.authentication_hop world (fun _ => overhead base)
    (fun request => simulateQ base (ClaudeWCT.W9.SiggolfT3Mac4.Source.corePayload request))
    (fromCoreCache published) (ClaudeWCT.W9.SiggolfT3Mac4.Source.transport program) limit state
    (fun result => cont (ClaudeWCT.W9.SiggolfT3Mac4.Source.restore result)) event
    (fun result hlong' => hlong _ (by simpa only [ClaudeWCT.W9.SiggolfT3Mac4.Source.restore,
      ClaudeWCT.W9.SiggolfT3Mac4.Source.toCoreLog_length] using hlong'))
end ClaudeWCT.W9.T3.Security.MacGame
end
section
namespace ClaudeWCT.W9.T3.Security.ProposalOverflow
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def logFragment : (input : LazyPrivate.Interaction.Domain) →
    LazyPrivate.Interaction.Range input → QueryLog Requests
  | .inl _, _ => []
  | .inr request, response => [⟨request,response⟩]
def logging : QueryImpl LazyPrivate.Interaction
    (WriterT (QueryLog Requests) (OracleComp LazyPrivate.Interaction)) :=
  QueryImpl.withTraceAppend (fun input => LazyPrivate.Interaction.query input) logFragment
def logged {Result : Type} (program : OracleComp LazyPrivate.Interaction Result) :
    OracleComp LazyPrivate.Interaction (Result × QueryLog Requests) :=
  (simulateQ logging program).run
theorem logged_pure {Result : Type} (value : Result) : logged (pure value) = pure (value,[]) := rfl
theorem logged_query_bind {Result : Type} (input : LazyPrivate.Interaction.Domain)
    (next : LazyPrivate.Interaction.Range input → OracleComp LazyPrivate.Interaction Result) :
    logged (LazyPrivate.Interaction.query input >>= next) = (do
      let response ← LazyPrivate.Interaction.query input
      let result ← logged (next response)
      pure (result.1, logFragment input response ++ result.2)) := by
  simp [logged, logging, QueryImpl.withTraceAppend_apply]
end ClaudeWCT.W9.T3.Security.ProposalOverflow
end
section
namespace ClaudeWCT.W9.T3.Security.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.FullGame
open SphincsSecurity (OracleWorld romImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq _root_.SiggolfT3Mac4.Cache := Classical.decEq _
noncomputable local instance : DecidableEq Region := Classical.decEq _
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
noncomputable def authenticatedSign (published : SigGolfCandidate.T3.Cache) (request : Request) :
    M (Option Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache=published then signPayload request.cache request.message else pure none
noncomputable def loggedWith {α : Type} (signer : Request → M (Option Signature))
    (program : OracleComp LazyPrivate.Interaction α) : M (α × QueryLog Requests) :=
  (simulateQ ((fun input => liftM (forwardWorld input) :
      QueryImpl OracleWorld (WriterT (QueryLog Requests) M))+
      (QueryImpl.withLogging (fun request => signer request) :
        QueryImpl Requests (WriterT (QueryLog Requests) M))) program).run
theorem loggedWith_pure {α : Type} (signer : Request → M (Option Signature)) (value : α) :
    loggedWith signer (pure value)=pure (value,[]) := rfl
theorem loggedWith_world {α : Type} (signer : Request → M (Option Signature))
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp LazyPrivate.Interaction α) :
    loggedWith signer (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next)=
      (forwardWorld input >>= fun answer => loggedWith signer (next answer)) := by
  unfold loggedWith
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inl]
  simp only [WriterT.run_bind',WriterT.run_liftM,bind_map_left]
  apply bind_congr
  intro answer
  change id <$> _ = _
  rw [id_map]
theorem loggedWith_request {α : Type} (signer : Request → M (Option Signature))
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    loggedWith signer (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next)=
      (signer request >>= fun answer =>
        (fun result => (result.1,⟨request,answer⟩::result.2)) <$> loggedWith signer (next answer)) := by
  unfold loggedWith
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inr]
  simp
theorem loggedWith_interpretation {State α : Type}
    (handler : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (signer : Request → M (Option Signature))
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    (simulateQ handler (loggedWith signer program)).run state=
      RequestHop.run (fun input => handler (.inl input))
        (fun request => simulateQ handler (signer request)) program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [loggedWith_pure,RequestHop.run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [loggedWith_world,RequestHop.run_public,simulateQ_bind,StateT.run_bind]
          simp only [forwardWorld,simulateQ_spec_query]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [loggedWith_request,RequestHop.run_request,simulateQ_bind,StateT.run_bind]
          apply bind_congr
          intro result
          simp only [simulateQ_map,StateT.run_map,ih]
theorem authenticatedSign_interpretation (other : OtherTable) (mac : MacTable)
    (published : SigGolfCandidate.T3.Cache) (request : Request) :
    simulateQ (SigGolfCandidate.T3.Security.MacGame.sourceHandler (baseHandler other) mac)
      (authenticatedSign published request)=
      MacGame.idealSigner (baseHandler other) published request := by
  classical
  unfold authenticatedSign privateMac
  simp only [bind_assoc,pure_bind,simulateQ_bind,SigGolfCandidate.T3.Security.MacGame.source_key_eq,
    bind_assoc,pure_bind]
  unfold MacGame.idealSigner _root_.SiggolfT3Mac4.Adaptive.idealSigner
  apply congrArg (fun next => SigGolfCandidate.T3.Security.MacGame.overhead (baseHandler other) >>= next)
  funext ignored
  simp only [_root_.SiggolfT3Mac4.Source.fromCoreRequest]
  have he : _root_.SiggolfT3Mac4.Source.fromCoreCache request.cache =
      _root_.SiggolfT3Mac4.Source.fromCoreCache published ↔ request.cache=published :=
    _root_.SiggolfT3Mac4.Source.coreCacheEquiv.symm.injective.eq_iff
  simp only [he]
  split_ifs
  · simpa only [ClaudeWCT.W9.SiggolfT3Mac4.Source.corePayload,
      _root_.SiggolfT3Mac4.Source.toCoreCache_fromCoreCache] using
      SigGolfCandidate.T3.Security.MacGame.simulate_no_mac (baseHandler other) mac _
        (MacGame.payload_no_mac request.cache request.message)
  · rfl
end ClaudeWCT.W9.T3.Security.FullGame
end

namespace ClaudeWCT.W9.T3.Security.PairedOuter
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest ClaudeWCT.WCT9
open _root_.SiggolfT3Mac4.Source (NonMac non_mac_tweak)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem privatePair_nonMac (tag lay tree position index : Nat) (h : tag%256≠14) :
    AllQueriesSatisfy (privatePair tag lay tree position index) NonMac := by
  unfold privatePair
  apply SourceQueries.bind_allowed
  · exact (allQueriesSatisfy_query_iff _ _).mpr ⟨non_mac_tweak _ _ _ _ _ h 0,non_mac_tweak _ _ _ _ _ h 1⟩
  · intro _;exact SourceQueries.pure_allowed _ _

theorem tail_nonMac : SharedQueries.TailAllowed NonMac where
  chainStep := fun _ _ _ _ _ _=>SourceQueries.shortHash_allowed _ (fun _=>trivial) _
  chainStepW := fun _ _ _ _ _ _=>SourceQueries.shortHash_allowed _ (fun _=>trivial) _
  leaf := fun _ _ _ _=>SourceQueries.shortHash_allowed _ (fun _=>trivial) _
  node := fun _ _ _ _ _ _=>Signer.lowerNodeHash_allowed_of_public _ (fun _=>trivial) _ _ _ _ _
  seed := fun _ _ _=>privatePair_nonMac _ _ _ _ _ (by decide)
  encoding := fun lay _ _ msg _=>by
    cases msg <;> exact SourceQueries.shortHash_allowed _ (fun _=>trivial) _
  top := _root_.SiggolfT3Mac4.Source.Payload.signTop_allowed

theorem forest_nonMac : ClaudeWCT.Bank.Paired.ForestAllowed NonMac where
  coefs := fun _ _=>Signer.ftsCoefs_allowed _
    (fun lay tree position index=>⟨non_mac_tweak 8 lay tree position index (by decide) 0,
      non_mac_tweak 8 lay tree position index (by decide) 1⟩) _ _
  child := Signer.buildChildH_allowed _ (fun _=>trivial)
  node := Signer.sharedNode_allowed _ (fun _=>trivial)

theorem signFromOutput_nonMac (cache : SigGolfCandidate.T3.Cache) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) :
    AllQueriesSatisfy (signFromOutput cache rho counter output) NonMac :=
  SharedQueries.signFromOutput_allowed _ tail_nonMac
    (ClaudeWCT.Bank.Paired.forest_allowed _ forest_nonMac) _ _ _ _

theorem digestSearch_nonMac (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (sharedDigestSearch rho message counter fuel) NonMac := by
  induction fuel generalizing counter with
  | zero=>exact SourceQueries.pure_allowed _ _
  | succ fuel ih=>
    unfold sharedDigestSearch
    apply SourceQueries.bind_allowed _ (SourceQueries.publicHash_allowed _ (fun _=>trivial) _)
    intro output
    split
    · exact SourceQueries.pure_allowed _ _
    · exact ih _

theorem signPayload_nonMac (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (SigGolfCandidate.Research.SharedForest.signPayload cache message) NonMac := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  apply SourceQueries.bind_allowed _ (SourceQueries.privateNonce_allowed _ _root_.SiggolfT3Mac4.Source.nonce_coordinate_other _)
  intro rho
  apply SourceQueries.bind_allowed _ (digestSearch_nonMac ..)
  intro found
  rcases found with _|⟨counter,output⟩
  · exact SourceQueries.pure_allowed _ _
  · apply SourceQueries.bind_allowed _ (signFromOutput_nonMac ..)
    intro signed
    cases signed <;> exact SourceQueries.pure_allowed _ _
end ClaudeWCT.W9.T3.Security.PairedOuter

namespace ClaudeWCT.W9.T3.Security.PairedOuter
open OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
abbrev Signature := SigGolfCandidate.Research.SharedForest.Signature
abbrev Requests := Request →ₒ Option Signature
abbrev signPayload := SigGolfCandidate.Research.SharedForest.signPayload
abbrev sign := SigGolfCandidate.Research.SharedForest.sign
end ClaudeWCT.W9.T3.Security.PairedOuter
section
namespace ClaudeWCT.W9.T3.Security.PairedOuter.LazyPrivate
open OracleComp OracleSpec
abbrev Interaction := SphincsSecurity.OracleWorld + Requests
end ClaudeWCT.W9.T3.Security.PairedOuter.LazyPrivate
end
section
namespace ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.RequestHop
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {State : Type}
abbrev Signer (State : Type) := Request → StateT State ProbComp (Option Signature)
noncomputable def run {α : Type} (world : Public State) (signer : Signer State)
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    ProbComp ((α × QueryLog Requests) × State) :=
  OracleComp.recOn program (fun value state => pure ((value,[]),state))
    (fun input _ ih state => match input with
      | .inl input => do
          let result ← (world input).run state
          ih result.1 result.2
      | .inr request => do
          let result ← (signer request).run state
          (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$> ih result.1 result.2) state
theorem run_pure {α : Type} (world : Public State) (signer : Signer State)
    (value : α) (state : State) : run world signer (pure value) state=pure ((value,[]),state) := rfl
theorem run_public {α : Type} (world : Public State) (signer : Signer State)
    (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp LazyPrivate.Interaction α)
    (state : State) :
    run world signer (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) state=
      (do let result ← (world input).run state; run world signer (next result.1) result.2) := rfl
theorem run_request {α : Type} (world : Public State) (signer : Signer State)
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α)
    (state : State) :
    run world signer (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) state=
      (do
        let result ← (signer request).run state
        (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$>
          run world signer (next result.1) result.2) := rfl
theorem erasure {α : Type} (world : Public State) (signer : Signer State)
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    (fun result => (result.1.1,result.2)) <$> run world signer program state=
      (simulateQ (world+signer) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [run_public,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [run_request,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          apply bind_congr
          intro result
          simpa only [Functor.map_map,Function.comp_def] using ih result.1 result.2
end ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop
end
section
namespace ClaudeWCT.W9.PairedMac.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
open _root_.SiggolfT3Mac4 _root_.SiggolfT3Mac4.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev WSignature := ClaudeWCT.W9.T3.Security.PairedOuter.Signature
noncomputable def sign (payload : Request T3Message → T3M (Option WSignature))
    (request : Request T3Message) : T3M (Option WSignature) := do
  let tag ← privateMac request.cache.region
  if tag = request.cache.tag then payload request else pure none
end ClaudeWCT.W9.PairedMac.Source
end
section
namespace ClaudeWCT.W9.PairedMac.Source
open OracleComp OracleSpec
open _root_.SiggolfT3Mac4 _root_.SiggolfT3Mac4.Source
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def corePayload (request : Request T3Message) : T3M (Option WSignature) :=
  SigGolfCandidate.Research.SharedForest.signPayload (toCoreCache request.cache) request.message
theorem corePayload_nonMac (request : Request T3Message) :
    AllQueriesSatisfy (corePayload request) NonMac :=
  ClaudeWCT.W9.T3.Security.PairedOuter.signPayload_nonMac _ _
theorem core_sign_eq (cache : _root_.SiggolfT3Mac4.Cache) (message : T3Message) :
    SigGolfCandidate.Research.SharedForest.sign (toCoreCache cache) message = sign corePayload ⟨message,cache⟩ := by
  unfold SigGolfCandidate.Research.SharedForest.sign
  unfold SigGolfCandidate.T3.privateMac sign _root_.SiggolfT3Mac4.Source.privateMac
  rw [privateMacKey_eq_core]
  simp only [bind_assoc,pure_bind,toCoreCache,tagRegion,regionBytes]
  apply congrArg (fun k => SigGolfCandidate.T3.privateMacKey >>= k)
  funext key
  by_cases h : macTag key (List.ofFn cache.region)=cache.tag
  · simp only [h,ne_eq,not_true_eq_false,ite_false,ite_true,corePayload,toCoreCache]
  · have he : encodeTag (macTag key (List.ofFn cache.region)) ≠ encodeTag cache.tag :=
      fun hx => h (encodeTag_injective hx)
    rw [if_pos he, if_neg h]
end ClaudeWCT.W9.PairedMac.Source
end
section
namespace ClaudeWCT.W9.PairedMac.Source
open OracleComp OracleSpec ENNReal
open _root_.SiggolfT3Mac4 _root_.SiggolfT3Mac4.Source
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev CoreRequests := ClaudeWCT.W9.T3.Security.PairedOuter.Requests
abbrev CoreInteraction := ClaudeWCT.W9.T3.Security.PairedOuter.LazyPrivate.Interaction
theorem entry_roundtrip (request : CoreRequest) (answer : Option WSignature) :
    (⟨toCoreRequest (fromCoreRequest request),answer⟩ :
      (input : CoreRequests.Domain) × CoreRequests.Range input)=⟨request,answer⟩ := by
  exact Sigma.ext (toCoreRequest_fromCoreRequest request) HEq.rfl
def toCoreLog (log : QueryLog (Requests T3Message WSignature)) : QueryLog CoreRequests :=
  log.map fun entry => ⟨toCoreRequest entry.1,entry.2⟩
theorem toCoreLog_length (log : QueryLog (Requests T3Message WSignature)) :
    (toCoreLog log).length=log.length := by simp [toCoreLog]
noncomputable def interactionMap : QueryImpl CoreInteraction
    (OracleComp (Interaction T3Message WSignature))
  | .inl input => liftM ((Interaction T3Message WSignature).query (.inl input))
  | .inr request => liftM ((Interaction T3Message WSignature).query (.inr (fromCoreRequest request)))
noncomputable def transport {α : Type} (program : OracleComp CoreInteraction α) :
    OracleComp (Interaction T3Message WSignature) α := simulateQ interactionMap program
def restore {α State : Type}
    (result : (α × QueryLog (Requests T3Message WSignature)) × State) :
    (α × QueryLog CoreRequests) × State := ((result.1.1,toCoreLog result.1.2),result.2)
theorem run_transport {α State : Type} (world : SigGolfCandidate.T3.Security.RequestHop.Public State)
    (signer : ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.Signer State)
    (program : OracleComp CoreInteraction α) (state : State) :
    ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run world signer program state =
      restore <$> Adaptive.run world (fun request => signer (toCoreRequest request))
        (transport program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [transport,simulateQ_bind,simulateQ_spec_query,interactionMap]
          rw [ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run_public,Adaptive.run_public,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          simp only [transport,simulateQ_bind,simulateQ_spec_query,interactionMap]
          rw [ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run_request,Adaptive.run_request,map_bind,
            toCoreRequest_fromCoreRequest]
          apply bind_congr
          intro head
          rw [ih]
          simp only [Functor.map_map,Function.comp_def,restore,toCoreLog,List.map_cons,
            toCoreRequest_fromCoreRequest,entry_roundtrip]
          rfl
theorem run_transport_bind {α β State : Type} (world : SigGolfCandidate.T3.Security.RequestHop.Public State)
    (signer : ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.Signer State)
    (program : OracleComp CoreInteraction α) (state : State)
    (cont : ((α × QueryLog CoreRequests) × State) → ProbComp β) :
    ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run world signer program state >>= cont =
      Adaptive.run world (fun request => signer (toCoreRequest request))
        (transport program) state >>= fun result => cont (restore result) := by
  rw [run_transport,bind_map_left]
end ClaudeWCT.W9.PairedMac.Source
end
section
namespace ClaudeWCT.W9.T3.Security.PairedOuter.MacGame
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.CacheAuthentication
open SigGolfCandidate.T3.Security.MacGame
open _root_.SiggolfT3Mac4 (MacKey encodeTag decodeTag tagRegion)
open _root_.SiggolfT3Mac4.Adaptive (retagRegion)
open _root_.SiggolfT3Mac4.Source (keyCoordinate toCoreCache fromCoreCache toCoreRequest fromCoreRequest)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType MacTable := macTableSampler
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
variable {State : Type}
theorem payload_no_mac (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (signPayload cache message) NonMac :=
  ClaudeWCT.W9.T3.Security.PairedOuter.signPayload_nonMac cache message
noncomputable def realSigner (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (key : MacTable) : RequestHop.Signer State := fun request =>
  _root_.SiggolfT3Mac4.Adaptive.realSigner (fun _ => overhead base)
    (fun request => simulateQ base (ClaudeWCT.W9.PairedMac.Source.corePayload request)) key
    (fromCoreRequest request)
noncomputable def idealSigner (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (published : SigGolfCandidate.T3.Cache) : RequestHop.Signer State := fun request =>
  _root_.SiggolfT3Mac4.Adaptive.idealSigner (fun _ => overhead base)
    (fun request => simulateQ base (ClaudeWCT.W9.PairedMac.Source.corePayload request))
    (fromCoreCache published) (fromCoreRequest request)
theorem source_signer_eq (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (key : MacTable) (request : Request) :
    simulateQ (sourceHandler base key) (sign request.cache request.message)=realSigner base key request := by
  change simulateQ (sourceHandler base key) (SigGolfCandidate.Research.SharedForest.sign request.cache request.message)=_
  rw [← _root_.SiggolfT3Mac4.Source.toCoreCache_fromCoreCache request.cache,
    ClaudeWCT.W9.PairedMac.Source.core_sign_eq]
  unfold ClaudeWCT.W9.PairedMac.Source.sign _root_.SiggolfT3Mac4.Source.privateMac
  rw [_root_.SiggolfT3Mac4.Source.privateMacKey_eq_core]
  simp only [bind_assoc,pure_bind,simulateQ_bind,source_key_eq,bind_assoc,pure_bind]
  change (overhead base >>= fun _ => _)=_
  unfold realSigner _root_.SiggolfT3Mac4.Adaptive.realSigner
  apply congrArg (fun next => overhead base >>= next)
  funext ignored
  simp only [_root_.SiggolfT3Mac4.Source.toCoreCache_fromCoreCache,
    fromCoreRequest,fromCoreCache]
  split_ifs
  · exact simulate_no_mac base key _ (ClaudeWCT.W9.PairedMac.Source.corePayload_nonMac _)
  · rfl
theorem authentication_hop {α β : Type} (world : SigGolfCandidate.T3.Security.RequestHop.Public State)
    (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp)) (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α) (limit : Nat) (state : State)
    (cont : ((α × QueryLog Requests) × State) → ProbComp β) (event : β → Prop)
    (hlong : ∀ result,limit < result.1.2.length → Pr[event | cont result]=0) :
    Pr[event | ($ᵗ MacTable : ProbComp _) >>= fun key =>
      RequestHop.run world (realSigner base (retag key published)) program state >>= cont] ≤
      Pr[event | RequestHop.run world (idealSigner base published) program state >>= cont]+
        limit*((2 : ENNReal)^184)⁻¹ := by
  have hr := @ClaudeWCT.W9.PairedMac.Source.run_transport_bind α β State
  simp only [hr]
  simp only [realSigner,idealSigner,retag,_root_.SiggolfT3Mac4.Source.fromCoreRequest_toCoreRequest]
  exact _root_.SiggolfT3Mac4.Adaptive.authentication_hop world (fun _ => overhead base)
    (fun request => simulateQ base (ClaudeWCT.W9.PairedMac.Source.corePayload request))
    (fromCoreCache published) (ClaudeWCT.W9.PairedMac.Source.transport program) limit state
    (fun result => cont (ClaudeWCT.W9.PairedMac.Source.restore result)) event
    (fun result hlong' => hlong _ (by simpa only [ClaudeWCT.W9.PairedMac.Source.restore,
      ClaudeWCT.W9.PairedMac.Source.toCoreLog_length] using hlong'))
end ClaudeWCT.W9.T3.Security.PairedOuter.MacGame
end
section
namespace ClaudeWCT.W9.T3.Security.PairedOuter.ProposalOverflow
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def logFragment : (input : LazyPrivate.Interaction.Domain) →
    LazyPrivate.Interaction.Range input → QueryLog Requests
  | .inl _, _ => []
  | .inr request, response => [⟨request,response⟩]
def logging : QueryImpl LazyPrivate.Interaction
    (WriterT (QueryLog Requests) (OracleComp LazyPrivate.Interaction)) :=
  QueryImpl.withTraceAppend (fun input => LazyPrivate.Interaction.query input) logFragment
def logged {Result : Type} (program : OracleComp LazyPrivate.Interaction Result) :
    OracleComp LazyPrivate.Interaction (Result × QueryLog Requests) :=
  (simulateQ logging program).run
theorem logged_pure {Result : Type} (value : Result) : logged (pure value) = pure (value,[]) := rfl
theorem logged_query_bind {Result : Type} (input : LazyPrivate.Interaction.Domain)
    (next : LazyPrivate.Interaction.Range input → OracleComp LazyPrivate.Interaction Result) :
    logged (LazyPrivate.Interaction.query input >>= next) = (do
      let response ← LazyPrivate.Interaction.query input
      let result ← logged (next response)
      pure (result.1, logFragment input response ++ result.2)) := by
  simp [logged, logging, QueryImpl.withTraceAppend_apply]
end ClaudeWCT.W9.T3.Security.PairedOuter.ProposalOverflow
end
section
namespace ClaudeWCT.W9.T3.Security.PairedOuter.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.FullGame
open SphincsSecurity (OracleWorld romImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq _root_.SiggolfT3Mac4.Cache := Classical.decEq _
noncomputable local instance : DecidableEq Region := Classical.decEq _
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
noncomputable def authenticatedSign (published : SigGolfCandidate.T3.Cache) (request : Request) :
    M (Option Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache=published then signPayload request.cache request.message else pure none
noncomputable def loggedWith {α : Type} (signer : Request → M (Option Signature))
    (program : OracleComp LazyPrivate.Interaction α) : M (α × QueryLog Requests) :=
  (simulateQ ((fun input => liftM (forwardWorld input) :
      QueryImpl OracleWorld (WriterT (QueryLog Requests) M))+
      (QueryImpl.withLogging (fun request => signer request) :
        QueryImpl Requests (WriterT (QueryLog Requests) M))) program).run
theorem loggedWith_pure {α : Type} (signer : Request → M (Option Signature)) (value : α) :
    loggedWith signer (pure value)=pure (value,[]) := rfl
theorem loggedWith_world {α : Type} (signer : Request → M (Option Signature))
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp LazyPrivate.Interaction α) :
    loggedWith signer (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next)=
      (forwardWorld input >>= fun answer => loggedWith signer (next answer)) := by
  unfold loggedWith
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inl]
  simp only [WriterT.run_bind',WriterT.run_liftM,bind_map_left]
  apply bind_congr
  intro answer
  change id <$> _ = _
  rw [id_map]
theorem loggedWith_request {α : Type} (signer : Request → M (Option Signature))
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    loggedWith signer (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next)=
      (signer request >>= fun answer =>
        (fun result => (result.1,⟨request,answer⟩::result.2)) <$> loggedWith signer (next answer)) := by
  unfold loggedWith
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inr]
  simp
theorem loggedWith_interpretation {State α : Type}
    (handler : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (signer : Request → M (Option Signature))
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    (simulateQ handler (loggedWith signer program)).run state=
      RequestHop.run (fun input => handler (.inl input))
        (fun request => simulateQ handler (signer request)) program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [loggedWith_pure,RequestHop.run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [loggedWith_world,RequestHop.run_public,simulateQ_bind,StateT.run_bind]
          simp only [forwardWorld,simulateQ_spec_query]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [loggedWith_request,RequestHop.run_request,simulateQ_bind,StateT.run_bind]
          apply bind_congr
          intro result
          simp only [simulateQ_map,StateT.run_map,ih]
theorem authenticatedSign_interpretation (other : OtherTable) (mac : MacTable)
    (published : SigGolfCandidate.T3.Cache) (request : Request) :
    simulateQ (SigGolfCandidate.T3.Security.MacGame.sourceHandler (baseHandler other) mac)
      (authenticatedSign published request)=
      MacGame.idealSigner (baseHandler other) published request := by
  classical
  unfold authenticatedSign privateMac
  simp only [bind_assoc,pure_bind,simulateQ_bind,SigGolfCandidate.T3.Security.MacGame.source_key_eq,
    bind_assoc,pure_bind]
  unfold MacGame.idealSigner _root_.SiggolfT3Mac4.Adaptive.idealSigner
  apply congrArg (fun next => SigGolfCandidate.T3.Security.MacGame.overhead (baseHandler other) >>= next)
  funext ignored
  simp only [_root_.SiggolfT3Mac4.Source.fromCoreRequest]
  have he : _root_.SiggolfT3Mac4.Source.fromCoreCache request.cache =
      _root_.SiggolfT3Mac4.Source.fromCoreCache published ↔ request.cache=published :=
    _root_.SiggolfT3Mac4.Source.coreCacheEquiv.symm.injective.eq_iff
  simp only [he]
  split_ifs
  · simpa only [ClaudeWCT.W9.PairedMac.Source.corePayload,
      _root_.SiggolfT3Mac4.Source.toCoreCache_fromCoreCache] using
      SigGolfCandidate.T3.Security.MacGame.simulate_no_mac (baseHandler other) mac _
        (MacGame.payload_no_mac request.cache request.message)
  · rfl
end ClaudeWCT.W9.T3.Security.PairedOuter.FullGame
end
end
-- ==== merged from T3M_SigCodec ====
section

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length)
def digNat (ds : List Digest) : Nat := readLE (ds.flatMap (bytesLE 16))
theorem digNat_nil : digNat [] = 0 := rfl
theorem digNat_cons (d : Digest) (ds : List Digest) :
    digNat (d :: ds) = d.toNat + 2 ^ 128 * digNat ds := by
  unfold digNat
  rw [List.flatMap_cons, readLE_append, readLE_bytesLE, bytesLE_length]
  norm_num
theorem digNat_lt (ds : List Digest) : digNat ds < 2 ^ (128 * ds.length) := by
  induction ds with
  | nil => simp [digNat_nil]
  | cons d ds ih =>
    rw [digNat_cons, List.length_cons, show 128 * (ds.length + 1) = 128 + 128 * ds.length by ring,
      pow_add]
    have := d.isLt
    nlinarith
theorem digNat_digit (ds : List Digest) (k : Nat) :
    digNat ds / 2 ^ (128 * k) % 2 ^ 128 = (ds.getD k 0).toNat := by
  induction ds generalizing k with
  | nil => simp [digNat_nil]
  | cons d ds ih =>
    have hd := d.isLt
    rcases k with _ | k
    · rw [digNat_cons]; simp; omega
    · rw [digNat_cons, show 128 * (k + 1) = 128 + 128 * k by ring, pow_add, ← Nat.div_div_eq_div_mul,
        show (d.toNat + 2 ^ 128 * digNat ds) / 2 ^ 128 = digNat ds by
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hd, Nat.zero_add], ih]
      simp
theorem digNat_eq_of_digits : ∀ (ds : List Digest) (B : Nat), B < 2 ^ (128 * ds.length) →
    (∀ k < ds.length, (ds.getD k 0).toNat = B / 2 ^ (128 * k) % 2 ^ 128) → digNat ds = B
  | [], B, hB, _ => by simp at hB; simp [digNat_nil, hB]
  | d :: ds, B, hB, h => by
    rw [digNat_cons]
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero, Nat.mul_zero, pow_zero, Nat.div_one] at h0
    have hB' : B / 2 ^ 128 < 2 ^ (128 * ds.length) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      simpa [show 128 * (ds.length + 1) = 128 * ds.length + 128 by ring] using hB
    have hrest : ∀ k < ds.length, (ds.getD k 0).toNat = B / 2 ^ 128 / 2 ^ (128 * k) % 2 ^ 128 := by
      intro k hk
      have := h (k + 1) (by simp; omega)
      rw [List.getD_cons_succ] at this
      rw [this, show 128 * (k + 1) = 128 + 128 * k by ring, pow_add, Nat.div_div_eq_div_mul]
    rw [digNat_eq_of_digits ds (B / 2 ^ 128) hB' hrest]
    omega
def sigDigests (s : Signature) : List Digest :=
  [s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof ++
    (List.ofFn fun lay : Layer => List.ofFn (s.layers lay).values ++ List.ofFn (s.layers lay).path).flatten
theorem ofFn_four {α : Type} (f : Fin 4 → α) : List.ofFn f = [f 0, f 1, f 2, f 3] := by
  simp [List.ofFn_succ]
theorem sigDigests_eq (s : Signature) : sigDigests s =
    [s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof ++
      ((List.ofFn (s.layers 0).values ++ List.ofFn (s.layers 0).path) ++
      ((List.ofFn (s.layers 1).values ++ List.ofFn (s.layers 1).path) ++
      ((List.ofFn (s.layers 2).values ++ List.ofFn (s.layers 2).path) ++
      (List.ofFn (s.layers 3).values ++ List.ofFn (s.layers 3).path)))) := by
  unfold sigDigests
  rw [ofFn_four]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
theorem serialize_eq (s : Signature) : serialize s = (sigDigests s).flatMap (bytesLE 16) := by
  rw [sigDigests_eq]
  unfold serialize serializeLayer
  rw [ofFn_four]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil]

/-- Machine slot of layer `lay`'s first value (campaign T51: the 51 top values start at slot 140, so the top ends at
slot 190 as in #938; lower layers unchanged). -/
def layIdx (lay : Layer) : Nat := (![140, 203, 253, 302] : Layer → Nat) lay
section getD
theorem getD_append_left' {l₁ l₂ : List Digest} {k : Nat} (h : k < l₁.length) :
    (l₁ ++ l₂).getD k 0 = l₁.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_append_right' {l₁ l₂ : List Digest} {k : Nat} (h : l₁.length ≤ k) :
    (l₁ ++ l₂).getD k 0 = l₂.getD (k - l₁.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]
theorem getD_ofFn' {n : Nat} (f : Fin n → Digest) (i : Nat) (hi : i < n) :
    (List.ofFn f).getD i 0 = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]
theorem chainCount_0 : chainCount 0 = 51 := rfl
theorem chainCount_1 : chainCount 1 = 43 := rfl
theorem chainCount_2 : chainCount 2 = 43 := rfl
theorem chainCount_3 : chainCount 3 = 43 := rfl
theorem height_0 : height 0 = 12 := rfl
theorem height_1 : height 1 = 7 := rfl
theorem height_2 : height 2 = 6 := rfl
theorem height_3 : height 3 = 6 := rfl
def layerList (s : Signature) (lay : Layer) : List Digest :=
  List.ofFn (s.layers lay).values ++ List.ofFn (s.layers lay).path
variable (s : Signature)
theorem length_layerList (lay : Layer) : (layerList s lay).length = chainCount lay + height lay := by
  simp only [layerList, List.length_append, List.length_ofFn]
theorem sigDigests_rho : (sigDigests s).getD 0 0 = s.rho := by
  rw [sigDigests_eq]; rfl
theorem sigDigests_secret (i : Nat) (hi : i < 21) : (sigDigests s).getD (1 + i) 0 = s.secrets ⟨i, hi⟩ := by
  have h1 : 1 + i < ([s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof).length := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  have h2 : 1 + i < ([s.rho] ++ List.ofFn s.secrets).length := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  rw [sigDigests_eq, getD_append_left' h1, getD_append_left' h2,
    getD_append_right' (by simp only [List.length_singleton]; omega), List.length_singleton,
    Nat.add_sub_cancel_left, getD_ofFn']
theorem sigDigests_proof (j : Nat) (hj : j < 115) : (sigDigests s).getD (22 + j) 0 = s.proof ⟨j, hj⟩ := by
  have h1 : 22 + j < ([s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof).length := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  have h2 : ([s.rho] ++ List.ofFn s.secrets).length ≤ 22 + j := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  rw [sigDigests_eq, getD_append_left' h1, getD_append_right' h2]
  simp only [List.length_append, List.length_singleton, List.length_ofFn]
  rw [show 22 + j - (1 + 21) = j by omega, getD_ofFn']
theorem sigDigests_tail (k : Nat) (hk : 137 ≤ k) : (sigDigests s).getD k 0 =
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3))).getD (k - 137) 0 := by
  have h1 : ([s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof).length ≤ k := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  rw [sigDigests_eq, getD_append_right' h1]
  simp only [List.length_append, List.length_singleton, List.length_ofFn]
  rfl

end getD
def sigDig (b : Bytes 5616) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
def sigDec (b : Bytes 5616) : Signature where
  rho := sigDig b 0
  secrets := fun i => sigDig b (1 + i.val)
  proof := fun j => sigDig b (22 + j.val)
  layers := fun lay => ⟨fun i => sigDig b (layIdx lay + i.val), fun j => sigDig b (layIdx lay + (chainCount lay + j.val))⟩
theorem pow_5728 : (2 : Nat) ^ (8 * 5616) = 2 ^ (128 * 351) := congrArg (fun n => 2 ^ n) rfl
def sigB (s : Signature) : Bytes 5616 := BitVec.ofNat _ (readLE (serialize s))
set_option exponentiation.threshold 50000 in
theorem sigDig_toNat (b : Bytes 5616) (k : Nat) : (sigDig b k).toNat = b.toNat / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem layerList_sigDec (b : Bytes 5616) (lay : Layer) (i : Nat) (hi : i < chainCount lay + height lay) :
    (layerList (sigDec b) lay).getD i 0 = sigDig b (layIdx lay + i) := by
  unfold layerList
  by_cases hc : i < chainCount lay
  · rw [getD_append_left' (by simpa using hc), getD_ofFn' _ i hc]; rfl
  · rw [getD_append_right' (by simp; omega), List.length_ofFn, getD_ofFn' _ (i - chainCount lay) (by omega)]
    show sigDig b (layIdx lay + (chainCount lay + (i - chainCount lay))) = _
    rw [show chainCount lay + (i - chainCount lay) = i by omega]

set_option exponentiation.threshold 50000 in
theorem sigDig_lo (b : Bytes 5616) (k : Nat) : (sigDig b k).extractLsb' 0 64 = b.extractLsb' (64 * (2 * k)) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  rw [show 64 * (2 * k) = 128 * k by ring, Nat.mod_mod_of_dvd _ (by norm_num)]
theorem sigDig_hi (b : Bytes 5616) (k : Nat) :
    (sigDig b k).extractLsb' 64 64 = b.extractLsb' (64 * (2 * k + 1)) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 64 * (2 * k + 1) = 128 * k + 64 by ring, pow_add, ← Nat.div_div_eq_div_mul]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd _ (by norm_num)]
end SigGolfCandidate.T3M
end
-- ==== merged from ClaudeWCT_W9_T3M_SigCodec ====
section

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.T3M (digNat digNat_lt digNat_digit digNat_eq_of_digits getD_append_left' getD_append_right'
  getD_ofFn' ofFn_four chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)
open SphincsSecurity (bytesLE bytesLE_length)
def openingList (op : WCT9.Opening) : List Digest := List.ofFn op.values ++ List.ofFn op.path
def layerList (s : WCT9.Signature) (lay : Layer) : List Digest :=
  List.ofFn (s.layers lay).values ++ List.ofFn (s.layers lay).path
def sigDigests (s : WCT9.Signature) : List Digest :=
  [s.rho] ++ (List.ofFn s.openings).flatMap openingList ++
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3)))
theorem serializeOpening_eq (op : WCT9.Opening) :
    WCT9.serializeOpening op = (openingList op).flatMap (bytesLE 16) := by
  unfold WCT9.serializeOpening openingList
  rw [List.flatMap_append]
theorem serialize_eq (s : WCT9.Signature) : WCT9.serialize s = (sigDigests s).flatMap (bytesLE 16) := by
  unfold WCT9.serialize sigDigests
  rw [ofFn_four]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatten_cons,
    List.flatten_nil, layerList, serializeLayer, List.flatMap_assoc, ← serializeOpening_eq]
theorem length_openingList (op : WCT9.Opening) : (openingList op).length = 13 := by
  simp [openingList]
theorem length_layerList (s : WCT9.Signature) (lay : Layer) :
    (layerList s lay).length = chainCount lay + height lay := by
  simp only [layerList, List.length_append, List.length_ofFn]
theorem length_openings (s : WCT9.Signature) :
    ((List.ofFn s.openings).flatMap openingList).length = 117 := by
  rw [List.length_flatMap]
  simp only [List.map_ofFn, Function.comp_def, length_openingList]
  rfl

def layIdx (lay : Layer) : Nat := (![118, 184, 234, 283] : Layer → Nat) lay
section getD
theorem getD_flatMap_chunks {α β : Type} (f : α → List β) (n : Nat) (d : β) (hf : ∀ a, (f a).length = n) :
    ∀ (L : List α) k i (hk : k < L.length), i < n → (L.flatMap f).getD (n * k + i) d = (f L[k]).getD i d
  | [], k, _, hk, _ => by simp at hk
  | a :: L, k, i, hk, hi => by
      have hl : (f a).length = n := hf a
      rw [List.flatMap_cons]
      rcases k with _ | k
      · simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < (f a).length by omega)]
      · simp only [List.getElem_cons_succ]
        have := getD_flatMap_chunks f n d hf L k i (by simpa using hk) hi
        simp only [List.getD_eq_getElem?_getD] at this ⊢
        rw [List.getElem?_append_right (show (f a).length ≤ n * (k + 1) + i by rw [hl]; nlinarith),
          show n * (k + 1) + i - (f a).length = n * k + i by rw [hl]; ring_nf; omega, this]
variable (s : WCT9.Signature)
theorem sigDigests_rho : (sigDigests s).getD 0 0 = s.rho := by
  unfold sigDigests; rfl
theorem sigDigests_opening (k : WCT9.Coord) (i : Nat) (hi : i < 13) :
    (sigDigests s).getD (1 + 13 * k.val + i) 0 = (openingList (s.openings k)).getD i 0 := by
  have hk := k.isLt
  unfold sigDigests
  rw [getD_append_left' (by simp only [List.length_append, List.length_singleton, length_openings]; omega),
    getD_append_right' (by simp; omega), List.length_singleton,
    show 1 + 13 * k.val + i - 1 = 13 * k.val + i by omega,
    getD_flatMap_chunks openingList 13 0 length_openingList _ k.val i (by simp [hk]) hi, List.getElem_ofFn]
theorem sigDigests_value (k : WCT9.Coord) (t : Fin 6) :
    (sigDigests s).getD (1 + 13 * k.val + t.val) 0 = (s.openings k).values t := by
  rw [sigDigests_opening s k t.val (by omega), openingList, getD_append_left' (by simp), getD_ofFn']
theorem sigDigests_path (k : WCT9.Coord) (l : Fin 7) :
    (sigDigests s).getD (1 + 13 * k.val + 6 + l.val) 0 = (s.openings k).path l := by
  rw [show 1 + 13 * k.val + 6 + l.val = 1 + 13 * k.val + (6 + l.val) by omega,
    sigDigests_opening s k _ (by omega), openingList, getD_append_right' (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left, getD_ofFn']
theorem sigDigests_tail (k : Nat) (hk : 118 ≤ k) : (sigDigests s).getD k 0 =
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3))).getD (k - 118) 0 := by
  unfold sigDigests
  rw [getD_append_right' (by simp only [List.length_append, List.length_singleton, length_openings]; omega)]
  simp only [List.length_append, List.length_singleton, length_openings]

end getD
def sigDig (b : Bytes 5312) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
def sigDec (b : Bytes 5312) : WCT9.Signature where
  rho := sigDig b 0
  openings := fun k => ⟨fun t => sigDig b (1 + 13 * k.val + t.val), fun l => sigDig b (1 + 13 * k.val + 6 + l.val)⟩
  layers := fun lay => ⟨fun i => sigDig b (layIdx lay + i.val), fun j => sigDig b (layIdx lay + (chainCount lay + j.val))⟩
theorem pow_5312 : (2 : Nat) ^ (8 * 5312) = 2 ^ (128 * 332) := congrArg (fun n => 2 ^ n) rfl
def sigB (s : WCT9.Signature) : Bytes 5312 := BitVec.ofNat _ (readLE (WCT9.serialize s))
set_option exponentiation.threshold 50000 in
theorem sigDig_toNat (b : Bytes 5312) (k : Nat) : (sigDig b k).toNat = b.toNat / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

set_option exponentiation.threshold 50000 in
theorem sigDig_lo (b : Bytes 5312) (k : Nat) : (sigDig b k).extractLsb' 0 64 = b.extractLsb' (64 * (2 * k)) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  rw [show 64 * (2 * k) = 128 * k by ring, Nat.mod_mod_of_dvd _ (by norm_num)]
theorem sigDig_hi (b : Bytes 5312) (k : Nat) :
    (sigDig b k).extractLsb' 64 64 = b.extractLsb' (64 * (2 * k + 1)) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 64 * (2 * k + 1) = 128 * k + 64 by ring, pow_add, ← Nat.div_div_eq_div_mul]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd _ (by norm_num)]
end ClaudeWCT.W9.T3M
end
-- ==== merged from ClaudeWCT_W9_T3M_SigCodecC ====
section

/-! # The compact (H2) signature bytes

5,310 bytes: the 332 digests of `sigDigests` with digest 183 (the top layer's level-11 sibling) cut out, then that
digest's low 14 bytes. `sigBC` encodes, `sigDecC` decodes (the omitted 16 bits decode as zero), and
`sigDecC (sigBC σ) = proj σ`, `sigBC (sigDecC b) = b`, `sigBC (proj σ) = sigBC σ`. -/

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.T3M (digNat digNat_lt digNat_digit digNat_eq_of_digits getD_append_left' getD_append_right'
  getD_ofFn' chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)
set_option maxRecDepth 10000

abbrev CBytes := Bytes 5310
def sibIdx : Nat := 183
def cDig (b : CBytes) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
/-- The digest at full-layout index `k` of the compact bytes. -/
def digC (b : CBytes) (k : Nat) : Digest :=
  if k < 183 then cDig b k else if k = 183 then cDig b 331 else cDig b (k - 1)
def sigDecC (b : CBytes) : WCT9.Signature where
  rho := digC b 0
  openings := fun k => ⟨fun t => digC b (1 + 13 * k.val + t.val), fun l => digC b (1 + 13 * k.val + 6 + l.val)⟩
  layers := fun lay => ⟨fun i => digC b (layIdx lay + i.val), fun j => digC b (layIdx lay + (chainCount lay + j.val))⟩
def sigBC (s : WCT9.Signature) : CBytes :=
  BitVec.ofNat _ (digNat ((sigDigests s).eraseIdx 183) + 2 ^ (128 * 331) * (((sigDigests s).getD 183 0).toNat % 2 ^ 112))


theorem cDig_toNat (b : CBytes) (k : Nat) : (cDig b k).toNat = b.toNat / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem cTail_lt (b : CBytes) : b.toNat / 2 ^ (128 * 331) < 2 ^ 112 := by
  have hb := b.isLt
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  exact lt_of_lt_of_eq hb (by norm_num)

theorem getD_eraseIdx {α : Type} (l : List α) (i j : Nat) (d : α) :
    (l.eraseIdx i).getD j d = if j < i then l.getD j d else l.getD (j + 1) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  split <;> rfl


theorem mod_digit (B n k : Nat) (hk : k < n) :
    B % 2 ^ (128 * n) / 2 ^ (128 * k) % 2 ^ 128 = B / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [show 2 ^ (128 * n) = 2 ^ (128 * k) * 2 ^ (128 * (n - k)) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact pow_dvd_pow 2 (by omega)

theorem lt_split (X y A M : Nat) (hX : X < 2 ^ A) (hy : y < M) : X + 2 ^ A * y < 2 ^ A * M := by
  have : 2 ^ A * y + 2 ^ A ≤ 2 ^ A * M := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hy
  omega

theorem split_mod (D T A : Nat) (hD : D < 2 ^ A) : (D + 2 ^ A * T) % 2 ^ A = D := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hD]

theorem split_div (D T A : Nat) (hD : D < 2 ^ A) : (D + 2 ^ A * T) / 2 ^ A = T := by
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hD, Nat.zero_add]

theorem pow_5310 : (2 : Nat) ^ (8 * 5310) = 2 ^ (128 * 331) * 2 ^ 112 := by rw [← pow_add]

set_option exponentiation.threshold 50000 in



theorem digC_183 (b : CBytes) : digC b 183 = cDig b 331 := by
  unfold digC; rw [if_neg (by decide), if_pos rfl]

end ClaudeWCT.W9.T3M

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.T3M (digNat digNat_lt digNat_cons digNat_nil)

/-- Full-layout digest index of compact digest slot `k` (slot 331 holds the top sibling). -/
def cIdx (k : Nat) : Nat := if k < 183 then k else if k < 331 then k + 1 else 183
def compactList (s : WCT9.Signature) : List Digest := (List.range 332).map fun k => (sigDigests s).getD (cIdx k) 0

theorem digNat_append (L1 L2 : List Digest) : digNat (L1 ++ L2) = digNat L1 + 2 ^ (128 * L1.length) * digNat L2 := by
  induction L1 with
  | nil => simp [digNat_nil]
  | cons d L ih =>
    rw [List.cons_append, digNat_cons, digNat_cons, ih, List.length_cons,
      show 128 * (L.length + 1) = 128 + 128 * L.length by ring, pow_add]
    ring


theorem mod_split (X y A M : Nat) (hX : X < 2 ^ A) (hM : 0 < M) :
    (X + 2 ^ A * y) % (2 ^ A * M) = X + 2 ^ A * (y % M) := by
  conv_lhs => rw [← Nat.div_add_mod y M]
  rw [show X + 2 ^ A * (M * (y / M) + y % M) = (X + 2 ^ A * (y % M)) + (2 ^ A * M) * (y / M) by ring,
    Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have hr : y % M < M := Nat.mod_lt _ hM
  have h1 : 2 ^ A * (y % M) + 2 ^ A ≤ 2 ^ A * M := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
  omega
end ClaudeWCT.W9.T3M

/-! Compact serialization for the shared forest. -/
namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
abbrev SharedSignature := SigGolfCandidate.Research.SharedForest.Signature
open SigGolfCandidate.T3M (digNat getD_append_left' getD_append_right' getD_ofFn'
  chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)

def pairList (p : PairOpening) : List Digest :=
  ((List.ofFn p.firstValues ++ List.ofFn p.firstPath) ++
    List.ofFn p.secondValues) ++ List.ofFn p.secondPath
def singletonList (p : SingletonOpening) : List Digest :=
  List.ofFn p.values ++ List.ofFn p.path
def layerList (s : SharedSignature) (lay : Layer) : List Digest :=
  List.ofFn (s.layers lay).values ++ List.ofFn (s.layers lay).path
def sigDigests (s : SharedSignature) : List Digest :=
  (([s.rho] ++ (List.ofFn s.forest.pairs).flatMap pairList) ++ singletonList s.forest.singleton) ++
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3)))
/-- T51: top values at 114..164, top path 165..176, L1 at 177, L2 at 227, L3 at 276 (325 digests). -/
def layIdx (lay : Layer) : Nat := (![114,177,227,276] : Layer → Nat) lay
theorem pairList_length (p : PairOpening) : (pairList p).length = 25 := by simp [pairList]
theorem singletonList_length (p : SingletonOpening) : (singletonList p).length = 13 := by
  simp [singletonList]
theorem pairs_length (s : SharedSignature) : ((List.ofFn s.forest.pairs).flatMap pairList).length = 100 := by
  rw [List.length_flatMap]
  simp only [List.map_ofFn, Function.comp_def, pairList_length]
  rfl
theorem layerList_length (s : SharedSignature) (lay : Layer) :
    (layerList s lay).length = chainCount lay + height lay := by
  simp only [layerList, List.length_append, List.length_ofFn]
theorem sigDigests_length (s : SharedSignature) : (sigDigests s).length = 325 := by
  simp only [sigDigests, List.length_append, List.length_singleton, pairs_length,
    singletonList_length, layerList_length]
  rfl

/-- T51: the 5,195-byte compact signature (324 digests + an 11-byte tail; #938 img-v6: 5,239 bytes). -/
abbrev CBytes := Bytes 5195
def cDig (b : CBytes) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
/-- Offset of the X field in the top `b_j = topZeroBits j` bits of the path node at height `j` (`j = 1..10`):
`Σ_{h < j} b_h` = 0, 1, 2, 4, 7, 11, 16, 22 for `j = 3..10` (heights 1, 2 carry no bits). -/
def xOff (j : Nat) : Nat := ((List.range j).map topZeroBits).sum
def clearTop (j : Nat) (d : Digest) : Digest := BitVec.ofNat 128 (d.toNat % 2 ^ (128 - j))
def topBits (j : Nat) (d : Digest) : Nat := d.toNat / 2 ^ (128 - j)
/-- T51: the 29-bit X field read from the top `b_j` bits of the path nodes of heights 3..10 (digests 168..175). -/
def xOfB (b : CBytes) : Nat :=
  topBits 1 (cDig b 168) + topBits 1 (cDig b 169) * 2 ^ 1 + topBits 2 (cDig b 170) * 2 ^ 2 +
  topBits 3 (cDig b 171) * 2 ^ 4 + topBits 4 (cDig b 172) * 2 ^ 7 + topBits 5 (cDig b 173) * 2 ^ 11 +
  topBits 6 (cDig b 174) * 2 ^ 16 + topBits 7 (cDig b 175) * 2 ^ 22
/-- Decoded digest `k`: the path nodes of heights 1..10 (digests 166..175) lose their top `b_j` bits; index 176 (top
sibling) = tail 88 bits + X bits 0..15 (bits 88..103; bits 104..127 zero, 112..127 brute-forced by expand). -/
def digC (b : CBytes) (k : Nat) : Digest :=
  if k < 176 then (if 166 ≤ k then clearTop (topZeroBits (k - 165)) (cDig b k) else cDig b k)
  else if k = 176 then BitVec.ofNat 128 (b.toNat / 2 ^ (128 * 324) % 2 ^ 88 + xOfB b % 2 ^ 16 * 2 ^ 88)
  else cDig b (k - 1)
def sigDecC (b : CBytes) : SharedSignature where
  rho := digC b 0
  policyHints := BitVec.ofNat 16 (xOfB b / 2 ^ 16)
  forest := {
    pairs := fun p => {
      firstValues := fun i => digC b (1 + 25 * p.val + i.val)
      firstPath := fun i => digC b (1 + 25 * p.val + 6 + i.val)
      secondValues := fun i => digC b (1 + 25 * p.val + 12 + i.val)
      secondPath := fun i => digC b (1 + 25 * p.val + 18 + i.val) }
    singleton := {
      values := fun i => digC b (101 + i.val)
      path := fun i => digC b (107 + i.val) } }
  layers := fun lay => {
    values := fun i => digC b (layIdx lay + i.val)
    path := fun i => digC b (layIdx lay + chainCount lay + i.val) }
/-- T51: X = top sibling bits 88..103 (16) | hint (13 bits) << 16 (29 bits). -/
def xField (s : SharedSignature) : Nat :=
  ((sigDigests s).getD 176 0).toNat / 2 ^ 88 % 2 ^ 16 + s.policyHints.toNat % 2 ^ 13 * 2 ^ 16
/-- T51: the path node of height `j` with X bits `xOff j ..` in its top `b_j = topZeroBits j` bits. -/
def packD (j : Nat) (d : Digest) (x : Nat) : Digest :=
  BitVec.ofNat 128 (d.toNat % 2 ^ (128 - topZeroBits j) +
    x / 2 ^ xOff j % 2 ^ topZeroBits j * 2 ^ (128 - topZeroBits j))
def encList (s : SharedSignature) : List Digest :=
  (List.range 324).map fun k => if 166 ≤ k ∧ k ≤ 175 then packD (k - 165) (((sigDigests s).eraseIdx 176).getD k 0)
    (xField s) else ((sigDigests s).eraseIdx 176).getD k 0
def sigBC (s : SharedSignature) : CBytes :=
  BitVec.ofNat _ (digNat (encList s) + 2 ^ (128 * 324) * (((sigDigests s).getD 176 0).toNat % 2 ^ 88))
theorem compact_length : 324 * 16 + 11 = 5195 := by decide
/-- The normal form a decoded signature has (T51): path tops of heights 1..10 clear (`b_j` bits), top sibling below
bit 104, hint 13 bits. -/
def normD (k : Nat) (d : Digest) : Digest :=
  if 166 ≤ k ∧ k ≤ 175 then clearTop (topZeroBits (k - 165)) d
  else if k = 176 then BitVec.ofNat 128 (d.toNat % 2 ^ 104) else d
theorem normD_of_lt (k : Nat) (d : Digest) (hk : k < 166) : normD k d = d := by
  unfold normD; rw [if_neg (by omega), if_neg (by omega)]
theorem sigDigests_rho (s : SharedSignature) : (sigDigests s).getD 0 0 = s.rho := by rfl
theorem sigDigests_pair (s : SharedSignature) (p : Fin 4) (i : Nat) (hi : i < 25) :
    (sigDigests s).getD (1 + 25 * p.val + i) 0 = (pairList (s.forest.pairs p)).getD i 0 := by
  unfold sigDigests
  rw [getD_append_left' (by simp only [List.length_append, List.length_singleton,
        pairs_length, singletonList_length]; omega),
    getD_append_left' (by simp only [List.length_append, List.length_singleton, pairs_length]; omega),
    getD_append_right' (by simp; omega), List.length_singleton,
    show 1 + 25 * p.val + i - 1 = 25 * p.val + i by omega,
    ClaudeWCT.W9.T3M.getD_flatMap_chunks pairList 25 0 pairList_length _ p.val i (by simp) hi,
    List.getElem_ofFn]
theorem pairList_firstValue (p : PairOpening) (i : Fin 6) :
    (pairList p).getD i.val 0 = p.firstValues i := by
  unfold pairList
  rw [getD_append_left' (by simp; omega), getD_append_left' (by simp; omega),
    getD_append_left' (by simp), getD_ofFn']
theorem pairList_firstPath (p : PairOpening) (i : Fin 6) :
    (pairList p).getD (6 + i.val) 0 = p.firstPath i := by
  unfold pairList
  rw [getD_append_left' (by simp; omega), getD_append_left' (by simp; omega),
    getD_append_right' (by simp), List.length_ofFn, Nat.add_sub_cancel_left, getD_ofFn']
theorem pairList_secondValue (p : PairOpening) (i : Fin 6) :
    (pairList p).getD (12 + i.val) 0 = p.secondValues i := by
  unfold pairList
  rw [getD_append_left' (by simp; omega), getD_append_right' (by simp)]
  simp only [List.length_append, List.length_ofFn]
  rw [show 12 + i.val - (6 + 6) = i.val by omega, getD_ofFn']
theorem pairList_secondPath (p : PairOpening) (i : Fin 7) :
    (pairList p).getD (18 + i.val) 0 = p.secondPath i := by
  unfold pairList
  rw [getD_append_right' (by simp)]
  simp only [List.length_append, List.length_ofFn]
  rw [show 18 + i.val - (6 + 6 + 6) = i.val by omega, getD_ofFn']
theorem sigDigests_singleton (s : SharedSignature) (i : Nat) (hi : i < 13) :
    (sigDigests s).getD (101 + i) 0 = (singletonList s.forest.singleton).getD i 0 := by
  unfold sigDigests
  rw [getD_append_left' (by simp only [List.length_append, List.length_singleton,
      pairs_length, singletonList_length]; omega), getD_append_right' (by
      simp only [List.length_append, List.length_singleton, pairs_length]; omega)]
  simp only [List.length_append, List.length_singleton, pairs_length]
  rw [show 101 + i - (1 + 100) = i by omega]
theorem sigDigests_tail (s : SharedSignature) (k : Nat) (hk : 114 ≤ k) : (sigDigests s).getD k 0 =
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3))).getD (k - 114) 0 := by
  unfold sigDigests
  rw [getD_append_right' (by simp only [List.length_append, List.length_singleton, pairs_length, singletonList_length]; omega)]
  simp only [List.length_append, List.length_singleton, pairs_length, singletonList_length]
theorem sigDigests_layer (s : SharedSignature) (lay : Layer) (i : Nat) (hi : i < chainCount lay + height lay) :
    (sigDigests s).getD (layIdx lay + i) 0 = (layerList s lay).getD i 0 := by
  have l0 := layerList_length s 0
  have l1 := layerList_length s 1
  have l2 := layerList_length s 2
  rw [chainCount_0, height_0] at l0
  rw [chainCount_1, height_1] at l1
  rw [chainCount_2, height_2] at l2
  fin_cases lay
  · show (sigDigests s).getD (114 + i) 0 = (layerList s 0).getD i 0
    have hi' : i < 63 := hi
    rw [sigDigests_tail s _ (by omega), show 114 + i - 114 = i by omega, getD_append_left' (by omega)]
  · show (sigDigests s).getD (177 + i) 0 = (layerList s 1).getD i 0
    have hi' : i < 50 := hi
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_left' (by omega),
      show 177 + i - 114 - 63 = i by omega]
  · show (sigDigests s).getD (227 + i) 0 = (layerList s 2).getD i 0
    have hi' : i < 49 := hi
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_right' (by omega), l1,
      getD_append_left' (by omega), show 227 + i - 114 - 63 - 50 = i by omega]
  · show (sigDigests s).getD (276 + i) 0 = (layerList s 3).getD i 0
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_right' (by omega), l1,
      getD_append_right' (by omega), l2, show 276 + i - 114 - 63 - 50 - 49 = i by omega]
theorem sigDigests_layValue (s : SharedSignature) (lay : Layer) (i : Nat) (hi : i < chainCount lay) :
    (sigDigests s).getD (layIdx lay + i) 0 = (s.layers lay).values ⟨i, hi⟩ := by
  rw [sigDigests_layer s lay i (by omega), layerList, getD_append_left' (by simpa using hi), getD_ofFn']
theorem sigDigests_layPath (s : SharedSignature) (lay : Layer) (j : Nat) (hj : j < height lay) :
    (sigDigests s).getD (layIdx lay + (chainCount lay + j)) 0 = (s.layers lay).path ⟨j, hj⟩ := by
  rw [sigDigests_layer s lay _ (by omega), layerList, getD_append_right' (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left, getD_ofFn']

end ClaudeWCT.W9.T3M.SharedCodec


namespace ClaudeWCT.W9.T3M.SharedCodec
/-- Internal expansion retains the four unused seventh A-path slots. T51: the expander's slot layout keeps #938's
lower-layer slots, so the top path follows the 51 top values (slots 169..180) and three unused slots 181..183 precede
L1 (slot 184): digest `k` sits at slot `k + 4` for `114 ≤ k ≤ 176`, `k + 7` for `k ≥ 177`. -/
def internalFullIndex (k : Nat) : Nat :=
  k + (if 13 ≤ k then 1 else 0) + (if 38 ≤ k then 1 else 0) +
    (if 63 ≤ k then 1 else 0) + (if 88 ≤ k then 1 else 0) + (if 177 ≤ k then 3 else 0)
def externalFullIndex (k : Nat) : Nat :=
  k - ((if 13 < k then 1 else 0) + (if 39 < k then 1 else 0) +
    (if 65 < k then 1 else 0) + (if 91 < k then 1 else 0) + (if 183 < k then 3 else 0))
def internalDummy (k : Nat) : Bool := decide (k = 13 ∨ k = 39 ∨ k = 65 ∨ k = 91 ∨ k = 181 ∨ k = 182 ∨ k = 183)
theorem internalFullIndex_spec (k : Nat) :
    internalFullIndex k = k + (([13,38,63,88].filter fun skip => decide (skip ≤ k)).length) +
      (if 177 ≤ k then 3 else 0) := by
  unfold internalFullIndex
  by_cases h13 : 13 ≤ k <;> by_cases h38 : 38 ≤ k <;> by_cases h63 : 63 ≤ k <;> by_cases h88 : 88 ≤ k <;>
    simp [h13, h38, h63, h88] <;> omega

theorem internalFullIndex_bound (k : Nat) (hk : k < 325) : internalFullIndex k < 332 := by
  unfold internalFullIndex
  split_ifs <;> omega
theorem internalFullIndex_dummy (k : Nat) : internalDummy (internalFullIndex k) = false := by
  simp only [internalDummy, decide_eq_false_iff_not]
  unfold internalFullIndex
  split_ifs <;> omega
theorem internalFullIndex_inverse (k : Nat) : externalFullIndex (internalFullIndex k) = k := by
  unfold externalFullIndex internalFullIndex
  split_ifs <;> omega
def inflatedRead {α : Type} (zero : α) (read : Nat → α) (k : Nat) : α :=
  if internalDummy k then zero else read (externalFullIndex k)
theorem inflatedRead_internal {α : Type} (zero : α) (read : Nat → α) (k : Nat) :
    inflatedRead zero read (internalFullIndex k) = read k := by
  simp only [inflatedRead, internalFullIndex_dummy, Bool.false_eq_true, ↓reduceIte,
    internalFullIndex_inverse]
theorem internalFullIndex_main (k : Nat) (hk : 114 ≤ k) (hk' : k ≤ 176) : internalFullIndex k = k + 4 := by
  unfold internalFullIndex
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)]
theorem internalFullIndex_lower (k : Nat) (hk : 177 ≤ k) : internalFullIndex k = k + 7 := by
  unfold internalFullIndex
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos hk]
theorem internalFullIndex_tail : internalFullIndex 176 = 180 := by rfl
end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.T3
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def serializedWord (read : Nat → BitVec 64) (k : Nat) : BitVec 64 :=
  if k < 26 then read k else if k < 28 then 0 else
  if k < 78 then read (k - 2) else if k < 80 then 0 else
  if k < 130 then read (k - 4) else if k < 132 then 0 else
  if k < 182 then read (k - 6) else if k < 184 then 0 else
  if k < 366 then read (k - 8) else if k = 366 then read 654 else
  if k = 367 then (read 655 <<< 16) >>> 16 else read (k - 10)

theorem externalFullIndex_tail_iff (k : Nat) : externalFullIndex k = 176 ↔ k = 180 := by
  unfold externalFullIndex
  split_ifs <;> omega

theorem extract_digest_word {n : Nat} (x : BitVec n) (a i : Nat) (hi : i < 2) :
    (x.extractLsb' a 128).extractLsb' (64*i) 64 = x.extractLsb' (a+64*i) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [show decide (64*i+j < 128) = true from decide_eq_true (by omega), Bool.true_and]
  congr 1
  omega

end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (digNat digNat_lt digNat_digit)
open ClaudeWCT.W9.T3M (getD_eraseIdx mod_digit lt_split split_mod split_div)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

theorem length_eraseIdx_sig (s : SharedSignature) :
    ((sigDigests s).eraseIdx 176).length = 324 := by
  rw [List.length_eraseIdx,sigDigests_length];decide

theorem encList_length (s : SharedSignature) : (encList s).length = 324 := by simp [encList]

theorem encList_getD (s : SharedSignature) (k : Nat) (hk : k < 324) :
    (encList s).getD k 0 = if 166 ≤ k ∧ k ≤ 175 then packD (k - 165) (((sigDigests s).eraseIdx 176).getD k 0)
      (xField s) else ((sigDigests s).eraseIdx 176).getD k 0 := by
  simp [encList, List.getD_eq_getElem?_getD, hk]

theorem sigBC_toNat (s : SharedSignature) :
    (sigBC s).toNat = digNat (encList s) + 2^(128*324)*(((sigDigests s).getD 176 0).toNat%2^88) := by
  unfold sigBC
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hD := digNat_lt (encList s)
  rw [encList_length] at hD
  have hT := lt_split _ _ _ _ hD (Nat.mod_lt ((sigDigests s).getD 176 0).toNat (show 0<2^88 by positivity))
  simpa only [←pow_add] using hT

theorem encoded_low (s : SharedSignature) : (sigBC s).toNat%2^(128*324)=digNat (encList s) := by
  have hD := digNat_lt (encList s)
  rw [encList_length] at hD
  rw [sigBC_toNat, split_mod _ _ _ hD]

theorem encoded_tail (s : SharedSignature) :
    (sigBC s).toNat/2^(128*324)%2^88=((sigDigests s).getD 176 0).toNat%2^88 := by
  have hD := digNat_lt (encList s)
  rw [encList_length] at hD
  rw [sigBC_toNat, split_div _ _ _ hD, Nat.mod_mod]

theorem cDig_sigBC (s : SharedSignature) (j : Nat) (hj : j<324) : cDig (sigBC s) j=(encList s).getD j 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [cDig,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,←digNat_digit]
  rw [←mod_digit _ 324 j hj,encoded_low]

theorem pack_gen (b : Nat) (hb : b ≤ 128) (d : Digest) (y : Nat) :
    clearTop b (BitVec.ofNat 128 (d.toNat % 2 ^ (128 - b) + y % 2 ^ b * 2 ^ (128 - b))) = clearTop b d ∧
      topBits b (BitVec.ofNat 128 (d.toNat % 2 ^ (128 - b) + y % 2 ^ b * 2 ^ (128 - b))) = y % 2 ^ b := by
  have hd : d.toNat % 2 ^ (128 - b) < 2 ^ (128 - b) := Nat.mod_lt _ (by positivity)
  have hf : y % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
  have hlt : d.toNat % 2 ^ (128 - b) + y % 2 ^ b * 2 ^ (128 - b) < 2 ^ 128 := by
    have : y % 2 ^ b * 2 ^ (128 - b) ≤ (2 ^ b - 1) * 2 ^ (128 - b) := Nat.mul_le_mul_right _ (by omega)
    have e : (2 ^ b - 1) * 2 ^ (128 - b) + 2 ^ (128 - b) = 2 ^ 128 := by
      rw [Nat.sub_mul, one_mul, ← pow_add, show b + (128 - b) = 128 by omega]
      have : 2 ^ (128 - b) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  unfold clearTop topBits
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_right, Nat.mod_mod]
  · rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hd, zero_add]

theorem topZeroBits_le_eight (j : Nat) (hj : j ≤ 11) : topZeroBits j ≤ 8 := by interval_cases j <;> decide

/-- T51: the X bits stored in the top `b_j = topZeroBits j` bits of a packed path node (`b` names `b_j`). -/
theorem pack_facts (j b : Nat) (hj : 1 ≤ j ∧ j ≤ 10) (hb : topZeroBits j = b) (d : Digest) (x : Nat) :
    clearTop b (packD j d x) = clearTop b d ∧ topBits b (packD j d x) = x / 2 ^ xOff j % 2 ^ b := by
  subst hb
  exact pack_gen (topZeroBits j) (by have := topZeroBits_le_eight j (by omega); omega) d (x / 2 ^ xOff j)

theorem xOff_vals : xOff 3 = 0 ∧ xOff 4 = 1 ∧ xOff 5 = 2 ∧ xOff 6 = 4 ∧ xOff 7 = 7 ∧ xOff 8 = 11 ∧ xOff 9 = 16 ∧
    xOff 10 = 22 := by decide

theorem xField_lt (s : SharedSignature) : xField s < 2 ^ 29 := by
  unfold xField
  have h1 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 88) (show 0 < 2 ^ 16 by positivity)
  have h2 := Nat.mod_lt s.policyHints.toNat (show 0 < 2 ^ 13 by positivity)
  omega

theorem xOfB_sigBC (s : SharedSignature) : xOfB (sigBC s) = xField s := by
  have hx := xField_lt s
  obtain ⟨o3, o4, o5, o6, o7, o8, o9, o10⟩ := xOff_vals
  unfold xOfB
  simp only [cDig_sigBC s _ (by norm_num : (168:Nat) < 324), cDig_sigBC s _ (by norm_num : (169:Nat) < 324),
    cDig_sigBC s _ (by norm_num : (170:Nat) < 324), cDig_sigBC s _ (by norm_num : (171:Nat) < 324),
    cDig_sigBC s _ (by norm_num : (172:Nat) < 324), cDig_sigBC s _ (by norm_num : (173:Nat) < 324),
    cDig_sigBC s _ (by norm_num : (174:Nat) < 324), cDig_sigBC s _ (by norm_num : (175:Nat) < 324)]
  simp only [encList_getD s _ (by norm_num : (168:Nat) < 324), encList_getD s _ (by norm_num : (169:Nat) < 324),
    encList_getD s _ (by norm_num : (170:Nat) < 324), encList_getD s _ (by norm_num : (171:Nat) < 324),
    encList_getD s _ (by norm_num : (172:Nat) < 324), encList_getD s _ (by norm_num : (173:Nat) < 324),
    encList_getD s _ (by norm_num : (174:Nat) < 324), encList_getD s _ (by norm_num : (175:Nat) < 324)]
  norm_num only [if_true, and_self, ite_true]
  rw [(pack_facts 3 1 (by norm_num) rfl _ _).2, (pack_facts 4 1 (by norm_num) rfl _ _).2,
    (pack_facts 5 2 (by norm_num) rfl _ _).2, (pack_facts 6 3 (by norm_num) rfl _ _).2,
    (pack_facts 7 4 (by norm_num) rfl _ _).2, (pack_facts 8 5 (by norm_num) rfl _ _).2,
    (pack_facts 9 6 (by norm_num) rfl _ _).2, (pack_facts 10 7 (by norm_num) rfl _ _).2,
    o3, o4, o5, o6, o7, o8, o9, o10]
  norm_num
  omega

theorem digC_sigBC (s : SharedSignature) (k : Nat) (hk : k<325) :
    digC (sigBC s) k = normD k ((sigDigests s).getD k 0) := by
  by_cases hlt : k<176
  · rw [digC, if_pos hlt, cDig_sigBC s k (by omega), encList_getD s k (by omega), getD_eraseIdx, if_pos hlt]
    by_cases hp : 166 ≤ k
    · rw [if_pos hp, if_pos ⟨hp, by omega⟩, (pack_facts _ _ ⟨by omega, by omega⟩ rfl _ _).1, normD,
        if_pos ⟨hp, by omega⟩]
    · rw [if_neg hp, if_neg (by omega), normD_of_lt _ _ (by omega)]
  · by_cases he : k=176
    · subst he
      rw [digC, if_neg (by decide), if_pos rfl, encoded_tail, xOfB_sigBC, normD, if_neg (by decide), if_pos rfl]
      congr 1
      unfold xField
      have h88 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 88) (show 0 < 2 ^ 16 by positivity)
      have hm : ((sigDigests s).getD 176 0).toNat % 2 ^ 104 =
          ((sigDigests s).getD 176 0).toNat % 2 ^ 88 + 2 ^ 88 * (((sigDigests s).getD 176 0).toNat / 2 ^ 88 % 2 ^ 16) := by
        rw [show (2:Nat) ^ 104 = 2 ^ 88 * 2 ^ 16 by norm_num, Nat.mod_mul]
      rw [hm]
      omega
    · rw [digC, if_neg hlt, if_neg he, cDig_sigBC s (k-1) (by omega), encList_getD s _ (by omega),
        if_neg (by omega), getD_eraseIdx, if_neg (by omega), show k-1+1=k by omega, normD, if_neg (by omega),
        if_neg he]

theorem policyHints_sigDecC_sigBC (s : SharedSignature) :
    (sigDecC (sigBC s)).policyHints = BitVec.ofNat 16 (s.policyHints.toNat % 2 ^ 13) := by
  change BitVec.ofNat 16 (xOfB (sigBC s) / 2 ^ 16) = _
  rw [xOfB_sigBC]
  unfold xField
  congr 1
  have h1 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 88) (show 0 < 2 ^ 16 by positivity)
  omega

end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (getD_append_left' getD_append_right' getD_ofFn')
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem forest_sigDecC_sigBC (s : SharedSignature) :
    (sigDecC (sigBC s)).forest=s.forest := by
  have hp : (sigDecC (sigBC s)).forest.pairs=s.forest.pairs := by
    funext p
    have h1 : ((sigDecC (sigBC s)).forest.pairs p).firstValues=(s.forest.pairs p).firstValues := by
      funext i
      change digC (sigBC s) (1+25*p.val+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),sigDigests_pair s p i.val (by omega),pairList_firstValue]
    have h2 : ((sigDecC (sigBC s)).forest.pairs p).firstPath=(s.forest.pairs p).firstPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+6+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),show 1+25*p.val+6+i.val=1+25*p.val+(6+i.val) by omega,
        sigDigests_pair s p (6+i.val) (by omega),pairList_firstPath]
    have h3 : ((sigDecC (sigBC s)).forest.pairs p).secondValues=(s.forest.pairs p).secondValues := by
      funext i
      change digC (sigBC s) (1+25*p.val+12+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),show 1+25*p.val+12+i.val=1+25*p.val+(12+i.val) by omega,
        sigDigests_pair s p (12+i.val) (by omega),pairList_secondValue]
    have h4 : ((sigDecC (sigBC s)).forest.pairs p).secondPath=(s.forest.pairs p).secondPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+18+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),show 1+25*p.val+18+i.val=1+25*p.val+(18+i.val) by omega,
        sigDigests_pair s p (18+i.val) (by omega),pairList_secondPath]
    cases h : (sigDecC (sigBC s)).forest.pairs p
    cases h' : s.forest.pairs p
    simp only [h,h'] at h1 h2 h3 h4
    cases h1;cases h2;cases h3;cases h4;rfl
  have hs : (sigDecC (sigBC s)).forest.singleton=s.forest.singleton := by
    have h1 : (sigDecC (sigBC s)).forest.singleton.values=s.forest.singleton.values := by
      funext i
      change digC (sigBC s) (101+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),sigDigests_singleton s i.val (by omega),singletonList,
        getD_append_left' (by simp),getD_ofFn']
    have h2 : (sigDecC (sigBC s)).forest.singleton.path=s.forest.singleton.path := by
      funext i
      change digC (sigBC s) (107+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),show 107+i.val=101+(6+i.val) by omega,
        sigDigests_singleton s (6+i.val) (by omega),singletonList,getD_append_right' (by simp),
        List.length_ofFn,Nat.add_sub_cancel_left,getD_ofFn']
    cases h : (sigDecC (sigBC s)).forest.singleton
    cases h' : s.forest.singleton
    simp only [h,h'] at h1 h2
    cases h1;cases h2;rfl
  cases h : (sigDecC (sigBC s)).forest
  cases h' : s.forest
  simp only [h,h'] at hp hs
  cases hp;cases hs;rfl

/-- Normal form (what the compact codec keeps; T51: 5,195 bytes). -/
def normalizeV6 (s : SharedSignature) : SharedSignature :=
  { s with
    policyHints := BitVec.ofNat 16 (s.policyHints.toNat % 2 ^ 13)
    layers := fun lay => ⟨(s.layers lay).values,
      fun j => normD (layIdx lay + chainCount lay + j.val) ((s.layers lay).path j)⟩ }

theorem normD_of_out (k : Nat) (d : Digest) (hk : k < 166 ∨ 176 < k) : normD k d = d := by
  unfold normD; rw [if_neg (by omega), if_neg (by omega)]

theorem sigDecC_sigBC (s : SharedSignature) : sigDecC (sigBC s) = normalizeV6 s := by
  have hr : (sigDecC (sigBC s)).rho=s.rho := by
    change digC (sigBC s) 0=s.rho
    rw [digC_sigBC s 0 (by decide),normD_of_lt _ _ (by decide),sigDigests_rho]
  have hh := policyHints_sigDecC_sigBC s
  have hf := forest_sigDecC_sigBC s
  have hl : (sigDecC (sigBC s)).layers=(normalizeV6 s).layers := by
    funext lay
    have hc : layIdx lay+chainCount lay≤325 := by fin_cases lay <;> decide
    have hp : layIdx lay+chainCount lay+height lay≤325 := by fin_cases lay <;> decide
    have hv : ((sigDecC (sigBC s)).layers lay).values=((normalizeV6 s).layers lay).values := by
      funext i
      change digC (sigBC s) (layIdx lay+i.val)=(s.layers lay).values i
      have hn : layIdx lay+i.val < 166 ∨ 176 < layIdx lay+i.val := by
        fin_cases lay <;> simp [layIdx,chainCount] at * <;> omega
      rw [digC_sigBC s _ (by omega),normD_of_out _ _ hn,sigDigests_layValue]
    have hpath : ((sigDecC (sigBC s)).layers lay).path=((normalizeV6 s).layers lay).path := by
      funext i
      change digC (sigBC s) (layIdx lay+chainCount lay+i.val) =
        normD (layIdx lay + chainCount lay + i.val) ((s.layers lay).path i)
      rw [digC_sigBC s _ (by omega), show layIdx lay+chainCount lay+i.val=layIdx lay+(chainCount lay+i.val) by omega,
        sigDigests_layPath s lay i.val i.isLt]
    cases h : (sigDecC (sigBC s)).layers lay
    cases h' : (normalizeV6 s).layers lay
    simp only [h,h'] at hv hpath
    cases hv;cases hpath;rfl
  have hf' : (sigDecC (sigBC s)).forest=(normalizeV6 s).forest := hf
  have hr' : (sigDecC (sigBC s)).rho=(normalizeV6 s).rho := hr
  have hh' : (sigDecC (sigBC s)).policyHints=(normalizeV6 s).policyHints := hh
  cases h : sigDecC (sigBC s)
  cases h' : normalizeV6 s
  simp only [h,h'] at hr' hh' hf' hl
  cases hr';cases hh';cases hf';cases hl;rfl

end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (digNat digNat_eq_of_digits getD_append_left' getD_append_right' getD_ofFn'
 chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)
open ClaudeWCT.W9.T3M (getD_eraseIdx mod_digit)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

theorem sigDigests_sigDecC (b : CBytes) (k : Nat) (hk : k<325) :
    (sigDigests (sigDecC b)).getD k 0=digC b k := by
  by_cases h0:k=0
  · subst h0;exact sigDigests_rho _
  by_cases hp:k<101
  · have hq:(k-1)/25<4:=by omega
    let p : Fin 4:=⟨(k-1)/25,hq⟩
    let j : Nat:=(k-1)%25
    have hj:j<25:=Nat.mod_lt _ (by decide)
    have he:k=1+25*p.val+j:=by dsimp [p,j];omega
    rw [he,sigDigests_pair _ p j hj]
    by_cases h1:j<6
    · rw [pairList_firstValue _ ⟨j,h1⟩]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
    · by_cases h2:j<12
      · rw [show j=6+(j-6) by omega,pairList_firstPath _ ⟨j-6,by omega⟩]
        change digC b _=digC b _
        congr 1 <;> simp only [Fin.val_mk] <;> omega
      · by_cases h3:j<18
        · rw [show j=12+(j-12) by omega,pairList_secondValue _ ⟨j-12,by omega⟩]
          change digC b _=digC b _
          congr 1 <;> simp only [Fin.val_mk] <;> omega
        · rw [show j=18+(j-18) by omega,pairList_secondPath _ ⟨j-18,by omega⟩]
          change digC b _=digC b _
          congr 1 <;> simp only [Fin.val_mk] <;> omega
  by_cases hs:k<114
  · have he:k=101+(k-101):=by omega
    rw [he,sigDigests_singleton _ (k-101) (by omega)]
    by_cases h1:k-101<6
    · unfold singletonList
      rw [getD_append_left' (by simp;omega),getD_ofFn' _ (k-101) h1]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
    · unfold singletonList
      rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ ((k-101)-6) (by omega)]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
  have key:∀ (lay:Layer) (i:Nat),i<chainCount lay+height lay→layIdx lay+i=k→
      (sigDigests (sigDecC b)).getD k 0=digC b k := by
    intro lay i hi he
    subst he
    rw [sigDigests_layer _ lay i hi]
    unfold layerList
    by_cases hc:i<chainCount lay
    · rw [getD_append_left' (by simpa using hc),getD_ofFn' _ i hc];rfl
    · rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ (i-chainCount lay) (by omega)]
      change digC b (layIdx lay+chainCount lay+(i-chainCount lay))=_
      congr 1;omega
  by_cases h1:k<177
  · exact key 0 (k-114) (by rw [chainCount_0,height_0];omega) (by simp [layIdx];omega)
  by_cases h2:k<227
  · exact key 1 (k-177) (by rw [chainCount_1,height_1];omega) (by simp [layIdx];omega)
  by_cases h3:k<276
  · exact key 2 (k-227) (by rw [chainCount_2,height_2];omega) (by simp [layIdx];omega)
  · exact key 3 (k-276) (by rw [chainCount_3,height_3];omega) (by simp [layIdx];omega)

theorem topBits_lt (j : Nat) (hj : j ≤ 128) (d : Digest) : topBits j d < 2 ^ j := by
  unfold topBits
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show j + (128 - j) = 128 by omega]
  exact d.isLt

theorem topBits_zero (d : Digest) : topBits 0 d = 0 := by
  unfold topBits; exact Nat.div_eq_of_lt d.isLt

theorem xOfB_digit (b : CBytes) (j : Nat) (h1 : 1 ≤ j) (h10 : j ≤ 10) :
    xOfB b / 2 ^ xOff j % 2 ^ topZeroBits j = topBits (topZeroBits j) (cDig b (165 + j)) := by
  have t3 := topBits_lt 1 (by norm_num) (cDig b 168); have t4 := topBits_lt 1 (by norm_num) (cDig b 169)
  have t5 := topBits_lt 2 (by norm_num) (cDig b 170); have t6 := topBits_lt 3 (by norm_num) (cDig b 171)
  have t7 := topBits_lt 4 (by norm_num) (cDig b 172); have t8 := topBits_lt 5 (by norm_num) (cDig b 173)
  have t9 := topBits_lt 6 (by norm_num) (cDig b 174); have t10 := topBits_lt 7 (by norm_num) (cDig b 175)
  obtain ⟨o3, o4, o5, o6, o7, o8, o9, o10⟩ := xOff_vals
  unfold xOfB
  interval_cases j
  · rw [show topZeroBits 1 = 0 from rfl, topBits_zero]; exact Nat.mod_one _
  · rw [show topZeroBits 2 = 0 from rfl, topBits_zero]; exact Nat.mod_one _
  all_goals
    first
      | (rw [o3, show topZeroBits 3 = 1 from rfl]; norm_num at *; omega)
      | (rw [o4, show topZeroBits 4 = 1 from rfl]; norm_num at *; omega)
      | (rw [o5, show topZeroBits 5 = 2 from rfl]; norm_num at *; omega)
      | (rw [o6, show topZeroBits 6 = 3 from rfl]; norm_num at *; omega)
      | (rw [o7, show topZeroBits 7 = 4 from rfl]; norm_num at *; omega)
      | (rw [o8, show topZeroBits 8 = 5 from rfl]; norm_num at *; omega)
      | (rw [o9, show topZeroBits 9 = 6 from rfl]; norm_num at *; omega)
      | (rw [o10, show topZeroBits 10 = 7 from rfl]; norm_num at *; omega)

theorem xOfB_lt (b : CBytes) : xOfB b < 2 ^ 29 := by
  have t3 := topBits_lt 1 (by norm_num) (cDig b 168); have t4 := topBits_lt 1 (by norm_num) (cDig b 169)
  have t5 := topBits_lt 2 (by norm_num) (cDig b 170); have t6 := topBits_lt 3 (by norm_num) (cDig b 171)
  have t7 := topBits_lt 4 (by norm_num) (cDig b 172); have t8 := topBits_lt 5 (by norm_num) (cDig b 173)
  have t9 := topBits_lt 6 (by norm_num) (cDig b 174); have t10 := topBits_lt 7 (by norm_num) (cDig b 175)
  unfold xOfB
  norm_num at *
  omega

theorem xField_sigDecC (b : CBytes) : xField (sigDecC b) = xOfB b := by
  have hx := xOfB_lt b
  unfold xField
  rw [sigDigests_sigDecC b 176 (by decide)]
  change (digC b 176).toNat / 2 ^ 88 % 2 ^ 16 + (BitVec.ofNat 16 (xOfB b / 2 ^ 16)).toNat % 2 ^ 13 * 2 ^ 16 = _
  rw [digC, if_neg (by decide), if_pos rfl, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have ht := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 88 by positivity)
  have hlt : b.toNat / 2 ^ (128 * 324) % 2 ^ 88 + xOfB b % 2 ^ 16 * 2 ^ 88 < 2 ^ 128 := by
    have := Nat.mod_lt (xOfB b) (show 0 < 2 ^ 16 by positivity)
    norm_num at *
    omega
  rw [Nat.mod_eq_of_lt hlt]
  norm_num at *
  omega

theorem packD_clear (j : Nat) (hj : 1 ≤ j ∧ j ≤ 10) (c : Digest) (x : Nat)
    (hx : x / 2 ^ xOff j % 2 ^ topZeroBits j = topBits (topZeroBits j) c) :
    packD j (clearTop (topZeroBits j) c) x = c := by
  have hb := topZeroBits_le_eight j (by omega)
  apply BitVec.eq_of_toNat_eq
  unfold packD clearTop
  unfold topBits at hx
  rw [hx, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hm : c.toNat % 2 ^ (128 - topZeroBits j) < 2 ^ 128 :=
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.mod_eq_of_lt hm, Nat.mod_mod]
  have e := Nat.mod_add_div c.toNat (2 ^ (128 - topZeroBits j))
  rw [mul_comm] at e
  rw [e]
  exact Nat.mod_eq_of_lt c.isLt

theorem sigBC_sigDecC (b : CBytes) : sigBC (sigDecC b)=b := by
  apply BitVec.eq_of_toNat_eq
  rw [sigBC_toNat]
  have hD : digNat (encList (sigDecC b))=b.toNat%2^(128*324) := by
    apply digNat_eq_of_digits
    · rw [encList_length];exact Nat.mod_lt _ (by positivity)
    · intro k hk
      rw [encList_length] at hk
      rw [mod_digit _ 324 k hk, encList_getD _ k hk, getD_eraseIdx]
      by_cases hp : 166 ≤ k ∧ k ≤ 175
      · rw [if_pos hp, if_pos (by omega), sigDigests_sigDecC b k (by omega), xField_sigDecC]
        have hj : 1 ≤ k - 165 ∧ k - 165 ≤ 10 := by omega
        have hdig := xOfB_digit b (k - 165) hj.1 hj.2
        rw [show 165 + (k - 165) = k by omega] at hdig
        have hc : digC b k = clearTop (topZeroBits (k - 165)) (cDig b k) := by
          rw [digC, if_pos (by omega), if_pos (by omega)]
        rw [hc, packD_clear _ hj _ _ hdig, cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
      · rw [if_neg hp]
        split
        · rename_i hlt
          rw [sigDigests_sigDecC b k (by omega),digC,if_pos hlt,if_neg (by omega),cDig,BitVec.extractLsb'_toNat,
            Nat.shiftRight_eq_div_pow]
        · rename_i hge
          rw [sigDigests_sigDecC b (k+1) (by omega),digC,if_neg (by omega),if_neg (by omega),
            show k+1-1=k by omega,cDig,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  have hT : ((sigDigests (sigDecC b)).getD 176 0).toNat%2^88=b.toNat/2^(128*324)%2^88 := by
    rw [sigDigests_sigDecC b 176 (by decide),digC,if_neg (by decide),if_pos rfl,BitVec.toNat_ofNat]
    have hlt : b.toNat / 2 ^ (128 * 324) % 2 ^ 88 + xOfB b % 2 ^ 16 * 2 ^ 88 < 2 ^ 128 := by
      have := Nat.mod_lt (xOfB b) (show 0 < 2 ^ 16 by positivity)
      have := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 88 by positivity)
      norm_num at *
      omega
    rw [Nat.mod_eq_of_lt hlt, Nat.add_mul_mod_self_right, Nat.mod_mod]
  rw [hD,hT]
  have hb : b.toNat / 2 ^ (128 * 324) < 2 ^ 88 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact b.isLt
  rw [Nat.mod_eq_of_lt hb]
  exact Nat.mod_add_div _ _
end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Research.SharedForest

theorem normalizeV6_fill (sig : SharedSignature) (c : Nat) :
    normalizeV6 (fillTopSignature sig c) = normalizeV6 sig := by
  unfold normalizeV6 fillTopSignature
  congr 1
  funext lay
  congr 1
  funext j
  simp only [ClaudeWCT.WCT9.fillLayer]
  split
  · rename_i h
    obtain ⟨hl, hj⟩ := h
    have : lay = 0 := Fin.ext hl
    subst this
    have hidx : layIdx 0 + SigGolfCandidate.T3.chainCount 0 + j.val = 176 := by
      simp [layIdx, SigGolfCandidate.T3.chainCount, hj]
    rw [hidx]
    unfold normD
    rw [if_neg (by decide), if_pos rfl, if_neg (by decide), if_pos rfl, ClaudeWCT.WCT9.setTop_toNat]
    congr 1
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 104 ≤ 112)),
      show c % 2 ^ 16 * 2 ^ 112 % 2 ^ 104 = 0 from
        Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by norm_num)) _), add_zero, Nat.mod_mod]
  · rfl

theorem sigBC_fillTopSignature (sig : SharedSignature) (c : Nat) :
    sigBC (fillTopSignature sig c) = sigBC sig := by
  calc
    sigBC (fillTopSignature sig c) = sigBC (sigDecC (sigBC (fillTopSignature sig c))) := (sigBC_sigDecC _).symm
    _ = sigBC (normalizeV6 (fillTopSignature sig c)) := by rw [sigDecC_sigBC]
    _ = sigBC (normalizeV6 sig) := by rw [normalizeV6_fill]
    _ = sigBC (sigDecC (sigBC sig)) := by rw [sigDecC_sigBC]
    _ = sigBC sig := sigBC_sigDecC _


theorem layIdx_ge (l : SigGolfCandidate.T3.Layer) (h : l.val ≠ 0) : 177 ≤ layIdx l := by
  revert h; revert l; decide

/-- The codec's normal form is the normal form `SharedForest.normTop` that `expand` applies first. -/
theorem normalizeV6_eq_normTop (s : SharedSignature) : normalizeV6 s = normTop s := by
  unfold normalizeV6 normTop
  congr 1
  funext lay
  unfold normLayer
  congr 1
  funext j
  by_cases h0 : lay.val = 0
  · have hl : lay = 0 := Fin.ext h0
    subst hl
    rw [if_pos (show ((0 : SigGolfCandidate.T3.Layer) : Nat) = 0 from rfl)]
    have hk : layIdx 0 + SigGolfCandidate.T3.chainCount 0 + j.val = 165 + j.val := rfl
    rw [hk]
    unfold normD normPathD clearTop
    rw [show 165 + j.val - 165 = j.val by omega]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [if_neg h0]
    apply normD_of_out
    right
    have := layIdx_ge lay h0
    omega

/-- img-v6 codec round trip in the form used by the final pipeline. -/
theorem sigDecC_sigBC_normTop (s : SharedSignature) : sigDecC (sigBC s) = normTop s :=
  (sigDecC_sigBC s).trans (normalizeV6_eq_normTop s)

end ClaudeWCT.W9.T3M.SharedCodec

/-! ## T51 decoded-signature facts (KEYCODEC, round 2)

The expander's decoder DEC (words 54569..54738) writes digest `k` of the 5,195-byte signature at slot
`internalFullIndex k` (16 bytes per slot from `0x7000`), zero at the dummy slots (`internalDummy`), and the hint
`xOfB b / 2^16` at `0x66000`. `fill_sigDecC`: the decoded signature has its brute-forced field (top sibling bits
112..127) clear. The `inflatedRead_*` lemmas read the slot layout back without letting the kernel unfold `digC` against
`inflatedRead` (that comparison blows up on T51's `digC`). -/
namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

/-- T51: the decoded top sibling (digest 176) is below `2^104` (bits 104..111 zero-test, 112..127 filled by expand). -/
theorem digC_176_lt (b : CBytes) : (digC b 176).toNat < 2 ^ 104 := by
  rw [digC, if_neg (by decide), if_pos rfl, BitVec.toNat_ofNat]
  have h1 := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 88 by positivity)
  have h2 := Nat.mod_lt (xOfB b) (show 0 < 2 ^ 16 by positivity)
  have hlt : b.toNat / 2 ^ (128 * 324) % 2 ^ 88 + xOfB b % 2 ^ 16 * 2 ^ 88 < 2 ^ 104 := by
    norm_num at *
    omega
  rw [Nat.mod_eq_of_lt (lt_trans hlt (by norm_num))]
  exact hlt

/-- T51: the decoded signature has its brute-forced top-sibling field (bits 112..127) clear. -/
theorem fill_sigDecC (b : CBytes) : fillTopSignature (sigDecC b) 0 = sigDecC b := by
  have hl : (fun lay => ClaudeWCT.WCT9.fillLayer lay ((sigDecC b).layers lay) 0) = (sigDecC b).layers := by
    funext lay
    have hp : (fun j : Fin (height lay) => if lay.val = 0 ∧ j.val = 11 then
        ClaudeWCT.WCT9.setTop (((sigDecC b).layers lay).path j) 0 else ((sigDecC b).layers lay).path j) =
        ((sigDecC b).layers lay).path := by
      funext j
      split
      · rename_i h
        obtain ⟨hl0, hj⟩ := h
        have : lay = 0 := Fin.ext hl0
        subst this
        apply BitVec.eq_of_toNat_eq
        rw [ClaudeWCT.WCT9.setTop_toNat]
        change (digC b (layIdx 0 + chainCount 0 + j.val)).toNat % 2 ^ 112 + 0 % 2 ^ 16 * 2 ^ 112 =
          (digC b (layIdx 0 + chainCount 0 + j.val)).toNat
        have hidx : layIdx 0 + chainCount 0 + j.val = 176 := by
          simp [layIdx, chainCount, hj]
        rw [hidx, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
        exact Nat.mod_eq_of_lt (lt_trans (digC_176_lt b) (by norm_num))
      · rfl
    unfold ClaudeWCT.WCT9.fillLayer
    rw [hp]
  unfold fillTopSignature
  rw [hl]

/-- T51: the decoded policy hints are the top 13 bits of the 29-bit X field. -/
theorem policyHints_sigDecC_toNat (b : CBytes) : (sigDecC b).policyHints.toNat = xOfB b / 2 ^ 16 := by
  change (BitVec.ofNat 16 (xOfB b / 2 ^ 16)).toNat = _
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := xOfB_lt b
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num at *
  omega

theorem policyHints_sigDecC_lt (b : CBytes) : (sigDecC b).policyHints.toNat < 2 ^ 13 := by
  rw [policyHints_sigDecC_toNat]
  have := xOfB_lt b
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num at *
  omega

/-! ### The slot layout (`internalFullIndex`) read back through `inflatedRead` -/

theorem inflatedRead_main {α : Type} (z : α) (read : Nat → α) (k : Nat) (hk : 114 ≤ k) (hk' : k ≤ 176) :
    inflatedRead z read (k + 4) = read k := by
  rw [← internalFullIndex_main k hk hk', inflatedRead_internal]

theorem inflatedRead_lower {α : Type} (z : α) (read : Nat → α) (k : Nat) (hk : 177 ≤ k) :
    inflatedRead z read (k + 7) = read k := by
  rw [← internalFullIndex_lower k hk, inflatedRead_internal]

/-- Slot 0 is `rho` (stated through `inflatedRead_internal`, so the kernel never unfolds `digC` against `inflatedRead`). -/
theorem inflatedRead_rho (b : CBytes) : inflatedRead (0 : Digest) (digC b) 0 = (sigDecC b).rho :=
  inflatedRead_internal (0 : Digest) (digC b) 0

theorem inflatedRead_dummy {α : Type} (z : α) (read : Nat → α) (k : Nat) (hk : internalDummy k = true) :
    inflatedRead z read k = z := by
  unfold inflatedRead; rw [if_pos hk]

theorem externalFullIndex_lt (k : Nat) (hk : k < 332) (hd : internalDummy k = false) : externalFullIndex k < 325 := by
  simp only [internalDummy, decide_eq_false_iff_not] at hd
  unfold externalFullIndex
  split_ifs <;> omega

theorem internalFullIndex_external (k : Nat) (hd : internalDummy k = false) :
    internalFullIndex (externalFullIndex k) = k := by
  simp only [internalDummy, decide_eq_false_iff_not] at hd
  unfold internalFullIndex externalFullIndex
  split_ifs <;> omega

end ClaudeWCT.W9.T3M.SharedCodec
end
-- ==== merged from Rv_Tactic ====
section

namespace SigGolfCandidate.Rv
open Lean Meta Elab Tactic Command
unsafe def evalOptResultUnsafe (e : Expr) : MetaM (Option Result) :=
  evalExpr (Option Result) (mkApp (mkConst ``Option [0]) (mkConst ``Result)) e
@[implemented_by evalOptResultUnsafe]
opaque evalOptResult (e : Expr) : MetaM (Option Result)
unsafe def evalExprExprUnsafe (e : Expr) : MetaM Expr := evalExpr Expr (mkConst ``Expr) e
@[implemented_by evalExprExprUnsafe]
opaque evalExprExpr (e : Expr) : MetaM Expr
def evalToLiteral (lhs : Expr) : MetaM Expr := do
  let lhs ← instantiateMVars lhs
  if lhs.hasFVar || lhs.hasMVar then
    throwError "sym_eval: the left-hand side must be a closed term, got{indentExpr lhs}"
  let α ← inferType lhs
  let u ← getLevel α
  let some u' := u.dec | throwError "sym_eval: type must live in `Type u`"
  let inst ← synthInstance (mkApp (mkConst ``Lean.ToExpr [u']) α)
  evalExprExpr (mkApp3 (mkConst ``Lean.toExpr [u']) α inst lhs)
def kernelEq (lhs lit : Expr) : MetaM Expr := do
  let ty ← mkEq lhs lit
  let pf ← mkEqRefl lit
  let name ← mkAuxLemma [] ty pf
  return mkConst name
elab "sym_eval" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := t.eq? | throwError "sym_eval: goal is not an equation"
  let lit ← evalToLiteral lhs
  unless ← isDefEq rhs lit do
    throwError "sym_eval: result mismatch; the computation returned{indentExpr lit}"
  goal.assign (← kernelEq lhs lit)
  replaceMainGoal []
section Shared
open Std
abbrev ShareM := StateM (HashMap USize Expr)
unsafe def eToExprShared (e : E) : ShareM Expr := do
  let key := ptrAddrUnsafe e
  if let some x := (← get).get? key then return x
  let x ← match e with
    | .c _ | .reg _ => pure (toExpr e)
    | .ld a => do pure (mkApp (mkConst ``E.ld) (← eToExprShared a))
    | .un op a => do pure (mkApp2 (mkConst ``E.un) (toExpr op) (← eToExprShared a))
    | .bin op a b => do
      pure (mkApp3 (mkConst ``E.bin) (toExpr op) (← eToExprShared a) (← eToExprShared b))
    | .ite op x y a b => do
      pure (mkApp5 (mkConst ``E.ite) (toExpr op) (← eToExprShared x) (← eToExprShared y)
        (← eToExprShared a) (← eToExprShared b))
  modify (·.insert key x)
  return x
unsafe def addrToExprShared (a : Addr) : ShareM Expr := do
  let b ← match a.base with
    | none => pure (mkApp (mkConst ``Option.none [0]) (mkConst ``E))
    | some b => do
      let x ← eToExprShared b
      pure (mkApp2 (mkConst ``Option.some [0]) (mkConst ``E) x)
  return mkApp2 (mkConst ``Addr.mk) b (toExpr a.off)
unsafe def obligToExprShared : Oblig → ShareM Expr
  | .valid a w => return mkApp2 (mkConst ``Oblig.valid) (← addrToExprShared a) (toExpr w)
  | .align8 b => return mkApp (mkConst ``Oblig.align8) (← eToExprShared b)
  | .ne a b => return mkApp2 (mkConst ``Oblig.ne) (← addrToExprShared a) (← addrToExprShared b)
def listLit (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc)
    (mkApp (mkConst ``List.nil [0]) ty)
unsafe def resultToExprSharedM (r : Result) : ShareM Expr := do
  let regs ← r.st.regs.fields.mapM eToExprShared
  let regsE := mkAppN (mkConst ``RegFile.mk) regs.toArray
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Addr) (mkConst ``E)
  let mem ← r.st.mem.mapM fun (k, v) => do
    return mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Addr) (mkConst ``E)
      (← addrToExprShared k) (← eToExprShared v)
  let obl ← r.st.obl.mapM obligToExprShared
  let st := mkApp3 (mkConst ``SymState.mk) regsE (listLit pairTy mem)
    (listLit (mkConst ``Oblig) obl)
  return mkApp5 (mkConst ``Result.mk) st (← eToExprShared r.pc) (toExpr r.stop)
    (toExpr r.steps) (toExpr r.cycles)
unsafe def resultToExprSharedUnsafe (r : Result) : Expr :=
  (resultToExprSharedM r).run' {}
@[implemented_by resultToExprSharedUnsafe]
opaque resultToExprShared (r : Result) : Expr
end Shared
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := t.eq? | throwError "kernel_rfl: goal is not an equation"
  if t.hasFVar || t.hasMVar then throwError "kernel_rfl: goal must be closed"
  let pf ← mkEqRefl lhs
  let name ← mkAuxLemma [] t (← mkExpectedTypeHint pf t)
  let _ := rhs
  goal.assign (mkConst name)
  replaceMainGoal []
elab "sym_block " id:ident " := " t:term : command => do
  liftTermElabM do
    let e ← Term.elabTermEnsuringType t (mkApp (mkConst ``Option [0]) (mkConst ``Result))
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasFVar || e.hasMVar then
      throwError "sym_block: the executor call must be a closed term"
    let v ← evalOptResult e
    let some r := v | throwError "sym_block: symbolic execution returned `none`{indentExpr e}"
    let base := (← getCurrNamespace) ++ id.getId
    let resName := base ++ `res
    addDecl <| Declaration.defnDecl {
      name := resName, levelParams := [], type := mkConst ``Result, value := resultToExprShared r,
      hints := .abbrev, safety := .safe }
    enableRealizationsForConst resName
    compileDecls #[resName]
    let lit := mkApp2 (mkConst ``Option.some [0]) (mkConst ``Result) (mkConst resName)
    let ty ← mkEq e lit
    let pf ← mkEqRefl lit
    addDecl <| Declaration.thmDecl { name := base, levelParams := [], type := ty, value := pf }
    enableRealizationsForConst base
end SigGolfCandidate.Rv
end
