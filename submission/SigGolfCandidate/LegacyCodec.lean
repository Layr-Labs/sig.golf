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
set_option linter.all false

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

theorem stageHistogram_lower (lay : Layer) (hl : lay ≠ 0) :
    stageHistogram lay.val = pathSplit (CanonicalPolicy.lowerBonus lay) lowerCounts := by
  fin_cases lay
  · exact absurd rfl hl
  · rfl
  · rfl
  · rfl

/-- The path-aware lower selection law (P0: the histogram of stage `lay`, LOW bonus `lowerBonus lay`). -/
theorem selected_lower_histogram_card
    (hd : ∀ (z : Fin 6) (i : Nat), i<128 →
      SharedDigitBlock.digit (2^132) SigGolfResearch.LowerEffectiveCounting.packed
        (65536*z.val+128*201+i) = lowerFiberN z.val i)
    (hcheck : lowerHistogramCheck = true)
    (lay : Layer) (hl : lay ≠ 0) (floor c : Nat) (hf : floor ≤ c) (hc : c < 128) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut lay floor answer = some dl ∧
        CanonicalPolicy.credit lay dl.2 dl.1 = c).card = histogramWeight (stageHistogram lay.val) c * 2^126 := by
  rw [selected_lower_path_card lay hl floor c hf, stageHistogram_lower lay hl, pathSplit, histogramWeight_split,
    lower_counts_of_check hd hcheck ⟨c, hc⟩]
  by_cases h4 : CanonicalPolicy.lowerBonus lay ≤ c
  · rw [if_pos h4, if_pos h4, lower_counts_of_check hd hcheck ⟨c - CanonicalPolicy.lowerBonus lay, by omega⟩]
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
      (histogramWeight (stageHistogram lay.val) c : ENNReal) / lowerDen := by
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

def rcPar : Par := ⟨812, (11 / 20 : ℚ), (51 / 5 : ℚ), (31934263 / 16000000 : ℚ), (93650 / 100000 : ℚ), (78112 / 10000000 : ℚ), (883810 / 10000000 : ℚ)⟩

def runs0 : List (ℕ × ℕ × ℕ) := [(0, 3877, 18446744073709551616), (3878, 3878, 18306125131558236066), (3879, 3879, 18124876367879441649), (3880, 3880, 17945422146415288762), (3881, 3881, 17767744699421077982), (3882, 3882, 17591826435070374240), (3883, 3883, 17417649935713241821), (3884, 3884, 17245197956151724576), (3885, 3885, 17074453421932400570), (3886, 3886, 16905399427655842149), (3887, 3887, 16738019235302814008), (3888, 3888, 16572296272577043573), (3889, 3889, 16408214131264399577), (3890, 3890, 16245756565608316413), (3891, 3891, 16084907490701303379), (3892, 3892, 15925650980892379583), (3893, 3893, 15767971268210276815), (3894, 3894, 15611852740802254272), (3895, 3895, 15457279941388370567), (3896, 3896, 15304237565731059967), (3897, 3897, 15152710461119861353), (3898, 3898, 15002683624871149855), (3899, 3899, 14854142202842722629), (3900, 3900, 14707071487963091712), (3901, 3901, 14561456918775338328), (3902, 3902, 14417284077995384483), (3903, 3903, 14274538691084539093), (3904, 3904, 14133206624836177319), (3905, 3905, 13993273885976413187), (3906, 3906, 13854726619778626918), (3907, 3907, 13717551108691709820), (3908, 3908, 13581733770981890911), (3909, 3909, 13447261159388010803), (3910, 3910, 13314119959790109706), (3911, 3911, 13182296989891197729), (3912, 3912, 13051779197912076959), (3913, 3913, 12922553661299086098), (3914, 3914, 12794607585444639701), (3915, 3915, 12667928302420435348), (3916, 3916, 12542503269723203314), (3917, 3917, 12418320069032874569), (3918, 3918, 12295366404983044127), (3919, 3919, 12173630103943608047), (3920, 3920, 12053099112815453512), (3921, 3921, 11933761497837082685), (3922, 3922, 11815605443403052163), (3923, 3923, 11698619250894111053), (3924, 3924, 11582791337518921835), (3925, 3925, 11468110235167249341), (3926, 3926, 11354564589274504298), (3927, 3927, 11242143157697529008), (3928, 3928, 11130834809601513869), (3929, 3929, 11020628524357934524), (3930, 3930, 10911513390453400519), (3931, 3931, 10803478604409307445), (3932, 3932, 10696513469712185589), (3933, 3933, 10590607395754639197), (3934, 3934, 10485749896786771482), (3935, 3935, 10381930590877991566), (3936, 3936, 10279139198889100561), (3937, 3937, 10177365543454555011), (3938, 3938, 10076599547974806941), (3939, 3939, 9976831235618620734), (3940, 3940, 9878050728335268053), (3941, 3941, 9780248245876503023), (3942, 3942, 9683414104828220815), (3943, 3943, 9587538717651703777), (3944, 3944, 9492612591734360175), (3945, 3945, 9398626328449861560), (3946, 3946, 9305570622227585703), (3947, 3947, 9213436259631272973), (3948, 3948, 9122214118446804924), (3949, 3949, 9031895166779014776), (3950, 3950, 8942470462157440372), (3951, 3951, 8853931150650931062), (3952, 3952, 8766268465991020853), (3953, 3953, 8679473728703981043), (3954, 3954, 8593538345251466379), (3955, 3955, 8508453807179669682), (3956, 3956, 8424211690276900675), (3957, 3957, 8340803653739505619), (3958, 3958, 8258221439346045168), (3959, 3959, 8176456870639648681), (3960, 3960, 8095501852118464040), (3961, 3961, 8015348368434122812), (3962, 3962, 7935988483598141398), (3963, 3963, 7857414340196179602), (3964, 3964, 7779618158610078814), (3965, 3965, 7702592236247602786), (3966, 3966, 7626328946779804739), (3967, 3967, 7550820739385945286), (3968, 3968, 7476060138005886422), (3969, 3969, 7402039740599887546), (3970, 3970, 7328752218415730244), (3971, 3971, 7256190315263099251), (3972, 3972, 7184346846795147774), (3973, 3973, 7113214699797176014), (3974, 3974, 7042786831482352489), (3975, 3975, 6973056268794408405), (3976, 3976, 6904016107717236044), (3977, 3977, 6835659512591322816), (3978, 3978, 6767979715436953283), (3979, 3979, 6700970015284112162), (3980, 3980, 6634623777509021942), (3981, 3981, 6568934433177249448), (3982, 3982, 6503895478393316285), (3983, 3983, 6439500473656748797), (3984, 3984, 6375743043224503759), (3985, 3985, 6312616874479706692), (3986, 3986, 6250115717306640290), (3987, 3987, 6188233383471921079), (3988, 3988, 6126963746011803048), (3989, 3989, 6066300738625547573), (3990, 3990, 6006238355074799577), (3991, 3991, 5946770648588910472), (3992, 3992, 5887891731276148982), (3993, 3993, 5829595773540741567), (3994, 3994, 5771877003505684719), (3995, 3995, 5714729706441271999), (3996, 3996, 5658148224199279207), (3997, 3997, 5602126954652751690), (3998, 3998, 5546660351141338307), (3999, 3999, 5491742921922117136), (4000, 4000, 5437369229625858550), (4001, 4001, 5383533890718671832), (4002, 4002, 5330231574968982012), (4003, 4003, 5277457004919784170), (4004, 4004, 5225204955366122941), (4005, 4005, 5173470252837745486), (4006, 4006, 5122247775086876719), (4007, 4007, 5071532450581066058), (4008, 4008, 5021319258001055503), (4009, 4009, 4971603225743619310), (4010, 4010, 4922379431429326050), (4011, 4011, 4873643001415174307), (4012, 4012, 4825389110312053769), (4013, 4013, 4777612980506983930), (4014, 4014, 4730309881690083099), (4015, 4015, 4683475130386220890), (4016, 4016, 4637104089491307812), (4017, 4017, 4591192167813176051), (4018, 4018, 4545734819617005991), (4019, 4019, 4500727544175253457), (4020, 4020, 4456165885322033125), (4021, 4021, 4412045431011913986), (4022, 4022, 4368361812883083154), (4023, 4023, 4325110705824834806), (4024, 4024, 4282287827549341392), (4025, 4025, 4239888938167664745), (4026, 4026, 4197909839769965094), (4027, 4027, 4156346376009866429), (4028, 4028, 4115194431692937059), (4029, 4029, 4074449932369244613), (4030, 4030, 4034108843929945161), (4031, 4031, 3994167172207866496), (4032, 4032, 3954620962582046036), (4033, 4033, 3915466299586184194), (4034, 4034, 3876699306520974449), (4035, 4035, 3838316145070271732), (4036, 4036, 3800313014921061121), (4037, 4037, 3762686153387189229), (4038, 4038, 3725431835036821018), (4039, 4039, 3688546371323585167), (4040, 4040, 3652026110221371452), (4041, 4041, 3615867435862744012), (4042, 4042, 3580066768180934665), (4043, 4043, 3544620562555380857), (4044, 4044, 3509525309460773126), (4045, 4045, 3474777534119577352), (4046, 4046, 3440373796157997378), (4047, 4047, 3406310689265343939), (4048, 4048, 3372584840856776177), (4049, 4049, 3339192911739382354), (4050, 4050, 3306131595781566687), (4051, 4051, 3273397619585709591), (4052, 4052, 3240987742164068902), (4053, 4053, 3208898754617890002), (4054, 4054, 3177127479819693071), (4055, 4055, 3145670772098706011), (4056, 4056, 3114525516929411892), (4057, 4057, 3083688630623180091), (4058, 4058, 3053157060022950585), (4059, 4059, 3022927782200941174), (4060, 4060, 2992997804159347697), (4061, 4061, 2963364162534007621), (4062, 4062, 2934023923300997644), (4063, 4063, 2904974181486136281), (4064, 4064, 2876212060877362655), (4065, 4065, 2847734713739963024), (4066, 4066, 2819539320534616856), (4067, 4067, 2791623089638234511), (4068, 4068, 2763983257067558922), (4069, 4069, 2736617086205503883), (4070, 4070, 2709521867530201864), (4071, 4071, 2682694918346734519), (4072, 4072, 2656133582521519326), (4073, 4073, 2629835230219326065), (4074, 4074, 2603797257642897094), (4075, 4075, 2578017086775145638), (4076, 4076, 2552492165123906572), (4077, 4077, 2527219965469214428), (4078, 4078, 2502197985613083592), (4079, 4079, 2477423748131765933), (4080, 4080, 2452894800130461319), (4081, 4081, 2428608713000456752), (4082, 4082, 2404563082178670051), (4083, 4083, 2380755526909574308), (4084, 4084, 2357183690009479513), (4085, 4085, 2333845237633148033), (4086, 4086, 2310737859042720825), (4087, 4087, 2287859266378931509), (4088, 4088, 2265207194434585653), (4089, 4089, 2242779400430282825), (4090, 4090, 2220573663792359232), (4091, 4091, 2198587785933028943), (4092, 4092, 2176819590032701924), (4093, 4093, 2155266920824457350), (4094, 4094, 2133927644380650842), (4095, 4095, 2112799647901634497), (4096, 4096, 2091880839506568809), (4097, 4097, 2071169148026305751), (4098, 4098, 2050662522798322526), (4099, 4099, 2030358933463685669), (4100, 4100, 2010256369766025415), (4101, 4101, 1990352841352500411), (4102, 4102, 1970646377576733080), (4103, 4103, 1951135027303696119), (4104, 4104, 1931816858716530811), (4105, 4105, 1912689959125278031), (4106, 4106, 1893752434777503001), (4107, 4107, 1875002410670795050), (4108, 4108, 1856438030367123812), (4109, 4109, 1838057455809033477), (4110, 4110, 1819858867137656908), (4111, 4111, 1801840462512531592), (4112, 4112, 1784000457933199596), (4113, 4113, 1766337087062573858), (4114, 4114, 1748848601052053325), (4115, 4115, 1731533268368369628), (4116, 4116, 1714389374622148147), (4117, 4117, 1697415222398166482), (4118, 4118, 1680609131087293547), (4119, 4119, 1663969436720092620), (4120, 4120, 1647494491802071901), (4121, 4121, 1631182665150566239), (4122, 4122, 1615032341733233900), (4123, 4123, 1599041922508152376), (4124, 4124, 1583209824265497402), (4125, 4125, 1567534479470789507), (4126, 4126, 1552014336109692581), (4127, 4127, 1536647857534349090), (4128, 4128, 1521433522311236723), (4129, 4129, 1506369824070531409), (4130, 4130, 1491455271356961791), (4131, 4131, 1476688387482140387), (4132, 4132, 1462067710378356819), (4133, 4133, 1447591792453818633), (4134, 4134, 1433259200449325379), (4135, 4135, 1419068515296361761), (4136, 4136, 1405018331976595803), (4137, 4137, 1391107259382768122), (4138, 4138, 1377333920180958537), (4139, 4139, 1363696950674216373), (4140, 4140, 1350195000667540963), (4141, 4141, 1336826733334198974), (4142, 4142, 1323590825083365321), (4143, 4143, 1310485965429074575), (4144, 4144, 1297510856860469876), (4145, 4145, 1284664214713336511), (4146, 4146, 1271944767042907437), (4147, 4147, 1259351254497928155), (4148, 4148, 1246882430195968470), (4149, 4149, 1234537059599968782), (4150, 4150, 1222313920396008696), (4151, 4151, 1210211802372285837), (4152, 4152, 1198229507299292908), (4153, 4153, 1186365848811181097), (4154, 4154, 1174619652288298116), (4155, 4155, 1162989754740889224), (4156, 4156, 1151475004693949726), (4157, 4157, 1140074262073217551), (4158, 4158, 1128786398092294605), (4159, 4159, 1117610295140885747), (4160, 4160, 1106544846674144304), (4161, 4161, 1095588957103113173), (4162, 4162, 1084741541686250666), (4163, 4163, 1074001526422030362), (4164, 4164, 1063367847942604319), (4165, 4165, 1052839453408519128), (4166, 4166, 1042415300404474384), (4167, 4167, 1032094356836113252), (4168, 4168, 1021875600827834903), (4169, 4169, 1011758020621618715), (4170, 4170, 1001740614476850213), (4171, 4171, 991822390571138825), (4172, 4172, 982002366902117649), (4173, 4173, 972279571190215494), (4174, 4174, 962653040782391578), (4175, 4175, 953121822556823344), (4176, 4176, 943684972828537965), (4177, 4177, 934341557255978183), (4178, 4178, 925090650748493250), (4179, 4179, 915931337374745793), (4180, 4180, 906862710272025537), (4181, 4181, 897883871556460928), (4182, 4182, 888993932234119731), (4183, 4183, 880192012112989832), (4184, 4184, 871477239715831517), (4185, 4185, 862848752193892591), (4186, 4186, 854305695241477813), (4187, 4187, 845847223011364171), (4188, 4188, 837472498031053635), (4189, 4189, 829180691119855084), (4190, 4190, 820970981306787212), (4191, 4191, 812842555749294269), (4192, 4192, 804794609652766603), (4193, 4193, 796826346190858023), (4194, 4194, 788936976426592102), (4195, 4195, 781125719234249606), (4196, 4196, 773391801222029313), (4197, 4197, 765734456655474567), (4198, 4198, 758152927381657987), (4199, 4199, 750646462754116819), (4200, 4200, 743214319558531504), (4201, 4201, 735855761939140103), (4202, 4202, 728570061325881290), (4203, 4203, 721356496362258703), (4204, 4204, 714214352833919508), (4205, 4205, 707142923597940107), (4206, 4206, 700141508512811987), (4207, 4207, 693209414369120779), (4208, 4208, 686345954820911663), (4209, 4209, 679550450317734320), (4210, 4210, 672822228037360712), (4211, 4211, 666160621819169022), (4212, 4212, 659564972098187151), (4213, 4213, 653034625839789258), (4214, 4214, 646568936475038870), (4215, 4215, 640167263836672148), (4216, 4216, 633828974095714998), (4217, 4217, 627553439698727721), (4218, 4218, 621340039305671011), (4219, 4219, 615188157728387139), (4220, 4220, 609097185869690237), (4221, 4221, 603066520663059641), (4222, 4222, 597095565012930337), (4223, 4223, 591183727735574591), (4224, 4224, 585330423500568902), (4225, 4225, 579535072772840497), (4226, 4226, 573797101755287621), (4227, 4227, 568115942331967942), (4228, 4228, 562491032011849447), (4229, 4229, 556921813873118265), (4230, 4230, 551407736508037886), (4231, 4231, 545948253968354342), (4232, 4232, 540542825711241923), (4233, 4233, 535190916545784082), (4234, 4234, 529891996579984240), (4235, 4235, 524645541168301228), (4236, 4236, 519451030859704186), (4237, 4237, 514307951346241768), (4238, 4238, 509215793412120562), (4239, 4239, 504174052883287686), (4240, 4240, 499182230577512560), (4241, 4241, 494239832254962931), (4242, 4242, 489346368569270228), (4243, 4243, 484501355019079434), (4244, 4244, 479704311900078648), (4245, 4245, 474954764257503612), (4246, 4246, 470252241839112487), (4247, 4247, 465596279048626224), (4248, 4248, 460986414899629925), (4249, 4249, 456422192969930619), (4250, 4250, 451903161356366950), (4251, 4251, 447428872630066287), (4252, 4252, 442998883792144838), (4253, 4253, 438612756229846375), (4254, 4254, 434270055673115222), (4255, 4255, 429970352151599230), (4256, 4256, 425713219952078446), (4257, 4257, 421498237576315293), (4258, 4258, 417324987699322072), (4259, 4259, 413193057128041655), (4260, 4260, 409102036760437283), (4261, 4261, 405051521544987408), (4262, 4262, 401041110440581593), (4263, 4263, 397070406376813458), (4264, 4264, 393139016214666790), (4265, 4265, 389246550707590881), (4266, 4266, 385392624462961269), (4267, 4267, 381576855903922048), (4268, 4268, 377798867231605988), (4269, 4269, 374058284387728701), (4270, 4270, 370354737017553170), (4271, 4271, 366687858433220960), (4272, 4272, 363057285577446495), (4273, 4273, 359462658987570787), (4274, 4274, 355903622759971076), (4275, 4275, 352379824514822848), (4276, 4276, 348890915361210741), (4277, 4277, 345436549862584892), (4278, 4278, 342016386002559299), (4279, 4279, 338630085151048811), (4280, 4280, 335277312030741397), (4281, 4281, 331957734683902373), (4282, 4282, 328671024439507300), (4283, 4283, 325416855880700297), (4284, 4284, 322194906812574551), (4285, 4285, 319004858230271833), (4286, 4286, 315846394287397855), (4287, 4287, 312719202264750351), (4288, 4288, 309622972539356783), (4289, 4289, 306557398553818597), (4290, 4290, 303522176785959007), (4291, 4291, 300517006718771294), (4292, 4292, 297541590810664648), (4293, 4293, 294595634466004602), (4294, 4294, 291678846005945150), (4295, 4295, 288790936639549654), (4296, 4296, 285931620435197677), (4297, 4297, 283100614292274928), (4298, 4298, 280297637913143493), (4299, 4299, 277522413775389597), (4300, 4300, 274774667104346135), (4301, 4301, 272054125845887263), (4302, 4302, 269360520639492339), (4303, 4303, 266693584791576574), (4304, 4304, 264053054249085717), (4305, 4305, 261438667573352195), (4306, 4306, 258850165914210094), (4307, 4307, 256287292984366429), (4308, 4308, 253749795034026168), (4309, 4309, 251237420825768483), (4310, 4310, 248749921609671765), (4311, 4311, 246287051098684916), (4312, 4312, 243848565444242491), (4313, 4313, 241434223212121278), (4314, 4314, 239043785358535919), (4315, 4315, 236677015206471207), (4316, 4316, 234333678422248720), (4317, 4317, 232013542992325465), (4318, 4318, 229716379200322243), (4319, 4319, 227441959604279448), (4320, 4320, 225190059014138068), (4321, 4321, 222960454469443631), (4322, 4322, 220752925217270922), (4323, 4323, 218567252690367250), (4324, 4324, 216403220485512128), (4325, 4325, 214260614342091216), (4326, 4326, 212139222120882392), (4327, 4327, 210038833783051874), (4328, 4328, 207959241369358291), (4329, 4329, 205900238979562664), (4330, 4330, 203861622752042242), (4331, 4331, 201843190843606180), (4332, 4332, 199844743409511069), (4333, 4333, 197866082583674326), (4334, 4334, 195907012459083491), (4335, 4335, 193967339068399496), (4336, 4336, 192046870364751976), (4337, 4337, 190145416202724729), (4338, 4338, 188262788319529435), (4339, 4339, 186398800316365777), (4340, 4340, 184553267639966116), (4341, 4341, 182726007564322887), (4342, 4342, 180916839172596918), (4343, 4343, 179125583339204869), (4344, 4344, 177352062712084029), (4345, 4345, 175596101695132702), (4346, 4346, 173857526430824457), (4347, 4347, 172136164782994512), (4348, 4348, 170431846319796547), (4349, 7209, 168744402296828264)]

def glob0 : ℕ := 18446744073709551616

def runs1 : List (ℕ × ℕ × ℕ) := [(0, 3000, 1869034792061467), (3001, 3001, 1887725139982082), (3002, 3002, 1906602391381902), (3003, 3003, 1925668415295721), (3004, 3004, 1944925099448679), (3005, 3005, 1964374350443165), (3006, 3006, 1984018093947597), (3007, 3007, 2003858274887073), (3008, 3008, 2023896857635944), (3009, 3009, 2044135826212303), (3010, 3010, 2064577184474426), (3011, 3011, 2085222956319170), (3012, 3012, 2106075185882362), (3013, 3013, 2127135937741186), (3014, 3014, 2148407297118598), (3015, 3015, 2169891370089784), (3016, 3016, 2191590283790681), (3017, 3017, 2213506186628588), (3018, 3018, 2235641248494874), (3019, 3019, 2257997660979823), (3020, 3020, 2280577637589621), (3021, 3021, 2303383413965517), (3022, 3022, 2326417248105172), (3023, 3023, 2349681420586224), (3024, 3024, 2373178234792086), (3025, 3025, 2396910017140007), (3026, 3026, 2420879117311407), (3027, 3027, 2445087908484521), (3028, 3028, 2469538787569367), (3029, 3029, 2494234175445060), (3030, 3030, 2519176517199511), (3031, 3031, 2544368282371506), (3032, 3032, 2569811965195221), (3033, 3033, 2595510084847173), (3034, 3034, 2621465185695645), (3035, 3035, 2647679837552601), (3036, 3036, 2674156635928127), (3037, 3037, 2700898202287409), (3038, 3038, 2727907184310283), (3039, 3039, 2755186256153386), (3040, 3040, 2782738118714919), (3041, 3041, 2810565499902069), (3042, 3042, 2838671154901089), (3043, 3043, 2867057866450100), (3044, 3044, 2895728445114601), (3045, 3045, 2924685729565747), (3046, 3046, 2953932586861405), (3047, 3047, 2983471912730019), (3048, 3048, 3013306631857319), (3049, 3049, 3043439698175892), (3050, 3050, 3073874095157651), (3051, 3051, 3104612836109228), (3052, 3052, 3135658964470320), (3053, 3053, 3167015554115023), (3054, 3054, 3198685709656173), (3055, 3055, 3230672566752735), (3056, 3056, 3262979292420262), (3057, 3057, 3295609085344465), (3058, 3058, 3328565176197910), (3059, 3059, 3361850827959889), (3060, 3060, 3395469336239488), (3061, 3061, 3429424029601882), (3062, 3062, 3463718269897901), (3063, 3063, 3498355452596880), (3064, 3064, 3533339007122849), (3065, 3065, 3568672397194078), (3066, 3066, 3604359121166018), (3067, 3067, 3640402712377678), (3068, 3068, 3676806739501455), (3069, 3069, 3713574806896470), (3070, 3070, 3750710554965434), (3071, 3071, 3788217660515089), (3072, 3072, 3826099837120240), (3073, 3073, 3864360835491442), (3074, 3074, 3903004443846357), (3075, 3075, 3942034488284820), (3076, 3076, 3981454833167668), (3077, 3077, 4021269381499345), (3078, 3078, 4061482075314338), (3079, 3079, 4102096896067482), (3080, 3080, 4143117865028157), (3081, 3081, 4184549043678438), (3082, 3082, 4226394534115223), (3083, 3083, 4268658479456375), (3084, 3084, 4311345064250938), (3085, 3085, 4354458514893448), (3086, 3086, 4398003100042382), (3087, 3087, 4441983131042806), (3088, 3088, 4486402962353234), (3089, 3089, 4531266991976767), (3090, 3090, 4576579661896534), (3091, 3091, 4622345458515500), (3092, 3092, 4668568913100655), (3093, 3093, 4715254602231661), (3094, 3094, 4762407148253978), (3095, 3095, 4810031219736517), (3096, 3096, 4858131531933883), (3097, 3097, 4906712847253221), (3098, 3098, 4955779975725754), (3099, 3099, 5005337775483011), (3100, 3100, 5055391153237841), (3101, 3101, 5105945064770220), (3102, 3102, 5157004515417922), (3103, 3103, 5208574560572101), (3104, 3104, 5260660306177822), (3105, 3105, 5313266909239600), (3106, 3106, 5366399578331996), (3107, 3107, 5420063574115316), (3108, 3108, 5474264209856469), (3109, 3109, 5529006851955034), (3110, 3110, 5584296920474584), (3111, 3111, 5640139889679330), (3112, 3112, 5696541288576124), (3113, 3113, 5753506701461885), (3114, 3114, 5811041768476504), (3115, 3115, 5869152186161269), (3116, 3116, 5927843708022881), (3117, 3117, 5987122145103110), (3118, 3118, 6046993366554141), (3119, 3119, 6107463300219683), (3120, 3120, 6168537933221880), (3121, 3121, 6230223312554098), (3122, 3122, 6292525545679639), (3123, 3123, 6355450801136436), (3124, 3124, 6419005309147800), (3125, 3125, 6483195362239278), (3126, 3126, 6548027315861671), (3127, 3127, 6613507589020287), (3128, 3128, 6679642664910490), (3129, 3129, 6746439091559595), (3130, 3130, 6813903482475191), (3131, 3131, 6882042517299943), (3132, 3132, 6950862942472943), (3133, 3133, 7020371571897672), (3134, 3134, 7090575287616649), (3135, 3135, 7161481040492815), (3136, 3136, 7233095850897743), (3137, 3137, 7305426809406721), (3138, 3138, 7378481077500788), (3139, 3139, 7452265888275796), (3140, 3140, 7526788547158554), (3141, 3141, 7602056432630139), (3142, 3142, 7678076996956441), (3143, 3143, 7754857766926005), (3144, 3144, 7832406344595265), (3145, 3145, 7910730408041218), (3146, 3146, 7989837712121630), (3147, 3147, 8069736089242846), (3148, 3148, 8150433450135275), (3149, 3149, 8231937784636627), (3150, 3150, 8314257162482994), (3151, 3151, 8397399734107824), (3152, 3152, 8481373731448902), (3153, 3153, 8566187468763391), (3154, 3154, 8651849343451025), (3155, 3155, 8738367836885535), (3156, 3156, 8825751515254390), (3157, 3157, 8914009030406934), (3158, 3158, 9003149120711004), (3159, 3159, 9093180611918114), (3160, 3160, 9184112418037295), (3161, 3161, 9275953542217668), (3162, 3162, 9368713077639844), (3163, 3163, 9462400208416243), (3164, 3164, 9557024210500405), (3165, 3165, 9652594452605409), (3166, 3166, 9749120397131463), (3167, 3167, 9846611601102778), (3168, 3168, 9945077717113806), (3169, 3169, 10044528494284944), (3170, 3170, 10144973779227793), (3171, 3171, 10246423517020071), (3172, 3172, 10348887752190272), (3173, 3173, 10452376629712175), (3174, 3174, 10556900396009296), (3175, 3175, 10662469399969389), (3176, 3176, 10769094093969083), (3177, 3177, 10876785034908774), (3178, 3178, 10985552885257862), (3179, 3179, 11095408414110440), (3180, 3180, 11206362498251545), (3181, 3181, 11318426123234060), (3182, 3182, 11431610384466401), (3183, 3183, 11545926488311065), (3184, 3184, 11661385753194175), (3185, 3185, 11777999610726117), (3186, 3186, 11895779606833378), (3187, 3187, 12014737402901712), (3188, 3188, 12134884776930729), (3189, 3189, 12256233624700037), (3190, 3190, 12378795960947037), (3191, 3191, 12502583920556507), (3192, 3192, 12627609759762072), (3193, 3193, 12753885857359693), (3194, 3194, 12881424715933290), (3195, 3195, 13010238963092623), (3196, 3196, 13140341352723549), (3197, 3197, 13271744766250785), (3198, 3198, 13404462213913292), (3199, 3199, 13538506836052425), (3200, 3200, 13673891904412950), (3201, 3201, 13810630823457079), (3202, 3202, 13948737131691650), (3203, 3203, 14088224503008566), (3204, 3204, 14229106748038652), (3205, 3205, 14371397815519039), (3206, 3206, 14515111793674229), (3207, 3207, 14660262911610971), (3208, 3208, 14806865540727081), (3209, 3209, 14954934196134352), (3210, 3210, 15104483538095695), (3211, 3211, 15255528373476652), (3212, 3212, 15408083657211419), (3213, 3213, 15562164493783533), (3214, 3214, 15717786138721368), (3215, 3215, 15874964000108582), (3216, 3216, 16033713640109668), (3217, 3217, 16194050776510764), (3218, 3218, 16355991284275872), (3219, 3219, 16519551197118631), (3220, 3220, 16684746709089817), (3221, 3221, 16851594176180715), (3222, 3222, 17020110117942522), (3223, 3223, 17190311219121948), (3224, 3224, 17362214331313167), (3225, 3225, 17535836474626299), (3226, 3226, 17711194839372562), (3227, 3227, 17888306787766287), (3228, 3228, 18067189855643950), (3229, 3229, 18247861754200390), (3230, 3230, 18430340371742394), (3231, 3231, 18614643775459818), (3232, 3232, 18800790213214416), (3233, 3233, 18988798115346560), (3234, 3234, 19178686096500025), (3235, 3235, 19370472957465026), (3236, 3236, 19564177687039676), (3237, 3237, 19759819463910073), (3238, 3238, 19957417658549173), (3239, 3239, 20156991835134665), (3240, 3240, 20358561753486012), (3241, 3241, 20562147371020872), (3242, 3242, 20767768844731081), (3243, 3243, 20975446533178391), (3244, 3244, 21185200998510175), (3245, 3245, 21397053008495277), (3246, 3246, 21611023538580230), (3247, 3247, 21827133773966032), (3248, 3248, 22045405111705692), (3249, 3249, 22265859162822749), (3250, 3250, 22488517754450977), (3251, 3251, 22713402931995487), (3252, 3252, 22940536961315441), (3253, 3253, 23169942330928596), (3254, 3254, 23401641754237882), (3255, 3255, 23635658171780261), (3256, 3256, 23872014753498063), (3257, 3257, 24110734901033044), (3258, 3258, 24351842250043374), (3259, 3259, 24595360672543808), (3260, 3260, 24841314279269246), (3261, 3261, 25089727422061939), (3262, 3262, 25340624696282558), (3263, 3263, 25594030943245384), (3264, 3264, 25849971252677837), (3265, 3265, 26108470965204616), (3266, 3266, 26369555674856662), (3267, 3267, 26633251231605229), (3268, 3268, 26899583743921281), (3269, 3269, 27168579581360494), (3270, 3270, 27440265377174099), (3271, 3271, 27714668030945840), (3272, 3272, 27991814711255298), (3273, 3273, 28271732858367851), (3274, 3274, 28554450186951529), (3275, 3275, 28839994688821045), (3276, 3276, 29128394635709255), (3277, 3277, 29419678582066348), (3278, 3278, 29713875367887011), (3279, 3279, 30011014121565881), (3280, 3280, 30311124262781540), (3281, 3281, 30614235505409355), (3282, 3282, 30920377860463449), (3283, 3283, 31229581639068083), (3284, 3284, 31541877455458764), (3285, 3285, 31857296230013352), (3286, 3286, 32175869192313485), (3287, 3287, 32497627884236620), (3288, 3288, 32822604163078986), (3289, 3289, 33150830204709776), (3290, 3290, 33482338506756874), (3291, 3291, 33817161891824443), (3292, 3292, 34155333510742687), (3293, 3293, 34496886845850114), (3294, 3294, 34841855714308615), (3295, 3295, 35190274271451701), (3296, 3296, 35542177014166218), (3297, 3297, 35897598784307881), (3298, 3298, 36256574772150959), (3299, 3299, 36619140519872469), (3300, 3300, 36985331925071194), (3301, 3301, 37355185244321906), (3302, 3302, 37728737096765125), (3303, 3303, 38106024467732776), (3304, 3304, 38487084712410104), (3305, 3305, 38871955559534205), (3306, 3306, 39260675115129547), (3307, 3307, 39653281866280842), (3308, 3308, 40049814684943651), (3309, 3309, 40450312831793087), (3310, 3310, 40854815960111018), (3311, 3311, 41263364119712128), (3312, 3312, 41675997760909249), (3313, 3313, 42092757738518342), (3314, 3314, 42513685315903525), (3315, 3315, 42938822169062561), (3316, 3316, 43368210390753186), (3317, 3317, 43801892494660718), (3318, 3318, 44239911419607325), (3319, 3319, 44682310533803398), (3320, 3320, 45129133639141432), (3321, 3321, 45580424975532847), (3322, 3322, 46036229225288175), (3323, 3323, 46496591517541057), (3324, 3324, 46961557432716468), (3325, 3325, 47431173007043632), (3326, 3326, 47905484737114069), (3327, 3327, 48384539584485209), (3328, 3328, 48868384980330061), (3329, 3329, 49357068830133362), (3330, 3330, 49850639518434696), (3331, 3331, 50349145913619042), (3332, 3332, 50852637372755233), (3333, 3333, 51361163746482785), (3334, 3334, 51874775383947613), (3335, 3335, 52393523137787089), (3336, 3336, 52917458369164960), (3337, 3337, 53446632952856610), (3338, 3338, 53981099282385176), (3339, 3339, 54520910275209028), (3340, 3340, 55066119377961118), (3341, 3341, 55616780571740729), (3342, 3342, 56172948377458136), (3343, 3343, 56734677861232718), (3344, 3344, 57302024639845045), (3345, 3345, 57875044886243495), (3346, 3346, 58453795335105930), (3347, 3347, 59038333288456989), (3348, 3348, 59628716621341559), (3349, 3349, 60225003787554975), (3350, 3350, 60827253825430525), (3351, 3351, 61435526363684830), (3352, 3352, 62049881627321678), (3353, 3353, 62670380443594895), (3354, 3354, 63297084248030844), (3355, 3355, 63930055090511152), (3356, 3356, 64569355641416264), (3357, 3357, 65215049197830427), (3358, 3358, 65867199689808731), (3359, 3359, 66525871686706818), (3360, 3360, 67191130403573886), (3361, 3361, 67863041707609625), (3362, 3362, 68541672124685721), (3363, 3363, 69227088845932579), (3364, 3364, 69919359734391904), (3365, 3365, 70618553331735823), (3366, 3366, 71324738865053182), (3367, 3367, 72037986253703713), (3368, 3368, 72758366116240751), (3369, 3369, 73485949777403158), (3370, 3370, 74220809275177190), (3371, 3371, 74963017367928962), (3372, 3372, 75712647541608251), (3373, 3373, 76469774017024334), (3374, 3374, 77234471757194577), (3375, 3375, 78006816474766523), (3376, 3376, 78786884639514188), (3377, 3377, 79574753485909330), (3378, 3378, 80370501020768423), (3379, 3379, 81174206030976107), (3380, 3380, 81985948091285868), (3381, 3381, 82805807572198727), (3382, 3382, 83633865647920714), (3383, 3383, 84470204304399922), (3384, 3384, 85314906347443921), (3385, 3385, 86168055410918360), (3386, 3386, 87029735965027544), (3387, 3387, 87900033324677819), (3388, 3388, 88779033657924597), (3389, 3389, 89666823994503843), (3390, 3390, 90563492234448882), (3391, 3391, 91469127156793370), (3392, 3392, 92383818428361304), (3393, 3393, 93307656612644917), (3394, 3394, 94240733178771366), (3395, 3395, 95183140510559080), (3396, 3396, 96134971915664671), (3397, 3397, 97096321634821317), (3398, 3398, 98067284851169531), (3399, 3399, 99047957699681226), (3400, 3400, 100038437276678038), (3401, 3401, 101038821649444819), (3402, 3402, 102049209865939267), (3403, 3403, 103069701964598659), (3404, 3404, 104100398984244646), (3405, 3405, 105141402974087092), (3406, 3406, 106192817003827963), (3407, 3407, 107254745173866243), (3408, 3408, 108327292625604905), (3409, 3409, 109410565551860954), (3410, 3410, 110504671207379564), (3411, 3411, 111609717919453360), (3412, 3412, 112725815098647893), (3413, 3413, 113853073249634372), (3414, 3414, 114991603982130716), (3415, 3415, 116141520021952023), (3416, 3416, 117302935222171543), (3417, 3417, 118475964574393259), (3418, 3418, 119660724220137191), (3419, 3419, 120857331462338563), (3420, 3420, 122065904776961949), (3421, 3421, 123286563824731568), (3422, 3422, 124519429462978884), (3423, 3423, 125764623757608673), (3424, 3424, 127022269995184759), (3425, 3425, 128292492695136607), (3426, 3426, 129575417622087973), (3427, 3427, 130871171798308853), (3428, 3428, 132179883516291941), (3429, 3429, 133501682351454861), (3430, 3430, 134836699174969409), (3431, 3431, 136185066166719103), (3432, 3432, 137546916828386294), (3433, 3433, 138922385996670157), (3434, 3434, 140311609856636859), (3435, 3435, 141714725955203228), (3436, 3436, 143131873214755260), (3437, 3437, 144563191946902812), (3438, 3438, 146008823866371841), (3439, 3439, 147468912105035559), (3440, 3440, 148943601226085915), (3441, 3441, 150433037238346774), (3442, 3442, 151937367610730241), (3443, 3443, 153456741286837544), (3444, 3444, 154991308699705919), (3445, 3445, 156541221786702978), (3446, 3446, 158106634004570008), (3447, 3447, 159687700344615708), (3448, 3448, 161284577348061865), (3449, 3449, 162897423121542484), (3450, 3450, 164526397352757909), (3451, 3451, 166171661326285488), (3452, 3452, 167833377939548343), (3453, 3453, 169511711718943826), (3454, 3454, 171206828836133265), (3455, 3455, 172918897124494597), (3456, 3456, 174648086095739543), (3457, 3457, 176394566956696939), (3458, 3458, 178158512626263908), (3459, 3459, 179940097752526547), (3460, 3460, 181739498730051812), (3461, 3461, 183556893717352331), (3462, 3462, 185392462654525854), (3463, 3463, 187246387281071112), (3464, 3464, 189118851153881824), (3465, 3465, 191010039665420642), (3466, 3466, 192920140062074848), (3467, 3467, 194849341462695597), (3468, 3468, 196797834877322553), (3469, 3469, 198765813226095778), (3470, 3470, 200753471358356736), (3471, 3471, 202761006071940303), (3472, 3472, 204788616132659706), (3473, 3473, 206836502293986303), (3474, 3474, 208904867316926166), (3475, 3475, 210993915990095428), (3476, 3476, 213103855149996382), (3477, 3477, 215234893701496346), (3478, 3478, 217387242638511310), (3479, 3479, 219561115064896423), (3480, 3480, 221756726215545387), (3481, 3481, 223974293477700841), (3482, 3482, 226214036412477849), (3483, 3483, 228476176776602628), (3484, 3484, 230760938544368654), (3485, 3485, 233068547929812340), (3486, 3486, 235399233409110464), (3487, 3487, 237753225743201569), (3488, 3488, 240130758000633584), (3489, 3489, 242532065580639920), (3490, 3490, 244957386236446319), (3491, 3491, 247406960098810782), (3492, 3492, 249881029699798890), (3493, 3493, 252379839996796879), (3494, 3494, 254903638396764848), (3495, 3495, 257452674780732496), (3496, 3496, 260027201528539821), (3497, 3497, 262627473543825220), (3498, 3498, 265253748279263472), (3499, 3499, 267906285762056106), (3500, 3500, 270585348619676668), (3501, 3501, 273291202105873434), (3502, 3502, 276024114126932169), (3503, 3503, 278784355268201490), (3504, 3504, 281572198820883505), (3505, 3505, 284387920809092340), (3506, 3506, 287231800017183264), (3507, 3507, 290104118017355096), (3508, 3508, 293005159197528647), (3509, 3509, 295935210789503934), (3510, 3510, 298894562897398973), (3511, 3511, 301883508526372963), (3512, 3512, 304902343611636692), (3513, 3513, 307951367047753059), (3514, 3514, 311030880718230590), (3515, 3515, 314141189525412896), (3516, 3516, 317282601420667025), (3517, 3517, 320455427434873695), (3518, 3518, 323659981709222432), (3519, 3519, 326896581526314656), (3520, 3520, 330165547341577803), (3521, 3521, 333467202814993581), (3522, 3522, 336801874843143516), (3523, 3523, 340169893591574952), (3524, 3524, 343571592527490701), (3525, 3525, 347007308452765608), (3526, 3526, 350477381537293264), (3527, 3527, 353982155352666197), (3528, 3528, 357521976906192859), (3529, 3529, 361097196675254787), (3530, 3530, 364708168642007335), (3531, 3531, 368355250328427409), (3532, 3532, 372038802831711683), (3533, 3533, 375759190860028800), (3534, 3534, 379516782768629088), (3535, 3535, 383311950596315378), (3536, 3536, 387145070102278532), (3537, 3537, 391016520803301318), (3538, 3538, 394926686011334331), (3539, 3539, 398875952871447674), (3540, 3540, 402864712400162151), (3541, 3541, 406893359524163772), (3542, 3542, 410962293119405410), (3543, 3543, 415071916050599464), (3544, 3544, 419222635211105459), (3545, 3545, 423414861563216513), (3546, 3546, 427649010178848678), (3547, 3547, 431925500280637165), (3548, 3548, 436244755283443537), (3549, 3549, 440607202836277972), (3550, 3550, 445013274864640752), (3551, 3551, 449463407613287159), (3552, 3552, 453958041689420031), (3553, 3553, 458497622106314231), (3554, 3554, 463082598327377374), (3555, 3555, 467713424310651147), (3556, 3556, 472390558553757659), (3557, 3557, 477114464139295235), (3558, 3558, 481885608780688188), (3559, 3559, 486704464868495070), (3560, 3560, 491571509517180020), (3561, 3561, 496487224612351820), (3562, 3562, 501452096858475339), (3563, 3563, 506466617827060092), (3564, 3564, 511531284005330693), (3565, 3565, 516646596845384000), (3566, 3566, 521813062813837840), (3567, 3567, 527031193441976218), (3568, 3568, 532301505376395980), (3569, 3569, 537624520430159940), (3570, 3570, 543000765634461540), (3571, 3571, 548430773290806155), (3572, 3572, 553915081023714217), (3573, 3573, 559454231833951359), (3574, 3574, 565048774152290872), (3575, 3575, 570699261893813781), (3576, 3576, 576406254512751919), (3577, 3577, 582170317057879438), (3578, 3578, 587992020228458232), (3579, 3579, 593871940430742815), (3580, 3580, 599810659835050243), (3581, 3581, 605808766433400745), (3582, 3582, 611866854097734753), (3583, 3583, 617985522638712100), (3584, 3584, 624165377865099221), (3585, 3585, 630407031643750213), (3586, 3586, 636711101960187716), (3587, 3587, 643078212979789593), (3588, 3588, 649508995109587489), (3589, 3589, 656004085060683364), (3590, 3590, 662564125911290197), (3591, 3591, 669189767170403099), (3592, 3592, 675881664842107130), (3593, 3593, 682640481490528201), (3594, 3594, 689466886305433483), (3595, 3595, 696361555168487818), (3596, 3596, 703325170720172696), (3597, 3597, 710358422427374423), (3598, 3598, 717462006651648168), (3599, 3599, 724636626718164649), (3600, 3600, 731882992985346296), (3601, 3601, 739201822915199759), (3602, 3602, 746593841144351756), (3603, 3603, 754059779555795274), (3604, 3604, 761600377351353227), (3605, 3605, 769216381124866759), (3606, 3606, 776908544936115427), (3607, 3607, 784677630385476581), (3608, 3608, 792524406689331347), (3609, 3609, 800449650756224660), (3610, 3610, 808454147263786907), (3611, 3611, 816538688736424776), (3612, 3612, 824704075623789023), (3613, 3613, 832951116380026914), (3614, 3614, 841280627543827183), (3615, 3615, 849693433819265455), (3616, 3616, 858190368157458109), (3617, 3617, 866772271839032690), (3618, 3618, 875439994557423017), (3619, 3619, 884194394502997247), (3620, 3620, 893036338448027220), (3621, 3621, 901966701832507492), (3622, 3622, 910986368850832567), (3623, 3623, 920096232539340893), (3624, 3624, 929297194864734301), (3625, 3625, 938590166813381644), (3626, 3626, 947976068481515461), (3627, 3627, 957455829166330616), (3628, 3628, 967030387457993922), (3629, 3629, 976700691332573861), (3630, 3630, 986467698245899599), (3631, 3631, 996332375228358595), (3632, 3632, 1006295698980642181), (3633, 3633, 1016358655970448603), (3634, 3634, 1026522242530153089), (3635, 3635, 1036787464955454620), (3636, 3636, 1047155339605009166), (3637, 3637, 1057626893001059258), (3638, 3638, 1068203161931069851), (3639, 3639, 1078885193550380549), (3640, 3640, 1089674045485884355), (3641, 3641, 1100570785940743198), (3642, 3642, 1111576493800150630), (3643, 3643, 1122692258738152136), (3644, 3644, 1133919181325533658), (3645, 3645, 1145258373138788994), (3646, 3646, 1156710956870176884), (3647, 3647, 1168278066438878653), (3648, 3648, 1179960847103267440), (3649, 3649, 1191760455574300114), (3650, 3650, 1203678060130043115), (3651, 3651, 1215714840731343546), (3652, 3652, 1227871989138656982), (3653, 3653, 1240150709030043552), (3654, 3654, 1252552216120343987), (3655, 3655, 1265077738281547427), (3656, 3656, 1277728515664362901), (3657, 3657, 1290505800821006530), (3658, 3658, 1303410858829216596), (3659, 3659, 1316444967417508761), (3660, 3660, 1329609417091683849), (3661, 3661, 1342905511262600688), (3662, 3662, 1356334566375226694), (3663, 3663, 1369897912038978961), (3664, 3664, 1383596891159368751), (3665, 3665, 1397432860070962438), (3666, 3666, 1411407188671672063), (3667, 3667, 1425521260558388783), (3668, 3668, 1439776473163972671), (3669, 3669, 1454174237895612398), (3670, 3670, 1468715980274568522), (3671, 3671, 1483403140077314207), (3672, 3672, 1498237171478087349), (3673, 3673, 1513219543192868223), (3674, 3674, 1528351738624796905), (3675, 3675, 1543635256011044874), (3676, 3676, 1559071608571155323), (3677, 3677, 1574662324656866876), (3678, 3678, 1590408947903435545), (3679, 3679, 1606313037382469900), (3680, 3680, 1622376167756294599), (3681, 3681, 1638599929433857545), (3682, 3682, 1654985928728196121), (3683, 3683, 1671535788015478082), (3684, 3684, 1688251145895632863), (3685, 3685, 1705133657354589191), (3686, 3686, 1722184993928135083), (3687, 3687, 1739406843867416434), (3688, 3688, 1756800912306090598), (3689, 3689, 1774368921429151504), (3690, 3690, 1792112610643443019), (3691, 3691, 1810033736749877450), (3692, 3692, 1828134074117376224), (3693, 3693, 1846415414858549986), (3694, 3694, 1864879569007135486), (3695, 3695, 1883528364697206841), (3696, 3696, 1902363648344178909), (3697, 3697, 1921387284827620698), (3698, 3698, 1940601157675896905), (3699, 3699, 1960007169252655874), (3700, 3700, 1979607240945182433), (3701, 3701, 1999403313354634258), (3702, 3702, 2019397346488180600), (3703, 3703, 2039591319953062406), (3704, 3704, 2059987233152593030), (3705, 3705, 2080587105484118960), (3706, 3706, 2101392976538960150), (3707, 3707, 2122406906304349752), (3708, 3708, 2143630975367393249), (3709, 3709, 2165067285121067182), (3710, 3710, 2186717957972277853), (3711, 3711, 2208585137552000632), (3712, 3712, 2230670988927520638), (3713, 3713, 2252977698816795845), (3714, 3714, 2275507475804963803), (3715, 3715, 2298262550563013441), (3716, 3716, 2321245176068643575), (3717, 3717, 2344457627829330011), (3718, 3718, 2367902204107623311), (3719, 3719, 2391581226148699544), (3720, 3720, 2415497038410186540), (3721, 3721, 2439652008794288405), (3722, 3722, 2464048528882231289), (3723, 3723, 2488689014171053602), (3724, 3724, 2513575904312764138), (3725, 3725, 2538711663355891780), (3726, 3726, 2564098779989450697), (3727, 3727, 2589739767789345204), (3728, 3728, 2615637165467238656), (3729, 3729, 2641793537121911043), (3730, 3730, 2668211472493130153), (3731, 3731, 2694893587218061455), (3732, 3732, 2721842523090242069), (3733, 3733, 2749060948321144490), (3734, 3734, 2776551557804355935), (3735, 3735, 2804317073382399494), (3736, 3736, 2832360244116223489), (3737, 3737, 2860683846557385724), (3738, 3738, 2889290685022959581), (3739, 3739, 2918183591873189177), (3740, 3740, 2947365427791921069), (3741, 3741, 2976839082069840280), (3742, 3742, 3006607472890538683), (3743, 3743, 3036673547619444069), (3744, 3744, 3067040283095638510), (3745, 3745, 3097710685926594895), (3746, 3746, 3128687792785860844), (3747, 3747, 3159974670713719453), (3748, 3748, 3191574417420856647), (3749, 3749, 3223490161595065213), (3750, 3750, 3255725063211015866), (3751, 3751, 3288282313843126024), (3752, 3752, 3321165136981557285), (3753, 3753, 3354376788351372857), (3754, 3754, 3387920556234886586), (3755, 3755, 3421799761797235452), (3756, 3756, 3456017759415207806), (3757, 3757, 3490577937009359884), (3758, 3758, 3525483716379453483), (3759, 3759, 3560738553543248018), (3760, 3760, 3596345939078680498), (3761, 3761, 3632309398469467303), (3762, 3762, 3668632492454161976), (3763, 3763, 3705318817378703596), (3764, 3764, 3742372005552490632), (3765, 3765, 3779795725608015538), (3766, 3766, 3817593682864095694), (3767, 3767, 3855769619692736651), (3768, 3768, 3894327315889664017), (3769, 3769, 3933270589048560657), (3770, 3770, 3972603294939046264), (3771, 3771, 4012329327888436726), (3772, 3772, 4052452621167321094), (3773, 3773, 4092977147378994305), (3774, 3774, 4133906918852784248), (3775, 3775, 4175245988041312090), (3776, 3776, 4216998447921725211), (3777, 3777, 4259168432400942463), (3778, 3778, 4301760116724951888), (3779, 3779, 4344777717892201407), (3780, 3780, 4388225495071123421), (3781, 3781, 4432107750021834655), (3782, 3782, 4476428827522053001), (3783, 3783, 4521193115797273531), (3784, 3784, 4566405046955246267), (3785, 3785, 4612069097424798729), (3786, 3786, 4658189788399046717), (3787, 3787, 4704771686283037184), (3788, 3788, 4751819403145867556), (3789, 3789, 4799337597177326231), (3790, 3790, 4847330973149099494), (3791, 3791, 4895804282880590488), (3792, 3792, 4944762325709396393), (3793, 3793, 4994209948966490357), (3794, 3794, 5044152048456155261), (3795, 3795, 5094593568940716813), (3796, 3796, 5145539504630123982), (3797, 3797, 5196994899676425221), (3798, 3798, 5248964848673189474), (3799, 3799, 5301454497159921368), (3800, 3800, 5354469042131520582), (3801, 3801, 5408013732552835788), (3802, 3802, 5462093869878364146), (3803, 3803, 5516714808577147787), (3804, 3804, 5571881956662919265), (3805, 3805, 5627600776229548458), (3806, 3806, 5683876783991843942), (3807, 3807, 5740715551831762382), (3808, 3808, 5798122707350080005), (3809, 3809, 5856103934423580805), (3810, 3810, 5914664973767816614), (3811, 3811, 5973811623505494780), (3812, 3812, 6033549739740549727), (3813, 3813, 6093885237137955225), (3814, 3814, 6154824089509334777), (3815, 3815, 6216372330404428125), (3816, 3816, 6278536053708472406), (3817, 3817, 6341321414245557130), (3818, 3818, 6404734628388012701), (3819, 3819, 6468781974671892828), (3820, 3820, 6533469794418611757), (3821, 3821, 6598804492362797874), (3822, 3822, 6664792537286425853), (3823, 3823, 6731440462659290111), (3824, 3824, 6798754867285883013), (3825, 3825, 6866742415958741843), (3826, 3826, 6935409840118329261), (3827, 3827, 7004763938519512554), (3828, 3828, 7074811577904707679), (3829, 3829, 7145559693683754756), (3830, 3830, 7217015290620592304), (3831, 3831, 7289185443526798227), (3832, 3832, 7362077297962066209), (3833, 3833, 7435698070941686871), (3834, 3834, 7510055051651103740), (3835, 3835, 7585155602167614777), (3836, 3836, 7661007158189290925), (3837, 3837, 7737617229771183834), (3838, 3838, 7814993402068895672), (3839, 3839, 7893143336089584629), (3840, 3840, 7972074769450480475), (3841, 3841, 8051795517144985280), (3842, 3842, 8132313472316435133), (3843, 3843, 8213636607039599484), (3844, 3844, 8295772973109995479), (3845, 3845, 8378730702841095434), (3846, 3846, 8462518009869506388), (3847, 3847, 8547143189968201452), (3848, 3848, 8632614621867883467), (3849, 3849, 8718940768086562301), (3850, 3850, 8806130175767427924), (3851, 3851, 8894191477525102203), (3852, 3852, 8983133392300353226), (3853, 3853, 9072964726223356758), (3854, 3854, 9163694373485590325), (3855, 3855, 9255331317220446229), (3856, 3856, 9347884630392650691), (3857, 3857, 9441363476696577198), (3858, 3858, 9535777111463542970), (3859, 3859, 9631134882578178399), (3860, 3860, 9727446231403960183), (3861, 3861, 9824720693717999785), (3862, 3862, 9922967900655179783), (3863, 3863, 10022197579661731581), (3864, 3864, 10122419555458348897), (3865, 3877, 10145709240540253389), (3878, 3878, 10068368822357029836), (3879, 3879, 9968682002333692907), (3880, 3880, 9869982180528408819), (3881, 3881, 9772259584681592890), (3882, 3882, 9675504539288705832), (3883, 3883, 9579707464642283002), (3884, 3884, 9484858875883448517), (3885, 3885, 9390949382062820314), (3886, 3886, 9297969685210713182), (3887, 3887, 9205910579416547705), (3888, 3888, 9114762949917373965), (3889, 3889, 9024517772195419768), (3890, 3890, 8935166111084574027), (3891, 3891, 8846699119885716859), (3892, 3892, 8759108039490808771), (3893, 3893, 8672384197515652249), (3894, 3894, 8586519007441239850), (3895, 3895, 8501503967763603812), (3896, 3896, 8417330661152082982), (3897, 3897, 8333990753615923745), (3898, 3898, 8251475993679132420), (3899, 3899, 8169778211563497446), (3900, 3900, 8088889318379700442), (3901, 3901, 8008801305326436081), (3902, 3902, 7929506242897461466), (3903, 3903, 7850996280096496501), (3904, 3904, 7773263643659897526), (3905, 3905, 7696300637287027253), (3906, 3906, 7620099640878244805), (3907, 3907, 7544653109780440401), (3908, 3908, 7469953574040040001), (3909, 3909, 7395993637663405942), (3910, 3910, 7322765977884560338), (3911, 3911, 7250263344440158751), (3912, 3912, 7178478558851642328), (3913, 3913, 7107404513714497354), (3914, 3914, 7037034171994551836), (3915, 3915, 6967360566331239441), (3916, 3916, 6898376798347761823), (3917, 3917, 6830076037968081013), (3918, 3918, 6762451522740674270), (3919, 3919, 6695496557168984426), (3920, 3920, 6629204512048499432), (3921, 3921, 6563568823810395477), (3922, 3922, 6498582993871678690), (3923, 3923, 6434240587991761079), (3924, 3924, 6370535235635407009), (3925, 3925, 6307460629341987138), (3926, 3926, 6245010524100977364), (3927, 3927, 6183178736733640955), (3928, 3928, 6121959145280832628), (3929, 3929, 6061345688396863989), (3930, 3930, 6001332364749370286), (3931, 3931, 5941913232425119095), (3932, 3932, 5883082408341702074), (3933, 3933, 5824834067665051558), (3934, 3934, 5767162443232724315), (3935, 3935, 5710061824982895362), (3936, 3936, 5653526559389005309), (3937, 3937, 5597551048900005256), (3938, 3938, 5542129751386143818), (3939, 3939, 5487257179590241404), (3940, 3940, 5432927900584397430), (3941, 3941, 5379136535232076663), (3942, 3942, 5325877757655521448), (3943, 3943, 5273146294708437078), (3944, 3944, 5220936925453898097), (3945, 3945, 5169244480647423858), (3946, 3946, 5118063842225172137), (3947, 3947, 5067389942797200135), (3948, 3948, 5017217765145742708), (3949, 3949, 4967542341728458127), (3950, 3950, 4918358754186592205), (3951, 3951, 4869662132858012084), (3952, 3952, 4821447656295061469), (3953, 3953, 4773710550787189574), (3954, 3954, 4726446089888306509), (3955, 3955, 4679649593948818325), (3956, 3956, 4633316429652295372), (3957, 3957, 4587442009556728091), (3958, 3958, 4542021791640324842), (3959, 3959, 4497051278851806775), (3960, 3960, 4452526018665155222), (3961, 3961, 4408441602638767547), (3962, 3962, 4364793665978977769), (3963, 3963, 4321577887107898781), (3964, 3964, 4278789987235543348), (3965, 3965, 4236425729936181533), (3966, 3966, 4194480920728892607), (3967, 3967, 4152951406662269908), (3968, 3968, 4111833075903237532), (3969, 3969, 4071121857329938151), (3970, 3970, 4030813720128651634), (3971, 3971, 3990904673394704589), (3972, 3972, 3951390765737331276), (3973, 3973, 3912268084888446808), (3974, 3974, 3873532757315293869), (3975, 3975, 3835180947836924623), (3976, 3976, 3797208859244479825), (3977, 3977, 3759612731925227549), (3978, 3978, 3722388843490324306), (3979, 3979, 3685533508406261689), (3980, 3980, 3649043077629962068), (3981, 3981, 3612913938247487196), (3982, 3982, 3577142513116323957), (3983, 3983, 3541725260511211839), (3984, 3984, 3506658673773477068), (3985, 3985, 3471939280963838681), (3986, 3986, 3437563644518652159), (3987, 3987, 3403528360909556594), (3988, 3988, 3369830060306491677), (3989, 3989, 3336465406244051165), (3990, 3990, 3303431095291139767), (3991, 3991, 3270723856723900760), (3992, 3992, 3238340452201881940), (3993, 3993, 3206277675447407862), (3994, 3994, 3174532351928126596), (3995, 3995, 3143101338542699600), (3996, 3996, 3111981523309603564), (3997, 3997, 3081169825059013430), (3998, 3998, 3050663193127736069), (3999, 3999, 3020458607057164425), (4000, 4000, 2990553076294222203), (4001, 4001, 2960943639895269508), (4002, 4002, 2931627366232940107), (4003, 4003, 2902601352705881294), (4004, 4004, 2873862725451367618), (4005, 4005, 2845408639060760018), (4006, 4006, 2817236276297782196), (4007, 4007, 2789342847819586332), (4008, 4008, 2761725591900580527), (4009, 4009, 2734381774158990621), (4010, 4010, 2707308687286129328), (4011, 4011, 2680503650778345869), (4012, 4012, 2653964010671629573), (4013, 4013, 2627687139278841162), (4014, 4014, 2601670434929545705), (4015, 4015, 2575911321712421490), (4016, 4016, 2550407249220219297), (4017, 4017, 2525155692297246828), (4018, 4018, 2500154150789353295), (4019, 4019, 2475400149296389401), (4020, 4020, 2450891236927118219), (4021, 4021, 2426624987056552692), (4022, 4022, 2402598997085695735), (4023, 4023, 2378810888203659144), (4024, 4024, 2355258305152137766), (4025, 4025, 2331938915992215610), (4026, 4026, 2308850411873480802), (4027, 4027, 2285990506805426536), (4028, 4028, 2263356937431115383), (4029, 4029, 2240947462803084537), (4030, 4030, 2218759864161469839), (4031, 4031, 2196791944714326573), (4032, 4032, 2175041529420125320), (4033, 4033, 2153506464772401307), (4034, 4034, 2132184618586535947), (4035, 4035, 2111073879788649453), (4036, 4036, 2090172158206583617), (4037, 4037, 2069477384362954076), (4038, 4038, 2048987509270251560), (4039, 4039, 2028700504227971842), (4040, 4040, 2008614360621754299), (4041, 4041, 1988727089724509207), (4042, 4042, 1969036722499514066), (4043, 4043, 1949541309405459472), (4044, 4044, 1930238920203425219), (4045, 4045, 1911127643765767544), (4046, 4046, 1892205587886898558), (4047, 4047, 1873470879095939167), (4048, 4048, 1854921662471226898), (4049, 4049, 1836556101456660295), (4050, 4050, 1818372377679861678), (4051, 4051, 1800368690772140275), (4052, 4052, 1782543258190237896), (4053, 4053, 1764894315039839501), (4054, 4054, 1747420113900831189), (4055, 4055, 1730118924654288306), (4056, 4056, 1712989034311176541), (4057, 4057, 1696028746842749050), (4058, 4058, 1679236383012622822), (4059, 4059, 1662610280210517646), (4060, 4060, 1646148792287641233), (4061, 4061, 1629850289393704192), (4062, 4062, 1613713157815548704), (4063, 4063, 1597735799817374955), (4064, 4064, 1581916633482549460), (4065, 4065, 1566254092556979664), (4066, 4066, 1550746626294039271), (4067, 4067, 1535392699301028981), (4068, 4068, 1520190791387157407), (4069, 4069, 1505139397413027136), (4070, 4070, 1490237027141611026), (4071, 4071, 1475482205090703986), (4072, 4072, 1460873470386835629), (4073, 4073, 1446409376620629336), (4074, 4074, 1432088491703593402), (4075, 4075, 1417909397726330101), (4076, 4076, 1403870690818148615), (4077, 4077, 1389970981008067936), (4078, 4078, 1376208892087195976), (4079, 4079, 1362583061472471263), (4080, 4080, 1349092140071753726), (4081, 4081, 1335734792150251214), (4082, 4082, 1322509695198268528), (4083, 4083, 1309415539800265870), (4084, 4084, 1296451029505213732), (4085, 4085, 1283614880698231418), (4086, 4086, 1270905822473496454), (4087, 4087, 1258322596508412330), (4088, 4088, 1245863956939022109), (4089, 4089, 1233528670236655554), (4090, 4090, 1221315515085797578), (4091, 4091, 1209223282263165919), (4092, 4092, 1197250774517986058), (4093, 4093, 1185396806453451543), (4094, 4094, 1173660204409357963), (4095, 4095, 1162039806345898973), (4096, 4096, 1150534461728612845), (4097, 4097, 1139143031414468163), (4098, 4098, 1127864387539077390), (4099, 4099, 1116697413405027118), (4100, 4100, 1105641003371313979), (4101, 4101, 1094694062743875226), (4102, 4102, 1083855507667203194), (4103, 4103, 1073124265017032866), (4104, 4104, 1062499272294091946), (4105, 4105, 1051979477518902917), (4106, 4106, 1041563839127626651), (4107, 4107, 1031251325868937278), (4108, 4108, 1021040916701918097), (4109, 4109, 1010931600694968413), (4110, 4110, 1000922376925711300), (4111, 4111, 991012254381892376), (4112, 4112, 981200251863259778), (4113, 4113, 971485397884415622), (4114, 4114, 961866730578629329), (4115, 4115, 952343297602603296), (4116, 4116, 942914156042181481), (4117, 4117, 933578372318991565), (4118, 4118, 924335022098011451), (4119, 4119, 915183190196050941), (4120, 4120, 906121970491139546), (4121, 4121, 897150465832811432), (4122, 4122, 888267787953278645), (4123, 4123, 879473057379483807), (4124, 4124, 870765403346023571), (4125, 4125, 862143963708934229), (4126, 4126, 853607884860330920), (4127, 4127, 845156321643892000), (4128, 4128, 836788437271180198), (4129, 4129, 828503403238792275), (4130, 4130, 820300399246328985), (4131, 4131, 812178613115177213), (4132, 4132, 804137240708096251), (4133, 4133, 796175485849600248), (4134, 4134, 788292560247128959), (4135, 4135, 780487683412998969), (4136, 4136, 772760082587127692), (4137, 4137, 765108992660522467), (4138, 4138, 757533656099527195), (4139, 4139, 750033322870819005), (4140, 4140, 742607250367147530), (4141, 4141, 735254703333809436), (4142, 4142, 727974953795850927), (4143, 4143, 720767280985991016), (4144, 4144, 713630971273258432), (4145, 4145, 706565318092335081), (4146, 4146, 699569621873599090), (4147, 4147, 692643189973860485), (4148, 4148, 685785336607782659), (4149, 4149, 678995382779982831), (4150, 4150, 672272656217804783), (4151, 4151, 665616491304757211), (4152, 4152, 659026229014611100), (4153, 4153, 652501216846149604), (4154, 4154, 646040808758563964), (4155, 4155, 639644365107489073), (4156, 4156, 633311252581672350), (4157, 4157, 627040844140269653), (4158, 4158, 620832518950762033), (4159, 4159, 614685662327487161), (4160, 4160, 608599665670779368), (4161, 4161, 602573926406712245), (4162, 4162, 596607847927437867), (4163, 4163, 590700839532116700), (4164, 4164, 584852316368432376), (4165, 4165, 579061699374685521), (4166, 4166, 573328415222460911), (4167, 4167, 567651896259862289), (4168, 4168, 562031580455309197), (4169, 4169, 556466911341890294), (4170, 4170, 550957337962267618), (4171, 4171, 545502314814126354), (4172, 4172, 540101301796164707), (4173, 4173, 534753764154618522), (4174, 4174, 529459172430315368), (4175, 4175, 524217002406252840), (4176, 4176, 519026735055695881), (4177, 4177, 513887856490788001), (4178, 4178, 508799857911671288), (4179, 4179, 503762235556110186), (4180, 4180, 498774490649614046), (4181, 4181, 493836129356053511), (4182, 4182, 488946662728765852), (4183, 4183, 484105606662144408), (4184, 4184, 479312481843707335), (4185, 4185, 474566813706640925), (4186, 4186, 469868132382812797), (4187, 4187, 465215972656250294), (4188, 4188, 460609873917079499), (4189, 4189, 456049380115920297), (4190, 4190, 451534039718732967), (4191, 4191, 447063405662111848), (4192, 4192, 442637035309021632), (4193, 4193, 438254490404971913), (4194, 4194, 433915337034625656), (4195, 4195, 429619145578837284), (4196, 4196, 425365490672116122), (4197, 4197, 421153951160511012), (4198, 4198, 416984110059911893), (4199, 4199, 412855554514764251), (4200, 4200, 408767875757192328), (4201, 4201, 404720669066527057), (4202, 4202, 400713533729234710), (4203, 4203, 396746072999242287), (4204, 4204, 392817894058655730), (4205, 4205, 388928607978867059), (4206, 4206, 385077829682046593), (4207, 4207, 381265177903016429), (4208, 4208, 377490275151501415), (4209, 4209, 373752747674753876), (4210, 4210, 370052225420548392), (4211, 4211, 366388342000542962), (4212, 4212, 362760734654002933), (4213, 4213, 359169044211884092), (4214, 4214, 355612915061271378), (4215, 4215, 352091995110169682), (4216, 4216, 348605935752643249), (4217, 4217, 345154391834300247), (4218, 4218, 341737021618119056), (4219, 4219, 338353486750612927), (4220, 4220, 335003452228329631), (4221, 4221, 331686586364682803), (4222, 4222, 328402560757111686), (4223, 4223, 325151050254566025), (4224, 4224, 321931732925312896), (4225, 4225, 318744290025062274), (4226, 4226, 315588405965408192), (4227, 4227, 312463768282582368), (4228, 4228, 309370067606517196), (4229, 4229, 306306997630215046), (4230, 4230, 303274255079420837), (4231, 4231, 300271539682594889), (4232, 4232, 297298554141183058), (4233, 4233, 294355004100181245), (4234, 4234, 291440598118991332), (4235, 4235, 288555047642565675), (4236, 4236, 285698066972837302), (4237, 4237, 282869373240432973), (4238, 4238, 280068686376666310), (4239, 4239, 277295729085808227), (4240, 4240, 274550226817631908), (4241, 4241, 271831907740229612), (4242, 4242, 269140502713098626), (4243, 4243, 266475745260493689), (4244, 4244, 263837371545043256), (4245, 4245, 261225120341626987), (4246, 4246, 258638733011511868), (4247, 4247, 256077953476744424), (4248, 4248, 253542528194796459), (4249, 4249, 251032206133461841), (4250, 4250, 248546738746001822), (4251, 4251, 246085879946536458), (4252, 4252, 243649386085679661), (4253, 4253, 241237015926415506), (4254, 4254, 238848530620213372), (4255, 4255, 236483693683379577), (4256, 4256, 234142270973643145), (4257, 4257, 231824030666973411), (4258, 4258, 229528743234627140), (4259, 4259, 227256181420422911), (4260, 4260, 225006120218240506), (4261, 4261, 222778336849743075), (4262, 4262, 220572610742319876), (4263, 4263, 218388723507247402), (4264, 4264, 216226458918066735), (4265, 4265, 214085602889174985), (4266, 4266, 211965943454628698), (4267, 4267, 209867270747157127), (4268, 4268, 207789376977383294), (4269, 4269, 205732056413250786), (4270, 4270, 203695105359654243), (4271, 4271, 201678322138271528), (4272, 4272, 199681507067595572), (4273, 4273, 197704462443163933), (4274, 4274, 195746992517984092), (4275, 4275, 193808903483152567), (4276, 4276, 191890003448665908), (4277, 4277, 189990102424421691), (4278, 4278, 188109012301407614), (4279, 4279, 186246546833076846), (4280, 4280, 184402521616907768), (4281, 4281, 182576754076146305), (4282, 4282, 180769063441729015), (4283, 4283, 178979270734385164), (4284, 4284, 177207198746916003), (4285, 4285, 175452672026649508), (4286, 4286, 173715516858068820), (4287, 4287, 171995561245612693), (4288, 4288, 170292634896646231), (4289, 4289, 168606569204600229), (4290, 4290, 166937197232277454), (4291, 4291, 165284353695324212), (4292, 4292, 163647874945865556), (4293, 4293, 162027598956302531), (4294, 4294, 160423365303269833), (4295, 4295, 158835015151752310), (4296, 4296, 157262391239358723), (4297, 4297, 155705337860751210), (4298, 4298, 154163700852228921), (4299, 4299, 152637327576464278), (4300, 4300, 151126066907390375), (4301, 4301, 149629769215237995), (4302, 4302, 148148286351720787), (4303, 4303, 146681471635367116), (4304, 4304, 145229179836997144), (4305, 4305, 143791267165343707), (4306, 4306, 142367591252815552), (4307, 4307, 140958011141401536), (4308, 4308, 139562387268714392), (4309, 4309, 138180581454172666), (4310, 4310, 136812456885319471), (4311, 4311, 135457878104276704), (4312, 4312, 134116710994333370), (4313, 4313, 132788822766666703), (4314, 4314, 131474081947194756), (4315, 4315, 130172358363559164), (4316, 4316, 128883523132236796), (4317, 4317, 127607448645779006), (4318, 4318, 126344008560177234), (4319, 4319, 125093077782353697), (4320, 4320, 123854532457775937), (4321, 4321, 122628249958193997), (4322, 4322, 121414108869499007), (4323, 4323, 120211988979701988), (4324, 4324, 119021771267031671), (4325, 4325, 117843337888150169), (4326, 4326, 116676572166485316), (4327, 4327, 115521358580678531), (4328, 4328, 114377582753147060), (4329, 4329, 113245131438759465), (4330, 4330, 112123892513623233), (4331, 4331, 111013754963983399), (4332, 4332, 109914608875231088), (4333, 4333, 108826345421020879), (4334, 4334, 107748856852495920), (4335, 4335, 106682036487619723), (4336, 4336, 105625778700613587), (4337, 4337, 104579978911498601), (4338, 4338, 103544533575741189), (4339, 4339, 102519340174001178), (4340, 4340, 101504297201981364), (4341, 4341, 100499304160377588), (4342, 4342, 99504261544928305), (4343, 4343, 98519070836562678), (4344, 4344, 97543634491646216), (4345, 4345, 96577855932322986), (4346, 4346, 95621639536953452), (4347, 4347, 94674890630646982), (4348, 4348, 93737515475888101), (4349, 7209, 92809421263255545)]

def glob1 : ℕ := 10145709240540253389

def runs2 : List (ℕ × ℕ × ℕ) := [(0, 3864, 0), (3865, 3877, 33539534679471912030), (3878, 3878, 33283863875560429210), (3879, 3879, 32954320668871712090), (3880, 3880, 32628040266209615930), (3881, 3881, 32304990362583778149), (3882, 3882, 31985138972855225890), (3883, 3883, 31668454428569530584), (3884, 3884, 31354905374821317410), (3885, 3885, 31044460767149819218), (3886, 3886, 30737089868465167542), (3887, 3887, 30432762246005116379), (3888, 3888, 30131447768321897405), (3889, 3889, 29833116602298908321), (3890, 3890, 29537739210196938932), (3891, 3891, 29245286346729642507), (3892, 3892, 28955729056167962878), (3893, 3893, 28669038669473230572), (3894, 3894, 28385186801458644131), (3895, 3895, 28104145347978855575), (3896, 3896, 27825886483147381758), (3897, 3897, 27550382656581566097), (3898, 3898, 27277606590674817918), (3899, 3899, 27007531277895859324), (3900, 3900, 26740129978114712202), (3901, 3901, 26475376215955160596), (3902, 3902, 26213243778173426333), (3903, 3903, 25953706711062798350), (3904, 3904, 25696739317883958762), (3905, 3905, 25442316156320751250), (3906, 3906, 25190412035961139851), (3907, 3907, 24941002015803108763), (3908, 3908, 24694061401785256201), (3909, 3909, 24449565744341837823), (3910, 3910, 24207490835982017647), (3911, 3911, 23967812708893086779), (3912, 3912, 23730507632567412652), (3913, 3913, 23495552111452883814), (3914, 3914, 23262922882626617638), (3915, 3915, 23032596913491700632), (3916, 3916, 22804551399496733299), (3917, 3917, 22578763761877953761), (3918, 3918, 22355211645423716595), (3919, 3919, 22133872916261105540), (3920, 3920, 21914725659664460930), (3921, 3921, 21697748177885604882), (3922, 3922, 21482918988005549388), (3923, 3923, 21270216819807474641), (3924, 3924, 21059620613670766972), (3925, 3925, 20851109518485907893), (3926, 3926, 20644662889590007814), (3927, 3927, 20440260286722780014), (3928, 3928, 20237881472002752489), (3929, 3929, 20037506407923517316), (3930, 3930, 19839115255369819125), (3931, 3931, 19642688371653286262), (3932, 3932, 19448206308567610161), (3933, 3933, 19255649810462980357), (3934, 3934, 19064999812339584512), (3935, 3935, 18876237437959984665), (3936, 3936, 18689343997980182837), (3937, 3937, 18504300988099190928), (3938, 3938, 18321090087226921711), (3939, 3939, 18139693155670219516), (3940, 3940, 17960092233336851006), (3941, 3941, 17782269537957278223), (3942, 3942, 17606207463324037845), (3943, 3943, 17431888577548552322), (3944, 3944, 17259295621335200318), (3945, 3945, 17088411506272475563), (3946, 3946, 16919219313141064914), (3947, 3947, 16751702290238678132), (3948, 3948, 16585843851721463497), (3949, 3949, 16421627575961845047), (3950, 3950, 16259037203922618858), (3951, 3951, 16098056637547147385), (3952, 3952, 15938669938165492460), (3953, 3953, 15780861324916329168), (3954, 3954, 15624615173184484325), (3955, 3955, 15469916013053944876), (3956, 3956, 15316748527776183046), (3957, 3957, 15165097552253646580), (3958, 3958, 15014948071538263941), (3959, 3959, 14866285219344815783), (3960, 3960, 14719094276579025528), (3961, 3961, 14573360669880223295), (3962, 3962, 14429069970178438906), (3963, 3963, 14286207891265781095), (3964, 3964, 14144760288381961480), (3965, 3965, 14004713156813823247), (3966, 3966, 13866052630508735888), (3967, 3967, 13728764980701718701), (3968, 3968, 13592836614556157130), (3969, 3969, 13458254073817977357), (3970, 3970, 13325004033483145898), (3971, 3971, 13193073300478362275), (3972, 3972, 13062448812354814134), (3973, 3973, 12933117635994865479), (3974, 3974, 12805066966331549979), (3975, 3975, 12678284125080742553), (3976, 3976, 12552756559485883716), (3977, 3977, 12428471841075132392), (3978, 3978, 12305417664430824151), (3979, 3979, 12183581845971113021), (3980, 3980, 12062952322743676258), (3981, 3981, 11943517151231362632), (3982, 3982, 11825264506169665972), (3983, 3983, 11708182679375906903), (3984, 3984, 11592260078590006835), (3985, 3985, 11477485226326739440), (3986, 3986, 11363846758739345981), (3987, 3987, 11251333424494401961), (3988, 3988, 11139934083657823724), (3989, 3989, 11029637706591904677), (3990, 3990, 10920433372863271957), (3991, 3991, 10812310270161655403), (3992, 3992, 10705257693229361785), (3993, 3993, 10599265042801348302), (3994, 3994, 10494321824555790398), (3995, 3995, 10390417648075039998), (3996, 3996, 10287542225816871286), (3997, 3997, 10185685372095912164), (3998, 3998, 10084837002075160558), (3999, 3999, 9984987130767485701), (4000, 4000, 9886125872047015546), (4001, 4001, 9788243437670312422), (4002, 4002, 9691330136307240022), (4003, 4003, 9595376372581425764), (4004, 4004, 9500372646120223529), (4005, 4005, 9406309550614082702), (4006, 4006, 9313177772885230398), (4007, 4007, 9220968091965574651), (4008, 4008, 9129671378183737278), (4009, 4009, 9039278592261126018), (4010, 4010, 8949780784416956454), (4011, 4011, 8861169093482135103), (4012, 4012, 8773434746021915943), (4013, 4013, 8686569055467243508), (4014, 4014, 8600563421254696543), (4015, 4015, 8515409327974947072), (4016, 4016, 8431098344529650566), (4017, 4017, 8347622123296683729), (4018, 4018, 8264972399303647256), (4019, 4019, 8183140989409551739), (4020, 4020, 8102119791494605682), (4021, 4021, 8021900783658025428), (4022, 4022, 7942476023423787552), (4023, 4023, 7863837646954245101), (4024, 4024, 7785977868271529803), (4025, 4025, 7708888978486663172), (4026, 4026, 7632563345036300170), (4027, 4027, 7556993410927029871), (4028, 4028, 7482171693987158288), (4029, 4029, 7408090786125899295), (4030, 4030, 7334743352599900293), (4031, 4031, 7262122131287029993), (4032, 4032, 7190219931967356428), (4033, 4033, 7119029635611243988), (4034, 4034, 7048544193674498999), (4035, 4035, 6978756627400494058), (4036, 4036, 6909660027129202038), (4037, 4037, 6841247551613071324), (4038, 4038, 6773512427339674579), (4039, 4039, 6706447947861063939), (4040, 4040, 6640047473129766276), (4041, 4041, 6574304428841352749), (4042, 4042, 6509212305783517573), (4043, 4043, 6444764659191601558), (4044, 4044, 6380955108110496592), (4045, 4045, 6317777334762867913), (4046, 4046, 6255225083923631597), (4047, 4047, 6193292162300625343), (4048, 4048, 6131972437921411231), (4049, 4049, 6071259839526149734), (4050, 4050, 6011148355966484885), (4051, 4051, 5951632035610381074), (4052, 4052, 5892704985752852549), (4053, 4053, 5834361372032527276), (4054, 4054, 5776595417853987402), (4055, 4055, 5719401403815829111), (4056, 4056, 5662773667144385258), (4057, 4057, 5606706601133054711), (4058, 4058, 5551194654587182882), (4059, 4059, 5496232331274438497), (4060, 4060, 5441814189380632175), (4061, 4061, 5387934840970922946), (4062, 4062, 5334588951456359352), (4063, 4063, 5281771239065702329), (4064, 4064, 5229476474322477554), (4065, 4065, 5177699479527205499), (4066, 4066, 5126435128244757919), (4067, 4067, 5075678344796790019), (4068, 4068, 5025424103759198039), (4069, 4069, 4975667429464552514), (4070, 4070, 4926403395509457934), (4071, 4071, 4877627124266790034), (4072, 4072, 4829333786402762410), (4073, 4073, 4781518600398774663), (4074, 4074, 4734176832077994716), (4075, 4075, 4687303794136628432), (4076, 4076, 4640894845679830131), (4077, 4077, 4594945391762208050), (4078, 4078, 4549450882932879258), (4079, 4079, 4504406814785028968), (4080, 4080, 4459808727509929671), (4081, 4081, 4415652205455375912), (4082, 4082, 4371932876688491002), (4083, 4083, 4328646412562862378), (4084, 4084, 4285788527289962751), (4085, 4085, 4243354977514814605), (4086, 4086, 4201341561895856044), (4087, 4087, 4159744120688966380), (4088, 4088, 4118558535335610278), (4089, 4089, 4077780728055059681), (4090, 4090, 4037406661440653149), (4091, 4091, 3997432338060052623), (4092, 4092, 3957853800059458043), (4093, 4093, 3918667128771740636), (4094, 4094, 3879868444328456076), (4095, 4095, 3841453905275699085), (4096, 4096, 3803419708193761470), (4097, 4097, 3765762087320555911), (4098, 4098, 3728477314178768229), (4099, 4099, 3691561697206701217), (4100, 4100, 3655011581392773482), (4101, 4101, 3618823347913637111), (4102, 4102, 3582993413775878327), (4103, 4103, 3547518231461265671), (4104, 4104, 3512394288575510565), (4105, 4105, 3477618107500505510), (4106, 4106, 3443186245050005455), (4107, 4107, 3409095292128718273), (4108, 4108, 3375341873394770567), (4109, 4109, 3341922646925515413), (4110, 4110, 3308834303886648924), (4111, 4111, 3276073568204602895), (4112, 4112, 3243637196242181084), (4113, 4113, 3211521976477407014), (4114, 4114, 3179724729185551499), (4115, 4115, 3148242306124308415), (4116, 4116, 3117071590222087539), (4117, 4117, 3086209495269393603), (4118, 4118, 3055652965613260993), (4119, 4119, 3025398975854713855), (4120, 4120, 2995444530549221638), (4121, 4121, 2965786663910120434), (4122, 4122, 2936422439514970727), (4123, 4123, 2907348950014822502), (4124, 4124, 2878563316846358913), (4125, 4125, 2850062689946890012), (4126, 4126, 2821844247472168329), (4127, 4127, 2793905195516998346), (4128, 4128, 2766242767838612224), (4129, 4129, 2738854225582784380), (4130, 4130, 2711736857012657802), (4131, 4131, 2684887977240255249), (4132, 4132, 2658304927960648762), (4133, 4133, 2631985077188761150), (4134, 4134, 2605925818998773416), (4135, 4135, 2580124573266112293), (4136, 4136, 2554578785411992369), (4137, 4137, 2529285926150487494), (4138, 4138, 2504243491238106430), (4139, 4139, 2479449001225847951), (4140, 4140, 2454900001213710842), (4141, 4141, 2430594060607634497), (4142, 4142, 2406528772878846037), (4143, 4143, 2382701755325590136), (4144, 4144, 2359110648837217956), (4145, 4145, 2335753117660611838), (4146, 4146, 2312626849168922611), (4147, 4147, 2289729553632596645), (4148, 4148, 2267058963992669946), (4149, 4149, 2244612835636306877), (4150, 4150, 2222388946174561264), (4151, 4151, 2200385095222337885), (4152, 4152, 2178599104180532560), (4153, 4153, 2157028816020329267), (4154, 4154, 2135672095069632938), (4155, 4155, 2114526826801616770), (4156, 4156, 2093590917625363139), (4157, 4157, 2072862294678577365), (4158, 4158, 2052338905622353827), (4159, 4159, 2032018718437974086), (4160, 4160, 2011899721225716917), (4161, 4161, 1991979922005660314), (4162, 4162, 1972257348520455756), (4163, 4163, 1952730048040055204), (4164, 4164, 1933396087168371489), (4165, 4165, 1914253551651852960), (4166, 4166, 1895300546189953425), (4167, 4167, 1876535194247478639), (4168, 4168, 1857955637868790732), (4169, 4169, 1839560037493852209), (4170, 4170, 1821346571776091297), (4171, 4171, 1803313437402070591), (4172, 4172, 1785458848912941179), (4173, 4173, 1767781038527664534), (4174, 4174, 1750278255967984687), (4175, 4175, 1732948768285133353), (4176, 4176, 1715790859688250845), (4177, 4177, 1698802831374505787), (4178, 4178, 1681983001360896819), (4179, 4179, 1665329704317719622), (4180, 4180, 1648841291403682794), (4181, 4181, 1632516130102656232), (4182, 4182, 1616352604062035873), (4183, 4183, 1600349112932708786), (4184, 4184, 1584504072210602758), (4185, 4185, 1568815913079804711), (4186, 4186, 1553283082257232387), (4187, 4187, 1537904041838843948), (4188, 4188, 1522677269147370245), (4189, 4189, 1507601256581554698), (4190, 4190, 1492674511466885840), (4191, 4191, 1477895555907807762), (4192, 4192, 1463262926641393824), (4193, 4193, 1448775174892469133), (4194, 4194, 1434430866230167458), (4195, 4195, 1420228580425908374), (4196, 4196, 1406166911312780569), (4197, 4197, 1392244466646317395), (4198, 4198, 1378459867966650886), (4199, 4199, 1364811750462030580), (4200, 4200, 1351298762833693644), (4201, 4201, 1337919567162072914), (4202, 4202, 1324672838774329618), (4203, 4203, 1311557266113197642), (4204, 4204, 1298571550607126378), (4205, 4205, 1285714406541709285), (4206, 4206, 1272984560932385431), (4207, 4207, 1260380753398401417), (4208, 4208, 1247901736038021205), (4209, 4209, 1235546273304971490), (4210, 4210, 1223313141886110386), (4211, 4211, 1211201130580307313), (4212, 4212, 1199209040178522092), (4213, 4213, 1187335683345071378), (4214, 4214, 1175579884500070671), (4215, 4215, 1163940479703040269), (4216, 4216, 1152416316537663632), (4217, 4217, 1141006253997686765), (4218, 4218, 1129709162373947292), (4219, 4219, 1118523923142522071), (4220, 4220, 1107449428853982249), (4221, 4221, 1096484583023744801), (4222, 4222, 1085628300023509704), (4223, 4223, 1074879504973771984), (4224, 4224, 1064237133637398004), (4225, 4225, 1053700132314255449), (4226, 4226, 1043267457736886583), (4227, 4227, 1032938076967214439), (4228, 4228, 1022710967294271722), (4229, 4229, 1012585116132942299), (4230, 4230, 1002559520923705246), (4231, 4231, 992633189033371531), (4232, 4232, 982805137656803496), (4233, 4233, 973074393719607422), (4234, 4234, 963439993781789527), (4235, 4235, 953900983942365868), (4236, 4236, 944456419744916701), (4237, 4237, 935105366084075942), (4238, 4238, 925846897112946477), (4239, 4239, 916680096151432155), (4240, 4240, 907604055595477381), (4241, 4241, 898617876827205328), (4242, 4242, 889720670125945870), (4243, 4243, 880911554580144425), (4244, 4244, 872189658000142995), (4245, 4245, 863554116831824748), (4246, 4246, 855004076071113612), (4247, 4247, 846538689179320408), (4248, 4248, 838157117999327136), (4249, 4249, 829858532672601125), (4250, 4250, 821642111557030817), (4251, 4251, 813507041145575066), (4252, 4252, 805452515985717887), (4253, 4253, 797477738599720681), (4254, 4254, 789581919405664040), (4255, 4255, 781764276639271327), (4256, 4256, 774024036276506264), (4257, 4257, 766360431956936895), (4258, 4258, 758772704907858312), (4259, 4259, 751260103869166646), (4260, 4260, 743821885018976877), (4261, 4261, 736457311899977106), (4262, 4262, 729165655346511986), (4263, 4263, 721946193412388105), (4264, 4264, 714798211299394163), (4265, 4265, 707721001286528875), (4266, 4266, 700713862659929579), (4267, 4267, 693776101643494633), (4268, 4268, 686907031330192705), (4269, 4269, 680105971614052184), (4270, 4270, 673372249122823944), (4271, 4271, 666705197151310836), (4272, 4272, 660104155595357263), (4273, 4273, 653568470886492340), (4274, 4274, 647097495927220138), (4275, 4275, 640690590026950632), (4276, 4276, 634347118838564982), (4277, 4277, 628066454295608893), (4278, 4278, 621847974550107815), (4279, 4279, 615691063910997837), (4280, 4280, 609595112783166175), (4281, 4281, 603559517607095223), (4282, 4282, 597583680799104181), (4283, 4283, 591667010692182358), (4284, 4284, 585808921477408275), (4285, 4285, 580008833145948787), (4286, 4286, 574266171431632462), (4287, 4287, 568580367754091547), (4288, 4288, 562950859162466878), (4289, 4289, 557377088279670176), (4290, 4290, 551858503247198194), (4291, 4291, 546394557670493262), (4292, 4292, 540984710564844814), (4293, 4293, 535628426301826548), (4294, 4294, 530325174556263909), (4295, 4295, 525074430253726643), (4296, 4296, 519875673518541230), (4297, 4297, 514728389622318050), (4298, 4298, 509632068932988168), (4299, 4299, 504586206864344721), (4300, 4300, 499590303826083882), (4301, 4301, 494643865174340477), (4302, 4302, 489746401162713344), (4303, 4303, 484897426893775588), (4304, 4304, 480096462271064939), (4305, 4305, 475343031951549444), (4306, 4306, 470636665298563806), (4307, 4307, 465976896335211689), (4308, 4308, 461363263698229395), (4309, 4309, 456795310592306332), (4310, 4310, 452272584744857755), (4311, 4311, 447794638361245302), (4312, 4312, 443361028080440893), (4313, 4313, 438971314931129597), (4314, 4314, 434625064288247125), (4315, 4315, 430321845829947649), (4316, 4316, 426061233494997672), (4317, 4317, 421842805440591755), (4318, 4318, 417666144000585896), (4319, 4319, 413530835644144451), (4320, 4320, 409436470934796486), (4321, 4321, 405382644489897511), (4322, 4322, 401368954940492585), (4323, 4323, 397395004891576817), (4324, 4324, 393460400882749324), (4325, 4325, 389564753349256756), (4326, 4326, 385707676583422531), (4327, 4327, 381888788696457952), (4328, 4328, 378107711580651437), (4329, 4329, 374364070871932116), (4330, 4330, 370657495912804075), (4331, 4331, 366987619715647599), (4332, 4332, 363354078926383762), (4333, 4333, 359756513788498774), (4334, 4334, 356194568107424529), (4335, 4335, 352667889215271811), (4336, 4336, 349176127935912684), (4337, 4337, 345718938550408598), (4338, 4338, 342295978762780790), (4339, 4339, 338906909666119594), (4340, 4340, 335551395709029301), (4341, 4341, 332229104662405248), (4342, 4342, 328939707586539850), (4343, 4343, 325682878798554307), (4344, 4344, 322458295840152779), (4345, 4345, 319265639445695821), (4346, 4346, 316104593510589922), (4347, 4347, 312974845059990022), (4348, 4348, 309876084217811902), (4349, 7209, 306808004176051389)]

def glob2 : ℕ := 33539534679471912030

def runs3 : List (ℕ × ℕ × ℕ) := [(0, 3864, 0), (3865, 3865, 140618942151315551), (3866, 3866, 321867705830109968), (3867, 3867, 501321927294262855), (3868, 3868, 678999374288473635), (3869, 3869, 854917638639177377), (3870, 3870, 1029094137996309796), (3871, 3871, 1201546117557827041), (3872, 3872, 1372290651777151047), (3873, 3873, 1541344646053709468), (3874, 3874, 1708724838406737609), (3875, 3875, 1874447801132508044), (3876, 3876, 2038529942445152040), (3877, 3877, 2200987508101235204), (3878, 3878, 2361836583008248238), (3879, 3879, 2521093092817172034), (3880, 3880, 2678772805499274802), (3881, 3881, 2834891332907297345), (3882, 3882, 2989464132321181050), (3883, 3883, 3142506507978491650), (3884, 3884, 3294033612589690264), (3885, 3885, 3444060448838401762), (3886, 3886, 3592601870866828988), (3887, 3887, 3739672585746459905), (3888, 3888, 3885287154934213289), (3889, 3889, 4029459995714167134), (3890, 3890, 4172205382625012524), (3891, 3891, 4313537448873374298), (3892, 3892, 4453470187733138430), (3893, 3893, 4592017453930924699), (3894, 3894, 4729192965017841797), (3895, 3895, 4865010302727660706), (3896, 3896, 4999482914321540814), (3897, 3897, 5132624113919441911), (3898, 3898, 5264447083818353888), (3899, 3899, 5394964875797474658), (3900, 3900, 5524190412410465519), (3901, 3901, 5652136488264911916), (3902, 3902, 5778815771289116269), (3903, 3903, 5904240803986348303), (3904, 3904, 6028424004676677048), (3905, 3905, 6151377668726507490), (3906, 3906, 6273113969765943570), (3907, 3907, 6393644960894098105), (3908, 3908, 6512982575872468932), (3909, 3909, 6631138630306499454), (3910, 3910, 6748124822815440564), (3911, 3911, 6863952736190629782), (3912, 3912, 6978633838542302276), (3913, 3913, 7092179484435047319), (3914, 3914, 7204600916012022609), (3915, 3915, 7315909264108037748), (3916, 3916, 7426115549351617093), (3917, 3917, 7535230683256151098), (3918, 3918, 7643265469300244172), (3919, 3919, 7750230603997366028), (3920, 3920, 7856136677954912420), (3921, 3921, 7960994176922780135), (3922, 3922, 8064813482831560051), (3923, 3923, 8167604874820451056), (3924, 3924, 8269378530254996606), (3925, 3925, 8370144525734744676), (3926, 3926, 8469912838090930883), (3927, 3927, 8568693345374283564), (3928, 3928, 8666495827833048594), (3929, 3929, 8763329968881330802), (3930, 3930, 8859205356057847840), (3931, 3931, 8954131481975191442), (3932, 3932, 9048117745259690057), (3933, 3933, 9141173451481965914), (3934, 3934, 9233307814078278644), (3935, 3935, 9324529955262746693), (3936, 3936, 9414848906930536841), (3937, 3937, 9504273611552111245), (3938, 3938, 9592812923058620555), (3939, 3939, 9680475607718530764), (3940, 3940, 9767270345005570574), (3941, 3941, 9853205728458085238), (3942, 3942, 9938290266529881935), (3943, 3943, 10022532383432650942), (3944, 3944, 10105940419970045998), (3945, 3945, 10188522634363506449), (3946, 3946, 10270287203069902936), (3947, 3947, 10351242221591087577), (3948, 3948, 10431395705275428805), (3949, 3949, 10510755590111410219), (3950, 3950, 10589329733513372015), (3951, 3951, 10667125915099472803), (3952, 3952, 10744151837461948831), (3953, 3953, 10820415126929746878), (3954, 3954, 10895923334323606331), (3955, 3955, 10970683935703665195), (3956, 3956, 11044704333109664071), (3957, 3957, 11117991855293821373), (3958, 3958, 11190553758446452366), (3959, 3959, 11262397226914403843), (3960, 3960, 11333529373912375603), (3961, 3961, 11403957242227199128), (3962, 3962, 11473687804915143212), (3963, 3963, 11542727965992315573), (3964, 3964, 11611084561118228801), (3965, 3965, 11678764358272598334), (3966, 3966, 11745774058425439455), (3967, 3967, 11812120296200529675), (3968, 3968, 11877809640532302169), (3969, 3969, 11942848595316235332), (3970, 3970, 12007243600052802820), (3971, 3971, 12071001030485047858), (3972, 3972, 12134127199229844925), (3973, 3973, 12196628356402911327), (3974, 3974, 12258510690237630538), (3975, 3975, 12319780327697748569), (3976, 3976, 12380443335084004044), (3977, 3977, 12440505718634752040), (3978, 3978, 12499973425120641145), (3979, 3979, 12558852342433402635), (3980, 3980, 12617148300168810050), (3981, 3981, 12674867070203866898), (3982, 3982, 12732014367268279618), (3983, 3983, 12788595849510272410), (3984, 3984, 12844617119056799927), (3985, 3985, 12900083722568213310), (3986, 3986, 12955001151787434481), (3987, 3987, 13009374844083693067), (3988, 3988, 13063210182990879785), (3989, 3989, 13116512498740569605), (3990, 3990, 13169287068789767447), (3991, 3991, 13221539118343428676), (3992, 3992, 13273273820871806131), (3993, 3993, 13324496298622674898), (3994, 3994, 13375211623128485559), (3995, 3995, 13425424815708496114), (3996, 3996, 13475140847965932307), (3997, 3997, 13524364642280225567), (3998, 3998, 13573101072294377310), (3999, 3999, 13621354963397497848), (4000, 4000, 13669131093202567687), (4001, 4001, 13716434192019468518), (4002, 4002, 13763268943323330727), (4003, 4003, 13809639984218243805), (4004, 4004, 13855551905896375566), (4005, 4005, 13901009254092545626), (4006, 4006, 13946016529534298160), (4007, 4007, 13990578188387518492), (4008, 4008, 14034698642697637631), (4009, 4009, 14078382260826468463), (4010, 4010, 14121633367884716811), (4011, 4011, 14164456246160210225), (4012, 4012, 14206855135541886872), (4013, 4013, 14248834233939586523), (4014, 4014, 14290397697699685188), (4015, 4015, 14331549642016614558), (4016, 4016, 14372294141340307004), (4017, 4017, 14412635229779606456), (4018, 4018, 14452576901501685121), (4019, 4019, 14492123111127505581), (4020, 4020, 14531277774123367423), (4021, 4021, 14570044767188577168), (4022, 4022, 14608427928639279885), (4023, 4023, 14646431058788490496), (4024, 4024, 14684057920322362388), (4025, 4025, 14721312238672730599), (4026, 4026, 14758197702385966450), (4027, 4027, 14794717963488180165), (4028, 4028, 14830876637846807605), (4029, 4029, 14866677305528616952), (4030, 4030, 14902123511154170760), (4031, 4031, 14937218764248778491), (4032, 4032, 14971966539589974265), (4033, 4033, 15006370277551554239), (4034, 4034, 15040433384444207678), (4035, 4035, 15074159232852775440), (4036, 4036, 15107551161970169263), (4037, 4037, 15140612477927984930), (4038, 4038, 15173346454123842026), (4039, 4039, 15205756331545482715), (4040, 4040, 15237845319091661615), (4041, 4041, 15269616593889858546), (4042, 4042, 15301073301610845606), (4043, 4043, 15332218556780139725), (4044, 4044, 15363055443086371526), (4045, 4045, 15393587013686601032), (4046, 4046, 15423816291508610443), (4047, 4047, 15453746269550203920), (4048, 4048, 15483379911175543996), (4049, 4049, 15512720150408553973), (4050, 4050, 15541769892223415336), (4051, 4051, 15570532012832188962), (4052, 4052, 15599009359969588593), (4053, 4053, 15627204753174934761), (4054, 4054, 15655120984071317106), (4055, 4055, 15682760816641992695), (4056, 4056, 15710126987504047734), (4057, 4057, 15737222206179349753), (4058, 4058, 15764049155362817098), (4059, 4059, 15790610491188032291), (4060, 4060, 15816908843490225552), (4061, 4061, 15842946816066654523), (4062, 4062, 15868726986934405979), (4063, 4063, 15894251908585645045), (4064, 4064, 15919524108240337189), (4065, 4065, 15944546088096468025), (4066, 4066, 15969320325577785684), (4067, 4067, 15993849273579090298), (4068, 4068, 16018135360709094865), (4069, 4069, 16042180991530881566), (4070, 4070, 16065988546799977309), (4071, 4071, 16089560383700072104), (4072, 4072, 16112898836076403584), (4073, 4073, 16136006214666830792), (4074, 4074, 16158884807330620108), (4075, 4075, 16181536879274965964), (4076, 4076, 16203964673279268792), (4077, 4077, 16226170409917192385), (4078, 4078, 16248156287776522674), (4079, 4079, 16269924483676849693), (4080, 4080, 16291477152885094267), (4081, 4081, 16312816429328900775), (4082, 4082, 16333944425807917120), (4083, 4083, 16354863234202982808), (4084, 4084, 16375574925683245866), (4085, 4085, 16396081550911229091), (4086, 4086, 16416385140245865948), (4087, 4087, 16436487703943526202), (4088, 4088, 16456391232357051206), (4089, 4089, 16476097696132818537), (4090, 4090, 16495609046405855498), (4091, 4091, 16514927214993020806), (4092, 4092, 16534054114584273586), (4093, 4093, 16552991638932048616), (4094, 4094, 16571741663038756567), (4095, 4095, 16590306043342427805), (4096, 4096, 16608686617900518140), (4097, 4097, 16626885206571894709), (4098, 4098, 16644903611197020025), (4099, 4099, 16662743615776352021), (4100, 4100, 16680406986646977759), (4101, 4101, 16697895472657498292), (4102, 4102, 16715210805341181989), (4103, 4103, 16732354699087403470), (4104, 4104, 16749328851311385135), (4105, 4105, 16766134942622258070), (4106, 4106, 16782774636989458997), (4107, 4107, 16799249581907479716), (4108, 4108, 16815561408558985378), (4109, 4109, 16831711731976317717), (4110, 4110, 16847702151201399241), (4111, 4111, 16863534249444054215), (4112, 4112, 16879209594238762110), (4113, 4113, 16894729737599859036), (4114, 4114, 16910096216175202527), (4115, 4115, 16925310551398314894), (4116, 4116, 16940374249639020208), (4117, 4117, 16955288802352589826), (4118, 4118, 16970055686227411230), (4119, 4119, 16984676363331194798), (4120, 4120, 16999152281255732984), (4121, 4121, 17013484873260226238), (4122, 4122, 17027675558413189856), (4123, 4123, 17041725741732955814), (4124, 4124, 17055636814326783495), (4125, 4125, 17069410153528593080), (4126, 4126, 17083047123035335244), (4127, 4127, 17096549073042010654), (4128, 4128, 17109917340375352643), (4129, 4129, 17123153248626186296), (4130, 4130, 17136258108280477042), (4131, 4131, 17149233216849081741), (4132, 4132, 17162079858996215106), (4133, 4133, 17174799306666644180), (4134, 4134, 17187392819211623462), (4135, 4135, 17199861643513583147), (4136, 4136, 17212207014109582835), (4137, 4137, 17224430153313542921), (4138, 4138, 17236532271337265780), (4139, 4139, 17248514566410258709), (4140, 4140, 17260378224898370520), (4141, 4141, 17272124421421253501), (4142, 4142, 17283754318968662393), (4143, 4143, 17295269069015601891), (4144, 4144, 17306669811636334066), (4145, 4145, 17317957675617257012), (4146, 4146, 17329133778568665870), (4147, 4147, 17340199227035407313), (4148, 4148, 17351155116606438444), (4149, 4149, 17362002532023300951), (4150, 4150, 17372742547287521255), (4151, 4151, 17383376225766947298), (4152, 4152, 17393904620301032489), (4153, 4153, 17404328773305077233), (4154, 4154, 17414649716873438365), (4155, 4155, 17424868472881716714), (4156, 4156, 17434986053087932902), (4157, 4157, 17445003459232701404), (4158, 4158, 17454921683138412792), (4159, 4159, 17464741706807433968), (4160, 4160, 17474464502519336123), (4161, 4161, 17484091032927160039), (4162, 4162, 17493622251152728273), (4163, 4163, 17503059100881013652), (4164, 4164, 17512402516453573434), (4165, 4165, 17521653422961058367), (4166, 4166, 17530812736334805824), (4167, 4167, 17539881363437526080), (4168, 4168, 17548860202153090689), (4169, 4169, 17557750141475431886), (4170, 4170, 17566552061596561785), (4171, 4171, 17575266833993720100), (4172, 4172, 17583895321515659026), (4173, 4173, 17592438378468073804), (4174, 4174, 17600896850698187446), (4175, 4175, 17609271575678497982), (4176, 4176, 17617563382589696533), (4177, 4177, 17625773092402764405), (4178, 4178, 17633901517960257348), (4179, 4179, 17641949464056785014), (4180, 4180, 17649917727518693594), (4181, 4181, 17657807097282959515), (4182, 4182, 17665618354475302011), (4183, 4183, 17673352272487522304), (4184, 4184, 17681009617054077050), (4185, 4185, 17688591146327893630), (4186, 4186, 17696097610955434798), (4187, 4187, 17703529754151020113), (4188, 4188, 17710888311770411514), (4189, 4189, 17718174012383670327), (4190, 4190, 17725387577347292914), (4191, 4191, 17732529720875632109), (4192, 4192, 17739601150111611510), (4193, 4193, 17746602565196739630), (4194, 4194, 17753534659340430838), (4195, 4195, 17760398118888639954), (4196, 4196, 17767193623391817297), (4197, 4197, 17773921845672190905), (4198, 4198, 17780583451890382595), (4199, 4199, 17787179101611364466), (4200, 4200, 17793709447869762359), (4201, 4201, 17800175137234512747), (4202, 4202, 17806576809872879469), (4203, 4203, 17812915099613836619), (4204, 4204, 17819190634010823896), (4205, 4205, 17825404034403880606), (4206, 4206, 17831555915981164478), (4207, 4207, 17837646887839861380), (4208, 4208, 17843677553046491976), (4209, 4209, 17849648508696621280), (4210, 4210, 17855560345973977026), (4211, 4211, 17861413650208982715), (4212, 4212, 17867209000936711120), (4213, 4213, 17872946971954263996), (4214, 4214, 17878628131377583675), (4215, 4215, 17884253041697702170), (4216, 4216, 17889822259836433352), (4217, 4217, 17895336337201513731), (4218, 4218, 17900795819741197275), (4219, 4219, 17906201247998309694), (4220, 4220, 17911553157163767535), (4221, 4221, 17916852077129567377), (4222, 4222, 17922098532541250389), (4223, 4223, 17927293042849847431), (4224, 4224, 17932436122363309849), (4225, 4225, 17937528280297431055), (4226, 4226, 17942570020826263931), (4227, 4227, 17947561843132039057), (4228, 4228, 17952504241454588686), (4229, 4229, 17957397705140281389), (4230, 4230, 17962242718690472183), (4231, 4231, 17967039761809472969), (4232, 4232, 17971789309452048005), (4233, 4233, 17976491831870439130), (4234, 4234, 17981147794660925393), (4235, 4235, 17985757658809921692), (4236, 4236, 17990321880739620998), (4237, 4237, 17994840912353184667), (4238, 4238, 17999315201079485330), (4239, 4239, 18003745189917406779), (4240, 4240, 18008131317479705242), (4241, 4241, 18012474018036436395), (4242, 4242, 18016773721557952387), (4243, 4243, 18021030853757473171), (4244, 4244, 18025245836133236324), (4245, 4245, 18029419086010229545), (4246, 4246, 18033551016581509962), (4247, 4247, 18037642036949114334), (4248, 4248, 18041692552164564209), (4249, 4249, 18045702963268970024), (4250, 4250, 18049673667332738159), (4251, 4251, 18053605057494884827), (4252, 4252, 18057497523001960736), (4253, 4253, 18061351449246590348), (4254, 4254, 18065167217805629569), (4255, 4255, 18068945206477945629), (4256, 4256, 18072685789321822916), (4257, 4257, 18076389336691998447), (4258, 4258, 18080056215276330657), (4259, 4259, 18083686788132105122), (4260, 4260, 18087281414721980830), (4261, 4261, 18090840450949580541), (4262, 4262, 18094364249194728769), (4263, 4263, 18097853158348340876), (4264, 4264, 18101307523846966725), (4265, 4265, 18104727687706992318), (4266, 4266, 18108113988558502806), (4267, 4267, 18111466761678810220), (4268, 4268, 18114786339025649244), (4269, 4269, 18118073049270044317), (4270, 4270, 18121327217828851320), (4271, 4271, 18124549166896977066), (4272, 4272, 18127739215479279784), (4273, 4273, 18130897679422153762), (4274, 4274, 18134024871444801266), (4275, 4275, 18137121101170194834), (4276, 4276, 18140186675155733020), (4277, 4277, 18143221896923592610), (4278, 4278, 18146227066990780323), (4279, 4279, 18149202482898886969), (4280, 4280, 18152148439243547015), (4281, 4281, 18155065227703606467), (4282, 4282, 18157953137070001963), (4283, 4283, 18160812453274353940), (4284, 4284, 18163643459417276689), (4285, 4285, 18166446435796408124), (4286, 4286, 18169221659934162020), (4287, 4287, 18171969406605205482), (4288, 4288, 18174689947863664354), (4289, 4289, 18177383553070059278), (4290, 4290, 18180050488917975043), (4291, 4291, 18182691019460465900), (4292, 4292, 18185305406136199422), (4293, 4293, 18187893907795341523), (4294, 4294, 18190456780725185188), (4295, 4295, 18192994278675525449), (4296, 4296, 18195506652883783134), (4297, 4297, 18197994152099879852), (4298, 4298, 18200457022610866701), (4299, 4299, 18202895508265309126), (4300, 4300, 18205309850497430339), (4301, 4301, 18207700288351015698), (4302, 4302, 18210067058503080410), (4303, 4303, 18212410395287302897), (4304, 4304, 18214730530717226152), (4305, 4305, 18217027694509229374), (4306, 4306, 18219302114105272169), (4307, 4307, 18221554014695413549), (4308, 4308, 18223783619240107986), (4309, 4309, 18225991148492280695), (4310, 4310, 18228176821019184367), (4311, 4311, 18230340853224039489), (4312, 4312, 18232483459367460401), (4313, 4313, 18234604851588669225), (4314, 4314, 18236705239926499743), (4315, 4315, 18238784832340193326), (4316, 4316, 18240843834729988953), (4317, 4317, 18242882450957509375), (4318, 4318, 18244900882865945437), (4319, 4319, 18246899330300040548), (4320, 4320, 18248877991125877291), (4321, 4321, 18250837061250468126), (4322, 4322, 18252776734641152121), (4323, 4323, 18254697203344799641), (4324, 4324, 18256598657506826888), (4325, 4325, 18258481285390022182), (4326, 4326, 18260345273393185840), (4327, 4327, 18262190806069585501), (4328, 4328, 18264018066145228730), (4329, 4329, 18265827234536954699), (4330, 4330, 18267618490370346748), (4331, 4331, 18269392010997467588), (4332, 4332, 18271147972014418915), (4333, 4333, 18272886547278727160), (4334, 4334, 18274607908926557105), (4335, 4335, 18276312227389755070), (4336, 4336, 18277999671412723353), (4337, 4337, 18279670408069127593), (4338, 4338, 18281324602778438722), (4339, 4339, 18282962419322311127), (4340, 4340, 18284584019860798657), (4341, 4341, 18286189564948410072), (4342, 4342, 18287779213550005533), (4343, 4343, 18289353123056535692), (4344, 4344, 18290911449300624959), (4345, 4345, 18292454346572000470), (4346, 4346, 18293981967632768303), (4347, 4347, 18295494463732538435), (4348, 4348, 18296991984623399952), (4349, 7209, 18446744073709486765)]

def glob3 : ℕ := 18446744073709551616

def runs4 : List (ℕ × ℕ × ℕ) := [(0, 3000, 188254050244167582370), (3001, 3001, 188255023189553912968), (3002, 3002, 188256005871199006979), (3003, 3003, 188256998386602284878), (3004, 3004, 188258000834240913330), (3005, 3005, 188259013313579638021), (3006, 3006, 188260035925080715924), (3007, 3007, 188261068770213948031), (3008, 3008, 188262111951466813565), (3009, 3009, 188263165572354706724), (3010, 3010, 188264229737431276997), (3011, 3011, 188265304552298874109), (3012, 3012, 188266390123619098683), (3013, 3013, 188267486559123459678), (3014, 3014, 188268593967624139713), (3015, 3015, 188269712459024869385), (3016, 3016, 188270842144331911674), (3017, 3017, 188271983135665157599), (3018, 3018, 188273135546269334227), (3019, 3019, 188274299490525326226), (3020, 3020, 188275475083961612089), (3021, 3021, 188276662443265816234), (3022, 3022, 188277861686296378154), (3023, 3023, 188279072932094339825), (3024, 3024, 188280296300895252583), (3025, 3025, 188281531914141204695), (3026, 3026, 188282779894492970868), (3027, 3027, 188284040365842284951), (3028, 3028, 188285313453324237084), (3029, 3029, 188286599283329796592), (3030, 3030, 188287897983518461893), (3031, 3031, 188289209682831038753), (3032, 3032, 188290534511502548191), (3033, 3033, 188291872601075265366), (3034, 3034, 188293224084411890810), (3035, 3035, 188294589095708855354), (3036, 3036, 188295967770509760139), (3037, 3037, 188297360245718953082), (3038, 3038, 188298766659615243228), (3039, 3039, 188300187151865754394), (3040, 3040, 188301621863539919546), (3041, 3041, 188303070937123617353), (3042, 3042, 188304534516533452407), (3043, 3043, 188306012747131180557), (3044, 3044, 188307505775738280891), (3045, 3045, 188309013750650675858), (3046, 3046, 188310536821653601058), (3047, 3047, 188312075140036626274), (3048, 3048, 188313628858608829267), (3049, 3049, 188315198131714123958), (3050, 3050, 188316783115246744559), (3051, 3051, 188318383966666887283), (3052, 3052, 188320000845016511268), (3053, 3053, 188321633910935300343), (3054, 3054, 188323283326676787331), (3055, 3055, 188324949256124642544), (3056, 3056, 188326631864809128194), (3057, 3057, 188328331319923720426), (3058, 3058, 188330047790341900716), (3059, 3059, 188331781446634118399), (3060, 3060, 188333532461084926082), (3061, 3061, 188335301007710289766), (3062, 3062, 188337087262275075461), (3063, 3063, 188338891402310714157), (3064, 3064, 188340713607133046975), (3065, 3065, 188342554057860352400), (3066, 3066, 188344412937431557468), (3067, 3067, 188346290430624634832), (3068, 3068, 188348186724075187637), (3069, 3069, 188350102006295224166), (3070, 3070, 188352036467692124225), (3071, 3071, 188353990300587799271), (3072, 3072, 188355963699238048300), (3073, 3073, 188357956859852111540), (3074, 3074, 188359969980612424007), (3075, 3075, 188362003261694571016), (3076, 3076, 188364056905287447753), (3077, 3077, 188366131115613625035), (3078, 3078, 188368226098949923426), (3079, 3079, 188370342063648197867), (3080, 3080, 188372479220156335045), (3081, 3081, 188374637781039465703), (3082, 3082, 188376817961001394165), (3083, 3083, 188379019976906247329), (3084, 3084, 188381244047800345443), (3085, 3085, 188383490394934296977), (3086, 3086, 188385759241785319953), (3087, 3087, 188388050814079792098), (3088, 3088, 188390365339816032223), (3089, 3089, 188392703049287315266), (3090, 3090, 188395064175105123442), (3091, 3091, 188397448952222635980), (3092, 3092, 188399857617958459975), (3093, 3093, 188402290412020604863), (3094, 3094, 188404747576530703109), (3095, 3095, 188407229356048479683), (3096, 3096, 188409735997596472951), (3097, 3097, 188412267750685009640), (3098, 3098, 188414824867337436534), (3099, 3099, 188417407602115611634), (3100, 3100, 188420016212145657506), (3101, 3101, 188422650957143979588), (3102, 3102, 188425312099443552260), (3103, 3103, 188427999904020475507), (3104, 3104, 188430714638520805030), (3105, 3105, 188433456573287658711), (3106, 3106, 188436225981388602345), (3107, 3107, 188439023138643317608), (3108, 3108, 188441848323651555250), (3109, 3109, 188444701817821376534), (3110, 3110, 188447583905397685979), (3111, 3111, 188450494873491058511), (3112, 3112, 188453435012106864137), (3113, 3113, 188456404614174693309), (3114, 3114, 188459403975578086177), (3115, 3115, 188462433395184568961), (3116, 3116, 188465493174876000721), (3117, 3117, 188468583619579233814), (3118, 3118, 188471705037297091408), (3119, 3119, 188474857739139665403), (3120, 3120, 188478042039355938212), (3121, 3121, 188481258255365731828), (3122, 3122, 188484506707791987700), (3123, 3123, 188487787720493380942), (3124, 3124, 188491101620597272453), (3125, 3125, 188494448738533002562), (3126, 3126, 188497829408065529874), (3127, 3127, 188501243966329418986), (3128, 3128, 188504692753863180849), (3129, 3129, 188508176114643969528), (3130, 3130, 188511694396122639220), (3131, 3131, 188515247949259165365), (3132, 3132, 188518837128558433804), (3133, 3133, 188522462292106401909), (3134, 3134, 188526123801606635713), (3135, 3135, 188529822022417227083), (3136, 3136, 188533557323588095035), (3137, 3137, 188537330077898675331), (3138, 3138, 188541140661896002558), (3139, 3139, 188544989455933188923), (3140, 3140, 188548876844208304058), (3141, 3141, 188552803214803660168), (3142, 3142, 188556768959725506915), (3143, 3143, 188560774474944140478), (3144, 3144, 188564820160434431277), (3145, 3145, 188568906420216774900), (3146, 3146, 188573033662398470842), (3147, 3147, 188577202299215533690), (3148, 3148, 188581412747074941459), (3149, 3149, 188585665426597325852), (3150, 3150, 188589960762660109232), (3151, 3151, 188594299184441093197), (3152, 3152, 188598681125462503671), (3153, 3153, 188603107023635497502), (3154, 3154, 188607577321305135599), (3155, 3155, 188612092465295827725), (3156, 3156, 188616652906957254089), (3157, 3157, 188621259102210768975), (3158, 3158, 188625911511596291673), (3159, 3159, 188630610600319690081), (3160, 3160, 188635356838300662360), (3161, 3161, 188640150700221122135), (3162, 3162, 188644992665574092769), (3163, 3163, 188649883218713116315), (3164, 3164, 188654822848902182812), (3165, 3165, 188659812050366185669), (3166, 3166, 188664851322341908939), (3167, 3167, 188669941169129552340), (3168, 3168, 188675082100144800005), (3169, 3169, 188680274629971438930), (3170, 3170, 188685519278414533244), (3171, 3171, 188690816570554160441), (3172, 3172, 188696167036799715812), (3173, 3173, 188701571212944791383), (3174, 3174, 188707029640222635759), (3175, 3175, 188712542865362201303), (3176, 3176, 188718111440644785229), (3177, 3177, 188723735923961271187), (3178, 3178, 188729416878869978079), (3179, 3179, 188735154874655122844), (3180, 3180, 188740950486385904110), (3181, 3181, 188746804294976213631), (3182, 3182, 188752716887244982558), (3183, 3183, 188758688855977169643), (3184, 3184, 188764720799985398589), (3185, 3185, 188770813324172251837), (3186, 3186, 188776967039593228155), (3187, 3187, 188783182563520371517), (3188, 3188, 188789460519506578821), (3189, 3189, 188795801537450594104), (3190, 3190, 188802206253662697006), (3191, 3191, 188808675310931093323), (3192, 3192, 188815209358589015588), (3193, 3193, 188821809052582541730), (3194, 3194, 188828475055539139936), (3195, 3195, 188835208036836947967), (3196, 3196, 188842008672674795267), (3197, 3197, 188848877646142976310), (3198, 3198, 188855815647294783739), (3199, 3199, 188862823373218809951), (3200, 3200, 188869901528112025904), (3201, 3201, 188877050823353646017), (3202, 3202, 188884271977579788146), (3203, 3203, 188891565716758937750), (3204, 3204, 188898932774268225451), (3205, 3205, 188906373890970527331), (3206, 3206, 188913889815292397404), (3207, 3207, 188921481303302841846), (3208, 3208, 188929149118792944659), (3209, 3209, 188936894033356354603), (3210, 3210, 188944716826470643311), (3211, 3211, 188952618285579544678), (3212, 3212, 188960599206176085694), (3213, 3213, 188968660391886619068), (3214, 3214, 188976802654555768081), (3215, 3215, 188985026814332294271), (3216, 3216, 188993333699755898673), (3217, 3217, 189001724147844967479), (3218, 3218, 189010199004185273127), (3219, 3219, 189018759123019641956), (3220, 3220, 189027405367338599738), (3221, 3221, 189036138608972006504), (3222, 3222, 189044959728681692270), (3223, 3223, 189053869616255105382), (3224, 3224, 189062869170599985393), (3225, 3225, 189071959299840072492), (3226, 3226, 189081140921411865718), (3227, 3227, 189090414962162442295), (3228, 3228, 189099782358448350630), (3229, 3229, 189109244056235589669), (3230, 3230, 189118801011200687449), (3231, 3231, 189128454188832891896), (3232, 3232, 189138204564537487056), (3233, 3233, 189148053123740248142), (3234, 3234, 189158000861993048939), (3235, 3235, 189168048785080635314), (3236, 3236, 189178197909128578736), (3237, 3237, 189188449260712423917), (3238, 3238, 189198803876968044854), (3239, 3239, 189209262805703223767), (3240, 3240, 189219827105510467599), (3241, 3241, 189230497845881076955), (3242, 3242, 189241276107320482563), (3243, 3243, 189252162981464864519), (3244, 3244, 189263159571199069820), (3245, 3245, 189274266990775843864), (3246, 3246, 189285486365936391833), (3247, 3247, 189296818834032286087), (3248, 3248, 189308265544148735905), (3249, 3249, 189319827657229236148), (3250, 3250, 189331506346201611634), (3251, 3251, 189343302796105474257), (3252, 3252, 189355218204221110103), (3253, 3253, 189367253780199814063), (3254, 3254, 189379410746195689678), (3255, 3255, 189391690336998932212), (3256, 3256, 189404093800170613163), (3257, 3257, 189416622396178984727), (3258, 3258, 189429277398537322934), (3259, 3259, 189442060093943328470), (3260, 3260, 189454971782420104461), (3261, 3261, 189468013777458730751), (3262, 3262, 189481187406162454483), (3263, 3263, 189494494009392517095), (3264, 3264, 189507934941915638079), (3265, 3265, 189521511572553176188), (3266, 3266, 189535225284331989039), (3267, 3267, 189549077474637012356), (3268, 3268, 189563069555365580414), (3269, 3269, 189577202953083509549), (3270, 3270, 189591479109182966888), (3271, 3271, 189605899480042146812), (3272, 3272, 189620465537186777935), (3273, 3273, 189635178767453483762), (3274, 3274, 189650040673155020478), (3275, 3275, 189665052772247415684), (3276, 3276, 189680216598499032235), (3277, 3277, 189695533701661581668), (3278, 3278, 189711005647643112094), (3279, 3279, 189726634018682995760), (3280, 3280, 189742420413528941866), (3281, 3281, 189758366447616060601), (3282, 3282, 189774473753248004730), (3283, 3283, 189790743979780215458), (3284, 3284, 189807178793805299683), (3285, 3285, 189823779879340566157), (3286, 3286, 189840548938017748473), (3287, 3287, 189857487689274943210), (3288, 3288, 189874597870550791987), (3289, 3289, 189891881237480936611), (3290, 3290, 189909339564096776926), (3291, 3291, 189926974643026561414), (3292, 3292, 189944788285698841062), (3293, 3293, 189962782322548317446), (3294, 3294, 189980958603224116455), (3295, 3295, 189999318996800519561), (3296, 3296, 190017865391990184996), (3297, 3297, 190036599697359891723), (3298, 3298, 190055523841548839538), (3299, 3299, 190074639773489539199), (3300, 3300, 190093949462631326943), (3301, 3301, 190113454899166538310), (3302, 3302, 190133158094259376718), (3303, 3303, 190153061080277512753), (3304, 3304, 190173165911026450730), (3305, 3305, 190193474661986699608), (3306, 3306, 190213989430553785920), (3307, 3307, 190234712336281146986), (3308, 3308, 190255645521125943222), (3309, 3309, 190276791149697829007), (3310, 3310, 190298151409510722154), (3311, 3311, 190319728511237612659), (3312, 3312, 190341524688968452049), (3313, 3313, 190363542200471165277), (3314, 3314, 190385783327455827789), (3315, 3315, 190408250375842051045), (3316, 3316, 190430945676029620459), (3317, 3317, 190453871583172430417), (3318, 3318, 190477030477455761748), (3319, 3319, 190500424764376947723), (3320, 3320, 190524056875029475410), (3321, 3321, 190547929266390569937), (3322, 3322, 190572044421612309991), (3323, 3323, 190596404850316323654), (3324, 3324, 190621013088892114440), (3325, 3325, 190645871700799068231), (3326, 3326, 190670983276872192607), (3327, 3327, 190696350435631640892), (3328, 3328, 190721975823596074097), (3329, 3329, 190747862115599914806), (3330, 3330, 190774012015114547894), (3331, 3331, 190800428254573523919), (3332, 3332, 190827113595701821884), (3333, 3333, 190854070829849229024), (3334, 3334, 190881302778327896209), (3335, 3335, 190908812292754128523), (3336, 3336, 190936602255394471542), (3337, 3337, 190964675579516154857), (3338, 3338, 190993035209741955392), (3339, 3339, 191021684122409544094), (3340, 3340, 191050625325935380652), (3341, 3341, 191079861861183221970), (3342, 3342, 191109396801837311190), (3343, 3343, 191139233254780315233), (3344, 3344, 191169374360476079901), (3345, 3345, 191199823293357272797), (3346, 3346, 191230583262217985479), (3347, 3347, 191261657510611367451), (3348, 3348, 191293049317252365878), (3349, 3349, 191324761996425646100), (3350, 3350, 191356798898398769335), (3351, 3351, 191389163409840705260), (3352, 3352, 191421858954245758470), (3353, 3353, 191454888992362989175), (3354, 3354, 191488257022631209876), (3355, 3355, 191521966581619641161), (3356, 3356, 191556021244474311199), (3357, 3357, 191590424625370284960), (3358, 3358, 191625180377969810691), (3359, 3359, 191660292195886472695), (3360, 3360, 191695763813155440989), (3361, 3361, 191731599004709910027), (3362, 3362, 191767801586863820248), (3363, 3363, 191804375417800957889), (3364, 3364, 191841324398070530141), (3365, 3365, 191878652471089314450), (3366, 3366, 191916363623650482523), (3367, 3367, 191954461886439201326), (3368, 3368, 191992951334555115242), (3369, 3369, 192031836088041815326), (3370, 3370, 192071120312423403554), (3371, 3371, 192110808219248261828), (3372, 3372, 192150904066640137496), (3373, 3373, 192191412159856659124), (3374, 3374, 192232336851855398322), (3375, 3375, 192273682543867595479), (3376, 3376, 192315453685979669421), (3377, 3377, 192357654777722633143), (3378, 3378, 192400290368669540004), (3379, 3379, 192443365059041087010), (3380, 3380, 192486883500319504141), (3381, 3381, 192530850395870860989), (3382, 3382, 192575270501575924429), (3383, 3383, 192620148626469703433), (3384, 3384, 192665489633389819692), (3385, 3385, 192711298439633845220), (3386, 3386, 192757580017625750748), (3387, 3387, 192804339395591611357), (3388, 3388, 192851581658244718519), (3389, 3389, 192899311947480250484), (3390, 3390, 192947535463079655790), (3391, 3391, 192996257463424907538), (3392, 3392, 193045483266222789035), (3393, 3393, 193095218249239374441), (3394, 3394, 193145467851044871076), (3395, 3395, 193196237571768993234), (3396, 3396, 193247532973867040533), (3397, 3397, 193299359682896857093), (3398, 3398, 193351723388306851205), (3399, 3399, 193404629844235258537), (3400, 3400, 193458084870320835437), (3401, 3401, 193512094352525172430), (3402, 3402, 193566664243966821662), (3403, 3403, 193621800565767435745), (3404, 3404, 193677509407910119275), (3405, 3405, 193733796930110198133), (3406, 3406, 193790669362698615688), (3407, 3407, 193848133007518169032), (3408, 3408, 193906194238832802521), (3409, 3409, 193964859504250180134), (3410, 3410, 194024135325657762461), (3411, 3411, 194084028300172618546), (3412, 3412, 194144545101105207335), (3413, 3413, 194205692478937368051), (3414, 3414, 194267477262314763562), (3415, 3415, 194329906359054025607), (3416, 3416, 194392986757164855629), (3417, 3417, 194456725525887340061), (3418, 3418, 194521129816744743971), (3419, 3419, 194586206864612052278), (3420, 3420, 194651963988800533092), (3421, 3421, 194718408594158603230), (3422, 3422, 194785548172189281569), (3423, 3423, 194853390302184521625), (3424, 3424, 194921942652376720620), (3425, 3425, 194991212981107708304), (3426, 3426, 195061209138015524901), (3427, 3427, 195131939065239303861), (3428, 3428, 195203410798642581467), (3429, 3429, 195275632469055361948), (3430, 3430, 195348612303535273406), (3431, 3431, 195422358626648156787), (3432, 3432, 195496879861768437075), (3433, 3433, 195572184532399633113), (3434, 3434, 195648281263515369782), (3435, 3435, 195725178782921263762), (3436, 3436, 195802885922638061811), (3437, 3437, 195881411620306418337), (3438, 3438, 195960764920613707081), (3439, 3439, 196040954976743269969), (3440, 3440, 196121991051846514601), (3441, 3441, 196203882520538280449), (3442, 3442, 196286638870415902692), (3443, 3443, 196370269703602411579), (3444, 3444, 196454784738314314493), (3445, 3445, 196540193810454417330), (3446, 3446, 196626506875230151449), (3447, 3447, 196713734008797882388), (3448, 3448, 196801885409933686665), (3449, 3449, 196890971401731093331), (3450, 3450, 196981002433326297615), (3451, 3451, 197071989081651364816), (3452, 3452, 197163942053215953779), (3453, 3453, 197256872185918100661), (3454, 3454, 197350790450884615380), (3455, 3455, 197445707954341655085), (3456, 3456, 197541635939516051227), (3457, 3457, 197638585788567979350), (3458, 3458, 197736569024555573552), (3459, 3459, 197835597313432100716), (3460, 3460, 197935682466076323094), (3461, 3461, 198036836440356691595), (3462, 3462, 198139071343230026283), (3463, 3463, 198242399432875355062), (3464, 3464, 198346833120863596361), (3465, 3465, 198452384974363786809), (3466, 3466, 198559067718386570497), (3467, 3467, 198666894238065682337), (3468, 3468, 198775877580978174418), (3469, 3469, 198886030959504150972), (3470, 3470, 198997367753226794769), (3471, 3471, 199109901511373485339), (3472, 3472, 199223645955298827449), (3473, 3473, 199338614981010426781), (3474, 3474, 199454822661738268667), (3475, 3475, 199572283250548575200), (3476, 3476, 199691011183003035937), (3477, 3477, 199811021079864327827), (3478, 3478, 199932327749848860961), (3479, 3479, 200054946192427708159), (3480, 3480, 200178891600676698478), (3481, 3481, 200304179364176677245), (3482, 3482, 200430825071964958412), (3483, 3483, 200558844515539018750), (3484, 3484, 200688253691913507749), (3485, 3485, 200819068806731672082), (3486, 3486, 200951306277432319110), (3487, 3487, 201084982736473470181), (3488, 3488, 201220115034613881442), (3489, 3489, 201356720244253637574), (3490, 3490, 201494815662835052198), (3491, 3491, 201634418816305137877), (3492, 3492, 201775547462640938493), (3493, 3493, 201918219595439047459), (3494, 3494, 202062453447570666720), (3495, 3495, 202208267494903593775), (3496, 3496, 202355680460092557141), (3497, 3497, 202504711316439354695), (3498, 3498, 202655379291824284301), (3499, 3499, 202807703872710391964), (3500, 3500, 202961704808222099616), (3501, 3501, 203117402114299812428), (3502, 3502, 203274816077932144382), (3503, 3503, 203433967261467440707), (3504, 3504, 203594876507006316711), (3505, 3505, 203757564940876974607), (3506, 3506, 203922053978195103126), (3507, 3507, 204088365327510209030), (3508, 3508, 204256520995540275253), (3509, 3509, 204426543291996687180), (3510, 3510, 204598454834501416654), (3511, 3511, 204772278553598502744), (3512, 3512, 204948037697861919023), (3513, 3513, 205125755839101969313), (3514, 3514, 205305456877672407432), (3515, 3515, 205487165047880531560), (3516, 3516, 205670904923502560486), (3517, 3517, 205856701423406657166), (3518, 3518, 206044579817286024835), (3519, 3519, 206234565731504562436), (3520, 3520, 206426685155057629304), (3521, 3521, 206620964445650534058), (3522, 3522, 206817430335897429470), (3523, 3523, 207016109939643363794), (3524, 3524, 207217030758412309686), (3525, 3525, 207420220687984064524), (3526, 3526, 207625708025102990671), (3527, 3527, 207833521474321641071), (3528, 3528, 208043690154982394686), (3529, 3529, 208256243608340307556), (3530, 3530, 208471211804830469007), (3531, 3531, 208688625151483238595), (3532, 3532, 208908514499490827952), (3533, 3533, 209130911151928782893), (3534, 3534, 209355846871636014908), (3535, 3535, 209583353889257127747), (3536, 3536, 209813464911450884133), (3537, 3537, 210046213129268759957), (3538, 3538, 210281632226707638564), (3539, 3539, 210519756389440806150), (3540, 3540, 210760620313731520875), (3541, 3541, 211004259215533543200), (3542, 3542, 211250708839783133274), (3543, 3543, 211500005469887143036), (3544, 3544, 211752185937411956174), (3545, 3545, 212007287631978158336), (3546, 3546, 212265348511365953093), (3547, 3547, 212526407111836476312), (3548, 3548, 212790502558674302836), (3549, 3549, 213057674576956584957), (3550, 3550, 213327963502554412123), (3551, 3551, 213601410293372135863), (3552, 3552, 213878056540830563179), (3553, 3553, 214157944481600085788), (3554, 3554, 214441117009589981777), (3555, 3555, 214727617688200300630), (3556, 3556, 215017490762842922327), (3557, 3557, 215310781173738566607), (3558, 3558, 215607534568996719527), (3559, 3559, 215907797317985641525), (3560, 3560, 216211616524999824397), (3561, 3561, 216519040043232474128), (3562, 3562, 216830116489060812689), (3563, 3563, 217144895256652214854), (3564, 3564, 217463426532899426061), (3565, 3565, 217785761312693344648), (3566, 3566, 218111951414542096566), (3567, 3567, 218442049496545383318), (3568, 3568, 218776109072733344517), (3569, 3569, 219114184529779445499), (3570, 3570, 219456331144097178101), (3571, 3571, 219802605099330649323), (3572, 3572, 220153063504249428467), (3573, 3573, 220507764411058328832), (3574, 3574, 220866766834133115429), (3575, 3575, 221230130769193455837), (3576, 3576, 221597917212924767689), (3577, 3577, 221970188183060963573), (3578, 3578, 222347006738940452954), (3579, 3579, 222728437002548131275), (3580, 3580, 223114544180056469315), (3581, 3581, 223505394583879211377), (3582, 3582, 223901055655251599668), (3583, 3583, 224301595987351464540), (3584, 3584, 224707085348975956800), (3585, 3585, 225117594708789149421), (3586, 3586, 225533196260156202343), (3587, 3587, 225953963446580266136), (3588, 3588, 226379970987758798724), (3589, 3589, 226811294906276484700), (3590, 3590, 227248012554952479710), (3591, 3591, 227690202644860253472), (3592, 3592, 228137945274038875044), (3593, 3593, 228591321956915173569), (3594, 3594, 229050415654456817665), (3595, 3595, 229515310805076987728), (3596, 3596, 229986093356311968320), (3597, 3597, 230462850797293663547), (3598, 3598, 230945672192039737575), (3599, 3599, 231434648213584806225), (3600, 3600, 231929871178976854744), (3601, 3601, 232431435085163832480), (3602, 3602, 232939435645796178169), (3603, 3603, 233453970328971861028), (3604, 3604, 233975138395951383886), (3605, 3605, 234503040940871086396), (3606, 3606, 235037780931484010002), (3607, 3607, 235579463250958543227), (3608, 3608, 236128194740766057149), (3609, 3609, 236684084244689768040), (3610, 3610, 237247242653988128500), (3611, 3611, 237817782953747151475), (3612, 3612, 238395820270457214785), (3613, 3613, 238981471920851078940), (3614, 3614, 239574857462041079557), (3615, 3615, 240176098742994729597), (3616, 3616, 240785319957389287473), (3617, 3617, 241402647697887216953), (3618, 3618, 242028211011875885533), (3619, 3619, 242662141458716321706), (3620, 3620, 243304573168547380456), (3621, 3621, 243955642902693252568), (3622, 3622, 244615490115723899403), (3623, 3623, 245284257019219702959), (3624, 3624, 245962088647293394026), (3625, 3625, 246649132923924161609), (3626, 3626, 247345540732160757403), (3627, 3627, 248051465985252392826), (3628, 3628, 248767065699768286034), (3629, 3629, 249492500070768855632), (3630, 3630, 250227932549093779762), (3631, 3631, 250973529920834447448), (3632, 3632, 251729462389060727020), (3633, 3633, 252495903657874468099), (3634, 3634, 253273031018864742826), (3635, 3635, 254061025440042523004), (3636, 3636, 254860071657335286975), (3637, 3637, 255670358268724957808), (3638, 3638, 256492077831115597674), (3639, 3639, 257325426960020426938), (3640, 3640, 258170606432161005855), (3641, 3641, 259027821291074817233), (3642, 3642, 259897280955831025751), (3643, 3643, 260779199332957869773), (3644, 3644, 261673794931688970784), (3645, 3645, 262581290982639830554), (3646, 3646, 263501915560029933662), (3647, 3647, 264435901707570190375), (3648, 3648, 265383487568139949561), (3649, 3649, 266344916517382491267), (3650, 3650, 267320437301352782185), (3651, 3651, 268310304178356353025), (3652, 3652, 269314777065123444116), (3653, 3653, 270334121687468073796), (3654, 3654, 271368609735587423452), (3655, 3655, 272418519024162913969), (3656, 3656, 273484133657430581812), (3657, 3657, 274565744199394860740), (3658, 3658, 275663647849366649247), (3659, 3659, 276778148623013607167), (3660, 3660, 277909557539117990776), (3661, 3661, 279058192812245018311), (3662, 3662, 280224380051532771921), (3663, 3663, 281408452465823003118), (3664, 3664, 282610751075360933249), (3665, 3665, 283831624930301245417), (3666, 3666, 285071431336266967723), (3667, 3667, 286330536087217868605), (3668, 3668, 287609313705895343334), (3669, 3669, 288908147692121587340), (3670, 3670, 290227430779242148993), (3671, 3671, 291567565199012754921), (3672, 3672, 292928962955243629282), (3673, 3673, 294312046106527410253), (3674, 3674, 295717247058390229304), (3675, 3675, 297145008865219590053), (3676, 3676, 298595785542337393448), (3677, 3677, 300070042388601836244), (3678, 3678, 301568256319937993326), (3679, 3679, 303090916214213716324), (3680, 3680, 304638523267895077859), (3681, 3681, 306211591364934001538), (3682, 3682, 307810647458359983138), (3683, 3683, 309436231965067971472), (3684, 3684, 311088899174315583469), (3685, 3685, 312769217670464924927), (3686, 3686, 314477770770527426638), (3687, 3687, 316215156977094338367), (3688, 3688, 317981990447260906574), (3689, 3689, 319778901478178855144), (3690, 3690, 321606537009899654163), (3691, 3691, 323465561146200265973), (3692, 3692, 325356655694113670070), (3693, 3693, 327280520722918562422), (3694, 3694, 329237875143376278221), (3695, 3695, 331229457308038282039), (3696, 3696, 333256025633484592615), (3697, 3697, 335318359245392352727), (3698, 3698, 337417258647374514740), (3699, 3699, 339553546414571391913), (3700, 3700, 341728067913022732832), (3701, 3701, 343941692045895125923), (3702, 3702, 346195312027689054263), (3703, 3703, 348489846187601926052), (3704, 3704, 350826238803278039042), (3705, 3705, 353205460966233841560), (3706, 3706, 355628511480307180837), (3707, 3707, 358096417794542642303), (3708, 3708, 360610236971991752012), (3709, 3709, 363171056695976919450), (3710, 3710, 365779996315441731200), (3711, 3711, 368438207931087770599), (3712, 3712, 371146877524079749921), (3713, 3713, 373907226129186628301), (3714, 3714, 376720511054316792736), (3715, 3715, 379588027148500558118), (3716, 3716, 382511108120473468151), (3717, 3717, 385491127910119441521), (3718, 3718, 388529502115144014188), (3719, 3719, 391627689475465105404), (3720, 3720, 394787193417932228547), (3721, 3721, 398009563664115246224), (3722, 3722, 401296397904041023503), (3723, 3723, 404649343538901079268), (3724, 3724, 408070099495906015554), (3725, 3725, 411560418118623588087), (3726, 3726, 415122107136307268112), (3727, 3727, 418757031715901567385), (3728, 3728, 422467116600599820847), (3729, 3729, 426254348339030147048), (3730, 3730, 430120777609356575856), (3731, 3731, 434068521642805529036), (3732, 3732, 438099766751363688866), (3733, 3733, 442216770964642567742), (3734, 3734, 446421866781168623086), (3735, 3735, 450717464039636426608), (3736, 3736, 455106052915957133276), (3737, 3737, 459590207052246303433), (3738, 3738, 464172586824225078716), (3739, 3739, 468855942753857937307), (3740, 3740, 473643119074419971931), (3741, 3741, 478537057455578142278), (3742, 3742, 483540800896485637561), (3743, 3743, 488657497795327824562), (3744, 3744, 493890406204223832710), (3745, 3745, 499242898278881330232), (3746, 3746, 504718464932925280317), (3747, 3747, 510320720707376364934), (3748, 3748, 516053408866343392200), (3749, 3749, 521920406730618570877), (3750, 3750, 527925731261527408017), (3751, 3751, 534073544908088694497), (3752, 3752, 540368161731287299292), (3753, 3753, 546814053820056200231), (3754, 3754, 553415858014407447644), (3755, 3755, 560178382952047921356), (3756, 3756, 567106616455768374857), (3757, 3757, 574205733279907195297), (3758, 3758, 581481103235267654660), (3759, 3759, 588938299713013596413), (3760, 3760, 596583108629288226287), (3761, 3761, 604421537813599037302), (3762, 3762, 612459826865394354627), (3763, 3763, 620704457504729397501), (3764, 3764, 629162164444488422311), (3765, 3765, 637839946813301203632), (3766, 3766, 646745080160074108702), (3767, 3767, 655885129072956155158), (3768, 3768, 665267960447587136004), (3769, 3769, 674901757441637215887), (3770, 3770, 684795034154955108897), (3771, 3771, 694956651077105551316), (3772, 3772, 705395831346707605739), (3773, 3773, 716122177869795577344), (3774, 3774, 727145691347427141508), (3775, 3775, 738476789265972857061), (3776, 3776, 750126325906952869559), (3777, 3777, 762105613436956801379), (3778, 3778, 774426444142109397845), (3779, 3779, 787101113875746689753), (3780, 3780, 800142446792466022711), (3781, 3781, 813563821446530745257), (3782, 3782, 827379198337770909128), (3783, 3783, 841603148993651255972), (3784, 3784, 856250886682105426672), (3785, 3785, 871338298856091440697), (3786, 3786, 886881981437641291995), (3787, 3787, 902899275056492984147), (3788, 3788, 919408303366245463196), (3789, 3789, 936428013569407940809), (3790, 3790, 953978219291770818352), (3791, 3791, 972079645956255470749), (3792, 3792, 990753978816858381792), (3793, 3793, 1010023913824549979756), (3794, 3794, 1029913211509083443545), (3795, 3795, 1050446754073682628988), (3796, 3796, 1071650605913585947260), (3797, 3797, 1093552077784505854251), (3798, 3798, 1116179794863310017269), (3799, 3799, 1139563768960736400607), (3800, 3800, 1163735475164825112595), (3801, 3801, 1188727933214098803986), (3802, 3802, 1214575793921474752764), (3803, 3803, 1241315430993580651685), (3804, 3804, 1268985038615719806799), (3805, 3805, 1297624735200350524532), (3806, 3806, 1327276673726784041388), (3807, 3807, 1357985159132056526692), (3808, 3808, 1389796773247802062428), (3809, 3809, 1422760507815672875727), (3810, 3810, 1456927906154669345934), (3811, 3811, 1492353214097927447962), (3812, 3812, 1529093540864362766217), (3813, 3813, 1567209030582413394925), (3814, 3814, 1606763045239315022399), (3815, 3815, 1647822359890270155419), (3816, 3816, 1690457371027966831017), (3817, 3817, 1734742319084628274504), (3818, 3818, 1780755526116646867429), (3819, 3819, 1828579649806436242222), (3820, 3820, 1878301955008041849834), (3821, 3821, 1930014604162960895373), (3822, 3822, 1983814968021281715529), (3823, 3823, 2039805958221478695776), (3824, 3824, 2098096383410891211057), (3825, 3825, 2158801330729063182711), (3826, 3826, 2222042574628812375534), (3827, 3827, 2287949015176334094890), (3828, 3828, 2356657148153142679628), (3829, 3829, 2428311569480670974666), (3830, 3830, 2503065516704486838239), (3831, 3831, 2581081450511116070898), (3832, 3832, 2662531679508335687189), (3833, 3833, 2747599031781676371749), (3834, 3834, 2836477577048130297769), (3835, 3835, 2929373403565333102717), (3836, 3836, 3026505454323688323402), (3837, 3837, 3128106427453250517914), (3838, 3838, 3234423746220245937185), (3839, 3839, 3345720604473836977175), (3840, 3840, 3462277093936506101780), (3841, 3841, 3584391420316099986181), (3842, 3842, 3712381215859519636467), (3843, 3843, 3846584956673243667758), (3844, 3844, 3987363493910967108657), (3845, 3845, 4135101708781002377797), (3846, 3846, 4290210302263922374014), (3847, 3847, 4453127731463349737043), (3848, 3848, 4624322305649964302165), (3849, 3849, 4804294456312019843809), (3850, 3850, 4993579196907531270884), (3851, 3851, 5192748789537862893480), (3852, 3852, 5402415637445389740837), (3853, 3853, 5623235424096711809099), (3854, 3854, 5855910521667115677047), (3855, 3855, 6101193694013436900028), (3856, 3856, 6359892121735600155105), (3857, 3857, 6632871779709226756227), (3858, 3858, 6921062200553393729370), (3859, 3859, 7225461660913178291480), (3860, 3860, 7547142831224446291523), (3861, 3861, 7887258933831538351008), (3862, 3862, 8247050458995443279993), (3863, 3863, 8627852493515049869199), (3864, 3864, 9031102722448187314354), (3865, 3877, 9127591108378997631599), (3878, 3878, 9058011772268443552824), (3879, 3879, 8968328487394498567153), (3880, 3880, 8879533155836137195201), (3881, 3881, 8791616985976373460595), (3882, 3882, 8704571273243934119401), (3883, 3883, 8618387399251419920199), (3884, 3884, 8533056830941999920989), (3885, 3885, 8448571119744554377217), (3886, 3886, 8364921900737182551700), (3887, 3887, 8282100891818992625445), (3888, 3888, 8200099892890091708362), (3889, 3889, 8118910785039694760754), (3890, 3890, 8038525529742272040351), (3891, 3891, 7958936168061655485496), (3892, 3892, 7880134819863025233164), (3893, 3893, 7802113683032698250657), (3894, 3894, 7724865032705641832334), (3895, 3895, 7648381220500635477558), (3896, 3896, 7572654673763005423325), (3897, 3897, 7497677894814856854777), (3898, 3898, 7423443460212729559186), (3899, 3899, 7349944020012603523946), (3900, 3900, 7277172297042181706877), (3901, 3901, 7205121086180377927601), (3902, 3902, 7133783253643938542180), (3903, 3903, 7063151736281127269485), (3904, 3904, 6993219540872403237114), (3905, 3905, 6923979743438023007043), (3906, 3906, 6855425488552498026775), (3907, 3907, 6787549988665839630471), (3908, 3908, 6720346523431524386605), (3909, 3909, 6653808439041113254064), (3910, 3910, 6587929147565458667390), (3911, 3911, 6522702126302434324149), (3912, 3912, 6458120917131123093216), (3913, 3913, 6394179125872399102195), (3914, 3914, 6330870421655840695242), (3915, 3915, 6268188536292911579448), (3916, 3916, 6206127263656348098463), (3917, 3917, 6144680459065691186597), (3918, 3918, 6083842038678902164948), (3919, 3919, 6023605978890002143512), (3920, 3920, 5963966315732675389616), (3921, 3921, 5904917144289777613482), (3922, 3922, 5846452618108690706417), (3923, 3923, 5788566948622466045958), (3924, 3924, 5731254404576699055404), (3925, 3925, 5674509311462078272677), (3926, 3926, 5618326050952552745225), (3927, 3927, 5562699060349062123985), (3928, 3928, 5507622832028774380183), (3929, 3929, 5453091912899776614043), (3930, 3930, 5399100903861164964399), (3931, 3931, 5345644459268480162771), (3932, 3932, 5292717286404435804724), (3933, 3933, 5240314144954886935370), (3934, 3934, 5188429846489987064723), (3935, 3935, 5137059253950482242300), (3936, 3936, 5086197281139091329010), (3937, 3937, 5035838892216922107930), (3938, 3938, 4985979101204873374189), (3939, 3939, 4936612971489973637810), (3940, 3940, 4887735615336607562189), (3941, 3941, 4839342193402581744741), (3942, 3942, 4791427914259981925486), (3943, 3943, 4743988033920774183650), (3944, 3944, 4697017855367103152129), (3945, 3945, 4650512728086240744682), (3946, 3946, 4604468047610139351170), (3947, 3947, 4558879255059543912050), (3948, 3948, 4513741836692617734702), (3949, 3949, 4469051323458037361092), (3950, 3950, 4424803290552512238705), (3951, 3951, 4380993356982685384856), (3952, 3952, 4337617185131371668174), (3953, 3953, 4294670480328090760569), (3954, 3954, 4252148990423852238187), (3955, 3955, 4210048505370150730878), (3956, 3956, 4168364856802129436513), (3957, 3957, 4127093917625870729221), (3958, 3958, 4086231601609772999228), (3959, 3959, 4045773862979973266563), (3960, 3960, 4005716696019775511448), (3961, 3961, 3966056134673045060840), (3962, 3962, 3926788252151529763208), (3963, 3963, 3887909160546069072483), (3964, 3964, 3849415010441652547013), (3965, 3965, 3811301990536289650508), (3966, 3966, 3773566327263653119315), (3967, 3967, 3736204284419458533975), (3968, 3968, 3699212162791543102945), (3969, 3969, 3662586299793607032619), (3970, 3970, 3626323069102581220415), (3971, 3971, 3590418880299585366748), (3972, 3972, 3554870178514440957176), (3973, 3973, 3519673444073703917996), (3974, 3974, 3484825192152182097026), (3975, 3975, 3450321972427903066362), (3976, 3976, 3416160368740498085507), (3977, 3977, 3382336998752968401492), (3978, 3978, 3348848513616800397517), (3979, 3979, 3315691597640396433185), (3980, 3980, 3282862967960788547708), (3981, 3981, 3250359374218602522483), (3982, 3982, 3218177598236240121270), (3983, 3983, 3186314453699247644822), (3984, 3984, 3154766785840839252299), (3985, 3985, 3123531471129543814158), (3986, 3986, 3092605416959944370453), (3987, 3987, 3061985561346479574706), (3988, 3988, 3031668872620276806640), (3989, 3989, 3001652349128986937267), (3990, 3990, 2971933018939591026997), (3991, 3991, 2942507939544149531680), (3992, 3992, 2913374197568464882852), (3993, 3993, 2884528908483628596883), (3994, 3994, 2855969216320424353349), (3995, 3995, 2827692293386558765693), (3996, 3996, 2799695339986691847220), (3997, 3997, 2771975584145239452693), (3998, 3998, 2744530281331920250191), (3999, 3999, 2717356714190020049695), (4000, 4000, 2690452192267346583856), (4001, 4001, 2663814051749848102828), (4002, 4002, 2637439655197869408740), (4003, 4003, 2611326391285019216575), (4004, 4004, 2585471674539622986708), (4005, 4005, 2559872945088735630403), (4006, 4006, 2534527668404688742974), (4007, 4007, 2509433335054147270271), (4008, 4008, 2484587460449650762645), (4009, 4009, 2459987584603614616480), (4010, 4010, 2435631271884766947010), (4011, 4011, 2411516110776996977237), (4012, 4012, 2387639713640591066572), (4013, 4013, 2363999716475832739180), (4014, 4014, 2340593778688943306119), (4015, 4015, 2317419582860339907048), (4016, 4016, 2294474834515188026780), (4017, 4017, 2271757261896225769089), (4018, 4018, 2249264615738837395138), (4019, 4019, 2226994669048353856572), (4020, 4020, 2204945216879558273834), (4021, 4021, 2183114076118374528549), (4022, 4022, 2161499085265717354999), (4023, 4023, 2140098104223482529702), (4024, 4024, 2118909014082655970002), (4025, 4025, 2097929716913520762378), (4026, 4026, 2077158135557941348889), (4027, 4027, 2056592213423704305831), (4028, 4028, 2036229914280895352308), (4029, 4029, 2016069222060292428027), (4030, 4030, 1996108140653754879235), (4031, 4031, 1976344693716588989342), (4032, 4032, 1956776924471870286477), (4033, 4033, 1937402895516703253937), (4034, 4034, 1918220688630399261324), (4035, 4035, 1899228404584553724083), (4036, 4036, 1880424162955003687211), (4037, 4037, 1861806101935647215061), (4038, 4038, 1843372378154106153525), (4039, 4039, 1825121166489214013391), (4040, 4040, 1807050659890310904348), (4041, 4041, 1789159069198327628067), (4042, 4042, 1771444622968641215908), (4043, 4043, 1753905567295684372186), (4044, 4044, 1736540165639291457610), (4045, 4045, 1719346698652763819416), (4046, 4046, 1702323464012637444966), (4047, 4047, 1685468776250136084125), (4048, 4048, 1668780966584293152599), (4049, 4049, 1652258382756725893663), (4050, 4050, 1635899388868045439270), (4051, 4051, 1619702365215886573535), (4052, 4052, 1603665708134541161915), (4053, 4053, 1587787829836179368233), (4054, 4054, 1572067158253642938845), (4055, 4055, 1556502136884794988955), (4056, 4056, 1541091224638410880154), (4057, 4057, 1525832895681594930845), (4058, 4058, 1510725639288707852322), (4059, 4059, 1495767959691789952794), (4060, 4060, 1480958375932465299796), (4061, 4061, 1466295421715312178016), (4062, 4062, 1451777645262685324768), (4063, 4063, 1437403609170975569077), (4064, 4064, 1423171890268292642651), (4065, 4065, 1409081079473557071932), (4066, 4066, 1395129781656987199932), (4067, 4067, 1381316615501967524685), (4068, 4068, 1367640213368284677906), (4069, 4069, 1354099221156717502878), (4070, 4070, 1340692298174967824631), (4071, 4071, 1327418117004918638249), (4072, 4072, 1314275363371206572524), (4073, 4073, 1301262736011095616360), (4074, 4074, 1288378946545639224119), (4075, 4075, 1275622719352118043682), (4076, 4076, 1262992791437740637309), (4077, 4077, 1250487912314594690405), (4078, 4078, 1238106843875836327134), (4079, 4079, 1225848360273105274390), (4080, 4080, 1213711247795153737019), (4081, 4081, 1201694304747676967346), (4082, 4082, 1189796341334333631036), (4083, 4083, 1178016179538944189144), (4084, 4084, 1166352653008855632816), (4085, 4085, 1154804606939461022590), (4086, 4086, 1143370897959862398604), (4087, 4087, 1132050394019665741192), (4088, 4088, 1120841974276896773458), (4089, 4089, 1109744528987026508374), (4090, 4090, 1098756959393095552845), (4091, 4091, 1087878177616926289946), (4092, 4092, 1077107106551412168263), (4093, 4093, 1066442679753873433924), (4094, 4094, 1055883841340468746460), (4095, 4095, 1045429545881652224217), (4096, 4096, 1035078758298665568532), (4097, 4097, 1024830453761055018349), (4098, 4098, 1014683617585202988464), (4099, 4099, 1004637245133864345014), (4100, 4100, 994690341716697371301), (4101, 4101, 984841922491779575545), (4102, 4102, 975091012368098589649), (4103, 4103, 965436645909008504603), (4104, 4104, 955877867236642083765), (4105, 4105, 946413729937269389867), (4106, 4106, 937043296967593455313), (4107, 4107, 927765640561973718132), (4108, 4108, 918579842140568037755), (4109, 4109, 909484992218384195797), (4110, 4110, 900480190315231877026), (4111, 4111, 891564544866566214878), (4112, 4112, 882737173135214074136), (4113, 4113, 873997201123974330828), (4114, 4114, 865343763489083495869), (4115, 4115, 856776003454538114722), (4116, 4116, 848293072727265460121), (4117, 4117, 839894131413134118932), (4118, 4118, 831578347933796157358), (4119, 4119, 823344898944352631047), (4120, 4120, 815192969251834288166), (4121, 4121, 807121751734489394224), (4122, 4122, 799130447261870687350), (4123, 4123, 791218264615713551832), (4124, 4124, 783384420411597576071), (4125, 4125, 775628139021383738684), (4126, 4126, 767948652496419543252), (4127, 4127, 760345200491504498269), (4128, 4128, 752817030189608414128), (4129, 4129, 745363396227335063493), (4130, 4130, 737983560621123825240), (4131, 4131, 730676792694182005189), (4132, 4132, 723442369004140599197), (4133, 4133, 716279573271426335838), (4134, 4134, 709187696308342906771), (4135, 4135, 702166035948854363139), (4136, 4136, 695213896979063725880), (4137, 4137, 688330591068379926614), (4138, 4138, 681515436701366263974), (4139, 4139, 674767759110263627698), (4140, 4140, 668086890208181809601), (4141, 4141, 661472168522952286734), (4142, 4142, 654922939131635927460), (4143, 4143, 648438553595679136099), (4144, 4144, 642018369896712015939), (4145, 4145, 635661752372982193999), (4146, 4146, 629368071656418013861), (4147, 4147, 623136704610314865209), (4148, 4148, 616967034267638480404), (4149, 4149, 610858449769939089509), (4150, 4150, 604810346306870385653), (4151, 4151, 598822125056307312528), (4152, 4152, 592893193125056745077), (4153, 4153, 587022963490155193145), (4154, 4154, 581210854940747715986), (4155, 4155, 575456292020542293055), (4156, 4156, 569758704970833953520), (4157, 4157, 564117529674093023287), (4158, 4158, 558532207598111904244), (4159, 4159, 553002185740704855688), (4160, 4160, 547526916574955302661), (4161, 4161, 542105857995005250159), (4162, 4162, 536738473262381435801), (4163, 4163, 531424230952852906734), (4164, 4164, 526162604903814759143), (4165, 4165, 520953074162192830834), (4166, 4166, 515795122932864188945), (4167, 4167, 510688240527588305886), (4168, 4168, 505631921314443867214), (4169, 4169, 500625664667766205162), (4170, 4170, 495668974918580401151), (4171, 4171, 490761361305525149654), (4172, 4172, 485902337926262524410), (4173, 4173, 481091423689368836050), (4174, 4174, 476328142266701817871), (4175, 4175, 471612022046239423635), (4176, 4176, 466942596085385567955), (4177, 4177, 462319402064738186094), (4178, 4178, 457741982242315035737), (4179, 4179, 453209883408232708650), (4180, 4180, 448722656839834365000), (4181, 4181, 444279858257261747525), (4182, 4182, 439881047779467076757), (4183, 4183, 435525789880660472037), (4184, 4184, 431213653347188586175), (4185, 4185, 426944211234840184332), (4186, 4186, 422717040826574439933), (4187, 4187, 418531723590667762310), (4188, 4188, 414387845139275012188), (4189, 4189, 410284995187401002166), (4190, 4190, 406222767512278219966), (4191, 4191, 402200759913146752442), (4192, 4192, 398218574171432428160), (4193, 4193, 394275816011319235802), (4194, 4194, 390372095060712114656), (4195, 4195, 386507024812586252134), (4196, 4196, 382680222586719061519), (4197, 4197, 378891309491801051009), (4198, 4198, 375139910387921832682), (4199, 4199, 371425653849427557111), (4200, 4200, 367748172128146096150), (4201, 4201, 364107101116976332822), (4202, 4202, 360502080313837953289), (4203, 4203, 356932752785978171573), (4204, 4204, 353398765134631853043), (4205, 4205, 349899767460031537666), (4206, 4206, 346435413326763898679), (4207, 4207, 343005359729469206613), (4208, 4208, 339609267058880402587), (4209, 4209, 336246799068198418403), (4210, 4210, 332917622839800414261), (4211, 4211, 329621408752277637882), (4212, 4212, 326357830447799641467), (4213, 4213, 323126564799801625215), (4214, 4214, 319927291880991708134), (4215, 4215, 316759694931674958548), (4216, 4216, 313623460328391048067), (4217, 4217, 310518277552862423829), (4218, 4218, 307443839161249924583), (4219, 4219, 304399840753712796617), (4220, 4220, 301385980944270095661), (4221, 4221, 298401961330960490753), (4222, 4222, 295447486466297515597), (4223, 4223, 292522263828017342175), (4224, 4224, 289626003790116180372), (4225, 4225, 286758419594174436011), (4226, 4226, 283919227320964788130), (4227, 4227, 281108145862341374386), (4228, 4228, 278324896893407301373), (4229, 4229, 275569204844957724131), (4230, 4230, 272840796876195766467), (4231, 4231, 270139402847718580660), (4232, 4232, 267464755294770871941), (4233, 4233, 264816589400763239545), (4234, 4234, 262194642971052712421), (4235, 4235, 259598656406982883585), (4236, 4236, 257028372680181072857), (4237, 4237, 254483537307109973125), (4238, 4238, 251963898323871260520), (4239, 4239, 249469206261258673782), (4240, 4240, 246999214120058092854), (4241, 4241, 244553677346592171142), (4242, 4242, 242132353808507100141), (4243, 4243, 239735003770799109050), (4244, 4244, 237361389872078325793), (4245, 4245, 235011277101067649300), (4246, 4246, 232684432773334306237), (4247, 4247, 230380626508251788354), (4248, 4248, 228099630206189889459), (4249, 4249, 225841218025930583623), (4250, 4250, 223605166362307508537), (4251, 4251, 221391253824066840136), (4252, 4252, 219199261211947366471), (4253, 4253, 217028971496977590566), (4254, 4254, 214880169798987713431), (4255, 4255, 212752643365334369734), (4256, 4256, 210646181549836009638), (4257, 4257, 208560575791916841225), (4258, 4258, 206495619595957268540), (4259, 4259, 204451108510848780733), (4260, 4260, 202426840109751268052), (4261, 4261, 200422613970050760448), (4262, 4262, 198438231653515604404), (4263, 4263, 196473496686649113271), (4264, 4264, 194528214541236745813), (4265, 4265, 192602192615085886943), (4266, 4266, 190695240212956323706), (4267, 4267, 188807168527679528422), (4268, 4268, 186937790621464879626), (4269, 4269, 185086921407390969927), (4270, 4270, 183254377631080168244), (4271, 4271, 181439977852554622024), (4272, 4272, 179643542428271902994), (4273, 4273, 177864893493338517816), (4274, 4274, 176103854943899522590), (4275, 4275, 174360252419702497614), (4276, 4276, 172633913286834156053), (4277, 4277, 170924666620627877281), (4278, 4278, 169232343188740472555), (4279, 4279, 167556775434396507480), (4280, 4280, 165897797459798522258), (4281, 4281, 164255245009701507186), (4282, 4282, 162628955455150007115), (4283, 4283, 161018767777376244668), (4284, 4284, 159424522551857667988), (4285, 4285, 157846061932532344543), (4286, 4286, 156283229636170638161), (4287, 4287, 154735870926901621942), (4288, 4288, 153203832600892694992), (4289, 4289, 151686962971180886130), (4290, 4290, 150185111852654342703), (4291, 4291, 148698130547182517528), (4292, 4292, 147225871828893581711), (4293, 4293, 145768189929597605655), (4294, 4294, 144324940524354065004), (4295, 4295, 142895980717182242579), (4296, 4296, 141481169026913111464), (4297, 4297, 140080365373181298479), (4298, 4298, 138693431062555741069), (4299, 4299, 137320228774807664424), (4300, 4300, 135960622549314519232), (4301, 4301, 134614477771598533893), (4302, 4302, 133281661159998548409), (4303, 4303, 131962040752473810306), (4304, 4304, 130655485893538426046), (4305, 4305, 129361867221325174302), (4306, 4306, 128081056654777400299), (4307, 4307, 126812927380967723069), (4308, 4308, 125557353842542300068), (4309, 4309, 124314211725289406008), (4310, 4310, 123083377945831095057), (4311, 4311, 121864730639436727780), (4312, 4312, 120658149147957156218), (4313, 4313, 119463514007878372493), (4314, 4314, 118280706938493438111), (4315, 4315, 117109610830191522883), (4316, 4316, 115950109732862893943), (4317, 4317, 114802088844418706875), (4318, 4318, 113665434499424462252), (4319, 4319, 112540034157846002230), (4320, 4320, 111425776393906932901), (4321, 4321, 110322550885056369209), (4322, 4322, 109230248401045910108), (4323, 4323, 108148760793114762483), (4324, 4324, 107077980983281943052), (4325, 4325, 106017802953744498071), (4326, 4326, 104968121736380691160), (4327, 4327, 103928833402357119960), (4328, 4328, 102899835051838732634), (4329, 4329, 101881024803800725380), (4330, 4330, 100872301785941312258), (4331, 4331, 99873566124694368572), (4332, 4332, 98884718935340958982), (4333, 4333, 97905662312218771269), (4334, 4334, 96936299319028486405), (4335, 4335, 95976533979236125154), (4336, 4336, 95026271266570420944), (4337, 4337, 94085417095614278163), (4338, 4338, 93153878312489384320), (4339, 4339, 92231562685633053782), (4340, 4340, 91318378896666389883), (4341, 4341, 90414236531352861270), (4342, 4342, 89519046070646397297), (4343, 4343, 88632718881828116136), (4344, 4344, 87755167209730808055), (4345, 4345, 86886304168050305005), (4346, 4346, 86026043730742876243), (4347, 4347, 85174300723507798260), (4348, 4348, 84330990815354255703), (4349, 7209, 83496030510251738320)]

def glob4 : ℕ := 9127591108378997631599

def runs5 : List (ℕ × ℕ × ℕ) := [(0, 3864, 0), (3865, 3865, 127694167447672482), (3866, 3866, 127811007057548124), (3867, 3867, 127957114945283011), (3868, 3868, 128133529296478472), (3869, 3869, 128341358632742229), (3870, 3870, 128581787409003987), (3871, 3871, 128856082157054034), (3872, 3872, 129165598238096914), (3873, 3873, 129511787275451936), (3874, 3874, 129896205348131215), (3875, 3875, 130320522037097464), (3876, 3876, 130786530428801524), (3877, 3877, 131296158195425619), (3878, 3878, 131851479888473392), (3879, 3879, 132454730602383949), (3880, 3880, 133108321188223149), (3881, 3881, 133814855224846000), (3882, 3882, 134577147986983529), (3883, 3883, 135398247687399688), (3884, 3884, 136281459314698501), (3885, 3885, 137230371440891383), (3886, 3886, 138248886435112635), (3887, 3887, 139341254593924936), (3888, 3888, 140512112786981104), (3889, 3889, 141766528322483000), (3890, 3890, 143110048863718613), (3891, 3891, 144548759380706720), (3892, 3892, 146089347305551983), (3893, 3893, 147739177283919839), (3894, 3894, 149506377187388988), (3895, 3895, 151399937384069518), (3896, 3896, 153429825672646875), (3897, 3897, 155607120786803545), (3898, 3898, 157944167996847962), (3899, 3899, 160454761104131345), (3900, 3900, 163154356080972622), (3901, 3901, 166060322805208601), (3902, 3902, 169192242839803000), (3903, 3903, 172572263099123856), (3904, 3904, 176225517634574677), (3905, 3905, 180180632805870263), (3906, 3906, 184470334965093973), (3907, 3907, 189132184707294063), (3908, 3908, 194209468040081885), (3909, 3909, 199752282884953463), (3910, 3910, 205818869631954569), (3911, 3911, 212477247619427352), (3912, 3912, 219807236089105292), (3913, 3913, 227902959101127926), (3914, 3914, 236875959704506164), (3915, 3915, 246859079528897002), (3916, 3916, 258011294948914629), (3917, 3917, 270523736645661597), (3918, 3918, 284627147287384806), (3919, 3919, 300601034062700556), (3920, 3920, 318784713311391292), (3921, 3921, 339590258082369514), (3922, 3922, 363516934446135871), (3923, 3923, 391165876766291764), (3924, 3924, 423252284587759534), (3925, 3925, 460610147586474370), (3926, 3926, 504181568450139124), (3927, 3927, 554980190959354105), (3928, 3928, 614018634286644986), (3929, 3929, 682197109745132823), (3930, 3930, 760166957210650067), (3931, 3931, 848203842344249646), (3932, 3932, 946136072205853295), (3933, 3933, 1053359225063306172), (3934, 3934, 1168932583208263900), (3935, 3935, 1291719814059471468), (3936, 3936, 1420527687440043326), (3937, 3937, 1554211585509439169), (3938, 3938, 1691738591832053313), (3939, 3939, 1832214327211451782), (3940, 3940, 1974885308048416906), (3941, 3941, 2119127784891346847), (3942, 3942, 2264430841295049796), (3943, 3943, 2410378389192794218), (3944, 3944, 2556632414882636345), (3945, 3945, 2702918428282938084), (3946, 3946, 2849013309125325081), (3947, 3947, 2994735383617271602), (3948, 3948, 3139936427298612152), (3949, 3949, 3284495264650490407), (3950, 3950, 3428312661532107217), (3951, 3951, 3571307250276185353), (3952, 3952, 3713412273585956115), (3953, 3953, 3854572975498875271), (3954, 3954, 3994744503358303555), (3955, 3955, 4133890213800700650), (3956, 3956, 4271980298921821499), (3957, 3957, 4408990666992768364), (3958, 3958, 4544902026308259228), (3959, 3959, 4679699131801923348), (3960, 3960, 4813370162649333472), (3961, 3961, 4945906205753137252), (3962, 3962, 5077300825201099340), (3963, 3963, 5207549701844569520), (3964, 3964, 5336650330321856165), (3965, 3965, 5464601763347842359), (3966, 3966, 5591404395061023672), (3967, 3967, 5717059776779403863), (3968, 3968, 5841570459757563387), (3969, 3969, 5964939860528157942), (3970, 3970, 6087172145205714832), (3971, 3971, 6208272129770381931), (3972, 3972, 6328245193866498347), (3973, 3973, 6447097206070645600), (3974, 3974, 6564834458925885748), (3975, 3975, 6681463612318661209), (3976, 3976, 6796991644004514132), (3977, 3977, 6911425806278034307), (3978, 3978, 7024773587938934302), (3979, 3979, 7137042680835996855), (3980, 3980, 7248240950378740560), (3981, 3981, 7358376409496940989), (3982, 3982, 7467457195603798988), (3983, 3983, 7575491550182133931), (3984, 3984, 7682487800666582347), (3985, 3985, 7788454344340100313), (3986, 3986, 7893399634001489931), (3987, 3987, 7997332165193334778), (3988, 3988, 8100260464807572986), (3989, 3989, 8202193080909732533), (3990, 3990, 8303138573643240903), (3991, 3991, 8403105507092731277), (3992, 3992, 8502102442000341762), (3993, 3993, 8600137929242011490), (3994, 3994, 8697220503982026339), (3995, 3995, 8793358680433816433), (3996, 3996, 8888560947163475316), (3997, 3997, 8982835762879840326), (3998, 3998, 9076191552661400586), (3999, 3999, 9168636704575914636), (4000, 4000, 9260179566653535846), (4001, 4001, 9350828444178555442), (4002, 4002, 9440591597268661355), (4003, 4003, 9529477238713945586), (4004, 4004, 9617493532050832673), (4005, 4005, 9704648589848698291), (4006, 4006, 9790950472189243709), (4007, 4007, 9876407185320726773), (4008, 4008, 9961026680470955697), (4009, 4009, 10044816852804556682), (4010, 4010, 10127785540511454545), (4011, 4011, 10209940524014778437), (4012, 4012, 10291289525287540849), (4013, 4013, 10371840207268453499), (4014, 4014, 10451600173368152391), (4015, 4015, 10530576967057918676), (4016, 4016, 10608778071533712562), (4017, 4017, 10686210909448993919), (4018, 4018, 10762882842710393617), (4019, 4019, 10838801172330831295), (4020, 4020, 10913973138335154613), (4021, 4021, 10988405919713807663), (4022, 4022, 11062106634420427189), (4023, 4023, 11135082339409618899), (4024, 4024, 11207340030711486376), (4025, 4025, 11278886643539775409), (4026, 4026, 11349729052430759968), (4027, 4027, 11419874071410235317), (4028, 4028, 11489328454186201265), (4029, 4029, 11558098894365016571), (4030, 4030, 11626192025688985797), (4031, 4031, 11693614422293504355), (4032, 4032, 11760372598982037518), (4033, 4033, 11826473011517346175), (4034, 4034, 11891922056927497426), (4035, 4035, 11956726073825312650), (4036, 4036, 12020891342740010679), (4037, 4037, 12084424086459899822), (4038, 4038, 12147330470385060696), (4039, 4039, 12209616602889042736), (4040, 4040, 12271288535688671621), (4041, 4041, 12332352264221133139), (4042, 4042, 12392813728027561915), (4043, 4043, 12452678811142421218), (4044, 4044, 12511953342488013387), (4045, 4045, 12570643096273509509), (4046, 4046, 12628753792397932287), (4047, 4047, 12686291096856567816), (4048, 4048, 12743260622150320632), (4049, 4049, 12799667927697562014), (4050, 4050, 12855518520248054562), (4051, 4051, 12910817854298566529), (4052, 4052, 12965571332509817674), (4053, 4053, 13019784306124424533), (4054, 4054, 13073462075385537259), (4055, 4055, 13126609889955882655), (4056, 4056, 13179232949336948869), (4057, 4057, 13231336403288066572), (4058, 4058, 13282925352245159408), (4059, 4059, 13334004847738953204), (4060, 4060, 13384579892812448908), (4061, 4061, 13434655442437478705), (4062, 4062, 13484236403930178125), (4063, 4063, 13533327637365219472), (4064, 4064, 13581933955988663529), (4065, 4065, 13630060126629297308), (4066, 4066, 13677710870108335722), (4067, 4067, 13724890861647374437), (4068, 4068, 13771604731274489952), (4069, 4069, 13817857064228391114), (4070, 4070, 13863652401360533915), (4071, 4071, 13908995239535118536), (4072, 4072, 13953890032026894245), (4073, 4073, 13998341188916703974), (4074, 4074, 14042353077484706191), (4075, 4075, 14085930022601217091), (4076, 4076, 14129076307115121220), (4077, 4077, 14171796172239803340), (4078, 4078, 14214093817936558798), (4079, 4079, 14255973403295443789), (4080, 4080, 14297439046913530750), (4081, 4081, 14338494827270537784), (4082, 4082, 14379144783101804351), (4083, 4083, 14419392913768588659), (4084, 4084, 14459243179625665145), (4085, 4085, 14498699502386203198), (4086, 4086, 14537765765483910886), (4087, 4087, 14576445814432429856), (4088, 4088, 14614743457181969870), (4089, 4089, 14652662464473173557), (4090, 4090, 14690206570188203929), (4091, 4091, 14727379471699049114), (4092, 4092, 14764184830213040458), (4093, 4093, 14800626271115581795), (4094, 4094, 14836707384310089211), (4095, 4095, 14872431724555142045), (4096, 4096, 14907802811798847192), (4097, 4097, 14942824131510420051), (4098, 4098, 14977499135008986575), (4099, 4099, 15011831239789612003), (4100, 4100, 15045823829846562869), (4101, 4101, 15079480255993809788), (4102, 4102, 15112803836182779457), (4103, 4103, 15145797855817365090), (4104, 4104, 15178465568066205286), (4105, 4105, 15210810194172242057), (4106, 4106, 15242834923759569378), (4107, 4107, 15274542915137584261), (4108, 4108, 15305937295602452922), (4109, 4109, 15337021161735905135), (4110, 4110, 15367797579701370373), (4111, 4111, 15398269585537469772), (4112, 4112, 15428440185448878406), (4113, 4113, 15458312356094572708), (4114, 4114, 15487889044873478273), (4115, 4115, 15517173170207533589), (4116, 4116, 15546167621822185524), (4117, 4117, 15574875261024332720), (4118, 4118, 15603298920977733263), (4119, 4119, 15631441406975893222), (4120, 4120, 15659305496712452901), (4121, 4121, 15686893940549087786), (4122, 4122, 15714209461780941371), (4123, 4123, 15741254756899607187), (4124, 4124, 15768032495853677495), (4125, 4125, 15794545322306876213), (4126, 4126, 15820795853893793781), (4127, 4127, 15846786682473241700), (4128, 4128, 15872520374379244634), (4129, 4129, 15897999470669687953), (4130, 4130, 15923226487372638700), (4131, 4131, 15948203915730357973), (4132, 4132, 15972934222441022774), (4133, 4133, 15997419849898175358), (4134, 4134, 16021663216427918166), (4135, 4135, 16045666716523872397), (4136, 4136, 16069432721079918299), (4137, 4137, 16092963577620735202), (4138, 4138, 16116261610530159348), (4139, 4139, 16139329121277377504), (4140, 4140, 16162168388640974324), (4141, 4141, 16184781668930851393), (4142, 4142, 16207171196208035828), (4143, 4143, 16229339182502396274), (4144, 4144, 16251287818028284054), (4145, 4145, 16273019271398117202), (4146, 4146, 16294535689833925015), (4147, 4147, 16315839199376870707), (4148, 4148, 16336931905094769675), (4149, 4149, 16357815891287620793), (4150, 4150, 16378493221691168095), (4151, 4151, 16398965939678510111), (4152, 4152, 16419236068459774030), (4153, 4153, 16439305611279871782), (4154, 4154, 16459176551614355047), (4155, 4155, 16478850853363386083), (4156, 4156, 16498330461043841200), (4157, 4157, 16517617299979563579), (4158, 4158, 16536713276489782049), (4159, 4159, 16555620278075712354), (4160, 4160, 16574340173605357282), (4161, 4161, 16592874813496522001), (4162, 4162, 16611226029898060772), (4163, 4163, 16629395636869371137), (4164, 4164, 16647385430558151582), (4165, 4165, 16665197189376438522), (4166, 4166, 16682832674174938403), (4167, 4167, 16700293628415670547), (4168, 4168, 16717581778342936314), (4169, 4169, 16734698833152629982), (4170, 4170, 16751646485159906684), (4171, 4171, 16768426409965222606), (4172, 4172, 16785040266618762524), (4173, 4173, 16801489697783269685), (4174, 4174, 16817776329895292871), (4175, 4175, 16833901773324865412), (4176, 4176, 16849867622533630787), (4177, 4177, 16865675456231429320), (4178, 4178, 16881326837531360403), (4179, 4179, 16896823314103334517), (4180, 4180, 16912166418326129245), (4181, 4181, 16927357667437963341), (4182, 4182, 16942398563685602799), (4183, 4183, 16957290594472012772), (4184, 4184, 16972035232502569057), (4185, 4185, 16986633935929842756), (4186, 4186, 17001088148496971616), (4187, 4187, 17015399299679631437), (4188, 4188, 17029568804826620804), (4189, 4189, 17043598065299072330), (4190, 4190, 17057488468608303431), (4191, 4191, 17071241388552319596), (4192, 4192, 17084858185350982961), (4193, 4193, 17098340205779858920), (4194, 4194, 17111688783302753363), (4195, 4195, 17124905238202953061), (4196, 4196, 17137990877713181566), (4197, 4197, 17150946996144282919), (4198, 4198, 17163774875012645345), (4199, 4199, 17176475783166376984), (4200, 4200, 17189050976910245640), (4201, 4201, 17201501700129394387), (4202, 4202, 17213829184411844781), (4203, 4203, 17226034649169799341), (4204, 4204, 17238119301759754814), (4205, 4205, 17250084337601437679), (4206, 4206, 17261930940295573224), (4207, 4207, 17273660281740499413), (4208, 4208, 17285273522247636697), (4209, 4209, 17296771810655824784), (4210, 4210, 17308156284444537294), (4211, 4211, 17319428069845985155), (4212, 4212, 17330588281956119440), (4213, 4213, 17341638024844544304), (4214, 4214, 17352578391663350548), (4215, 4215, 17363410464754880249), (4216, 4216, 17374135315758432809), (4217, 4217, 17384754005715922657), (4218, 4218, 17395267585176498786), (4219, 4219, 17405677094300136146), (4220, 4220, 17415983562960208908), (4221, 4221, 17426188010845055432), (4222, 4222, 17436291447558544754), (4223, 4223, 17446294872719654263), (4224, 4224, 17456199276061068193), (4225, 4225, 17466005637526806418), (4226, 4226, 17475714927368892994), (4227, 4227, 17485328106243073782), (4228, 4228, 17494846125303592385), (4229, 4229, 17504269926297033585), (4230, 4230, 17513600441655243334), (4231, 4231, 17522838594587334308), (4232, 4232, 17531985299170785915), (4233, 4233, 17541041460441647592), (4234, 4234, 17550007974483854120), (4235, 4235, 17558885728517661621), (4236, 4236, 17567675600987212808), (4237, 4237, 17576378461647239981), (4238, 4238, 17584995171648914187), (4239, 4239, 17593526583624848867), (4240, 4240, 17601973541773266263), (4241, 4241, 17610336881941334734), (4242, 4242, 17618617431707685108), (4243, 4243, 17626816010464114071), (4244, 4244, 17634933429496482541), (4245, 4245, 17642970492064816904), (4246, 4246, 17650927993482620903), (4247, 4247, 17658806721195405888), (4248, 4248, 17666607454858447089), (4249, 4249, 17674330966413773479), (4250, 4250, 17681978020166398718), (4251, 4251, 17689549372859800620), (4252, 4252, 17697045773750656494), (4253, 4253, 17704467964682841639), (4254, 4254, 17711816680160698225), (4255, 4255, 17719092647421581692), (4256, 4256, 17726296586507691754), (4257, 4257, 17733429210337195014), (4258, 4258, 17740491224774646142), (4259, 4259, 17747483328700714481), (4260, 4260, 17754406214081222892), (4261, 4261, 17761260566035505598), (4262, 4262, 17768047062904091683), (4263, 4263, 17774766376315720881), (4264, 4264, 17781419171253698195), (4265, 4265, 17788006106121593831), (4266, 4266, 17794527832808294891), (4267, 4267, 17800984996752415165), (4268, 4268, 17807378237006069333), (4269, 4269, 17813708186298017825), (4270, 4270, 17819975471096188507), (4271, 4271, 17826180711669581322), (4272, 4272, 17832324522149561938), (4273, 4273, 17838407510590550418), (4274, 4274, 17844430279030110848), (4275, 4275, 17850393423548447800), (4276, 4276, 17856297534327315487), (4277, 4277, 17862143195708345351), (4278, 4278, 17867930986250797824), (4279, 4279, 17873661478788743906), (4280, 4280, 17879335240487682185), (4281, 4281, 17884952832900596831), (4282, 4282, 17890514812023462075), (4283, 4283, 17896021728350198610), (4284, 4284, 17901474126927087312), (4285, 4285, 17906872547406645615), (4286, 4286, 17912217524100971822), (4287, 4287, 17917509586034562598), (4288, 4288, 17922749256996608826), (4289, 4289, 17927937055592774950), (4290, 4290, 17933073495296466906), (4291, 4291, 17938159084499593652), (4292, 4292, 17943194326562827315), (4293, 4293, 17948179719865366849), (4294, 4294, 17953115757854210135), (4295, 4295, 17958002929092939331), (4296, 4296, 17962841717310024282), (4297, 4297, 17967632601446648734), (4298, 4298, 17972376055704064046), (4299, 4299, 17977072549590475062), (4300, 4300, 17981722547967462746), (4301, 4301, 17986326511095948143), (4302, 4302, 17990884894681702198), (4303, 4303, 17995398149920405883), (4304, 4304, 17999866723542265085), (4305, 4305, 18004291057856184639), (4306, 4306, 18008671590793505840), (4307, 4307, 18013008755951311741), (4308, 4308, 18017302982635304510), (4309, 4309, 18021554695902259043), (4310, 4310, 18025764316602057024), (4311, 4311, 18029932261419305568), (4312, 4312, 18034058942914544535), (4313, 4313, 18038144769565046574), (4314, 4314, 18042190145805213923), (4315, 4315, 18046195472066575917), (4316, 4316, 18050161144817391174), (4317, 4317, 18054087556601858322), (4318, 4318, 18057975096078939165), (4319, 4319, 18061824148060798076), (4320, 4320, 18065635093550861425), (4321, 4321, 18069408309781500787), (4322, 4322, 18073144170251343628), (4323, 4323, 18076843044762215161), (4324, 4324, 18080505299455715003), (4325, 4325, 18084131296849432229), (4326, 4326, 18087721395872802408), (4327, 4327, 18091275951902610138), (4328, 4328, 18094795316798140584), (4329, 4329, 18098279838935983487), (4330, 4330, 18101729863244493064), (4331, 4331, 18105145731237907202), (4332, 4332, 18108527781050129310), (4333, 4333, 18111876347468176151), (4334, 4334, 18115191761965294959), (4335, 4335, 18118474352733753096), (4336, 4336, 18121724444717303498), (4337, 4337, 18124942359643329084), (4338, 4338, 18128128416054669329), (4339, 4339, 18131282929341132112), (4340, 4340, 18134406211770693960), (4341, 4341, 18137498572520391762), (4342, 4342, 18140560317706909001), (4343, 4343, 18143591750416859508), (4344, 4344, 18146593170736771750), (4345, 4345, 18149564875782776580), (4346, 4346, 18152507159730001402), (4347, 4347, 18155420313841673627), (4348, 4348, 18158304626497936320), (4349, 7209, 18446744073709426701)]

def glob5 : ℕ := 19928872880962755145

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

def meanN : ℕ := 93650
def meanD : ℕ := 100000
def secN : ℕ := 78112
def secD : ℕ := 10000000
def countN : ℕ := 50864
def countD : ℕ := 10000000
def overN : ℕ := 23188
def overD : ℕ := 10000000
def mgfN : ℕ := 11931
def mgfD : ℕ := 1000
def scarfN : ℕ := 11550
def scarfD : ℕ := 10000000
def longN : ℕ := 1
def longD : ℕ := 100000000000000000000000000000000000000000000000000

theorem env_mean : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowAll Pack0 glob0 r) (glob0 * alphabetSize) (glob0 * pst) feeScale meanN meanD 80 = true := by
  decide +kernel
theorem env_sec : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowAll Pack1 glob1 r) (glob1 * alphabetSize) (glob1 * pst) feeScale secN secD 80 = true := by
  decide +kernel
theorem env_count : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowAll Pack2 glob2 r) (glob2 * alphabetSize) (glob2 * pst) feeScale countN countD 80 = true := by
  decide +kernel
theorem env_over : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowAll Pack3 glob3 r) (glob3 * alphabetSize) (glob3 * pst) feeScale overN overD 80 = true := by
  decide +kernel
theorem env_mgf : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowAll Pack4 glob4 r) (glob4 * alphabetSize) (glob4 * pst) feeScale mgfN mgfD 80 = true := by
  decide +kernel
theorem env_scarf : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowAll Pack5 glob5 r) (glob5 * alphabetSize) (glob5 * pst) feeScale scarfN scarfD 80 = true := by
  decide +kernel
theorem env_long : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowLong r) (feeScale * alphabetSize) (feeScale * pst) feeScale longN longD 80 = true := by
  decide +kernel

/-! ### Parameter values and the route-C totals (generated) -/

theorem rc_c0 : (rcPar.c0 : ℝ) = (11 / 20 : ℝ) := by norm_num [rcPar]
theorem rc_a : (rcPar.a : ℝ) = (51 / 5 : ℝ) := by norm_num [rcPar]
theorem rc_θ : (rcPar.θ : ℝ) = 499217 / 250000 - 1 / 1024 := by norm_num [rcPar]
theorem rc_m : (rcPar.m : ℝ) = (meanN : ℝ) / meanD := by norm_num [rcPar, meanN, meanD]
theorem rc_vv : (rcPar.vv : ℝ) = (secN : ℝ) / secD := by norm_num [rcPar, secN, secD]

/-- `exp (B - a θ_mid) ≤ (2189 / 10000000 : ℝ)` from the Taylor lower bound of `exp (a θ_mid - B)`. -/
theorem rc_exp_mid : Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) ≤ (2189 / 10000000 : ℝ) := by
  have hx : (mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ ≤ -(8427 / 1000 : ℝ) := by norm_num [rcPar, mgfN, mgfD]
  have h0 : (0 : ℝ) ≤ (8427 / 1000 : ℝ) := by norm_num
  have he := Real.sum_le_exp_of_nonneg h0 30
  have hs : (10000000 / 2189 : ℝ) ≤ ∑ i ∈ Finset.range 30, (8427 / 1000 : ℝ) ^ i / (Nat.factorial i) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  refine (Real.exp_le_exp.mpr hx).trans ?_
  rw [Real.exp_neg, show (2189 / 10000000 : ℝ) = ((10000000 / 2189 : ℝ))⁻¹ by norm_num]
  exact inv_anti₀ (by norm_num) (hs.trans he)

/-- Route-C total at the middle threshold: `K0 + K1 + O Λ + tF ≤ (1175 / 1000000 : ℝ)`. -/
theorem rc_total_mid :
    3 / (8 * (rcPar.a : ℝ)) * Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (1175 / 1000000 : ℝ) := by
  have hk : (0 : ℝ) ≤ 3 / (8 * (rcPar.a : ℝ)) := by rw [rc_a]; norm_num
  have h1 := mul_le_mul_of_nonneg_left rc_exp_mid hk
  have h2 : 3 / (8 * (rcPar.a : ℝ)) * (2189 / 10000000 : ℝ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (1175 / 1000000 : ℝ) := by
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
    (2:ENNReal)^128 * ((812*2^62:Nat):ENNReal) *
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

noncomputable def feeCoefficient : ENNReal := 812/2^66

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

 theorem feeCoefficient_real : feeCoefficient.toReal = (812:ℝ)/2^66 := by
  norm_num [feeCoefficient,ENNReal.toReal_div]

 theorem cappedIncrement_nat (n : Nat) :
    cappedIncrement (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (Real.exp (6*min ((812:ℝ)/2^66*(n:ℝ)) (6/5))-1) := by
  rw [cappedIncrement_real _ (by unfold feeCoefficient; finiteness),
    ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast]

 theorem cappedResidual_nat (n : Nat) :
    cappedResidual (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (max 0 ((812:ℝ)/2^66*(n:ℝ)-6/5)) := by
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
    ((812:ℝ)/2^66) (alphabetSize:ℝ) ENNReal.toReal_nonneg hx).1
  rw [cappedIncrement_real _ (priceBucket_ne_top W)]
  calc
    _ ≤ ENNReal.ofReal ((maxFee:ℝ)*((812:ℝ)/2^66)*(alphabetSize:ℝ)/scale) :=
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
`(1 - kappa 2^-31)^(T-80) ≤ 13283369e-8` for the cap-777 `kappa`. -/
 theorem thin_window (T : ℕ) (hT : 2 ^ 32 ≤ T) :
    (1 - kappa * (2^31 : ENNReal)⁻¹) ^ (T - 80) ≤
      ((13283369 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal) := by
  have hq1 := kappa_mul_rate_le_one
  have hfin : (1 - kappa * (2^31 : ENNReal)⁻¹) ^ (T - 80) ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  apply (ENNReal.toReal_le_toReal hfin (by finiteness)).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hq1 ENNReal.one_ne_top, ENNReal.toReal_mul,
    kappa_toReal, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  simp only [ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  set k : ℝ := (ClaudeWCT.Numerics.SharedFtsCount.total : ℝ) / ClaudeWCT.Numerics.SharedFtsCount.count with hk
  have hkv : k = 52416169542617085727767971710947931910569984 / 51927206731424509281114869451843031004872704 := by
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
  have hlow : (100000000 : ℝ) / 13283369 ≤ (2.7182818283 : ℝ) ^ 2 * (a0 - 1) := by
    rw [ha0, hkv]; norm_num
  have hexp : (100000000 : ℝ) / 13283369 ≤ Real.exp (n * (k * (2^31)⁻¹)) :=
    hlow.trans ((ClaudeWCT.Numerics.PoissonReflect.exp_lower a0).trans (Real.exp_le_exp.mpr ha))
  refine hpow.trans ?_
  rw [Real.exp_neg]
  have hpos : (0:ℝ) < 100000000 / 13283369 := by norm_num
  calc (Real.exp (n * (k * (2^31)⁻¹)))⁻¹ ≤ ((100000000 : ℝ) / 13283369)⁻¹ :=
        inv_anti₀ hpos hexp
    _ = ((13283369 : ℕ) : ℝ) / ((100000000 : ℕ) : ℝ) := by norm_num

/-- Thinned Poisson parameter: `2^32 · kappa · 2^-31 = 2 kappa ≤ 2.018833` (cap 777). -/
 theorem thin_lambda :
    ((2^32 : ℕ) : ENNReal) * (kappa * (2^31 : ENNReal)⁻¹) * 1 ≤
      ((2018833 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal) := by
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

 theorem law_nearPrice_mean_bound : Law.lawAvg honestLaw (2^32) nearPrice ≤ (19399/50) := by
  rw [law_nearPrice_coordAverage]
  apply coordAverage_history_bound (2^32) 54 1 (by norm_num) (by norm_num)
    nearBucket (fun _ h => feeCoefficient*(SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit h:ENNReal))
    forestNearMoment (19399/50) (fun L b R => nearBucket_insert L R b)
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
    nearPrice average_nearScore (19399/50)
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
rate `kappa * p` (cap-777 thinning), whose rows are checked by `poissonCheckQ` with `u = 13283369e-8` and
`λ = 2018833e-6`. -/
theorem rc_envelope_thin (rate : ENNReal) (hrate : kappa * rate ≤ 1) (T : ℕ)
    (hlam : (T : ENNReal) * (kappa * rate) * 1 ≤ ((2018833 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal))
    (hu : (1 - kappa * rate) ^ (T - 80) ≤ ((13283369 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal))
    (G : ℕ) (hG0 : 0 < G) (row : ℕ → ℕ) (f : List Alphabet → ENNReal)
    (hmono : ∀ L b R, f (L ++ R) ≤ f (L ++ b :: R))
    (g : (r : ℕ) → ForestHistory (Fin 563) r → ENNReal)
    (hfg : ∀ r ≤ 80, ∀ h : Fin r → Alphabet, f (List.ofFn h) ≤ g r (splitHistory h))
    (hfees : ∀ r ≤ 80, (∑ h, g r h) ≤ feeCoefficient / (feeScale : ENNReal) * (row r : ENNReal))
    (hpoint : ∀ W, f W ≤ (G : ENNReal) * feeCoefficient * alphabetSize / (feeScale : ENNReal))
    (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : N600.poissonCheckQ fieldSize 13283369 100000000 2018833 1000000 (fun r => 16 ^ r * row r)
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
    (hlam : (T : ENNReal) * (kappa * rate) * 1 ≤ ((2018833 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal))
    (hu : (1 - kappa * rate) ^ (T - 80) ≤ ((13283369 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal))
    (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : N600.poissonCheckQ fieldSize 13283369 100000000 2018833 1000000 (fun r => 16 ^ r * rowAll pack G r)
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
    (hlam : (T : ENNReal) * (kappa * rate) * 1 ≤ ((2018833 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal))
    (hu : (1 - kappa * rate) ^ (T - 80) ≤ ((13283369 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal))
    (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : N600.poissonCheckQ fieldSize 13283369 100000000 2018833 1000000 (fun r => 16 ^ r * rowLong r)
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
    ((2018833 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal) := thin_lambda

theorem rc_u_uncond : (1 - kappa * (2 ^ 31 : ENNReal)⁻¹) ^ (2 ^ 32 - 80) ≤
    ((13283369 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal) := thin_window (2 ^ 32) le_rfl

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
      ((2018833 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal) := by
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

/-- Conditional thinned window: `(1 - kappa/(2^31-1))^(2^32 - r - 80) ≤ 13283369e-8` for `r ≤ 80`
(tangent line of `exp` at 2, as `thin_window`). -/
theorem rc_u_cond (r : ℕ) (hr : r ≤ 80) :
    (1 - kappa * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) ^ (2 ^ 32 - r - 80) ≤
      ((13283369 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal) := by
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
  have hkv : k = 52416169542617085727767971710947931910569984 / 51927206731424509281114869451843031004872704 := by
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
  have hlow : (100000000 : ℝ) / 13283369 ≤ (2.7182818283 : ℝ) ^ 2 * (a0 - 1) := by
    rw [ha0, hkv]; norm_num
  have hexp : (100000000 : ℝ) / 13283369 ≤ Real.exp (n * (k * ((2 : ℝ) ^ 31 - 1)⁻¹)) :=
    hlow.trans ((ClaudeWCT.Numerics.PoissonReflect.exp_lower a0).trans (Real.exp_le_exp.mpr ha))
  refine hpow.trans ?_
  rw [Real.exp_neg]
  have hpos : (0 : ℝ) < 100000000 / 13283369 := by norm_num
  calc (Real.exp (n * (k * ((2 : ℝ) ^ 31 - 1)⁻¹)))⁻¹ ≤ ((100000000 : ℝ) / 13283369)⁻¹ :=
        inv_anti₀ hpos hexp
    _ = ((13283369 : ℕ) : ℝ) / ((100000000 : ℕ) : ℝ) := by norm_num

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
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((499217 : ℝ) / 250000 - 1 / 1024)) ≤
      ENNReal.ofReal ((1175 : ℝ) / 1000000) := by
  have hP := parFacts_of_ok rcPar par_ok
  have he : (fun W : List Proposal => price W - ENNReal.ofReal ((499217 : ℝ) / 250000 - 1 / 1024)) =
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
      (fun W => price W-ENNReal.ofReal ((499217:ℝ)/250000-1/1024)) ≤
        ENNReal.ofReal ((1175 : ℝ) / 1000000) := rc_excess_middle

theorem excess_high_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((2:ℝ)-597/250000-1/1024)) ≤
        ENNReal.ofReal ((14788287:ℝ)/12500000000) :=
  (Law.lawAvg_mono _ _ (fun W => tsub_le_tsub_left
    (ENNReal.ofReal_le_ofReal (by norm_num : (499217 : ℝ) / 250000 - 1 / 1024 ≤ 2 - 597 / 250000 - 1 / 1024)) _)).trans
    (rc_excess_middle.trans (ENNReal.ofReal_le_ofReal (by norm_num)))

theorem excess_low_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((1:ℝ)-1/1024)) ≤
        ENNReal.ofReal ((49:ℝ)/100) := rc_excess_low

/-- Large queries: the cap-777 envelope `(993/1000) y` from the high and low endpoints (as in #938). -/
theorem excess_large_certified (y : ℝ)
    (hy0 : 597/500000 ≤ y) (hy1 : y ≤ 1/2) :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal (2-2*y-1/1024)) ≤
        ENNReal.ofReal ((24771/25000)*y) := by
  let t : ℝ := (y-597/500000)/(1/2-597/500000)
  have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hy0) (by norm_num)
  have ht1 : t≤1 := (div_le_one (by norm_num : (0:ℝ)<1/2-597/500000)).2 (by linarith)
  have h := price_excess_affine (2^32) (2-597/250000-1/1024) (1-1/1024)
    (14788287/12500000000) (49/100) t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ht0 ht1 excess_high_certified excess_low_certified
  have harg : (1-t)*(2-597/250000-1/1024)+t*(1-1/1024) = 2-2*y-1/1024 := by
    dsimp [t]; ring
  rw [harg] at h
  have hgap : (24771/25000)*y-((1-t)*(14788287/12500000000)+t*(49/100)) = t*(271/50000) := by
    dsimp [t]; ring
  have hval : (1-t)*(14788287/12500000000)+t*(49/100) ≤ (24771/25000)*y := by nlinarith
  exact h.trans (ENNReal.ofReal_le_ofReal hval)

/-- Tiny queries: affine interpolation between the middle and low endpoints. -/
theorem excess_tiny_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W=>price W-ENNReal.ofReal ((249:ℝ)/125-1/1024)) ≤
        ENNReal.ofReal ((18:ℝ)/5000) := by
  have h := price_excess_affine (2^32) ((499217:ℝ)/250000-1/1024) (1-1/1024)
    (1175/1000000) (49/100) (1217/249217) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) excess_middle_certified excess_low_certified
  have harg : (1-(1217:ℝ)/249217)*((499217:ℝ)/250000-1/1024)+1217/249217*(1-1/1024) = 249/125-1/1024 := by
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
  node := fun _ _ _ _ _ _ _ _=>Signer.lowerNodeHashN_allowed_of_public _ (fun _=>trivial) _ _ _ _ _ _
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


end
