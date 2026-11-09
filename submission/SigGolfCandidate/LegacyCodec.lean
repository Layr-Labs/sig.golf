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
set_option debug.skipKernelTC true
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
theorem selected_top_histogram_card (c : Nat) (hc : 17 ≤ c) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 17 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c).card =
      histogramWeight TopZero.topAcceptedHistogram c := by
  rw [selected_top_path_card 17 c le_rfl hc, TopZero.topAcceptedHistogram, histogramWeight_split,
    if_pos (by omega : 2 ≤ c), topWordCount_eq_hist (c - 2) (by omega), topWordCount_eq_hist c (by omega),
    topHighWeight_eq]
  ring

theorem selected_top_histogram_probability (c : Nat) (hc : 17 ≤ c) :
    Pr[fun answer => ∃ dl, CanonicalPolicy.producerDecodeOut 0 17 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (histogramWeight TopZero.topAcceptedHistogram c : ENNReal) / topDen := by
  classical
  rw [probEvent_uniformSample]
  rw [show (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 17 answer = some dl ∧
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

def rcPar : Par := ⟨934, (11 / 25 : ℚ), (19 / 2 : ℚ), (6350011 / 3200000 : ℚ), (111099 / 100000 : ℚ), (94302 / 10000000 : ℚ), (971093 / 10000000 : ℚ)⟩

def runs0 : List (ℕ × ℕ × ℕ) := [(0, 3840, 18446744073709551616), (3841, 3841, 18398668588458568393), (3842, 3842, 18216503552929275636), (3843, 3843, 18036142131613144194), (3844, 3844, 17857566466943707123), (3845, 3845, 17680758878162086261), (3846, 3846, 17505701859566422040), (3847, 3847, 17332378078778635683), (3848, 3848, 17160770375028352162), (3849, 3849, 16990861757453814022), (3850, 3850, 16822635403419617843), (3851, 3851, 16656074656851106775), (3852, 3852, 16491163026585254233), (3853, 3853, 16327884184737875478), (3854, 3854, 16166221965087005424), (3855, 3855, 16006160361472282598), (3856, 3856, 15847683526210180790), (3857, 3857, 15690775768524931475), (3858, 3858, 15535421552994981659), (3859, 3859, 15381605498014833326), (3860, 3860, 15229312374272112204), (3861, 3861, 15078527103239715053), (3862, 3862, 14929234755682886191), (3863, 3863, 14781420550181075437), (3864, 3864, 14635069851664431125), (3865, 3865, 14490168169964783293), (3866, 3866, 14346701158380973557), (3867, 3867, 14204654612258389660), (3868, 3868, 14064014467582564020), (3869, 3869, 13924766799586697050), (3870, 3870, 13786897821372967376), (3871, 3871, 13650393882547492451), (3872, 3872, 13515241467868804407), (3873, 3873, 13381427195909707334), (3874, 3874, 13248937817732383499), (3875, 3875, 13117760215576617326), (3876, 3876, 12987881401561007253), (3877, 3877, 12859288516397036884), (3878, 3878, 12731968828115878103), (3879, 3879, 12605909730807800102), (3880, 3880, 12481098743374059507), (3881, 3881, 12357523508291148027), (3882, 3882, 12235171790387275274), (3883, 3883, 12114031475630965618), (3884, 3884, 11994090569931649127), (3885, 3885, 11875337197952127848), (3886, 3886, 11757759601932799850), (3887, 3887, 11641346140527524604), (3888, 3888, 11526085287651014459), (3889, 3889, 11411965631337638079), (3890, 3890, 11298975872611522850), (3891, 3891, 11187104824367844406), (3892, 3892, 11076341410265192481), (3893, 3893, 10966674663628903447), (3894, 3894, 10858093726365250937), (3895, 3895, 10750587847886387067), (3896, 3896, 10644146384045927789), (3897, 3897, 10538758796085077019), (3898, 3898, 10434414649589185167), (3899, 3899, 10331103613454638779), (3900, 3900, 10228815458865978989), (3901, 3901, 10127540058283147514), (3902, 3902, 10027267384438759915), (3903, 3903, 9927987509345306847), (3904, 3904, 9829690603312184997), (3905, 3905, 9732366933972460393), (3906, 3906, 9636006865319267715), (3907, 3907, 9540600856751750213), (3908, 3908, 9446139462130445756), (3909, 3909, 9352613328842025501), (3910, 3910, 9260013196873292575), (3911, 3911, 9168329897894349084), (3912, 3912, 9077554354350840677), (3913, 3913, 8987677578565188790), (3914, 3914, 8898690671846721574), (3915, 3915, 8810584823610615420), (3916, 3916, 8723351310505559821), (3917, 3917, 8636981495550059229), (3918, 3918, 8551466827277286365), (3919, 3919, 8466798838888402342), (3920, 3920, 8382969147414259745), (3921, 3921, 8299969452885405688), (3922, 3922, 8217791537510302661), (3923, 3923, 8136427264861685803), (3924, 3924, 8055868579070976043), (3925, 3925, 7976107504030669349), (3926, 3926, 7897136142604623118), (3927, 3927, 7818946675846161503), (3928, 3928, 7741531362223922280), (3929, 3929, 7664882536855368594), (3930, 3930, 7588992610747889697), (3931, 3931, 7513854070047415542), (3932, 3932, 7439459475294470834), (3933, 3933, 7365801460687594885), (3934, 3934, 7292872733354054341), (3935, 3935, 7220666072627776576), (3936, 3936, 7149174329334432253), (3937, 3937, 7078390425083596290), (3938, 3938, 7008307351567917119), (3939, 3939, 6938918169869224870), (3940, 3940, 6870216009771509773), (3941, 3941, 6802194069080702745), (3942, 3942, 6734845612951190837), (3943, 3943, 6668163973219000828), (3944, 3944, 6602142547741584979), (3945, 3945, 6536774799744143543), (3946, 3946, 6472054257172419350), (3947, 3947, 6407974512051900346), (3948, 3948, 6344529219853366680), (3949, 3949, 6281712098864719485), (3950, 3950, 6219516929569029193), (3951, 3951, 6157937554028741775), (3952, 3952, 6096967875275981955), (3953, 3953, 6036601856708893025), (3954, 3954, 5976833521493953490), (3955, 3955, 5917656951974211377), (3956, 3956, 5859066289083377601), (3957, 3957, 5801055731765720397), (3958, 3958, 5743619536401703363), (3959, 3959, 5686752016239310260), (3960, 3960, 5630447540831000258), (3961, 3961, 5574700535476237879), (3962, 3962, 5519505480669542454), (3963, 3963, 5464856911554002430), (3964, 3964, 5410749417380200426), (3965, 3965, 5357177640970495471), (3966, 3966, 5304136278188609377), (3967, 3967, 5251620077414464730), (3968, 3968, 5199623839024222505), (3969, 3969, 5148142414875467827), (3970, 3970, 5097170707797492898), (3971, 3971, 5046703671086626632), (3972, 3972, 4996736308006561021), (3973, 3973, 4947263671293624774), (3974, 3974, 4898280862666955221), (3975, 3975, 4849783032343520021), (3976, 3976, 4801765378557940615), (3977, 3977, 4754223147087069916), (3978, 3978, 4707151630779277144), (3979, 3979, 4660546169088393212), (3980, 3980, 4614402147612270507), (3981, 3981, 4568714997635911393), (3982, 3982, 4523480195679120191), (3983, 3983, 4478693263048633853), (3984, 3984, 4434349765394686983), (3985, 3985, 4390445312271967310), (3986, 3986, 4346975556704918129), (3987, 3987, 4303936194757344682), (3988, 3988, 4261322965106281863), (3989, 3989, 4219131648620081053), (3990, 3990, 4177358067940674310), (3991, 3991, 4135998087069974564), (3992, 3992, 4095047610960370855), (3993, 3993, 4054502585109278075), (3994, 3994, 4014358995157701064), (3995, 3995, 3974612866492773331), (3996, 3996, 3935260263854231021), (3997, 3997, 3896297290944783189), (3998, 3998, 3857720090044339791), (3999, 3999, 3819524841628059199), (4000, 4000, 3781707763988177425), (4001, 4001, 3744265112859581608), (4002, 4002, 3707193181049090701), (4003, 4003, 3670488298068406635), (4004, 4004, 3634146829770699639), (4005, 4005, 3598165177990791722), (4006, 4006, 3562539780188902695), (4007, 4007, 3527267109097923460), (4008, 4008, 3492343672374181644), (4009, 4009, 3457766012251664994), (4010, 4010, 3423530705199668311), (4011, 4011, 3389634361583830010), (4012, 4012, 3356073625330524763), (4013, 4013, 3322845173594578973), (4014, 4014, 3289945716430276211), (4015, 4015, 3257371996465620011), (4016, 4016, 3225120788579821793), (4017, 4017, 3193188899583981973), (4018, 4018, 3161573167904932647), (4019, 4019, 3130270463272210541), (4020, 4020, 3099277686408129249), (4021, 4021, 3068591768720920048), (4022, 4022, 3038209672000910939), (4023, 4023, 3008128388119713801), (4024, 4024, 2978344938732389902), (4025, 4025, 2948856374982564259), (4026, 4026, 2919659777210459663), (4027, 4027, 2890752254663821448), (4028, 4028, 2862130945211704404), (4029, 4029, 2833793015061093470), (4030, 4030, 2805735658476330168), (4031, 4031, 2777956097501316998), (4032, 4032, 2750451581684472275), (4033, 4033, 2723219387806408193), (4034, 4034, 2696256819610305142), (4035, 4035, 2669561207534955586), (4036, 4036, 2643129908450451075), (4037, 4037, 2616960305396486213), (4038, 4038, 2591049807323253676), (4039, 4039, 2565395848834904630), (4040, 4040, 2539995889935549139), (4041, 4041, 2514847415777771424), (4042, 4042, 2489947936413635074), (4043, 4043, 2465294986548153538), (4044, 4044, 2440886125295201523), (4045, 4045, 2416718935935843092), (4046, 4046, 2392791025679052567), (4047, 4047, 2369100025424804521), (4048, 4048, 2345643589529509427), (4049, 4049, 2322419395573771710), (4050, 4050, 2299425144132447238), (4051, 4051, 2276658558546977463), (4052, 4052, 2254117384699977686), (4053, 4053, 2231799390792057115), (4054, 4054, 2209702367120848629), (4055, 4055, 2187824125862226365), (4056, 4056, 2166162500853689470), (4057, 4057, 2144715347379890565), (4058, 4058, 2123480541960287688), (4059, 4059, 2102455982138898701), (4060, 4060, 2081639586276137328), (4061, 4061, 2061029293342710225), (4062, 4062, 2040623062715554679), (4063, 4063, 2020418873975796711), (4064, 4064, 2000414726708709615), (4065, 4065, 1980608640305653084), (4066, 4066, 1960998653767973351), (4067, 4067, 1941582825512844902), (4068, 4068, 1922359233181034556), (4069, 4069, 1903325973446568868), (4070, 4070, 1884481161828286008), (4071, 4071, 1865822932503253473), (4072, 4072, 1847349438122033141), (4073, 4073, 1829058849625775388), (4074, 4074, 1810949356065124146), (4075, 4075, 1793019164420914996), (4076, 4076, 1775266499426648511), (4077, 4077, 1757689603392721298), (4078, 4078, 1740286736032397325), (4079, 4079, 1723056174289502302), (4080, 4080, 1705996212167824061), (4081, 4081, 1689105160562202041), (4082, 4082, 1672381347091289149), (4083, 4083, 1655823115931969455), (4084, 4084, 1639428827655415302), (4085, 4085, 1623196859064767626), (4086, 4086, 1607125603034423392), (4087, 4087, 1591213468350914249), (4088, 4088, 1575458879555360643), (4089, 4089, 1559860276787485785), (4090, 4090, 1544416115631174044), (4091, 4091, 1529124866961558460), (4092, 4092, 1513985016793622237), (4093, 4093, 1498995066132299245), (4094, 4094, 1484153530824058658), (4095, 4095, 1469458941409959068), (4096, 4096, 1454909842980157493), (4097, 4097, 1440504795029858904), (4098, 4098, 1426242371316691984), (4099, 4099, 1412121159719497014), (4100, 4100, 1398139762098511895), (4101, 4101, 1384296794156942470), (4102, 4102, 1370590885303903436), (4103, 4103, 1357020678518716273), (4104, 4104, 1343584830216550765), (4105, 4105, 1330282010115396798), (4106, 4106, 1317110901104353265), (4107, 4107, 1304070199113221054), (4108, 4108, 1291158612983387183), (4109, 4109, 1278374864339987309), (4110, 4110, 1265717687465333970), (4111, 4111, 1253185829173597990), (4112, 4112, 1240778048686730683), (4113, 4113, 1228493117511614538), (4114, 4114, 1216329819318430235), (4115, 4115, 1204286949820227956), (4116, 4116, 1192363316653691045), (4117, 4117, 1180557739261080243), (4118, 4118, 1168869048773346775), (4119, 4119, 1157296087894402748), (4120, 4120, 1145837710786537374), (4121, 4121, 1134492782956967697), (4122, 4122, 1123260181145512571), (4123, 4123, 1112138793213378783), (4124, 4124, 1101127518033048300), (4125, 4125, 1090225265379255743), (4126, 4126, 1079430955821045290), (4127, 4127, 1068743520614896327), (4128, 4128, 1058161901598907254), (4129, 4129, 1047685051088026984), (4130, 4130, 1037311931770323747), (4131, 4131, 1027041516604280938), (4132, 4132, 1016872788717109839), (4133, 4133, 1006804741304069148), (4134, 4134, 996836377528781334), (4135, 4135, 986966710424535975), (4136, 4136, 977194762796570272), (4137, 4137, 967519567125317101), (4138, 4138, 957940165470610991), (4139, 4139, 948455609376842565), (4140, 4140, 939064959779052045), (4141, 4141, 929767286909952520), (4142, 4142, 920561670207873782), (4143, 4143, 911447198225617606), (4144, 4144, 902422968540215451), (4145, 4145, 893488087663579655), (4146, 4146, 884641670954039262), (4147, 4147, 875882842528751745), (4148, 4148, 867210735176981926), (4149, 4149, 858624490274239530), (4150, 4150, 850123257697266862), (4151, 4151, 841706195739868180), (4152, 4152, 833372471029572455), (4153, 4153, 825121258445121243), (4154, 4154, 816951741034773508), (4155, 4155, 808863109935419315), (4156, 4156, 800854564292494371), (4157, 4157, 792925311180687496), (4158, 4158, 785074565525433164), (4159, 4159, 777301550025181351), (4160, 4160, 769605495074436981), (4161, 4161, 761985638687561367), (4162, 4162, 754441226423328087), (4163, 4163, 746971511310225828), (4164, 4164, 739575753772500820), (4165, 4165, 732253221556931505), (4166, 4166, 725003189660328223), (4167, 4167, 717824940257750716), (4168, 4168, 710717762631436352), (4169, 4169, 703680953100432032), (4170, 4170, 696713814950922804), (4171, 4171, 689815658367250301), (4172, 4172, 682985800363614159), (4173, 4173, 676223564716449663), (4174, 4174, 669528281897474913), (4175, 4175, 662899289007400904), (4176, 4176, 656335929710297925), (4177, 4177, 649837554168611807), (4178, 4178, 643403518978823571), (4179, 4179, 637033187107746110), (4180, 4180, 630725927829451594), (4181, 4181, 624481116662823361), (4182, 4182, 618298135309726100), (4183, 4183, 612176371593788218), (4184, 4184, 606115219399790314), (4185, 4185, 600114078613653777), (4186, 4186, 594172355063023541), (4187, 4187, 588289460458439150), (4188, 4188, 582464812335088267), (4189, 4189, 576697833995136898), (4190, 4190, 570987954450630592), (4191, 4191, 565334608366960982), (4192, 4192, 559737236006892062), (4193, 4193, 554195283175140655), (4194, 4194, 548708201163505599), (4195, 4195, 543275446696540197), (4196, 4196, 537896481877762572), (4197, 4197, 532570774136398586), (4198, 4198, 527297796174652065), (4199, 4199, 522077025915497094), (4200, 4200, 516907946450987222), (4201, 4201, 511790045991076457), (4202, 4202, 506722817812946987), (4203, 4203, 501705760210838601), (4204, 4204, 496738376446374853), (4205, 4205, 491820174699381043), (4206, 4206, 486950668019189151), (4207, 4207, 482129374276424902), (4208, 4208, 477355816115272180), (4209, 4209, 472629520906210079), (4210, 4210, 467950020699217900), (4211, 4211, 463316852177443466), (4212, 4212, 458729556611330164), (4213, 4213, 454187679813198182), (4214, 4214, 449690772092275428), (4215, 4215, 445238388210173691), (4216, 4216, 440830087336805635), (4217, 4217, 436465433006738252), (4218, 4218, 432143993075978468), (4219, 4219, 427865339679186602), (4220, 4220, 423629049187313467), (4221, 4221, 419434702165656898), (4222, 4222, 415281883332333562), (4223, 4223, 411170181517161943), (4224, 4224, 407099189620952419), (4225, 4225, 403068504575200415), (4226, 4226, 399077727302178628), (4227, 4227, 395126462675424384), (4228, 4228, 391214319480618202), (4229, 4229, 387340910376849705), (4230, 4230, 383505851858267035), (4231, 4231, 379708764216105975), (4232, 4232, 375949271501095025), (4233, 4233, 372227001486232698), (4234, 4234, 368541585629933364), (4235, 4235, 364892659039537985), (4236, 4236, 361279860435186123), (4237, 4237, 357702832114045667), (4238, 4238, 354161219914896700), (4239, 4239, 350654673183066039), (4240, 4240, 347182844735708950), (4241, 4241, 343745390827434604), (4242, 4242, 340341971116271885), (4243, 4243, 336972248629972163), (4244, 4244, 333635889732645706), (4245, 4245, 330332564091728422), (4246, 4246, 327061944645275665), (4247, 4247, 323823707569579867), (4248, 4248, 320617532247108779), (4249, 4249, 317443101234761167), (4250, 4250, 314300100232436799), (4251, 4251, 311188218051917623), (4252, 4252, 308107146586057053), (4253, 4253, 305056580778274309), (4254, 4254, 302036218592350801), (4255, 4255, 299045760982525546), (4256, 4256, 296084911863886679), (4257, 4257, 293153378083056118), (4258, 4258, 290250869389164473), (4259, 4259, 287377098405113340), (4260, 4260, 284531780599122119), (4261, 4261, 281714634256556553), (4262, 4262, 278925380452036191), (4263, 4263, 276163743021818011), (4264, 4264, 273429448536453476), (4265, 4265, 270722226273716313), (4266, 4266, 268041808191798330), (4267, 4267, 265387928902770624), (4268, 4268, 262760325646307548), (4269, 4269, 260158738263670840), (4270, 4270, 257582909171951327), (4271, 4271, 255032583338565670), (4272, 4272, 252507508256005614), (4273, 4273, 250007433916837241), (4274, 4274, 247532112788947764), (4275, 4275, 245081299791037390), (4276, 4276, 242654752268353851), (4277, 4277, 240252229968667180), (4278, 4278, 237873495018482356), (4279, 4279, 235518311899487481), (4280, 4280, 233186447425235130), (4281, 4281, 230877670718054584), (4282, 4282, 228591753186192658), (4283, 4283, 226328468501180849), (4284, 4284, 224087592575426583), (4285, 4285, 221868903540026320), (4286, 4286, 219672181722798337), (4287, 4287, 217497209626533007), (4288, 4288, 215343771907458422), (4289, 4289, 213211655353919230), (4290, 4290, 211100648865266564), (4291, 4291, 209010543430956994), (4292, 4292, 206941132109858410), (4293, 4293, 204892210009760802), (4294, 4294, 202863574267089903), (4295, 4295, 200855024026821686), (4296, 4296, 198866360422595729), (4297, 4297, 196897386557025474), (4298, 4298, 194947907482203440), (4299, 4299, 193017730180399446), (4300, 4300, 191106663544949946), (4301, 4301, 189214518361336580), (4302, 4302, 187341107288452060), (4303, 4303, 185486244840051544), (4304, 4304, 183649747366387668), (4305, 4305, 181831433036027394), (4306, 4306, 180031121817848905), (4307, 4307, 178248635463216737), (4308, 4308, 176483797488333403), (4309, 4309, 174736433156765746), (4310, 4310, 173006369462144303), (4311, 4311, 171293435111033963), (4312, 4312, 169597460505974221), (4313, 4313, 167918277728687348), (4314, 4314, 166255720523452819), (4315, 4315, 164609624280646356), (4316, 4316, 162979826020441936), (4317, 4317, 161366164376675185), (4318, 4318, 159768479580866519), (4319, 4319, 158186613446402494), (4320, 4320, 156620409352873757), (4321, 4321, 155069712230568076), (4322, 4322, 153534368545116907), (4323, 4323, 152014226282293967), (4324, 4324, 150509134932964324), (4325, 4325, 149018945478182499), (4326, 4326, 147543510374438118), (4327, 4327, 146082683539047642), (4328, 4328, 144636320335690734), (4329, 4329, 143204277560089836), (4330, 4330, 141786413425831521), (4331, 4331, 140382587550328238), (4332, 4332, 138992660940919048), (4333, 4333, 137616495981107968), (4334, 4334, 136253956416938582), (4335, 7209, 134904907343503547)]

def glob0 : ℕ := 18446744073709551616

def runs1 : List (ℕ × ℕ × ℕ) := [(0, 3000, 2149850364267746), (3001, 3001, 2171348867910424), (3002, 3002, 2193062356589528), (3003, 3003, 2214992980155423), (3004, 3004, 2237142909956978), (3005, 3005, 2259514339056547), (3006, 3006, 2282109482447113), (3007, 3007, 2304930577271584), (3008, 3008, 2327979883044300), (3009, 3009, 2351259681874743), (3010, 3010, 2374772278693490), (3011, 3011, 2398520001480425), (3012, 3012, 2422505201495229), (3013, 3013, 2446730253510182), (3014, 3014, 2471197556045283), (3015, 3015, 2495909531605736), (3016, 3016, 2520868626921794), (3017, 3017, 2546077313191012), (3018, 3018, 2571538086322922), (3019, 3019, 2597253467186151), (3020, 3020, 2623226001858012), (3021, 3021, 2649458261876592), (3022, 3022, 2675952844495358), (3023, 3023, 2702712372940312), (3024, 3024, 2729739496669715), (3025, 3025, 2757036891636412), (3026, 3026, 2784607260552776), (3027, 3027, 2812453333158304), (3028, 3028, 2840577866489887), (3029, 3029, 2868983645154786), (3030, 3030, 2897673481606334), (3031, 3031, 2926650216422397), (3032, 3032, 2955916718586621), (3033, 3033, 2985475885772487), (3034, 3034, 3015330644630212), (3035, 3035, 3045483951076514), (3036, 3036, 3075938790587280), (3037, 3037, 3106698178493152), (3038, 3038, 3137765160278084), (3039, 3039, 3169142811880865), (3040, 3040, 3200834239999673), (3041, 3041, 3232842582399670), (3042, 3042, 3265171008223667), (3043, 3043, 3297822718305903), (3044, 3044, 3330800945488962), (3045, 3045, 3364108954943852), (3046, 3046, 3397750044493291), (3047, 3047, 3431727544938223), (3048, 3048, 3466044820387606), (3049, 3049, 3500705268591482), (3050, 3050, 3535712321277397), (3051, 3051, 3571069444490171), (3052, 3052, 3606780138935072), (3053, 3053, 3642847940324423), (3054, 3054, 3679276419727667), (3055, 3055, 3716069183924944), (3056, 3056, 3753229875764193), (3057, 3057, 3790762174521835), (3058, 3058, 3828669796267054), (3059, 3059, 3866956494229724), (3060, 3060, 3905626059172021), (3061, 3061, 3944682319763741), (3062, 3062, 3984129142961379), (3063, 3063, 4023970434390993), (3064, 3064, 4064210138734903), (3065, 3065, 4104852240122252), (3066, 3066, 4145900762523474), (3067, 3067, 4187359770148709), (3068, 3068, 4229233367850196), (3069, 3069, 4271525701528698), (3070, 3070, 4314240958543985), (3071, 3071, 4357383368129425), (3072, 3072, 4400957201810719), (3073, 3073, 4444966773828826), (3074, 3074, 4489416441567114), (3075, 3075, 4534310605982786), (3076, 3076, 4579653712042613), (3077, 3077, 4625450249163040), (3078, 3078, 4671704751654670), (3079, 3079, 4718421799171217), (3080, 3080, 4765606017162929), (3081, 3081, 4813262077334558), (3082, 3082, 4861394698107904), (3083, 3083, 4910008645088983), (3084, 3084, 4959108731539872), (3085, 3085, 5008699818855271), (3086, 3086, 5058786817043824), (3087, 3087, 5109374685214262), (3088, 3088, 5160468432066405), (3089, 3089, 5212073116387069), (3090, 3090, 5264193847550940), (3091, 3091, 5316835786026449), (3092, 3092, 5370004143886713), (3093, 3093, 5423704185325581), (3094, 3094, 5477941227178836), (3095, 3095, 5532720639450625), (3096, 3096, 5588047845845131), (3097, 3097, 5643928324303582), (3098, 3098, 5700367607546618), (3099, 3099, 5757371283622084), (3100, 3100, 5814944996458305), (3101, 3101, 5873094446422888), (3102, 3102, 5931825390887117), (3103, 3103, 5991143644795988), (3104, 3104, 6051055081243948), (3105, 3105, 6111565632056387), (3106, 3106, 6172681288376951), (3107, 3107, 6234408101260721), (3108, 3108, 6296752182273328), (3109, 3109, 6359719704096061), (3110, 3110, 6423316901137022), (3111, 3111, 6487550070148392), (3112, 3112, 6552425570849876), (3113, 3113, 6617949826558375), (3114, 3114, 6684129324823959), (3115, 3115, 6750970618072198), (3116, 3116, 6818480324252920), (3117, 3117, 6886665127495449), (3118, 3118, 6955531778770404), (3119, 3119, 7025087096558108), (3120, 3120, 7095337967523689), (3121, 3121, 7166291347198926), (3122, 3122, 7237954260670915), (3123, 3123, 7310333803277624), (3124, 3124, 7383437141310400), (3125, 3125, 7457271512723504), (3126, 3126, 7531844227850739), (3127, 3127, 7607162670129247), (3128, 3128, 7683234296830539), (3129, 3129, 7760066639798845), (3130, 3130, 7837667306196833), (3131, 3131, 7916043979258801), (3132, 3132, 7995204419051389), (3133, 3133, 8075156463241903), (3134, 3134, 8155908027874322), (3135, 3135, 8237467108153066), (3136, 3136, 8319841779234596), (3137, 3137, 8403040197026942), (3138, 3138, 8487070598997212), (3139, 3139, 8571941304987184), (3140, 3140, 8657660718037056), (3141, 3141, 8744237325217426), (3142, 3142, 8831679698469600), (3143, 3143, 8919996495454296), (3144, 3144, 9009196460408839), (3145, 3145, 9099288425012928), (3146, 3146, 9190281309263057), (3147, 3147, 9282184122355688), (3148, 3148, 9375005963579244), (3149, 3149, 9468756023215037), (3150, 3150, 9563443583447187), (3151, 3151, 9659078019281659), (3152, 3152, 9755668799474476), (3153, 3153, 9853225487469220), (3154, 3154, 9951757742343913), (3155, 3155, 10051275319767352), (3156, 3156, 10151788072965025), (3157, 3157, 10253305953694676), (3158, 3158, 10355839013231622), (3159, 3159, 10459397403363939), (3160, 3160, 10563991377397578), (3161, 3161, 10669631291171554), (3162, 3162, 10776327604083269), (3163, 3163, 10884090880124102), (3164, 3164, 10992931788925343), (3165, 3165, 11102861106814596), (3166, 3166, 11213889717882742), (3167, 3167, 11326028615061570), (3168, 3168, 11439288901212185), (3169, 3169, 11553681790224307), (3170, 3170, 11669218608126550), (3171, 3171, 11785910794207816), (3172, 3172, 11903769902149894), (3173, 3173, 12022807601171393), (3174, 3174, 12143035677183107), (3175, 3175, 12264466033954938), (3176, 3176, 12387110694294487), (3177, 3177, 12510981801237432), (3178, 3178, 12636091619249806), (3179, 3179, 12762452535442305), (3180, 3180, 12890077060796728), (3181, 3181, 13018977831404695), (3182, 3182, 13149167609718742), (3183, 3183, 13280659285815929), (3184, 3184, 13413465878674088), (3185, 3185, 13547600537460829), (3186, 3186, 13683076542835438), (3187, 3187, 13819907308263792), (3188, 3188, 13958106381346430), (3189, 3189, 14097687445159894), (3190, 3190, 14238664319611493), (3191, 3191, 14381050962807608), (3192, 3192, 14524861472435684), (3193, 3193, 14670110087160041), (3194, 3194, 14816811188031641), (3195, 3195, 14964979299911958), (3196, 3196, 15114629092911077), (3197, 3197, 15265775383840188), (3198, 3198, 15418433137678590), (3199, 3199, 15572617469055376), (3200, 3200, 15728343643745930), (3201, 3201, 15885627080183389), (3202, 3202, 16044483350985223), (3203, 3203, 16204928184495075), (3204, 3204, 16366977466340026), (3205, 3205, 16530647241003426), (3206, 3206, 16695953713413460), (3207, 3207, 16862913250547595), (3208, 3208, 17031542383053071), (3209, 3209, 17201857806883602), (3210, 3210, 17373876384952438), (3211, 3211, 17547615148801962), (3212, 3212, 17723091300289982), (3213, 3213, 17900322213292881), (3214, 3214, 18079325435425810), (3215, 3215, 18260118689780068), (3216, 3216, 18442719876677869), (3217, 3217, 18627147075444648), (3218, 3218, 18813418546199094), (3219, 3219, 19001552731661085), (3220, 3220, 19191568258977696), (3221, 3221, 19383483941567473), (3222, 3222, 19577318780983148), (3223, 3223, 19773091968792979), (3224, 3224, 19970822888480909), (3225, 3225, 20170531117365718), (3226, 3226, 20372236428539375), (3227, 3227, 20575958792824769), (3228, 3228, 20781718380753017), (3229, 3229, 20989535564560547), (3230, 3230, 21199430920206152), (3231, 3231, 21411425229408214), (3232, 3232, 21625539481702296), (3233, 3233, 21841794876519319), (3234, 3234, 22060212825284512), (3235, 3235, 22280814953537357), (3236, 3236, 22503623103072731), (3237, 3237, 22728659334103458), (3238, 3238, 22955945927444492), (3239, 3239, 23185505386718937), (3240, 3240, 23417360440586127), (3241, 3241, 23651534044991988), (3242, 3242, 23888049385441908), (3243, 3243, 24126929879296327), (3244, 3244, 24368199178089290), (3245, 3245, 24611881169870183), (3246, 3246, 24857999981568885), (3247, 3247, 25106579981384574), (3248, 3248, 25357645781198420), (3249, 3249, 25611222239010404), (3250, 3250, 25867334461400508), (3251, 3251, 26126007806014513), (3252, 3252, 26387267884074658), (3253, 3253, 26651140562915405), (3254, 3254, 26917651968544559), (3255, 3255, 27186828488230004), (3256, 3256, 27458696773112304), (3257, 3257, 27733283740843427), (3258, 3258, 28010616578251862), (3259, 3259, 28290722744034380), (3260, 3260, 28573629971474724), (3261, 3261, 28859366271189471), (3262, 3262, 29147959933901366), (3263, 3263, 29439439533240380), (3264, 3264, 29733833928572783), (3265, 3265, 30031172267858511), (3266, 3266, 30331483990537096), (3267, 3267, 30634798830442467), (3268, 3268, 30941146818746892), (3269, 3269, 31250558286934361), (3270, 3270, 31563063869803704), (3271, 3271, 31878694508501741), (3272, 3272, 32197481453586759), (3273, 3273, 32519456268122626), (3274, 3274, 32844650830803853), (3275, 3275, 33173097339111891), (3276, 3276, 33504828312503010), (3277, 3277, 33839876595628040), (3278, 3278, 34178275361584321), (3279, 3279, 34520058115200164), (3280, 3280, 34865258696352165), (3281, 3281, 35213911283315687), (3282, 3282, 35566050396148844), (3283, 3283, 35921710900110332), (3284, 3284, 36280928009111436), (3285, 3285, 36643737289202550), (3286, 3286, 37010174662094576), (3287, 3287, 37380276408715521), (3288, 3288, 37754079172802677), (3289, 3289, 38131619964530703), (3290, 3290, 38512936164176010), (3291, 3291, 38898065525817770), (3292, 3292, 39287046181075948), (3293, 3293, 39679916642886708), (3294, 3294, 40076715809315575), (3295, 3295, 40477482967408730), (3296, 3296, 40882257797082818), (3297, 3297, 41291080375053646), (3298, 3298, 41703991178804182), (3299, 3299, 42121031090592224), (3300, 3300, 42542241401498146), (3301, 3301, 42967663815513128), (3302, 3302, 43397340453668259), (3303, 3303, 43831313858204942), (3304, 3304, 44269626996786991), (3305, 3305, 44712323266754861), (3306, 3306, 45159446499422410), (3307, 3307, 45611040964416634), (3308, 3308, 46067151374060800), (3309, 3309, 46527822887801408), (3310, 3310, 46993101116679422), (3311, 3311, 47463032127846216), (3312, 3312, 47937662449124678), (3313, 3313, 48417039073615925), (3314, 3314, 48901209464352085), (3315, 3315, 49390221558995605), (3316, 3316, 49884123774585561), (3317, 3317, 50382965012331417), (3318, 3318, 50886794662454731), (3319, 3319, 51395662609079278), (3320, 3320, 51909619235170071), (3321, 3321, 52428715427521772), (3322, 3322, 52953002581796990), (3323, 3323, 53482532607614960), (3324, 3324, 54017357933691109), (3325, 3325, 54557531513028020), (3326, 3326, 55103106828158300), (3327, 3327, 55654137896439883), (3328, 3328, 56210679275404282), (3329, 3329, 56772786068158325), (3330, 3330, 57340513928839908), (3331, 3331, 57913919068128307), (3332, 3332, 58493058258809590), (3333, 3333, 59077988841397686), (3334, 3334, 59668768729811663), (3335, 3335, 60265456417109780), (3336, 3336, 60868110981280878), (3337, 3337, 61476792091093686), (3338, 3338, 62091560012004623), (3339, 3339, 62712475612124670), (3340, 3340, 63339600368245916), (3341, 3341, 63972996371928375), (3342, 3342, 64612726335647659), (3343, 3343, 65258853599004136), (3344, 3344, 65911442134994177), (3345, 3345, 66570556556344119), (3346, 3346, 67236262121907560), (3347, 3347, 67908624743126636), (3348, 3348, 68587710990557902), (3349, 3349, 69273588100463481), (3350, 3350, 69966323981468116), (3351, 3351, 70665987221282797), (3352, 3352, 71372647093495625), (3353, 3353, 72086373564430581), (3354, 3354, 72807237300074887), (3355, 3355, 73535309673075636), (3356, 3356, 74270662769806392), (3357, 3357, 75013369397504456), (3358, 3358, 75763503091479501), (3359, 3359, 76521138122394296), (3360, 3360, 77286349503618239), (3361, 3361, 78059212998654421), (3362, 3362, 78839805128640965), (3363, 3363, 79628203179927375), (3364, 3364, 80424485211726649), (3365, 3365, 81228730063843915), (3366, 3366, 82041017364482354), (3367, 3367, 82861427538127178), (3368, 3368, 83690041813508449), (3369, 3369, 84526942231643534), (3370, 3370, 85372211653959969), (3371, 3371, 86225933770499569), (3372, 3372, 87088193108204565), (3373, 3373, 87959075039286610), (3374, 3374, 88838665789679476), (3375, 3375, 89727052447576271), (3376, 3376, 90624322972052034), (3377, 3377, 91530566201772554), (3378, 3378, 92445871863790280), (3379, 3379, 93370330582428183), (3380, 3380, 94304033888252464), (3381, 3381, 95247074227134989), (3382, 3382, 96199544969406339), (3383, 3383, 97161540419100402), (3384, 3384, 98133155823291406), (3385, 3385, 99114487381524320), (3386, 3386, 100105632255339564), (3387, 3387, 101106688577892959), (3388, 3388, 102117755463671889), (3389, 3389, 103138933018308608), (3390, 3390, 104170322348491694), (3391, 3391, 105212025571976611), (3392, 3392, 106264145827696377), (3393, 3393, 107326787285973341), (3394, 3394, 108400055158833074), (3395, 3395, 109484055710421405), (3396, 3396, 110578896267525619), (3397, 3397, 111684685230200875), (3398, 3398, 112801532082502884), (3399, 3399, 113929547403327912), (3400, 3400, 115068842877361192), (3401, 3401, 116219531306134803), (3402, 3402, 117381726619196152), (3403, 3403, 118555543885388113), (3404, 3404, 119741099324241994), (3405, 3405, 120938510317484414), (3406, 3406, 122147895420659258), (3407, 3407, 123369374374865851), (3408, 3408, 124603068118614509), (3409, 3409, 125849098799800654), (3410, 3410, 127107589787798661), (3411, 3411, 128378665685676648), (3412, 3412, 129662452342533414), (3413, 3413, 130959076865958748), (3414, 3414, 132268667634618336), (3415, 3415, 133591354310964519), (3416, 3416, 134927267854074164), (3417, 3417, 136276540532614906), (3418, 3418, 137639305937941055), (3419, 3419, 139015698997320465), (3420, 3420, 140405855987293670), (3421, 3421, 141809914547166607), (3422, 3422, 143228013692638273), (3423, 3423, 144660293829564656), (3424, 3424, 146106896767860302), (3425, 3425, 147567965735538905), (3426, 3426, 149043645392894294), (3427, 3427, 150534081846823237), (3428, 3428, 152039422665291469), (3429, 3429, 153559816891944384), (3430, 3430, 155095415060863828), (3431, 3431, 156646369211472466), (3432, 3432, 158212832903587191), (3433, 3433, 159794961232623063), (3434, 3434, 161392910844949293), (3435, 3435, 163006839953398786), (3436, 3436, 164636908352932774), (3437, 3437, 166283277436462102), (3438, 3438, 167946110210826723), (3439, 3439, 169625571312934990), (3440, 3440, 171321827026064340), (3441, 3441, 173035045296324983), (3442, 3442, 174765395749288233), (3443, 3443, 176513049706781116), (3444, 3444, 178278180203848927), (3445, 3445, 180060962005887416), (3446, 3446, 181861571625946290), (3447, 3447, 183680187342205753), (3448, 3448, 185516989215627811), (3449, 3449, 187372159107784089), (3450, 3450, 189245880698861930), (3451, 3451, 191138339505850549), (3452, 3452, 193049722900909054), (3453, 3453, 194980220129918145), (3454, 3454, 196930022331217326), (3455, 3455, 198899322554529500), (3456, 3456, 200888315780074795), (3457, 3457, 202897198937875543), (3458, 3458, 204926170927254298), (3459, 3459, 206975432636526841), (3460, 3460, 209045186962892109), (3461, 3461, 211135638832521030), (3462, 3462, 213246995220846241), (3463, 3463, 215379465173054703), (3464, 3464, 217533259824785250), (3465, 3465, 219708592423033103), (3466, 3466, 221905678347263434), (3467, 3467, 224124735130736068), (3468, 3468, 226365982482043429), (3469, 3469, 228629642306863863), (3470, 3470, 230915938729932502), (3471, 3471, 233225098117231827), (3472, 3472, 235557349098404145), (3473, 3473, 237912922589388186), (3474, 3474, 240292051815282068), (3475, 3475, 242694972333434889), (3476, 3476, 245121922056769238), (3477, 3477, 247573141277336930), (3478, 3478, 250048872690110299), (3479, 3479, 252549361417011402), (3480, 3480, 255074855031181516), (3481, 3481, 257625603581493332), (3482, 3482, 260201859617308265), (3483, 3483, 262803878213481348), (3484, 3484, 265431916995616161), (3485, 3485, 268086236165572323), (3486, 3486, 270767098527228046), (3487, 3487, 273474769512500326), (3488, 3488, 276209517207625330), (3489, 3489, 278971612379701583), (3490, 3490, 281761328503498599), (3491, 3491, 284578941788533585), (3492, 3492, 287424731206418920), (3493, 3493, 290298978518483110), (3494, 3494, 293201968303667941), (3495, 3495, 296133987986704620), (3496, 3496, 299095327866571666), (3497, 3497, 302086281145237383), (3498, 3498, 305107143956689757), (3499, 3499, 308158215396256654), (3500, 3500, 311239797550219221), (3501, 3501, 314352195525721413), (3502, 3502, 317495717480978627), (3503, 3503, 320670674655788414), (3504, 3504, 323877381402346298), (3505, 3505, 327116155216369761), (3506, 3506, 330387316768533458), (3507, 3507, 333691189936218793), (3508, 3508, 337028101835580981), (3509, 3509, 340398382853936791), (3510, 3510, 343802366682476158), (3511, 3511, 347240390349300920), (3512, 3512, 350712794252793929), (3513, 3513, 354219922195321868), (3514, 3514, 357762121417275087), (3515, 3515, 361339742631447838), (3516, 3516, 364953140057762316), (3517, 3517, 368602671458339940), (3518, 3518, 372288698172923339), (3519, 3519, 376011585154652572), (3520, 3520, 379771701006199098), (3521, 3521, 383569418016261089), (3522, 3522, 387405112196423700), (3523, 3523, 391279163318387937), (3524, 3524, 395191954951571816), (3525, 3525, 399143874501087534), (3526, 3526, 403135313246098410), (3527, 3527, 407166666378559394), (3528, 3528, 411238333042344988), (3529, 3529, 415350716372768438), (3530, 3530, 419504223536496122), (3531, 3531, 423699265771861083), (3532, 3532, 427936258429579694), (3533, 3533, 432215621013875491), (3534, 3534, 436537777224014246), (3535, 3535, 440903154996254388), (3536, 3536, 445312186546216932), (3537, 3537, 449765308411679102), (3538, 3538, 454262961495795893), (3539, 3539, 458805591110753852), (3540, 3540, 463393647021861390), (3541, 3541, 468027583492080004), (3542, 3542, 472707859327000804), (3543, 3543, 477434937920270812), (3544, 3544, 482209287299473520), (3545, 3545, 487031380172468255), (3546, 3546, 491901693974192938), (3547, 3547, 496820710913934867), (3548, 3548, 501788918023074216), (3549, 3549, 506806807203304958), (3550, 3550, 511874875275338008), (3551, 3551, 516993624028091388), (3552, 3552, 522163560268372302), (3553, 3553, 527385195871056025), (3554, 3554, 532659047829766585), (3555, 3555, 537985638308064251), (3556, 3556, 543365494691144893), (3557, 3557, 548799149638056342), (3558, 3558, 554287141134436906), (3559, 3559, 559830012545781275), (3560, 3560, 565428312671239087), (3561, 3561, 571082595797951478), (3562, 3562, 576793421755930993), (3563, 3563, 582561355973490303), (3564, 3564, 588386969533225206), (3565, 3565, 594270839228557458), (3566, 3566, 600213547620843033), (3567, 3567, 606215683097051463), (3568, 3568, 612277839928021977), (3569, 3569, 618400618327302197), (3570, 3570, 624584624510575219), (3571, 3571, 630830470755680971), (3572, 3572, 637138775463237781), (3573, 3573, 643510163217870159), (3574, 3574, 649945264850048860), (3575, 3575, 656444717498549349), (3576, 3576, 663009164673534843), (3577, 3577, 669639256320270191), (3578, 3578, 676335648883472893), (3579, 3579, 683099005372307622), (3580, 3580, 689929995426030698), (3581, 3581, 696829295380291005), (3582, 3582, 703797588334093915), (3583, 3583, 710835564217434854), (3584, 3584, 717943919859609203), (3585, 3585, 725123359058205295), (3586, 3586, 732374592648787348), (3587, 3587, 739698338575275221), (3588, 3588, 747095321961027973), (3589, 3589, 754566275180638253), (3590, 3590, 762111937932444636), (3591, 3591, 769733057311769082), (3592, 3592, 777430387884886773), (3593, 3593, 785204691763735641), (3594, 3594, 793056738681372997), (3595, 3595, 800987306068186727), (3596, 3596, 808997179128868594), (3597, 3597, 817087150920157280), (3598, 3598, 825258022429358853), (3599, 3599, 833510602653652441), (3600, 3600, 841845708680188966), (3601, 3601, 850264165766990855), (3602, 3602, 858766807424660764), (3603, 3603, 867354475498907372), (3604, 3604, 876028020253896445), (3605, 3605, 884788300456435410), (3606, 3606, 893636183460999764), (3607, 3607, 902572545295609762), (3608, 3608, 911598270748565859), (3609, 3609, 920714253456051518), (3610, 3610, 929921395990612033), (3611, 3611, 939220609950518153), (3612, 3612, 948612816050023335), (3613, 3613, 958098944210523568), (3614, 3614, 967679933652628804), (3615, 3615, 977356732989155092), (3616, 3616, 987130300319046643), (3617, 3617, 997001603322237109), (3618, 3618, 1006971619355459480), (3619, 3619, 1017041335549014075), (3620, 3620, 1027211748904504216), (3621, 3621, 1037483866393549258), (3622, 3622, 1047858705057484751), (3623, 3623, 1058337292108059598), (3624, 3624, 1068920665029140194), (3625, 3625, 1079609871679431596), (3626, 3626, 1090405970396225912), (3627, 3627, 1101310030100188171), (3628, 3628, 1112323130401190053), (3629, 3629, 1123446361705201953), (3630, 3630, 1134680825322253973), (3631, 3631, 1146027633575476512), (3632, 3632, 1157487909911231278), (3633, 3633, 1169062789010343590), (3634, 3634, 1180753416900447026), (3635, 3635, 1192560951069451497), (3636, 3636, 1204486560580146011), (3637, 3637, 1216531426185947472), (3638, 3638, 1228696740447806946), (3639, 3639, 1240983707852285016), (3640, 3640, 1253393544930807866), (3641, 3641, 1265927480380115945), (3642, 3642, 1278586755183917104), (3643, 3643, 1291372622735756275), (3644, 3644, 1304286348963113838), (3645, 3645, 1317329212452744976), (3646, 3646, 1330502504577272426), (3647, 3647, 1343807529623045150), (3648, 3648, 1357245604919275602), (3649, 3649, 1370818060968468358), (3650, 3650, 1384526241578153041), (3651, 3651, 1398371503993934572), (3652, 3652, 1412355219033873917), (3653, 3653, 1426478771224212657), (3654, 3654, 1440743558936454783), (3655, 3655, 1455150994525819331), (3656, 3656, 1469702504471077524), (3657, 3657, 1484399529515788299), (3658, 3658, 1499243524810946182), (3659, 3659, 1514235960059055644), (3660, 3660, 1529378319659646201), (3661, 3661, 1544672102856242663), (3662, 3662, 1560118823884805089), (3663, 3663, 1575720012123653140), (3664, 3664, 1591477212244889672), (3665, 3665, 1607391984367338568), (3666, 3666, 1623465904211011954), (3667, 3667, 1639700563253122074), (3668, 3668, 1656097568885653294), (3669, 3669, 1672658544574509827), (3670, 3670, 1689385130020254925), (3671, 3671, 1706278981320457475), (3672, 3672, 1723341771133662049), (3673, 3673, 1740575188844998670), (3674, 3674, 1757980940733448657), (3675, 3675, 1775560750140783143), (3676, 3676, 1793316357642190975), (3677, 3677, 1811249521218612884), (3678, 3678, 1829362016430799013), (3679, 3679, 1847655636595107003), (3680, 3680, 1866132192961058073), (3681, 3681, 1884793514890668654), (3682, 3682, 1903641450039575341), (3683, 3683, 1922677864539971094), (3684, 3684, 1941904643185370805), (3685, 3685, 1961323689617224513), (3686, 3686, 1980936926513396758), (3687, 3687, 2000746295778530726), (3688, 3688, 2020753758736316033), (3689, 3689, 2040961296323679193), (3690, 3690, 2061370909286915985), (3691, 3691, 2081984618379785145), (3692, 3692, 2102804464563582997), (3693, 3693, 2123832509209218826), (3694, 3694, 2145070834301311015), (3695, 3695, 2166521542644324125), (3696, 3696, 2188186758070767366), (3697, 3697, 2210068625651475040), (3698, 3698, 2232169311907989790), (3699, 3699, 2254491005027069688), (3700, 3700, 2277035915077340385), (3701, 3701, 2299806274228113789), (3702, 3702, 2322804336970394927), (3703, 3703, 2346032380340098876), (3704, 3704, 2369492704143499865), (3705, 3705, 2393187631184934863), (3706, 3706, 2417119507496784212), (3707, 3707, 2441290702571752054), (3708, 3708, 2465703609597469575), (3709, 3709, 2490360645693444270), (3710, 3710, 2515264252150378713), (3711, 3711, 2540416894671882500), (3712, 3712, 2565821063618601325), (3713, 3713, 2591479274254787338), (3714, 3714, 2617394066997335212), (3715, 3715, 2643568007667308564), (3716, 3716, 2670003687743981650), (3717, 3717, 2696703724621421466), (3718, 3718, 2723670761867635681), (3719, 3719, 2750907469486312038), (3720, 3720, 2778416544181175158), (3721, 3721, 2806200709622986909), (3722, 3722, 2834262716719216779), (3723, 3723, 2862605343886408946), (3724, 3724, 2891231397325273036), (3725, 3725, 2920143711298525766), (3726, 3726, 2949345148411511024), (3727, 3727, 2978838599895626134), (3728, 3728, 3008626985894582395), (3729, 3729, 3038713255753528219), (3730, 3730, 3069100388311063501), (3731, 3731, 3099791392194174136), (3732, 3732, 3130789306116115878), (3733, 3733, 3162097199177277037), (3734, 3734, 3193718171169049807), (3735, 3735, 3225655352880740305), (3736, 3736, 3257911906409547708), (3737, 3737, 3290491025473643185), (3738, 3738, 3323395935728379617), (3739, 3739, 3356629895085663413), (3740, 3740, 3390196194036520047), (3741, 3741, 3424098155976885248), (3742, 3742, 3458339137536654100), (3743, 3743, 3492922528912020641), (3744, 3744, 3527851754201140848), (3745, 3745, 3563130271743152256), (3746, 3746, 3598761574460583779), (3747, 3747, 3634749190205189616), (3748, 3748, 3671096682107241513), (3749, 3749, 3707807648928313928), (3750, 3750, 3744885725417597067), (3751, 3751, 3782334582671773038), (3752, 3752, 3820157928498490768), (3753, 3753, 3858359507783475676), (3754, 3754, 3896943102861310432), (3755, 3755, 3935912533889923537), (3756, 3756, 3975271659228822772), (3757, 3757, 4015024375821111000), (3758, 3758, 4055174619579322110), (3759, 3759, 4095726365775115331), (3760, 3760, 4136683629432866484), (3761, 3761, 4178050465727195149), (3762, 3762, 4219830970384467101), (3763, 3763, 4262029280088311772), (3764, 3764, 4304649572889194889), (3765, 3765, 4347696068618086838), (3766, 3766, 4391173029304267707), (3767, 3767, 4435084759597310384), (3768, 3768, 4479435607193283487), (3769, 3769, 4524229963265216322), (3770, 3770, 4569472262897868486), (3771, 3771, 4615166985526847170), (3772, 3772, 4661318655382115642), (3773, 3773, 4707931841935936799), (3774, 3774, 4755011160355296167), (3775, 3775, 4802561271958849128), (3776, 3776, 4850586884678437619), (3777, 3777, 4899092753525221996), (3778, 3778, 4948083681060474216), (3779, 3779, 4997564517871078958), (3780, 3780, 5047540163049789747), (3781, 3781, 5098015564680287645), (3782, 3782, 5148995720327090521), (3783, 3783, 5200485677530361426), (3784, 3784, 5252490534305665041), (3785, 3785, 5305015439648721691), (3786, 3786, 5358065594045208908), (3787, 3787, 5411646249985660997), (3788, 3788, 5465762712485517607), (3789, 3789, 5520420339610372783), (3790, 3790, 5575624543006476511), (3791, 3791, 5631380788436541276), (3792, 3792, 5687694596320906689), (3793, 3793, 5744571542284115756), (3794, 3794, 5802017257706956913), (3795, 3795, 5860037430284026482), (3796, 3796, 5918637804586866747), (3797, 3797, 5977824182632735415), (3798, 3798, 6037602424459062769), (3799, 3799, 6097978448703653396), (3800, 3800, 6158958233190689930), (3801, 3801, 6220547815522596830), (3802, 3802, 6282753293677822798), (3803, 3803, 6345580826614601026), (3804, 3804, 6409036634880747036), (3805, 3805, 6473127001229554507), (3806, 3806, 6537858271241850052), (3807, 3807, 6603236853954268552), (3808, 3808, 6669269222493811238), (3809, 3809, 6735961914718749350), (3810, 3810, 6803321533865936844), (3811, 3811, 6871354749204596212), (3812, 3812, 6940068296696642174), (3813, 3813, 7009468979663608596), (3814, 3814, 7079563669460244682), (3815, 3815, 7150359306154847129), (3816, 3816, 7221862899216395600), (3817, 3817, 7294081528208559556), (3818, 3818, 7367022343490645151), (3819, 3819, 7440692566925551603), (3820, 3820, 7515099492594807119), (3821, 3821, 7590250487520755190), (3822, 3822, 7666152992395962742), (3823, 3823, 7742814522319922369), (3824, 3824, 7820242667543121593), (3825, 3825, 7898445094218552809), (3826, 3826, 7977429545160738337), (3827, 3827, 8057203840612345721), (3828, 3840, 8116567392432202712), (3841, 3841, 8095414178921770093), (3842, 3842, 8015261563288881280), (3843, 3843, 7935902537909783446), (3844, 3844, 7857329245455231134), (3845, 3845, 7779533906391317955), (3846, 3846, 7702508818209225698), (3847, 3847, 7626246354662599701), (3848, 3848, 7550738965012474951), (3849, 3849, 7475979173279678170), (3850, 3850, 7401959577504631851), (3851, 3851, 7328672849014486981), (3852, 3852, 7256111731697511863), (3853, 3853, 7184269041284665211), (3854, 3854, 7113137664638282387), (3855, 3855, 7042710559047804343), (3856, 3856, 6972980751532479548), (3857, 3857, 6903941338150969849), (3858, 3858, 6835585483317791930), (3859, 3859, 6767906419126526664), (3860, 3860, 6700897444679729370), (3861, 3861, 6634551925425474624), (3862, 3862, 6568863292500469924), (3863, 3863, 6503825042079673192), (3864, 3864, 6439430734732349695), (3865, 3865, 6375673994784504649), (3866, 3866, 6312548509687628365), (3867, 3867, 6250048029393691451), (3868, 3868, 6188166365736328169), (3869, 3869, 6126897391818146702), (3870, 3870, 6066235041404105646), (3871, 3871, 6006173308320896679), (3872, 3872, 5946706245862273940), (3873, 3873, 5887827966200271227), (3874, 3874, 5829532639802248740), (3875, 3875, 5771814494853711624), (3876, 3876, 5714667816686843192), (3877, 3877, 5658086947214696229), (3878, 3878, 5602066284370986366), (3879, 3879, 5546600281555432045), (3880, 3880, 5491683447084586184), (3881, 3881, 5437310343648105132), (3882, 3882, 5383475587770401121), (3883, 3883, 5330173849277624872), (3884, 3884, 5277399850769925616), (3885, 3885, 5225148367098936254), (3886, 3886, 5173414224850431934), (3887, 3887, 5122192301832110826), (3888, 3888, 5071477526566446362), (3889, 3889, 5021264877788560755), (3890, 3890, 4971549383949070054), (3891, 3891, 4922326122721851539), (3892, 3892, 4873590220516684692), (3893, 3893, 4825336851996717517), (3894, 3894, 4777561239600710413), (3895, 3895, 4730258653070010310), (3896, 3896, 4683424408980208227), (3897, 3897, 4637053870277433888), (3898, 3898, 4591142445819241474), (3899, 3899, 4545685589920041063), (3900, 3900, 4500678801901030756), (3901, 3901, 4456117625644584906), (3902, 3902, 4411997649153054363), (3903, 3903, 4368314504111935013), (3904, 3904, 4325063865457361399), (3905, 3905, 4282241450947882573), (3906, 3906, 4239843020740477795), (3907, 3907, 4197864376970770094), (3908, 3908, 4156301363337396133), (3909, 3909, 4115149864690491221), (3910, 3910, 4074405806624248733), (3911, 3911, 4034065155073513597), (3912, 3912, 3994123915914369898), (3913, 3913, 3954578134568683068), (3914, 3914, 3915423895612557493), (3915, 3915, 3876657322388670785), (3916, 3916, 3838274576622446322), (3917, 3917, 3800271858042026061), (3918, 3918, 3762645404002006001), (3919, 3919, 3725391489110897031), (3920, 3920, 3688506424862274288), (3921, 3921, 3651986559269578503), (3922, 3922, 3615828276504533171), (3923, 3923, 3580027996539141754), (3924, 3924, 3544582174791229459), (3925, 3925, 3509487301773494514), (3926, 3926, 3474739902746034172), (3927, 3927, 3440336537372311062), (3928, 3928, 3406273799378525804), (3929, 3929, 3372548316216362182), (3930, 3930, 3339156748729071467), (3931, 3931, 3306095790820862839), (3932, 3932, 3273362169129567167), (3933, 3933, 3240952642702541750), (3934, 3934, 3208864002675783910), (3935, 3935, 3177093071956221694), (3936, 3936, 3145636704907150192), (3937, 3937, 3114491787036782368), (3938, 3938, 3083655234689883533), (3939, 3939, 3053123994742458943), (3940, 3940, 3022895044299464300), (3941, 3941, 2992965390395509208), (3942, 3942, 2963332069698523968), (3943, 3943, 2933992148216360365), (3944, 3944, 2904942721006297391), (3945, 3945, 2876180911887423159), (3946, 3946, 2847703873155864514), (3947, 3947, 2819508785302836153), (3948, 3948, 2791592856735481339), (3949, 3949, 2763953323500476574), (3950, 3950, 2736587449010372845), (3951, 3951, 2709492523772646381), (3952, 3952, 2682665865121432061), (3953, 3953, 2656104816951912931), (3954, 3954, 2629806749457339536), (3955, 3955, 2603769058868653006), (3956, 3956, 2577989167196686145), (3957, 3957, 2552464521976916975), (3958, 3958, 2527192596016749480), (3959, 3959, 2502170887145296515), (3960, 3960, 2477396917965640114), (3961, 3961, 2452868235609544667), (3962, 3962, 2428582411494598680), (3963, 3963, 2404537041083761070), (3964, 3964, 2380729743647288188), (3965, 3965, 2357158162027018008), (3966, 3966, 2333819962402988126), (3967, 3967, 2310712834062364482), (3968, 3968, 2287834489170657903), (3969, 3969, 2265182662545205844), (3970, 3970, 2242755111430896875), (3971, 3971, 2220549615278115718), (3972, 3972, 2198563975522886850), (3973, 3973, 2176796015369194901), (3974, 3974, 2155243579573460298), (3975, 3975, 2133904534231148810), (3976, 3976, 2112776766565493871), (3977, 3977, 2091858184718310763), (3978, 3978, 2071146717542881944), (3979, 3979, 2050640314398893014), (3980, 3980, 2030336944949399023), (3981, 3981, 2010234598959801013), (3982, 3982, 1990331286098812885), (3983, 3983, 1970625035741398896), (3984, 3984, 1951113896773662273), (3985, 3985, 1931795937399665617), (3986, 3986, 1912669244950163977), (3987, 3987, 1893731925693231660), (3988, 3988, 1874982104646764020), (3989, 3989, 1856417925392835663), (3990, 3990, 1838037549893896697), (3991, 3991, 1819839158310788808), (3992, 3992, 1801820948822563177), (3993, 3993, 1783981137448082353), (3994, 3994, 1766317957869388468), (3995, 3995, 1748829661256820266), (3996, 3996, 1731514516095861649), (3997, 3997, 1714370808015704603), (3998, 3998, 1697396839619509508), (3999, 3999, 1680590930316346048), (4000, 4000, 1663951416154798067), (4001, 4001, 1647476649658215908), (4002, 4002, 1631164999661599909), (4003, 4003, 1615014851150098920), (4004, 4004, 1599024605099107841), (4005, 4005, 1583192678315948358), (4006, 4006, 1567517503283117186), (4007, 4007, 1551997528003086323), (4008, 4008, 1536631215844639923), (4009, 4009, 1521417045390732597), (4010, 4010, 1506353510287854057), (4011, 4011, 1491439119096885205), (4012, 4012, 1476672395145430896), (4013, 4013, 1462051876381614748), (4014, 4014, 1447576115229321533), (4015, 4015, 1433243678444872805), (4016, 4016, 1419053146975121589), (4017, 4017, 1405003115816952069), (4018, 4018, 1391092193878170365), (4019, 4019, 1377319003839772638), (4020, 4020, 1363682182019576870), (4021, 4021, 1350180378237204822), (4022, 4022, 1336812255680400813), (4023, 4023, 1323576490772674073), (4024, 4024, 1310471773042251557), (4025, 4025, 1297496804992328274), (4026, 4026, 1284650301972602252), (4027, 4027, 1271930992052081438), (4028, 4028, 1259337615893149938), (4029, 4029, 1246868926626881127), (4030, 4030, 1234523689729585274), (4031, 4031, 1222300682900579479), (4032, 4032, 1210198695941167801), (4033, 4033, 1198216530634819605), (4034, 4034, 1186353000628534263), (4035, 4035, 1174606931315380458), (4036, 4036, 1162977159718198473), (4037, 4037, 1151462534374453934), (4038, 4038, 1140061915222231618), (4039, 4039, 1128774173487358038), (4040, 4040, 1117598191571641621), (4041, 4041, 1106532862942219427), (4042, 4042, 1095577092021999433), (4043, 4043, 1084729794081187557), (4044, 4044, 1073989895129888670), (4045, 4045, 1063356331811770961), (4046, 4046, 1052828051298783130), (4047, 4047, 1042404011186913990), (4048, 4048, 1032083179392984148), (4049, 4049, 1021864534052459553), (4050, 4050, 1011747063418276785), (4051, 4051, 1001729765760670084), (4052, 4052, 991811649267990182), (4053, 4053, 981991731948505131), (4054, 4054, 972269041533173397), (4055, 4055, 962642615379379601), (4056, 4056, 953111500375623367), (4057, 4057, 943674752847151849), (4058, 4058, 934331438462526583), (4059, 4059, 925080632141115429), (4060, 4060, 915921417961500424), (4061, 4061, 906852889070792499), (4062, 4062, 897874147594844059), (4063, 4063, 888984304549350553), (4064, 4064, 880182479751832231), (4065, 4065, 871467801734487357), (4066, 4066, 862839407657908275), (4067, 4067, 854296443225651757), (4068, 4068, 845838062599655205), (4069, 4069, 837463428316490302), (4070, 4070, 829171711204445844), (4071, 4071, 820962090301431528), (4072, 4072, 812833752773694583), (4073, 4073, 804785893835341171), (4074, 4074, 796817716668654625), (4075, 4075, 788928432345202599), (4076, 4076, 781117259747725345), (4077, 4077, 773383425492797371), (4078, 4078, 765726163854254823), (4079, 4079, 758144716687381013), (4080, 4080, 750638333353842587), (4081, 4081, 743206270647368898), (4082, 4082, 735847792720167226), (4083, 4083, 728562171010066560), (4084, 4084, 721348684168382733), (4085, 4085, 714206617988497756), (4086, 4086, 707135265335146293), (4087, 4087, 700133926074402270), (4088, 4088, 693201907004358683), (4089, 4089, 686338521786493746), (4090, 4090, 679543090877716580), (4091, 4091, 672814941463085723), (4092, 4092, 666153407389193785), (4093, 4093, 659557829098211668), (4094, 4094, 653027553562585810), (4095, 4095, 646561934220381990), (4096, 4096, 640160330911269297), (4097, 4097, 633822109813137918), (4098, 4098, 627546643379344473), (4099, 4099, 621333310276578686), (4100, 4100, 615181495323345234), (4101, 4101, 609090589429054687), (4102, 4102, 603059989533717512), (4103, 4103, 597089098548235160), (4104, 4104, 591177325295282337), (4105, 4105, 585324084450774591), (4106, 4106, 579528796485915437), (4107, 4107, 573790887609817264), (4108, 4108, 568109789712690361), (4109, 4109, 562484940309594416), (4110, 4110, 556915782484746947), (4111, 4111, 551401764836383116), (4112, 4112, 545942341422161501), (4113, 4113, 540536971705110397), (4114, 4114, 535185120500109304), (4115, 4115, 529886257920900301), (4116, 4116, 524639859327624060), (4117, 4117, 519445405274875307), (4118, 4118, 514302381460272581), (4119, 4119, 509210278673537209), (4120, 4120, 504168592746076445), (4121, 4121, 499176824501065787), (4122, 4122, 494234479704025532), (4123, 4123, 489341069013886665), (4124, 4124, 484496107934541252), (4125, 4125, 479699116766872527), (4126, 4126, 474949620561259928), (4127, 4127, 470247149070554384), (4128, 4128, 465591236703519192), (4129, 4129, 460981422478731873), (4130, 4130, 456417249978942449), (4131, 4131, 451898267305883613), (4132, 4132, 447424027035528330), (4133, 4133, 442994086173790425), (4134, 4134, 438608006112663787), (4135, 4135, 434265352586795829), (4136, 4136, 429965695630490920), (4137, 4137, 425708609535139525), (4138, 4138, 421493672807068836), (4139, 4139, 417320468125810729), (4140, 4140, 413188582302782900), (4141, 4141, 409097606240379109), (4142, 4142, 405047134891464464), (4143, 4143, 401036767219271747), (4144, 4144, 397066106157694799), (4145, 4145, 393134758571975048), (4146, 4146, 389242335219777276), (4147, 4147, 385388450712650768), (4148, 4148, 381572723477872048), (4149, 4149, 377794775720665394), (4150, 4150, 374054233386797419), (4151, 4151, 370350726125541999), (4152, 4152, 366683887253011881), (4153, 4153, 363053353715853347), (4154, 4154, 359458766055300344), (4155, 4155, 355899768371584499), (4156, 4156, 352376008288697523), (4157, 4157, 348887136919502499), (4158, 4158, 345432808831190593), (4159, 4159, 342012682011079795), (4160, 4160, 338626417832752272), (4161, 4161, 335273681022527002), (4162, 4162, 331954139626264358), (4163, 4163, 328667464976499365), (4164, 4164, 325413331659900361), (4165, 4165, 322191417485049862), (4166, 4166, 319001403450544418), (4167, 4167, 315842973713410315), (4168, 4168, 312715815557831995), (4169, 4169, 309619619364190094), (4170, 4170, 306554078578406034), (4171, 4171, 303518889681590133), (4172, 4172, 300513752159990230), (4173, 4173, 297538368475237852), (4174, 4174, 294592444034888962), (4175, 4175, 291675687163256398), (4176, 4176, 288787809072531087), (4177, 4177, 285928523834189195), (4178, 4178, 283097548350682372), (4179, 4179, 280294602327408289), (4180, 4180, 277519408244958702), (4181, 4181, 274771691331642279), (4182, 4182, 272051179536279484), (4183, 4183, 269357603501266816), (4184, 4184, 266690696535907739), (4185, 4185, 264050194590007662), (4186, 4186, 261435836227730358), (4187, 4187, 258847362601713226), (4188, 4188, 256284517427438838), (4189, 4189, 253747046957860235), (4190, 4190, 251234699958277461), (4191, 4191, 248747227681462833), (4192, 4192, 246284383843032507), (4193, 4193, 243845924597061889), (4194, 4194, 241431608511942464), (4195, 4195, 239041196546477687), (4196, 4196, 236674452026215532), (4197, 4197, 234331140620015378), (4198, 4198, 232011030316846909), (4199, 4199, 229713891402818722), (4200, 4200, 227439496438434378), (4201, 4201, 225187620236073642), (4202, 4202, 222958039837696675), (4203, 4203, 220750534492768985), (4204, 4204, 218564885636404936), (4205, 4205, 216400876867727659), (4206, 4206, 214258293928443227), (4207, 4207, 212136924681626957), (4208, 4208, 210036559090719760), (4209, 4209, 207956989198732435), (4210, 4210, 205898009107655876), (4211, 4211, 203859414958075125), (4212, 4212, 201841004908985272), (4213, 4213, 199842579117807200), (4214, 4214, 197863939720601189), (4215, 4215, 195904890812476424), (4216, 4216, 193965238428194480), (4217, 4217, 192044790522964831), (4218, 4218, 190143356953430526), (4219, 4219, 188260749458842105), (4220, 4220, 186396781642417926), (4221, 4221, 184551268952889035), (4222, 4222, 182724028666226768), (4223, 4223, 180914879867551255), (4224, 4224, 179123643433219065), (4225, 4225, 177350142013088183), (4226, 4226, 175594200012958597), (4227, 4227, 173855643577186729), (4228, 4228, 172134300571472009), (4229, 4229, 170430000565813871), (4230, 4230, 168742574817637496), (4231, 4231, 167071856255086629), (4232, 4232, 165417679460481811), (4233, 4233, 163779880653942387), (4234, 4234, 162158297677170681), (4235, 4235, 160552769977396714), (4236, 4236, 158963138591481895), (4237, 4237, 157389246130180094), (4238, 4238, 155830936762554548), (4239, 4239, 154288056200549058), (4240, 4240, 152760451683711938), (4241, 4241, 151247971964071226), (4242, 4242, 149750467291159630), (4243, 4243, 148267789397187752), (4244, 4244, 146799791482364111), (4245, 4245, 145346328200360506), (4246, 4246, 143907255643921293), (4247, 4247, 142482431330615142), (4248, 4248, 141071714188727863), (4249, 4249, 139674964543294914), (4250, 4250, 138292044102272192), (4251, 4251, 136922815942843754), (4252, 4252, 135567144497865103), (4253, 4253, 134224895542440696), (4254, 4254, 132895936180634353), (4255, 4255, 131580134832311241), (4256, 4256, 130277361220110139), (4257, 4257, 128987486356544692), (4258, 4258, 127710382531232369), (4259, 4259, 126445923298249870), (4260, 4260, 125193983463613733), (4261, 4261, 123954439072884884), (4262, 4262, 122727167398895924), (4263, 4263, 121512046929599925), (4264, 4264, 120308957356039530), (4265, 4265, 119117779560435178), (4266, 4266, 117938395604391265), (4267, 4267, 116770688717219075), (4268, 4268, 115614543284375322), (4269, 4269, 114469844836015170), (4270, 4270, 113336480035658584), (4271, 4271, 112214336668968895), (4272, 4272, 111103303632642470), (4273, 4273, 110003270923408386), (4274, 4274, 108914129627137016), (4275, 4275, 107835771908056452), (4276, 4276, 106768090998075695), (4277, 4277, 105710981186213559), (4278, 4278, 104664337808132237), (4279, 4279, 103628057235774492), (4280, 4280, 102602036867103457), (4281, 4281, 101586175115944017), (4282, 4282, 100580371401924770), (4283, 4283, 99584526140519574), (4284, 4284, 98598540733187697), (4285, 4285, 97622317557611581), (4286, 4286, 96655759958031268), (4287, 4287, 95698772235674523), (4288, 4288, 94751259639281706), (4289, 4289, 93813128355724462), (4290, 4290, 92884285500717289), (4291, 4291, 91964639109621078), (4292, 4292, 91054098128337701), (4293, 4293, 90152572404294753), (4294, 4294, 89259972677519558), (4295, 4295, 88376210571801542), (4296, 4296, 87501198585942121), (4297, 4297, 86634850085091209), (4298, 4298, 85777079292169514), (4299, 4299, 84927801279375756), (4300, 4300, 84086931959777977), (4301, 4301, 83254388078988096), (4302, 4302, 82430087206918907), (4303, 4303, 81613947729622680), (4304, 4304, 80805888841210574), (4305, 4305, 80005830535852054), (4306, 4306, 79213693599853518), (4307, 4307, 78429399603815365), (4308, 4308, 77652870894866698), (4309, 4309, 76884030588976928), (4310, 4310, 76122802563343494), (4311, 4311, 75369111448854944), (4312, 4312, 74622882622628658), (4313, 4313, 73884042200622433), (4314, 4314, 73152517030319241), (4315, 4315, 72428234683484397), (4316, 4316, 71711123448994452), (4317, 4317, 71001112325737081), (4318, 4318, 70298131015581269), (4319, 4319, 69602109916417098), (4320, 4320, 68912980115264453), (4321, 4321, 68230673381449954), (4322, 4322, 67555122159851439), (4323, 4323, 66886259564209346), (4324, 4324, 66224019370504303), (4325, 4325, 65568336010400300), (4326, 4326, 64919144564752772), (4327, 4327, 64276380757180963), (4328, 4328, 63639980947703923), (4329, 4329, 63009882126439528), (4330, 4330, 62386021907365869), (4331, 4331, 61768338522144425), (4332, 4332, 61156770814004381), (4333, 4333, 60551258231687506), (4334, 4334, 59951740823452977), (4335, 7209, 59358159231141561)]

def glob1 : ℕ := 8116567392432202712

def runs2 : List (ℕ × ℕ × ℕ) := [(0, 3827, 0), (3828, 3840, 41924418349339890037), (3841, 3841, 41815155882860382710), (3842, 3842, 41401144438475626446), (3843, 3843, 40991232117302600441), (3844, 3844, 40585378333962970734), (3845, 3845, 40183542904913832410), (3846, 3846, 39785686044469141000), (3847, 3847, 39391768360860535643), (3848, 3848, 39001750852337164003), (3849, 3849, 38615594903304122776), (3850, 3850, 38233262280499131461), (3851, 3851, 37854715129207060852), (3852, 3852, 37479915969511941438), (3853, 3853, 37108827692586080632), (3854, 3854, 36741413557015921418), (3855, 3855, 36377637185164278631), (3856, 3856, 36017462559568592704), (3857, 3857, 35660854019374844262), (3858, 3858, 35307776256806776497), (3859, 3859, 34958194313670075739), (3860, 3860, 34612073577891164098), (3861, 3861, 34269379780090261483), (3862, 3862, 33930078990188377706), (3863, 3863, 33594137614047898719), (3864, 3864, 33261522390146434375), (3865, 3865, 32932200386283598392), (3866, 3866, 32606138996320394447), (3867, 3867, 32283305936950885591), (3868, 3868, 31963669244505827318), (3869, 3869, 31647197271787947840), (3870, 3870, 31333858684938562217), (3871, 3871, 31023622460335210116), (3872, 3872, 30716457881520010016), (3873, 3873, 30412334536158425759), (3874, 3874, 30111222313028144315), (3875, 3875, 29813091399037766649), (3876, 3876, 29517912276275016484), (3877, 3877, 29225655719084174737), (3878, 3878, 28936292791172450234), (3879, 3879, 28649794842745000232), (3880, 3880, 28366133507668317061), (3881, 3881, 28085280700661700061), (3882, 3882, 27807208614516534714), (3883, 3883, 27531889717343103677), (3884, 3884, 27259296749844657106), (3885, 3885, 26989402722618472382), (3886, 3886, 26722180913483636022), (3887, 3887, 26457604864835283190), (3888, 3888, 26195648381025032861), (3889, 3889, 25936285525767359269), (3890, 3890, 25679490619571642840), (3891, 3891, 25425238237199646377), (3892, 3892, 25173503205148164729), (3893, 3893, 24924260599156598742), (3894, 3894, 24677485741739206675), (3895, 3895, 24433154199741788787), (3896, 3896, 24191241781922563156), (3897, 3897, 23951724536556993223), (3898, 3898, 23714578749066329924), (3899, 3899, 23479780939669633588), (3900, 3900, 23247307861059043157), (3901, 3901, 23017136496098062531), (3902, 3902, 22789244055542636170), (3903, 3903, 22563607975784788287), (3904, 3904, 22340205916618602264), (3905, 3905, 22119015759028319074), (3906, 3906, 21900015602998335716), (3907, 3907, 21683183765344886848), (3908, 3908, 21468498777569194899), (3909, 3909, 21255939383731876138), (3910, 3910, 21045484538348392215), (3911, 3911, 20837113404305338827), (3912, 3912, 20630805350797365175), (3913, 3913, 20426539951284519976), (3914, 3914, 20224296981469821758), (3915, 3915, 20024056417296853226), (3916, 3916, 19825798432967181412), (3917, 3917, 19629503398977407338), (3918, 3918, 19435151880175650830), (3919, 3919, 19242724633837278050), (3920, 3920, 19052202607759681237), (3921, 3921, 18863566938375922017), (3922, 3922, 18676798948887051502), (3923, 3923, 18491880147412922279), (3924, 3924, 18308792225161309187), (3925, 3925, 18127517054615157611), (3926, 3926, 17948036687737779813), (3927, 3927, 17770333354195821597), (3928, 3928, 17594389459599823363), (3929, 3929, 17420187583762201350), (3930, 3930, 17247710478972476584), (3931, 3931, 17076941068289580776), (3932, 3932, 16907862443851070076), (3933, 3933, 16740457865199079283), (3934, 3934, 16574710757622850775), (3935, 3935, 16410604710517674035), (3936, 3936, 16248123475760073302), (3937, 3937, 16087250966099082477), (3938, 3938, 15927971253563447997), (3939, 3939, 15770268567884601977), (3940, 3940, 15614127294935249482), (3941, 3941, 15459531975183415329), (3942, 3942, 15306467302161797356), (3943, 3943, 15154918120952274609), (3944, 3944, 15004869426685420405), (3945, 3945, 14856306363054871689), (3946, 3946, 14709214220846407612), (3947, 3947, 14563578436481591695), (3948, 3948, 14419384590575833362), (3949, 3949, 14276618406510726101), (3950, 3950, 14135265749020520892), (3951, 3951, 13995312622792594943), (3952, 3952, 13856745171081777171), (3953, 3953, 13719549674338393238), (3954, 3954, 13583712548849894295), (3955, 3955, 13449220345395934946), (3956, 3956, 13316059747916767273), (3957, 3957, 13184217572194819082), (3958, 3958, 13053680764549325824), (3959, 3959, 12924436400543886955), (3960, 3960, 12796471683706818767), (3961, 3961, 12669773944264176997), (3962, 3962, 12544330637885323759), (3963, 3963, 12420129344440914613), (3964, 3964, 12297157766773182786), (3965, 3965, 12175403729478398798), (3966, 3966, 12054855177701384948), (3967, 3967, 11935500175941965295), (3968, 3968, 11817326906873232965), (3969, 3969, 11700323670171517788), (3970, 3970, 11584478881357938404), (3971, 3971, 11469781070651424162), (3972, 3972, 11356218881833093230), (3973, 3973, 11243781071121874485), (3974, 3974, 11132456506061261866), (3975, 3975, 11022234164417090957), (3976, 3976, 10913103133086228670), (3977, 3977, 10805052607016067990), (3978, 3978, 10698071888134720782), (3979, 3979, 10592150384291802755), (3980, 3980, 10487277608209705698), (3981, 3981, 10383443176445253166), (3982, 3982, 10280636808361636798), (3983, 3983, 10178848325110531483), (3984, 3984, 10078067648624288597), (3985, 3985, 9978284800618107522), (3986, 3986, 9879489901602086655), (3987, 3987, 9781673169903056095), (3988, 3988, 9684824920696095143), (3989, 3989, 9588935565045638756), (3990, 3990, 9493995608956077976), (3991, 3991, 9399995652431760372), (3992, 3992, 9306926388546297398), (3993, 3993, 9214778602521086533), (3994, 3994, 9123543170812956963), (3995, 3995, 9033211060210848478), (3996, 3996, 8943773326941434137), (3997, 3997, 8855221115783598155), (3998, 3998, 8767545659191681342), (3999, 3999, 8680738276427407269), (4000, 4000, 8594790372700403237), (4001, 4001, 8509693438317230928), (4002, 4002, 8425439047838842503), (4003, 4003, 8342018859246378716), (4004, 4004, 8259424613115226451), (4005, 4005, 8177648131797253912), (4006, 4006, 8096681318611142487), (4007, 4007, 8016516157040735136), (4008, 4008, 7937144709941321917), (4009, 4009, 7858559118753784076), (4010, 4010, 7780751602726518887), (4011, 4011, 7703714458145068205), (4012, 4012, 7627440057569374460), (4013, 4013, 7551920849078588575), (4014, 4014, 7477149355523355024), (4015, 4015, 7403118173785500024), (4016, 4016, 7329819974045049529), (4017, 4017, 7257247499054504484), (4018, 4018, 7185393563420301469), (4019, 4019, 7114251052891387593), (4020, 4020, 7043812923654839201), (4021, 4021, 6974072201638454655), (4022, 4022, 6905021981820252133), (4023, 4023, 6836655427544804093), (4024, 4024, 6768965769846340686), (4025, 4025, 6701946306778555134), (4026, 4026, 6635590402751044687), (4027, 4027, 6569891487872321473), (4028, 4028, 6504843057299328191), (4029, 4029, 6440438670593394248), (4030, 4030, 6376671951082568563), (4031, 4031, 6313536585230265904), (4032, 4032, 6251026322010164261), (4033, 4033, 6189134972287291348), (4034, 4034, 6127856408205238958), (4035, 4035, 6067184562579444513), (4036, 4036, 6007113428296479716), (4037, 4037, 5947637057719286847), (4038, 4038, 5888749562098303809), (4039, 4039, 5830445110988419613), (4040, 4040, 5772717931671702587), (4041, 4041, 5715562308585844146), (4042, 4042, 5658972582758261531), (4043, 4043, 5602943151245803496), (4044, 4044, 5547468466580003461), (4045, 4045, 5492543036217825209), (4046, 4046, 5438161421997846741), (4047, 4047, 5384318239601828457), (4048, 4048, 5331008158021612334), (4049, 4049, 5278225899031299340), (4050, 4050, 5225966236664652812), (4051, 4051, 5174223996697676052), (4052, 4052, 5122994056136312922), (4053, 4053, 5072271342709220715), (4054, 4054, 5022050834365565065), (4055, 4055, 4972327558777787193), (4056, 4056, 4923096592849294250), (4057, 4057, 4874353062227024010), (4058, 4058, 4826092140818835653), (4059, 4059, 4778309050315678865), (4060, 4060, 4730999059718493926), (4061, 4061, 4684157484869795966), (4062, 4062, 4637779687989896996), (4063, 4063, 4591861077217719798), (4064, 4064, 4546397106156158216), (4065, 4065, 4501383273421938828), (4066, 4066, 4456815122199939433), (4067, 4067, 4412688239801920231), (4068, 4068, 4368998257229623991), (4069, 4069, 4325740848742201971), (4070, 4070, 4282911731427922744), (4071, 4071, 4240506664780121529), (4072, 4072, 4198521450277348048), (4073, 4073, 4156951930967671335), (4074, 4074, 4115793991057100331), (4075, 4075, 4075043555502079536), (4076, 4076, 4034696589606019343), (4077, 4077, 3994749098619821131), (4078, 4078, 3955197127346357556), (4079, 4079, 3916036759748868867), (4080, 4080, 3877264118563236502), (4081, 4081, 3838875364914095547), (4082, 4082, 3800866697934748066), (4083, 4083, 3763234354390839669), (4084, 4084, 3725974608307762049), (4085, 4085, 3689083770601744603), (4086, 4086, 3652558188714598617), (4087, 4087, 3616394246252077838), (4088, 4088, 3580588362625819642), (4089, 4089, 3545136992698831329), (4090, 4090, 3510036626434486464), (4091, 4091, 3475283788548996499), (4092, 4092, 3440875038167323266), (4093, 4093, 3406806968482498284), (4094, 4094, 3373076206418315132), (4095, 4095, 3339679412295361517), (4096, 4096, 3306613279500357938), (4097, 4097, 3273874534158770235), (4098, 4098, 3241459934810663599), (4099, 4099, 3209366272089765940), (4100, 4100, 3177590368405708851), (4101, 4101, 3146129077629414704), (4102, 4102, 3114979284781598717), (4103, 4103, 3084137905724355166), (4104, 4104, 3053601886855797194), (4105, 4105, 3023368204807719994), (4106, 4106, 2993433866146257420), (4107, 4107, 2963795907075502396), (4108, 4108, 2934451393144061778), (4109, 4109, 2905397418954516612), (4110, 4110, 2876631107875759021), (4111, 4111, 2848149611758177249), (4112, 4112, 2819950110651660643), (4113, 4113, 2792029812526396676), (4114, 4114, 2764385952996432352), (4115, 4115, 2737015795045972626), (4116, 4116, 2709916628758388739), (4117, 4117, 2683085771047909642), (4118, 4118, 2656520565393969943), (4119, 4119, 2630218381578188062), (4120, 4120, 2604176615423948576), (4121, 4121, 2578392688538562947), (4122, 4122, 2552864048057983116), (4123, 4123, 2527588166394042689), (4124, 4124, 2502562540984200682), (4125, 4125, 2477784694043763052), (4126, 4126, 2453252172320557477), (4127, 4127, 2428962546852037106), (4128, 4128, 2404913412724789214), (4129, 4129, 2381102388836424964), (4130, 4130, 2357527117659826697), (4131, 4131, 2334185265009729403), (4132, 4132, 2311074519811613270), (4133, 4133, 2288192593872884426), (4134, 4134, 2265537221656321214), (4135, 4135, 2243106160055763578), (4136, 4136, 2220897188174023345), (4137, 4137, 2198908107102993411), (4138, 4138, 2177136739705934070), (4139, 4139, 2155580930401914921), (4140, 4140, 2134238544952391011), (4141, 4141, 2113107470249892090), (4142, 4142, 2092185614108804049), (4143, 4143, 2071470905058221831), (4144, 4144, 2050961292136853298), (4145, 4145, 2030654744689953760), (4146, 4146, 2010549252168271050), (4147, 4147, 1990642823928981238), (4148, 4148, 1970933489038595285), (4149, 4149, 1951419296077817114), (4150, 4150, 1932098312948333776), (4151, 4151, 1912968626681518590), (4152, 4152, 1894028343249028307), (4153, 4153, 1875275587375275551), (4154, 4154, 1856708502351757972), (4155, 4155, 1838325249853225714), (4156, 4156, 1820124009755669024), (4157, 4157, 1802102979956107945), (4158, 4158, 1784260376194166282), (4159, 4159, 1766594431875412160), (4160, 4160, 1749103397896447684), (4161, 4161, 1731785542471730380), (4162, 4162, 1714639150962109287), (4163, 4163, 1697662525705058700), (4164, 4164, 1680853985846592772), (4165, 4165, 1664211867174844329), (4166, 4166, 1647734521955291415), (4167, 4167, 1631420318767615262), (4168, 4168, 1615267642344173527), (4169, 4169, 1599274893410072799), (4170, 4170, 1583440488524824553), (4171, 4171, 1567762859925568865), (4172, 4172, 1552240455371850361), (4173, 4173, 1536871737991931051), (4174, 4174, 1521655186130624803), (4175, 4175, 1506589293198638418), (4176, 4176, 1491672567523404375), (4177, 4177, 1476903532201390470), (4178, 4178, 1462280724951871752), (4179, 4179, 1447802697972150250), (4180, 4180, 1433468017794208168), (4181, 4181, 1419275265142780365), (4182, 4182, 1405223034794832044), (4183, 4183, 1391309935440427767), (4184, 4184, 1377534589544977987), (4185, 4185, 1363895633212849492), (4186, 4186, 1350391716052326229), (4187, 4187, 1337021501041907158), (4188, 4188, 1323783664397927879), (4189, 4189, 1310676895443492950), (4190, 4190, 1297699896478705891), (4191, 4191, 1284851382652184050), (4192, 4192, 1272130081833845594), (4193, 4193, 1259534734488956034), (4194, 4194, 1247064093553421816), (4195, 4195, 1234716924310318630), (4196, 4196, 1222492004267642207), (4197, 4197, 1210388123037269512), (4198, 4198, 1198404082215118329), (4199, 4199, 1186538695262493395), (4200, 4200, 1174790787388607322), (4201, 4201, 1163159195434264675), (4202, 4202, 1151642767756697698), (4203, 4203, 1140240364115542275), (4204, 4204, 1128950855559942847), (4205, 4205, 1117773124316775096), (4206, 4206, 1106706063679975343), (4207, 4207, 1095748577900965686), (4208, 4208, 1084899582080164045), (4209, 4209, 1074158002059568362), (4210, 4210, 1063522774316404318), (4211, 4211, 1052992845857826058), (4212, 4212, 1042567174116659463), (4213, 4213, 1032244726848177686), (4214, 4214, 1022024482027898699), (4215, 4215, 1011905427750394752), (4216, 4216, 1001886562129103715), (4217, 4217, 991966893197132391), (4218, 4218, 982145438809041971), (4219, 4219, 972421226543605912), (4220, 4220, 962793293607530606), (4221, 4221, 953260686740129313), (4222, 4222, 943822462118939914), (4223, 4223, 934477685266277142), (4224, 4224, 925225430956710042), (4225, 4225, 916064783125455487), (4226, 4226, 906994834777678700), (4227, 4227, 898014687898691782), (4228, 4228, 889123453365041369), (4229, 4229, 880320250856476603), (4230, 4230, 871604208768788715), (4231, 4231, 862974464127513580), (4232, 4232, 854430162502488693), (4233, 4233, 845970457923256131), (4234, 4234, 837594512795303100), (4235, 4235, 829301497817131783), (4236, 4236, 821090591898150280), (4237, 4237, 812960982077376515), (4238, 4238, 804911863442947044), (4239, 4239, 796942439052422816), (4240, 4240, 789051919853883976), (4241, 4241, 781239524607805917), (4242, 4242, 773504479809708829), (4243, 4243, 765846019613573098), (4244, 4244, 758263385756012968), (4245, 4245, 750755827481200959), (4246, 4246, 743322601466535603), (4247, 4247, 735962971749045151), (4248, 4248, 728676209652519952), (4249, 4249, 721461593715366289), (4250, 4250, 714318409619174543), (4251, 4251, 707245950117994597), (4252, 4252, 700243514968311482), (4253, 4253, 693310410859714339), (4254, 4254, 686445951346251821), (4255, 4255, 679649456778467149), (4256, 4256, 672920254236106088), (4257, 4257, 666257677461491177), (4258, 4258, 659661066793555621), (4259, 4259, 653129769102530317), (4260, 4260, 646663137725277542), (4261, 4261, 640260532401264893), (4262, 4262, 633921319209173161), (4263, 4263, 627644870504131843), (4264, 4264, 621430564855576082), (4265, 4265, 615277786985718893), (4266, 4266, 609185927708632568), (4267, 4267, 603154383869933235), (4268, 4268, 597182558287062609), (4269, 4269, 591269859690160999), (4270, 4270, 585415702663525742), (4271, 4271, 579619507587649249), (4272, 4272, 573880700581830940), (4273, 4273, 568198713447357366), (4274, 4274, 562572983611244917), (4275, 4275, 557002954070539522), (4276, 4276, 551488073337167843), (4277, 4277, 546027795383334498), (4278, 4278, 540621579587459899), (4279, 4279, 535268890680653366), (4280, 4280, 529969198693716204), (4281, 4281, 524721978904669509), (4282, 4282, 519526711786801494), (4283, 4283, 514382882957229202), (4284, 4284, 509289983125969507), (4285, 4285, 504247508045514363), (4286, 4286, 499254958460905310), (4287, 4287, 494311840060302287), (4288, 4288, 489417663426041868), (4289, 4289, 484571943986180068), (4290, 4290, 479774201966514919), (4291, 4291, 475023962343084078), (4292, 4292, 470320754795132750), (4293, 4293, 465664113658547277), (4294, 4294, 461053577879749780), (4295, 4295, 456488690970049287), (4296, 4296, 451969000960444838), (4297, 4297, 447494060356876078), (4298, 4298, 443063426095916909), (4299, 4299, 438676659500907830), (4300, 4300, 434333326238522604), (4301, 4301, 430032996275764955), (4302, 4302, 425775243837391044), (4303, 4303, 421559647363753509), (4304, 4304, 417385789469062880), (4305, 4305, 413253256900062258), (4306, 4306, 409161640495111146), (4307, 4307, 405110535143674402), (4308, 4308, 401099539746212280), (4309, 4309, 397128257174467604), (4310, 4310, 393196294232146142), (4311, 4311, 389303261615986279), (4312, 4312, 385448773877214138), (4313, 4313, 381632449383380335), (4314, 4314, 377853910280574589), (4315, 4315, 374112782456014444), (4316, 4316, 370408695501004400), (4317, 4317, 366741282674261782), (4318, 4318, 363110180865605725), (4319, 4319, 359515030560005669), (4320, 4320, 355955475801985810), (4321, 4321, 352431164160381991), (4322, 4322, 348941746693447515), (4323, 4323, 345486877914304471), (4324, 4324, 342066215756737100), (4325, 4325, 338679421541323861), (4326, 4326, 335326159941904813), (4327, 4327, 332006098952381003), (4328, 4328, 328718909853842577), (4329, 4329, 325464267182022354), (4330, 4330, 322241848695071637), (4331, 4331, 319051335341655086), (4332, 4332, 315892411229361472), (4333, 4333, 312764763593427200), (4334, 4334, 309668082765769505), (4335, 7209, 306602062144326242)]

def glob2 : ℕ := 41924418349339890037

def runs3 : List (ℕ × ℕ × ℕ) := [(0, 3827, 0), (3828, 3828, 48075485250983224), (3829, 3829, 230240520780275981), (3830, 3830, 410601942096407423), (3831, 3831, 589177606765844494), (3832, 3832, 765985195547465356), (3833, 3833, 941042214143129577), (3834, 3834, 1114365994930915934), (3835, 3835, 1285973698681199455), (3836, 3836, 1455882316255737595), (3837, 3837, 1624108670289933774), (3838, 3838, 1790669416858444842), (3839, 3839, 1955581047124297384), (3840, 3840, 2118859888971676139), (3841, 3841, 2280522108622546193), (3842, 3842, 2440583712237269019), (3843, 3843, 2599060547499370827), (3844, 3844, 2755968305184620142), (3845, 3845, 2911322520714569958), (3846, 3846, 3065138575694718291), (3847, 3847, 3217431699437439413), (3848, 3848, 3368216970469836564), (3849, 3849, 3517509318026665426), (3850, 3850, 3665323523528476180), (3851, 3851, 3811674222045120492), (3852, 3852, 3956575903744768324), (3853, 3853, 4100042915328578060), (3854, 3854, 4242089461451161957), (3855, 3855, 4382729606126987597), (3856, 3856, 4521977274122854567), (3857, 3857, 4659846252336584241), (3858, 3858, 4796350191162059166), (3859, 3859, 4931502605840747210), (3860, 3860, 5065316877799844283), (3861, 3861, 5197806255977168118), (3862, 3862, 5328983858132934291), (3863, 3863, 5458862672148544364), (3864, 3864, 5587455557312514733), (3865, 3865, 5714775245593673514), (3866, 3866, 5840834342901751515), (3867, 3867, 5965645330335492110), (3868, 3868, 6089220565418403590), (3869, 3869, 6211572283322276343), (3870, 3870, 6332712598078585999), (3871, 3871, 6452653503777902490), (3872, 3872, 6571406875757423769), (3873, 3873, 6688984471776751767), (3874, 3874, 6805397933182027013), (3875, 3875, 6920658786058537158), (3876, 3876, 7034778442371913538), (3877, 3877, 7147768201098028767), (3878, 3878, 7259639249341707211), (3879, 3879, 7370402663444359136), (3880, 3880, 7480069410080648170), (3881, 3881, 7588650347344300680), (3882, 3882, 7696156225823164550), (3883, 3883, 7802597689663623828), (3884, 3884, 7907985277624474598), (3885, 3885, 8012329424120366450), (3886, 3886, 8115640460254912838), (3887, 3887, 8217928614843572628), (3888, 3888, 8319204015426404103), (3889, 3889, 8419476689270791702), (3890, 3890, 8518756564364244770), (3891, 3891, 8617053470397366620), (3892, 3892, 8714377139737091224), (3893, 3893, 8810737208390283902), (3894, 3894, 8906143216957801404), (3895, 3895, 9000604611579105861), (3896, 3896, 9094130744867526116), (3897, 3897, 9186730876836259042), (3898, 3898, 9278414175815202533), (3899, 3899, 9369189719358710940), (3900, 3900, 9459066495144362827), (3901, 3901, 9548053401862830043), (3902, 3902, 9636159250098936197), (3903, 3903, 9723392763203991796), (3904, 3904, 9809762578159492388), (3905, 3905, 9895277246432265252), (3906, 3906, 9979945234821149275), (3907, 3907, 10063774926295291872), (3908, 3908, 10146774620824145929), (3909, 3909, 10228952536199248956), (3910, 3910, 10310316808847865814), (3911, 3911, 10390875494638575574), (3912, 3912, 10470636569678882268), (3913, 3913, 10549607931104928499), (3914, 3914, 10627797397863390114), (3915, 3915, 10705212711485629337), (3916, 3916, 10781861536854183023), (3917, 3917, 10857751462961661920), (3918, 3918, 10932890003662136075), (3919, 3919, 11007284598415080783), (3920, 3920, 11080942613021956732), (3921, 3921, 11153871340355497276), (3922, 3922, 11226078001081775041), (3923, 3923, 11297569744375119364), (3924, 3924, 11368353648625955327), (3925, 3925, 11438436722141634498), (3926, 3926, 11507825903840326747), (3927, 3927, 11576528063938041844), (3928, 3928, 11644550004628848872), (3929, 3929, 11711898460758360780), (3930, 3930, 11778580100490550789), (3931, 3931, 11844601525967966638), (3932, 3932, 11909969273965408074), (3933, 3933, 11974689816537132267), (3934, 3934, 12038769561657651271), (3935, 3935, 12102214853856184937), (3936, 3936, 12165031974844832132), (3937, 3937, 12227227144140522424), (3938, 3938, 12288806519680809842), (3939, 3939, 12349776198433569662), (3940, 3940, 12410142217000658592), (3941, 3941, 12469910552215598127), (3942, 3942, 12529087121735340240), (3943, 3943, 12587677784626174016), (3944, 3944, 12645688341943831220), (3945, 3945, 12703124537307848254), (3946, 3946, 12759992057470241357), (3947, 3947, 12816296532878551359), (3948, 3948, 12872043538233313738), (3949, 3949, 12927238593040009163), (3950, 3950, 12981887162155549187), (3951, 3951, 13035994656329351191), (3952, 3952, 13089566432739056146), (3953, 3953, 13142607795520942240), (3954, 3954, 13195123996295086887), (3955, 3955, 13247120234685329112), (3956, 3956, 13298601658834083790), (3957, 3957, 13349573365912058719), (3958, 3958, 13400040402622924985), (3959, 3959, 13450007765702990596), (3960, 3960, 13499480402415926843), (3961, 3961, 13548463211042596396), (3962, 3962, 13596961041366031596), (3963, 3963, 13644978695151611002), (3964, 3964, 13692520926622481701), (3965, 3965, 13739592442930274473), (3966, 3966, 13786197904621158405), (3967, 3967, 13832341926097281110), (3968, 3968, 13878029076073640224), (3969, 3969, 13923263878030431426), (3970, 3970, 13968050810660917764), (3971, 3971, 14012394308314864634), (3972, 3972, 14056298761437584307), (3973, 3973, 14099768517004633488), (3974, 3974, 14142807878952206935), (3975, 3975, 14185421108603269754), (3976, 3976, 14227612425089470564), (3977, 3977, 14269386005768877307), (3978, 3978, 14310745986639577053), (3979, 3979, 14351696462749180762), (3980, 3980, 14392241488600273542), (3981, 3981, 14432385078551850553), (3982, 3982, 14472131207216778286), (3983, 3983, 14511483809855320596), (3984, 3984, 14550446782764768428), (3985, 3985, 14589023983665211826), (3986, 3986, 14627219232081492418), (3987, 3987, 14665036309721374192), (3988, 3988, 14702478960849970009), (3989, 3989, 14739550892660460916), (3990, 3990, 14776255775641144982), (3991, 3991, 14812597243938851978), (3992, 3992, 14848578895718759895), (3993, 3993, 14884204293520648922), (3994, 3994, 14919476964611628157), (3995, 3995, 14954400401335369973), (3996, 3996, 14988978061457886623), (3997, 3997, 15023213368509883306), (3998, 3998, 15057109712125721607), (3999, 3999, 15090670448379026854), (4000, 4000, 15123898900114972644), (4001, 4001, 15156798357279275406), (4002, 4002, 15189372077243931606), (4003, 4003, 15221623285129729824), (4004, 4004, 15253555174125569644), (4005, 4005, 15285170905804618970), (4006, 4006, 15316473610437341076), (4007, 4007, 15347466387301422368), (4008, 4008, 15378152304988631569), (4009, 4009, 15408534401708640678), (4010, 4010, 15438615685589837816), (4011, 4011, 15468399134977161715), (4012, 4012, 15497887698726987358), (4013, 4013, 15527084296499091954), (4014, 4014, 15555991819045730169), (4015, 4015, 15584613128497847213), (4016, 4016, 15612951058648458147), (4017, 4017, 15641008415233221449), (4018, 4018, 15668787976208234619), (4019, 4019, 15696292492025079342), (4020, 4020, 15723524685903143424), (4021, 4021, 15750487254099246475), (4022, 4022, 15777182866174596031), (4023, 4023, 15803614165259100542), (4024, 4024, 15829783768313065404), (4025, 4025, 15855694266386297941), (4026, 4026, 15881348224874646987), (4027, 4027, 15906748183774002478), (4028, 4028, 15931896657931780193), (4029, 4029, 15956796137295916543), (4030, 4030, 15981449087161398079), (4031, 4031, 16005857948414350094), (4032, 4032, 16030025137773708525), (4033, 4033, 16053953048030499050), (4034, 4034, 16077644048284747096), (4035, 4035, 16101100484180042190), (4036, 4036, 16124324678135779907), (4037, 4037, 16147318929577104379), (4038, 4038, 16170085515162574154), (4039, 4039, 16192626689009573931), (4040, 4040, 16214944682917494502), (4041, 4041, 16237041706588702988), (4042, 4042, 16258919947847325252), (4043, 4043, 16280581572855862147), (4044, 4044, 16302028726329661052), (4045, 4045, 16323263531749263929), (4046, 4046, 16344288091570652916), (4047, 4047, 16365104487433414289), (4048, 4048, 16385714780366841392), (4049, 4049, 16406121010993996938), (4050, 4050, 16426325199733754906), (4051, 4051, 16446329347000842002), (4052, 4052, 16466135433403898533), (4053, 4053, 16485745419941578266), (4054, 4054, 16505161248196706715), (4055, 4055, 16524384840528517061), (4056, 4056, 16543418100262982749), (4057, 4057, 16562262911881265609), (4058, 4058, 16580921141206298144), (4059, 4059, 16599394635587518476), (4060, 4060, 16617685224083776229), (4061, 4061, 16635794717644427471), (4062, 4062, 16653724909288636621), (4063, 4063, 16671477574282903106), (4064, 4064, 16689054470316830319), (4065, 4065, 16706457337677154292), (4066, 4066, 16723687899420049315), (4067, 4067, 16740747861541727556), (4068, 4068, 16757638913147349576), (4069, 4069, 16774362726618262468), (4070, 4070, 16790920957777582162), (4071, 4071, 16807315246054136315), (4072, 4072, 16823547214644783991), (4073, 4073, 16839618470675128225), (4074, 4074, 16855530605358637368), (4075, 4075, 16871285194154190974), (4076, 4076, 16886883796922065832), (4077, 4077, 16902327958078377573), (4078, 4078, 16917619206747993157), (4079, 4079, 16932759056915929380), (4080, 4080, 16947749007577252372), (4081, 4081, 16962590542885492959), (4082, 4082, 16977285132299592549), (4083, 4083, 16991834230729394124), (4084, 4084, 17006239278679692713), (4085, 4085, 17020501702392859633), (4086, 4086, 17034622913990054603), (4087, 4087, 17048604311611039722), (4088, 4088, 17062447279552609147), (4089, 4089, 17076153188405648181), (4090, 4090, 17089723395190835344), (4091, 4091, 17103159243493000852), (4092, 4092, 17116462063594154819), (4093, 4093, 17129633172605198352), (4094, 4094, 17142673874596330563), (4095, 4095, 17155585460726164434), (4096, 4096, 17168369209369564308), (4097, 4097, 17181026386244217647), (4098, 4098, 17193558244535953627), (4099, 4099, 17205966025022820934), (4100, 4100, 17218250956197937079), (4101, 4101, 17230414254391121382), (4102, 4102, 17242457123889323661), (4103, 4103, 17254380757055860572), (4104, 4104, 17266186334448471374), (4105, 4105, 17277875024936204842), (4106, 4106, 17289447985815148869), (4107, 4107, 17300906362923014243), (4108, 4108, 17312251290752583920), (4109, 4109, 17323483892564039046), (4110, 4110, 17334605280496172834), (4111, 4111, 17345616555676503317), (4112, 4112, 17356518808330295874), (4113, 4113, 17367313117888506327), (4114, 4114, 17378000553094655290), (4115, 4115, 17388582172110644363), (4116, 4116, 17399059022621524633), (4117, 4117, 17409432141939227870), (4118, 4118, 17419702557105270679), (4119, 4119, 17429871284992441778), (4120, 4120, 17439939332405482469), (4121, 4121, 17449907696180770283), (4122, 4122, 17459777363285015642), (4123, 4123, 17469549310912981345), (4124, 4124, 17479224506584234516), (4125, 4125, 17488803908238940626), (4126, 4126, 17498288464332709052), (4127, 4127, 17507679113930499572), (4128, 4128, 17516976786799599097), (4129, 4129, 17526182403501677835), (4130, 4130, 17535296875483934011), (4131, 4131, 17544321105169336166), (4132, 4132, 17553255986045971962), (4133, 4133, 17562102402755512355), (4134, 4134, 17570861231180799872), (4135, 4135, 17579533338532569691), (4136, 4136, 17588119583435312087), (4137, 4137, 17596620816012284755), (4138, 4138, 17605037877969683437), (4139, 4139, 17613371602679979162), (4140, 4140, 17621622815264430374), (4141, 4141, 17629792332674778109), (4142, 4142, 17637880963774132302), (4143, 4143, 17645889509417057246), (4144, 4144, 17653818762528864121), (4145, 4145, 17661669508184118453), (4146, 4146, 17669442523684370266), (4147, 4147, 17677138578635114636), (4148, 4148, 17684758435021990250), (4149, 4149, 17692302847286223530), (4150, 4150, 17699772562399325789), (4151, 4151, 17707168319937050797), (4152, 4152, 17714490852152620112), (4153, 4153, 17721740884049223394), (4154, 4154, 17728919133451800901), (4155, 4155, 17736026311078115265), (4156, 4156, 17743063120609119585), (4157, 4157, 17750030258758628813), (4158, 4158, 17756928415342301316), (4159, 4159, 17763758273345937458), (4160, 4160, 17770520508993101954), (4161, 4161, 17777215791812076704), (4162, 4162, 17783844784702150713), (4163, 4163, 17790408143999253692), (4164, 4164, 17796906519540939810), (4165, 4165, 17803340554730728046), (4166, 4166, 17809710886601805507), (4167, 4167, 17816018145880100023), (4168, 4168, 17822262957046728256), (4169, 4169, 17828445938399825517), (4170, 4170, 17834567702115763399), (4171, 4171, 17840628854309761303), (4172, 4172, 17846629995095897840), (4173, 4173, 17852571718646528076), (4174, 4174, 17858454613251112467), (4175, 4175, 17864279261374463350), (4176, 4176, 17870046239714414719), (4177, 4177, 17875756119258921025), (4178, 4178, 17881409465342590635), (4179, 4179, 17887006837702659555), (4180, 4180, 17892548790534410962), (4181, 4181, 17898035872546046018), (4182, 4182, 17903468627013011420), (4183, 4183, 17908847591831789045), (4184, 4184, 17914173299573153031), (4185, 4185, 17919446277534899552), (4186, 4186, 17924667047794054523), (4187, 4187, 17929836127258564395), (4188, 4188, 17934954027718475160), (4189, 4189, 17940021255896604630), (4190, 4190, 17945038313498713016), (4191, 4191, 17950005697263176764), (4192, 4192, 17954923899010170574), (4193, 4193, 17959793405690362466), (4194, 4194, 17964614699433126715), (4195, 4195, 17969388257594279437), (4196, 4196, 17974114552803341538), (4197, 4197, 17978794053010333717), (4198, 4198, 17983427221532108151), (4199, 4199, 17988014517098221453), (4200, 4200, 17992556393896353435), (4201, 4201, 17997053301617276189), (4202, 4202, 18001505685499377926), (4203, 4203, 18005913986372745982), (4204, 4204, 18010278640702813365), (4205, 4205, 18014600080633573149), (4206, 4206, 18018878734030365015), (4207, 4207, 18023115024522238150), (4208, 4208, 18027309371543894719), (4209, 4209, 18031462190377218055), (4210, 4210, 18035573892192389674), (4211, 4211, 18039644884088599198), (4212, 4212, 18043675569134351202), (4213, 4213, 18047666346407372989), (4214, 4214, 18051617611034127233), (4215, 4215, 18055529754228933415), (4216, 4216, 18059403163332701912), (4217, 4217, 18063238221851284582), (4218, 4218, 18067035309493445642), (4219, 4219, 18070794802208456592), (4220, 4220, 18074517072223318919), (4221, 4221, 18078202488079618253), (4222, 4222, 18081851414670013632), (4223, 4223, 18085464213274365494), (4224, 4224, 18089041241595505950), (4225, 4225, 18092582853794654917), (4226, 4226, 18096089400526485578), (4227, 4227, 18099561228973842667), (4228, 4228, 18102998682882117013), (4229, 4229, 18106402102593279732), (4230, 4230, 18109771825079579454), (4231, 4231, 18113108183976905911), (4232, 4232, 18116411509617823195), (4233, 4233, 18119682129064275952), (4234, 4234, 18122920366139971750), (4235, 4235, 18126126541462442838), (4236, 4236, 18129300972474790450), (4237, 4237, 18132443973477114818), (4238, 4238, 18135555855657633994), (4239, 4239, 18138636927123494564), (4240, 4240, 18141687492931277308), (4241, 4241, 18144707855117200816), (4242, 4242, 18147698312727026071), (4243, 4243, 18150659161845664938), (4244, 4244, 18153590695626495499), (4245, 4245, 18156493204320387144), (4246, 4246, 18159366975304438277), (4247, 4247, 18162212293110429498), (4248, 4248, 18165029439452995064), (4249, 4249, 18167818693257515426), (4250, 4250, 18170580330687733606), (4251, 4251, 18173314625173098141), (4252, 4252, 18176021847435835304), (4253, 4253, 18178702265517753287), (4254, 4254, 18181356144806780993), (4255, 4255, 18183983748063244069), (4256, 4256, 18186585335445880777), (4257, 4257, 18189161164537600290), (4258, 4258, 18191711490370985947), (4259, 4259, 18194236565453546003), (4260, 4260, 18196736639792714376), (4261, 4261, 18199211960920603853), (4262, 4262, 18201662773918514227), (4263, 4263, 18204089321441197766), (4264, 4264, 18206491843740884437), (4265, 4265, 18208870578691069261), (4266, 4266, 18211225761810064136), (4267, 4267, 18213557626284316487), (4268, 4268, 18215866402991497033), (4269, 4269, 18218152320523358959), (4270, 4270, 18220415605208370768), (4271, 4271, 18222656481134125034), (4272, 4272, 18224875170169525297), (4273, 4273, 18227071891986753280), (4274, 4274, 18229246864083018610), (4275, 4275, 18231400301802093195), (4276, 4276, 18233532418355632387), (4277, 4277, 18235643424844285053), (4278, 4278, 18237733530278594623), (4279, 4279, 18239802941599693207), (4280, 4280, 18241851863699790815), (4281, 4281, 18243880499442461714), (4282, 4282, 18245889049682729931), (4283, 4283, 18247877713286955888), (4284, 4284, 18249846687152526143), (4285, 4285, 18251796166227348177), (4286, 4286, 18253726343529152171), (4287, 4287, 18255637410164601671), (4288, 4288, 18257529555348215037), (4289, 4289, 18259402966421099557), (4290, 4290, 18261257828869500073), (4291, 4291, 18263094326343163949), (4292, 4292, 18264912640673524223), (4293, 4293, 18266712951891702712), (4294, 4294, 18268495438246334880), (4295, 4295, 18270260276221218214), (4296, 4296, 18272007640552785871), (4297, 4297, 18273737704247407314), (4298, 4298, 18275450638598517654), (4299, 4299, 18277146613203577396), (4300, 4300, 18278825795980864269), (4301, 4301, 18280488353186098798), (4302, 4302, 18282134449428905261), (4303, 4303, 18283764247689109681), (4304, 4304, 18285377909332876432), (4305, 4305, 18286975594128685098), (4306, 4306, 18288557460263149123), (4307, 4307, 18290123664356677860), (4308, 4308, 18291674361478983541), (4309, 4309, 18293209705164434710), (4310, 4310, 18294729847427257650), (4311, 4311, 18296234938776587293), (4312, 4312, 18297725128231369118), (4313, 4313, 18299200563335113499), (4314, 4314, 18300661390170503975), (4315, 4315, 18302107753373860883), (4316, 4316, 18303539796149461781), (4317, 4317, 18304957660283720096), (4318, 4318, 18306361486159223379), (4319, 4319, 18307751412768632569), (4320, 4320, 18309127577728443649), (4321, 4321, 18310490117292613035), (4322, 4322, 18311839166366048070), (4323, 4323, 18313174858517963947), (4324, 4324, 18314497325995108379), (4325, 4325, 18315806699734855342), (4326, 4326, 18317103109378169166), (4327, 4327, 18318386683282440280), (4328, 4328, 18319657548534193857), (4329, 4329, 18320915830961672647), (4330, 4330, 18322161655147295211), (4331, 4331, 18323395144439990819), (4332, 4332, 18324616420967412213), (4333, 4333, 18325825605648027455), (4334, 4334, 18327022818203092050), (4335, 7209, 18446744073709506512)]

def glob3 : ℕ := 18446744073709551616

def runs4 : List (ℕ × ℕ × ℕ) := [(0, 3000, 175341116510584023475), (3001, 3001, 175342087350496414587), (3002, 3002, 175343067906082343292), (3003, 3003, 175344058274644822922), (3004, 3004, 175345058554462839013), (3005, 3005, 175346068844801168228), (3006, 3006, 175347089245920296644), (3007, 3007, 175348119859086438449), (3008, 3008, 175349160786581656065), (3009, 3009, 175350212131714082733), (3010, 3010, 175351273998828248617), (3011, 3011, 175352346493315511484), (3012, 3012, 175353429721624593038), (3013, 3013, 175354523791272221980), (3014, 3014, 175355628810853884904), (3015, 3015, 175356744890054686122), (3016, 3016, 175357872139660317544), (3017, 3017, 175359010671568139742), (3018, 3018, 175360160598798375335), (3019, 3019, 175361322035505415858), (3020, 3020, 175362495096989243264), (3021, 3021, 175363679899706967263), (3022, 3022, 175364876561284479661), (3023, 3023, 175366085200528226921), (3024, 3024, 175367305937437102156), (3025, 3025, 175368538893214457780), (3026, 3026, 175369784190280240065), (3027, 3027, 175371041952283246847), (3028, 3028, 175372312304113509671), (3029, 3029, 175373595371914801625), (3030, 3030, 175374891283097272194), (3031, 3031, 175376200166350210406), (3032, 3032, 175377522151654937631), (3033, 3033, 175378857370297831328), (3034, 3034, 175380205954883481133), (3035, 3035, 175381568039347978619), (3036, 3036, 175382943758972342126), (3037, 3037, 175384333250396078055), (3038, 3038, 175385736651630880022), (3039, 3039, 175387154102074467314), (3040, 3040, 175388585742524564071), (3041, 3041, 175390031715193020662), (3042, 3042, 175391492163720078712), (3043, 3043, 175392967233188781272), (3044, 3044, 175394457070139529645), (3045, 3045, 175395961822584788358), (3046, 3046, 175397481640023939844), (3047, 3047, 175399016673458290364), (3048, 3048, 175400567075406228746), (3049, 3049, 175402132999918539520), (3050, 3050, 175403714602593872052), (3051, 3051, 175405312040594367294), (3052, 3052, 175406925472661443784), (3053, 3053, 175408555059131744554), (3054, 3054, 175410200961953246604), (3055, 3055, 175411863344701534650), (3056, 3056, 175413542372596240830), (3057, 3057, 175415238212517652111), (3058, 3058, 175416951033023487136), (3059, 3059, 175418681004365844257), (3060, 3060, 175420428298508322570), (3061, 3061, 175422193089143317713), (3062, 3062, 175423975551709494271), (3063, 3063, 175425775863409436631), (3064, 3064, 175427594203227480123), (3065, 3065, 175429430751947724349), (3066, 3066, 175431285692172230590), (3067, 3067, 175433159208339405214), (3068, 3068, 175435051486742571023), (3069, 3069, 175436962715548728508), (3070, 3070, 175438893084817508980), (3071, 3071, 175440842786520321614), (3072, 3072, 175442812014559696387), (3073, 3073, 175444800964788825007), (3074, 3074, 175446809835031301866), (3075, 3075, 175448838825101067134), (3076, 3076, 175450888136822554103), (3077, 3077, 175452957974051042916), (3078, 3078, 175455048542693222856), (3079, 3079, 175457160050727965367), (3080, 3080, 175459292708227310037), (3081, 3081, 175461446727377665751), (3082, 3082, 175463622322501229306), (3083, 3083, 175465819710077623740), (3084, 3084, 175468039108765758711), (3085, 3085, 175470280739425915241), (3086, 3086, 175472544825142057199), (3087, 3087, 175474831591244371898), (3088, 3088, 175477141265332042227), (3089, 3089, 175479474077296252758), (3090, 3090, 175481830259343432278), (3091, 3091, 175484210046018735265), (3092, 3092, 175486613674229764806), (3093, 3093, 175489041383270539516), (3094, 3094, 175491493414845707036), (3095, 3095, 175493970013095006710), (3096, 3096, 175496471424617984075), (3097, 3097, 175498997898498959837), (3098, 3098, 175501549686332256017), (3099, 3099, 175504127042247681983), (3100, 3100, 175506730222936283146), (3101, 3101, 175509359487676355075), (3102, 3102, 175512015098359725866), (3103, 3103, 175514697319518309603), (3104, 3104, 175517406418350933788), (3105, 3105, 175520142664750443658), (3106, 3106, 175522906331331086319), (3107, 3107, 175525697693456177690), (3108, 3108, 175528517029266055250), (3109, 3109, 175531364619706319640), (3110, 3110, 175534240748556368190), (3111, 3111, 175537145702458223499), (3112, 3112, 175540079770945660187), (3113, 3113, 175543043246473633032), (3114, 3114, 175546036424448009689), (3115, 3115, 175549059603255611246), (3116, 3116, 175552113084294563926), (3117, 3117, 175555197172004965243), (3118, 3118, 175558312173899867986), (3119, 3119, 175561458400596585442), (3120, 3120, 175564636165848321286), (3121, 3121, 175567845786576127635), (3122, 3122, 175571087582901194778), (3123, 3123, 175574361878177476150), (3124, 3124, 175577668999024652139), (3125, 3125, 175581009275361436395), (3126, 3126, 175584383040439228295), (3127, 3127, 175587790630876115315), (3128, 3128, 175591232386691229069), (3129, 3129, 175594708651339458825), (3130, 3130, 175598219771746526364), (3131, 3131, 175601766098344426072), (3132, 3132, 175605347985107234222), (3133, 3133, 175608965789587291428), (3134, 3134, 175612619872951762314), (3135, 3135, 175616310600019576476), (3136, 3136, 175620038339298754881), (3137, 3137, 175623803463024125861), (3138, 3138, 175627606347195434948), (3139, 3139, 175631447371615852821), (3140, 3140, 175635326919930885682), (3141, 3141, 175639245379667692448), (3142, 3142, 175643203142274813186), (3143, 3143, 175647200603162313257), (3144, 3144, 175651238161742347717), (3145, 3145, 175655316221470150544), (3146, 3146, 175659435189885453339), (3147, 3147, 175663595478654338188), (3148, 3148, 175667797503611529430), (3149, 3149, 175672041684803129135), (3150, 3150, 175676328446529801156), (3151, 3151, 175680658217390408663), (3152, 3152, 175685031430326110132), (3153, 3153, 175689448522664918837), (3154, 3154, 175693909936166730915), (3155, 3155, 175698416117068827173), (3156, 3156, 175702967516131853842), (3157, 3157, 175707564588686287561), (3158, 3158, 175712207794679389916), (3159, 3159, 175716897598722656949), (3160, 3160, 175721634470139769092), (3161, 3161, 175726418883015047070), (3162, 3162, 175731251316242419348), (3163, 3163, 175736132253574906816), (3164, 3164, 175741062183674630408), (3165, 3165, 175746041600163347493), (3166, 3166, 175751071001673522876), (3167, 3167, 175756150891899940371), (3168, 3168, 175761281779651860945), (3169, 3169, 175766464178905733526), (3170, 3170, 175771698608858464630), (3171, 3171, 175776985593981253039), (3172, 3172, 175782325664073995843), (3173, 3173, 175787719354320272217), (3174, 3174, 175793167205342911420), (3175, 3175, 175798669763260151526), (3176, 3176, 175804227579742395538), (3177, 3177, 175809841212069571562), (3178, 3178, 175815511223189103840), (3179, 3179, 175821238181774501500), (3180, 3180, 175827022662284571978), (3181, 3181, 175832865245023266145), (3182, 3182, 175838766516200162262), (3183, 3183, 175844727067991595975), (3184, 3184, 175850747498602443647), (3185, 3185, 175856828412328566417), (3186, 3186, 175862970419619922463), (3187, 3187, 175869174137144355052), (3188, 3188, 175875440187852064031), (3189, 3189, 175881769201040768533), (3190, 3190, 175888161812421568752), (3191, 3191, 175894618664185514740), (3192, 3192, 175901140405070890296), (3193, 3193, 175907727690431220089), (3194, 3194, 175914381182304008284), (3195, 3195, 175921101549480217035), (3196, 3196, 175927889467574493304), (3197, 3197, 175934745619096152593), (3198, 3198, 175941670693520928267), (3199, 3199, 175948665387363495256), (3200, 3200, 175955730404250777053), (3201, 3201, 175962866454996045010), (3202, 3202, 175970074257673819079), (3203, 3203, 175977354537695579230), (3204, 3204, 175984708027886296925), (3205, 3205, 175992135468561796132), (3206, 3206, 175999637607606953470), (3207, 3207, 176007215200554747241), (3208, 3208, 176014869010666165177), (3209, 3209, 176022599809010980899), (3210, 3210, 176030408374549409200), (3211, 3211, 176038295494214650375), (3212, 3212, 176046261962996333984), (3213, 3213, 176054308584024872560), (3214, 3214, 176062436168656735882), (3215, 3215, 176070645536560656620), (3216, 3216, 176078937515804778255), (3217, 3217, 176087312942944756346), (3218, 3218, 176095772663112824350), (3219, 3219, 176104317530107835351), (3220, 3220, 176112948406486291201), (3221, 3221, 176121666163654370722), (3222, 3222, 176130471681960968793), (3223, 3223, 176139365850791758261), (3224, 3224, 176148349568664286825), (3225, 3225, 176157423743324121149), (3226, 3226, 176166589291842050674), (3227, 3227, 176175847140712363709), (3228, 3228, 176185198225952208614), (3229, 3229, 176194643493202052987), (3230, 3230, 176204183897827254007), (3231, 3231, 176213820405020753201), (3232, 3232, 176223553989906909139), (3233, 3233, 176233385637646481685), (3234, 3234, 176243316343542781657), (3235, 3235, 176253347113148999925), (3236, 3236, 176263478962376730151), (3237, 3237, 176273712917605699586), (3238, 3238, 176284050015794722526), (3239, 3239, 176294491304593891222), (3240, 3240, 176305037842458019256), (3241, 3241, 176315690698761352583), (3242, 3242, 176326450953913563659), (3243, 3243, 176337319699477044270), (3244, 3244, 176348298038285512917), (3245, 3245, 176359387084563952808), (3246, 3246, 176370587964049896734), (3247, 3247, 176381901814116075331), (3248, 3248, 176393329783894445470), (3249, 3249, 176404873034401615726), (3250, 3250, 176416532738665686140), (3251, 3251, 176428310081854519689), (3252, 3252, 176440206261405463176), (3253, 3253, 176452222487156535437), (3254, 3254, 176464359981479101075), (3255, 3255, 176476619979412048120), (3256, 3256, 176489003728797488349), (3257, 3257, 176501512490417999182), (3258, 3258, 176514147538135426406), (3259, 3259, 176526910159031267210), (3260, 3260, 176539801653548653310), (3261, 3261, 176552823335635954200), (3262, 3262, 176565976532892020891), (3263, 3263, 176579262586713090746), (3264, 3264, 176592682852441374337), (3265, 3265, 176606238699515345557), (3266, 3266, 176619931511621756492), (3267, 3267, 176633762686849398910), (3268, 3268, 176647733637844634500), (3269, 3269, 176661845791968716341), (3270, 3270, 176676100591456924388), (3271, 3271, 176690499493579538108), (3272, 3272, 176705043970804669716), (3273, 3273, 176719735510962981822), (3274, 3274, 176734575617414313637), (3275, 3275, 176749565809216240231), (3276, 3276, 176764707621294589721), (3277, 3277, 176780002604615943600), (3278, 3278, 176795452326362145806), (3279, 3279, 176811058370106846520), (3280, 3280, 176826822335994107028), (3281, 3281, 176842745840919092419), (3282, 3282, 176858830518710879242), (3283, 3283, 176875078020317405694), (3284, 3284, 176891490013992592275), (3285, 3285, 176908068185485661306), (3286, 3286, 176924814238232684103), (3287, 3287, 176941729893550385039), (3288, 3288, 176958816890832232169), (3289, 3289, 176976076987746844545), (3290, 3290, 176993511960438746782), (3291, 3291, 177011123603731501919), (3292, 3292, 177028913731333254090), (3293, 3293, 177046884176044712977), (3294, 3294, 177065036789969612531), (3295, 3295, 177083373444727676919), (3296, 3296, 177101896031670127182), (3297, 3297, 177120606462097762584), (3298, 3298, 177139506667481651155), (3299, 3299, 177158598599686464483), (3300, 3300, 177177884231196492320), (3301, 3301, 177197365555344373143), (3302, 3302, 177217044586542577352), (3303, 3303, 177236923360517680378), (3304, 3304, 177257003934547463524), (3305, 3305, 177277288387700880987), (3306, 3306, 177297778821080932083), (3307, 3307, 177318477358070478321), (3308, 3308, 177339386144581045588), (3309, 3309, 177360507349304652357), (3310, 3310, 177381843163968705441), (3311, 3311, 177403395803594005526), (3312, 3312, 177425167506755905316), (3313, 3313, 177447160535848663878), (3314, 3314, 177469377177353041400), (3315, 3315, 177491819742107179340), (3316, 3316, 177514490565580811612), (3317, 3317, 177537392008152853224), (3318, 3318, 177560526455392413504), (3319, 3319, 177583896318343281833), (3320, 3320, 177607504033811934544), (3321, 3321, 177631352064659112466), (3322, 3322, 177655442900095019374), (3323, 3323, 177679779055978192423), (3324, 3324, 177704363075118096487), (3325, 3325, 177729197527581495163), (3326, 3326, 177754285011002652056), (3327, 3327, 177779628150897416854), (3328, 3328, 177805229600981251592), (3329, 3329, 177831092043491253405), (3330, 3330, 177857218189512231020), (3331, 3331, 177883610779306893157), (3332, 3332, 177910272582650208010), (3333, 3333, 177937206399167993911), (3334, 3334, 177964415058679802336), (3335, 3335, 177991901421546155391), (3336, 3336, 178019668379020200973), (3337, 3337, 178047718853603849857), (3338, 3338, 178076055799408460044), (3339, 3339, 178104682202520134794), (3340, 3340, 178133601081369701901), (3341, 3341, 178162815487107442902), (3342, 3342, 178192328503982642081), (3343, 3343, 178222143249728026309), (3344, 3344, 178252262875949167981), (3345, 3345, 178282690568518924541), (3346, 3346, 178313429547976989329), (3347, 3347, 178344483069934629797), (3348, 3348, 178375854425484690408), (3349, 3349, 178407546941616938901), (3350, 3350, 178439563981638835936), (3351, 3351, 178471908945601809537), (3352, 3352, 178504585270733117139), (3353, 3353, 178537596431873379522), (3354, 3354, 178570945941919872338), (3355, 3355, 178604637352275662465), (3356, 3356, 178638674253304677953), (3357, 3357, 178673060274792801841), (3358, 3358, 178707799086415081771), (3359, 3359, 178742894398209148892), (3360, 3360, 178778349961054941240), (3361, 3361, 178814169567160828427), (3362, 3362, 178850357050556236220), (3363, 3363, 178886916287590871329), (3364, 3364, 178923851197440648522), (3365, 3365, 178961165742620423978), (3366, 3366, 178998863929503640710), (3367, 3367, 179036949808848993711), (3368, 3368, 179075427476334224491), (3369, 3369, 179114301073097156579), (3370, 3370, 179153574786284085640), (3371, 3371, 179193252849605639871), (3372, 3372, 179233339543900228461), (3373, 3373, 179273839197705198040), (3374, 3374, 179314756187835819227), (3375, 3375, 179356094939972227618), (3376, 3376, 179397859929254445822), (3377, 3377, 179440055680885615515), (3378, 3378, 179482686770743570793), (3379, 3379, 179525757826000886592), (3380, 3380, 179569273525753538368), (3381, 3381, 179613238601658311777), (3382, 3382, 179657657838579103662), (3383, 3383, 179702536075242258288), (3384, 3384, 179747878204901085451), (3385, 3385, 179793689176009709824), (3386, 3386, 179839973992906403711), (3387, 3387, 179886737716506558228), (3388, 3388, 179933985465005450858), (3389, 3389, 179981722414590970291), (3390, 3390, 180029953800166462538), (3391, 3391, 180078684916083865363), (3392, 3392, 180127921116887301310), (3393, 3393, 180177667818067302792), (3394, 3394, 180227930496825846061), (3395, 3395, 180278714692852374235), (3396, 3396, 180330026009110993016), (3397, 3397, 180381870112639026280), (3398, 3398, 180434252735357122303), (3399, 3399, 180487179674891105076), (3400, 3400, 180540656795405768942), (3401, 3401, 180594690028450818607), (3402, 3402, 180649285373819160519), (3403, 3403, 180704448900417755622), (3404, 3404, 180760186747151247599), (3405, 3405, 180816505123818584889), (3406, 3406, 180873410312022859064), (3407, 3407, 180930908666094586531), (3408, 3408, 180989006614028664977), (3409, 3409, 181047710658435240574), (3410, 3410, 181107027377504726606), (3411, 3411, 181166963425987218985), (3412, 3412, 181227525536186558977), (3413, 3413, 181288720518969298477), (3414, 3414, 181350555264788828253), (3415, 3415, 181413036744724934813), (3416, 3416, 181476172011539056860), (3417, 3417, 181539968200745517788), (3418, 3418, 181604432531699016202), (3419, 3419, 181669572308698662190), (3420, 3420, 181735394922108852874), (3421, 3421, 181801907849497286744), (3422, 3422, 181869118656790422376), (3423, 3423, 181937034999446693353), (3424, 3424, 182005664623647797616), (3425, 3425, 182075015367508385974), (3426, 3426, 182145095162304481162), (3427, 3427, 182215912033720965704), (3428, 3428, 182287474103118483775), (3429, 3429, 182359789588820109424), (3430, 3430, 182432866807418140818), (3431, 3431, 182506714175101387657), (3432, 3432, 182581340209003326526), (3433, 3433, 182656753528571506831), (3434, 3434, 182732962856958597921), (3435, 3435, 182809977022435476222), (3436, 3436, 182887804959826759609), (3437, 3437, 182966455711969204788), (3438, 3438, 183045938431193392280), (3439, 3439, 183126262380829132589), (3440, 3440, 183207436936735036302), (3441, 3441, 183289471588852700356), (3442, 3442, 183372375942785972287), (3443, 3443, 183456159721405764199), (3444, 3444, 183540832766480898274), (3445, 3445, 183626405040335475992), (3446, 3446, 183712886627533273856), (3447, 3447, 183800287736589679228), (3448, 3448, 183888618701711691029), (3449, 3449, 183977889984566521413), (3450, 3450, 184068112176079346179), (3451, 3451, 184159295998260763642), (3452, 3452, 184251452306064533881), (3453, 3453, 184344592089276182807), (3454, 3454, 184438726474433068342), (3455, 3455, 184533866726776519107), (3456, 3456, 184630024252236669499), (3457, 3457, 184727210599450628808), (3458, 3458, 184825437461814636169), (3459, 3459, 184924716679570867605), (3460, 3460, 185025060241929576255), (3461, 3461, 185126480289227262081), (3462, 3462, 185228989115121582907), (3463, 3463, 185332599168823734640), (3464, 3464, 185437323057369044835), (3465, 3465, 185543173547926540569), (3466, 3466, 185650163570148268759), (3467, 3467, 185758306218559164685), (3468, 3468, 185867614754988282517), (3469, 3469, 185978102611042220197), (3470, 3470, 186089783390621589958), (3471, 3471, 186202670872481405282), (3472, 3472, 186316779012836274990), (3473, 3473, 186432121948011315681), (3474, 3474, 186548713997139714668), (3475, 3475, 186666569664907897115), (3476, 3476, 186785703644349273132), (3477, 3477, 186906130819687563212), (3478, 3478, 187027866269230723647), (3479, 3479, 187150925268316517330), (3480, 3480, 187275323292310799819), (3481, 3481, 187401076019659615590), (3482, 3482, 187528199334996225120), (3483, 3483, 187656709332304209823), (3484, 3484, 187786622318137828960), (3485, 3485, 187917954814900830380), (3486, 3486, 188050723564184945507), (3487, 3487, 188184945530169328213), (3488, 3488, 188320637903082227267), (3489, 3489, 188457818102726212855), (3490, 3490, 188596503782068309320), (3491, 3491, 188736712830896418741), (3492, 3492, 188878463379543453315), (3493, 3493, 189021773802680628734), (3494, 3494, 189166662723181405893), (3495, 3495, 189313149016057604367), (3496, 3496, 189461251812469248129), (3497, 3497, 189610990503809742061), (3498, 3498, 189762384745868016865), (3499, 3499, 189915454463069320160), (3500, 3500, 190070219852796372725), (3501, 3501, 190226701389792651268), (3502, 3502, 190384919830649602533), (3503, 3503, 190544896218379638316), (3504, 3504, 190706651887076806833), (3505, 3505, 190870208466667083097), (3506, 3506, 191035587887750269418), (3507, 3507, 191202812386535546976), (3508, 3508, 191371904509872770600), (3509, 3509, 191542887120381651531), (3510, 3510, 191715783401681026985), (3511, 3511, 191890616863720470983), (3512, 3512, 192067411348216558006), (3513, 3513, 192246191034196149821), (3514, 3514, 192426980443649136202), (3515, 3515, 192609804447293122384), (3516, 3516, 192794688270452619942), (3517, 3517, 192981657499055363447), (3518, 3518, 193170738085748442801), (3519, 3519, 193361956356137010578), (3520, 3520, 193555339015148395163), (3521, 3521, 193750913153524523955), (3522, 3522, 193948706254445636476), (3523, 3523, 194148746200288345018), (3524, 3524, 194351061279521180454), (3525, 3525, 194555680193740843170), (3526, 3526, 194762632064852463780), (3527, 3527, 194971946442397265482), (3528, 3528, 195183653311031109596), (3529, 3529, 195397783098157498196), (3530, 3530, 195614366681718702790), (3531, 3531, 195833435398148785825), (3532, 3532, 196055021050492382538), (3533, 3533, 196279155916693214367), (3534, 3534, 196505872758056411910), (3535, 3535, 196735204827888835365), (3536, 3536, 196967185880321693607), (3537, 3537, 197201850179319879654), (3538, 3538, 197439232507882560384), (3539, 3539, 197679368177439682048), (3540, 3540, 197922293037449180569), (3541, 3541, 198168043485199816883), (3542, 3542, 198416656475824692822), (3543, 3543, 198668169532530642421), (3544, 3544, 198922620757048837097), (3545, 3545, 199180048840312091172), (3546, 3546, 199440493073364506680), (3547, 3547, 199703993358509253655), (3548, 3548, 199970590220700444069), (3549, 3549, 200240324819185224687), (3550, 3550, 200513238959402386279), (3551, 3551, 200789375105143964209), (3552, 3552, 201068776390986488485), (3553, 3553, 201351486634998730177), (3554, 3554, 201637550351732985814), (3555, 3555, 201927012765507142183), (3556, 3556, 202219919823984971128), (3557, 3557, 202516318212062317607), (3558, 3558, 202816255366067064751), (3559, 3559, 203119779488280987086), (3560, 3560, 203426939561791837825), (3561, 3561, 203737785365684258289), (3562, 3562, 204052367490578347492), (3563, 3563, 204370737354524987900), (3564, 3564, 204692947219267289662), (3565, 3565, 205019050206877790505), (3566, 3566, 205349100316781332286), (3567, 3567, 205683152443173828217), (3568, 3568, 206021262392847437346), (3569, 3569, 206363486903432975335), (3570, 3570, 206709883662070713285), (3571, 3571, 207060511324521049664), (3572, 3572, 207415429534726884695), (3573, 3573, 207774698944839882239), (3574, 3574, 208138381235723171707), (3575, 3575, 208506539137943422229), (3576, 3576, 208879236453265613677), (3577, 3577, 209256538076664234669), (3578, 3578, 209638510018865056758), (3579, 3579, 210025219429432067262), (3580, 3580, 210416734620414591025), (3581, 3581, 210813125090570094405), (3582, 3582, 211214461550178643557), (3583, 3583, 211620815946465484084), (3584, 3584, 212032261489648721122), (3585, 3585, 212448872679629608449), (3586, 3586, 212870725333343502885), (3587, 3587, 213297896612790106892), (3588, 3588, 213730465053762208454), (3589, 3589, 214168510595292733884), (3590, 3590, 214612114609840556805), (3591, 3591, 215061359934236156154), (3592, 3592, 215516330901408888316), (3593, 3593, 215977113372918334410), (3594, 3594, 216443794772312904194), (3595, 3595, 216916464119339623895), (3596, 3596, 217395212065029807641), (3597, 3597, 217880130927686111911), (3598, 3598, 218371314729797300765), (3599, 3599, 218868859235907907549), (3600, 3600, 219372861991470867511), (3601, 3601, 219883422362712116522), (3602, 3602, 220400641577537105088), (3603, 3603, 220924622767510165387), (3604, 3604, 221455471010938693605), (3605, 3605, 221993293377095171647), (3606, 3606, 222538198971611153025), (3607, 3607, 223090298983078478805), (3608, 3608, 223649706730894172564), (3609, 3609, 224216537714386690103), (3610, 3610, 224790909663262471883), (3611, 3611, 225372942589413065668), (3612, 3612, 225962758840124455554), (3613, 3613, 226560483152731653504), (3614, 3614, 227166242710763082668), (3615, 3615, 227780167201620810459), (3616, 3616, 228402388875844275747), (3617, 3617, 229033042608006801045), (3618, 3618, 229672265959295889688), (3619, 3619, 230320199241830082312), (3620, 3620, 230976985584766989136), (3621, 3621, 231642771002259027511), (3622, 3622, 232317704463315380793), (3623, 3623, 233001937963630758043), (3624, 3624, 233695626599443677416), (3625, 3625, 234398928643489222966), (3626, 3626, 235112005623113538269), (3627, 3627, 235835022400619724639), (3628, 3628, 236568147255917310505), (3629, 3629, 237311551971550055893), (3630, 3630, 238065411920179556008), (3631, 3631, 238829906154604915210), (3632, 3632, 239605217500401681722), (3633, 3633, 240391532651266269148), (3634, 3634, 241189042267155248303), (3635, 3635, 241997941075312177349), (3636, 3636, 242818427974278055297), (3637, 3637, 243650706140985039435), (3638, 3638, 244494983141036767237), (3639, 3639, 245351471042282474272), (3640, 3640, 246220386531796108120), (3641, 3641, 247101951036375811488), (3642, 3642, 247996390846683492845), (3643, 3643, 248903937245148727695), (3644, 3644, 249824826637765946216), (3645, 3645, 250759300689918771784), (3646, 3646, 251707606466370488869), (3647, 3647, 252669996575564947144), (3648, 3648, 253646729318387761276), (3649, 3649, 254638068841543452932), (3650, 3650, 255644285295710213842), (3651, 3651, 256665654998640257622), (3652, 3652, 257702460603380285282), (3653, 3653, 258754991271793427433), (3654, 3654, 259823542853571158171), (3655, 3655, 260908418070931115272), (3656, 3656, 262009926709204522944), (3657, 3657, 263128385813525012327), (3658, 3658, 264264119891839086835), (3659, 3659, 265417461124467301328), (3660, 3660, 266588749580454433282), (3661, 3661, 267778333440956539273), (3662, 3662, 268986569229922830546), (3663, 3663, 270213822052340787627), (3664, 3664, 271460465840323887361), (3665, 3665, 272726883607332759081), (3666, 3666, 274013467710832543457), (3667, 3667, 275320620123701723186), (3668, 3668, 276648752714720755202), (3669, 3669, 277998287538482487357), (3670, 3670, 279369657135080617703), (3671, 3671, 280763304839947382363), (3672, 3672, 282179685104227270812), (3673, 3673, 283619263826089899441), (3674, 3674, 285082518693402261360), (3675, 3675, 286569939538198450440), (3676, 3676, 288082028703403670549), (3677, 3677, 289619301422288928785), (3678, 3678, 291182286211153318735), (3679, 3679, 292771525275752273108), (3680, 3680, 294387574932012653868), (3681, 3681, 296031006041599104362), (3682, 3682, 297702404462920766722), (3683, 3683, 299402371518193327166), (3684, 3684, 301131524477198452771), (3685, 3685, 302890497058411090617), (3686, 3686, 304679939948194882032), (3687, 3687, 306500521338797173204), (3688, 3688, 308352927485907854666), (3689, 3689, 310237863286580616731), (3690, 3690, 312156052878351250740), (3691, 3691, 314108240260425446990), (3692, 3692, 316095189937848234361), (3693, 3693, 318117687589608874529), (3694, 3694, 320176540761678771487), (3695, 3695, 322272579586025897358), (3696, 3696, 324406657526697487117), (3697, 3697, 326579652154113443823), (3698, 3698, 328792465948766155560), (3699, 3699, 331046027135578396581), (3700, 3700, 333341290550229817729), (3701, 3701, 335679238538824383212), (3702, 3702, 338060881892336150147), (3703, 3703, 340487260817339191519), (3704, 3704, 342959445944599420856), (3705, 3705, 345478539377181787636), (3706, 3706, 348045675779805988001), (3707, 3707, 350662023511267700429), (3708, 3708, 353328785801830648774), (3709, 3709, 356047201977587768526), (3710, 3710, 358818548733887674423), (3711, 3711, 361644141460025783717), (3712, 3712, 364525335617508141746), (3713, 3713, 367463528174310546415), (3714, 3714, 370460159097676316814), (3715, 3715, 373516712908123361226), (3716, 3716, 376634720297465456517), (3717, 3717, 379815759813794263959), (3718, 3718, 383061459616518011587), (3719, 3719, 386373499304710433405), (3720, 3720, 389753611822189963988), (3721, 3721, 393203585442924867648), (3722, 3722, 396725265840545492428), (3723, 3723, 400320558245940774898), (3724, 3724, 403991429697123114730), (3725, 3725, 407739911385764462104), (3726, 3726, 411568101105037634101), (3727, 3727, 415478165803641263268), (3728, 3728, 419472344251145197972), (3729, 3729, 423552949820066489291), (3730, 3730, 427722373390375240123), (3731, 3731, 431983086382435547887), (3732, 3732, 436337643924710597853), (3733, 3733, 440788688162903785843), (3734, 3734, 445338951717570769181), (3735, 3735, 449991261297621846884), (3736, 3736, 454748541477541425590), (3737, 3737, 459613818646583001404), (3738, 3738, 464590225138655645420), (3739, 3739, 469681003552103095561), (3740, 3740, 474889511269091019214), (3741, 3741, 480219225184863733576), (3742, 3742, 485673746657710701541), (3743, 3743, 491256806691097651299), (3744, 3744, 496972271360069543328), (3745, 3745, 502824147494725340497), (3746, 3746, 508816588634300315554), (3747, 3747, 514953901266173337143), (3748, 3748, 521240551364947298980), (3749, 3749, 527681171247633907634), (3750, 3750, 534280566761912972205), (3751, 3751, 541043724825434951800), (3752, 3752, 547975821335197899140), (3753, 3753, 555082229467160475245), (3754, 3754, 562368528387456107683), (3755, 3755, 569840512397854677814), (3756, 3756, 577504200539482780158), (3757, 3757, 585365846680267433757), (3758, 3758, 593431950113117411641), (3759, 3759, 601709266693507832757), (3760, 3760, 610204820546894582144), (3761, 3761, 618925916378263291250), (3762, 3762, 627880152418121416900), (3763, 3763, 637075434041380442980), (3764, 3764, 646519988097858126632), (3765, 3765, 656222377995568505671), (3766, 3766, 666191519580571374325), (3767, 3767, 676436697859935298988), (3768, 3768, 686967584617342116648), (3769, 3769, 697794256974040400742), (3770, 3770, 708927216951255876192), (3771, 3771, 720377412093804713946), (3772, 3772, 732156257218548847322), (3773, 3773, 744275657355500166197), (3774, 3774, 756748031953843446953), (3775, 3775, 769586340429928632575), (3776, 3776, 782804109139405879443), (3777, 3777, 796415459861167907958), (3778, 3778, 810435139886652059585), (3779, 3779, 824878553814369840420), (3780, 3780, 839761797156307934005), (3781, 3781, 855101691870117775818), (3782, 3782, 870915823938819894593), (3783, 3783, 887222583128136717564), (3784, 3784, 904041205060579357527), (3785, 3785, 921391815755099890979), (3786, 3786, 939295478791534883220), (3787, 3787, 957774245270267128202), (3788, 3788, 976851206749584503687), (3789, 3789, 996550551356186756801), (3790, 3790, 1016897623278258201802), (3791, 3791, 1037918985865568563897), (3792, 3792, 1059642488577274542873), (3793, 3793, 1082097338035567936064), (3794, 3794, 1105314173462157756750), (3795, 3795, 1129325146794898486868), (3796, 3796, 1154164007803809440619), (3797, 3797, 1179866194549407441583), (3798, 3798, 1206468929551845175986), (3799, 3799, 1234011322066972692381), (3800, 3800, 1262534476895296348342), (3801, 3801, 1292081610182091019993), (3802, 3802, 1322698172701838309318), (3803, 3803, 1354431981157946014831), (3804, 3804, 1387333358069603877980), (3805, 3805, 1421455280861922689526), (3806, 3806, 1456853540823489174845), (3807, 3807, 1493586912647477009975), (3808, 3808, 1531717335328845420577), (3809, 3809, 1571310105251326024252), (3810, 3810, 1612434082364278672114), (3811, 3811, 1655161910421562484029), (3812, 3812, 1699570252332839433891), (3813, 3813, 1745740041762775735654), (3814, 3814, 1793756752206057757739), (3815, 3815, 1843710684866682722069), (3816, 3816, 1895697276779376520975), (3817, 3817, 1949817430730063245156), (3818, 3818, 2006177868661978125270), (3819, 3819, 2064891510395284014902), (3820, 3820, 2126077879642029293111), (3821, 3821, 2189863539466192525986), (3822, 3822, 2256382559521741210917), (3823, 3823, 2325777017601571084688), (3824, 3824, 2398197538248524229871), (3825, 3825, 2473803871418213396628), (3826, 3826, 2552765514444099359746), (3827, 3827, 2635262380840379186429), (3828, 3840, 2698500957556355349776), (3841, 3841, 2691468185677134702154), (3842, 3842, 2664819985818945249657), (3843, 3843, 2638435629523708167978), (3844, 3844, 2612312504478918978196), (3845, 3845, 2586448024236553443758), (3846, 3846, 2560839627956983607681), (3847, 3847, 2535484780155429314536), (3848, 3848, 2510380970450920113402), (3849, 3849, 2485525713317742686537), (3850, 3850, 2460916547839349194591), (3851, 3851, 2436551037464702172862), (3852, 3852, 2412426769767031854319), (3853, 3853, 2388541356204982033979), (3854, 3854, 2364892431886120825722), (3855, 3855, 2341477655332792896754), (3856, 3856, 2318294708250289996787), (3857, 3857, 2295341295297316828501), (3858, 3858, 2272615143858729533170), (3859, 3859, 2250114003820524290267), (3860, 3860, 2227835647347053752740), (3861, 3861, 2205777868660449260138), (3862, 3862, 2183938483822226990236), (3863, 3863, 2162315330517056425976), (3864, 3864, 2140906267838669728689), (3865, 3865, 2119709176077890820485), (3866, 3866, 2098721956512763188599), (3867, 3867, 2077942531200755632276), (3868, 3868, 2057368842773025378491), (3869, 3869, 2036998854230718196526), (3870, 3870, 2016830548743285343095), (3871, 3871, 1996861929448797369401), (3872, 3872, 1977091019256235019209), (3873, 3873, 1957515860649737642781), (3874, 3874, 1938134515494789745328), (3875, 3875, 1918945064846326480522), (3876, 3876, 1899945608758739089626), (3877, 3877, 1881134266097761474877), (3878, 3878, 1862509174354219282057), (3879, 3879, 1844068489459623051541), (3880, 3880, 1825810385603587179744), (3881, 3881, 1807733055053056613608), (3882, 3882, 1789834707973323379810), (3883, 3883, 1772113572250815227534), (3884, 3884, 1754567893317638839143), (3885, 3885, 1737195933977860236775), (3886, 3886, 1719995974235505184926), (3887, 3887, 1702966311124262559333), (3888, 3888, 1686105258538873821121), (3889, 3889, 1669411147068191902100), (3890, 3890, 1652882323829892972377), (3891, 3891, 1636517152306824725125), (3892, 3892, 1620314012184974975372), (3893, 3893, 1604271299193044530071), (3894, 3894, 1588387424943608445615), (3895, 3895, 1572660816775849946153), (3896, 3896, 1557089917599851431835), (3897, 3897, 1541673185742427160233), (3898, 3898, 1526409094794482336864), (3899, 3899, 1511296133459883501846), (3900, 3900, 1496332805405825249352), (3901, 3901, 1481517629114678464705), (3902, 3902, 1466849137737305410599), (3903, 3903, 1452325878947827139207), (3904, 3904, 1437946414799828850700), (3905, 3905, 1423709321583988961089), (3906, 3906, 1409613189687117783257), (3907, 3907, 1395656623452591864610), (3908, 3908, 1381838241042170162981), (3909, 3909, 1368156674299178379189), (3910, 3910, 1354610568613047900187), (3911, 3911, 1341198582785195940779), (3912, 3912, 1327919388896233604732), (3913, 3913, 1314771672174488717556), (3914, 3914, 1301754130865830413422), (3915, 3915, 1288865476104782587547), (3916, 3916, 1276104431786913453016), (3917, 3917, 1263469734442488567343), (3918, 3918, 1250960133111374819151), (3919, 3919, 1238574389219182989259), (3920, 3920, 1226311276454636623029), (3921, 3921, 1214169580648155072306), (3922, 3922, 1202148099651638685451), (3923, 3923, 1190245643219444243021), (3924, 3924, 1178461032890538854476), (3925, 3925, 1166793101871820647996), (3926, 3926, 1155240694922594700986), (3927, 3927, 1143802668240192773254), (3928, 3928, 1132477889346725518073), (3929, 3929, 1121265236976955958488), (3930, 3930, 1110163600967283127216), (3931, 3931, 1099171882145824878432), (3932, 3932, 1088288992223588988546), (3933, 3933, 1077513853686721770838), (3934, 3934, 1066845399689823535483), (3935, 3935, 1056282573950320332161), (3936, 3936, 1045824330643881516991), (3937, 3937, 1035469634300872789100), (3938, 3938, 1025217459703834444654), (3939, 3939, 1015066791785974697677), (3940, 3940, 1005016625530668017502), (3941, 3941, 995065965871948532180), (3942, 3942, 985213827595988645723), (3943, 3943, 975459235243553114577), (3944, 3944, 965801223013418925324), (3945, 3945, 956238834666751411212), (3946, 3946, 946771123432427139814), (3947, 3947, 937397151913294197836), (3948, 3948, 928115991993360591916), (3949, 3949, 918926724745901576155), (3950, 3950, 909828440342476808074), (3951, 3951, 900820237962848324826), (3952, 3952, 891901225705790420620), (3953, 3953, 883070520500782594673), (3954, 3954, 874327248020576826409), (3955, 3955, 865670542594630521197), (3956, 3956, 857099547123396555640), (3957, 3957, 848613412993461936278), (3958, 3958, 840211299993526669582), (3959, 3959, 831892376231214524339), (3960, 3960, 823655818050707449840), (3961, 3961, 815500809951195494891), (3962, 3962, 807426544506134153358), (3963, 3963, 799432222283301141938), (3964, 3964, 791517051765644694988), (3965, 3965, 783680249272915539592), (3966, 3966, 775921038884074791676), (3967, 3967, 768238652360470090768), (3968, 3968, 760632329069772367097), (3969, 3969, 753101315910665709997), (3970, 3970, 745644867238282881185), (3971, 3971, 738262244790379090282), (3972, 3972, 730952717614236723052), (3973, 3973, 723715561994293785200), (3974, 3974, 716550061380488896238), (3975, 3975, 709455506317315738849), (3976, 3976, 702431194373579939455), (3977, 3977, 695476430072851425203), (3978, 3978, 688590524824605371488), (3979, 3979, 681772796856044922265), (3980, 3980, 675022571144598932936), (3981, 3981, 668339179351088052412), (3982, 3982, 661721959753552527140), (3983, 3983, 655170257181735175386), (3984, 3984, 648683422952213044937), (3985, 3985, 642260814804171331621), (3986, 3986, 635901796835813199624), (3987, 3987, 629605739441399207549), (3988, 3988, 623372019248910106484), (3989, 3989, 617200019058326838103), (3990, 3990, 611089127780521621884), (3991, 3991, 605038740376754081074), (3992, 3992, 599048257798766416905), (3993, 3993, 593117086929471699905), (3994, 3994, 587244640524229405847), (3995, 3995, 581430337152702382027), (3996, 3996, 575673601141289487155), (3997, 3997, 569973862516128205104), (3998, 3998, 564330556946661589212), (3999, 3999, 558743125689763949715), (4000, 4000, 553211015534419752193), (4001, 4001, 547733678746950249696), (4002, 4002, 542310573016782425442), (4003, 4003, 536941161402754876675), (4004, 4004, 531624912279955323440), (4005, 4005, 526361299287084478654), (4006, 4006, 521149801274341067974), (4007, 4007, 515989902251822839578), (4008, 4008, 510881091338438455028), (4009, 4009, 505822862711325202998), (4010, 4010, 500814715555767527721), (4011, 4011, 495856154015611413585), (4012, 4012, 490946687144169716421), (4013, 4013, 486085828855613580615), (4014, 4014, 481273097876845129322), (4015, 4015, 476508017699846662695), (4016, 4016, 471790116534501646232), (4017, 4017, 467118927261882818052), (4018, 4018, 462493987388002790150), (4019, 4019, 457914838998022564505), (4020, 4020, 453381028710913430203), (4021, 4021, 448892107634567752676), (4022, 4022, 444447631321354210571), (4023, 4023, 440047159724113079773), (4024, 4024, 435690257152587207696), (4025, 4025, 431376492230284364056), (4026, 4026, 427105437851766697085), (4027, 4027, 422876671140363066420), (4028, 4028, 418689773406300065763), (4029, 4029, 414544330105247589864), (4030, 4030, 410439930797274841450), (4031, 4031, 406376169106212714307), (4032, 4032, 402352642679418529017), (4033, 4033, 398368953147939137640), (4034, 4034, 394424706087068453109), (4035, 4035, 390519510977295498128), (4036, 4036, 386652981165639107057), (4037, 4037, 382824733827365452532), (4038, 4038, 379034389928084606467), (4039, 4039, 375281574186222382641), (4040, 4040, 371565915035863745189), (4041, 4041, 367887044589964104147), (4042, 4042, 364244598603924855592), (4043, 4043, 360638216439529559992), (4044, 4044, 357067541029237188111), (4045, 4045, 353532218840828899119), (4046, 4046, 350031899842404850613), (4047, 4047, 346566237467727574865), (4048, 4048, 343134888581908489965), (4049, 4049, 339737513447434148480), (4050, 4050, 336373775690528859881), (4051, 4051, 333043342267850356318), (4052, 4052, 329745883433515204275), (4053, 4053, 326481072706450697302), (4054, 4054, 323248586838069997329), (4055, 4055, 320048105780267324088), (4056, 4056, 316879312653730023850), (4057, 4057, 313741893716564380049), (4058, 4058, 310635538333232059455), (4059, 4059, 307559938943794118272), (4060, 4060, 304514791033459523042), (4061, 4061, 301499793102435171328), (4062, 4062, 298514646636074427058), (4063, 4063, 295559056075321214909), (4064, 4064, 292632728787446747434), (4065, 4065, 289735375037075987559), (4066, 4066, 286866707957500977781), (4067, 4067, 284026443522278195823), (4068, 4068, 281214300517107124577), (4069, 4069, 278430000511987252056), (4070, 4070, 275673267833650744610), (4071, 4071, 272943829538268063971), (4072, 4072, 270241415384423825713), (4073, 4073, 267565757806360223479), (4074, 4074, 264916591887485369781), (4075, 4075, 262293655334143930476), (4076, 4076, 259696688449647455917), (4077, 4077, 257125434108561837542), (4078, 4078, 254579637731249344101), (4079, 4079, 252059047258662716931), (4080, 4080, 249563413127388828645), (4081, 4081, 247092488244939434302), (4082, 4082, 244646027965286568616), (4083, 4083, 242223790064640166946), (4084, 4084, 239825534717465511828), (4085, 4085, 237451024472738130523), (4086, 4086, 235100024230433792597), (4087, 4087, 232772301218251279799), (4088, 4088, 230467624968565623563), (4089, 4089, 228185767295609528280), (4090, 4090, 225926502272880721070), (4091, 4091, 223689606210772991158), (4092, 4092, 221474857634428704117), (4093, 4093, 219282037261810598136), (4094, 4094, 217110927981990691223), (4095, 4095, 214961314833654149726), (4096, 4096, 212832984983815989828), (4097, 4097, 210725727706748504780), (4098, 4098, 208639334363117331465), (4099, 4099, 206573598379324090560), (4100, 4100, 204528315227053555010), (4101, 4101, 202503282403023321792), (4102, 4102, 200498299408933981972), (4103, 4103, 198513167731617803933), (4104, 4104, 196547690823383964290), (4105, 4105, 194601674082558380485), (4106, 4106, 192674924834216218302), (4107, 4107, 190767252311105166636), (4108, 4108, 188878467634757590728), (4109, 4109, 187008383796789693790), (4110, 4110, 185156815640385835436), (4111, 4111, 183323579841966173699), (4112, 4112, 181508494893035815544), (4113, 4113, 179711381082213678756), (4114, 4114, 177932060477439285897), (4115, 4115, 176170356908355728611), (4116, 4116, 174426095948867058031), (4117, 4117, 172699104899868374288), (4118, 4118, 170989212772146905235), (4119, 4119, 169296250269452381421), (4120, 4120, 167620049771735031110), (4121, 4121, 165960445318549535753), (4122, 4122, 164317272592623302725), (4123, 4123, 162690368903587428441), (4124, 4124, 161079573171868741031), (4125, 4125, 159484725912741327753), (4126, 4126, 157905669220535968072), (4127, 4127, 156342246753005908983), (4128, 4128, 154794303715847434636), (4129, 4129, 153261686847373697660), (4130, 4130, 151744244403340294713), (4131, 4131, 150241826141921083874), (4132, 4132, 148754283308832756311), (4133, 4133, 147281468622606689417), (4134, 4134, 145823236260006623185), (4135, 4135, 144379441841590716024), (4136, 4136, 142949942417416550519), (4137, 4137, 141534596452887673781), (4138, 4138, 140133263814740271071), (4139, 4139, 138745805757168585219), (4140, 4140, 137372084908087708137), (4141, 4141, 136011965255532384294), (4142, 4142, 134665312134190479499), (4143, 4143, 133331992212069781682), (4144, 4144, 132011873477296813547), (4145, 4145, 130704825225046350047), (4146, 4146, 129410718044600346581), (4147, 4147, 128129423806534996615), (4148, 4148, 126860815650034650113), (4149, 4149, 125604767970331336746), (4150, 4150, 124361156406268650244), (4151, 4151, 123129857827988762617), (4152, 4152, 121910750324741349126), (4153, 4153, 120703713192813216957), (4154, 4154, 119508626923577442531), (4155, 4155, 118325373191660834189), (4156, 4156, 117153834843228548702), (4157, 4157, 115993895884384701686), (4158, 4158, 114845441469687823451), (4159, 4159, 113708357890780023219), (4160, 4160, 112582532565128735860), (4161, 4161, 111467854024879936495), (4162, 4162, 110364211905821719302), (4163, 4163, 109271496936457147824), (4164, 4164, 108189600927185294875), (4165, 4165, 107118416759589400867), (4166, 4166, 106057838375831089967), (4167, 4167, 105007760768149594027), (4168, 4168, 103968079968464944581), (4169, 4169, 102938693038084103545), (4170, 4170, 101919498057509013411), (4171, 4171, 100910394116345557833), (4172, 4172, 99911281303312433498), (4173, 4173, 98922060696348944057), (4174, 4174, 97942634352820736691), (4175, 4175, 96972905299822511575), (4176, 4176, 96012777524576744134), (4177, 4177, 95062155964927469439), (4178, 4178, 94120946499928187563), (4179, 4179, 93189055940522957984), (4180, 4180, 92266392020319760380), (4181, 4181, 91352863386455208297), (4182, 4182, 90448379590549711185), (4183, 4183, 89552851079752189292), (4184, 4184, 88666189187873454745), (4185, 4185, 87788306126607380935), (4186, 4186, 86919114976838991025), (4187, 4187, 86058529680038604975), (4188, 4188, 85206465029741193045), (4189, 4189, 84362836663110092124), (4190, 4190, 83527561052584249627), (4191, 4191, 82700555497608167948), (4192, 4192, 81881738116443730642), (4193, 4193, 81071027838063099645), (4194, 4194, 80268344394121880837), (4195, 4195, 79473608311011763205), (4196, 4196, 78686740901991844757), (4197, 4197, 77907664259397866096), (4198, 4198, 77136301246928580293), (4199, 4199, 76372575492008495340), (4200, 4200, 75616411378226233010), (4201, 4201, 74867734037847755455), (4202, 4202, 74126469344403718272), (4203, 4203, 73392543905350216111), (4204, 4204, 72665885054802194170), (4205, 4205, 71946420846338806109), (4206, 4206, 71234080045880006048), (4207, 4207, 70528792124633669355), (4208, 4208, 69830487252112543915), (4209, 4209, 69139096289220340510), (4210, 4210, 68454550781406277733), (4211, 4211, 67776782951887403696), (4212, 4212, 67105725694938023461), (4213, 4213, 66441312569245567784), (4214, 4214, 65783477791332245330), (4215, 4215, 65132156229041827060), (4216, 4216, 64487283395090917881), (4217, 4217, 63848795440684077110), (4218, 4218, 63216629149192155554), (4219, 4219, 62590721929893223321), (4220, 4220, 61971011811775468635), (4221, 4221, 61357437437401454094), (4222, 4222, 60749938056833122865), (4223, 4223, 60148453521616953332), (4224, 4224, 59552924278828666665), (4225, 4225, 58963291365176897688), (4226, 4226, 58379496401165245236), (4227, 4227, 57801481585312123996), (4228, 4228, 57229189688427845541), (4229, 4229, 56662564047948361921), (4230, 4230, 56101548562325110813), (4231, 4231, 55546087685470406746), (4232, 4232, 54996126421257828461), (4233, 4233, 54451610318077057882), (4234, 4234, 53912485463442631567), (4235, 4235, 53378698478656070858), (4236, 4236, 52850196513520862236), (4237, 4237, 52326927241109764590), (4238, 4238, 51808838852583925337), (4239, 4239, 51295880052063292412), (4240, 4240, 50788000051547814270), (4241, 4241, 50285148565888925020), (4242, 4242, 49787275807810816851), (4243, 4243, 49294332482981006783), (4244, 4244, 48806269785129709686), (4245, 4245, 48323039391217534343), (4246, 4246, 47844593456651024102), (4247, 4247, 47370884610545568418), (4248, 4248, 46901865951035216255), (4249, 4249, 46437491040628926985), (4250, 4250, 45977713901612798995), (4251, 4251, 45522489011497820788), (4252, 4252, 45071771298512693849), (4253, 4253, 44625516137141281039), (4254, 4254, 44183679343704238652), (4255, 4255, 43746217171984394705), (4256, 4256, 43313086308895440302), (4257, 4257, 42884243870193505250), (4258, 4258, 42459647396231193316), (4259, 4259, 42039254847753656749), (4260, 4260, 41623024601736293811), (4261, 4261, 41210915447263657238), (4262, 4262, 40802886581449165583), (4263, 4263, 40398897605395213448), (4264, 4264, 39998908520193280642), (4265, 4265, 39602879722963644200), (4266, 4266, 39210772002934301188), (4267, 4267, 38822546537558714047), (4268, 4268, 38438164888671994106), (4269, 4269, 38057588998685142680), (4270, 4270, 37680781186816972950), (4271, 4271, 37307704145363339555), (4272, 4272, 36938320936003306490), (4273, 4273, 36572594986141887614), (4274, 4274, 36210490085288997637), (4275, 4275, 35851970381474255086), (4276, 4276, 35497000377697282264), (4277, 4277, 35145544928413150756), (4278, 4278, 34797569236052624511), (4279, 4279, 34453038847576855951), (4280, 4280, 34111919651066194011), (4281, 4281, 33774177872342766348), (4282, 4282, 33439780071626501335), (4283, 4283, 33108693140224258747), (4284, 4284, 32780884297251741334), (4285, 4285, 32456321086387862707), (4286, 4286, 32134971372661250205), (4287, 4287, 31816803339268564559), (4288, 4288, 31501785484424321346), (4289, 4289, 31189886618241902322), (4290, 4290, 30881075859645447844), (4291, 4291, 30575322633312324598), (4292, 4292, 30272596666645865939), (4293, 4293, 29972867986778085088), (4294, 4294, 29676106917602064443), (4295, 4295, 29382284076833727172), (4296, 4296, 29091370373102700170), (4297, 4297, 28803337003071980366), (4298, 4298, 28518155448586119175), (4299, 4299, 28235797473847642747), (4300, 4300, 27956235122621428462), (4301, 4301, 27679440715466760854), (4302, 4302, 27405386846996792925), (4303, 4303, 27134046383165141510), (4304, 4304, 26865392458579348029), (4305, 4305, 26599398473840938643), (4306, 4306, 26336038092911820438), (4307, 4307, 26075285240506752909), (4308, 4308, 25817114099511636544), (4309, 4309, 25561499108427362915), (4310, 4310, 25308414958838973183), (4311, 4311, 25057836592909874439), (4312, 4312, 24809739200900865781), (4313, 4313, 24564098218713728496), (4314, 4314, 24320889325459137125), (4315, 4315, 24080088441048650618), (4316, 4316, 23841671723810545167), (4317, 4317, 23605615568129252640), (4318, 4318, 23371896602108170931), (4319, 4319, 23140491685255614783), (4320, 4320, 22911377906193678003), (4321, 4321, 22684532580389780201), (4322, 4322, 22459933247910673467), (4323, 4323, 22237557671198686601), (4324, 4324, 22017383832869986733), (4325, 4325, 21799389933534640330), (4326, 4326, 21583554389638257752), (4327, 4327, 21369855831325007676), (4328, 4328, 21158273100321789778), (4329, 4329, 20948785247843356216), (4330, 4330, 20741371532518174471), (4331, 4331, 20536011418334826209), (4332, 4332, 20332684572608738821), (4333, 4333, 20131370863969048337), (4334, 4334, 19932050360365394393), (4335, 7209, 19734703327094449894)]

def glob4 : ℕ := 2698500957556355349776

def runs5 : List (ℕ × ℕ × ℕ) := [(0, 3827, 0), (3828, 3828, 225267904201945785), (3829, 3829, 225276610576541947), (3830, 3830, 225334392455601425), (3831, 3831, 225438665524708667), (3832, 3832, 225590909580047169), (3833, 3833, 225792700582100828), (3834, 3834, 226045717815817933), (3835, 3835, 226351751704118753), (3836, 3836, 226712712344599611), (3837, 3837, 227130638847869731), (3838, 3838, 227607709565732438), (3839, 3839, 228146253308573967), (3840, 3840, 228748761664067142), (3841, 3841, 229417902543886806), (3842, 3842, 230156535101866762), (3843, 3843, 230967726186254485), (3844, 3844, 231854768510853458), (3845, 3845, 232821200755372212), (3846, 3846, 233870829834803015), (3847, 3847, 235007755611818495), (3848, 3848, 236236398365818496), (3849, 3849, 237561529378355923), (3850, 3850, 238988305048382107), (3851, 3851, 240522305013470882), (3852, 3852, 242169574826574601), (3853, 3853, 243936673823939211), (3854, 3854, 245830728920971829), (3855, 3855, 247859495192022300), (3856, 3856, 250031424230723988), (3857, 3857, 252355741453989714), (3858, 3858, 254842533710126706), (3859, 3859, 257502848786066257), (3860, 3860, 260348808687982731), (3861, 3861, 263393738902812594), (3862, 3862, 266652316246563270), (3863, 3863, 270140738382401161), (3864, 3864, 273876918663784158), (3865, 3865, 277880710645251141), (3866, 3866, 282174167429855454), (3867, 3867, 286781842016305856), (3868, 3868, 291731136004680299), (3869, 3869, 297052705456959578), (3870, 3870, 302780934433396453), (3871, 3871, 308954488789034157), (3872, 3872, 315616965271006631), (3873, 3873, 322817653860014369), (3874, 3874, 330612434692363243), (3875, 3875, 339064834800840355), (3876, 3876, 348247274290180955), (3877, 3877, 358242536285638150), (3878, 3878, 369145499760064696), (3879, 3879, 381065178565792562), (3880, 3880, 394127112608365519), (3881, 3881, 408476156280500291), (3882, 3882, 424279702039129359), (3883, 3883, 441731358625875363), (3884, 3884, 461055066694024958), (3885, 3885, 482509569029612592), (3886, 3886, 506393043841532409), (3887, 3887, 533047540120283012), (3888, 3888, 562862605947867853), (3889, 3889, 596277164054292620), (3890, 3890, 633778279177318286), (3891, 3891, 675895047860780810), (3892, 3892, 723185582001468517), (3893, 3893, 776215224848343811), (3894, 3894, 835525081895013845), (3895, 3895, 901591937542406397), (3896, 3896, 974783547709307411), (3897, 3897, 1055316347227642343), (3898, 3898, 1143224330763443284), (3899, 3899, 1238346820102647747), (3900, 3900, 1340338707872117528), (3901, 3901, 1448701004506095584), (3902, 3902, 1562824620076332101), (3903, 3903, 1682038262986790996), (3904, 3904, 1805652421383425389), (3905, 3905, 1932994393396792855), (3906, 3906, 2063432613209951499), (3907, 3907, 2196390969139328518), (3908, 3908, 2331355098727890045), (3909, 3909, 2467872980819017319), (3910, 3910, 2605551911528081592), (3911, 3911, 2744053486145766790), (3912, 3912, 2883087723092364021), (3913, 3913, 3022407057755063654), (3914, 3914, 3161800630444318524), (3915, 3915, 3301089085371442811), (3916, 3916, 3440119965564463382), (3917, 3917, 3578763710294643563), (3918, 3918, 3716910218955995053), (3919, 3919, 3854465925216240168), (3920, 3920, 3991351318577811988), (3921, 3921, 4127498851347064046), (3922, 3922, 4262851173723641481), (3923, 3923, 4397359646083664876), (3924, 3924, 4530983084280982061), (3925, 3925, 4663686700257860429), (3926, 3926, 4795441206119269521), (3927, 3927, 4926222054965404797), (3928, 3928, 5056008796188809692), (3929, 3929, 5184784526675387807), (3930, 3930, 5312535422477384591), (3931, 3931, 5439250338132401998), (3932, 3932, 5564920462964313452), (3933, 3933, 5689539025490977122), (3934, 3934, 5813101038542409163), (3935, 3935, 5935603078915018462), (3936, 3936, 6057043096397608941), (3937, 3937, 6177420247840597757), (3938, 3938, 6296734752632269129), (3939, 3939, 6414987766520392252), (3940, 3940, 6532181271195109121), (3941, 3941, 6648317977446788640), (3942, 3942, 6763401240044578436), (3943, 3943, 6877434982759146867), (3944, 3944, 6990423632185994489), (3945, 3945, 7102372059221428109), (3946, 3946, 7213285527208149446), (3947, 3947, 7323169645906604434), (3948, 3948, 7432030330566039338), (3949, 3949, 7539873765469136852), (3950, 3950, 7646706371409067042), (3951, 3951, 7752534776630191221), (3952, 3952, 7857365790825497195), (3953, 3953, 7961206381836780697), (3954, 3954, 8064063654749001528), (3955, 3955, 8165944833109287072), (3956, 3956, 8266857242034694858), (3957, 3957, 8366808293001888285), (3958, 3958, 8465805470137004570), (3959, 3959, 8563856317845773454), (3960, 3960, 8660968429642861417), (3961, 3961, 8757149438055877167), (3962, 3962, 8852407005493825442), (3963, 3963, 8946748815982331082), (3964, 3964, 9040182567678923450), (3965, 3965, 9132715966091285332), (3966, 3966, 9224356717929812042), (3967, 3967, 9315112525533251103), (3968, 3968, 9404991081812733772), (3969, 3969, 9494000065665281332), (3970, 3970, 9582147137812969950), (3971, 3971, 9669439937028452883), (3972, 3972, 9755886076711541268), (3973, 3973, 9841493141785097986), (3974, 3974, 9926268685881658193), (3975, 3975, 10010220228795002664), (3976, 3976, 10093355254173417636), (3977, 3977, 10175681207433613408), (3978, 3978, 10257205493876275085), (3979, 3979, 10337935476986010009), (3980, 3980, 10417878476900061689), (3981, 3981, 10497041769031600480), (3982, 3982, 10575432582834695366), (3983, 3983, 10653058100699235214), (3984, 3984, 10729925456965116099), (3985, 3985, 10806041737045956314), (3986, 3986, 10881413976653453609), (3987, 3987, 10956049161114269872), (3988, 3988, 11029954224772025509), (3989, 3989, 11103136050467616956), (3990, 3990, 11175601469091642786), (3991, 3991, 11247357259203242967), (3992, 3992, 11318410146710127126), (3993, 3993, 11388766804604996269), (3994, 3994, 11458433852753952250), (3995, 3995, 11527417857732844454), (3996, 3996, 11595725332707826866), (3997, 3997, 11663362737356694069), (3998, 3998, 11730336477827834458), (3999, 3999, 11796652906733885501), (4000, 4000, 11862318323177401381), (4001, 4001, 11927338972806049840), (4002, 4002, 11991721047895044222), (4003, 4003, 12055470687454690163), (4004, 4004, 12118593977361085602), (4005, 4005, 12181096950508158967), (4006, 4006, 12242985586979364765), (4007, 4007, 12304265814237479391), (4008, 4008, 12364943507331053743), (4009, 4009, 12425024489116183963), (4010, 4010, 12484514530492358233), (4011, 4011, 12543419350651226600), (4012, 4012, 12601744617337223008), (4013, 4013, 12659495947119044638), (4014, 4014, 12716678905671063820), (4015, 4015, 12773299008063812642), (4016, 4016, 12829361719062740418), (4017, 4017, 12884872453434499754), (4018, 4018, 12939836576260068427), (4019, 4019, 12994259403254062020), (4020, 4020, 13048146201089636507), (4021, 4021, 13101502187728421057), (4022, 4022, 13154332532754959460), (4023, 4023, 13206642357715173986), (4024, 4024, 13258436736458398429), (4025, 4025, 13309720695482557691), (4026, 4026, 13360499214282099737), (4027, 4027, 13410777225698312296), (4028, 4028, 13460559616271681328), (4029, 4029, 13509851226595971329), (4030, 4030, 13558656851673728949), (4031, 4031, 13606981241272931416), (4032, 4032, 13654829100284519929), (4033, 4033, 13702205089080575540), (4034, 4034, 13749113823872911391), (4035, 4035, 13795559877071870261), (4036, 4036, 13841547777645130657), (4037, 4037, 13887082011476337898), (4038, 4038, 13932167021723389055), (4039, 4039, 13976807209176212247), (4040, 4040, 14021006932613891619), (4041, 4041, 14064770509160999519), (4042, 4042, 14108102214643006916), (4043, 4043, 14151006283940651998), (4044, 4044, 14193486911343155293), (4045, 4045, 14235548250900177443), (4046, 4046, 14277194416772423142), (4047, 4047, 14318429483580801639), (4048, 4048, 14359257486754060636), (4049, 4049, 14399682422874816535), (4050, 4050, 14439708250023909630), (4051, 4051, 14479338888123018205), (4052, 4052, 14518578219275470533), (4053, 4053, 14557430088105198457), (4054, 4054, 14595898302093780680), (4055, 4055, 14633986631915528050), (4056, 4056, 14671698811770567032), (4057, 4057, 14709038539715881232), (4058, 4058, 14746009477994274303), (4059, 4059, 14782615253361220794), (4060, 4060, 14818859457409574578), (4061, 4061, 14854745646892107340), (4062, 4062, 14890277344041852328), (4063, 4063, 14925458036890231105), (4064, 4064, 14960291179582943411), (4065, 4065, 14994780192693602527), (4066, 4066, 15028928463535100597), (4067, 4067, 15062739346468690402), (4068, 4068, 15096216163210771906), (4069, 4069, 15129362203137373695), (4070, 4070, 15162180723586321031), (4071, 4071, 15194674950157083855), (4072, 4072, 15226848077008299496), (4073, 4073, 15258703267152966229), (4074, 4074, 15290243652751305128), (4075, 4075, 15321472335401288855), (4076, 4076, 15352392386426837193), (4077, 4077, 15383006847163680178), (4078, 4078, 15413318729242890718), (4079, 4079, 15443331014872089502), (4080, 4080, 15473046657114325938), (4081, 4081, 15502468580164639632), (4082, 4082, 15531599679624307763), (4083, 4083, 15560442822772784392), (4084, 4084, 15589000848837338470), (4085, 4085, 15617276569260397921), (4086, 4086, 15645272767964607809), (4087, 4087, 15672992201615611132), (4088, 4088, 15700437599882561347), (4089, 4089, 15727611665696376187), (4090, 4090, 15754517075505742817), (4091, 4091, 15781156479530884798), (4092, 4092, 15807532502015101722), (4093, 4093, 15833647741474092760), (4094, 4094, 15859504770943075703), (4095, 4095, 15885106138221713411), (4096, 4096, 15910454366116859862), (4097, 4097, 15935551952683138288), (4098, 4098, 15960401371461364131), (4099, 4099, 15985005071714825779), (4100, 4100, 16009365478663436273), (4101, 4101, 16033484993715769367), (4102, 4102, 16057365994698993496), (4103, 4103, 16081010836086717387), (4104, 4104, 16104421849224761186), (4105, 4105, 16127601342554867121), (4106, 4106, 16150551601836363827), (4107, 4107, 16173274890365798595), (4108, 4108, 16195773449194551867), (4109, 4109, 16218049497344448430), (4110, 4110, 16240105232021379796), (4111, 4111, 16261942828826952348), (4112, 4112, 16283564441968175875), (4113, 4113, 16304972204465207163), (4114, 4114, 16326168228357163367), (4115, 4115, 16347154604906019882), (4116, 4116, 16367933404798607490), (4117, 4117, 16388506678346723555), (4118, 4118, 16408876455685372041), (4119, 4119, 16429044746969147148), (4120, 4120, 16449013542566775335), (4121, 4121, 16468784813253830507), (4122, 4122, 16488360510403637108), (4123, 4123, 16507742566176375853), (4124, 4124, 16526932893706406806), (4125, 4125, 16545933387287824467), (4126, 4126, 16564745922558259516), (4127, 4127, 16583372356680941790), (4128, 4128, 16601814528525039076), (4129, 4129, 16620074258844286192), (4130, 4130, 16638153350453918839), (4131, 4131, 16656053588405926605), (4132, 4132, 16673776740162639483), (4133, 4133, 16691324555768662166), (4134, 4134, 16708698768021170369), (4135, 4135, 16725901092638583302), (4136, 4136, 16742933228427626421), (4137, 4137, 16759796857448798446), (4138, 4138, 16776493645180256610), (4139, 4139, 16793025240680134026), (4140, 4140, 16809393276747302941), (4141, 4141, 16825599370080597643), (4142, 4142, 16841645121436510629), (4143, 4143, 16857532115785375625), (4144, 4144, 16873261922466050936), (4145, 4145, 16888836095339116524), (4146, 4146, 16904256172938598144), (4147, 4147, 16919523678622231765), (4148, 4148, 16934640120720281430), (4149, 4149, 16949606992682923618), (4150, 4150, 16964425773226211085), (4151, 4151, 16979097926476629078), (4152, 4152, 16993624902114256711), (4153, 4153, 17008008135514546230), (4154, 4154, 17022249047888732776), (4155, 4155, 17036349046422887197), (4156, 4156, 17050309524415624323), (4157, 4157, 17064131861414479092), (4158, 4158, 17077817423350962754), (4159, 4159, 17091367562674311350), (4160, 4160, 17104783618483938529), (4161, 4161, 17118066916660604697), (4162, 4162, 17131218769996314387), (4163, 4163, 17144240478322953673), (4164, 4164, 17157133328639679312), (4165, 4165, 17169898595239071263), (4166, 4166, 17182537539832060098), (4167, 4167, 17195051411671640740), (4168, 4168, 17207441447675383894), (4169, 4169, 17219708872546756400), (4170, 4170, 17231854898895261700), (4171, 4171, 17243880727355411471), (4172, 4172, 17255787546704539422), (4173, 4173, 17267576533979468137), (4174, 4174, 17279248854592039783), (4175, 4175, 17290805662443521371), (4176, 4176, 17302248100037895223), (4177, 4177, 17313577298594045153), (4178, 4178, 17324794378156848830), (4179, 4179, 17335900447707186659), (4180, 4180, 17346896605270877470), (4181, 4181, 17357783938026551179), (4182, 4182, 17368563522412468526), (4183, 4183, 17379236424232297890), (4184, 4184, 17389803698759859109), (4185, 4185, 17400266390842844133), (4186, 4186, 17410625535005524263), (4187, 4187, 17420882155550453640), (4188, 4188, 17431037266659178555), (4189, 4189, 17441091872491962094), (4190, 4190, 17451046967286533510), (4191, 4191, 17460903535455871655), (4192, 4192, 17470662551685031734), (4193, 4193, 17480324981027024514), (4194, 4194, 17489891778997757099), (4195, 4195, 17499363891670044255), (4196, 4196, 17508742255766699211), (4197, 4197, 17518027798752712771), (4198, 4198, 17527221438926529505), (4199, 4199, 17536324085510429693), (4200, 4200, 17545336638740025627), (4201, 4201, 17554259989952880799), (4202, 4202, 17563095021676260420), (4203, 4203, 17571842607714021635), (4204, 4204, 17580503613232651744), (4205, 4205, 17589078894846462626), (4206, 4206, 17597569300701949528), (4207, 4207, 17605975670561322278), (4208, 4208, 17614298835885216919), (4209, 4209, 17622539619914595684), (4210, 4210, 17630698837751843161), (4211, 4211, 17638777296441066426), (4212, 4212, 17646775795047606842), (4213, 4213, 17654695124736771159), (4214, 4214, 17662536068851789485), (4215, 4215, 17670299402991007596), (4216, 4216, 17677985895084321044), (4217, 4217, 17685596305468858372), (4218, 4218, 17693131386963920761), (4219, 4219, 17700591884945185295), (4220, 4220, 17707978537418179009), (4221, 4221, 17715292075091030795), (4222, 4222, 17722533221446508187), (4223, 4223, 17729702692813345967), (4224, 4224, 17736801198436873486), (4225, 4225, 17743829440548947507), (4226, 4226, 17750788114437197343), (4227, 4227, 17757677908513588962), (4228, 4228, 17764499504382314703), (4229, 4229, 17771253576907015164), (4230, 4230, 17777940794277339766), (4231, 4231, 17784561818074852432), (4232, 4232, 17791117303338288771), (4233, 4233, 17797607898628171082), (4234, 4234, 17804034246090787441), (4235, 4235, 17810396981521541069), (4236, 4236, 17816696734427676136), (4237, 4237, 17822934128090386070), (4238, 4238, 17829109779626310406), (4239, 4239, 17835224300048426147), (4240, 4240, 17841278294326339538), (4241, 4241, 17847272361445984125), (4242, 4242, 17853207094468730887), (4243, 4243, 17859083080589916184), (4244, 4244, 17864900901196793224), (4245, 4245, 17870661131925912675), (4246, 4246, 17876364342719937999), (4247, 4247, 17882011097883901048), (4248, 4248, 17887601956140903390), (4249, 4249, 17893137470687268789), (4250, 4250, 17898618189247152204), (4251, 4251, 17904044654126610640), (4252, 4252, 17909417402267141102), (4253, 4253, 17914736965298690884), (4254, 4254, 17920003869592145351), (4255, 4255, 17925218636311298330), (4256, 4256, 17930381781464310191), (4257, 4257, 17935493815954658623), (4258, 4258, 17940555245631587080), (4259, 4259, 17945566571340055830), (4260, 4260, 17950528288970200465), (4261, 4261, 17955440889506302716), (4262, 4262, 17960304859075278350), (4263, 4263, 17965120678994686877), (4264, 4264, 17969888825820267774), (4265, 4265, 17974609771393007852), (4266, 4266, 17979283982885744380), (4267, 4267, 17983911922849308514), (4268, 4268, 17988494049258213544), (4269, 4269, 17993030815555892429), (4270, 4270, 17997522670699489036), (4271, 4271, 18001970059204207479), (4272, 4272, 18006373421187223886), (4273, 4273, 18010733192411164883), (4274, 4274, 18015049804327157082), (4275, 4275, 18019323684117451742), (4276, 4276, 18023555254737628817), (4277, 4277, 18027744934958384498), (4278, 4278, 18031893139406906354), (4279, 4279, 18036000278607840113), (4280, 4280, 18040066759023852114), (4281, 4281, 18044092983095791384), (4282, 4282, 18048079349282455292), (4283, 4283, 18052026252099962668), (4284, 4284, 18055934082160738248), (4285, 4285, 18059803226212112271), (4286, 4286, 18063634067174539008), (4287, 4287, 18067426984179437969), (4288, 4288, 18071182352606661511), (4289, 4289, 18074900544121592507), (4290, 4290, 18078581926711875720), (4291, 4291, 18082226864723786497), (4292, 4292, 18085835718898240335), (4293, 4293, 18089408846406446863), (4294, 4294, 18092946600885211733), (4295, 4295, 18096449332471889901), (4296, 4296, 18099917387838993700), (4297, 4297, 18103351110228459138), (4298, 4298, 18106750839485573753), (4299, 4299, 18110116912092569385), (4300, 4300, 18113449661201883142), (4301, 4301, 18116749416669089844), (4302, 4302, 18120016505085509166), (4303, 4303, 18123251249810490700), (4304, 4304, 18126453971003380084), (4305, 4305, 18129624985655169371), (4306, 4306, 18132764607619834720), (4307, 4307, 18135873147645364505), (4308, 4308, 18138950913404480886), (4309, 4309, 18141998209525057865), (4310, 4310, 18145015337620238814), (4311, 4311, 18148002596318256445), (4312, 4312, 18150960281291958139), (4313, 4313, 18153888685288039552), (4314, 4314, 18156788098155989368), (4315, 4315, 18159658806876748041), (4316, 4316, 18162501095591083358), (4317, 4317, 18165315245627685594), (4318, 4318, 18168101535530985049), (4319, 4319, 18170860241088694681), (4320, 4320, 18173591635359080557), (4321, 4321, 18176295988697962804), (4322, 4322, 18178973568785449717), (4323, 4323, 18181624640652407654), (4324, 4324, 18184249466706669321), (4325, 4325, 18186848306758983040), (4326, 4326, 18189421418048705530), (4327, 4327, 18191969055269240759), (4328, 4328, 18194491470593227351), (4329, 4329, 18196988913697477035), (4330, 4330, 18199461631787666595), (4331, 4331, 18201909869622785743), (4332, 4332, 18204333869539343343), (4333, 4333, 18206733871475334336), (4334, 4334, 18209110112993969767), (4335, 7209, 18446744073709462085)]

def glob5 : ℕ := 20482369533115327708

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
cap-777 law through the binomial thinning, so the envelope is `u = 13167581e-8`, `λ = 2027792e-6` on uniform
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

def meanN : ℕ := 111099
def meanD : ℕ := 100000
def secN : ℕ := 94302
def secD : ℕ := 10000000
def countN : ℕ := 106013
def countD : ℕ := 10000000
def overN : ℕ := 40729
def overD : ℕ := 10000000
def mgfN : ℕ := 11886
def mgfD : ℕ := 1000
def scarfN : ℕ := 20744
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

theorem rc_c0 : (rcPar.c0 : ℝ) = (11 / 25 : ℝ) := by norm_num [rcPar]
theorem rc_a : (rcPar.a : ℝ) = (19 / 2 : ℝ) := by norm_num [rcPar]
theorem rc_θ : (rcPar.θ : ℝ) = 397071 / 200000 - 1 / 1024 := by norm_num [rcPar]
theorem rc_m : (rcPar.m : ℝ) = (meanN : ℝ) / meanD := by norm_num [rcPar, meanN, meanD]
theorem rc_vv : (rcPar.vv : ℝ) = (secN : ℝ) / secD := by norm_num [rcPar, secN, secD]

/-- `exp (B - a θ_mid) ≤ (9444 / 10000000 : ℝ)` from the Taylor lower bound of `exp (a θ_mid - B)`. -/
theorem rc_exp_mid : Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) ≤ (9444 / 10000000 : ℝ) := by
  have hx : (mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ ≤ -(1393 / 200 : ℝ) := by norm_num [rcPar, mgfN, mgfD]
  have h0 : (0 : ℝ) ≤ (1393 / 200 : ℝ) := by norm_num
  have he := Real.sum_le_exp_of_nonneg h0 30
  have hs : (10000000 / 9444 : ℝ) ≤ ∑ i ∈ Finset.range 30, (1393 / 200 : ℝ) ^ i / (Nat.factorial i) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  refine (Real.exp_le_exp.mpr hx).trans ?_
  rw [Real.exp_neg, show (9444 / 10000000 : ℝ) = ((10000000 / 9444 : ℝ))⁻¹ by norm_num]
  exact inv_anti₀ (by norm_num) (hs.trans he)

/-- Route-C total at the middle threshold: `K0 + K1 + O Λ + tF ≤ (2155 / 1000000 : ℝ)`. -/
theorem rc_total_mid :
    3 / (8 * (rcPar.a : ℝ)) * Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (2155 / 1000000 : ℝ) := by
  have hk : (0 : ℝ) ≤ 3 / (8 * (rcPar.a : ℝ)) := by rw [rc_a]; norm_num
  have h1 := mul_le_mul_of_nonneg_left rc_exp_mid hk
  have h2 : 3 / (8 * (rcPar.a : ℝ)) * (9444 / 10000000 : ℝ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (2155 / 1000000 : ℝ) := by
    rw [rc_a]; norm_num [scarfN, scarfD, overN, overD, countN, countD, longN, longD]
  linarith

/-- Low threshold: `3/(8a) exp (B - a (1 - 1/1024)) + O ≤ 49/100`. -/
theorem rc_total_low :
    3 / (8 * (rcPar.a : ℝ)) * Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * (1 - 1 / 1024)) + (overN : ℝ) / overD ≤
      49 / 100 := by
  have hy : (mgfN : ℝ) / mgfD - rcPar.a * (1 - 1 / 1024) ≤ 2 + 2 / 5 := by norm_num [rcPar, mgfN, mgfD]
  have hx : Real.exp ((2 / 5 : ℝ) / 2) ≤ 1 / (1 - (2 / 5 : ℝ) / 2) := by
    have h := Real.add_one_le_exp (-((2 / 5 : ℝ) / 2))
    rw [Real.exp_neg] at h
    rw [le_div_iff₀ (by norm_num)]
    have hpos := Real.exp_pos ((2 / 5 : ℝ) / 2)
    have h' : (1 - (2 / 5 : ℝ) / 2) * Real.exp ((2 / 5 : ℝ) / 2) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h hpos.le
      rwa [inv_mul_cancel₀ hpos.ne', show -((2 / 5 : ℝ) / 2) + 1 = 1 - (2 / 5 : ℝ) / 2 by ring] at this
    linarith
  have he : Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * (1 - 1 / 1024)) ≤
      (2.7182818286 : ℝ) ^ 2 * (1 / (1 - (2 / 5 : ℝ) / 2)) ^ 2 := by
    refine (Real.exp_le_exp.mpr hy).trans ?_
    have hp : Real.exp (2 + 2 / 5 : ℝ) = Real.exp 1 ^ 2 * Real.exp ((2 / 5 : ℝ) / 2) ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [hp]
    exact mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le _)
      (pow_le_pow_left₀ (Real.exp_pos _).le hx _) (by positivity) (by positivity)
  have hk : (0 : ℝ) ≤ 3 / (8 * (rcPar.a : ℝ)) := by rw [rc_a]; norm_num
  have h1 := mul_le_mul_of_nonneg_left he hk
  have h2 : 3 / (8 * (rcPar.a : ℝ)) * ((2.7182818286 : ℝ) ^ 2 * (1 / (1 - (2 / 5 : ℝ) / 2)) ^ 2) +
      (overN : ℝ) / overD ≤ 49 / 100 := by
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
    (2:ENNReal)^128 * ((934*2^62:Nat):ENNReal) *
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

noncomputable def feeCoefficient : ENNReal := 934/2^66

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

 theorem feeCoefficient_real : feeCoefficient.toReal = (934:ℝ)/2^66 := by
  norm_num [feeCoefficient,ENNReal.toReal_div]

 theorem cappedIncrement_nat (n : Nat) :
    cappedIncrement (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (Real.exp (6*min ((934:ℝ)/2^66*(n:ℝ)) (6/5))-1) := by
  rw [cappedIncrement_real _ (by unfold feeCoefficient; finiteness),
    ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast]

 theorem cappedResidual_nat (n : Nat) :
    cappedResidual (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (max 0 ((934:ℝ)/2^66*(n:ℝ)-6/5)) := by
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
    ((934:ℝ)/2^66) (alphabetSize:ℝ) ENNReal.toReal_nonneg hx).1
  rw [cappedIncrement_real _ (priceBucket_ne_top W)]
  calc
    _ ≤ ENNReal.ofReal ((maxFee:ℝ)*((934:ℝ)/2^66)*(alphabetSize:ℝ)/scale) :=
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

 theorem law_price_mean_bound : Law.lawAvg honestLaw (2^32) price ≤ (1115:ENNReal)/1000 := by
  rw [law_price_coordAverage]
  apply coordAverage_bound_of_rows (2^32) 1 1 (by norm_num) (by norm_num)
    id forestMoment (1115/1000) (fun _ _ h => h)
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

 theorem law_nearPrice_mean_bound : Law.lawAvg honestLaw (2^32) nearPrice ≤ (23017/50) := by
  rw [law_nearPrice_coordAverage]
  apply coordAverage_history_bound (2^32) 54 1 (by norm_num) (by norm_num)
    nearBucket (fun _ h => feeCoefficient*(SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit h:ENNReal))
    forestNearMoment (23017/50) (fun L b R => nearBucket_insert L R b)
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
    nearPrice average_nearScore (23017/50)
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
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((397071 : ℝ) / 200000 - 1 / 1024)) ≤
      ENNReal.ofReal ((2155 : ℝ) / 1000000) := by
  have hP := parFacts_of_ok rcPar par_ok
  have he : (fun W : List Proposal => price W - ENNReal.ofReal ((397071 : ℝ) / 200000 - 1 / 1024)) =
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
      (fun W => price W-ENNReal.ofReal ((397071:ℝ)/200000-1/1024)) ≤
        ENNReal.ofReal ((2155 : ℝ) / 1000000) := rc_excess_middle

theorem excess_high_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((2:ℝ)-4326/1000000-1/1024)) ≤
        ENNReal.ofReal ((215501853:ℝ)/100000000000) :=
  (Law.lawAvg_mono _ _ (fun W => tsub_le_tsub_left
    (ENNReal.ofReal_le_ofReal (by norm_num : (397071 : ℝ) / 200000 - 1 / 1024 ≤ 2 - 4326 / 1000000 - 1 / 1024)) _)).trans
    (rc_excess_middle.trans (ENNReal.ofReal_le_ofReal (by norm_num)))

theorem excess_low_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((1:ℝ)-1/1024)) ≤
        ENNReal.ofReal ((49:ℝ)/100) := rc_excess_low

/-- Large queries: the cap-777 envelope `(993/1000) y` from the high and low endpoints (as in #938). -/
theorem excess_large_certified (y : ℝ)
    (hy0 : 2163/1000000 ≤ y) (hy1 : y ≤ 1/2) :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal (2-2*y-1/1024)) ≤
        ENNReal.ofReal ((99631/100000)*y) := by
  let t : ℝ := (y-2163/1000000)/(1/2-2163/1000000)
  have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hy0) (by norm_num)
  have ht1 : t≤1 := (div_le_one (by norm_num : (0:ℝ)<1/2-2163/1000000)).2 (by linarith)
  have h := price_excess_affine (2^32) (2-4326/1000000-1/1024) (1-1/1024)
    (215501853/100000000000) (49/100) t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ht0 ht1 excess_high_certified excess_low_certified
  have harg : (1-t)*(2-4326/1000000-1/1024)+t*(1-1/1024) = 2-2*y-1/1024 := by
    dsimp [t]; ring
  rw [harg] at h
  have hgap : (99631/100000)*y-((1-t)*(215501853/100000000000)+t*(49/100)) = t*(1631/200000) := by
    dsimp [t]; ring
  have hval : (1-t)*(215501853/100000000000)+t*(49/100) ≤ (99631/100000)*y := by nlinarith
  exact h.trans (ENNReal.ofReal_le_ofReal hval)

/-- Tiny queries: affine interpolation between the middle and low endpoints. -/
theorem excess_tiny_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W=>price W-ENNReal.ofReal ((249:ℝ)/125-1/1024)) ≤
        ENNReal.ofReal ((18:ℝ)/5000) :=
  (Law.lawAvg_mono _ _ (fun W => tsub_le_tsub_left
    (ENNReal.ofReal_le_ofReal (by norm_num : (397071 : ℝ) / 200000 - 1 / 1024 ≤ 249 / 125 - 1 / 1024)) _)).trans
    (excess_middle_certified.trans (ENNReal.ofReal_le_ofReal (by norm_num)))
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
