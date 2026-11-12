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
theorem selected_top_histogram_card (c : Nat) (hc : 18 ≤ c) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 18 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c).card =
      histogramWeight TopZero.topAcceptedHistogram c := by
  rw [selected_top_path_card 18 c le_rfl hc, TopZero.topAcceptedHistogram, histogramWeight_split,
    if_pos (by omega : 2 ≤ c), topWordCount_eq_hist (c - 2) (by omega), topWordCount_eq_hist c (by omega),
    topHighWeight_eq]
  ring

theorem selected_top_histogram_probability (c : Nat) (hc : 18 ≤ c) :
    Pr[fun answer => ∃ dl, CanonicalPolicy.producerDecodeOut 0 18 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (histogramWeight TopZero.topAcceptedHistogram c : ENNReal) / topDen := by
  classical
  rw [probEvent_uniformSample]
  rw [show (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 18 answer = some dl ∧
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

def rcPar : Par := ⟨929, (11 / 25 : ℚ), (19 / 2 : ℚ), (9869009 / 5000000 : ℚ), (110506 / 100000 : ℚ), (93490 / 10000000 : ℚ), (966903 / 10000000 : ℚ)⟩

def runs0 : List (ℕ × ℕ × ℕ) := [(0, 3841, 18446744073709551616), (3842, 3842, 18314547167315332018), (3843, 3843, 18133215017143893087), (3844, 3844, 17953678234795933749), (3845, 3845, 17775919044352409653), (3846, 3846, 17599919845893474904), (3847, 3847, 17425663213755915746), (3848, 3848, 17253131894807837373), (3849, 3849, 17082308806740433042), (3850, 3850, 16913177036376666378), (3851, 3851, 16745719837996699384), (3852, 3852, 16579920631679900381), (3853, 3853, 16415763001663267704), (3854, 3854, 16253230694716106637), (3855, 3855, 16092307618530798651), (3856, 3856, 15932977840129503615), (3857, 3857, 15775225584286637242), (3858, 3858, 15619035231966967567), (3859, 3859, 15464391318779175808), (3860, 3860, 15311278533444728523), (3861, 3861, 15159681716281909429), (3862, 3862, 15009585857704860821), (3863, 3863, 14860976096737485961), (3864, 3864, 14713837719542065308), (3865, 3865, 14568156157962440899), (3866, 3866, 14423916988081624653), (3867, 3867, 14281105928793687775), (3868, 3868, 14139708840389789876), (3869, 3869, 13999711723158207798), (3870, 3870, 13861100715998225543), (3871, 3871, 13723862095047748062), (3872, 3872, 13587982272324503032), (3873, 3873, 13453447794380696071), (3874, 3874, 13320245340970986209), (3875, 3875, 13188361723733649712), (3876, 3876, 13057783884884801695), (3877, 3877, 12928498895925546233), (3878, 3878, 12800493956361926963), (3879, 3879, 12673756392437551448), (3880, 3880, 12548273655878763810), (3881, 3881, 12424033322652241396), (3882, 3882, 12301023091734892472), (3883, 3883, 12179230783895933140), (3884, 3884, 12058644340491022911), (3885, 3885, 11939251822268339516), (3886, 3886, 11821041408186474768), (3887, 3887, 11704001394244034424), (3888, 3888, 11588120192320826163), (3889, 3889, 11473386329030520953), (3890, 3890, 11359788444584674211), (3891, 3891, 11247315291667994268), (3892, 3892, 11135955734324746800), (3893, 3893, 11025698746856184951), (3894, 3894, 10916533412728895991), (3895, 3895, 10808448923493956427), (3896, 3896, 10701434577716788541), (3897, 3897, 10595479779917612417), (3898, 3898, 10490574039522388532), (3899, 3899, 10386706969824147061), (3900, 3900, 10283868286954601051), (3901, 3901, 10182047808865941634), (3902, 3902, 10081235454322714489), (3903, 3903, 9981421241903677712), (3904, 3904, 9882595289013542289), (3905, 3905, 9784747810904497316), (3906, 3906, 9687869119707423085), (3907, 3907, 9591949623472696124), (3908, 3908, 9496979825220491212), (3909, 3909, 9402950322000486348), (3910, 3910, 9309851803960877573), (3911, 3911, 9217675053426611458), (3912, 3912, 9126410943986744018), (3913, 3913, 9036050439590835661), (3914, 3914, 8946584593654292734), (3915, 3915, 8858004548172567063), (3916, 3916, 8770301532844125805), (3917, 3917, 8683466864202104758), (3918, 3918, 8597491944754559166), (3919, 3919, 8512368262133226897), (3920, 3920, 8428087388250719700), (3921, 3921, 8344640978466059109), (3922, 3922, 8262020770758474365), (3923, 3923, 8180218584909380560), (3924, 3924, 8099226321692456000), (3925, 3925, 8019035962071738614), (3926, 3926, 7939639566407661994), (3927, 3927, 7861029273670952469), (3928, 3928, 7783197300664309375), (3929, 3929, 7706135941251791461), (3930, 3930, 7629837565595833129), (3931, 3931, 7554294619401814980), (3932, 3932, 7479499623170113841), (3933, 3933, 7405445171455558259), (3934, 3934, 7332123932134216098), (3935, 3935, 7259528645677441681), (3936, 3936, 7187652124433110575), (3937, 3937, 7116487251913970867), (3938, 3938, 7046026982093040462), (3939, 3939, 6976264338705980655), (3940, 3940, 6907192414560376886), (3941, 3941, 6838804370851858303), (3942, 3942, 6771093436486988419), (3943, 3943, 6704052907412859821), (3944, 3944, 6637676145953326556), (3945, 3945, 6571956580151808471), (3946, 3946, 6506887703120602446), (3947, 3947, 6442463072396636086), (3948, 3948, 6378676309303600085), (3949, 3949, 6315521098320396123), (3950, 3950, 6252991186455837746), (3951, 3951, 6191080382629542323), (3952, 3952, 6129782557058952795), (3953, 3953, 6069091640652428510), (3954, 3954, 6009001624408345059), (3955, 3955, 5949506558820143623), (3956, 3956, 5890600553287270914), (3957, 3957, 5832277775531951400), (3958, 3958, 5774532451021734059), (3959, 3959, 5717358862397756494), (3960, 3960, 5660751348908669796), (3961, 3961, 5604704305850168115), (3962, 3962, 5549212184010067441), (3963, 3963, 5494269489118878654), (3964, 3964, 5439870781305820450), (3965, 3965, 5386010674560218267), (3966, 3966, 5332683836198235908), (3967, 3967, 5279884986334887038), (3968, 3968, 5227608897361274295), (3969, 3969, 5175850393427004252), (3970, 3970, 5124604349927726982), (3971, 3971, 5073865692997749487), (3972, 3972, 5023629399007672760), (3973, 3973, 4973890494067002733), (3974, 3974, 4924644053531685874), (3975, 3975, 4875885201516520667), (3976, 3976, 4827609110412396700), (3977, 3977, 4779811000408313565), (3978, 3978, 4732486139018132242), (3979, 3979, 4685629840612012121), (3980, 3980, 4639237465952487248), (3981, 3981, 4593304421735135890), (3982, 3982, 4547826160133797910), (3983, 3983, 4502798178350294961), (3984, 3984, 4458216018168608872), (3985, 3985, 4414075265513474131), (3986, 3986, 4370371550013340724), (3987, 3987, 4327100544567664083), (3988, 3988, 4284257964918479290), (3989, 3989, 4241839569226217119), (3990, 3990, 4199841157649719919), (3991, 3991, 4158258571930415762), (3992, 3992, 4117087694980609665), (3993, 3993, 4076324450475851154), (3994, 3994, 4035964802451337776), (3995, 3995, 3996004754902314630), (3996, 3996, 3956440351388430326), (3997, 3997, 3917267674642010224), (3998, 3998, 3878482846180208143), (3999, 3999, 3840082025920998161), (4000, 4000, 3802061411802968476), (4001, 4001, 3764417239408879680), (4002, 4002, 3727145781592950178), (4003, 4003, 3690243348111831859), (4004, 4004, 3653706285259239465), (4005, 4005, 3617530975504197490), (4006, 4006, 3581713837132868802), (4007, 4007, 3546251323893929507), (4008, 4008, 3511139924647454957), (4009, 4009, 3476376163017282136), (4010, 4010, 3441956597046813996), (4011, 4011, 3407877818858231679), (4012, 4012, 3374136454315080870), (4013, 4013, 3340729162688198881), (4014, 4014, 3307652636324949388), (4015, 4015, 3274903600321732067), (4016, 4016, 3242478812199734720), (4017, 4017, 3210375061583895762), (4018, 4018, 3178589169885045309), (4019, 4019, 3147117989985193375), (4020, 4020, 3115958405925934035), (4021, 4021, 3085107332599934688), (4022, 4022, 3054561715445479889), (4023, 4023, 3024318530144039494), (4024, 4024, 2994374782320831182), (4025, 4025, 2964727507248347705), (4026, 4026, 2935373769552819510), (4027, 4027, 2906310662923583674), (4028, 4028, 2877535309825330370), (4029, 4029, 2849044861213198386), (4030, 4030, 2820836496250691471), (4031, 4031, 2792907422030387595), (4032, 4032, 2765254873297413461), (4033, 4033, 2737876112175656892), (4034, 4034, 2710768427896689992), (4035, 4035, 2683929136531376230), (4036, 4036, 2657355580724134881), (4037, 4037, 2631045129429836516), (4038, 4038, 2604995177653303481), (4039, 4039, 2579203146191389585), (4040, 4040, 2553666481377613451), (4041, 4041, 2528382654829320248), (4042, 4042, 2503349163197346780), (4043, 4043, 2478563527918165129), (4044, 4044, 2454023294968480326), (4045, 4045, 2429726034622257748), (4046, 4046, 2405669341210156186), (4047, 4047, 2381850832881342759), (4048, 4048, 2358268151367666098), (4049, 4049, 2334918961750164453), (4050, 4050, 2311800952227885597), (4051, 4051, 2288911833888995641), (4052, 4052, 2266249340484154100), (4053, 4053, 2243811228202132772), (4054, 4054, 2221595275447656210), (4055, 4055, 2199599282621441792), (4056, 4056, 2177821071902417616), (4057, 4057, 2156258487032096650), (4058, 4058, 2134909393101085792), (4059, 4059, 2113771676337708705), (4060, 4060, 2092843243898721490), (4061, 4061, 2072122023662100485), (4062, 4062, 2051605964021881668), (4063, 4063, 2031293033685031355), (4064, 4064, 2011181221470328074), (4065, 4065, 1991268536109235717), (4066, 4066, 1971553006048748234), (4067, 4067, 1952032679256186371), (4068, 4068, 1932705623025927100), (4069, 4069, 1913569923788046633), (4070, 4070, 1894623686918858053), (4071, 4071, 1875865036553324805), (4072, 4072, 1857292115399331490), (4073, 4073, 1838903084553793554), (4074, 4074, 1820696123320587678), (4075, 4075, 1802669429030284829), (4076, 4076, 1784821216861668148), (4077, 4077, 1767149719665017968), (4078, 4078, 1749653187787146503), (4079, 4079, 1732329888898164855), (4080, 4080, 1715178107819965203), (4081, 4081, 1698196146356401191), (4082, 4082, 1681382323125149694), (4083, 4083, 1664734973391237321), (4084, 4084, 1648252448902215169), (4085, 4085, 1631933117724965514), (4086, 4086, 1615775364084124271), (4087, 4087, 1599777588202103239), (4088, 4088, 1583938206140696276), (4089, 4089, 1568255649644253739), (4090, 4090, 1552728365984409642), (4091, 4091, 1537354817806346180), (4092, 4092, 1522133482976580377), (4093, 4093, 1507062854432257799), (4094, 4094, 1492141440031938414), (4095, 4095, 1477367762407859816), (4096, 4096, 1462740358819663184), (4097, 4097, 1448257781009567509), (4098, 4098, 1433918595058977732), (4099, 4099, 1419721381246512606), (4100, 4100, 1405664733907438224), (4101, 4101, 1391747261294493291), (4102, 4102, 1377967585440092367), (4103, 4103, 1364324342019893433), (4104, 4104, 1350816180217716270), (4105, 4105, 1337441762591798287), (4106, 4106, 1324199764942374542), (4107, 4107, 1311088876180568853), (4108, 4108, 1298107798198583023), (4109, 4109, 1285255245741171310), (4110, 4110, 1272529946278387436), (4111, 4111, 1259930639879591520), (4112, 4112, 1247456079088704476), (4113, 4113, 1235105028800697501), (4114, 4114, 1222876266139304456), (4115, 4115, 1210768580335945006), (4116, 4116, 1198780772609846541), (4117, 4117, 1186911656049353011), (4118, 4118, 1175160055494408921), (4119, 4119, 1163524807420206853), (4120, 4120, 1152004759821986983), (4121, 4121, 1140598772100977211), (4122, 4122, 1129305714951462585), (4123, 4123, 1118124470248972857), (4124, 4124, 1107053930939577086), (4125, 4125, 1096093000930274342), (4126, 4126, 1085240594980469646), (4127, 4127, 1074495638594524402), (4128, 4128, 1063857067915370695), (4129, 4129, 1053323829619178906), (4130, 4130, 1042894880811068224), (4131, 4131, 1032569188921849726), (4132, 4132, 1022345731605791808), (4133, 4133, 1012223496639397830), (4134, 4134, 1002201481821185970), (4135, 4135, 992278694872461357), (4136, 4136, 982454153339070650), (4137, 4137, 972726884494129357), (4138, 4138, 963095925241712234), (4139, 4139, 953560322021497262), (4140, 4140, 944119130714353724), (4141, 4141, 934771416548865074), (4142, 4142, 925516254008777301), (4143, 4143, 916352726741363664), (4144, 4144, 907279927466696697), (4145, 4145, 898296957887818512), (4146, 4146, 889402928601800507), (4147, 4147, 880596959011683670), (4148, 4148, 871878177239290763), (4149, 4149, 863245720038901745), (4150, 4150, 854698732711783906), (4151, 4151, 846236369021568224), (4152, 4152, 837857791110463588), (4153, 4153, 829562169416300582), (4154, 4154, 821348682590396616), (4155, 4155, 813216517416234273), (4156, 4156, 805164868728944825), (4157, 4157, 797192939335588936), (4158, 4158, 789299939936226669), (4159, 4159, 781485089045768979), (4160, 4160, 773747612916602950), (4161, 4161, 766086745461983119), (4162, 4162, 758501728180181305), (4163, 4163, 750991810079387431), (4164, 4164, 743556247603353892), (4165, 4165, 736194304557776131), (4166, 4166, 728905252037402110), (4167, 4167, 721688368353863475), (4168, 4168, 714542938964221262), (4169, 4169, 707468256400219072), (4170, 4170, 700463620198236705), (4171, 4171, 693528336829937331), (4172, 4172, 686661719633601318), (4173, 4173, 679863088746139919), (4174, 4174, 673131771035782098), (4175, 4175, 666467100035427820), (4176, 4176, 659868415876661208), (4177, 4177, 653335065224417037), (4178, 4178, 646866401212294096), (4179, 4179, 640461783378509006), (4180, 4180, 634120577602484165), (4181, 4181, 627842156042063530), (4182, 4182, 621625897071350029), (4183, 4183, 615471185219158445), (4184, 4184, 609377411108077668), (4185, 4185, 603343971394136305), (4186, 4186, 597370268707065649), (4187, 4187, 591455711591154108), (4188, 4188, 585599714446687235), (4189, 4189, 579801697471967560), (4190, 4190, 574061086605908475), (4191, 4191, 568377313471196510), (4192, 4192, 562749815318016346), (4193, 4193, 557178034968333016), (4194, 4194, 551661420760725759), (4195, 4195, 546199426495768078), (4196, 4196, 540791511381948592), (4197, 4197, 535437139982127319), (4198, 4198, 530135782160522098), (4199, 4199, 524886913030219899), (4200, 4200, 519690012901207821), (4201, 4201, 514544567228918634), (4202, 4202, 509450066563285776), (4203, 4203, 504406006498302749), (4204, 4204, 499411887622081930), (4205, 4205, 494467215467407851), (4206, 4206, 489571500462780051), (4207, 4207, 484724257883940644), (4208, 4208, 479925007805881826), (4209, 4209, 475173275055328541), (4210, 4210, 470468589163691624), (4211, 4211, 465810484320486757), (4212, 4212, 461198499327214611), (4213, 4213, 456632177551697634), (4214, 4214, 452111066882868945), (4215, 4215, 447634719686008856), (4216, 4216, 443202692758424610), (4217, 4217, 438814547285568921), (4218, 4218, 434469848797592991), (4219, 4219, 430168167126329694), (4220, 4220, 425909076362702667), (4221, 4221, 421692154814557097), (4222, 4222, 417516984964908016), (4223, 4223, 413383153430601996), (4224, 4224, 409290250921388115), (4225, 4225, 405237872199394174), (4226, 4226, 401225616039004132), (4227, 4227, 397253085187132804), (4228, 4228, 393319886323893866), (4229, 4229, 389425630023657293), (4230, 4230, 385569930716492369), (4231, 4231, 381752406649992444), (4232, 4232, 377972679851477668), (4233, 4233, 374230376090571948), (4234, 4234, 370525124842150444), (4235, 4235, 366856559249653905), (4236, 4236, 363224316088766242), (4237, 4237, 359628035731451725), (4238, 4238, 356067362110348243), (4239, 4239, 352541942683513112), (4240, 4240, 349051428399517932), (4241, 4241, 345595473662889042), (4242, 4242, 342173736299890141), (4243, 4243, 338785877524643703), (4244, 4244, 335431561905587825), (4245, 4245, 332110457332265174), (4246, 4246, 328822234982440766), (4247, 4247, 325566569289545313), (4248, 4248, 322343137910440904), (4249, 4249, 319151621693505845), (4250, 4250, 315991704647035490), (4251, 4251, 312863073907955931), (4252, 4252, 309765419710847456), (4253, 4253, 306698435357274709), (4254, 4254, 303661817185420504), (4255, 4255, 300655264540020301), (4256, 4256, 297678479742594358), (4257, 4257, 294731168061974612), (4258, 4258, 291813037685123378), (4259, 4259, 288923799688240968), (4260, 4260, 286063168008159374), (4261, 4261, 283230859414019183), (4262, 4262, 280426593479226914), (4263, 4263, 277650092553690013), (4264, 4264, 274901081736326746), (4265, 4265, 272179288847848263), (4266, 4266, 269484444403810162), (4267, 4267, 266816281587930853), (4268, 4268, 264174536225674112), (4269, 4269, 261558946758093180), (4270, 4270, 258969254215933842), (4271, 4271, 256405202193993903), (4272, 4272, 253866536825736537), (4273, 4273, 251353006758154988), (4274, 4274, 248864363126886126), (4275, 4275, 246400359531570422), (4276, 4276, 243960752011455863), (4277, 4277, 241545299021243429), (4278, 4278, 239153761407171712), (4279, 4279, 236785902383338329), (4280, 4280, 234441487508255771), (4281, 4281, 232120284661639377), (4282, 4282, 229822064021425126), (4283, 4283, 227546598041014976), (4284, 4284, 225293661426747501), (4285, 4285, 223063031115591585), (4286, 4286, 220854486253060976), (4287, 4287, 218667808171347501), (4288, 4288, 216502780367670793), (4289, 4289, 214359188482842369), (4290, 4290, 212236820280041950), (4291, 4291, 210135465623803910), (4292, 4292, 208054916459211793), (4293, 4293, 205994966791298805), (4294, 4294, 203955412664652282), (4295, 4295, 201936052143220081), (4296, 4296, 199936685290316912), (4297, 4297, 197957114148828626), (4298, 4298, 195997142721612501), (4299, 4299, 194056576952091585), (4300, 4300, 192135224705041173), (4301, 4301, 190232895747565518), (4302, 4302, 188349401730262889), (4303, 4303, 186484556168577118), (4304, 4304, 184638174424333780), (4305, 4305, 182810073687459188), (4306, 4306, 181000072957880384), (4307, 4307, 179207993027604341), (4308, 4308, 177433656462974595), (4309, 4309, 175676887587103559), (4310, 4310, 173937512462478772), (4311, 4311, 172215358873741358), (4312, 4312, 170510256310635008), (4313, 4313, 168822035951123770), (4314, 4314, 167150530644677000), (4315, 4315, 165495574895719802), (4316, 4316, 163857004847247329), (4317, 4317, 162234658264601316), (4318, 4318, 160628374519407243), (4319, 4319, 159037994573670538), (4320, 4320, 157463360964030236), (4321, 4321, 155904317786168550), (4322, 4322, 154360710679374802), (4323, 4323, 152832386811262180), (4324, 4324, 151319194862635822), (4325, 4325, 149820985012510715), (4326, 4326, 148337608923277936), (4327, 4327, 146868919726017758), (4328, 4328, 145414772005958176), (4329, 4329, 143975021788077402), (4330, 4330, 142549526522848913), (4331, 4331, 141138145072127637), (4332, 4332, 139740737695175878), (4333, 4333, 138357166034827602), (4334, 4334, 136987293103789705), (4335, 4335, 135630983271078916), (4336, 7209, 134288102248592986)]

def glob0 : ℕ := 18446744073709551616

def runs1 : List (ℕ × ℕ × ℕ) := [(0, 3000, 2138341529341260), (3001, 3001, 2159724944634672), (3002, 3002, 2181322194081019), (3003, 3003, 2203135416021829), (3004, 3004, 2225166770182047), (3005, 3005, 2247418437883868), (3006, 3006, 2269892622262706), (3007, 3007, 2292591548485333), (3008, 3008, 2315517463970187), (3009, 3009, 2338672638609889), (3010, 3010, 2362059364995988), (3011, 3011, 2385679958645947), (3012, 3012, 2409536758232407), (3013, 3013, 2433632125814731), (3014, 3014, 2457968447072878), (3015, 3015, 2482548131543607), (3016, 3016, 2507373612859043), (3017, 3017, 2532447348987634), (3018, 3018, 2557771822477510), (3019, 3019, 2583349540702285), (3020, 3020, 2609183036109308), (3021, 3021, 2635274866470401), (3022, 3022, 2661627615135105), (3023, 3023, 2688243891286456), (3024, 3024, 2715126330199320), (3025, 3025, 2742277593501314), (3026, 3026, 2769700369436327), (3027, 3027, 2797397373130690), (3028, 3028, 2825371346861997), (3029, 3029, 2853625060330617), (3030, 3030, 2882161310933923), (3031, 3031, 2910982924043262), (3032, 3032, 2940092753283695), (3033, 3033, 2969493680816532), (3034, 3034, 2999188617624697), (3035, 3035, 3029180503800944), (3036, 3036, 3059472308838954), (3037, 3037, 3090067031927343), (3038, 3038, 3120967702246617), (3039, 3039, 3152177379269083), (3040, 3040, 3183699153061774), (3041, 3041, 3215536144592391), (3042, 3042, 3247691506038315), (3043, 3043, 3280168421098698), (3044, 3044, 3312970105309685), (3045, 3045, 3346099806362782), (3046, 3046, 3379560804426410), (3047, 3047, 3413356412470674), (3048, 3048, 3447489976595381), (3049, 3049, 3481964876361335), (3050, 3050, 3516784525124948), (3051, 3051, 3551952370376197), (3052, 3052, 3587471894079959), (3053, 3053, 3623346613020759), (3054, 3054, 3659580079150967), (3055, 3055, 3696175879942476), (3056, 3056, 3733137638741901), (3057, 3057, 3770469015129320), (3058, 3058, 3808173705280613), (3059, 3059, 3846255442333419), (3060, 3060, 3884717996756754), (3061, 3061, 3923565176724321), (3062, 3062, 3962800828491564), (3063, 3063, 4002428836776480), (3064, 3064, 4042453125144245), (3065, 3065, 4082877656395687), (3066, 3066, 4123706432959644), (3067, 3067, 4164943497289240), (3068, 3068, 4206592932262133), (3069, 3069, 4248658861584754), (3070, 3070, 4291145450200602), (3071, 3071, 4334056904702608), (3072, 3072, 4377397473749634), (3073, 3073, 4421171448487130), (3074, 3074, 4465383162972001), (3075, 3075, 4510036994601721), (3076, 3076, 4555137364547739), (3077, 3077, 4600688738193216), (3078, 3078, 4646695625575148), (3079, 3079, 4693162581830900), (3080, 3080, 4740094207649209), (3081, 3081, 4787495149725701), (3082, 3082, 4835370101222958), (3083, 3083, 4883723802235187), (3084, 3084, 4932561040257539), (3085, 3085, 4981886650660115), (3086, 3086, 5031705517166716), (3087, 3087, 5082022572338383), (3088, 3088, 5132842798061767), (3089, 3089, 5184171226042384), (3090, 3090, 5236012938302808), (3091, 3091, 5288373067685836), (3092, 3092, 5341256798362695), (3093, 3093, 5394669366346322), (3094, 3094, 5448616060009785), (3095, 3095, 5503102220609883), (3096, 3096, 5558133242815981), (3097, 3097, 5613714575244141), (3098, 3098, 5669851720996583), (3099, 3099, 5726550238206548), (3100, 3100, 5783815740588614), (3101, 3101, 5841653897994500), (3102, 3102, 5900070436974445), (3103, 3103, 5959071141344189), (3104, 3104, 6018661852757631), (3105, 3105, 6078848471285208), (3106, 3106, 6139636955998060), (3107, 3107, 6201033325558040), (3108, 3108, 6263043658813621), (3109, 3109, 6325674095401757), (3110, 3110, 6388930836355775), (3111, 3111, 6452820144719332), (3112, 3112, 6517348346166526), (3113, 3113, 6582521829628191), (3114, 3114, 6648347047924473), (3115, 3115, 6714830518403717), (3116, 3116, 6781978823587755), (3117, 3117, 6849798611823632), (3118, 3118, 6918296597941868), (3119, 3119, 6987479563921287), (3120, 3120, 7057354359560500), (3121, 3121, 7127927903156105), (3122, 3122, 7199207182187666), (3123, 3123, 7271199254009543), (3124, 3124, 7343911246549638), (3125, 3125, 7417350359015135), (3126, 3126, 7491523862605286), (3127, 3127, 7566439101231339), (3128, 3128, 7642103492243652), (3129, 3129, 7718524527166089), (3130, 3130, 7795709772437749), (3131, 3131, 7873666870162127), (3132, 3132, 7952403538863748), (3133, 3133, 8031927574252386), (3134, 3134, 8112246849994910), (3135, 3135, 8193369318494859), (3136, 3136, 8275303011679807), (3137, 3137, 8358056041796605), (3138, 3138, 8441636602214571), (3139, 3139, 8526052968236717), (3140, 3140, 8611313497919084), (3141, 3141, 8697426632898275), (3142, 3142, 8784400899227258), (3143, 3143, 8872244908219530), (3144, 3144, 8960967357301726), (3145, 3145, 9050577030874743), (3146, 3146, 9141082801183490), (3147, 3147, 9232493629195325), (3148, 3148, 9324818565487278), (3149, 3149, 9418066751142151), (3150, 3150, 9512247418653573), (3151, 3151, 9607369892840109), (3152, 3152, 9703443591768510), (3153, 3153, 9800478027686195), (3154, 3154, 9898482807963057), (3155, 3155, 9997467636042687), (3156, 3156, 10097442312403114), (3157, 3157, 10198416735527145), (3158, 3158, 10300400902882417), (3159, 3159, 10403404911911241), (3160, 3160, 10507438961030353), (3161, 3161, 10612513350640657), (3162, 3162, 10718638484147063), (3163, 3163, 10825824868988534), (3164, 3164, 10934083117678419), (3165, 3165, 11043423948855203), (3166, 3166, 11153858188343755), (3167, 3167, 11265396770227193), (3168, 3168, 11378050737929465), (3169, 3169, 11491831245308760), (3170, 3170, 11606749557761847), (3171, 3171, 11722817053339466), (3172, 3172, 11840045223872860), (3173, 3173, 11958445676111589), (3174, 3174, 12078030132872705), (3175, 3175, 12198810434201432), (3176, 3176, 12320798538543446), (3177, 3177, 12444006523928881), (3178, 3178, 12568446589168169), (3179, 3179, 12694131055059851), (3180, 3180, 12821072365610450), (3181, 3181, 12949283089266554), (3182, 3182, 13078775920159220), (3183, 3183, 13209563679360812), (3184, 3184, 13341659316154420), (3185, 3185, 13475075909315964), (3186, 3186, 13609826668409124), (3187, 3187, 13745924935093215), (3188, 3188, 13883384184444147), (3189, 3189, 14022218026288589), (3190, 3190, 14162440206551474), (3191, 3191, 14304064608616989), (3192, 3192, 14447105254703159), (3193, 3193, 14591576307250191), (3194, 3194, 14737492070322693), (3195, 3195, 14884866991025919), (3196, 3196, 15033715660936179), (3197, 3197, 15184052817545540), (3198, 3198, 15335893345720996), (3199, 3199, 15489252279178206), (3200, 3200, 15644144801969988), (3201, 3201, 15800586249989688), (3202, 3202, 15958592112489585), (3203, 3203, 16118178033614480), (3204, 3204, 16279359813950625), (3205, 3205, 16442153412090132), (3206, 3206, 16606574946211033), (3207, 3207, 16772640695673143), (3208, 3208, 16940367102629875), (3209, 3209, 17109770773656173), (3210, 3210, 17280868481392735), (3211, 3211, 17453677166206662), (3212, 3212, 17628213937868729), (3213, 3213, 17804496077247416), (3214, 3214, 17982541038019890), (3215, 3215, 18162366448400089), (3216, 3216, 18343990112884090), (3217, 3217, 18527430014012931), (3218, 3218, 18712704314153060), (3219, 3219, 18899831357294591), (3220, 3220, 19088829670867537), (3221, 3221, 19279717967576212), (3222, 3222, 19472515147251974), (3223, 3223, 19667240298724494), (3224, 3224, 19863912701711739), (3225, 3225, 20062551828728856), (3226, 3226, 20263177347016145), (3227, 3227, 20465809120486306), (3228, 3228, 20670467211691170), (3229, 3229, 20877171883808081), (3230, 3230, 21085943602646162), (3231, 3231, 21296803038672624), (3232, 3232, 21509771069059350), (3233, 3233, 21724868779749943), (3234, 3234, 21942117467547443), (3235, 3235, 22161538642222917), (3236, 3236, 22383154028645146), (3237, 3237, 22606985568931598), (3238, 3238, 22833055424620914), (3239, 3239, 23061385978867123), (3240, 3240, 23291999838655794), (3241, 3241, 23524919837042352), (3242, 3242, 23760169035412776), (3243, 3243, 23997770725766903), (3244, 3244, 24237748433024572), (3245, 3245, 24480125917354818), (3246, 3246, 24724927176528366), (3247, 3247, 24972176448293650), (3248, 3248, 25221898212776586), (3249, 3249, 25474117194904352), (3250, 3250, 25728858366853396), (3251, 3251, 25986146950521930), (3252, 3252, 26246008420027149), (3253, 3253, 26508468504227421), (3254, 3254, 26773553189269695), (3255, 3255, 27041288721162392), (3256, 3256, 27311701608374016), (3257, 3257, 27584818624457756), (3258, 3258, 27860666810702333), (3259, 3259, 28139273478809357), (3260, 3260, 28420666213597450), (3261, 3261, 28704872875733425), (3262, 3262, 28991921604490759), (3263, 3263, 29281840820535667), (3264, 3264, 29574659228741023), (3265, 3265, 29870405821028433), (3266, 3266, 30169109879238718), (3267, 3267, 30470800978031105), (3268, 3268, 30775508987811416), (3269, 3269, 31083264077689530), (3270, 3270, 31394096718466425), (3271, 3271, 31708037685651090), (3272, 3272, 32025118062507601), (3273, 3273, 32345369243132677), (3274, 3274, 32668822935564003), (3275, 3275, 32995511164919643), (3276, 3276, 33325466276568840), (3277, 3277, 33658720939334528), (3278, 3278, 33995308148727873), (3279, 3279, 34335261230215152), (3280, 3280, 34678613842517304), (3281, 3281, 35025399980942477), (3282, 3282, 35375653980751902), (3283, 3283, 35729410520559421), (3284, 3284, 36086704625765015), (3285, 3285, 36447571672022665), (3286, 3286, 36812047388742892), (3287, 3287, 37180167862630320), (3288, 3288, 37551969541256624), (3289, 3289, 37927489236669190), (3290, 3290, 38306764129035882), (3291, 3291, 38689831770326241), (3292, 3292, 39076730088029503), (3293, 3293, 39467497388909798), (3294, 3294, 39862172362798896), (3295, 3295, 40260794086426885), (3296, 3296, 40663402027291154), (3297, 3297, 41070036047564065), (3298, 3298, 41480736408039706), (3299, 3299, 41895543772120103), (3300, 3300, 42314499209841304), (3301, 3301, 42737644201939717), (3302, 3302, 43165020643959114), (3303, 3303, 43596670850398705), (3304, 3304, 44032637558902692), (3305, 3305, 44472963934491719), (3306, 3306, 44917693573836637), (3307, 3307, 45366870509575003), (3308, 3308, 45820539214670753), (3309, 3309, 46278744606817460), (3310, 3310, 46741532052885635), (3311, 3311, 47208947373414491), (3312, 3312, 47681036847148636), (3313, 3313, 48157847215620123), (3314, 3314, 48639425687776324), (3315, 3315, 49125819944654087), (3316, 3316, 49617078144100628), (3317, 3317, 50113248925541634), (3318, 3318, 50614381414797051), (3319, 3319, 51120525228945021), (3320, 3320, 51631730481234471), (3321, 3321, 52148047786046816), (3322, 3322, 52669528263907284), (3323, 3323, 53196223546546357), (3324, 3324, 53728185782011821), (3325, 3325, 54265467639831939), (3326, 3326, 54808122316230258), (3327, 3327, 55356203539392561), (3328, 3328, 55909765574786486), (3329, 3329, 56468863230534351), (3330, 3330, 57033551862839695), (3331, 3331, 57603887381468092), (3332, 3332, 58179926255282773), (3333, 3333, 58761725517835600), (3334, 3334, 59349342773013956), (3335, 3335, 59942836200744096), (3336, 3336, 60542264562751537), (3337, 3337, 61147687208379052), (3338, 3338, 61759164080462843), (3339, 3339, 62376755721267471), (3340, 3340, 63000523278480146), (3341, 3341, 63630528511264947), (3342, 3342, 64266833796377597), (3343, 3343, 64909502134341373), (3344, 3344, 65558597155684786), (3345, 3345, 66214183127241634), (3346, 3346, 66876324958514051), (3347, 3347, 67545088208099191), (3348, 3348, 68220539090180183), (3349, 3349, 68902744481081985), (3350, 3350, 69591771925892805), (3351, 3351, 70287689645151733), (3352, 3352, 70990566541603250), (3353, 3353, 71700472207019283), (3354, 3354, 72417476929089475), (3355, 3355, 73141651698380370), (3356, 3356, 73873068215364174), (3357, 3357, 74611798897517816), (3358, 3358, 75357916886492994), (3359, 3359, 76111496055357924), (3360, 3360, 76872611015911503), (3361, 3361, 77641337126070618), (3362, 3362, 78417750497331324), (3363, 3363, 79201928002304637), (3364, 3364, 79993947282327684), (3365, 3365, 80793886755150960), (3366, 3366, 81601825622702470), (3367, 3367, 82417843878929495), (3368, 3368, 83242022317718790), (3369, 3369, 84074442540895978), (3370, 3370, 84915186966304937), (3371, 3371, 85764338835967987), (3372, 3372, 86621982224327667), (3373, 3373, 87488202046570943), (3374, 3374, 88363084067036653), (3375, 3375, 89246714907707019), (3376, 3376, 90139182056784089), (3377, 3377, 91040573877351930), (3378, 3378, 91950979616125450), (3379, 3379, 92870489412286704), (3380, 3380, 93799194306409571), (3381, 3381, 94737186249473667), (3382, 3382, 95684558111968403), (3383, 3383, 96641403693088087), (3384, 3384, 97607817730018968), (3385, 3385, 98583895907319158), (3386, 3386, 99569734866392350), (3387, 3387, 100565432215056273), (3388, 3388, 101571086537206836), (3389, 3389, 102586797402578904), (3390, 3390, 103612665376604693), (3391, 3391, 104648792030370740), (3392, 3392, 105695279950674448), (3393, 3393, 106752232750181192), (3394, 3394, 107819755077683004), (3395, 3395, 108897952628459834), (3396, 3396, 109986932154744432), (3397, 3397, 111086801476291877), (3398, 3398, 112197669491054795), (3399, 3399, 113319646185965343), (3400, 3400, 114452842647824997), (3401, 3401, 115597371074303247), (3402, 3402, 116753344785046279), (3403, 3403, 117920878232896742), (3404, 3404, 119100087015225709), (3405, 3405, 120291087885377966), (3406, 3406, 121493998764231746), (3407, 3407, 122708938751874064), (3408, 3408, 123936028139392804), (3409, 3409, 125175388420786732), (3410, 3410, 126427142304994600), (3411, 3411, 127691413728044546), (3412, 3412, 128968327865324991), (3413, 3413, 130258011143978241), (3414, 3414, 131560591255418023), (3415, 3415, 132876197167972204), (3416, 3416, 134204959139651926), (3417, 3417, 135547008731048445), (3418, 3418, 136902478818358929), (3419, 3419, 138271503606542519), (3420, 3420, 139654218642607944), (3421, 3421, 141050760829034023), (3422, 3422, 142461268437324363), (3423, 3423, 143885881121697607), (3424, 3424, 145324739932914583), (3425, 3425, 146777987332243729), (3426, 3426, 148245767205566166), (3427, 3427, 149728224877621828), (3428, 3428, 151225507126398046), (3429, 3429, 152737762197662027), (3430, 3430, 154265139819638647), (3431, 3431, 155807791217835033), (3432, 3432, 157365869130013384), (3433, 3433, 158939527821313517), (3434, 3434, 160528923099526653), (3435, 3435, 162134212330521919), (3436, 3436, 163755554453827138), (3437, 3437, 165393109998365410), (3438, 3438, 167047041098349064), (3439, 3439, 168717511509332554), (3440, 3440, 170404686624425880), (3441, 3441, 172108733490670139), (3442, 3442, 173829820825576840), (3443, 3443, 175568119033832609), (3444, 3444, 177323800224170935), (3445, 3445, 179097038226412644), (3446, 3446, 180888008608676770), (3447, 3447, 182696888694763538), (3448, 3448, 184523857581711174), (3449, 3449, 186369096157528285), (3450, 3450, 188232787119103568), (3451, 3451, 190115114990294604), (3452, 3452, 192016266140197550), (3453, 3453, 193936428801599525), (3454, 3454, 195875793089615521), (3455, 3455, 197834551020511676), (3456, 3456, 199812896530716792), (3457, 3457, 201811025496023960), (3458, 3458, 203829135750984200), (3459, 3459, 205867427108494042), (3460, 3460, 207926101379578982), (3461, 3461, 210005362393374772), (3462, 3462, 212105416017308520), (3463, 3463, 214226470177481605), (3464, 3464, 216368734879256421), (3465, 3465, 218532422228048985), (3466, 3466, 220717746450329475), (3467, 3467, 222924923914832770), (3468, 3468, 225154173153981098), (3469, 3469, 227405714885520909), (3470, 3470, 229679772034376118), (3471, 3471, 231976569754719879), (3472, 3472, 234296335452267078), (3473, 3473, 236639298806789748), (3474, 3474, 239005691794857646), (3475, 3475, 241395748712806222), (3476, 3476, 243809706199934285), (3477, 3477, 246247803261933627), (3478, 3478, 248710281294552964), (3479, 3479, 251197384107498493), (3480, 3480, 253709357948573478), (3481, 3481, 256246451528059213), (3482, 3482, 258808916043339805), (3483, 3483, 261397005203773203), (3484, 3484, 264010975255810935), (3485, 3485, 266651085008369045), (3486, 3486, 269317595858452735), (3487, 3487, 272010771817037262), (3488, 3488, 274730879535207635), (3489, 3489, 277478188330559711), (3490, 3490, 280252970213865308), (3491, 3491, 283055499916003962), (3492, 3492, 285886054915164001), (3493, 3493, 288744915464315641), (3494, 3494, 291632364618958798), (3495, 3495, 294548688265148386), (3496, 3496, 297494175147799869), (3497, 3497, 300469116899277868), (3498, 3498, 303473808068270647), (3499, 3499, 306508546148953353), (3500, 3500, 309573631610442887), (3501, 3501, 312669367926547316), (3502, 3502, 315796061605812789), (3503, 3503, 318954022221870917), (3504, 3504, 322143562444089626), (3505, 3505, 325364998068530522), (3506, 3506, 328618648049215827), (3507, 3507, 331904834529707986), (3508, 3508, 335223882875005065), (3509, 3509, 338576121703755116), (3510, 3510, 341961882920792667), (3511, 3511, 345381501750000594), (3512, 3512, 348835316767500600), (3513, 3513, 352323669935175606), (3514, 3514, 355846906634527362), (3515, 3515, 359405375700872635), (3516, 3516, 362999429457881362), (3517, 3517, 366629423752460175), (3518, 3518, 370295717989984777), (3519, 3519, 373998675169884625), (3520, 3520, 377738661921583471), (3521, 3521, 381516048540799306), (3522, 3522, 385331209026207299), (3523, 3523, 389184521116469372), (3524, 3524, 393076366327634066), (3525, 3525, 397007129990910406), (3526, 3526, 400977201290819510), (3527, 3527, 404986973303727705), (3528, 3528, 409036843036764983), (3529, 3529, 413127211467132632), (3530, 3530, 417258483581803959), (3531, 3531, 421431068417621998), (3532, 3532, 425645379101798218), (3533, 3533, 429901832892816200), (3534, 3534, 434200851221744362), (3535, 3535, 438542859733961806), (3536, 3536, 442928288331301424), (3537, 3537, 447357571214614438), (3538, 3538, 451831146926760583), (3539, 3539, 456349458396028189), (3540, 3540, 460912952979988470), (3541, 3541, 465522082509788355), (3542, 3542, 470177303334886239), (3543, 3543, 474879076368235101), (3544, 3544, 479627867131917452), (3545, 3545, 484424145803236627), (3546, 3546, 489268387261268993), (3547, 3547, 494161071133881683), (3548, 3548, 499102681845220500), (3549, 3549, 504093708663672705), (3550, 3550, 509134645750309432), (3551, 3551, 514225992207812526), (3552, 3552, 519368252129890651), (3553, 3553, 524561934651189558), (3554, 3554, 529807553997701453), (3555, 3555, 535105629537678468), (3556, 3556, 540456685833055252), (3557, 3557, 545861252691385805), (3558, 3558, 551319865218299663), (3559, 3559, 556833063870482660), (3560, 3560, 562401394509187486), (3561, 3561, 568025408454279361), (3562, 3562, 573705662538822155), (3563, 3563, 579442719164210376), (3564, 3564, 585237146355852480), (3565, 3565, 591089517819411005), (3566, 3566, 597000412997605115), (3567, 3567, 602970417127581166), (3568, 3568, 609000121298856978), (3569, 3569, 615090122511845547), (3570, 3570, 621241023736964003), (3571, 3571, 627453433974333643), (3572, 3572, 633727968314076979), (3573, 3573, 640065247997217749), (3574, 3574, 646465900477189927), (3575, 3575, 652930559481961826), (3576, 3576, 659459865076781444), (3577, 3577, 666054463727549258), (3578, 3578, 672715008364824751), (3579, 3579, 679442158448472999), (3580, 3580, 686236580032957729), (3581, 3581, 693098945833287306), (3582, 3582, 700029935291620179), (3583, 3583, 707030234644536381), (3584, 3584, 714100536990981744), (3585, 3585, 721241542360891562), (3586, 3586, 728453957784500478), (3587, 3587, 735738497362345482), (3588, 3588, 743095882335968937), (3589, 3589, 750526841159328626), (3590, 3590, 758032109570921913), (3591, 3591, 765612430666631132), (3592, 3592, 773268554973297443), (3593, 3593, 781001240523030418), (3594, 3594, 788811252928260722), (3595, 3595, 796699365457543329), (3596, 3596, 804666359112118762), (3597, 3597, 812713022703239950), (3598, 3598, 820840152930272349), (3599, 3599, 829048554459575073), (3600, 3600, 837339040004170824), (3601, 3601, 845712430404212532), (3602, 3602, 854169554708254657), (3603, 3603, 862711250255337204), (3604, 3604, 871338362757890576), (3605, 3605, 880051746385469482), (3606, 3606, 888852263849324176), (3607, 3607, 897740786487817418), (3608, 3608, 906718194352695592), (3609, 3609, 915785376296222548), (3610, 3610, 924943230059184774), (3611, 3611, 934192662359776621), (3612, 3612, 943534588983374388), (3613, 3613, 952969934873208131), (3614, 3614, 962499634221940213), (3615, 3615, 972124630564159615), (3616, 3616, 981845876869801211), (3617, 3617, 991664335638499223), (3618, 3618, 1001580978994884215), (3619, 3619, 1011596788784833058), (3620, 3620, 1021712756672681388), (3621, 3621, 1031929884239408202), (3622, 3622, 1042249183081802284), (3623, 3623, 1052671674912620307), (3624, 3624, 1063198391661746510), (3625, 3625, 1073830375578363975), (3626, 3626, 1084568679334147615), (3627, 3627, 1095414366127489091), (3628, 3628, 1106368509788763982), (3629, 3629, 1117432194886651622), (3630, 3630, 1128606516835518138), (3631, 3631, 1139892582003873319), (3632, 3632, 1151291507823912052), (3633, 3633, 1162804422902151173), (3634, 3634, 1174432467131172685), (3635, 3635, 1186176791802484411), (3636, 3636, 1198038559720509256), (3637, 3637, 1210018945317714348), (3638, 3638, 1222119134770891492), (3639, 3639, 1234340326118600406), (3640, 3640, 1246683729379786411), (3641, 3641, 1259150566673584275), (3642, 3642, 1271742072340320117), (3643, 3643, 1284459493063723319), (3644, 3644, 1297304087994360552), (3645, 3645, 1310277128874304157), (3646, 3646, 1323379900163047199), (3647, 3647, 1336613699164677671), (3648, 3648, 1349979836156324447), (3649, 3649, 1363479634517887692), (3650, 3650, 1377114430863066569), (3651, 3651, 1390885575171697235), (3652, 3652, 1404794430923414207), (3653, 3653, 1418842375232648349), (3654, 3654, 1433030798984974832), (3655, 3655, 1447361106974824581), (3656, 3656, 1461834718044572827), (3657, 3657, 1476453065225018555), (3658, 3658, 1491217595877268740), (3659, 3659, 1506129771836041428), (3660, 3660, 1521191069554401842), (3661, 3661, 1536402980249945860), (3662, 3662, 1551767010052445319), (3663, 3663, 1567284680152969772), (3664, 3664, 1582957526954499470), (3665, 3665, 1598787102224044465), (3666, 3666, 1614774973246284909), (3667, 3667, 1630922722978747758), (3668, 3668, 1647231950208535236), (3669, 3669, 1663704269710620588), (3670, 3670, 1680341312407726794), (3671, 3671, 1697144725531804062), (3672, 3672, 1714116172787122103), (3673, 3673, 1731257334514993324), (3674, 3674, 1748569907860143257), (3675, 3675, 1766055606938744690), (3676, 3676, 1783716163008132136), (3677, 3677, 1801553324638213458), (3678, 3678, 1819568857884595592), (3679, 3679, 1837764546463441548), (3680, 3680, 1856142191928075964), (3681, 3681, 1874703613847356723), (3682, 3682, 1893450649985830291), (3683, 3683, 1912385156485688594), (3684, 3684, 1931509008050545479), (3685, 3685, 1950824098131050934), (3686, 3686, 1970332339112361444), (3687, 3687, 1990035662503485058), (3688, 3688, 2009936019128519909), (3689, 3689, 2030035379319805108), (3690, 3690, 2050335733113003159), (3691, 3691, 2070839090444133190), (3692, 3692, 2091547481348574522), (3693, 3693, 2112462956162060267), (3694, 3694, 2133587585723680870), (3695, 3695, 2154923461580917679), (3696, 3696, 2176472696196726856), (3697, 3697, 2198237423158694124), (3698, 3698, 2220219797390281065), (3699, 3699, 2242421995364183876), (3700, 3700, 2264846215317825715), (3701, 3701, 2287494677471003972), (3702, 3702, 2310369624245714012), (3703, 3703, 2333473320488171152), (3704, 3704, 2356808053693052863), (3705, 3705, 2380376134229983392), (3706, 3706, 2404179895572283226), (3707, 3707, 2428221694528006058), (3708, 3708, 2452503911473286119), (3709, 3709, 2477028950588018980), (3710, 3710, 2501799240093899170), (3711, 3711, 2526817232494838161), (3712, 3712, 2552085404819786543), (3713, 3713, 2577606258867984408), (3714, 3714, 2603382321456664252), (3715, 3715, 2629416144671230895), (3716, 3716, 2655710306117943204), (3717, 3717, 2682267409179122636), (3718, 3718, 2709090083270913862), (3719, 3719, 2736180984103623001), (3720, 3720, 2763542793944659231), (3721, 3721, 2791178221884105823), (3722, 3722, 2819090004102946881), (3723, 3723, 2847280904143976350), (3724, 3724, 2875753713185416114), (3725, 3725, 2904511250317270275), (3726, 3726, 2933556362820442978), (3727, 3727, 2962891926448647407), (3728, 3728, 2992520845713133881), (3729, 3729, 3022446054170265220), (3730, 3730, 3052670514711967872), (3731, 3731, 3083197219859087551), (3732, 3732, 3114029192057678427), (3733, 3733, 3145169483978255211), (3734, 3734, 3176621178818037763), (3735, 3735, 3208387390606218141), (3736, 3736, 3240471264512280322), (3737, 3737, 3272875977157403125), (3738, 3738, 3305604736928977157), (3739, 3739, 3338660784298266928), (3740, 3740, 3372047392141249597), (3741, 3741, 3405767866062662093), (3742, 3742, 3439825544723288714), (3743, 3743, 3474223800170521601), (3744, 3744, 3508966038172226817), (3745, 3745, 3544055698553949086), (3746, 3746, 3579496255539488576), (3747, 3747, 3615291218094883462), (3748, 3748, 3651444130275832297), (3749, 3749, 3687958571578590620), (3750, 3750, 3724838157294376526), (3751, 3751, 3762086538867320291), (3752, 3752, 3799707404255993494), (3753, 3753, 3837704478298553429), (3754, 3754, 3876081523081538963), (3755, 3755, 3914842338312354353), (3756, 3756, 3953990761695477897), (3757, 3757, 3993530669312432675), (3758, 3758, 4033465976005557002), (3759, 3759, 4073800635765612572), (3760, 3760, 4114538642123268698), (3761, 3761, 4155684028544501385), (3762, 3762, 4197240868829946399), (3763, 3763, 4239213277518245863), (3764, 3764, 4281605410293428321), (3765, 3765, 4324421464396362605), (3766, 3766, 4367665679040326231), (3767, 3767, 4411342335830729493), (3768, 3768, 4455455759189036788), (3769, 3769, 4500010316780927156), (3770, 3770, 4545010419948736427), (3771, 3771, 4590460524148223792), (3772, 3772, 4636365129389706029), (3773, 3773, 4682728780683603090), (3774, 3774, 4729556068490439121), (3775, 3775, 4776851629175343512), (3776, 3776, 4824620145467096947), (3777, 3777, 4872866346921767916), (3778, 3778, 4921595010390985596), (3779, 3779, 4970810960494895452), (3780, 3780, 5020519070099844406), (3781, 3781, 5070724260800842850), (3782, 3782, 5121431503408851279), (3783, 3783, 5172645818442939791), (3784, 3784, 5224372276627369189), (3785, 3785, 5276615999393642881), (3786, 3786, 5329382159387579310), (3787, 3787, 5382675980981455103), (3788, 3788, 5436502740791269654), (3789, 3789, 5490867768199182351), (3790, 3790, 5545776445881174174), (3791, 3791, 5601234210339985916), (3792, 3792, 5657246552443385775), (3793, 3793, 5713819017967819633), (3794, 3794, 5770957208147497829), (3795, 3795, 5828666780228972807), (3796, 3796, 5886953448031262535), (3797, 3797, 5945822982511575161), (3798, 3798, 6005281212336690912), (3799, 3799, 6065334024460057822), (3800, 3800, 6125987364704658400), (3801, 3801, 6187247238351704984), (3802, 3802, 6249119710735222034), (3803, 3803, 6311610907842574254), (3804, 3804, 6374727016920999996), (3805, 3805, 6438474287090209996), (3806, 3806, 6502859029961112096), (3807, 3807, 6567887620260723217), (3808, 3808, 6633566496463330449), (3809, 3809, 6699902161427963754), (3810, 3810, 6766901183042243392), (3811, 3811, 6834570194872665825), (3812, 3812, 6902915896821392484), (3813, 3813, 6971945055789606408), (3814, 3814, 7041664506347502473), (3815, 3815, 7112081151410977497), (3816, 3816, 7183201962925087272), (3817, 3817, 7255033982554338145), (3818, 3818, 7327584322379881526), (3819, 3819, 7400860165603680342), (3820, 3820, 7474868767259717145), (3821, 3821, 7549617454932314317), (3822, 3822, 7625113629481637460), (3823, 3823, 7701364765776453834), (3824, 3824, 7778378413434218373), (3825, 3825, 7856162197568560556), (3826, 3826, 7934723819544246162), (3827, 3827, 8014071057739688624), (3828, 3828, 8094211768317085510), (3829, 3841, 8116567392432202712), (3842, 3842, 8058400753618746088), (3843, 3843, 7978614607543312958), (3844, 3844, 7899618423310210850), (3845, 3845, 7821404379515060247), (3846, 3846, 7743964732193128958), (3847, 3847, 7667291814052602929), (3848, 3848, 7591378033715448444), (3849, 3849, 7516215874965790539), (3850, 3850, 7441797896005733207), (3851, 3851, 7368116728718547729), (3852, 3852, 7295165077939156168), (3853, 3853, 7222935720731837790), (3854, 3854, 7151421505675086921), (3855, 3855, 7080615352153551407), (3856, 3856, 7010510249656981591), (3857, 3857, 6941099257086120387), (3858, 3858, 6872375502065465730), (3859, 3859, 6804332180262837356), (3860, 3860, 6736962554715680551), (3861, 3861, 6670259955164040149), (3862, 3862, 6604217777390138761), (3863, 3863, 6538829482564493823), (3864, 3864, 6474088596598508736), (3865, 3865, 6409988709503473996), (3866, 3866, 6346523474755914847), (3867, 3867, 6283686608669222621), (3868, 3868, 6221471889771507546), (3869, 3869, 6159873158189611431), (3870, 3870, 6098884315039219239), (3871, 3871, 6038499321821009148), (3872, 3872, 5978712199822781334), (3873, 3873, 5919517029527506272), (3874, 3874, 5860907950027233932), (3875, 3875, 5802879158442805873), (3876, 3876, 5745424909349312746), (3877, 3877, 5688539514207240343), (3878, 3878, 5632217340799247864), (3879, 3879, 5576452812672522638), (3880, 3880, 5521240408586656077), (3881, 3881, 5466574661966986215), (3882, 3882, 5412450160363352688), (3883, 3883, 5358861544914210582), (3884, 3884, 5305803509816050081), (3885, 3885, 5253270801798069387), (3886, 3886, 5201258219602048898), (3887, 3887, 5149760613467375147), (3888, 3888, 5098772884621163512), (3889, 3889, 5048289984773429220), (3890, 3890, 4998306915617256653), (3891, 3891, 4948818728333917478), (3892, 3892, 4899820523102888592), (3893, 3893, 4851307448616721379), (3894, 3894, 4803274701600714236), (3895, 3895, 4755717526337340828), (3896, 3896, 4708631214195386958), (3897, 3897, 4662011103163749464), (3898, 3898, 4615852577389850954), (3899, 3899, 4570151066722624707), (3900, 3900, 4524902046260024463), (3901, 3901, 4480101035901014319), (3902, 3902, 4435743599901994376), (3903, 3903, 4391825346437618194), (3904, 3904, 4348341927165958608), (3905, 3905, 4305289036797978819), (3906, 3906, 4262662412671266158), (3907, 3907, 4220457834327986295), (3908, 3908, 4178671123097016134), (3909, 3909, 4137298141680213994), (3910, 3910, 4096334793742786132), (3911, 3911, 4055777023507709042), (3912, 3912, 4015620815354167368), (3913, 3913, 3975862193419967691), (3914, 3914, 3936497221207888803), (3915, 3915, 3897522001195929508), (3916, 3916, 3858932674451415355), (3917, 3917, 3820725420248926094), (3918, 3918, 3782896455692006033), (3919, 3919, 3745442035338619835), (3920, 3920, 3708358450830316668), (3921, 3921, 3671642030525066008), (3922, 3922, 3635289139133728721), (3923, 3923, 3599296177360127447), (3924, 3924, 3563659581544680640), (3925, 3925, 3528375823311564990), (3926, 3926, 3493441409219371278), (3927, 3927, 3458852880415219087), (3928, 3928, 3424606812292296125), (3929, 3929, 3390699814150788243), (3930, 3930, 3357128528862166577), (3931, 3931, 3323889632536798591), (3932, 3932, 3290979834194850090), (3933, 3933, 3258395875440445634), (3934, 3934, 3226134530139055083), (3935, 3935, 3194192604098074340), (3936, 3936, 3162566934750568653), (3937, 3937, 3131254390842147182), (3938, 3938, 3100251872120937804), (3939, 3939, 3069556309030631489), (3940, 3940, 3039164662406565830), (3941, 3941, 3009073923174817654), (3942, 3942, 2979281112054274905), (3943, 3943, 2949783279261658322), (3944, 3944, 2920577504219463685), (3945, 3945, 2891660895266795727), (3946, 3946, 2863030589373065077), (3947, 3947, 2834683751854519878), (3948, 3948, 2806617576093584038), (3949, 3949, 2778829283260974295), (3950, 3950, 2751316122040568609), (3951, 3951, 2724075368356998622), (3952, 3952, 2697104325105939230), (3953, 3953, 2670400321887068545), (3954, 3954, 2643960714739671826), (3955, 3955, 2617782885880863194), (3956, 3956, 2591864243446399202), (3957, 3957, 2566202221234058616), (3958, 3958, 2540794278449562986), (3959, 3959, 2515637899455012858), (3960, 3960, 2490730593519814711), (3961, 3961, 2466069894574073971), (3962, 3962, 2441653360964429674), (3963, 3963, 2417478575212306608), (3964, 3964, 2393543143774560998), (3965, 3965, 2369844696806496038), (3966, 3966, 2346380887927223800), (3967, 3967, 2323149393987350297), (3968, 3968, 2300147914838960690), (3969, 3969, 2277374173107881871), (3970, 3970, 2254825913968199873), (3971, 3971, 2232500904919009775), (3972, 3972, 2210396935563376015), (3973, 3973, 2188511817389481203), (3974, 3974, 2166843383553941785), (3975, 3975, 2145389488667269094), (3976, 3976, 2124148008581454548), (3977, 3977, 2103116840179657969), (3978, 3978, 2082293901167978187), (3979, 3979, 2061677129869285333), (3980, 3980, 2041264485019094390), (3981, 3981, 2021053945563459792), (3982, 3982, 2001043510458871081), (3983, 3983, 1981231198474129783), (3984, 3984, 1961615047994187904), (3985, 3985, 1942193116825928618), (3986, 3986, 1922963482005869919), (3987, 3987, 1903924239609772197), (3988, 3988, 1885073504564130888), (3989, 3989, 1866409410459535532), (3990, 3990, 1847930109365876765), (3991, 3991, 1829633771649382936), (3992, 3992, 1811518585791468253), (3993, 3993, 1793582758209374508), (3994, 3994, 1775824513078588622), (3995, 3995, 1758242092157018437), (3996, 3996, 1740833754610909344), (3997, 3997, 1723597776842484499), (3998, 3998, 1706532452319291583), (3999, 3999, 1689636091405239191), (4000, 4000, 1672907021193306130), (4001, 4001, 1656343585339907059), (4002, 4002, 1639944143900898079), (4003, 4003, 1623707073169206018), (4004, 4004, 1607630765514065365), (4005, 4005, 1591713629221846896), (4006, 4006, 1575954088338462273), (4007, 4007, 1560350582513328983), (4008, 4008, 1544901566844880181), (4009, 4009, 1529605511727604140), (4010, 4010, 1514460902700598158), (4011, 4011, 1499466240297621939), (4012, 4012, 1484620039898635583), (4013, 4013, 1469920831582807508), (4014, 4014, 1455367159982977731), (4015, 4015, 1440957584141562110), (4016, 4016, 1426690677367883277), (4017, 4017, 1412565027096914136), (4018, 4018, 1398579234749419936), (4019, 4019, 1384731915593485085), (4020, 4020, 1371021698607410976), (4021, 4021, 1357447226343971263), (4022, 4022, 1344007154796011152), (4023, 4023, 1330700153263377378), (4024, 4024, 1317524904221165721), (4025, 4025, 1304480103189272991), (4026, 4026, 1291564458603240585), (4027, 4027, 1278776691686376817), (4028, 4028, 1266115536323145363), (4029, 4029, 1253579738933807290), (4030, 4030, 1241168058350304248), (4031, 4031, 1228879265693370542), (4032, 4032, 1216712144250861923), (4033, 4033, 1204665489357289033), (4034, 4034, 1192738108274543597), (4035, 4035, 1180928820073805541), (4036, 4036, 1169236455518619348), (4037, 4037, 1157659856949128067), (4038, 4038, 1146197878167453532), (4039, 4039, 1134849384324211418), (4040, 4040, 1123613251806149919), (4041, 4041, 1112488368124900909), (4042, 4042, 1101473631806832584), (4043, 4043, 1090567952283992657), (4044, 4044, 1079770249786131344), (4045, 4045, 1069079455233793409), (4046, 4046, 1058494510132468722), (4047, 4047, 1048014366467790814), (4048, 4048, 1037637986601773083), (4049, 4049, 1027364343170072360), (4050, 4050, 1017192418980269663), (4051, 4051, 1007121206911158082), (4052, 4052, 997149709813027804), (4053, 4053, 987276940408938420), (4054, 4054, 977501921196968733), (4055, 4055, 967823684353434389), (4056, 4056, 958241271637063751), (4057, 4057, 948753734294122526), (4058, 4058, 939360132964477749), (4059, 4059, 930059537588591830), (4060, 4060, 920851027315437456), (4061, 4061, 911733690411324214), (4062, 4062, 902706624169627934), (4063, 4063, 893768934821413796), (4064, 4064, 884919737446944353), (4065, 4065, 876158155888063716), (4066, 4066, 867483322661449223), (4067, 4067, 858894378872722003), (4068, 4068, 850390474131407924), (4069, 4069, 841970766466740519), (4070, 4070, 833634422244297544), (4071, 4071, 825380616083462914), (4072, 4072, 817208530775705856), (4073, 4073, 809117357203669164), (4074, 4074, 801106294261058578), (4075, 4075, 793174548773325325), (4076, 4076, 785321335419133985), (4077, 4077, 777545876652607906), (4078, 4078, 769847402626344462), (4079, 4079, 762225151115192536), (4080, 4080, 754678367440784689), (4081, 4081, 747206304396816524), (4082, 4082, 739808222175065866), (4083, 4083, 732483388292144421), (4084, 4084, 725231077516974675), (4085, 4085, 718050571798984826), (4086, 4086, 710941160197014680), (4087, 4087, 703902138808925425), (4088, 4088, 696932810701906362), (4089, 4089, 690032485843471645), (4090, 4090, 683200481033140243), (4091, 4091, 676436119834792320), (4092, 4092, 669738732509695366), (4093, 4093, 663107655950193432), (4094, 4094, 656542233614052903), (4095, 4095, 650041815459458319), (4096, 4096, 643605757880651801), (4097, 4097, 637233423644209704), (4098, 4098, 630924181825950202), (4099, 4099, 624677407748465547), (4100, 4100, 618492482919272819), (4101, 4101, 612368794969577048), (4102, 4102, 606305737593640642), (4103, 4103, 600302710488753111), (4104, 4104, 594359119295795159), (4105, 4105, 588474375540391247), (4106, 4106, 582647896574644799), (4107, 4107, 576879105519450296), (4108, 4108, 571167431207376530), (4109, 4109, 565512308126115377), (4110, 4110, 559913176362490472), (4111, 4111, 554369481547020269), (4112, 4112, 548880674799029970), (4113, 4113, 543446212672306901), (4114, 4114, 538065557101293961), (4115, 4115, 532738175347815803), (4116, 4116, 527463539948332478), (4117, 4117, 522241128661715325), (4118, 4118, 517070424417539926), (4119, 4119, 511950915264891016), (4120, 4120, 506882094321674273), (4121, 4121, 501863459724429973), (4122, 4122, 496894514578643538), (4123, 4123, 491974766909548057), (4124, 4124, 487103729613413918), (4125, 4125, 482280920409320711), (4126, 4126, 477505861791406644), (4127, 4127, 472778080981590737), (4128, 4128, 468097109882763106), (4129, 4129, 463462485032438719), (4130, 4130, 458873747556870019), (4131, 4131, 454330443125613880), (4132, 4132, 449832121906548396), (4133, 4133, 445378338521335045), (4134, 4134, 440968652001321827), (4135, 4135, 436602625743882997), (4136, 4136, 432279827469191086), (4137, 4137, 427999829177416917), (4138, 4138, 423762207106353383), (4139, 4139, 419566541689458795), (4140, 4140, 415412417514315639), (4141, 4141, 411299423281500633), (4142, 4142, 407227151763862013), (4143, 4143, 403195199766200012), (4144, 4144, 399203168085346547), (4145, 4145, 395250661470640146), (4146, 4146, 391337288584792223), (4147, 4147, 387462661965140815), (4148, 4148, 383626397985287936), (4149, 4149, 379828116817116768), (4150, 4150, 376067442393184919), (4151, 4151, 372344002369490019), (4152, 4152, 368657428088603979), (4153, 4153, 365007354543172256), (4154, 4154, 361393420339774511), (4155, 4155, 357815267663143081), (4156, 4156, 354272542240735723), (4157, 4157, 350764893307659132), (4158, 4158, 347291973571939735), (4159, 4159, 343853439180138351), (4160, 4160, 340448949683305298), (4161, 4161, 337078168003272572), (4162, 4162, 333740760399279775), (4163, 4163, 330436396434930470), (4164, 4164, 327164748945475713), (4165, 4165, 323925494005421498), (4166, 4166, 320718310896456929), (4167, 4167, 317542882075699929), (4168, 4168, 314398893144257356), (4169, 4169, 311286032816096392), (4170, 4170, 308203992887224150), (4171, 4171, 305152468205172426), (4172, 4172, 302131156638784580), (4173, 4173, 299139759048301565), (4174, 4174, 296177979255744123), (4175, 4175, 293245524015588241), (4176, 4176, 290342102985730932), (4177, 4177, 287467428698743497), (4178, 4178, 284621216533409403), (4179, 4179, 281803184686543963), (4180, 4180, 279013054145093033), (4181, 4181, 276250548658507953), (4182, 4182, 273515394711394013), (4183, 4183, 270807321496429716), (4184, 4184, 268126060887554174), (4185, 4185, 265471347413419975), (4186, 4186, 262842918231108886), (4187, 4187, 260240513100107808), (4188, 4188, 257663874356542384), (4189, 4189, 255112746887665726), (4190, 4190, 252586878106599729), (4191, 4191, 250086017927326465), (4192, 4192, 247609918739927193), (4193, 4193, 245158335386066527), (4194, 4194, 242731025134719334), (4195, 4195, 240327747658137954), (4196, 4196, 237948265008057381), (4197, 4197, 235592341592136020), (4198, 4198, 233259744150629723), (4199, 4199, 230950241733296756), (4200, 4200, 228663605676531441), (4201, 4201, 226399609580724199), (4202, 4202, 224158029287845742), (4203, 4203, 221938642859253210), (4204, 4204, 219741230553716049), (4205, 4205, 217565574805659455), (4206, 4206, 215411460203623223), (4207, 4207, 213278673468933884), (4208, 4208, 211167003434588004), (4209, 4209, 209076241024344558), (4210, 4210, 207006179232024315), (4211, 4211, 204956613101014173), (4212, 4212, 202927339703974429), (4213, 4213, 200918158122746959), (4214, 4214, 198928869428462336), (4215, 4215, 196959276661843897), (4216, 4216, 195009184813706829), (4217, 4217, 193078400805650326), (4218, 4218, 191166733470940916), (4219, 4219, 189273993535585066), (4220, 4220, 187399993599589174), (4221, 4221, 185544548118405123), (4222, 4222, 183707473384559527), (4223, 4223, 181888587509464879), (4224, 4224, 180087710405410771), (4225, 4225, 178304663767733437), (4226, 4226, 176539271057161818), (4227, 4227, 174791357482338434), (4228, 4228, 173060749982513301), (4229, 4229, 171347277210409209), (4230, 4230, 169650769515256643), (4231, 4231, 167971058925996676), (4232, 4232, 166307979134650174), (4233, 4233, 164661365479851658), (4234, 4234, 163031054930546196), (4235, 4235, 161416886069847718), (4236, 4236, 159818699079057147), (4237, 4237, 158236335721838759), (4238, 4238, 156669639328553227), (4239, 4239, 155118454780745769), (4240, 4240, 153582628495787891), (4241, 4241, 152062008411671179), (4242, 4242, 150556443971951662), (4243, 4243, 149065786110843230), (4244, 4244, 147589887238458643), (4245, 4245, 146128601226196677), (4246, 4246, 144681783392273937), (4247, 4247, 143249290487399938), (4248, 4248, 141830980680593998), (4249, 4249, 140426713545142572), (4250, 4250, 139036350044695616), (4251, 4251, 137659752519500610), (4252, 4252, 136296784672772881), (4253, 4253, 134947311557200872), (4254, 4254, 133611199561585022), (4255, 4255, 132288316397608933), (4256, 4256, 130978531086741518), (4257, 4257, 129681713947268829), (4258, 4258, 128397736581454287), (4259, 4259, 127126471862826026), (4260, 4260, 125867793923590125), (4261, 4261, 124621578142168441), (4262, 4262, 123387701130859842), (4263, 4263, 122166040723623606), (4264, 4264, 120956475963983768), (4265, 4265, 119758887093053236), (4266, 4266, 118573155537676471), (4267, 4267, 117399163898689576), (4268, 4268, 116236795939296610), (4269, 4269, 115085936573561000), (4270, 4270, 113946471855010891), (4271, 4271, 112818288965357318), (4272, 4272, 111701276203324077), (4273, 4273, 110595322973588195), (4274, 4274, 109500319775829896), (4275, 4275, 108416158193890986), (4276, 4276, 107342730885040580), (4277, 4277, 106279931569347109), (4278, 4278, 105227655019155554), (4279, 4279, 104185797048668865), (4280, 4280, 103154254503632540), (4281, 4281, 102132925251121326), (4282, 4282, 101121708169427056), (4283, 4283, 100120503138046590), (4284, 4284, 99129211027768901), (4285, 4285, 98147733690860298), (4286, 4286, 97175973951346830), (4287, 4287, 96213835595392901), (4288, 4288, 95261223361775149), (4289, 4289, 94318042932450643), (4290, 4290, 93384200923218458), (4291, 4291, 92459604874473721), (4292, 4292, 91544163242053189), (4293, 4293, 90637785388171474), (4294, 4294, 89740381572447004), (4295, 4295, 88851862943016836), (4296, 4296, 87972141527739441), (4297, 4297, 87101130225484596), (4298, 4298, 86238742797509501), (4299, 4299, 85384893858920298), (4300, 4300, 84539498870218116), (4301, 4301, 83702474128928828), (4302, 4302, 82873736761315671), (4303, 4303, 82053204714173932), (4304, 4304, 81240796746706863), (4305, 4305, 80436432422482043), (4306, 4306, 79640032101467369), (4307, 4307, 78851516932145910), (4308, 4308, 78070808843708822), (4309, 4309, 77297830538325566), (4310, 4310, 76532505483490660), (4311, 4311, 75774757904446198), (4312, 4312, 75024512776679404), (4313, 4313, 74281695818494459), (4314, 4314, 73546233483657880), (4315, 4315, 72818052954116713), (4316, 4316, 72097082132788825), (4317, 4317, 71383249636424579), (4318, 4318, 70676484788539187), (4319, 4319, 69976717612415037), (4320, 4320, 69283878824173304), (4321, 4321, 68597899825914162), (4322, 4322, 67918712698924913), (4323, 4323, 67246250196955360), (4324, 4324, 66580445739559762), (4325, 4325, 65921233405504715), (4326, 4326, 65268547926242292), (4327, 4327, 64622324679447814), (4328, 4328, 63982499682621598), (4329, 4329, 63349009586754057), (4330, 4330, 62721791670053522), (4331, 4331, 62100783831736160), (4332, 4332, 61485924585877387), (4333, 4333, 60877153055324145), (4334, 4334, 60274408965667470), (4335, 4335, 59677632639274723), (4336, 7209, 59086764989380914)]

def glob1 : ℕ := 8116567392432202712

def runs2 : List (ℕ × ℕ × ℕ) := [(0, 3828, 0), (3829, 3841, 41924418349339890037), (3842, 3842, 41623970834807572767), (3843, 3843, 41211852311690666106), (3844, 3844, 40803814169990758520), (3845, 3845, 40399816009891840119), (3846, 3846, 39999817831576079326), (3847, 3847, 39603780031263444877), (3848, 3848, 39211663397290539482), (3849, 3849, 38823429106228256913), (3850, 3850, 38439038719037878132), (3851, 3851, 38058454177265225873), (3852, 3852, 37681637799272500865), (3853, 3853, 37308552276507426599), (3854, 3854, 36939160669809333266), (3855, 3855, 36573426405751815115), (3856, 3856, 36211313273021599124), (3857, 3857, 35852785418833266459), (3858, 3858, 35497807345379471742), (3859, 3859, 35146343906316308655), (3860, 3860, 34798360303283473916), (3861, 3861, 34453822082458885065), (3862, 3862, 34112695131147410956), (3863, 3863, 33774945674403377184), (3864, 3864, 33440540271686512063), (3865, 3865, 33109445813551002043), (3866, 3866, 32781629518367328755), (3867, 3867, 32457058929076563124), (3868, 3868, 32135701909976795172), (3869, 3869, 31817526643541381359), (3870, 3870, 31502501627268694415), (3871, 3871, 31190595670563063777), (3872, 3872, 30881777891646597799), (3873, 3873, 30576017714501581979), (3874, 3874, 30273284865843150474), (3875, 3875, 29973549372121931163), (3876, 3876, 29676781556556367488), (3877, 3877, 29382952036194423255), (3878, 3878, 29092031719004379461), (3879, 3879, 28803991800994435110), (3880, 3880, 28518803763360826841), (3881, 3881, 28236439369664184991), (3882, 3882, 27956870663033846526), (3883, 3883, 27680069963399848046), (3884, 3884, 27406009864752324798), (3885, 3885, 27134663232428044354), (3886, 3886, 26866003200423806291), (3887, 3887, 26600003168736441872), (3888, 3888, 26336636800729150369), (3889, 3889, 26075878020523911256), (3890, 3890, 25817701010419714115), (3891, 3891, 25562080208336350609), (3892, 3892, 25308990305283515454), (3893, 3893, 25058406242854965796), (3894, 3894, 24810303210747490888), (3895, 3895, 24564656644304446423), (3896, 3896, 24321442222083610320), (3897, 3897, 24080635863449119129), (3898, 3898, 23842213726187246662), (3899, 3899, 23606152204145788774), (3900, 3900, 23372427924896820569), (3901, 3901, 23141017747422594623), (3902, 3902, 22911898759824351111), (3903, 3903, 22685048277053812982), (3904, 3904, 22460443838667141566), (3905, 3905, 22238063206601130263), (3906, 3906, 22017884362971416102), (3907, 3907, 21799885507892491190), (3908, 3908, 21584045057319298208), (3909, 3909, 21370341640910196246), (3910, 3910, 21158754099911085392), (3911, 3911, 20949261485060480586), (3912, 3912, 20741843054515327313), (3913, 3913, 20536478271797353775), (3914, 3914, 20333146803759756213), (3915, 3915, 20131828518574016053), (3916, 3916, 19932503483736649557), (3917, 3917, 19735151964095692631), (3918, 3918, 19539754419896725377), (3919, 3919, 19346291504848242948), (3920, 3920, 19154744064206181136), (3921, 3921, 18965093132877407066), (3922, 3922, 18777319933541987194), (3923, 3923, 18591405874794046726), (3924, 3924, 18407332549301036363), (3925, 3925, 18225081731981224121), (3926, 3926, 18044635378199231803), (3927, 3927, 17865975621979437429), (3928, 3928, 17689084774237066762), (3929, 3929, 17513945321026798774), (3930, 3930, 17340539921808711657), (3931, 3931, 17168851407731397680), (3932, 3932, 16998862779932076911), (3933, 3933, 16830557207853541496), (3934, 3934, 16663918027577763858), (3935, 3935, 16498928740176003820), (3936, 3936, 16335573010075251307), (3937, 3937, 16173834663440842878), (3938, 3938, 16013697686575091958), (3939, 3939, 15855146224331774216), (3940, 3940, 15698164578546311105), (3941, 3941, 15542737206481496144), (3942, 3942, 15388848719288610043), (3943, 3943, 15236483880483772320), (3944, 3944, 15085627604439378535), (3945, 3945, 14936264954890473797), (3946, 3946, 14788381143455914650), (3947, 3947, 14641961528174172921), (3948, 3948, 14496991612053636555), (3949, 3949, 14353457041637263916), (3950, 3950, 14211343605581449422), (3951, 3951, 14070637233248959824), (3952, 3952, 13931323993315801806), (3953, 3953, 13793390092391882976), (3954, 3954, 13656821873655329679), (3955, 3955, 13521605815500326415), (3956, 3956, 13387728530198342985), (3957, 3957, 13255176762572616817), (3958, 3958, 13123937388685759225), (3959, 3959, 12993997414540355668), (3960, 3960, 12865343974792431355), (3961, 3961, 12737964331477654807), (3962, 3962, 12611845872750153274), (3963, 3963, 12486976111633815123), (3964, 3964, 12363342684785955567), (3965, 3965, 12240933351273223334), (3966, 3966, 12119735991359627063), (3967, 3967, 11999738605306561448), (3968, 3968, 11880929312184714305), (3969, 3969, 11763296348697736936), (3970, 3970, 11646828068017561323), (3971, 3971, 11531512938631248835), (3972, 3972, 11417339543199256272), (3973, 3973, 11304296577425006210), (3974, 3974, 11192372848935649713), (3975, 3975, 11081557276173910607), (3976, 3976, 10971838887300901591), (3977, 3977, 10863206819109803555), (3978, 3978, 10755650315950300550), (3979, 3979, 10649158728663663910), (3980, 3980, 10543721513528380109), (3981, 3981, 10439328231216217930), (3982, 3982, 10335968545758631614), (3983, 3983, 10233632223523397638), (3984, 3984, 10132309132201383800), (3985, 3985, 10031989239803350297), (3986, 3986, 9932662613666683462), (3987, 3987, 9834319419471963824), (3988, 3988, 9736949920269271113), (3989, 3989, 9640544475514129815), (3990, 3990, 9545093540112999816), (3991, 3991, 9450587663478217640), (3992, 3992, 9357017488592294693), (3993, 3993, 9264373751081479894), (3994, 3994, 9172647278298494945), (3995, 3995, 9081828988414351430), (3996, 3996, 8991909889519159832), (3997, 3997, 8902881078731841418), (3998, 3998, 8814733741318654869), (3999, 3999, 8727459149820450366), (4000, 4000, 8641048663188564718), (4001, 4001, 8555493725929271998), (4002, 4002, 8470785867256704949), (4003, 4003, 8386916700254163316), (4004, 4004, 8303877921043726055), (4005, 4005, 8221661307964085203), (4006, 4006, 8140258720756520003), (4007, 4007, 8059662099758930696), (4008, 4008, 7979863465107852174), (4009, 4009, 7900854915948368490), (4010, 4010, 7822628629651849990), (4011, 4011, 7745176861041435633), (4012, 4012, 7668491941625183795), (4013, 4013, 7592566278836815639), (4014, 4014, 7517392355283975880), (4015, 4015, 7442962728003936515), (4016, 4016, 7369270027726669817), (4017, 4017, 7296306958145217641), (4018, 4018, 7224066295193284793), (4019, 4019, 7152540886329984943), (4020, 4020, 7081723649831668261), (4021, 4021, 7011607574090760654), (4022, 4022, 6942185716921545202), (4023, 4023, 6873451204872817032), (4024, 4024, 6805397232547343596), (4025, 4025, 6738017061928062966), (4026, 4026, 6671304021710953432), (4027, 4027, 6605251506644508348), (4028, 4028, 6539852976875750840), (4029, 4029, 6475101957302723604), (4030, 4030, 6410992036933389707), (4031, 4031, 6347516868250880898), (4032, 4032, 6284670166585030592), (4033, 4033, 6222445709490129299), (4034, 4034, 6160837336128840890), (4035, 4035, 6099838946662218703), (4036, 4036, 6039444501645761092), (4037, 4037, 5979648021431446626), (4038, 4038, 5920443585575689729), (4039, 4039, 5861825332253158147), (4040, 4040, 5803787457676394205), (4041, 4041, 5746324215521182381), (4042, 4042, 5689429916357606318), (4043, 4043, 5633098927086738929), (4044, 4044, 5577325670382909830), (4045, 4045, 5522104624141494882), (4046, 4046, 5467430320932173150), (4047, 4047, 5413297347457597178), (4048, 4048, 5359700344017422949), (4049, 4049, 5306634003977646484), (4050, 4050, 5254093073245194539), (4051, 4051, 5202072349747717365), (4052, 4052, 5150566682918532045), (4053, 4053, 5099570973186665391), (4054, 4054, 5049080171471945931), (4055, 4055, 4999089278685094982), (4056, 4056, 4949593345232767309), (4057, 4057, 4900587470527492385), (4058, 4058, 4852066802502467708), (4059, 4059, 4804026537131156146), (4060, 4060, 4756461917951639749), (4061, 4061, 4709368235595682919), (4062, 4062, 4662740827322458336), (4063, 4063, 4616575076556889442), (4064, 4064, 4570866412432563804), (4065, 4065, 4525610309339172083), (4066, 4066, 4480802286474427805), (4067, 4067, 4436437907400423569), (4068, 4068, 4392512779604379771), (4069, 4069, 4349022554063742348), (4070, 4070, 4305962924815586483), (4071, 4071, 4263329628530283647), (4072, 4072, 4221118444089389749), (4073, 4073, 4179325192167712623), (4074, 4074, 4137945734819517448), (4075, 4075, 4096975975068829157), (4076, 4076, 4056411856503791244), (4077, 4077, 4016249362875040836), (4078, 4078, 3976484517698060234), (4079, 4079, 3937113383859465578), (4080, 4080, 3898132063227193642), (4081, 4081, 3859536696264548160), (4082, 4082, 3821323461648067485), (4083, 4083, 3783488575889175728), (4084, 4084, 3746028292959579929), (4085, 4085, 3708938903920376167), (4086, 4086, 3672216736554827888), (4087, 4087, 3635858155004780087), (4088, 4088, 3599859559410673354), (4089, 4089, 3564217385555122132), (4090, 4090, 3528928104510021913), (4091, 4091, 3493988222287150409), (4092, 4092, 3459394279492228128), (4093, 4093, 3425142850982404087), (4094, 4094, 3391230545527132759), (4095, 4095, 3357654005472408673), (4096, 4096, 3324409906408325418), (4097, 4097, 3291494956839926157), (4098, 4098, 3258905897861313027), (4099, 4099, 3226639502832983195), (4100, 4100, 3194692577062359599), (4101, 4101, 3163061957487484751), (4102, 4102, 3131744512363846288), (4103, 4103, 3100737140954303256), (4104, 4104, 3070036773222082431), (4105, 4105, 3039640369526814289), (4106, 4106, 3009544920323578504), (4107, 4107, 2979747445864929211), (4108, 4108, 2950244995905870506), (4109, 4109, 2921034649411752977), (4110, 4110, 2892113514269062353), (4111, 4111, 2863478726999071637), (4112, 4112, 2835127452474328353), (4113, 4113, 2807056883637948865), (4114, 4114, 2779264241225691945), (4115, 4115, 2751746773490784104), (4116, 4116, 2724501755931469410), (4117, 4117, 2697526491021256842), (4118, 4118, 2670818307941838457), (4119, 4119, 2644374562318651938), (4120, 4120, 2618192635959061324), (4121, 4121, 2592269936593130024), (4122, 4122, 2566603897616960420), (4123, 4123, 2541191977838574673), (4124, 4124, 2516031661226311558), (4125, 4125, 2491120456659714414), (4126, 4126, 2466455897682885558), (4127, 4127, 2442035542260282731), (4128, 4128, 2417856972534933397), (4129, 4129, 2393917794589042967), (4130, 4130, 2370215638206973235), (4131, 4131, 2346748156640567559), (4132, 4132, 2323513026376799563), (4133, 4133, 2300507946907722340), (4134, 4134, 2277730640502695386), (4135, 4135, 2255178851982866719), (4136, 4136, 2232850348497887841), (4137, 4137, 2210742919304839446), (4138, 4138, 2188854375549345986), (4139, 4139, 2167182550048857412), (4140, 4140, 2145725297078076646), (4141, 4141, 2124480492156511530), (4142, 4142, 2103446031838130228), (4143, 4143, 2082619833503099236), (4144, 4144, 2061999835151583402), (4145, 4145, 2041583995199587527), (4146, 4146, 2021370292276819333), (4147, 4147, 2001356725026553795), (4148, 4148, 1981541311907479005), (4149, 4149, 1961922090997503966), (4150, 4150, 1942497119799508877), (4151, 4151, 1923264475049018690), (4152, 4152, 1904222252523780881), (4153, 4153, 1885368566855228595), (4154, 4154, 1866701551341810490), (4155, 4155, 1848219357764168802), (4156, 4156, 1829920156202147329), (4157, 4157, 1811802134853611217), (4158, 4158, 1793863499855060611), (4159, 4159, 1776102475104020407), (4160, 4160, 1758517302083188521), (4161, 4161, 1741106239686325269), (4162, 4162, 1723867564045866603), (4163, 4163, 1706799568362244161), (4164, 4164, 1689900562734895209), (4165, 4165, 1673168873994945752), (4166, 4166, 1656602845539550249), (4167, 4167, 1640200837167871534), (4168, 4168, 1623961224918684687), (4169, 4169, 1607882400909588799), (4170, 4170, 1591962773177810692), (4171, 4171, 1576200765522584844), (4172, 4172, 1560594817349093904), (4173, 4173, 1545143383513954361), (4174, 4174, 1529844934172232040), (4175, 4175, 1514697954625972317), (4176, 4176, 1499700945174230017), (4177, 4177, 1484852420964584175), (4178, 4178, 1470150911846122946), (4179, 4179, 1455594962223884105), (4180, 4180, 1441183130914736738), (4181, 4181, 1426913991004689839), (4182, 4182, 1412786129707613702), (4183, 4183, 1398798148225360101), (4184, 4184, 1384948661609267427), (4185, 4185, 1371236298623037056), (4186, 4186, 1357659701606967382), (4187, 4187, 1344217526343532062), (4188, 4188, 1330908441924289170), (4189, 4189, 1317731130618108089), (4190, 4190, 1304684287740701079), (4191, 4191, 1291766621525446612), (4192, 4192, 1278976852995491695), (4193, 4193, 1266313715837120491), (4194, 4194, 1253775956274376723), (4195, 4195, 1241362332944927449), (4196, 4196, 1229071616777155890), (4197, 4197, 1216902590868471178), (4198, 4198, 1204854050364822949), (4199, 4199, 1192924802341408860), (4200, 4200, 1181113665684563228), (4201, 4201, 1169419470974815077), (4202, 4202, 1157841060371104037), (4203, 4203, 1146377287496142611), (4204, 4204, 1135027017322913476), (4205, 4205, 1123789126062290570), (4206, 4206, 1112662501051772842), (4207, 4207, 1101646040645319645), (4208, 4208, 1090738654104276877), (4209, 4209, 1079939261489383046), (4210, 4210, 1069246793553844600), (4211, 4211, 1058660191637469901), (4212, 4212, 1048178407561851387), (4213, 4213, 1037800403526585532), (4214, 4214, 1027525152006520329), (4215, 4215, 1017351635650020127), (4216, 4216, 1007278847178237750), (4217, 4217, 997305789285383911), (4218, 4218, 987431474539984070), (4219, 4219, 977654925287112941), (4220, 4220, 967975173551596971), (4221, 4221, 958391260942175219), (4222, 4222, 948902238556609127), (4223, 4223, 939507166887731809), (4224, 4224, 930205115730427534), (4225, 4225, 920995164089532212), (4226, 4226, 911876400088645754), (4227, 4227, 902847920879847282), (4228, 4228, 893908832554304239), (4229, 4229, 885058250053766573), (4230, 4230, 876295297082937201), (4231, 4231, 867619106022710100), (4232, 4232, 859028817844267426), (4233, 4233, 850523582024027155), (4234, 4234, 842102556459432826), (4235, 4235, 833764907385577056), (4236, 4236, 825509809292650550), (4237, 4237, 817336444844208466), (4238, 4238, 809244004796246006), (4239, 4239, 801231687917075253), (4240, 4240, 793298700907995300), (4241, 4241, 785444258324747822), (4242, 4242, 777667582499750319), (4243, 4243, 769967903465099325), (4244, 4244, 762344458876335966), (4245, 4245, 754796493936966303), (4246, 4246, 747323261323729013), (4247, 4247, 739924021112602983), (4248, 4248, 732598040705547508), (4249, 4249, 725344594757967829), (4250, 4250, 718162965106898841), (4251, 4251, 711052440699899843), (4252, 4252, 704012317524653310), (4253, 4253, 697041898539260703), (4254, 4254, 690140493603228418), (4255, 4255, 683307419409137048), (4256, 4256, 676541999414987176), (4257, 4257, 669843563777215026), (4258, 4258, 663211449284371313), (4259, 4259, 656644999291456745), (4260, 4260, 650143563654907669), (4261, 4261, 643706498668225414), (4262, 4262, 637333166998242985), (4263, 4263, 631022937622022757), (4264, 4264, 624775185764378967), (4265, 4265, 618589292836018780), (4266, 4266, 612464646372295821), (4267, 4267, 606400639972570120), (4268, 4268, 600396673240168436), (4269, 4269, 594452151722939045), (4270, 4270, 588566486854395094), (4271, 4271, 582739095895440688), (4272, 4272, 576969401876673948), (4273, 4273, 571256833541261335), (4274, 4274, 565600825288377559), (4275, 4275, 560000817117205504), (4276, 4276, 554456254571490598), (4277, 4277, 548966588684644157), (4278, 4278, 543531275925390254), (4279, 4279, 538149778143950747), (4280, 4280, 532821562518763115), (4281, 4281, 527546101503725857), (4282, 4282, 522322872775966195), (4283, 4283, 517151359184124946), (4284, 4284, 512031048697153411), (4285, 4285, 506961434353617239), (4286, 4286, 501942014211502217), (4287, 4287, 496972291298517046), (4288, 4288, 492051773562888165), (4289, 4289, 487179973824641747), (4290, 4290, 482356409727368067), (4291, 4291, 477580603690463432), (4292, 4292, 472852082861844982), (4293, 4293, 468170379071133646), (4294, 4294, 463535028783300640), (4295, 4295, 458945573052772911), (4296, 4296, 454401557477992981), (4297, 4297, 449902532156428694), (4298, 4298, 445448051640028410), (4299, 4299, 441037674891117237), (4300, 4300, 436670965238729938), (4301, 4301, 432347490335376176), (4302, 4302, 428066822114233838), (4303, 4303, 423828536746766176), (4304, 4304, 419632214600758590), (4305, 4305, 415477440198770881), (4306, 4306, 411363802177000873), (4307, 4307, 407290893244555319), (4308, 4308, 403258310143124079), (4309, 4309, 399265653607053543), (4310, 4310, 395312528323815389), (4311, 4311, 391398542894866722), (4312, 4312, 387523309796897745), (4313, 4313, 383686445343463114), (4314, 4314, 379887569646993182), (4315, 4315, 376126306581181368), (4316, 4316, 372402283743743929), (4317, 4317, 368715132419548444), (4318, 4318, 365064487544107371), (4319, 4319, 361449987667433040), (4320, 4320, 357871274918250535), (4321, 4321, 354327994968564886), (4322, 4322, 350819796998579095), (4323, 4323, 347346333661959500), (4324, 4324, 343907261051445050), (4325, 4325, 340502238664797079), (4326, 4326, 337130929371086217), (4327, 4327, 333792999377313086), (4328, 4328, 330488118195359491), (4329, 4329, 327215958609266823), (4330, 4330, 323976196642838438), (4331, 4331, 320768511527562810), (4332, 4332, 317592585670854268), (4333, 4333, 314448104624608186), (4334, 4334, 311334757054067511), (4335, 4335, 308252234706997535), (4336, 7209, 305200232383165877)]

def glob2 : ℕ := 41924418349339890037

def runs3 : List (ℕ × ℕ × ℕ) := [(0, 3828, 0), (3829, 3829, 132196906394219599), (3830, 3830, 313529056565658530), (3831, 3831, 493065838913617868), (3832, 3832, 670825029357141964), (3833, 3833, 846824227816076713), (3834, 3834, 1021080859953635871), (3835, 3835, 1193612178901714244), (3836, 3836, 1364435266969118575), (3837, 3837, 1533567037332885239), (3838, 3838, 1701024235712852233), (3839, 3839, 1866823442029651236), (3840, 3840, 2030981072046283913), (3841, 3841, 2193513378993444980), (3842, 3842, 2354436455178752966), (3843, 3843, 2513766233580048002), (3844, 3844, 2671518489422914375), (3845, 3845, 2827708841742584050), (3846, 3846, 2982352754930375809), (3847, 3847, 3135465540264823094), (3848, 3848, 3287062357427642188), (3849, 3849, 3437158216004690796), (3850, 3850, 3585767976972065656), (3851, 3851, 3732906354167486309), (3852, 3852, 3878587915747110718), (3853, 3853, 4022827085627926964), (3854, 3854, 4165638144915863842), (3855, 3855, 4307035233319761741), (3856, 3856, 4447032350551343819), (3857, 3857, 4585643357711326074), (3858, 3858, 4722881978661803555), (3859, 3859, 4858761801385048585), (3860, 3860, 4993296279328855546), (3861, 3861, 5126498732738565408), (3862, 3862, 5258382349975901905), (3863, 3863, 5388960188824749922), (3864, 3864, 5518245177784005384), (3865, 3865, 5646250117347624654), (3866, 3866, 5772987681272000169), (3867, 3867, 5898470417830787807), (3868, 3868, 6022710751057310221), (3869, 3869, 6145720981974659145), (3870, 3870, 6267513289813618477), (3871, 3871, 6388099733218528706), (3872, 3872, 6507492251441212101), (3873, 3873, 6625702665523076849), (3874, 3874, 6742742679465517193), (3875, 3875, 6858623881388725454), (3876, 3876, 6973357744679030664), (3877, 3877, 7086955629124877406), (3878, 3878, 7199428782041557349), (3879, 3879, 7310788339384804817), (3880, 3880, 7421045326853366666), (3881, 3881, 7530210660980655626), (3882, 3882, 7638295150215595190), (3883, 3883, 7745309495992763076), (3884, 3884, 7851264293791939200), (3885, 3885, 7956170034187163085), (3886, 3886, 8060037103885404556), (3887, 3887, 8162875786754950566), (3888, 3888, 8264696264843609983), (3889, 3889, 8365508619386837128), (3890, 3890, 8465322831805873905), (3891, 3891, 8564148784696009328), (3892, 3892, 8661996262805054301), (3893, 3893, 8758874954002128532), (3894, 3894, 8854794450236855493), (3895, 3895, 8949764248489060405), (3896, 3896, 9043793751709065269), (3897, 3897, 9136892269748674044), (3898, 3898, 9229069020282940159), (3899, 3899, 9320333129722807599), (3900, 3900, 9410693634118715956), (3901, 3901, 9500159480055258883), (3902, 3902, 9588739525536984554), (3903, 3903, 9676442540865425812), (3904, 3904, 9763277209507446859), (3905, 3905, 9849252128954992451), (3906, 3906, 9934375811576324720), (3907, 3907, 10018656685458831917), (3908, 3908, 10102103095243492508), (3909, 3909, 10184723302951077252), (3910, 3910, 10266525488800171057), (3911, 3911, 10347517752017095617), (3912, 3912, 10427708111637813003), (3913, 3913, 10507104507301889623), (3914, 3914, 10585714800038599148), (3915, 3915, 10663546773045242242), (3916, 3916, 10740608132457760156), (3917, 3917, 10816906508113718488), (3918, 3918, 10892449454307736637), (3919, 3919, 10967244450539437776), (3920, 3920, 11041298902253993358), (3921, 3921, 11114620141575335519), (3922, 3922, 11187215428032109936), (3923, 3923, 11259091949276441042), (3924, 3924, 11330256821795580750), (3925, 3925, 11400717091616511155), (3926, 3926, 11470479735003570962), (3927, 3927, 11539551659149174731), (3928, 3928, 11607939702857693314), (3929, 3929, 11675650637222563198), (3930, 3930, 11742691166296691796), (3931, 3931, 11809067927756225061), (3932, 3932, 11874787493557743146), (3933, 3933, 11939856370588949171), (3934, 3934, 12004281001312915531), (3935, 3935, 12068067764405951532), (3936, 3936, 12131222975389155494), (3937, 3937, 12193752887253713871), (3938, 3938, 12255663691080009294), (3939, 3939, 12316961516650598822), (3940, 3940, 12377652433057123107), (3941, 3941, 12437742449301206558), (3942, 3942, 12497237514889407994), (3943, 3943, 12556143520422280703), (3944, 3944, 12614466298177600217), (3945, 3945, 12672211622687817558), (3946, 3946, 12729385211311795123), (3947, 3947, 12785992724800881821), (3948, 3948, 12842039767859383502), (3949, 3949, 12897531889699484176), (3950, 3950, 12952474584590672963), (3951, 3951, 13006873292403731167), (3952, 3952, 13060733399149333350), (3953, 3953, 13114060237511315709), (3954, 3954, 13166859087374664579), (3955, 3955, 13219135176348277322), (3956, 3956, 13270893680282547365), (3957, 3957, 13322139723781824635), (3958, 3958, 13372878380711802130), (3959, 3959, 13423114674701878857), (3960, 3960, 13472853579642548884), (3961, 3961, 13522100020177865743), (3962, 3962, 13570858872193030950), (3963, 3963, 13619134963297154917), (3964, 3964, 13666933073301238052), (3965, 3965, 13714257934691419375), (3966, 3966, 13761114233097539496), (3967, 3967, 13807506607757064369), (3968, 3968, 13853439651974415727), (3969, 3969, 13898917913575753707), (3970, 3970, 13943945895359256656), (3971, 3971, 13988528055540942745), (3972, 3972, 14032668808196077486), (3973, 3973, 14076372523696210893), (3974, 3974, 14119643529141887534), (3975, 3975, 14162486108791072327), (3976, 3976, 14204904504483334498), (3977, 3977, 14246902916059831698), (3978, 3978, 14288485501779135855), (3979, 3979, 14329656378728941952), (3980, 3980, 14370419623233700463), (3981, 3981, 14410779271258213841), (3982, 3982, 14450739318807236987), (3983, 3983, 14490303722321121291), (3984, 3984, 14529476399067541393), (3985, 3985, 14568261227529343474), (3986, 3986, 14606662047788553456), (3987, 3987, 14644682661906583141), (3988, 3988, 14682326834300671937), (3989, 3989, 14719598292116601439), (3990, 3990, 14756500725597719758), (3991, 3991, 14793037788450312152), (3992, 3992, 14829213098205354127), (3993, 3993, 14865030236576682815), (3994, 3994, 14900492749815622110), (3995, 3995, 14935604149062096660), (3996, 3996, 14970367910692269481), (3997, 3997, 15004787476662737621), (3998, 3998, 15038866254851319938), (3999, 3999, 15072607619394470747), (4000, 4000, 15106014911021352736), (4001, 4001, 15139091437384602229), (4002, 4002, 15171840473387819550), (4003, 4003, 15204265261509816897), (4004, 4004, 15236369012125655855), (4005, 4005, 15268154903824506308), (4006, 4006, 15299626083724358242), (4007, 4007, 15330785667783617582), (4008, 4008, 15361636741109616929), (4009, 4009, 15392182358264071728), (4010, 4010, 15422425543565512123), (4011, 4011, 15452369291388720435), (4012, 4012, 15482016566461203912), (4013, 4013, 15511370304156732107), (4014, 4014, 15540433410785967943), (4015, 4015, 15569208763884221247), (4016, 4016, 15597699212496353231), (4017, 4017, 15625907577458860146), (4018, 4018, 15653836651679164022), (4019, 4019, 15681489200412138156), (4020, 4020, 15708867961533894725), (4021, 4021, 15735975645812861625), (4022, 4022, 15762814937178175387), (4023, 4023, 15789388492985416736), (4024, 4024, 15815698944279715101), (4025, 4025, 15841748896056248136), (4026, 4026, 15867540927518162032), (4027, 4027, 15893077592331938166), (4028, 4028, 15918361418880231369), (4029, 4029, 15943394910512204837), (4030, 4030, 15968180545791386488), (4031, 4031, 15992720778741071291), (4032, 4032, 16017018039087293869), (4033, 4033, 16041074732499395431), (4034, 4034, 16064893240828208858), (4035, 4035, 16088475922341885519), (4036, 4036, 16111825111959387164), (4037, 4037, 16134943121481666020), (4038, 4038, 16157832239820555976), (4039, 4039, 16180494733225397517), (4040, 4040, 16202932845507418845), (4041, 4041, 16225148798261895407), (4042, 4042, 16247144791088109825), (4043, 4043, 16268923001807134001), (4044, 4044, 16290485586677454967), (4045, 4045, 16311834680608465825), (4046, 4046, 16332972397371842912), (4047, 4047, 16353900829810830127), (4048, 4048, 16374622050047451132), (4049, 4049, 16395138109687669949), (4050, 4050, 16415451040024520262), (4051, 4051, 16435562852239223543), (4052, 4052, 16455475537600315900), (4053, 4053, 16475191067660803383), (4054, 4054, 16494711394453365246), (4055, 4055, 16514038450683624517), (4056, 4056, 16533174149921504984), (4057, 4057, 16552120386790693564), (4058, 4058, 16570879037156226812), (4059, 4059, 16589451958310220127), (4060, 4060, 16607840989155758063), (4061, 4061, 16626047950388963939), (4062, 4062, 16644074644679266788), (4063, 4063, 16661922856847883469), (4064, 4064, 16679594354044533649), (4065, 4065, 16697090885922405114), (4066, 4066, 16714414184811386762), (4067, 4067, 16731565965889586414), (4068, 4068, 16748547927353150426), (4069, 4069, 16765361750584401923), (4070, 4070, 16782009100318314296), (4071, 4071, 16798491624807336448), (4072, 4072, 16814810955984586103), (4073, 4073, 16830968709625427346), (4074, 4074, 16846966485507448378), (4075, 4075, 16862805867568855341), (4076, 4076, 16878488424065297878), (4077, 4077, 16894015707725141975), (4078, 4078, 16909389255903205437), (4079, 4079, 16924610590732971240), (4080, 4080, 16939681219277293818), (4081, 4081, 16954602633677613203), (4082, 4082, 16969376311301691801), (4083, 4083, 16984003714889888433), (4084, 4084, 16998486292699984108), (4085, 4085, 17012825478650573885), (4086, 4086, 17027022692463039011), (4087, 4087, 17041079339802113393), (4088, 4088, 17054996812415058326), (4089, 4089, 17068776488269459250), (4090, 4090, 17082419731689658184), (4091, 4091, 17095927893491835347), (4092, 4092, 17109302311117753330), (4093, 4093, 17122544308767177075), (4094, 4094, 17135655197528982764), (4095, 4095, 17148636275510968594), (4096, 4096, 17161488827968380307), (4097, 4097, 17174214127431164181), (4098, 4098, 17186813433829960097), (4099, 4099, 17199287994620847141), (4100, 4100, 17211639044908854116), (4101, 4101, 17223867807570247161), (4102, 4102, 17235975493373606611), (4103, 4103, 17247963301099705076), (4104, 4104, 17259832417660198606), (4105, 4105, 17271584018215142696), (4106, 4106, 17283219266289344764), (4107, 4107, 17294739313887564634), (4108, 4108, 17306145301608574406), (4109, 4109, 17317438358758089032), (4110, 4110, 17328619603460578760), (4111, 4111, 17339690142769974531), (4112, 4112, 17350651072779277275), (4113, 4113, 17361503478729081971), (4114, 4114, 17372248435115027215), (4115, 4115, 17382887005794180922), (4116, 4116, 17393420244090372711), (4117, 4117, 17403849192898483393), (4118, 4118, 17414174884787701891), (4119, 4119, 17424398342103759809), (4120, 4120, 17434520577070153787), (4121, 4121, 17444542591888365647), (4122, 4122, 17454465378837090260), (4123, 4123, 17464289920370480967), (4124, 4124, 17474017189215422260), (4125, 4125, 17483648148467839383), (4126, 4126, 17493183751688054355), (4127, 4127, 17502624942995197893), (4128, 4128, 17511972657160686543), (4129, 4129, 17521227819700774316), (4130, 4130, 17530391346968187953), (4131, 4131, 17539464146242854920), (4132, 4132, 17548447115821733105), (4133, 4133, 17557341145107751110), (4134, 4134, 17566147114697867947), (4135, 4135, 17574865896470260854), (4136, 4136, 17583498353670649872), (4137, 4137, 17592045340997767711), (4138, 4138, 17600507704687983393), (4139, 4139, 17608886282599088029), (4140, 4140, 17617181904293251035), (4141, 4141, 17625395391119155001), (4142, 4142, 17633527556293317344), (4143, 4143, 17641579204980606792), (4144, 4144, 17649551134373962681), (4145, 4145, 17657444133773324948), (4146, 4146, 17665258984663782638), (4147, 4147, 17672996460792948667), (4148, 4148, 17680657328247568498), (4149, 4149, 17688242345529370312), (4150, 4150, 17695752263630164186), (4151, 4151, 17703187826106197725), (4152, 4152, 17710549769151775486), (4153, 4153, 17717838821672149507), (4154, 4154, 17725055705355688142), (4155, 4155, 17732201134745330355), (4156, 4156, 17739275817309332545), (4157, 4157, 17746280453511314912), (4158, 4158, 17753215736879614286), (4159, 4159, 17760082354075950299), (4160, 4160, 17766880984963411698), (4161, 4161, 17773612302673769519), (4162, 4162, 17780276973674123797), (4163, 4163, 17786875657832890409), (4164, 4164, 17793409008485134580), (4165, 4165, 17799877672497257521), (4166, 4166, 17806282290331042611), (4167, 4167, 17812623496107067452), (4168, 4168, 17818901917667488087), (4169, 4169, 17825118176638201588), (4170, 4170, 17831272888490393172), (4171, 4171, 17837366662601473949), (4172, 4172, 17843400102315415312), (4173, 4173, 17849373805002485968), (4174, 4174, 17855288362118397509), (4175, 4175, 17861144359262864382), (4176, 4176, 17866942376237584057), (4177, 4177, 17872682987103643142), (4178, 4178, 17878366760238355107), (4179, 4179, 17883994258391535271), (4180, 4180, 17889566038741218601), (4181, 4181, 17895082652948825858), (4182, 4182, 17900544647213783539), (4183, 4183, 17905952562327603025), (4184, 4184, 17911306933727424298), (4185, 4185, 17916608291549029519), (4186, 4186, 17921857160679331718), (4187, 4187, 17927054060808343796), (4188, 4188, 17932199506480632983), (4189, 4189, 17937294007146265841), (4190, 4190, 17942338067211248868), (4191, 4191, 17947332186087469687), (4192, 4192, 17952276858242143766), (4193, 4193, 17957172573246771566), (4194, 4194, 17962019815825610973), (4195, 4195, 17966819065903669791), (4196, 4196, 17971570798654223076), (4197, 4197, 17976275484545859993), (4198, 4198, 17980933589389064860), (4199, 4199, 17985545574382337006), (4200, 4200, 17990111896157853983), (4201, 4201, 17994633006826682672), (4202, 4202, 17999109354023542761), (4203, 4203, 18003541380951127007), (4204, 4204, 18007929526423982696), (4205, 4205, 18012274224911958626), (4206, 4206, 18016575906583221923), (4207, 4207, 18020834997346848950), (4208, 4208, 18025051918894994520), (4209, 4209, 18029227088744643601), (4210, 4210, 18033360920278949621), (4211, 4211, 18037453822788163502), (4212, 4212, 18041506201510157443), (4213, 4213, 18045518457670547485), (4214, 4214, 18049490988522418813), (4215, 4215, 18053424187385657751), (4216, 4216, 18057318443685894324), (4217, 4217, 18061174142993059248), (4218, 4218, 18064991667059559173), (4219, 4219, 18068771393858073949), (4220, 4220, 18072513697618979669), (4221, 4221, 18076218948867401173), (4222, 4222, 18079887514459897712), (4223, 4223, 18083519757620785375), (4224, 4224, 18087116037978099892), (4225, 4225, 18090676711599203374), (4226, 4226, 18094202131026038505), (4227, 4227, 18097692645310033685), (4228, 4228, 18101148600046662575), (4229, 4229, 18104570337409661476), (4230, 4230, 18107958196184907914), (4231, 4231, 18111312511803963792), (4232, 4232, 18114633616377286443), (4233, 4233, 18117921838727110851), (4234, 4234, 18121177504420006304), (4235, 4235, 18124400935799110713), (4236, 4236, 18127592452016045772), (4237, 4237, 18130752369062516127), (4238, 4238, 18133880999801595686), (4239, 4239, 18136978653998704161), (4240, 4240, 18140045638352276908), (4241, 4241, 18143082256524131113), (4242, 4242, 18146088809169531316), (4243, 4243, 18149065593966957259), (4244, 4244, 18152012905647577005), (4245, 4245, 18154931036024428239), (4246, 4246, 18157820274021310649), (4247, 4247, 18160680905701392243), (4248, 4248, 18163513214295532434), (4249, 4249, 18166317480230324703), (4250, 4250, 18169093981155861604), (4251, 4251, 18171842991973224871), (4252, 4252, 18174564784861703354), (4253, 4253, 18177259629305741455), (4254, 4254, 18179927792121620764), (4255, 4255, 18182569537483877505), (4256, 4256, 18185185126951458437), (4257, 4257, 18187774819493617775), (4258, 4258, 18190338871515557714), (4259, 4259, 18192877536883815080), (4260, 4260, 18195391066951396629), (4261, 4261, 18197879710582665491), (4262, 4262, 18200343714177981195), (4263, 4263, 18202783321698095754), (4264, 4264, 18205198774688308188), (4265, 4265, 18207590312302379905), (4266, 4266, 18209958171326213288), (4267, 4267, 18212302586201295846), (4268, 4268, 18214623789047912240), (4269, 4269, 18216922009688126491), (4270, 4270, 18219197475668536641), (4271, 4271, 18221450412282804116), (4272, 4272, 18223681042593960032), (4273, 4273, 18225889587456490641), (4274, 4274, 18228076265538204116), (4275, 4275, 18230241293341880824), (4276, 4276, 18232384885226709248), (4277, 4277, 18234507253429509667), (4278, 4278, 18236608608085747707), (4279, 4279, 18238689157250339824), (4280, 4280, 18240749106918252812), (4281, 4281, 18242788661044899335), (4282, 4282, 18244808021566331536), (4283, 4283, 18246807388419234705), (4284, 4284, 18248786959560722991), (4285, 4285, 18250746930987939116), (4286, 4286, 18252687496757460032), (4287, 4287, 18254608849004510444), (4288, 4288, 18256511177961986099), (4289, 4289, 18258394671979288728), (4290, 4290, 18260259517540974499), (4291, 4291, 18262105899285217837), (4292, 4292, 18263934000022092429), (4293, 4293, 18265744000751671233), (4294, 4294, 18267536080681947276), (4295, 4295, 18269310417246577022), (4296, 4296, 18271067186122448058), (4297, 4297, 18272806561247072845), (4298, 4298, 18274528714835810259), (4299, 4299, 18276233817398916609), (4300, 4300, 18277922037758427847), (4301, 4301, 18279593543064874617), (4302, 4302, 18281248498813831815), (4303, 4303, 18282887068862304288), (4304, 4304, 18284509415444950301), (4305, 4305, 18286115699190144374), (4306, 4306, 18287706079135881079), (4307, 4307, 18289280712745521381), (4308, 4308, 18290839755923383067), (4309, 4309, 18292383363030176815), (4310, 4310, 18293911686898289437), (4311, 4311, 18295424878846915795), (4312, 4312, 18296923088697040902), (4313, 4313, 18298406464786273681), (4314, 4314, 18299875153983533859), (4315, 4315, 18301329301703593441), (4316, 4316, 18302769051921474215), (4317, 4317, 18304194547186702704), (4318, 4318, 18305605928637423980), (4319, 4319, 18307003336014375739), (4320, 4320, 18308386907674724015), (4321, 4321, 18309756780605761912), (4322, 4322, 18311113090438472701), (4323, 4323, 18312455971460958631), (4324, 4324, 18313785556631736779), (4325, 4325, 18315101977592903263), (4326, 4326, 18316405364683167108), (4327, 4327, 18317695846950755073), (4328, 4328, 18318973552166188703), (4329, 4329, 18320238606834934870), (4330, 4330, 18321491136209931075), (4331, 4331, 18322731264303986724), (4332, 4332, 18323959113902061624), (4333, 4333, 18325174806573422911), (4334, 4334, 18326378462683681611), (4335, 4335, 18327570201406710027), (4336, 7209, 18446744073709506269)]

def glob3 : ℕ := 18446744073709551616

def runs4 : List (ℕ × ℕ × ℕ) := [(0, 3000, 175340596791948633717), (3001, 3001, 175341562430810215886), (3002, 3002, 175342537733257119199), (3003, 3003, 175343522796069911892), (3004, 3004, 175344517716999878509), (3005, 3005, 175345522594778785630), (3006, 3006, 175346537529128746427), (3007, 3007, 175347562620772185072), (3008, 3008, 175348597971441902013), (3009, 3009, 175349643683891241162), (3010, 3010, 175350699861904360016), (3011, 3011, 175351766610306603802), (3012, 3012, 175352844034974984671), (3013, 3013, 175353932242848767058), (3014, 3014, 175355031341940160265), (3015, 3015, 175356141441345119386), (3016, 3016, 175357262651254255682), (3017, 3017, 175358395082963857522), (3018, 3018, 175359538848887023035), (3019, 3019, 175360694062564905615), (3020, 3020, 175361860838678073442), (3021, 3021, 175363039293057984184), (3022, 3022, 175364229542698576069), (3023, 3023, 175365431705767976526), (3024, 3024, 175366645901620329596), (3025, 3025, 175367872250807743339), (3026, 3026, 175369110875092358477), (3027, 3027, 175370361897458539509), (3028, 3028, 175371625442125189571), (3029, 3029, 175372901634558190303), (3030, 3030, 175374190601482968026), (3031, 3031, 175375492470897187512), (3032, 3032, 175376807372083574682), (3033, 3033, 175378135435622869540), (3034, 3034, 175379476793406910709), (3035, 3035, 175380831578651852905), (3036, 3036, 175382199925911518731), (3037, 3037, 175383581971090886188), (3038, 3038, 175384977851459713276), (3039, 3039, 175386387705666301133), (3040, 3040, 175387811673751397118), (3041, 3041, 175389249897162239304), (3042, 3042, 175390702518766743821), (3043, 3043, 175392169682867836551), (3044, 3044, 175393651535217930650), (3045, 3045, 175395148223033551411), (3046, 3046, 175396659895010109997), (3047, 3047, 175398186701336827582), (3048, 3048, 175399728793711811457), (3049, 3049, 175401286325357284677), (3050, 3050, 175402859451034970845), (3051, 3051, 175404448327061635631), (3052, 3052, 175406053111324786662), (3053, 3053, 175407673963298533421), (3054, 3054, 175409311044059608818), (3055, 3055, 175410964516303554109), (3056, 3056, 175412634544361068860), (3057, 3057, 175414321294214527677), (3058, 3058, 175416024933514665429), (3059, 3059, 175417745631597432714), (3060, 3060, 175419483559501023347), (3061, 3061, 175421238889983075656), (3062, 3062, 175423011797538049391), (3063, 3063, 175424802458414780084), (3064, 3064, 175426611050634212702), (3065, 3065, 175428437754007316459), (3066, 3066, 175430282750153182688), (3067, 3067, 175432146222517307670), (3068, 3068, 175434028356390062353), (3069, 3069, 175435929338925350918), (3070, 3070, 175437849359159460155), (3071, 3071, 175439788608030101650), (3072, 3072, 175441747278395648795), (3073, 3073, 175443725565054570656), (3074, 3074, 175445723664765064761), (3075, 3075, 175447741776264890892), (3076, 3076, 175449780100291407980), (3077, 3077, 175451838839601816234), (3078, 3078, 175453918198993606649), (3079, 3079, 175456018385325220078), (3080, 3080, 175458139607536918056), (3081, 3081, 175460282076671867600), (3082, 3082, 175462446005897442231), (3083, 3083, 175464631610526741497), (3084, 3084, 175466839108040331274), (3085, 3085, 175469068718108207189), (3086, 3086, 175471320662611983490), (3087, 3087, 175473595165667309754), (3088, 3088, 175475892453646517814), (3089, 3089, 175478212755201501342), (3090, 3090, 175480556301286830539), (3091, 3091, 175482923325183104395), (3092, 3092, 175485314062520543050), (3093, 3093, 175487728751302822771), (3094, 3094, 175490167631931156106), (3095, 3095, 175492630947228619817), (3096, 3096, 175495118942464733206), (3097, 3097, 175497631865380289470), (3098, 3098, 175500169966212442783), (3099, 3099, 175502733497720053792), (3100, 3100, 175505322715209296279), (3101, 3101, 175507937876559527740), (3102, 3102, 175510579242249426700), (3103, 3103, 175513247075383399577), (3104, 3104, 175515941641718259958), (3105, 3105, 175518663209690183185), (3106, 3106, 175521412050441939180), (3107, 3107, 175524188437850406452), (3108, 3108, 175526992648554370288), (3109, 3109, 175529824961982608161), (3110, 3110, 175532685660382265385), (3111, 3111, 175535575028847524149), (3112, 3112, 175538493355348569018), (3113, 3113, 175541440930760852101), (3114, 3114, 175544418048894661049), (3115, 3115, 175547425006524993154), (3116, 3116, 175550462103421738787), (3117, 3117, 175553529642380177504), (3118, 3118, 175556627929251790162), (3119, 3119, 175559757272975390422), (3120, 3120, 175562917985608579067), (3121, 3121, 175566110382359524598), (3122, 3122, 175569334781619073596), (3123, 3123, 175572591504993194405), (3124, 3124, 175575880877335757709), (3125, 3125, 175579203226781657620), (3126, 3126, 175582558884780276952), (3127, 3127, 175585948186129300368), (3128, 3128, 175589371469008879162), (3129, 3129, 175592829075016151463), (3130, 3130, 175596321349200121680), (3131, 3131, 175599848640096903085), (3132, 3132, 175603411299765327442), (3133, 3133, 175607009683822925657), (3134, 3134, 175610644151482283450), (3135, 3135, 175614315065587776124), (3136, 3136, 175618022792652686520), (3137, 3137, 175621767702896710324), (3138, 3138, 175625550170283852917), (3139, 3139, 175629370572560722024), (3140, 3140, 175633229291295220464), (3141, 3141, 175637126711915643334), (3142, 3142, 175641063223750184051), (3143, 3143, 175645039220066853677), (3144, 3144, 175649055098113818052), (3145, 3145, 175653111259160157272), (3146, 3146, 175657208108537052135), (3147, 3147, 175661346055679402206), (3148, 3148, 175665525514167880224), (3149, 3149, 175669746901771427626), (3150, 3150, 175674010640490196003), (3151, 3151, 175678317156598939391), (3152, 3152, 175682666880690862330), (3153, 3153, 175687060247721928683), (3154, 3154, 175691497697055636300), (3155, 3155, 175695979672508262616), (3156, 3156, 175700506622394586394), (3157, 3157, 175705078999574090823), (3158, 3158, 175709697261497653306), (3159, 3159, 175714361870254727280), (3160, 3160, 175719073292621021517), (3161, 3161, 175723832000106682386), (3162, 3162, 175728638469004984653), (3163, 3163, 175733493180441536433), (3164, 3164, 175738396620424003996), (3165, 3165, 175743349279892362189), (3166, 3166, 175748351654769676306), (3167, 3167, 175753404246013421312), (3168, 3168, 175758507559667344381), (3169, 3169, 175763662106913876819), (3170, 3170, 175768868404127101459), (3171, 3171, 175774126972926281749), (3172, 3172, 175779438340229958779), (3173, 3173, 175784803038310622607), (3174, 3174, 175790221604849964288), (3175, 3175, 175795694582994715120), (3176, 3176, 175801222521413079671), (3177, 3177, 175806805974351769259), (3178, 3178, 175812445501693642605), (3179, 3179, 175818141669015960504), (3180, 3180, 175823895047649261393), (3181, 3181, 175829706214736864831), (3182, 3182, 175835575753295009947), (3183, 3183, 175841504252273636029), (3184, 3184, 175847492306617812498), (3185, 3185, 175853540517329825620), (3186, 3186, 175859649491531929368), (3187, 3187, 175865819842529767976), (3188, 3188, 175872052189876477788), (3189, 3189, 175878347159437476116), (3190, 3190, 175884705383455944927), (3191, 3191, 175891127500619017237), (3192, 3192, 175897614156124674240), (3193, 3193, 175904166001749361264), (3194, 3194, 175910783695916330752), (3195, 3195, 175917467903764720594), (3196, 3196, 175924219297219376202), (3197, 3197, 175931038555061424851), (3198, 3198, 175937926362999610924), (3199, 3199, 175944883413742400773), (3200, 3200, 175951910407070866059), (3201, 3201, 175959008049912354512), (3202, 3202, 175966177056414957195), (3203, 3203, 175973418148022781446), (3204, 3204, 175980732053552038804), (3205, 3205, 175988119509267957338), (3206, 3206, 175995581258962527930), (3207, 3207, 176003118054033094152), (3208, 3208, 176010730653561795553), (3209, 3209, 176018419824395874242), (3210, 3210, 176026186341228854828), (3211, 3211, 176034030986682607871), (3212, 3212, 176041954551390307153), (3213, 3213, 176049957834080291203), (3214, 3214, 176058041641660839639), (3215, 3215, 176066206789305875042), (3216, 3216, 176074454100541601197), (3217, 3217, 176082784407334088693), (3218, 3218, 176091198550177819022), (3219, 3219, 176099697378185198428), (3220, 3220, 176108281749177052953), (3221, 3221, 176116952529774116241), (3222, 3222, 176125710595489521825), (3223, 3223, 176134556830822311784), (3224, 3224, 176143492129351973792), (3225, 3225, 176152517393834018771), (3226, 3226, 176161633536296611494), (3227, 3227, 176170841478138266656), (3228, 3228, 176180142150226623113), (3229, 3229, 176189536492998309125), (3230, 3230, 176199025456559911652), (3231, 3231, 176208610000790062889), (3232, 3232, 176218291095442657419), (3233, 3233, 176228069720251213548), (3234, 3234, 176237946865034392564), (3235, 3235, 176247923529802689827), (3236, 3236, 176258000724866311825), (3237, 3237, 176268179470944253483), (3238, 3238, 176278460799274590232), (3239, 3239, 176288845751725999521), (3240, 3240, 176299335380910526682), (3241, 3241, 176309930750297610222), (3242, 3242, 176320632934329381865), (3243, 3243, 176331443018537256847), (3244, 3244, 176342362099659830180), (3245, 3245, 176353391285762094845), (3246, 3246, 176364531696355998052), (3247, 3247, 176375784462522351962), (3248, 3248, 176387150727034115477), (3249, 3249, 176398631644481063935), (3250, 3250, 176410228381395863778), (3251, 3251, 176421942116381569509), (3252, 3252, 176433774040240560483), (3253, 3253, 176445725356104935329), (3254, 3254, 176457797279568382042), (3255, 3255, 176469991038819542045), (3256, 3256, 176482307874776886779), (3257, 3257, 176494749041225125615), (3258, 3258, 176507315804953164199), (3259, 3259, 176520009445893632541), (3260, 3260, 176532831257264002505), (3261, 3261, 176545782545709314572), (3262, 3262, 176558864631446534079), (3263, 3263, 176572078848410557396), (3264, 3264, 176585426544401888796), (3265, 3265, 176598909081236009099), (3266, 3266, 176612527834894457427), (3267, 3267, 176626284195677647752), (3268, 3268, 176640179568359442210), (3269, 3269, 176654215372343503486), (3270, 3270, 176668393041821448877), (3271, 3271, 176682714025932828984), (3272, 3272, 176697179788926954314), (3273, 3273, 176711791810326593408), (3274, 3274, 176726551585093566451), (3275, 3275, 176741460623796258685), (3276, 3276, 176756520452779078279), (3277, 3277, 176771732614333883701), (3278, 3278, 176787098666873405969), (3279, 3279, 176802620185106691568), (3280, 3280, 176818298760216592174), (3281, 3281, 176834136000039327722), (3282, 3282, 176850133529246149756), (3283, 3283, 176866292989527132381), (3284, 3284, 176882616039777118564), (3285, 3285, 176899104356283849928), (3286, 3286, 176915759632918308611), (3287, 3287, 176932583581327300194), (3288, 3288, 176949577931128307133), (3289, 3289, 176966744430106642562), (3290, 3290, 176984084844414934812), (3291, 3291, 177001600958774973421), (3292, 3292, 177019294576681947891), (3293, 3293, 177037167520611110919), (3294, 3294, 177055221632226898313), (3295, 3295, 177073458772594538290), (3296, 3296, 177091880822394183366), (3297, 3297, 177110489682137598527), (3298, 3298, 177129287272387439936), (3299, 3299, 177148275533979158893), (3300, 3300, 177167456428245566369), (3301, 3301, 177186831937244093923), (3302, 3302, 177206404063986787399), (3303, 3303, 177226174832673070358), (3304, 3304, 177246146288925314762), (3305, 3305, 177266320500027257029), (3306, 3306, 177286699555165298159), (3307, 3307, 177307285565672727253), (3308, 3308, 177328080665276908339), (3309, 3309, 177349087010349471078), (3310, 3310, 177370306780159546526), (3311, 3311, 177391742177130089825), (3312, 3312, 177413395427097332299), (3313, 3313, 177435268779573406161), (3314, 3314, 177457364508012185701), (3315, 3315, 177479684910078389495), (3316, 3316, 177502232307919988957), (3317, 3317, 177525009048443969198), (3318, 3318, 177548017503595488965), (3319, 3319, 177571260070640487126), (3320, 3320, 177594739172451783994), (3321, 3321, 177618457257798726490), (3322, 3322, 177642416801640427003), (3323, 3323, 177666620305422646585), (3324, 3324, 177691070297378373931), (3325, 3325, 177715769332832152453), (3326, 3326, 177740719994508208612), (3327, 3327, 177765924892842435523), (3328, 3328, 177791386666298286747), (3329, 3329, 177817107981686636092), (3330, 3330, 177843091534489660150), (3331, 3331, 177869340049188801246), (3332, 3332, 177895856279596869428), (3333, 3333, 177922643009194343088), (3334, 3334, 177949703051469928816), (3335, 3335, 177977039250265442081), (3336, 3336, 178004654480125071364), (3337, 3337, 178032551646649089427), (3338, 3338, 178060733686852076467), (3339, 3339, 178089203569525720973), (3340, 3340, 178117964295606265257), (3341, 3341, 178147018898546663702), (3342, 3342, 178176370444693522988), (3343, 3343, 178206022033668894671), (3344, 3344, 178235976798756991736), (3345, 3345, 178266237907295901929), (3346, 3346, 178296808561074371943), (3347, 3347, 178327691996733737791), (3348, 3348, 178358891486175077988), (3349, 3349, 178390410336971667485), (3350, 3350, 178422251892786811654), (3351, 3351, 178454419533797140972), (3352, 3352, 178486916677121448464), (3353, 3353, 178519746777255153389), (3354, 3354, 178552913326510476094), (3355, 3355, 178586419855462410455), (3356, 3356, 178620269933400581835), (3357, 3357, 178654467168787080008), (3358, 3358, 178689015209720358104), (3359, 3359, 178723917744405290197), (3360, 3360, 178759178501629481814), (3361, 3361, 178794801251245929314), (3362, 3362, 178830789804662125750), (3363, 3363, 178867148015335712615), (3364, 3364, 178903879779276778589), (3365, 3365, 178940989035556908258), (3366, 3366, 178978479766825085565), (3367, 3367, 179016355999830558674), (3368, 3368, 179054621805952774832), (3369, 3369, 179093281301738495743), (3370, 3370, 179132338649446206014), (3371, 3371, 179171798057597929213), (3372, 3372, 179211663781538568192), (3373, 3373, 179251940124002888440), (3374, 3374, 179292631435690265391), (3375, 3375, 179333742115847318804), (3376, 3376, 179375276612858559619), (3377, 3377, 179417239424845176963), (3378, 3378, 179459635100272095335), (3379, 3379, 179502468238563434395), (3380, 3380, 179545743490726506239), (3381, 3381, 179589465559984487501), (3382, 3382, 179633639202417906225), (3383, 3383, 179678269227615085995), (3384, 3384, 179723360499331692514), (3385, 3385, 179768917936159530496), (3386, 3386, 179814946512204741527), (3387, 3387, 179861451257775556373), (3388, 3388, 179908437260079758085), (3389, 3389, 179955909663932015222), (3390, 3390, 180003873672471247487), (3391, 3391, 180052334547888189195), (3392, 3392, 180101297612163319072), (3393, 3393, 180150768247815328136), (3394, 3394, 180200751898660300658), (3395, 3395, 180251254070581786556), (3396, 3396, 180302280332311946996), (3397, 3397, 180353836316223958431), (3398, 3398, 180405927719135863933), (3399, 3399, 180458560303126064238), (3400, 3400, 180511739896360644721), (3401, 3401, 180565472393932738249), (3402, 3402, 180619763758714127797), (3403, 3403, 180674620022219296642), (3404, 3404, 180730047285482138032), (3405, 3405, 180786051719945540340), (3406, 3406, 180842639568364067976), (3407, 3407, 180899817145719962637), (3408, 3408, 180957590840152693894), (3409, 3409, 181015967113902292650), (3410, 3410, 181074952504266705611), (3411, 3411, 181134553624573413624), (3412, 3412, 181194777165165561578), (3413, 3413, 181255629894402852490), (3414, 3414, 181317118659677463425), (3415, 3415, 181379250388445246091), (3416, 3416, 181442032089272480166), (3417, 3417, 181505470852898452863), (3418, 3418, 181569573853314143690), (3419, 3419, 181634348348857299042), (3420, 3420, 181699801683324186992), (3421, 3421, 181765941287098328549), (3422, 3422, 181832774678296507678), (3423, 3423, 181900309463932368532), (3424, 3424, 181968553341097914644), (3425, 3425, 182037514098163231282), (3426, 3426, 182107199615994758751), (3427, 3427, 182177617869192451163), (3428, 3428, 182248776927346162124), (3429, 3429, 182320684956311605796), (3430, 3430, 182393350219506249046), (3431, 3431, 182466781079225497767), (3432, 3432, 182540985997979548011), (3433, 3433, 182615973539851280302), (3434, 3434, 182691752371875583417), (3435, 3435, 182768331265440502006), (3436, 3436, 182845719097710610718), (3437, 3437, 182923924853073025968), (3438, 3438, 183002957624606475162), (3439, 3439, 183082826615573852074), (3440, 3440, 183163541140938696160), (3441, 3441, 183245110628906042905), (3442, 3442, 183327544622488101802), (3443, 3443, 183410852781095228339), (3444, 3444, 183495044882152666342), (3445, 3445, 183580130822743547216), (3446, 3446, 183666120621278643140), (3447, 3447, 183753024419193381934), (3448, 3448, 183840852482672642325), (3449, 3449, 183929615204403859544), (3450, 3450, 184019323105358982715), (3451, 3451, 184109986836605837254), (3452, 3452, 184201617181149457595), (3453, 3453, 184294225055803967875), (3454, 3454, 184387821513095600924), (3455, 3455, 184482417743197458820), (3456, 3456, 184578025075896631600), (3457, 3457, 184674654982594304291), (3458, 3458, 184772319078339496395), (3459, 3459, 184871029123897092227), (3460, 3460, 184970797027850835169), (3461, 3461, 185071634848741973864), (3462, 3462, 185173554797244263788), (3463, 3463, 185276569238376043349), (3464, 3464, 185380690693750119844), (3465, 3465, 185485931843862217108), (3466, 3466, 185592305530418753687), (3467, 3467, 185699824758704737728), (3468, 3468, 185808502699992582595), (3469, 3469, 185918352693992665504), (3470, 3470, 186029388251346470187), (3471, 3471, 186141623056163173791), (3472, 3472, 186255070968600557913), (3473, 3473, 186369746027491143869), (3474, 3474, 186485662453014472953), (3475, 3475, 186602834649416473741), (3476, 3476, 186721277207776880184), (3477, 3477, 186841004908825686632), (3478, 3478, 186962032725809648791), (3479, 3479, 187084375827409863128), (3480, 3480, 187208049580711481318), (3481, 3481, 187333069554226641075), (3482, 3482, 187459451520971720046), (3483, 3483, 187587211461600045477), (3484, 3484, 187716365567591219074), (3485, 3485, 187846930244498243852), (3486, 3486, 187978922115253667905), (3487, 3487, 188112358023535988866), (3488, 3488, 188247255037197592440), (3489, 3489, 188383630451755528792), (3490, 3490, 188521501793946461762), (3491, 3491, 188660886825347157897), (3492, 3492, 188801803546061915175), (3493, 3493, 188944270198478365025), (3494, 3494, 189088305271093115925), (3495, 3495, 189233927502408742404), (3496, 3496, 189381155884903659822), (3497, 3497, 189530009669076462826), (3498, 3498, 189680508367566343877), (3499, 3499, 189832671759351247829), (3500, 3500, 189986519894025459177), (3501, 3501, 190142073096158360328), (3502, 3502, 190299351969736142118), (3503, 3503, 190458377402688291880), (3504, 3504, 190619170571500729576), (3505, 3505, 190781752945917509041), (3506, 3506, 190946146293733049137), (3507, 3507, 191112372685676908724), (3508, 3508, 191280454500393169793), (3509, 3509, 191450414429516544957), (3510, 3510, 191622275482847378784), (3511, 3511, 191796060993627767230), (3512, 3512, 191971794623921075731), (3513, 3513, 192149500370097194390), (3514, 3514, 192329202568425928199), (3515, 3515, 192510925900780981422), (3516, 3516, 192694695400457058143), (3517, 3517, 192880536458102665712), (3518, 3518, 193068474827771274290), (3519, 3519, 193258536633093554138), (3520, 3520, 193450748373573482643), (3521, 3521, 193645136931011185447), (3522, 3522, 193841729576055450485), (3523, 3523, 194040553974888930335), (3524, 3524, 194241638196049127059), (3525, 3525, 194445010717388334798), (3526, 3526, 194650700433175798774), (3527, 3527, 194858736661345435229), (3528, 3528, 195069149150892545109), (3529, 3529, 195281968089423045291), (3530, 3530, 195497224110858834647), (3531, 3531, 195714948303303008634), (3532, 3532, 195935172217068735201), (3533, 3533, 196157927872875706932), (3534, 3534, 196383247770218189404), (3535, 3535, 196611164895908794002), (3536, 3536, 196841712732802214846), (3537, 3537, 197074925268703284264), (3538, 3538, 197310837005463819433), (3539, 3539, 197549482968272854555), (3540, 3540, 197790898715144978355), (3541, 3541, 198035120346611625830), (3542, 3542, 198282184515620306326), (3543, 3543, 198532128437646887082), (3544, 3544, 198784989901026192737), (3545, 3545, 199040807277506326846), (3546, 3546, 199299619533032271534), (3547, 3547, 199561466238764476061), (3548, 3548, 199826387582338304478), (3549, 3549, 200094424379370376870), (3550, 3550, 200365618085218008099), (3551, 3551, 200640010806998122584), (3552, 3552, 200917645315872203763), (3553, 3553, 201198565059604022562), (3554, 3554, 201482814175397080689), (3555, 3555, 201770437503018902093), (3556, 3556, 202061480598219509614), (3557, 3557, 202355989746451634006), (3558, 3558, 202654011976900419278), (3559, 3559, 202955595076830611951), (3560, 3560, 203260787606259452586), (3561, 3561, 203569638912963726072), (3562, 3562, 203882199147829672873), (3563, 3563, 204198519280554717081), (3564, 3564, 204518651115710228847), (3565, 3565, 204842647309174809032), (3566, 3566, 205170561384947862835), (3567, 3567, 205502447752353517177), (3568, 3568, 205838361723645234002), (3569, 3569, 206178359532021778733), (3570, 3570, 206522498350065520254), (3571, 3571, 206870836308614366321), (3572, 3572, 207223432516078976651), (3573, 3573, 207580347078217245407), (3574, 3574, 207941641118378405881), (3575, 3575, 208307376798229483224), (3576, 3576, 208677617338977206563), (3577, 3577, 209052427043098890207), (3578, 3578, 209431871316596205353), (3579, 3579, 209816016691786189251), (3580, 3580, 210204930850644278678), (3581, 3581, 210598682648714609348), (3582, 3582, 210997342139603293042), (3583, 3583, 211400980600070870449), (3584, 3584, 211809670555740640460), (3585, 3585, 212223485807440086624), (3586, 3586, 212642501458193159281), (3587, 3587, 213066793940881728240), (3588, 3588, 213496441046595096365), (3589, 3589, 213931521953687059961), (3590, 3590, 214372117257560617956), (3591, 3591, 214818309001201069542), (3592, 3592, 215270180706478899850), (3593, 3593, 215727817406244536286), (3594, 3594, 216191305677237765255), (3595, 3595, 216660733673835331000), (3596, 3596, 217136191162660996250), (3597, 3597, 217617769558083129188), (3598, 3598, 218105561958625694051), (3599, 3599, 218599663184319364481), (3600, 3600, 219100169815020350744), (3601, 3601, 219607180229725435268), (3602, 3602, 220120794646912646821), (3603, 3603, 220641115165937973442), (3604, 3604, 221168245809519519154), (3605, 3605, 221702292567341551007), (3606, 3606, 222243363440811962570), (3607, 3607, 222791568489007799075), (3608, 3608, 223347019875844649634), (3609, 3609, 223909831918506914961), (3610, 3610, 224480121137177206509), (3611, 3611, 225058006306104426702), (3612, 3612, 225643608506051421867), (3613, 3613, 226237051178164491530), (3614, 3614, 226838460179308481887), (3615, 3615, 227447963838912689770), (3616, 3616, 228065693017374358362), (3617, 3617, 228691781166068159710), (3618, 3618, 229326364389011734133), (3619, 3619, 229969581506239095400), (3620, 3620, 230621574118935515842), (3621, 3621, 231282486676389379915), (3622, 3622, 231952466544818441299), (3623, 3623, 232631664078129940162), (3624, 3624, 233320232690676137090), (3625, 3625, 234018328932069001552), (3626, 3626, 234726112564120059177), (3627, 3627, 235443746639973757098), (3628, 3628, 236171397585505153976), (3629, 3629, 236909235283055285013), (3630, 3630, 237657433157580196371), (3631, 3631, 238416168265292392321), (3632, 3632, 239185621384876296591), (3633, 3633, 239965977111362301589), (3634, 3634, 240757423952747070276), (3635, 3635, 241560154429450970779), (3636, 3636, 242374365176706868625), (3637, 3637, 243200257049977981617), (3638, 3638, 244038035233506123587), (3639, 3639, 244887909352095432021), (3640, 3640, 245750093586240597180), (3641, 3641, 246624806790712693808), (3642, 3642, 247512272616719967947), (3643, 3643, 248412719637765358272), (3644, 3644, 249326381479327141648), (3645, 3645, 250253496952493894459), (3646, 3646, 251194310191689963452), (3647, 3647, 252149070796632851330), (3648, 3648, 253118033978669352753), (3649, 3649, 254101460711642935665), (3650, 3650, 255099617887450761557), (3651, 3651, 256112778476454887251), (3652, 3652, 257141221692918601781), (3653, 3653, 258185233165645536907), (3654, 3654, 259245105114006161592), (3655, 3655, 260321136529543542685), (3656, 3656, 261413633363357840151), (3657, 3657, 262522908719476920241), (3658, 3658, 263649283054428729470), (3659, 3659, 264793084383239692429), (3660, 3660, 265954648492092394507), (3661, 3661, 267134319157885204365), (3662, 3662, 268332448374946299592), (3663, 3663, 269549396589164802056), (3664, 3664, 270785532939812428172), (3665, 3665, 272041235509340235404), (3666, 3666, 273316891581446723178), (3667, 3667, 274612897907725748129), (3668, 3668, 275929660983215466051), (3669, 3669, 277267597331182842883), (3670, 3670, 278627133797492213073), (3671, 3671, 280008707854920935458), (3672, 3672, 281412767917800436054), (3673, 3673, 282839773667376866846), (3674, 3674, 284290196388302284872), (3675, 3675, 285764519316684703360), (3676, 3676, 287263238000143625224), (3677, 3677, 288786860670336779760), (3678, 3678, 290335908628443788976), (3679, 3679, 291910916644113436217), (3680, 3680, 293512433368403144415), (3681, 3681, 295141021761262245123), (3682, 3682, 296797259534134685798), (3683, 3683, 298481739608282037876), (3684, 3684, 300195070589454091555), (3685, 3685, 301937877259562017555), (3686, 3686, 303710801086038107791), (3687, 3687, 305514500749596545778), (3688, 3688, 307349652691141577735), (3689, 3689, 309216951678602934711), (3690, 3690, 311117111394513477292), (3691, 3691, 313050865045180884750), (3692, 3692, 315018965992343882007), (3693, 3693, 317022188408244088150), (3694, 3694, 319061327955087182436), (3695, 3695, 321137202489911826956), (3696, 3696, 323250652795931774660), (3697, 3697, 325402543341465949593), (3698, 3698, 327593763067623141973), (3699, 3699, 329825226205962451255), (3700, 3700, 332097873127407880258), (3701, 3701, 334412671223755686415), (3702, 3702, 336770615823176394684), (3703, 3703, 339172731141179943020), (3704, 3704, 341620071268582447983), (3705, 3705, 344113721198086738662), (3706, 3706, 346654797891166316780), (3707, 3707, 349244451387023977149), (3708, 3708, 351883865955482196455), (3709, 3709, 354574261295752814481), (3710, 3710, 357316893783128750178), (3711, 3711, 360113057765740791350), (3712, 3712, 362964086913628163884), (3713, 3713, 365871355622482935435), (3714, 3714, 368836280474545669596), (3715, 3715, 371860321759253470688), (3716, 3716, 374944985056372019297), (3717, 3717, 378091822884480791033), (3718, 3718, 381302436417825796845), (3719, 3719, 384578477274707330961), (3720, 3720, 387921649380731838525), (3721, 3721, 391333710910427626544), (3722, 3722, 394816476310904278324), (3723, 3723, 398371818411425867707), (3724, 3724, 402001670622969016495), (3725, 3725, 405708029232049147980), (3726, 3726, 409492955793322654945), (3727, 3727, 413358579625709861380), (3728, 3728, 417307100417034400883), (3729, 3729, 421340790942439801434), (3730, 3730, 425461999902124551089), (3731, 3731, 429673154884233677384), (3732, 3732, 433976765459058923735), (3733, 3733, 438375426411032035989), (3734, 3734, 442871821115347642318), (3735, 3735, 447468725066424958636), (3736, 3736, 452169009565812403183), (3737, 3737, 456975645577557571248), (3738, 3738, 461891707759508414697), (3739, 3739, 466920378679481505406), (3740, 3740, 472064953225731662684), (3741, 3741, 477328843221685838136), (3742, 3742, 482715582255464951253), (3743, 3743, 488228830735312467975), (3744, 3744, 493872381182680173287), (3745, 3745, 499650163775392228174), (3746, 3746, 505566252154020812994), (3747, 3747, 511624869505363220052), (3748, 3748, 517830394937714142970), (3749, 3749, 524187370163481308029), (3750, 3750, 530700506505600921541), (3751, 3751, 537374692245175333735), (3752, 3752, 544215000328782776455), (3753, 3753, 551226696455002239269), (3754, 3754, 558415247560860036261), (3755, 3755, 565786330730143247423), (3756, 3756, 573345842546844217763), (3757, 3757, 581099908918405276079), (3758, 3758, 589054895394929824753), (3759, 3759, 597217418012121435384), (3760, 3760, 605594354687413534369), (3761, 3761, 614192857200566177118), (3762, 3762, 623020363791941358863), (3763, 3763, 632084612413732979612), (3764, 3764, 641393654671631322256), (3765, 3765, 650955870496754788479), (3766, 3766, 660779983590194518296), (3767, 3767, 670875077685202091058), (3768, 3768, 681250613674919376925), (3769, 3769, 691916447656616375563), (3770, 3770, 702882849946682212220), (3771, 3771, 714160525124122190489), (3772, 3772, 725760633164067015184), (3773, 3773, 737694811726817452198), (3774, 3774, 749975199672248720581), (3775, 3775, 762614461874005358374), (3776, 3776, 775625815412852456045), (3777, 3777, 789023057233838193126), (3778, 3778, 802820593357592787123), (3779, 3779, 817033469742169749254), (3780, 3780, 831677404898358652147), (3781, 3781, 846768824368399009627), (3782, 3782, 862324897185539786517), (3783, 3783, 878363574439959068962), (3784, 3784, 894903630085227517258), (3785, 3785, 911964704128815094097), (3786, 3786, 929567348360154962081), (3787, 3787, 947733074780547540341), (3788, 3788, 966484406910772480439), (3789, 3789, 985844934164742997889), (3790, 3790, 1005839369490957540461), (3791, 3791, 1026493610497956409309), (3792, 3792, 1047834804295560729779), (3793, 3793, 1069891416300450620314), (3794, 3794, 1092693303272729218605), (3795, 3795, 1116271790869629010015), (3796, 3796, 1140659756023566047239), (3797, 3797, 1165891714474466224029), (3798, 3798, 1192003913810817545367), (3799, 3799, 1219034432400397917161), (3800, 3800, 1247023284620258004004), (3801, 3801, 1276012532826487218375), (3802, 3802, 1306046406537758844622), (3803, 3803, 1337171429342857135214), (3804, 3804, 1369436554081574758440), (3805, 3805, 1402893306890795381306), (3806, 3806, 1437595940753530140092), (3807, 3807, 1473601599238471965737), (3808, 3808, 1510970491171611542052), (3809, 3809, 1549766077039999072078), (3810, 3810, 1590055267991248926302), (3811, 3811, 1631908638361321119105), (3812, 3812, 1675400652737969458865), (3813, 3813, 1720609908648564226266), (3814, 3814, 1767619396049373400830), (3815, 3815, 1816516774889475252131), (3816, 3816, 1867394672126995502046), (3817, 3817, 1920350999689104420565), (3818, 3818, 1975489294991041983797), (3819, 3819, 2032919085764318398383), (3820, 3820, 2092756281091214839965), (3821, 3821, 2155123590702943513107), (3822, 3822, 2220150974773593230516), (3823, 3823, 2287976126632693170139), (3824, 3824, 2358744991027424355616), (3825, 3825, 2432612320792906986297), (3826, 3826, 2509742275037480987414), (3827, 3827, 2590309062221563231913), (3828, 3828, 2674497631805812933691), (3829, 3841, 2698500957556355349776), (3842, 3842, 2679162396937454104607), (3843, 3843, 2652636036571736737235), (3844, 3844, 2626372313437363106173), (3845, 3845, 2600368627165706045716), (3846, 3846, 2574622403134362421501), (3847, 3847, 2549131092212240021288), (3848, 3848, 2523892170507168337909), (3849, 3849, 2498903139116008255355), (3850, 3850, 2474161523877235896392), (3851, 3851, 2449664875125976135041), (3852, 3852, 2425410767451461519843), (3853, 3853, 2401396799456892593904), (3854, 3854, 2377620593521675835548), (3855, 3855, 2354079795566015678761), (3856, 3856, 2330772074817837305704), (3857, 3857, 2307695123582017134360), (3858, 3858, 2284846657011898152832), (3859, 3859, 2262224412883067478051), (3860, 3860, 2239826151369373740645), (3861, 3861, 2217649654821162119450), (3862, 3862, 2195692727545705068763), (3863, 3863, 2173953195589806998775), (3864, 3864, 2152428906524561384926), (3865, 3865, 2131117729232238994976), (3866, 3866, 2110017553695286133639), (3867, 3867, 2089126290787412013504), (3868, 3868, 2068441872066744567826), (3869, 3869, 2047962249571034225570), (3870, 3870, 2027685395614885371852), (3871, 3871, 2007609302588995417675), (3872, 3872, 1987731982761381601659), (3873, 3873, 1968051468080575843226), (3874, 3874, 1948565809980768161610), (3875, 3875, 1929273079188879367931), (3876, 3876, 1910171365533543928645), (3877, 3877, 1891258777755984087767), (3878, 3878, 1872533443322756522541), (3879, 3879, 1853993508240352992615), (3880, 3880, 1835637136871636626352), (3881, 3881, 1817462511754095669655), (3882, 3882, 1799467833419896702629), (3883, 3883, 1781651320217719507553), (3884, 3884, 1764011208136355948073), (3885, 3885, 1746545750630055394131), (3886, 3886, 1729253218445599400130), (3887, 3887, 1712131899451088514980), (3888, 3888, 1695180098466424272258), (3889, 3889, 1678396137095469576493), (3890, 3890, 1661778353559870867815), (3891, 3891, 1645325102534525611698), (3892, 3892, 1629034754984678823463), (3893, 3893, 1612905698004632498478), (3894, 3894, 1596936334658051978691), (3895, 3895, 1581125083819853444249), (3896, 3896, 1565470380019656875494), (3897, 3897, 1549970673286788985638), (3898, 3898, 1534624428996820777859), (3899, 3899, 1519430127719624532534), (3900, 3900, 1504386265068935180726), (3901, 3901, 1489491351553401169036), (3902, 3902, 1474743912429110068353), (3903, 3903, 1460142487553574325102), (3904, 3904, 1445685631241162698120), (3905, 3905, 1431371912119963067446), (3906, 3906, 1417199912990062443016), (3907, 3907, 1403168230683230141600), (3908, 3908, 1389275475923990239208), (3909, 3909, 1375520273192069543770), (3910, 3910, 1361901260586207469079), (3911, 3911, 1348417089689314325821), (3912, 3912, 1335066425434964679031), (3913, 3913, 1321847945975212553496), (3914, 3914, 1308760342549715399501), (3915, 3915, 1295802319356153860892), (3916, 3916, 1282972593421934515734), (3917, 3917, 1270269894477162886866), (3918, 3918, 1257692964828874145412), (3919, 3919, 1245240559236509054863), (3920, 3920, 1232911444788622826597), (3921, 3921, 1220704400780814679799), (3922, 3922, 1208618218594866019603), (3923, 3923, 1196651701579075266934), (3924, 3924, 1184803664929777492014), (3925, 3925, 1173072935574037120806), (3926, 3926, 1161458352053502099807), (3927, 3927, 1149958764409408019611), (3928, 3928, 1138573034068720811496), (3929, 3929, 1127300033731406744056), (3930, 3930, 1116138647258818558471), (3931, 3931, 1105087769563186691556), (3932, 3932, 1094146306498204645105), (3933, 3933, 1083313174750697668420), (3934, 3934, 1072587301733364028139), (3935, 3935, 1061967625478578245682), (3936, 3936, 1051453094533245787804), (3937, 3937, 1041042667854698799806), (3938, 3938, 1030735314707622574065), (3939, 3939, 1020530014562002548580), (3940, 3940, 1010425756992081731267), (3941, 3941, 1000421541576318545809), (3942, 3942, 990516377798335193870), (3943, 3943, 980709284948846726604), (3944, 3944, 970999292028561115450), (3945, 3945, 961385437652040708366), (3946, 3946, 951866769952515552838), (3947, 3947, 942442346487639161225), (3948, 3948, 933111234146177387352), (3949, 3949, 923872509055621175596), (3950, 3950, 914725256490714035243), (3951, 3951, 905668570782885183409), (3952, 3952, 896701555230579389514), (3953, 3953, 887823322010474643083), (3954, 3954, 879032992089578854538), (3955, 3955, 870329695138196885681), (3956, 3956, 861712569443759292754), (3957, 3957, 853180761825504250251), (3958, 3958, 844733427550004208170), (3959, 3959, 836369730247528918980), (3960, 3960, 828088841829236553445), (3961, 3961, 819889942405184706381), (3962, 3962, 811772220203153174635), (3963, 3963, 803734871488270469936), (3964, 3964, 795777100483436108847), (3965, 3965, 787898119290530800839), (3966, 3966, 780097147812406733504), (3967, 3967, 772373413675650231192), (3968, 3968, 764726152154109139794), (3969, 3969, 757154606093177366133), (3970, 3970, 749658025834829075379), (3971, 3971, 742235669143395124138), (3972, 3972, 734886801132074380334), (3973, 3973, 727610694190172653796), (3974, 3974, 720406627911062033462), (3975, 3975, 713273889020853498477), (3976, 3976, 706211771307775741066), (3977, 3977, 699219575552253208976), (3978, 3978, 692296609457676444531), (3979, 3979, 685442187581857865872), (3980, 3980, 678655631269166203834), (3981, 3981, 671936268583332875083), (3982, 3982, 665283434240923638696), (3983, 3983, 658696469545468949204), (3984, 3984, 652174722322246484361), (3985, 3985, 645717546853709390456), (3986, 3986, 639324303815553851937), (3987, 3987, 632994360213419655383), (3988, 3988, 626727089320217480577), (3989, 3989, 620521870614076713443), (3990, 3990, 614378089716907637072), (3991, 3991, 608295138333571917893), (3992, 3992, 602272414191655364251), (3993, 3993, 596309320981836994308), (3994, 3994, 590405268298848509215), (3995, 3995, 584559671583018325956), (3996, 3996, 578771952062394382135), (3997, 3997, 573041536695439982311), (3998, 3998, 567367858114297012190), (3999, 3999, 561750354568610903158), (4000, 4000, 556188469869911785305), (4001, 4001, 550681653336546322084), (4002, 4002, 545229359739154774341), (4003, 4003, 539831049246687895387), (4004, 4004, 534486187372958312264), (4005, 4005, 529194244923721101252), (4006, 4006, 523954697944278318071), (4007, 4007, 518767027667602295120), (4008, 4008, 513630720462972569425), (4009, 4009, 508545267785121355867), (4010, 4010, 503510166123882530561), (4011, 4011, 498524916954339139170), (4012, 4012, 493589026687464494227), (4013, 4013, 488702006621251974482), (4014, 4014, 483863372892328687606), (4015, 4015, 479072646428048205551), (4016, 4016, 474329352899057629258), (4017, 4017, 469633022672334286394), (4018, 4018, 464983190764687412272), (4019, 4019, 460379396796720210170), (4020, 4020, 455821184947247732842), (4021, 4021, 451308103908166072120), (4022, 4022, 446839706839768388238), (4023, 4023, 442415551326503354691), (4024, 4024, 438035199333171638308), (4025, 4025, 433698217161556077533), (4026, 4026, 429404175407481264884), (4027, 4027, 425152648918298282063), (4028, 4028, 420943216750790378280), (4029, 4029, 416775462129495424040), (4030, 4030, 412648972405441013901), (4031, 4031, 408563339015288132575), (4032, 4032, 404518157440879339183), (4033, 4033, 400513027169187464538), (4034, 4034, 396547551652660855978), (4035, 4035, 392621338269961243543), (4036, 4036, 388733998287090340141), (4037, 4037, 384885146818901326873), (4038, 4038, 381074402790991412745), (4039, 4039, 377301388901971695787), (4040, 4040, 373565731586110589889), (4041, 4041, 369867060976347118702), (4042, 4042, 366205010867670414556), (4043, 4043, 362579218680861796590), (4044, 4044, 358989325426595838208), (4045, 4045, 355434975669896869513), (4046, 4046, 351915817494947395557), (4047, 4047, 348431502470244946096), (4048, 4048, 344981685614103907026), (4049, 4049, 341566025360498917848), (4050, 4050, 338184183525246453314), (4051, 4051, 334835825272521240905), (4052, 4052, 331520619081704198916), (4053, 4053, 328238236714558612788), (4054, 4054, 324988353182731299790), (4055, 4055, 321770646715575544347), (4056, 4056, 318584798728292618165), (4057, 4057, 315430493790388730857), (4058, 4058, 312307419594444287977), (4059, 4059, 309215266925192364334), (4060, 4060, 306153729628903331023), (4061, 4061, 303122504583072604974), (4062, 4062, 300121291666408519776), (4063, 4063, 297149793729117346313), (4064, 4064, 294207716563482521102), (4065, 4065, 291294768874735169408), (4066, 4066, 288410662252213039018), (4067, 4067, 285555111140804989126), (4068, 4068, 282727832812678207056), (4069, 4069, 279928547339285353521), (4070, 4070, 277156977563648864872), (4071, 4071, 274412849072919668190), (4072, 4072, 271695890171207592267), (4073, 4073, 269005831852680784423), (4074, 4074, 266342407774931469726), (4075, 4075, 263705354232605415570), (4076, 4076, 261094410131292490664), (4077, 4077, 258509316961675733330), (4078, 4078, 255949818773936369634), (4079, 4079, 253415662152412247162), (4080, 4080, 250906596190507175408), (4081, 4081, 248422372465848688523), (4082, 4082, 245962745015691770815), (4083, 4083, 243527470312566109718), (4084, 4084, 241116307240164465067), (4085, 4085, 238729017069469767393), (4086, 4086, 236365363435118581577), (4087, 4087, 234025112311998595621), (4088, 4088, 231708031992077817447), (4089, 4089, 229413893061463185591), (4090, 4090, 227142468377686322367), (4091, 4091, 224893533047214180561), (4092, 4092, 222666864403182356992), (4093, 4093, 220462241983348868308), (4094, 4094, 218279447508266206246), (4095, 4095, 216118264859669511135), (4096, 4096, 213978480059078723896), (4097, 4097, 211859881246612597917), (4098, 4098, 209762258660012473185), (4099, 4099, 207685404613873735826), (4100, 4100, 205629113479082906759), (4101, 4101, 203593181662458323524), (4102, 4102, 201577407586592399528), (4103, 4103, 199581591669893464880), (4104, 4104, 197605536306825212752), (4105, 4105, 195649045848341794804), (4106, 4106, 193711926582516628519), (4107, 4107, 191793986715362998534), (4108, 4108, 189895036351844553003), (4109, 4109, 188014887477073814855), (4110, 4110, 186153353937696846391), (4111, 4111, 184310251423462224150), (4112, 4112, 182485397448972499158), (4113, 4113, 180678611335616335800), (4114, 4114, 178889714193679540396), (4115, 4115, 177118528904633208313), (4116, 4116, 175364880103597235953), (4117, 4117, 173628594161977461340), (4118, 4118, 171909499170274714198), (4119, 4119, 170207424921064073463), (4120, 4120, 168522202892142646993), (4121, 4121, 166853666229844204944), (4122, 4122, 165201649732519014796), (4123, 4123, 163565989834177242372), (4124, 4124, 161946524588294299379), (4125, 4125, 160343093651776534038), (4126, 4126, 158755538269085677266), (4127, 4127, 157183701256520472540), (4128, 4128, 155627426986653933208), (4129, 4129, 154086561372924686345), (4130, 4130, 152560951854380877569), (4131, 4131, 151050447380575126306), (4132, 4132, 149554898396609035946), (4133, 4133, 148074156828325778165), (4134, 4134, 146608076067649285312), (4135, 4135, 145156510958068599318), (4136, 4136, 143719317780265939919), (4137, 4137, 142296354237887069227), (4138, 4138, 140887479443452543789), (4139, 4139, 139492553904408459197), (4140, 4140, 138111439509315306136), (4141, 4141, 136743999514173570432), (4142, 4142, 135390098528884723200), (4143, 4143, 134049602503846260594), (4144, 4144, 132722378716679465934), (4145, 4145, 131408295759088580133), (4146, 4146, 130107223523850079340), (4147, 4147, 128819033191930771623), (4148, 4148, 127543597219733437251), (4149, 4149, 126280789326468749753), (4150, 4150, 125030484481652227478), (4151, 4151, 123792558892724977701), (4152, 4152, 122566889992797007625), (4153, 4153, 121353356428511888738), (4154, 4154, 120151838048031573008), (4155, 4155, 118962215889140171295), (4156, 4156, 117784372167465516134), (4157, 4157, 116618190264817342706), (4158, 4158, 115463554717640933373), (4159, 4159, 114320351205585082547), (4160, 4160, 113188466540183250047), (4161, 4161, 112067788653646782225), (4162, 4162, 110958206587769091311), (4163, 4163, 109859610482939694368), (4164, 4164, 108771891567267024127), (4165, 4165, 107694942145808934779), (4166, 4166, 106628655589909836415), (4167, 4167, 105572926326643402391), (4168, 4168, 104527649828359804347), (4169, 4169, 103492722602336439948), (4170, 4170, 102468042180531128661), (4171, 4171, 101453507109436761051), (4172, 4172, 100449016940036397080), (4173, 4173, 99454472217857818891), (4174, 4174, 98469774473126553357), (4175, 4175, 97494826211016389463), (4176, 4176, 96529530901996425211), (4177, 4177, 95573792972273688327), (4178, 4178, 94627517794330384483), (4179, 4179, 93690611677554836121), (4180, 4180, 92762981858965184279), (4181, 4181, 91844536494024934929), (4182, 4182, 90935184647549440524), (4183, 4183, 90034836284702416360), (4184, 4184, 89143402262081600357), (4185, 4185, 88260794318892673621), (4186, 4186, 87386925068210567941), (4187, 4187, 86521707988327294991), (4188, 4188, 85665057414185440586), (4189, 4189, 84816888528896475827), (4190, 4190, 83977117355343045374), (4191, 4191, 83145660747864401360), (4192, 4192, 82322436384024159762), (4193, 4193, 81507362756459564121), (4194, 4194, 80700359164811449625), (4195, 4195, 79901345707734108539), (4196, 4196, 79110243274984265881), (4197, 4197, 78326973539588382060), (4198, 4198, 77551458950087506990), (4199, 4199, 76783622722858917812), (4200, 4200, 76023388834513780012), (4201, 4201, 75270682014370079220), (4202, 4202, 74525427737000078435), (4203, 4203, 73787552214851562807), (4204, 4204, 73056982390942141393), (4205, 4205, 72333645931625882568), (4206, 4206, 71617471219431566899), (4207, 4207, 70908387345971848415), (4208, 4208, 70206324104922622193), (4209, 4209, 69511211985071903161), (4210, 4210, 68822982163437527882), (4211, 4211, 68141566498452997903), (4212, 4212, 67466897523220790003), (4213, 4213, 66798908438832465350), (4214, 4214, 66137533107754916188), (4215, 4215, 65482706047282095235), (4216, 4216, 64834362423051579441), (4217, 4217, 64192438042625326179), (4218, 4218, 63556869349133986316), (4219, 4219, 62927593414984144867), (4220, 4220, 62304547935627866205), (4221, 4221, 61687671223393926936), (4222, 4222, 61076902201380125679), (4223, 4223, 60472180397406065029), (4224, 4224, 59873445938025806959), (4225, 4225, 59280639542599808871), (4226, 4226, 58693702517425553337), (4227, 4227, 58112576749926290433), (4228, 4228, 57537204702897317260), (4229, 4229, 56967529408809225010), (4230, 4230, 56403494464167549515), (4231, 4231, 55845044023928266847), (4232, 4232, 55292122795968581036), (4233, 4233, 54744676035612456472), (4234, 4234, 54202649540210352942), (4235, 4235, 53665989643772626675), (4236, 4236, 53134643211656066015), (4237, 4237, 52608557635303035659), (4238, 4238, 52087680827032708573), (4239, 4239, 51571961214883869874), (4240, 4240, 51061347737508782054), (4241, 4241, 50555789839117605994), (4242, 4242, 50055237464472877222), (4243, 4243, 49559641053933541804), (4244, 4244, 49068951538548061192), (4245, 4245, 48583120335196100190), (4246, 4246, 48102099341778317020), (4247, 4247, 47625840932453779227), (4248, 4248, 47154297952924533888), (4249, 4249, 46687423715766865236), (4250, 4250, 46225171995808777461), (4251, 4251, 45767497025553245011), (4252, 4252, 45314353490646777239), (4253, 4253, 44865696525392848751), (4254, 4254, 44421481708309751239), (4255, 4255, 43981665057732426969), (4256, 4256, 43546203027457848485), (4257, 4257, 43115052502433513351), (4258, 4258, 42688170794488627080), (4259, 4259, 42265515638107551565), (4260, 4260, 41847045186245100559), (4261, 4261, 41432718006183267880), (4262, 4262, 41022493075428978099), (4263, 4263, 40616329777652453564), (4264, 4264, 40214187898665795608), (4265, 4265, 39816027622441381790), (4266, 4266, 39421809527169684940), (4267, 4267, 39031494581356123703), (4268, 4268, 38645044139956558122), (4269, 4269, 38262419940551047646), (4270, 4270, 37883584099555492718), (4271, 4271, 37508499108470784870), (4272, 4272, 37137127830169093930), (4273, 4273, 36769433495216924684), (4274, 4274, 36405379698234578895), (4275, 4275, 36044930394291662272), (4276, 4276, 35688049895338279477), (4277, 4277, 35334702866671563839), (4278, 4278, 34984854323437191920), (4279, 4279, 34638469627165536554), (4280, 4280, 34295514482342115400), (4281, 4281, 33955954933011995446), (4282, 4282, 33619757359417817273), (4283, 4283, 33286888474671106211), (4284, 4284, 32957315321456540803), (4285, 4285, 32631005268768852280), (4286, 4286, 32307926008682031960), (4287, 4287, 31988045553150526693), (4288, 4288, 31671332230842105637), (4289, 4289, 31357754684002084789), (4290, 4290, 31047281865348598801), (4291, 4291, 30739883034998612674), (4292, 4292, 30435527757424368985), (4293, 4293, 30134185898439969292), (4294, 4294, 29835827622217791378), (4295, 4295, 29540423388334446909), (4296, 4296, 29247943948845987038), (4297, 4297, 28958360345392066375), (4298, 4298, 28671643906328778589), (4299, 4299, 28387766243889879791), (4300, 4300, 28106699251376118605), (4301, 4301, 27828415100372394658), (4302, 4302, 27552886237992469959), (4303, 4303, 27280085384150960355), (4304, 4304, 27009985528862336985), (4305, 4305, 26742559929566670282), (4306, 4306, 26477782108481851765), (4307, 4307, 26215625849982031450), (4308, 4308, 25956065198002011337), (4309, 4309, 25699074453467337957), (4310, 4310, 25444628171749839562), (4311, 4311, 25192701160148356002), (4312, 4312, 24943268475394411883), (4313, 4313, 24696305421182586023), (4314, 4314, 24451787545725332696), (4315, 4315, 24209690639332012570), (4316, 4316, 23969990732011893634), (4317, 4317, 23732664091100884786), (4318, 4318, 23497687218911767115), (4319, 4319, 23265036850407690213), (4320, 4320, 23034689950898703181), (4321, 4321, 22806623713761092258), (4322, 4322, 22580815558179299266), (4323, 4323, 22357243126910197293), (4324, 4324, 22135884284069502270), (4325, 4325, 21916717112940101257), (4326, 4326, 21699719913802080453), (4327, 4327, 21484871201784238072), (4328, 4328, 21272149704736869378), (4329, 4329, 21061534361125613246), (4330, 4330, 20853004317946151729), (4331, 4331, 20646538928659556167), (4332, 4332, 20442117751148075413), (4333, 4333, 20239720545691163775), (4334, 4334, 20039327272961548292), (4335, 4335, 19840918092041136923), (4336, 7209, 19644473358456571211)]

def glob4 : ℕ := 2698500957556355349776

def runs5 : List (ℕ × ℕ × ℕ) := [(0, 3828, 0), (3829, 3829, 225726567803128162), (3830, 3830, 225784196484782355), (3831, 3831, 225888399611699870), (3832, 3832, 226040659274893577), (3833, 3833, 226242553868973889), (3834, 3834, 226495765261478870), (3835, 3835, 226802086616267701), (3836, 3836, 227163430940893284), (3837, 3837, 227581840436458904), (3838, 3838, 228059496738245512), (3839, 3839, 228598732146554602), (3840, 3840, 229202041959963071), (3841, 3841, 229872098037783931), (3842, 3842, 230611763735268102), (3843, 3843, 231424110374317931), (3844, 3844, 232312435434626124), (3845, 3845, 233280282675692795), (3846, 3846, 234331464429687157), (3847, 3847, 235470086339295739), (3848, 3848, 236700574854352654), (3849, 3849, 238027707847152702), (3850, 3850, 239456648760067257), (3851, 3851, 240992984761806506), (3852, 3852, 242642769462067078), (3853, 3853, 244412570820374053), (3854, 3854, 246309524986081247), (3855, 3855, 248341396925639605), (3856, 3856, 250516648833890447), (3857, 3857, 252844517492533750), (3858, 3858, 255335101936204563), (3859, 3859, 257999463020999556), (3860, 3860, 260849736769400340), (3861, 3861, 263899263698532505), (3862, 3862, 267162736736740874), (3863, 3863, 270656370810097045), (3864, 3864, 274398097752097022), (3865, 3865, 278407790876290305), (3866, 3866, 282707524376784071), (3867, 3867, 287321873714055231), (3868, 3868, 292278264337159013), (3869, 3869, 297607377527907956), (3870, 3870, 303343623873459389), (3871, 3871, 309525696931792645), (3872, 3872, 316197222103815141), (3873, 3873, 323407518619133981), (3874, 3874, 331212495922879865), (3875, 3875, 339675709636044444), (3876, 3876, 348869606617066014), (3877, 3877, 358876993346105880), (3878, 3878, 369792766582877621), (3879, 3879, 381725949422399541), (3880, 3880, 394802078425774345), (3881, 3881, 409165986616758037), (3882, 3882, 424985019827034430), (3883, 3883, 442452705426204826), (3884, 3884, 461792855704997752), (3885, 3885, 483264022657835509), (3886, 3886, 507164112418846821), (3887, 3887, 533834798650178391), (3888, 3888, 563665127066836442), (3889, 3889, 597093368386358073), (3890, 3890, 634605769762852968), (3891, 3891, 676730444002015718), (3892, 3892, 724024379492385987), (3893, 3893, 777051722043640101), (3894, 3894, 836352419376508716), (3895, 3895, 902402295463025654), (3896, 3896, 975568521756284348), (3897, 3897, 1056067480708724887), (3898, 3898, 1143933728399422066), (3899, 3899, 1239007731778658285), (3900, 3900, 1340945969569934457), (3901, 3901, 1449251263016865388), (3902, 3902, 1563316329535499947), (3903, 3903, 1682471496475909839), (3904, 3904, 1806028570022449457), (3905, 3905, 1933315825998520025), (3906, 3906, 2063702351817560348), (3907, 3907, 2196612412472259023), (3908, 3908, 2331531805552429610), (3909, 3909, 2468008511950479575), (3910, 3910, 2605649722262636814), (3911, 3911, 2744116858585979596), (3912, 3912, 2883119728146463136), (3913, 3913, 3022410538117620096), (3914, 3914, 3161778197726847552), (3915, 3915, 3301043126296972835), (3916, 3916, 3440052653592022230), (3917, 3917, 3578677020165209223), (3918, 3918, 3716805942484246645), (3919, 3919, 3854345687248020007), (3920, 3920, 3991216592447819048), (3921, 3921, 4127350973453199271), (3922, 3922, 4262691357021700889), (3923, 3923, 4397188992427319311), (3924, 3924, 4530802595607963553), (3925, 3925, 4663497288668738019), (3926, 3926, 4795243702920427118), (3927, 3927, 4926017218759905651), (3928, 3928, 5055797320102554717), (3929, 3929, 5184567044804577719), (3930, 3930, 5312312515638920399), (3931, 3931, 5439022538992904293), (3932, 3932, 5564688260616805252), (3933, 3933, 5689302869541518034), (3934, 3934, 5812861342762426404), (3935, 3935, 5935360224508942219), (3936, 3936, 6056797434929779732), (3937, 3937, 6177172103860305816), (3938, 3938, 6296484426031207388), (3939, 3939, 6414735534652730471), (3940, 3940, 6531927390786790765), (3941, 3941, 6648062686317472577), (3942, 3942, 6763144758662851499), (3943, 3943, 6877177515649178993), (3944, 3944, 6990165369201656290), (3945, 3945, 7102113176702005227), (3946, 3946, 7213026189028136341), (3947, 3947, 7322910004430613212), (3948, 3948, 7431770527518591052), (3949, 3949, 7539613932727990606), (3950, 3950, 7646446631729766409), (3951, 3951, 7752275244308650365), (3952, 3952, 7857106572304695604), (3953, 3953, 7960947576262972326), (3954, 3954, 8063805354482259919), (3955, 3955, 8165687124192692682), (3956, 3956, 8266600204626015755), (3957, 3957, 8366552001771202919), (3958, 3958, 8465549994633359094), (3959, 3959, 8563601722835650236), (3960, 3960, 8660714775422955057), (3961, 3961, 8756896780742425222), (3962, 3962, 8852155397290519345), (3963, 3963, 8946498305428635216), (3964, 3964, 9039933199880454097), (3965, 3965, 9132467782933743809), (3966, 3966, 9224109758277825506), (3967, 3967, 9314866825415348438), (3968, 3968, 9404746674593570910), (3969, 3969, 9493756982206128868), (3970, 3970, 9581905406621384691), (3971, 3971, 9669199584397972902), (3972, 3972, 9755647126852170077), (3973, 3973, 9841255616945276751), (3974, 3974, 9926032606462364692), (3975, 3975, 10009985613456561261), (3976, 3976, 10093122119935555270), (3977, 3977, 10175449569769251975), (3978, 3978, 10256975366799510118), (3979, 3979, 10337706873134688822), (3980, 3980, 10417651407613340758), (3981, 3981, 10496816244422831465), (3982, 3982, 10575208611859961518), (3983, 3983, 10652835691221834706), (3984, 3984, 10729704615816265824), (3985, 3985, 10805822470081968676), (3986, 3986, 10881196288809619662), (3987, 3987, 10955833056455664578), (3988, 3988, 11029739706541434814), (3989, 3989, 11102923121130771643), (3990, 3990, 11175390130379930544), (3991, 3991, 11247147512154057705), (3992, 3992, 11318201991705003157), (3993, 3993, 11388560241405664491), (3994, 3994, 11458228880536445830), (3995, 3995, 11527214475119772591), (3996, 3996, 11595523537798927045), (3997, 3997, 11663162527757765650), (3998, 3998, 11730137850678149470), (3999, 3999, 11796455858732166052), (4000, 4000, 11862122850606447152), (4001, 4001, 11927145071556093616), (4002, 4002, 11991528713485908284), (4003, 4003, 12055279915056811681), (4004, 4004, 12118404761815474733), (4005, 4005, 12180909286345349338), (4006, 4006, 12242799468437412216), (4007, 4007, 12304081235279061368), (4008, 4008, 12364760461659718444), (4009, 4009, 12424842970191795339), (4010, 4010, 12484334531545780099), (4011, 4011, 12543240864698286498), (4012, 4012, 12601567637191994000), (4013, 4013, 12659320465406480953), (4014, 4014, 12716504914839024108), (4015, 4015, 12773126500394502640), (4016, 4016, 12829190686683604954), (4017, 4017, 12884702888328592281), (4018, 4018, 12939668470275924671), (4019, 4019, 12994092748115102793), (4020, 4020, 13047980988403123325), (4021, 4021, 13101338408993986878), (4022, 4022, 13154170179372735597), (4023, 4023, 13206481420993533091), (4024, 4024, 13258277207621332360), (4025, 4025, 13309562565676708016), (4026, 4026, 13360342474583457707), (4027, 4027, 13410621867118604171), (4028, 4028, 13460405629764454122), (4029, 4029, 13509698603062393216), (4030, 4030, 13558505581968117835), (4031, 4031, 13606831316208024478), (4032, 4032, 13654680510636496224), (4033, 4033, 13702057825593843215), (4034, 4034, 13748967877264670367), (4035, 4035, 13795415238036460772), (4036, 4036, 13841404436858177449), (4037, 4037, 13886939959598699424), (4038, 4038, 13932026249404920537), (4039, 4039, 13976667707059351013), (4040, 4040, 14020868691337072725), (4041, 4041, 14064633519361909270), (4042, 4042, 14107966466961681517), (4043, 4043, 14150871769022428232), (4044, 4044, 14193353619841479766), (4045, 4045, 14235416173479280649), (4046, 4046, 14277063544109864285), (4047, 4047, 14318299806369889860), (4048, 4048, 14359128995706158055), (4049, 4049, 14399555108721528237), (4050, 4050, 14439582103519165484), (4051, 4051, 14479213900045051213), (4052, 4052, 14518454380428696139), (4053, 4053, 14557307389321999076), (4054, 4054, 14595776734236199509), (4055, 4055, 14633866185876876028), (4056, 4056, 14671579478476946639), (4057, 4057, 14708920310127630672), (4058, 4058, 14745892343107335431), (4059, 4059, 14782499204208434018), (4060, 4060, 14818744485061903807), (4061, 4061, 14854631742459797928), (4062, 4062, 14890164498675524824), (4063, 4063, 14925346241781913503), (4064, 4064, 14960180425967044475), (4065, 4065, 14994670471847828646), (4066, 4066, 15028819766781318538), (4067, 4067, 15062631665173738205), (4068, 4068, 15096109488787220094), (4069, 4069, 15129256527044238843), (4070, 4070, 15162076037329733701), (4071, 4071, 15194571245290912775), (4072, 4072, 15226745345134733803), (4073, 4073, 15258601499923057517), (4074, 4074, 15290142841865470974), (4075, 4075, 15321372472609779410), (4076, 4076, 15352293463530166384), (4077, 4077, 15382908856013022979), (4078, 4078, 15413221661740447903), (4079, 4079, 15443234862971421240), (4080, 4080, 15472951412820655504), (4081, 4081, 15502374235535128507), (4082, 4082, 15531506226768303290), (4083, 4083, 15560350253852041151), (4084, 4084, 15588909156066214460), (4085, 4085, 15617185744906026615), (4086, 4086, 15645182804347047079), (4087, 4087, 15672903091107970039), (4088, 4088, 15700349334911105706), (4089, 4089, 15727524238740613820), (4090, 4090, 15754430479098489354), (4091, 4091, 15781070706258310844), (4092, 4092, 15807447544516762201), (4093, 4093, 15833563592442939181), (4094, 4094, 15859421423125452103), (4095, 4095, 15885023584417336659), (4096, 4096, 15910372599178785022), (4097, 4097, 15935470965517709684), (4098, 4098, 15960321157028152732), (4099, 4099, 15984925623026553525), (4100, 4100, 16009286788785887912), (4101, 4101, 16033407055767692352), (4102, 4102, 16057288801851986491), (4103, 4103, 16080934381565107892), (4104, 4104, 16104346126305472773), (4105, 4105, 16127526344567276763), (4106, 4106, 16150477322162149778), (4107, 4107, 16173201322438779253), (4108, 4108, 16195700586500516061), (4109, 4109, 16217977333420977520), (4110, 4110, 16240033760457661993), (4111, 4111, 16261872043263589625), (4112, 4112, 16283494336096983833), (4113, 4113, 16304902772029008206), (4114, 4114, 16326099463149573517), (4115, 4115, 16347086500771229557), (4116, 4116, 16367865955631156566), (4117, 4117, 16388439878091270999), (4118, 4118, 16408810298336460414), (4119, 4119, 16428979226570962249), (4120, 4120, 16448948653212901258), (4121, 4121, 16468720549087000364), (4122, 4122, 16488296865615479668), (4123, 4123, 16507679535007158333), (4124, 4124, 16526870470444774048), (4125, 4125, 16545871566270534714), (4126, 4126, 16564684698169917003), (4127, 4127, 16583311723353726362), (4128, 4128, 16601754480738433008), (4129, 4129, 16620014791124798428), (4130, 4130, 16638094457374806807), (4131, 4131, 16655995264586915802), (4132, 4132, 16673718980269640982), (4133, 4133, 16691267354513488220), (4134, 4134, 16708642120161248260), (4135, 4135, 16725844992976667592), (4136, 4136, 16742877671811509736), (4137, 4137, 16759741838771020947), (4138, 4138, 16776439159377814277), (4139, 4139, 16792971282734185876), (4140, 4140, 16809339841682877324), (4141, 4141, 16825546452966297705), (4142, 4142, 16841592717384219084), (4143, 4143, 16857480219949958927), (4144, 4144, 16873210530045062964), (4145, 4145, 16888785201572501878), (4146, 4146, 16904205773108395152), (4147, 4147, 16919473768052275288), (4148, 4148, 16934590694775905566), (4149, 4149, 16949558046770664375), (4150, 4150, 16964377302793509121), (4151, 4151, 16979049927011532576), (4152, 4152, 16993577369145124469), (4153, 4153, 17007961064609751042), (4154, 4154, 17022202434656365169), (4155, 4155, 17036302886510459589), (4156, 4156, 17050263813509775678), (4157, 4157, 17064086595240680117), (4158, 4158, 17077772597673221709), (4159, 4159, 17091323173294880525), (4160, 4160, 17104739661243021438), (4161, 4161, 17118023387436064044), (4162, 4162, 17131175664703380855), (4163, 4163, 17144197792913935577), (4164, 4164, 17157091059103673170), (4165, 4165, 17169856737601673320), (4166, 4166, 17182496090155078848), (4167, 4167, 17195010366052810489), (4168, 4168, 17207400802248079390), (4169, 4169, 17219668623479708582), (4170, 4170, 17231815042392274585), (4171, 4171, 17243841259655080222), (4172, 4172, 17255748464079969619), (4173, 4173, 17267537832737996293), (4174, 4174, 17279210531074955117), (4175, 4175, 17290767713025788878), (4176, 4176, 17302210521127880058), (4177, 4177, 17313540086633238356), (4178, 4178, 17324757529619594416), (4179, 4179, 17335863959100410092), (4180, 4180, 17346860473133815536), (4181, 4181, 17357748158930483293), (4182, 4182, 17368528092960449469), (4183, 4183, 17379201341058892015), (4184, 4184, 17389768958530876013), (4185, 4185, 17400231990255075821), (4186, 4186, 17410591470786483814), (4187, 4187, 17420848424458115390), (4188, 4188, 17431003865481719806), (4189, 4189, 17441058798047506364), (4190, 4190, 17451014216422895328), (4191, 4191, 17460871105050302921), (4192, 4192, 17470630438643969638), (4193, 4193, 17480293182285841040), (4194, 4194, 17489860291520510105), (4195, 4195, 17499332712449230148), (4196, 4196, 17508711381823007209), (4197, 4197, 17517997227134780777), (4198, 4198, 17527191166710701578), (4199, 4199, 17536294109800515130), (4200, 4200, 17545306956667059664), (4201, 4201, 17554230598674886920), (4202, 4202, 17563065918378014291), (4203, 4203, 17571813789606816657), (4204, 4204, 17580475077554066225), (4205, 4205, 17589050638860128579), (4206, 4206, 17597541321697323094), (4207, 4207, 17605947965853455771), (4208, 4208, 17614271402814532491), (4209, 4209, 17622512455846660619), (4210, 4210, 17630671940077146788), (4211, 4211, 17638750662574798649), (4212, 4212, 17646749422429438292), (4213, 4213, 17654669010830634962), (4214, 4214, 17662510211145664638), (4215, 4215, 17670273798996703963), (4216, 4216, 17677960542337265949), (4217, 4217, 17685571201527884805), (4218, 4218, 17693106529411057176), (4219, 4219, 17700567271385447011), (4220, 4220, 17707954165479361198), (4221, 4221, 17715267942423503062), (4222, 4222, 17722509325723010725), (4223, 4223, 17729679031728787300), (4224, 4224, 17736777769708129774), (4225, 4225, 17743806241914663424), (4226, 4226, 17750765143657588514), (4227, 4227, 17757655163370245957), (4228, 4228, 17764476982678008580), (4229, 4229, 17771231276465504552), (4230, 4230, 17777918712943179491), (4231, 4231, 17784539953713203666), (4232, 4232, 17791095653834730712), (4233, 4233, 17797586461888514145), (4234, 4234, 17804013020040887962), (4235, 4235, 17810375964107117512), (4236, 4236, 17816675923614126796), (4237, 4237, 17822913521862608260), (4238, 4238, 17829089375988521130), (4239, 4239, 17835204097023984245), (4240, 4240, 17841258289957569297), (4241, 4241, 17847252553794000347), (4242, 4242, 17853187481613265406), (4243, 4243, 17859063660629145828), (4244, 4244, 17864881672247169213), (4245, 4245, 17870642092121991438), (4246, 4246, 17876345490214213417), (4247, 4247, 17881992430846638105), (4248, 4248, 17887583472759973223), (4249, 4249, 17893119169167985131), (4250, 4250, 17898600067812109220), (4251, 4251, 17904026711015522127), (4252, 4252, 17909399635736681071), (4253, 4253, 17914719373622335491), (4254, 4254, 17919986451060016183), (4255, 4255, 17925201389230007036), (4256, 4256, 17930364704156804446), (4257, 4257, 17935476906760069413), (4258, 4258, 17940538502905077313), (4259, 4259, 17945549993452670243), (4260, 4260, 17950511874308716843), (4261, 4261, 17955424636473084395), (4262, 4262, 17960288766088128001), (4263, 4263, 17965104744486701568), (4264, 4264, 17969873048239695294), (4265, 4265, 17974594149203104292), (4266, 4266, 17979268514564632960), (4267, 4267, 17983896606889839652), (4268, 4268, 17988478884167826148), (4269, 4269, 17993015799856476416), (4270, 4270, 17997507802927249066), (4271, 4271, 18001955337909527882), (4272, 4272, 18006358844934534794), (4273, 4273, 18010718759778809546), (4274, 4274, 18015035513907260356), (4275, 4275, 18019309534515789755), (4276, 4276, 18023541244573499789), (4277, 4277, 18027731062864480714), (4278, 4278, 18031879404029187280), (4279, 4279, 18035986678605406650), (4280, 4280, 18040053293068821972), (4281, 4281, 18044079649873175577), (4282, 4282, 18048066147490035744), (4283, 4283, 18052013180448170913), (4284, 4284, 18055921139372535230), (4285, 4285, 18059790411022869220), (4286, 4286, 18063621378331919395), (4287, 4287, 18067414420443280531), (4288, 4288, 18071169912748864325), (4289, 4289, 18074888226925998124), (4290, 4290, 18078569730974157335), (4291, 4291, 18082214789251335156), (4292, 4292, 18085823762510053162), (4293, 4293, 18089397007933016311), (4294, 4294, 18092934879168415843), (4295, 4295, 18096437726364883553), (4296, 4296, 18099905896206100872), (4297, 4297, 18103339731945066135), (4298, 4298, 18106739573438023425), (4299, 4299, 18110105757178056304), (4300, 4300, 18113438616328349751), (4301, 4301, 18116738480755123546), (4302, 4302, 18120005677060240372), (4303, 4303, 18123240528613491801), (4304, 4304, 18126443355584565367), (4305, 4305, 18129614474974695845), (4306, 4306, 18132754200648003865), (4307, 4307, 18135862843362524922), (4308, 4308, 18138940710800931848), (4309, 4309, 18141988107600953765), (4310, 4310, 18145005335385494489), (4311, 4311, 18147992692792453383), (4312, 4312, 18150950475504251553), (4313, 4313, 18153878976277066314), (4314, 4314, 18156778484969776805), (4315, 4315, 18159649288572623571), (4316, 4316, 18162491671235584968), (4317, 4317, 18165305914296473157), (4318, 4318, 18168092296308752459), (4319, 4319, 18170851093069082812), (4320, 4320, 18173582577644591034), (4321, 4321, 18176287020399872575), (4322, 4322, 18178964689023726427), (4323, 4323, 18181615848555625810), (4324, 4324, 18184240761411927240), (4325, 4325, 18186839687411820573), (4326, 4326, 18189412883803022561), (4327, 4327, 18191960605287216465), (4328, 4328, 18194483104045240219), (4329, 4329, 18196980629762025632), (4330, 4330, 18199453429651291081), (4331, 4331, 18201901748479990123), (4332, 4332, 18204325828592518447), (4333, 4333, 18206725909934681527), (4334, 4334, 18209102230077425367), (4335, 4335, 18211455024240332646), (4336, 7209, 18446744073709462082)]

def glob5 : ℕ := 20473586367471141001

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

def meanN : ℕ := 110506
def meanD : ℕ := 100000
def secN : ℕ := 93490
def secD : ℕ := 10000000
def countN : ℕ := 104187
def countD : ℕ := 10000000
def overN : ℕ := 40293
def overD : ℕ := 10000000
def mgfN : ℕ := 11817
def mgfD : ℕ := 1000
def scarfN : ℕ := 20624
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
theorem rc_θ : (rcPar.θ : ℝ) = 397071 / 200000 - 28883 / 2500000 := by norm_num [rcPar]
theorem rc_m : (rcPar.m : ℝ) = (meanN : ℝ) / meanD := by norm_num [rcPar, meanN, meanD]
theorem rc_vv : (rcPar.vv : ℝ) = (secN : ℝ) / secD := by norm_num [rcPar, secN, secD]

/-- `exp (B - a θ_mid) ≤ (9741 / 10000000 : ℝ)` from the Taylor lower bound of `exp (a θ_mid - B)`. -/
theorem rc_exp_mid : Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) ≤ (9741 / 10000000 : ℝ) := by
  have hx : (mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ ≤ -(3467 / 500 : ℝ) := by norm_num [rcPar, mgfN, mgfD]
  have h0 : (0 : ℝ) ≤ (3467 / 500 : ℝ) := by norm_num
  have he := Real.sum_le_exp_of_nonneg h0 30
  have hs : (10000000 / 9741 : ℝ) ≤ ∑ i ∈ Finset.range 30, (3467 / 500 : ℝ) ^ i / (Nat.factorial i) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  refine (Real.exp_le_exp.mpr hx).trans ?_
  rw [Real.exp_neg, show (9741 / 10000000 : ℝ) = ((10000000 / 9741 : ℝ))⁻¹ by norm_num]
  exact inv_anti₀ (by norm_num) (hs.trans he)

/-- Route-C total at the middle threshold: `K0 + K1 + O Λ + tF ≤ (2143 / 1000000 : ℝ)`. -/
theorem rc_total_mid :
    3 / (8 * (rcPar.a : ℝ)) * Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (2143 / 1000000 : ℝ) := by
  have hk : (0 : ℝ) ≤ 3 / (8 * (rcPar.a : ℝ)) := by rw [rc_a]; norm_num
  have h1 := mul_le_mul_of_nonneg_left rc_exp_mid hk
  have h2 : 3 / (8 * (rcPar.a : ℝ)) * (9741 / 10000000 : ℝ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (2143 / 1000000 : ℝ) := by
    rw [rc_a]; norm_num [scarfN, scarfD, overN, overD, countN, countD, longN, longD]
  linarith

/-- Low threshold: `3/(8a) exp (B - a (1 - 28883/2500000)) + O ≤ 49/100`. -/
theorem rc_total_low :
    3 / (8 * (rcPar.a : ℝ)) * Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * (1 - 28883 / 2500000)) + (overN : ℝ) / overD ≤
      49 / 100 := by
  have hy : (mgfN : ℝ) / mgfD - rcPar.a * (1 - 28883 / 2500000) ≤ 2 + 43 / 100 := by norm_num [rcPar, mgfN, mgfD]
  have hx : Real.exp ((43 / 100 : ℝ) / 2) ≤ 1 / (1 - (43 / 100 : ℝ) / 2) := by
    have h := Real.add_one_le_exp (-((43 / 100 : ℝ) / 2))
    rw [Real.exp_neg] at h
    rw [le_div_iff₀ (by norm_num)]
    have hpos := Real.exp_pos ((43 / 100 : ℝ) / 2)
    have h' : (1 - (43 / 100 : ℝ) / 2) * Real.exp ((43 / 100 : ℝ) / 2) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h hpos.le
      rwa [inv_mul_cancel₀ hpos.ne', show -((43 / 100 : ℝ) / 2) + 1 = 1 - (43 / 100 : ℝ) / 2 by ring] at this
    linarith
  have he : Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * (1 - 28883 / 2500000)) ≤
      (2.7182818286 : ℝ) ^ 2 * (1 / (1 - (43 / 100 : ℝ) / 2)) ^ 2 := by
    refine (Real.exp_le_exp.mpr hy).trans ?_
    have hp : Real.exp (2 + 43 / 100 : ℝ) = Real.exp 1 ^ 2 * Real.exp ((43 / 100 : ℝ) / 2) ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [hp]
    exact mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le _)
      (pow_le_pow_left₀ (Real.exp_pos _).le hx _) (by positivity) (by positivity)
  have hk : (0 : ℝ) ≤ 3 / (8 * (rcPar.a : ℝ)) := by rw [rc_a]; norm_num
  have h1 := mul_le_mul_of_nonneg_left he hk
  have h2 : 3 / (8 * (rcPar.a : ℝ)) * ((2.7182818286 : ℝ) ^ 2 * (1 / (1 - (43 / 100 : ℝ) / 2)) ^ 2) +
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
    (2:ENNReal)^128 * ((929*2^62:Nat):ENNReal) *
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

noncomputable def feeCoefficient : ENNReal := 929/2^66

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

 theorem feeCoefficient_real : feeCoefficient.toReal = (929:ℝ)/2^66 := by
  norm_num [feeCoefficient,ENNReal.toReal_div]

 theorem cappedIncrement_nat (n : Nat) :
    cappedIncrement (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (Real.exp (6*min ((929:ℝ)/2^66*(n:ℝ)) (6/5))-1) := by
  rw [cappedIncrement_real _ (by unfold feeCoefficient; finiteness),
    ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast]

 theorem cappedResidual_nat (n : Nat) :
    cappedResidual (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (max 0 ((929:ℝ)/2^66*(n:ℝ)-6/5)) := by
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
    ((929:ℝ)/2^66) (alphabetSize:ℝ) ENNReal.toReal_nonneg hx).1
  rw [cappedIncrement_real _ (priceBucket_ne_top W)]
  calc
    _ ≤ ENNReal.ofReal ((maxFee:ℝ)*((929:ℝ)/2^66)*(alphabetSize:ℝ)/scale) :=
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

 theorem law_price_mean_bound : Law.lawAvg honestLaw (2^32) price ≤ (1109:ENNReal)/1000 := by
  rw [law_price_coordAverage]
  apply coordAverage_bound_of_rows (2^32) 1 1 (by norm_num) (by norm_num)
    id forestMoment (1109/1000) (fun _ _ h => h)
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

 theorem law_nearPrice_mean_bound : Law.lawAvg honestLaw (2^32) nearPrice ≤ (22894/50) := by
  rw [law_nearPrice_coordAverage]
  apply coordAverage_history_bound (2^32) 54 1 (by norm_num) (by norm_num)
    nearBucket (fun _ h => feeCoefficient*(SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit h:ENNReal))
    forestNearMoment (22894/50) (fun L b R => nearBucket_insert L R b)
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
    nearPrice average_nearScore (22894/50)
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
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((397071 : ℝ) / 200000 - 28883 / 2500000)) ≤
      ENNReal.ofReal ((2143 : ℝ) / 1000000) := by
  have hP := parFacts_of_ok rcPar par_ok
  have he : (fun W : List Proposal => price W - ENNReal.ofReal ((397071 : ℝ) / 200000 - 28883 / 2500000)) =
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
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((1 : ℝ) - 28883 / 2500000)) ≤
      ENNReal.ofReal ((49 : ℝ) / 100) := by
  have hP := parFacts_of_ok rcPar par_ok
  apply price_excess_of_bucket_bounds (2 ^ 32) (ENNReal.ofReal rcPar.c0) ENNReal.ofReal_ne_top
    (1 - 28883 / 2500000) (rcPar.a : ℝ) ((mgfN : ℝ) / mgfD) ((overN : ℝ) / overD) (49 / 100)
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
      (fun W => price W-ENNReal.ofReal ((397071:ℝ)/200000-28883/2500000)) ≤
        ENNReal.ofReal ((2143 : ℝ) / 1000000) := rc_excess_middle

theorem excess_high_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((2:ℝ)-4326/1000000-28883/2500000)) ≤
        ENNReal.ofReal ((53575347:ℝ)/25000000000) :=
  (Law.lawAvg_mono _ _ (fun W => tsub_le_tsub_left
    (ENNReal.ofReal_le_ofReal (by norm_num : (397071 : ℝ) / 200000 - 28883 / 2500000 ≤ 2 - 4326 / 1000000 - 28883 / 2500000)) _)).trans
    (rc_excess_middle.trans (ENNReal.ofReal_le_ofReal (by norm_num)))

theorem excess_low_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((1:ℝ)-28883/2500000)) ≤
        ENNReal.ofReal ((49:ℝ)/100) := rc_excess_low

/-- Large queries: the cap-777 envelope `(99076/100000) y` from the high and low endpoints (as in #938). -/
theorem excess_large_certified (y : ℝ)
    (hy0 : 2163/1000000 ≤ y) (hy1 : y ≤ 1/2) :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal (2-2*y-28883/2500000)) ≤
        ENNReal.ofReal ((99076/100000)*y) := by
  let t : ℝ := (y-2163/1000000)/(1/2-2163/1000000)
  have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hy0) (by norm_num)
  have ht1 : t≤1 := (div_le_one (by norm_num : (0:ℝ)<1/2-2163/1000000)).2 (by linarith)
  have h := price_excess_affine (2^32) (2-4326/1000000-28883/2500000) (1-28883/2500000)
    (53575347/25000000000) (49/100) t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ht0 ht1 excess_high_certified excess_low_certified
  have harg : (1-t)*(2-4326/1000000-28883/2500000)+t*(1-28883/2500000) = 2-2*y-28883/2500000 := by
    dsimp [t]; ring
  rw [harg] at h
  have hgap : (99076/100000)*y-((1-t)*(53575347/25000000000)+t*(49/100)) = t*(269/50000) := by
    dsimp [t]; ring
  have hval : (1-t)*(53575347/25000000000)+t*(49/100) ≤ (99076/100000)*y := by nlinarith
  exact h.trans (ENNReal.ofReal_le_ofReal hval)

/-- Tiny queries: affine interpolation between the middle and low endpoints. -/
theorem excess_tiny_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W=>price W-ENNReal.ofReal ((249:ℝ)/125-28883/2500000)) ≤
        ENNReal.ofReal ((18:ℝ)/5000) :=
  (Law.lawAvg_mono _ _ (fun W => tsub_le_tsub_left
    (ENNReal.ofReal_le_ofReal (by norm_num : (397071 : ℝ) / 200000 - 28883 / 2500000 ≤ 249 / 125 - 28883 / 2500000)) _)).trans
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
