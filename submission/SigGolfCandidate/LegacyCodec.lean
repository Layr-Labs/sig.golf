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

def rcPar : Par := ⟨926, (11 / 25 : ℚ), (19 / 2 : ℚ), (9868277 / 5000000 : ℚ), (110151 / 100000 : ℚ), (93003 / 10000000 : ℚ), (964381 / 10000000 : ℚ)⟩

-- Z7 (replay cut): f25ef952's rcPar and globs with our lineage's run layout (single bins only below the first bin
-- of lower price >= 60, then one top run; kind 5 from bin 4351), each fee the least `okOf` accepts
-- (docs/results/Z7/tools/rc_coarse.py; every env_* value stays within its literal).
def runs0 : List (ℕ × ℕ × ℕ) := [(0, 3841, 18446744073709551616), (3842, 3842, 18373881553386547996), (3843, 3843, 18191961934046087125), (3844, 3844, 18011843499055531807), (3845, 3845, 17833508414906467135), (3846, 3846, 17656939024659868451), (3847, 3847, 17482117846197889555), (3848, 3848, 17309027570492959956), (3849, 3849, 17137651059894019758), (3850, 3850, 16967971346429722533), (3851, 3851, 16799971630128438151), (3852, 3852, 16633635277354889259), (3853, 3853, 16468945819163256692), (3854, 3854, 16305886949666590784), (3855, 3855, 16144442524422367113), (3856, 3856, 15984596558834026844), (3857, 3857, 15826333226568343410), (3858, 3858, 15669636857988458822), (3859, 3859, 15514491938602434477), (3860, 3860, 15360883107527162849), (3861, 3861, 15208795155967487969), (3862, 3862, 15058213025710384128), (3863, 3863, 14909121807634043691), (3864, 3864, 14761506740231726427), (3865, 3865, 14615353208150224185), (3866, 3866, 14470646740742796223), (3867, 3867, 14327373010636431904), (3868, 3868, 14185517832313298915), (3869, 3869, 14045067160706236549), (3870, 3870, 13906007089808154999), (3871, 3871, 13768323851295202969), (3872, 3872, 13632003813163567296), (3873, 3873, 13497033478379769600), (3874, 3874, 13363399483544326337), (3875, 3875, 13231088597568639938), (3876, 3876, 13100087720364990037), (3877, 3877, 12970383881549495086), (3878, 3878, 12841964239157915927), (3879, 3879, 12714816078374174185), (3880, 3880, 12588926810271459589), (3881, 3881, 12464283970565801574), (3882, 3882, 12340875218381981756), (3883, 3883, 12218688335031665105), (3884, 3884, 12097711222803628817), (3885, 3885, 11977931903765969126), (3886, 3886, 11859338518580167451), (3887, 3887, 11741919325326898467), (3888, 3888, 11625662698343463828), (3889, 3889, 11510557127072736464), (3890, 3890, 11396591214923501449), (3891, 3891, 11283753678142080643), (3892, 3892, 11172033344695129349), (3893, 3893, 11061419153163494405), (3894, 3894, 10951900151647024164), (3895, 3895, 10843465496680221944), (3896, 3896, 10736104452158635588), (3897, 3897, 10629806388275876820), (3898, 3898, 10524560780471165168), (3899, 3899, 10420357208387292246), (3900, 3900, 10317185354838903214), (3901, 3901, 10215035004790993281), (3902, 3902, 10113896044347518100), (3903, 3903, 10013758459750017921), (3904, 3904, 9914612336386156357), (3905, 3905, 9816447857808075601), (3906, 3906, 9719255304760470892), (3907, 3907, 9623025054218288012), (3908, 3908, 9527747578433948527), (3909, 3909, 9433413443994008442), (3910, 3910, 9340013310885156874), (3911, 3911, 9247537931569462251), (3912, 3912, 9155978150068774506), (3913, 3913, 9065324901058192580), (3914, 3914, 8975569208968507505), (3915, 3915, 8886702187097532184), (3916, 3916, 8798715036730229885), (3917, 3917, 8711599046267554341), (3918, 3918, 8625345590363915189), (3919, 3919, 8539946129073183356), (3920, 3920, 8455392207003151837), (3921, 3921, 8371675452478368156), (3922, 3922, 8288787576711255600), (3923, 3923, 8206720372981441188), (3924, 3924, 8125465715823209097), (3925, 3925, 8045015560220999106), (3926, 3926, 7965361940812870402), (3927, 3927, 7886496971101851883), (3928, 3928, 7808412842675100874), (3929, 3929, 7731101824430792945), (3930, 3930, 7654556261812666282), (3931, 3931, 7578768576052144834), (3932, 3932, 7503731263417965182), (3933, 3933, 7429436894473232853), (3934, 3934, 7355878113339834508), (3935, 3935, 7283047636970133177), (3936, 3936, 7210938254425874432), (3937, 3937, 7139542826164232111), (3938, 3938, 7068854283330922882), (3939, 3939, 6998865627060319686), (3940, 3940, 6929569927782494738), (3941, 3941, 6860960324537123503), (3942, 3942, 6793030024294181686), (3943, 3943, 6725772301281368006), (3944, 3944, 6659180496318186145), (3945, 3945, 6593248016156619945), (3946, 3946, 6527968332828336580), (3947, 3947, 6463334982998353049), (3948, 3948, 6399341567325102029), (3949, 3949, 6335981749826833692), (3950, 3950, 6273249257254290784), (3951, 3951, 6211137878469594836), (3952, 3952, 6149641463831282016), (3953, 3953, 6088753924585427738), (3954, 3954, 6028469232262799741), (3955, 3955, 5968781418081979941), (3956, 3956, 5909684572358395982), (3957, 3957, 5851172843919203942), (3958, 3958, 5793240439523964299), (3959, 3959, 5735881623291053762), (3960, 3960, 5679090716129756200), (3961, 3961, 5622862095177976435), (3962, 3962, 5567190193245521223), (3963, 3963, 5512069498262892300), (3964, 3964, 5457494552735536931), (3965, 3965, 5403459953203501912), (3966, 3966, 5349960349706437536), (3967, 3967, 5296990445253898551), (3968, 3968, 5244544995300889654), (3969, 3969, 5192618807228603618), (3970, 3970, 5141206739830300612), (3971, 3971, 5090303702802277834), (3972, 3972, 5039904656239879043), (3973, 3973, 4990004610138494102), (3974, 3974, 4940598623899499111), (3975, 3975, 4891681805841088229), (3976, 3976, 4843249312713948741), (3977, 3977, 4795296349221731427), (3978, 3978, 4747818167546268740), (3979, 3979, 4700810066877493802), (3980, 3980, 4654267392948013665), (3981, 3981, 4608185537572290757), (3982, 3982, 4562559938190386889), (3983, 3983, 4517386077416224642), (3984, 3984, 4472659482590321428), (3985, 3985, 4428375725336951909), (3986, 3986, 4384530421125694959), (3987, 3987, 4341119228837321742), (3988, 3988, 4298137850333981923), (3989, 3989, 4255582030033645468), (3990, 3990, 4213447554488757889), (3991, 3991, 4171730251969067217), (3992, 3992, 4130425992048581403), (3993, 3993, 4089530685196615250), (3994, 3994, 4049040282372886386), (3995, 3995, 4008950774626620185), (3996, 3996, 3969258192699623945), (3997, 3997, 3929958606633291035), (3998, 3998, 3891048125379496074), (3999, 3999, 3852522896415342648), (4000, 4000, 3814379105361725394), (4001, 4001, 3776612975605668707), (4002, 4002, 3739220767926404660), (4003, 4003, 3702198780125153129), (4004, 4004, 3665543346658567454), (4005, 4005, 3629250838275809361), (4006, 4006, 3593317661659217189), (4007, 4007, 3557740259068531870), (4008, 4008, 3522515107988645416), (4009, 4009, 3487638720780837045), (4010, 4010, 3453107644337462421), (4011, 4011, 3418918459740061803), (4012, 4012, 3385067781920853270), (4013, 4013, 3351552259327577496), (4014, 4014, 3318368573591660887), (4015, 4015, 3285513439199664244), (4016, 4016, 3252983603167984400), (4017, 4017, 3220775844720776634), (4018, 4018, 3188886974971065974), (4019, 4019, 3157313836605015816), (4020, 4020, 3126053303569322590), (4021, 4021, 3095102280761705535), (4022, 4022, 3064457703724460926), (4023, 4023, 3034116538341050421), (4024, 4024, 3004075780535693486), (4025, 4025, 2974332455975934145), (4026, 4026, 2944883619778152619), (4027, 4027, 2915726356215992692), (4028, 4028, 2886857778431675933), (4029, 4029, 2858275028150174191), (4030, 4030, 2829975275396212070), (4031, 4031, 2801955718214071356), (4032, 4032, 2774213582390169660), (4033, 4033, 2746746121178385802), (4034, 4034, 2719550615028104754), (4035, 4035, 2692624371314955202), (4036, 4036, 2665964724074213072), (4037, 4037, 2639569033736844625), (4038, 4038, 2613434686868162995), (4039, 4039, 2587559095909072273), (4040, 4040, 2561939698919873537), (4041, 4041, 2536573959326607463), (4042, 4042, 2511459365669908379), (4043, 4043, 2486593431356344930), (4044, 4044, 2461973694412222703), (4045, 4045, 2437597717239824458), (4046, 4046, 2413463086376063820), (4047, 4047, 2389567412253528534), (4048, 4048, 2365908328963889638), (4049, 4049, 2342483494023653107), (4050, 4050, 2319290588142230799), (4051, 4051, 2296327314992307722), (4052, 4052, 2273591400982482893), (4053, 4053, 2251080595032161280), (4054, 4054, 2228792668348674535), (4055, 4055, 2206725414206608450), (4056, 4056, 2184876647729315297), (4057, 4057, 2163244205672589403), (4058, 4058, 2141825946210484558), (4059, 4059, 2120619748723252037), (4060, 4060, 2099623513587378255), (4061, 4061, 2078835161967701242), (4062, 4062, 2058252635611585388), (4063, 4063, 2037873896645134048), (4064, 4064, 2017696927371419850), (4065, 4065, 1997719730070712722), (4066, 4066, 1977940326802685864), (4067, 4067, 1958356759210580063), (4068, 4068, 1938967088327306993), (4069, 4069, 1919769394383472270), (4070, 4070, 1900761776617299278), (4071, 4071, 1881942353086434928), (4072, 4072, 1863309260481618741), (4073, 4073, 1844860653942196773), (4074, 4074, 1826594706873462152), (4075, 4075, 1808509610765804111), (4076, 4076, 1790603575015647634), (4077, 4077, 1772874826748165975), (4078, 4078, 1755321610641748490), (4079, 4079, 1737942188754206425), (4080, 4080, 1720734840350699431), (4081, 4081, 1703697861733365773), (4082, 4082, 1686829566072639380), (4083, 4083, 1670128283240237009), (4084, 4084, 1653592359643799019), (4085, 4085, 1637220158063167346), (4086, 4086, 1621010057488284501), (4087, 4087, 1604960452958697526), (4088, 4088, 1589069755404651015), (4089, 4089, 1573336391489753481), (4090, 4090, 1557758803455201466), (4091, 4091, 1542335448965546006), (4092, 4092, 1527064800955986144), (4093, 4093, 1511945347481174400), (4094, 4094, 1496975591565519208), (4095, 4095, 1482154051054969513), (4096, 4096, 1467479258470266845), (4097, 4097, 1452949760861650341), (4098, 4098, 1438564119665000338), (4099, 4099, 1424320910559406275), (4100, 4100, 1410218723326144827), (4101, 4101, 1396256161709054284), (4102, 4102, 1382431843276291371), (4103, 4103, 1368744399283456802), (4104, 4104, 1355192474538076042), (4105, 4105, 1341774727265421824), (4106, 4106, 1328489828975665172), (4107, 4107, 1315336464332341755), (4108, 4108, 1302313331022120549), (4109, 4109, 1289419139625861930), (4110, 4110, 1276652613490952406), (4111, 4111, 1264012488604903372), (4112, 4112, 1251497513470201358), (4113, 4113, 1239106448980397385), (4114, 4114, 1226838068297423153), (4115, 4115, 1214691156730121934), (4116, 4116, 1202664511613982113), (4117, 4117, 1190756942192061498), (4118, 4118, 1178967269497090592), (4119, 4119, 1167294326234743160), (4120, 4120, 1155736956668062535), (4121, 4121, 1144294016503032213), (4122, 4122, 1132964372775279419), (4123, 4123, 1121746903737900414), (4124, 4124, 1110640498750396450), (4125, 4125, 1099644058168709356), (4126, 4126, 1088756493236345897), (4127, 4127, 1077976725976580096), (4128, 4128, 1067303689085722868), (4129, 4129, 1056736325827448384), (4130, 4130, 1046273589928166717), (4131, 4131, 1035914445473432393), (4132, 4132, 1025657866805378607), (4133, 4133, 1015502838421166937), (4134, 4134, 1005448354872442512), (4135, 4135, 995493420665784666), (4136, 4136, 985637050164143233), (4137, 4137, 975878267489250726), (4138, 4138, 966216106425000719), (4139, 4139, 956649610321782890), (4140, 4140, 947177832001765238), (4141, 4141, 937799833665114097), (4142, 4142, 928514686797142670), (4143, 4143, 919321472076378881), (4144, 4144, 910219279283543447), (4145, 4145, 901207207211429155), (4146, 4146, 892284363575672431), (4147, 4147, 883449864926408347), (4148, 4148, 874702836560800344), (4149, 4149, 866042412436435984), (4150, 4150, 857467735085580182), (4151, 4151, 848977955530277408), (4152, 4152, 840572233198294464), (4153, 4153, 832249735839895508), (4154, 4154, 824009639445441097), (4155, 4155, 815851128163803067), (4156, 4156, 807773394221587195), (4157, 4157, 799775637843155638), (4158, 4158, 791857067171441226), (4159, 4159, 784016898189545769), (4160, 4160, 776254354643114622), (4161, 4161, 768568667963479824), (4162, 4162, 760959077191564182), (4163, 4163, 753424828902538794), (4164, 4164, 745965177131226529), (4165, 4165, 738579383298244088), (4166, 4166, 731266716136875335), (4167, 4167, 724026451620668648), (4168, 4168, 716857872891751137), (4169, 4169, 709760270189852611), (4170, 4170, 702732940782032288), (4171, 4171, 695775188893101275), (4172, 4172, 688886325636733936), (4173, 4173, 682065668947261323), (4174, 4174, 675312543512139923), (4175, 4175, 668626280705089033), (4176, 4176, 662006218519890132), (4177, 4177, 655451701504841715), (4178, 4178, 648962080697863084), (4179, 4179, 642536713562240677), (4180, 4180, 636174963923010571), (4181, 4181, 629876201903970863), (4182, 4182, 623639803865317686), (4183, 4183, 617465152341898699), (4184, 4184, 611351635982077920), (4185, 4185, 605298649487205861), (4186, 4186, 599305593551688971), (4187, 4187, 593371874803652447), (4188, 4188, 587496905746190542), (4189, 4189, 581680104699198556), (4190, 4190, 575920895741780748), (4191, 4191, 570218708655228464), (4192, 4192, 564572978866562836), (4193, 4193, 558983147392636471), (4194, 4194, 553448660784788585), (4195, 4195, 547968971074048104), (4196, 4196, 542543535716879311), (4197, 4197, 537171817541464664), (4198, 4198, 531853284694519470), (4199, 4199, 526587410588633138), (4200, 4200, 521373673850131820), (4201, 4201, 516211558267457247), (4202, 4202, 511100552740056681), (4203, 4203, 506040151227778892), (4204, 4204, 501029852700771180), (4205, 4205, 496069161089872455), (4206, 4206, 491157585237497481), (4207, 4207, 486294638849007407), (4208, 4208, 481479840444561789), (4209, 4209, 476712713311447316), (4210, 4210, 471992785456878530), (4211, 4211, 467319589561265872), (4212, 4212, 462692662931946407), (4213, 4213, 458111547457372681), (4214, 4214, 453575789561755129), (4215, 4215, 449084940160153593), (4216, 4216, 444638554614013459), (4217, 4217, 440236192687142038), (4218, 4218, 435877418502120830), (4219, 4219, 431561800497149337), (4220, 4220, 427288911383316175), (4221, 4221, 423058328102293243), (4222, 4222, 418869631784448755), (4223, 4223, 414722407707375005), (4224, 4224, 410616245254826738), (4225, 4225, 406550737876066077), (4226, 4226, 402525483045609977), (4227, 4227, 398540082223376215), (4228, 4228, 394594140815223975), (4229, 4229, 390687268133885124), (4230, 4230, 386819077360282301), (4231, 4231, 382989185505230001), (4232, 4232, 379197213371514852), (4233, 4233, 375442785516351339), (4234, 4234, 371725530214209247), (4235, 4235, 368045079420009155), (4236, 4236, 364401068732682332), (4237, 4237, 360793137359091418), (4238, 4238, 357220928078308334), (4239, 4239, 353684087206245876), (4240, 4240, 350182264560639481), (4241, 4241, 346715113426375723), (4242, 4242, 343282290521164083), (4243, 4243, 339883455961548597), (4244, 4244, 336518273229256036), (4245, 4245, 333186409137877264), (4246, 4246, 329887533799878479), (4247, 4247, 326621320593939088), (4248, 4248, 323387446132612958), (4249, 4249, 320185590230309860), (4250, 4250, 317015435871593921), (4251, 4251, 313876669179795961), (4252, 4252, 310768979385936595), (4253, 4253, 307692058797957025), (4254, 4254, 304645602770254480), (4255, 4255, 301629309673519287), (4256, 4256, 298642880864870581), (4257, 4257, 295686020658287704), (4258, 4258, 292758436295334361), (4259, 4259, 289859837916172634), (4260, 4260, 286989938530863994), (4261, 4261, 284148453990954450), (4262, 4262, 281335102961341040), (4263, 4263, 278549606892416871), (4264, 4264, 275791689992491951), (4265, 4265, 273061079200487081), (4266, 4266, 270357504158898100), (4267, 4267, 267680697187027821), (4268, 4268, 265030393254482991), (4269, 4269, 262406329954933655), (4270, 4270, 259808247480132332), (4271, 4271, 257235888594190427), (4272, 4272, 254688998608109334), (4273, 4273, 252167325354563697), (4274, 4274, 249670619162934354), (4275, 4275, 247198632834588469), (4276, 4276, 244751121618404425), (4277, 4277, 242327843186539034), (4278, 4278, 239928557610434687), (4279, 4279, 237553027337064047), (4280, 4280, 235201017165409947), (4281, 4281, 232872294223178166), (4282, 4282, 230566627943740758), (4283, 4283, 228283790043307681), (4284, 4284, 226023554498324437), (4285, 4285, 223785697523093502), (4286, 4286, 221569997547617329), (4287, 4287, 219376235195660722), (4288, 4288, 217204193263030417), (4289, 4289, 215053656696069720), (4290, 4290, 212924412570366060), (4291, 4291, 210816250069669366), (4292, 4292, 208728960465019174), (4293, 4293, 206662337094078390), (4294, 4294, 204616175340671674), (4295, 4295, 202590272614526409), (4296, 4296, 200584428331214267), (4297, 4297, 198598443892291353), (4298, 4298, 196632122665635003), (4299, 4299, 194685269965975251), (4300, 4300, 192757693035619060), (4301, 4301, 190849201025365406), (4302, 4302, 188959604975609313), (4303, 4303, 187088717797632983), (4304, 4304, 185236354255082162), (4305, 4305, 183402330945625903), (4306, 4306, 181586466282797923), (4307, 4307, 179788580478017746), (4308, 4308, 178008495522789847), (4309, 4309, 176246035171079057), (4310, 4310, 174501024921860452), (4311, 4311, 172773292001842032), (4312, 4312, 171062665348358448), (4313, 4313, 169368975592434106), (4314, 4314, 167692055042013967), (4315, 4315, 166031737665360363), (4316, 4316, 164387859074614221), (4317, 4317, 162760256509519031), (4318, 4318, 161148768821305971), (4319, 4319, 159553236456738585), (4320, 4320, 157973501442315431), (4321, 4321, 156409407368629139), (4322, 4322, 154860799374880336), (4323, 4323, 153327524133544887), (4324, 4324, 151809429835192958), (4325, 4325, 150306366173458374), (4326, 4326, 148818184330156806), (4327, 4327, 147344736960551293), (4328, 4328, 145885878178763656), (4329, 4329, 144441463543330353), (4330, 4330, 143011350042901339), (4331, 4331, 141595396082080534), (4332, 4332, 140193461467406469), (4333, 4333, 138805407393471752), (4334, 4334, 137431096429179952), (4335, 4335, 136070392504138567), (4336, 7209, 134723160895186700)]

def glob0 : ℕ := 18446744073709551616

def runs1 : List (ℕ × ℕ × ℕ) := [(0, 3000, 2131436228385367), (3001, 3001, 2152750590669221), (3002, 3002, 2174278096575913), (3003, 3003, 2196020877541672), (3004, 3004, 2217981086317089), (3005, 3005, 2240160897180260), (3006, 3006, 2262562506152063), (3007, 3007, 2285188131213583), (3008, 3008, 2308040012525719), (3009, 3009, 2331120412650976), (3010, 3010, 2354431616777486), (3011, 3011, 2377975932945261), (3012, 3012, 2401755692274713), (3013, 3013, 2425773249197461), (3014, 3014, 2450030981689435), (3015, 3015, 2474531291506330), (3016, 3016, 2499276604421393), (3017, 3017, 2524269370465607), (3018, 3018, 2549512064170263), (3019, 3019, 2575007184811965), (3020, 3020, 2600757256660085), (3021, 3021, 2626764829226686), (3022, 3022, 2653032477518953), (3023, 3023, 2679562802294142), (3024, 3024, 2706358430317084), (3025, 3025, 2733422014620255), (3026, 3026, 2760756234766457), (3027, 3027, 2788363797114122), (3028, 3028, 2816247435085263), (3029, 3029, 2844409909436115), (3030, 3030, 2872854008530477), (3031, 3031, 2901582548615781), (3032, 3032, 2930598374101939), (3033, 3033, 2959904357842959), (3034, 3034, 2989503401421388), (3035, 3035, 3019398435435602), (3036, 3036, 3049592419789958), (3037, 3037, 3080088343987858), (3038, 3038, 3110889227427736), (3039, 3039, 3141998119702014), (3040, 3040, 3173418100899034), (3041, 3041, 3205152281908024), (3042, 3042, 3237203804727104), (3043, 3043, 3269575842774375), (3044, 3044, 3302271601202119), (3045, 3045, 3335294317214140), (3046, 3046, 3368647260386282), (3047, 3047, 3402333732990144), (3048, 3048, 3436357070320046), (3049, 3049, 3470720641023246), (3050, 3050, 3505427847433479), (3051, 3051, 3540482125907814), (3052, 3052, 3575886947166892), (3053, 3053, 3611645816638561), (3054, 3054, 3647762274804946), (3055, 3055, 3684239897552996), (3056, 3056, 3721082296528526), (3057, 3057, 3758293119493811), (3058, 3058, 3795876050688749), (3059, 3059, 3833834811195636), (3060, 3060, 3872173159307593), (3061, 3061, 3910894890900669), (3062, 3062, 3950003839809675), (3063, 3063, 3989503878207772), (3064, 3064, 4029398916989850), (3065, 3065, 4069692906159748), (3066, 3066, 4110389835221346), (3067, 3067, 4151493733573559), (3068, 3068, 4193008670909295), (3069, 3069, 4234938757618388), (3070, 3070, 4277288145194572), (3071, 3071, 4320061026646517), (3072, 3072, 4363261636912983), (3073, 3073, 4406894253282112), (3074, 3074, 4450963195814934), (3075, 3075, 4495472827773083), (3076, 3076, 4540427556050814), (3077, 3077, 4585831831611322), (3078, 3078, 4631690149927435), (3079, 3079, 4678007051426709), (3080, 3080, 4724787121940977), (3081, 3081, 4772034993160386), (3082, 3082, 4819755343091990), (3083, 3083, 4867952896522910), (3084, 3084, 4916632425488139), (3085, 3085, 4965798749743021), (3086, 3086, 5015456737240451), (3087, 3087, 5065611304612855), (3088, 3088, 5116267417658984), (3089, 3089, 5167430091835574), (3090, 3090, 5219104392753929), (3091, 3091, 5271295436681469), (3092, 3092, 5324008391048283), (3093, 3093, 5377248474958766), (3094, 3094, 5431020959708354), (3095, 3095, 5485331169305437), (3096, 3096, 5540184480998492), (3097, 3097, 5595586325808477), (3098, 3098, 5651542189066561), (3099, 3099, 5708057610957227), (3100, 3100, 5765138187066799), (3101, 3101, 5822789568937467), (3102, 3102, 5881017464626842), (3103, 3103, 5939827639273110), (3104, 3104, 5999225915665841), (3105, 3105, 6059218174822500), (3106, 3106, 6119810356570725), (3107, 3107, 6181008460136432), (3108, 3108, 6242818544737796), (3109, 3109, 6305246730185174), (3110, 3110, 6368299197487026), (3111, 3111, 6431982189461896), (3112, 3112, 6496302011356515), (3113, 3113, 6561265031470080), (3114, 3114, 6626877681784781), (3115, 3115, 6693146458602629), (3116, 3116, 6760077923188655), (3117, 3117, 6827678702420542), (3118, 3118, 6895955489444747), (3119, 3119, 6964915044339195), (3120, 3120, 7034564194782587), (3121, 3121, 7104909836730413), (3122, 3122, 7175958935097717), (3123, 3123, 7247718524448694), (3124, 3124, 7320195709693181), (3125, 3125, 7393397666790113), (3126, 3126, 7467331643458014), (3127, 3127, 7542004959892594), (3128, 3128, 7617425009491520), (3129, 3129, 7693599259586435), (3130, 3130, 7770535252182299), (3131, 3131, 7848240604704122), (3132, 3132, 7926723010751163), (3133, 3133, 8005990240858675), (3134, 3134, 8086050143267262), (3135, 3135, 8166910644699934), (3136, 3136, 8248579751146934), (3137, 3137, 8331065548658403), (3138, 3138, 8414376204144987), (3139, 3139, 8498519966186437), (3140, 3140, 8583505165848301), (3141, 3141, 8669340217506784), (3142, 3142, 8756033619681852), (3143, 3143, 8843593955878671), (3144, 3144, 8932029895437457), (3145, 3145, 9021350194391832), (3146, 3146, 9111563696335750), (3147, 3147, 9202679333299108), (3148, 3148, 9294706126632099), (3149, 3149, 9387653187898420), (3150, 3150, 9481529719777404), (3151, 3151, 9576345016975178), (3152, 3152, 9672108467144930), (3153, 3153, 9768829551816379), (3154, 3154, 9866517847334543), (3155, 3155, 9965183025807888), (3156, 3156, 10064834856065967), (3157, 3157, 10165483204626627), (3158, 3158, 10267138036672893), (3159, 3159, 10369809417039622), (3160, 3160, 10473507511210018), (3161, 3161, 10578242586322119), (3162, 3162, 10684025012185340), (3163, 3163, 10790865262307193), (3164, 3164, 10898773914930265), (3165, 3165, 11007761654079568), (3166, 3166, 11117839270620363), (3167, 3167, 11229017663326567), (3168, 3168, 11341307839959833), (3169, 3169, 11454720918359431), (3170, 3170, 11569268127543025), (3171, 3171, 11684960808818456), (3172, 3172, 11801810416906640), (3173, 3173, 11919828521075706), (3174, 3174, 12039026806286464), (3175, 3175, 12159417074349328), (3176, 3176, 12281011245092821), (3177, 3177, 12403821357543750), (3178, 3178, 12527859571119187), (3179, 3179, 12653138166830379), (3180, 3180, 12779669548498683), (3181, 3181, 12907466243983670), (3182, 3182, 13036540906423506), (3183, 3183, 13166906315487741), (3184, 3184, 13298575378642619), (3185, 3185, 13431561132429045), (3186, 3186, 13565876743753335), (3187, 3187, 13701535511190869), (3188, 3188, 13838550866302777), (3189, 3189, 13976936374965805), (3190, 3190, 14116705738715463), (3191, 3191, 14257872796102618), (3192, 3192, 14400451524063644), (3193, 3193, 14544456039304280), (3194, 3194, 14689900599697323), (3195, 3195, 14836799605694297), (3196, 3196, 14985167601751239), (3197, 3197, 15135019277768752), (3198, 3198, 15286369470546439), (3199, 3199, 15439233165251904), (3200, 3200, 15593625496904423), (3201, 3201, 15749561751873467), (3202, 3202, 15907057369392202), (3203, 3203, 16066127943086124), (3204, 3204, 16226789222516985), (3205, 3205, 16389057114742155), (3206, 3206, 16552947685889576), (3207, 3207, 16718477162748472), (3208, 3208, 16885661934375957), (3209, 3209, 17054518553719716), (3210, 3210, 17225063739256914), (3211, 3211, 17397314376649483), (3212, 3212, 17571287520415977), (3213, 3213, 17747000395620137), (3214, 3214, 17924470399576339), (3215, 3215, 18103715103572102), (3216, 3216, 18284752254607823), (3217, 3217, 18467599777153901), (3218, 3218, 18652275774925440), (3219, 3219, 18838798532674695), (3220, 3220, 19027186518001442), (3221, 3221, 19217458383181456), (3222, 3222, 19409632967013271), (3223, 3223, 19603729296683403), (3224, 3224, 19799766589650237), (3225, 3225, 19997764255546740), (3226, 3226, 20197741898102207), (3227, 3227, 20399719317083229), (3228, 3228, 20603716510254061), (3229, 3229, 20809753675356602), (3230, 3230, 21017851212110168), (3231, 3231, 21228029724231270), (3232, 3232, 21440310021473582), (3233, 3233, 21654713121688318), (3234, 3234, 21871260252905201), (3235, 3235, 22089972855434253), (3236, 3236, 22310872583988596), (3237, 3237, 22533981309828482), (3238, 3238, 22759321122926767), (3239, 3239, 22986914334156034), (3240, 3240, 23216783477497595), (3241, 3241, 23448951312272571), (3242, 3242, 23683440825395296), (3243, 3243, 23920275233649249), (3244, 3244, 24159477985985742), (3245, 3245, 24401072765845599), (3246, 3246, 24645083493504055), (3247, 3247, 24891534328439096), (3248, 3248, 25140449671723487), (3249, 3249, 25391854168440722), (3250, 3250, 25645772710125129), (3251, 3251, 25902230437226380), (3252, 3252, 26161252741598644), (3253, 3253, 26422865269014630), (3254, 3254, 26687093921704777), (3255, 3255, 26953964860921824), (3256, 3256, 27223504509531043), (3257, 3257, 27495739554626353), (3258, 3258, 27770696950172616), (3259, 3259, 28048403919674343), (3260, 3260, 28328887958871086), (3261, 3261, 28612176838459797), (3262, 3262, 28898298606844395), (3263, 3263, 29187281592912839), (3264, 3264, 29479154408841967), (3265, 3265, 29773945952930387), (3266, 3266, 30071685412459691), (3267, 3267, 30372402266584288), (3268, 3268, 30676126289250130), (3269, 3269, 30982887552142632), (3270, 3270, 31292716427664058), (3271, 3271, 31605643591940699), (3272, 3272, 31921700027860106), (3273, 3273, 32240917028138707), (3274, 3274, 32563326198420094), (3275, 3275, 32888959460404295), (3276, 3276, 33217849055008338), (3277, 3277, 33550027545558421), (3278, 3278, 33885527821014005), (3279, 3279, 34224383099224145), (3280, 3280, 34566626930216387), (3281, 3281, 34912293199518551), (3282, 3282, 35261416131513736), (3283, 3283, 35614030292828873), (3284, 3284, 35970170595757162), (3285, 3285, 36329872301714734), (3286, 3286, 36693171024731881), (3287, 3287, 37060102734979200), (3288, 3288, 37430703762328992), (3289, 3289, 37805010799952282), (3290, 3290, 38183060907951805), (3291, 3291, 38564891517031323), (3292, 3292, 38950540432201636), (3293, 3293, 39340045836523652), (3294, 3294, 39733446294888889), (3295, 3295, 40130780757837778), (3296, 3296, 40532088565416155), (3297, 3297, 40937409451070317), (3298, 3298, 41346783545581020), (3299, 3299, 41760251381036830), (3300, 3300, 42177853894847199), (3301, 3301, 42599632433795671), (3302, 3302, 43025628758133627), (3303, 3303, 43455885045714964), (3304, 3304, 43890443896172113), (3305, 3305, 44329348335133834), (3306, 3306, 44772641818485173), (3307, 3307, 45220368236670024), (3308, 3308, 45672571919036725), (3309, 3309, 46129297638227092), (3310, 3310, 46590590614609363), (3311, 3311, 47056496520755456), (3312, 3312, 47527061485963011), (3313, 3313, 48002332100822641), (3314, 3314, 48482355421830868), (3315, 3315, 48967178976049176), (3316, 3316, 49456850765809668), (3317, 3317, 49951419273467765), (3318, 3318, 50450933466202442), (3319, 3319, 50955442800864467), (3320, 3320, 51464997228873111), (3321, 3321, 51979647201161842), (3322, 3322, 52499443673173461), (3323, 3323, 53024438109905195), (3324, 3324, 53554682491004247), (3325, 3325, 54090229315914290), (3326, 3326, 54631131609073433), (3327, 3327, 55177442925164167), (3328, 3328, 55729217354415809), (3329, 3329, 56286509527959967), (3330, 3330, 56849374623239567), (3331, 3331, 57417868369471962), (3332, 3332, 57992047053166682), (3333, 3333, 58571967523698349), (3334, 3334, 59157687198935332), (3335, 3335, 59749264070924685), (3336, 3336, 60346756711633932), (3337, 3337, 60950224278750272), (3338, 3338, 61559726521537774), (3339, 3339, 62175323786753152), (3340, 3340, 62797077024620684), (3341, 3341, 63425047794866890), (3342, 3342, 64059298272815559), (3343, 3343, 64699891255543715), (3344, 3344, 65346890168099152), (3345, 3345, 66000359069780143), (3346, 3346, 66660362660477945), (3347, 3347, 67326966287082724), (3348, 3348, 68000235949953552), (3349, 3349, 68680238309453087), (3350, 3350, 69367040692547618), (3351, 3351, 70060711099473094), (3352, 3352, 70761318210467825), (3353, 3353, 71468931392572503), (3354, 3354, 72183620706498228), (3355, 3355, 72905456913563211), (3356, 3356, 73634511482698843), (3357, 3357, 74370856597525831), (3358, 3358, 75114565163501089), (3359, 3359, 75865710815136100), (3360, 3360, 76624367923287461), (3361, 3361, 77390611602520336), (3362, 3362, 78164517718545539), (3363, 3363, 78946162895730995), (3364, 3364, 79735624524688305), (3365, 3365, 80532980769935188), (3366, 3366, 81338310577634540), (3367, 3367, 82151693683410885), (3368, 3368, 82973210620244994), (3369, 3369, 83802942726447444), (3370, 3370, 84640972153711918), (3371, 3371, 85487381875249037), (3372, 3372, 86342255694001528), (3373, 3373, 87205678250941543), (3374, 3374, 88077735033450958), (3375, 3375, 88958512383785468), (3376, 3376, 89848097507623323), (3377, 3377, 90746578482699556), (3378, 3378, 91654044267526551), (3379, 3379, 92570584710201817), (3380, 3380, 93496290557303835), (3381, 3381, 94431253462876873), (3382, 3382, 95375565997505642), (3383, 3383, 96329321657480699), (3384, 3384, 97292614874055506), (3385, 3385, 98265541022796061), (3386, 3386, 99248196433024021), (3387, 3387, 100240678397354261), (3388, 3388, 101243085181327804), (3389, 3389, 102255516033141082), (3390, 3390, 103278071193472493), (3391, 3391, 104310851905407218), (3392, 3392, 105353960424461290), (3393, 3393, 106407500028705903), (3394, 3394, 107471575028992962), (3395, 3395, 108546290779282892), (3396, 3396, 109631753687075720), (3397, 3397, 110728071223946478), (3398, 3398, 111835351936185942), (3399, 3399, 112953705455547802), (3400, 3400, 114083242510103280), (3401, 3401, 115224074935204313), (3402, 3402, 116376315684556356), (3403, 3403, 117540078841401919), (3404, 3404, 118715479629815939), (3405, 3405, 119902634426114098), (3406, 3406, 121101660770375239), (3407, 3407, 122312677378078991), (3408, 3408, 123535804151859781), (3409, 3409, 124771162193378379), (3410, 3410, 126018873815312163), (3411, 3411, 127279062553465284), (3412, 3412, 128551853178999937), (3413, 3413, 129837371710789937), (3414, 3414, 131135745427897836), (3415, 3415, 132447102882176814), (3416, 3416, 133771573910998582), (3417, 3417, 135109289650108568), (3418, 3418, 136460382546609654), (3419, 3419, 137824986372075750), (3420, 3420, 139203236235796508), (3421, 3421, 140595268598154473), (3422, 3422, 142001221284136018), (3423, 3423, 143421233496977378), (3424, 3424, 144855445831947152), (3425, 3425, 146304000290266623), (3426, 3426, 147767040293169289), (3427, 3427, 149244710696100982), (3428, 3428, 150737157803061992), (3429, 3429, 152244529381092612), (3430, 3430, 153766974674903538), (3431, 3431, 155304644421652574), (3432, 3432, 156857690865869099), (3433, 3433, 158426267774527790), (3434, 3434, 160010530452273068), (3435, 3435, 161610635756795799), (3436, 3436, 163226742114363757), (3437, 3437, 164859009535507394), (3438, 3438, 166507599630862468), (3439, 3439, 168172675627171093), (3440, 3440, 169854402383442804), (3441, 3441, 171552946407277232), (3442, 3442, 173268475871350004), (3443, 3443, 175001160630063504), (3444, 3444, 176751172236364139), (3445, 3445, 178518683958727781), (3446, 3446, 180303870798315059), (3447, 3447, 182106909506298209), (3448, 3448, 183927978601361191), (3449, 3449, 185767258387374803), (3450, 3450, 187624930971248551), (3451, 3451, 189501180280961037), (3452, 3452, 191396192083770647), (3453, 3453, 193310154004608354), (3454, 3454, 195243255544654437), (3455, 3455, 197195688100100981), (3456, 3456, 199167644981101991), (3457, 3457, 201159321430913011), (3458, 3458, 203170914645222141), (3459, 3459, 205202623791674363), (3460, 3460, 207254650029591106), (3461, 3461, 209327196529887017), (3462, 3462, 211420468495185887), (3463, 3463, 213534673180137746), (3464, 3464, 215670019911939124), (3465, 3465, 217826720111058515), (3466, 3466, 220004987312169100), (3467, 3467, 222205037185290791), (3468, 3468, 224427087557143699), (3469, 3469, 226671358432715136), (3470, 3470, 228938072017042287), (3471, 3471, 231227452737212710), (3472, 3472, 233539727264584837), (3473, 3473, 235875124537230686), (3474, 3474, 238233875782602993), (3475, 3475, 240616214540429023), (3476, 3476, 243022376685833313), (3477, 3477, 245452600452691646), (3478, 3478, 247907126457218562), (3479, 3479, 250386197721790748), (3480, 3480, 252890059699008655), (3481, 3481, 255418960295998742), (3482, 3482, 257973149898958729), (3483, 3483, 260552881397948317), (3484, 3484, 263158410211927800), (3485, 3485, 265789994314047078), (3486, 3486, 268447894257187549), (3487, 3487, 271132373199759424), (3488, 3488, 273843696931757018), (3489, 3489, 276582133901074589), (3490, 3490, 279347955240085334), (3491, 3491, 282141434792486188), (3492, 3492, 284962849140411050), (3493, 3493, 287812477631815160), (3494, 3494, 290690602408133312), (3495, 3495, 293597508432214645), (3496, 3496, 296533483516536791), (3497, 3497, 299498818351702159), (3498, 3498, 302493806535219181), (3499, 3499, 305518744600571373), (3500, 3500, 308573932046577086), (3501, 3501, 311659671367042857), (3502, 3502, 314776268080713286), (3503, 3503, 317924030761520419), (3504, 3504, 321103271069135623), (3505, 3505, 324314303779826979), (3506, 3506, 327557446817625249), (3507, 3507, 330833021285801501), (3508, 3508, 334141351498659516), (3509, 3509, 337482765013646111), (3510, 3510, 340857592663782572), (3511, 3511, 344266168590420398), (3512, 3512, 347708830276324602), (3513, 3513, 351185918579087848), (3514, 3514, 354697777764878727), (3515, 3515, 358244755542527514), (3516, 3516, 361827203097952789), (3517, 3517, 365445475128932317), (3518, 3518, 369099929880221640), (3519, 3519, 372790929179023857), (3520, 3520, 376518838470814095), (3521, 3521, 380284026855522236), (3522, 3522, 384086867124077458), (3523, 3523, 387927735795318233), (3524, 3524, 391807013153271415), (3525, 3525, 395725083284804129), (3526, 3526, 399682334117652171), (3527, 3527, 403679157458828692), (3528, 3528, 407715949033416979), (3529, 3529, 411793108523751149), (3530, 3530, 415911039608988661), (3531, 3531, 420070150005078547), (3532, 3532, 424270851505129333), (3533, 3533, 428513560020180626), (3534, 3534, 432798695620382432), (3535, 3535, 437126682576586257), (3536, 3536, 441497949402352119), (3537, 3537, 445912928896375640), (3538, 3538, 450372058185339397), (3539, 3539, 454875778767192791), (3540, 3540, 459424536554864719), (3541, 3541, 464018781920413366), (3542, 3542, 468658969739617499), (3543, 3543, 473345559437013674), (3544, 3544, 478079015031383811), (3545, 3545, 482859805181697649), (3546, 3546, 487688403233514626), (3547, 3547, 492565287265849772), (3548, 3548, 497490940138508270), (3549, 3549, 502465849539893352), (3550, 3550, 507490508035292286), (3551, 3551, 512565413115645209), (3552, 3552, 517691067246801661), (3553, 3553, 522867977919269677), (3554, 3554, 528096657698462374), (3555, 3555, 533377624275446998), (3556, 3556, 538711400518201468), (3557, 3557, 544098514523383483), (3558, 3558, 549539499668617317), (3559, 3559, 555034894665303491), (3560, 3560, 560585243611956526), (3561, 3561, 566191096048076091), (3562, 3562, 571853007008556852), (3563, 3563, 577571537078642420), (3564, 3564, 583347252449428844), (3565, 3565, 589180724973923133), (3566, 3566, 595072532223662364), (3567, 3567, 601023257545898988), (3568, 3568, 607033490121357978), (3569, 3569, 613103825022571557), (3570, 3570, 619234863272797273), (3571, 3571, 625427211905525246), (3572, 3572, 631681484024580498), (3573, 3573, 637998298864826303), (3574, 3574, 644378281853474566), (3575, 3575, 650822064672009312), (3576, 3576, 657330285318729405), (3577, 3577, 663903588171916699), (3578, 3578, 670542624053635866), (3579, 3579, 677248050294172225), (3580, 3580, 684020530797113947), (3581, 3581, 690860736105085086), (3582, 3582, 697769343466135937), (3583, 3583, 704747036900797297), (3584, 3584, 711794507269805270), (3585, 3585, 718912452342503322), (3586, 3586, 726101576865928355), (3587, 3587, 733362592634587639), (3588, 3588, 740696218560933515), (3589, 3589, 748103180746542851), (3590, 3590, 755584212554008279), (3591, 3591, 763140054679548362), (3592, 3592, 770771455226343845), (3593, 3593, 778479169778607284), (3594, 3594, 786263961476393357), (3595, 3595, 794126601091157290), (3596, 3596, 802067867102068863), (3597, 3597, 810088545773089552), (3598, 3598, 818189431230820447), (3599, 3599, 826371325543128652), (3600, 3600, 834635038798559938), (3601, 3601, 842981389186545538), (3602, 3602, 851411203078410993), (3603, 3603, 859925315109195103), (3604, 3604, 868524568260287054), (3605, 3605, 877209813942889925), (3606, 3606, 885981912082318824), (3607, 3607, 894841731203142012), (3608, 3608, 903790148515173432), (3609, 3609, 912828050000325166), (3610, 3610, 921956330500328418), (3611, 3611, 931175893805331702), (3612, 3612, 940487652743385019), (3613, 3613, 949892529270818869), (3614, 3614, 959391454563527058), (3615, 3615, 968985369109162329), (3616, 3616, 978675222800253952), (3617, 3617, 988461975028256492), (3618, 3618, 998346594778539056), (3619, 3619, 1008330060726324447), (3620, 3620, 1018413361333587691), (3621, 3621, 1028597494946923568), (3622, 3622, 1038883469896392804), (3623, 3623, 1049272304595356732), (3624, 3624, 1059765027641310299), (3625, 3625, 1070362677917723402), (3626, 3626, 1081066304696900636), (3627, 3627, 1091876967743869643), (3628, 3628, 1102795737421308339), (3629, 3629, 1113823694795521423), (3630, 3630, 1124961931743476637), (3631, 3631, 1136211551060911403), (3632, 3632, 1147573666571520517), (3633, 3633, 1159049403237235722), (3634, 3634, 1170639897269608080), (3635, 3635, 1182346296242304160), (3636, 3636, 1194169759204727202), (3637, 3637, 1206111456796774474), (3638, 3638, 1218172571364742219), (3639, 3639, 1230354297078389641), (3640, 3640, 1242657840049173537), (3641, 3641, 1255084418449665273), (3642, 3642, 1267635262634161925), (3643, 3643, 1280311615260503545), (3644, 3644, 1293114731413108580), (3645, 3645, 1306045878727239666), (3646, 3646, 1319106337514512063), (3647, 3647, 1332297400889657183), (3648, 3648, 1345620374898553755), (3649, 3649, 1359076578647539293), (3650, 3650, 1372667344434014685), (3651, 3651, 1386394017878354832), (3652, 3652, 1400257958057138381), (3653, 3653, 1414260537637709764), (3654, 3654, 1428403143014086862), (3655, 3655, 1442687174444227731), (3656, 3656, 1457114046188670008), (3657, 3657, 1471685186650556708), (3658, 3658, 1486402038517062275), (3659, 3659, 1501266058902232898), (3660, 3660, 1516278719491255227), (3661, 3661, 1531441506686167779), (3662, 3662, 1546755921753029457), (3663, 3663, 1562223480970559751), (3664, 3664, 1577845715780265349), (3665, 3665, 1593624172938068002), (3666, 3666, 1609560414667448682), (3667, 3667, 1625656018814123169), (3668, 3668, 1641912579002264401), (3669, 3669, 1658331704792287045), (3670, 3670, 1674915021840209915), (3671, 3671, 1691664172058612015), (3672, 3672, 1708580813779198135), (3673, 3673, 1725666621916990116), (3674, 3674, 1742923288136160017), (3675, 3675, 1760352521017521617), (3676, 3676, 1777956046227696834), (3677, 3677, 1795735606689973802), (3678, 3678, 1813692962756873540), (3679, 3679, 1831829892384442275), (3680, 3680, 1850148191308286698), (3681, 3681, 1868649673221369565), (3682, 3682, 1887336169953583261), (3683, 3683, 1906209531653119093), (3684, 3684, 1925271626969650284), (3685, 3685, 1944524343239346787), (3686, 3686, 1963969586671740255), (3687, 3687, 1983609282538457657), (3688, 3688, 2003445375363842234), (3689, 3689, 2023479829117480656), (3690, 3690, 2043714627408655463), (3691, 3691, 2064151773682742018), (3692, 3692, 2084793291419569438), (3693, 3693, 2105641224333765132), (3694, 3694, 2126697636577102783), (3695, 3695, 2147964612942873811), (3696, 3696, 2169444259072302549), (3697, 3697, 2191138701663025575), (3698, 3698, 2213050088679655831), (3699, 3699, 2235180589566452389), (3700, 3700, 2257532395462116913), (3701, 3701, 2280107719416738082), (3702, 3702, 2302908796610905463), (3703, 3703, 2325937884577014517), (3704, 3704, 2349197263422784662), (3705, 3705, 2372689236057012509), (3706, 3706, 2396416128417582634), (3707, 3707, 2420380289701758460), (3708, 3708, 2444584092598776045), (3709, 3709, 2469029933524763806), (3710, 3710, 2493720232860011444), (3711, 3711, 2518657435188611558), (3712, 3712, 2543844009540497674), (3713, 3713, 2569282449635902650), (3714, 3714, 2594975274132261677), (3715, 3715, 2620925026873584294), (3716, 3716, 2647134277142320136), (3717, 3717, 2673605619913743338), (3718, 3718, 2700341676112880771), (3719, 3719, 2727345092874009579), (3720, 3720, 2754618543802749675), (3721, 3721, 2782164729240777171), (3722, 3722, 2809986376533184943), (3723, 3723, 2838086240298516793), (3724, 3724, 2866467102701501961), (3725, 3725, 2895131773728516980), (3726, 3726, 2924083091465802150), (3727, 3727, 2953323922380460171), (3728, 3728, 2982857161604264773), (3729, 3729, 3012685733220307421), (3730, 3730, 3042812590552510495), (3731, 3731, 3073240716458035600), (3732, 3732, 3103973123622615956), (3733, 3733, 3135012854858842116), (3734, 3734, 3166362983407430537), (3735, 3735, 3198026613241504842), (3736, 3736, 3230006879373919890), (3737, 3737, 3262306948167659089), (3738, 3738, 3294930017649335680), (3739, 3739, 3327879317825829037), (3740, 3740, 3361158111004087327), (3741, 3741, 3394769692114128201), (3742, 3742, 3428717389035269483), (3743, 3743, 3463004562925622178), (3744, 3744, 3497634608554878399), (3745, 3745, 3532610954640427183), (3746, 3746, 3567937064186831455), (3747, 3747, 3603616434828699770), (3748, 3748, 3639652599176986767), (3749, 3749, 3676049125168756635), (3750, 3750, 3712809616420444201), (3751, 3751, 3749937712584648643), (3752, 3752, 3787437089710495130), (3753, 3753, 3825311460607600081), (3754, 3754, 3863564575213676082), (3755, 3755, 3902200220965812843), (3756, 3756, 3941222223175470971), (3757, 3757, 3980634445407225681), (3758, 3758, 4020440789861297938), (3759, 3759, 4060645197759910917), (3760, 3760, 4101251649737510026), (3761, 3761, 4142264166234885126), (3762, 3762, 4183686807897233978), (3763, 3763, 4225523675976206317), (3764, 3764, 4267778912735968381), (3765, 3765, 4310456701863328064), (3766, 3766, 4353561268881961345), (3767, 3767, 4397096881570780959), (3768, 3768, 4441067850386488768), (3769, 3769, 4485478528890353656), (3770, 3770, 4530333314179257192), (3771, 3771, 4575636647321049764), (3772, 3772, 4621393013794260262), (3773, 3773, 4667606943932202865), (3774, 3774, 4714283013371524893), (3775, 3775, 4761425843505240142), (3776, 3776, 4809040101940292543), (3777, 3777, 4857130502959695469), (3778, 3778, 4905701807989292424), (3779, 3779, 4954758826069185348), (3780, 3780, 5004306414329877201), (3781, 3781, 5054349478473175973), (3782, 3782, 5104892973257907733), (3783, 3783, 5155941902990486810), (3784, 3784, 5207501322020391678), (3785, 3785, 5259576335240595595), (3786, 3786, 5312172098593001551), (3787, 3787, 5365293819578931567), (3788, 3788, 5418946757774720882), (3789, 3789, 5473136225352468091), (3790, 3790, 5527867587605992772), (3791, 3791, 5583146263482052700), (3792, 3792, 5638977726116873227), (3793, 3793, 5695367503378041959), (3794, 3794, 5752321178411822379), (3795, 3795, 5809844390195940602), (3796, 3796, 5867942834097900008), (3797, 3797, 5926622262438879009), (3798, 3798, 5985888485063267799), (3799, 3799, 6045747369913900477), (3800, 3800, 6106204843613039481), (3801, 3801, 6167266892049169876), (3802, 3802, 6228939560969661575), (3803, 3803, 6291228956579358191), (3804, 3804, 6354141246145151773), (3805, 3805, 6417682658606603290), (3806, 3806, 6481859485192669323), (3807, 3807, 6546678080044596016), (3808, 3808, 6612144860845041977), (3809, 3809, 6678266309453492396), (3810, 3810, 6745048972548027320), (3811, 3811, 6812499462273507593), (3812, 3812, 6880624456896242669), (3813, 3813, 6949430701465205096), (3814, 3814, 7018925008479857147), (3815, 3815, 7089114258564655719), (3816, 3816, 7160005401150302276), (3817, 3817, 7231605455161805298), (3818, 3818, 7303921509713423351), (3819, 3819, 7376960724810557585), (3820, 3820, 7450730332058663161), (3821, 3821, 7525237635379249792), (3822, 3822, 7600490011733042290), (3823, 3823, 7676494911850372713), (3824, 3824, 7753259860968876440), (3825, 3825, 7830792459578565205), (3826, 3826, 7909100384174350857), (3827, 3827, 7988191388016094365), (3828, 3828, 8068073301896255309), (3829, 3841, 8116567392432202712), (3842, 3842, 8084507883490081119), (3843, 3843, 8004463250980278335), (3844, 3844, 7925211139584433995), (3845, 3845, 7846743702558845540), (3846, 3846, 7769053170850342119), (3847, 3847, 7692131852327071405), (3848, 3848, 7615972131016902381), (3849, 3849, 7540566466353368694), (3850, 3850, 7465907392429077915), (3851, 3851, 7391987517256512787), (3852, 3852, 7318799522036151274), (3853, 3853, 7246336160431832945), (3854, 3854, 7174590257853299945), (3855, 3855, 7103554710745841530), (3856, 3856, 7033222485886971812), (3857, 3857, 6963586619690071101), (3858, 3858, 6894640217514921882), (3859, 3859, 6826376452985071170), (3860, 3860, 6758788567311951654), (3861, 3861, 6691869868625694707), (3862, 3862, 6625613731312569017), (3863, 3863, 6560013595358979224), (3864, 3864, 6495062965701959628), (3865, 3865, 6430755411586098642), (3866, 3866, 6367084565926830338), (3867, 3867, 6304044124680030038), (3868, 3868, 6241627846217851523), (3869, 3869, 6179829550710744082), (3870, 3870, 6118643119515588200), (3871, 3871, 6058062494569889307), (3872, 3872, 5998081677791969611), (3873, 3873, 5938694730487098624), (3874, 3874, 5879895772759503589), (3875, 3875, 5821678982930201573), (3876, 3876, 5764038596960595617), (3877, 3877, 5706968907881777838), (3878, 3878, 5650464265229483008), (3879, 3879, 5594519074484636642), (3880, 3880, 5539127796519442220), (3881, 3881, 5484284947048952693), (3882, 3882, 5429985096088071973), (3883, 3883, 5376222867413932647), (3884, 3884, 5322992938033596680), (3885, 3885, 5270290037657026416), (3886, 3886, 5218108948175273679), (3887, 3887, 5166444503143835326), (3888, 3888, 5115291587271124085), (3889, 3889, 5064645135912004044), (3890, 3890, 5014500134566340638), (3891, 3891, 4964851618382515483), (3892, 3892, 4915694671665856914), (3893, 3893, 4867024427391937539), (3894, 3894, 4818836066724690632), (3895, 3895, 4771124818539297656), (3896, 3896, 4723885958949799659), (3897, 3897, 4677114810841385801), (3898, 3898, 4630806743407312674), (3899, 3899, 4584957171690408588), (3900, 3900, 4539561556129117414), (3901, 3901, 4494615402108037044), (3902, 3902, 4450114259512907964), (3903, 3903, 4406053722290007885), (3904, 3904, 4362429428009908797), (3905, 3905, 4319237057435553265), (3906, 3906, 4276472334094607193), (3907, 3907, 4234131023856046726), (3908, 3908, 4192208934510937352), (3909, 3909, 4150701915357363715), (3910, 3910, 4109605856789469025), (3911, 3911, 4068916689890563391), (3912, 3912, 4028630386030260783), (3913, 3913, 3988742956465604736), (3914, 3914, 3949250451946143303), (3915, 3915, 3910148962322914161), (3916, 3916, 3871434616161301150), (3917, 3917, 3833103580357723910), (3918, 3918, 3795152059760122684), (3919, 3919, 3757576296792200677), (3920, 3920, 3720372571081386809), (3921, 3921, 3683537199090481989), (3922, 3922, 3647066533752952464), (3923, 3923, 3610956964111834123), (3924, 3924, 3575204914962212003), (3925, 3925, 3539806846497239607), (3926, 3926, 3504759253957662977), (3927, 3927, 3470058667284814829), (3928, 3928, 3435701650777044385), (3929, 3929, 3401684802749548896), (3930, 3930, 3368004755197573164), (3931, 3931, 3334658173462943727), (3932, 3932, 3301641755903904680), (3933, 3933, 3268952233568222456), (3934, 3934, 3236586369869527184), (3935, 3935, 3204540960266858598), (3936, 3936, 3172812831947384751), (3937, 3937, 3141398843512262129), (3938, 3938, 3110295884665606069), (3939, 3939, 3079500875906540662), (3940, 3940, 3049010768224297685), (3941, 3941, 3018822542796334342), (3942, 3942, 2988933210689439942), (3943, 3943, 2959339812563801923), (3944, 3944, 2930039418380001904), (3945, 3945, 2901029127108912776), (3946, 3946, 2872306066444468095), (3947, 3947, 2843867392519275342), (3948, 3948, 2815710289623044893), (3949, 3949, 2787831969923806825), (3950, 3950, 2760229673191887945), (3951, 3951, 2732900666526621728), (3952, 3952, 2705842244085764087), (3953, 3953, 2679051726817588205), (3954, 3954, 2652526462195631886), (3955, 3955, 2626263823956071174), (3956, 3956, 2600261211837694232), (3957, 3957, 2574516051324449735), (3958, 3958, 2549025793390544292), (3959, 3959, 2523787914248063655), (3960, 3960, 2498799915097092728), (3961, 3961, 2474059321878309632), (3962, 3962, 2449563685028029338), (3963, 3963, 2425310579235672612), (3964, 3964, 2401297603203636250), (3965, 3965, 2377522379409540841), (3966, 3966, 2353982553870832516), (3967, 3967, 2330675795911715363), (3968, 3968, 2307599797932391448), (3969, 3969, 2284752275180585592), (3970, 3970, 2262130965525332270), (3971, 3971, 2239733629233002247), (3972, 3972, 2217558048745546779), (3973, 3973, 2195602028460937405), (3974, 3974, 2173863394515779609), (3975, 3975, 2152339994570078821), (3976, 3976, 2131029697594137446), (3977, 3977, 2109930393657561828), (3978, 3978, 2089039993720358246), (3979, 3979, 2068356429426097273), (3980, 3980, 2047877652897126013), (3981, 3981, 2027601636531807934), (3982, 3982, 2007526372803770231), (3983, 3983, 1987649874063138843), (3984, 3984, 1967970172339741429), (3985, 3985, 1948485319148258840), (3986, 3986, 1929193385295305782), (3987, 3987, 1910092460688421567), (3988, 3988, 1891180654146952046), (3989, 3989, 1872456093214804006), (3990, 3990, 1853916923975053471), (3991, 3991, 1835561310866389576), (3992, 3992, 1817387436501375818), (3993, 3993, 1799393501486510710), (3994, 3994, 1781577724244070010), (3995, 3995, 1763938340835712882), (3996, 3996, 1746473604787834536), (3997, 3997, 1729181786918648056), (3998, 3998, 1712061175166978273), (3999, 3999, 1695110074422750765), (4000, 4000, 1678326806359159173), (4001, 4001, 1661709709266494231), (4002, 4002, 1645257137887618051), (4003, 4003, 1628967463255067377), (4004, 4004, 1612839072529769680), (4005, 4005, 1596870368841356119), (4006, 4006, 1581059771130055563), (4007, 4007, 1565405713990154023), (4008, 4008, 1549906647515003983), (4009, 4009, 1534561037143568300), (4010, 4010, 1519367363508483466), (4011, 4011, 1504324122285627194), (4012, 4012, 1489429824045175439), (4013, 4013, 1474682994104134098), (4014, 4014, 1460082172380330790), (4015, 4015, 1445625913247852268), (4016, 4016, 1431312785393913136), (4017, 4017, 1417141371677141719), (4018, 4018, 1403110268987269029), (4019, 4019, 1389218088106206959), (4020, 4020, 1375463453570501940), (4021, 4021, 1361845003535150436), (4022, 4022, 1348361389638762808), (4023, 4023, 1335011276870062186), (4024, 4024, 1321793343435705134), (4025, 4025, 1308706280629411024), (4026, 4026, 1295748792702387153), (4027, 4027, 1282919596735036785), (4028, 4028, 1270217422509937411), (4029, 4029, 1257641012386076644), (4030, 4030, 1245189121174333311), (4031, 4031, 1232860516014191397), (4032, 4032, 1220653976251674651), (4033, 4033, 1208568293318489753), (4034, 4034, 1196602270612366092), (4035, 4035, 1184754723378580289), (4036, 4036, 1173024478592653752), (4037, 4037, 1161410374844211635), (4038, 4038, 1149911262221991718), (4039, 4039, 1138526002199991800), (4040, 4040, 1127253467524744357), (4041, 4041, 1116092542103707284), (4042, 4042, 1105042120894759687), (4043, 4043, 1094101109796791769), (4044, 4044, 1083268425541377989), (4045, 4045, 1072542995585522762), (4046, 4046, 1061923758005468081), (4047, 4047, 1051409661391552555), (4048, 4048, 1040999664744111441), (4049, 4049, 1030692737370407367), (4050, 4050, 1020487858782581552), (4051, 4051, 1010384018596615398), (4052, 4052, 1000380216432292473), (4053, 4053, 990475461814150964), (4054, 4054, 980668774073416796), (4055, 4055, 970959182250907718), (4056, 4056, 961345725000898731), (4057, 4057, 951827450495939338), (4058, 4058, 942403416332613206), (4059, 4059, 933072689438230897), (4060, 4060, 923834345978446432), (4061, 4061, 914687471265788547), (4062, 4062, 905631159669097571), (4063, 4063, 896664514523858981), (4064, 4064, 887786648043424734), (4065, 4065, 878996681231113598), (4066, 4066, 870293743793181780), (4067, 4067, 861676974052655228), (4068, 4068, 853145518864015077), (4069, 4069, 844698533528727799), (4070, 4070, 836335181711611682), (4071, 4071, 828054635358031369), (4072, 4072, 819856074611912246), (4073, 4073, 811738687734566581), (4074, 4074, 803701671024323347), (4075, 4075, 795744228736953809), (4076, 4076, 787865573006884959), (4077, 4077, 780064923769193029), (4078, 4078, 772341508682369336), (4079, 4079, 764694563051850827), (4080, 4080, 757123329754307750), (4081, 4081, 749627059162680941), (4082, 4082, 742205009071961327), (4083, 4083, 734856444625704284), (4084, 4084, 727580638243271569), (4085, 4085, 720376869547793632), (4086, 4086, 713244425294845181), (4087, 4087, 706182599301826912), (4088, 4088, 699190692378046447), (4089, 4089, 692268012255491532), (4090, 4090, 685413873520288645), (4091, 4091, 678627597544840243), (4092, 4092, 671908512420633904), (4093, 4093, 665255952891716736), (4094, 4094, 658669260288828452), (4095, 4095, 652147782464186586), (4096, 4096, 645690873726917412), (4097, 4097, 639297894779126151), (4098, 4098, 632968212652600149), (4099, 4099, 626701200646138761), (4100, 4100, 620496238263503724), (4101, 4101, 614352711151983885), (4102, 4102, 608270011041568203), (4103, 4103, 602247535684720993), (4104, 4104, 596284688796753459), (4105, 4105, 590380879996785603), (4106, 4106, 584535524749292676), (4107, 4107, 578748044306230372), (4108, 4108, 573017865649733042), (4109, 4109, 567344421435379249), (4110, 4110, 561727149936019059), (4111, 4111, 556165494986157484), (4112, 4112, 550658905926888598), (4113, 4113, 545206837551374850), (4114, 4114, 539808750050866188), (4115, 4115, 534464108961253651), (4116, 4116, 529172385110152130), (4117, 4117, 523933054564507059), (4118, 4118, 518745598578719861), (4119, 4119, 513609503543286991), (4120, 4120, 508524260933947516), (4121, 4121, 503489367261334174), (4122, 4122, 498504324021122944), (4123, 4123, 493568637644676183), (4124, 4124, 488681819450174438), (4125, 4125, 483843385594232117), (4126, 4126, 479052857023992195), (4127, 4127, 474309759429695243), (4128, 4128, 469613623197718062), (4129, 4129, 464963983364077289), (4130, 4130, 460360379568393356), (4131, 4131, 455802356008310253), (4132, 4132, 451289461394366587), (4133, 4133, 446821248905313453), (4134, 4134, 442397276143874706), (4135, 4135, 438017105092945253), (4136, 4136, 433680302072223023), (4137, 4137, 429386437695270320), (4138, 4138, 425135086827000317), (4139, 4139, 420925828541584472), (4140, 4140, 416758246080776705), (4141, 4141, 412631926812650203), (4142, 4142, 408546462190742775), (4143, 4143, 404501447713606708), (4144, 4144, 400496482884759117), (4145, 4145, 396531171173028829), (4146, 4146, 392605119973295870), (4147, 4147, 388717940567619673), (4148, 4148, 384869248086752152), (4149, 4149, 381058661472031833), (4150, 4150, 377285803437655280), (4151, 4151, 373550300433322060), (4152, 4152, 369851782607249564), (4153, 4153, 366189883769554024), (4154, 4154, 362564241355994083), (4155, 4155, 358974496392073350), (4156, 4156, 355420293457498366), (4157, 4157, 351901280650988481), (4158, 4158, 348417109555434140), (4159, 4159, 344967435203400138), (4160, 4160, 341551916042970434), (4161, 4161, 338170213903931123), (4162, 4162, 334821993964288240), (4163, 4163, 331506924717117070), (4164, 4164, 328224677937739673), (4165, 4165, 324974928651227399), (4166, 4166, 321757355100225148), (4167, 4167, 318571638713094206), (4168, 4168, 315417464072370501), (4169, 4169, 312294518883535149), (4170, 4170, 309202493944094207), (4171, 4171, 306141083112964561), (4172, 4172, 303109983280162932), (4173, 4173, 300108894336794982), (4174, 4174, 297137519145341567), (4175, 4175, 294195563510239175), (4176, 4176, 291282736148751658), (4177, 4177, 288398748662130355), (4178, 4178, 285543315507059757), (4179, 4179, 282716153967385898), (4180, 4180, 279916984126124652), (4181, 4181, 277145528837747180), (4182, 4182, 274401513700739782), (4183, 4183, 271684667030435428), (4184, 4184, 268994719832114285), (4185, 4185, 266331405774370579), (4186, 4186, 263694461162743148), (4187, 4187, 261083624913607077), (4188, 4188, 258498638528323839), (4189, 4189, 255939246067647365), (4190, 4190, 253405194126383530), (4191, 4191, 250896231808300524), (4192, 4192, 248412110701287648), (4193, 4193, 245952584852760047), (4194, 4194, 243517410745306978), (4195, 4195, 241106347272581166), (4196, 4196, 238719155715426897), (4197, 4197, 236355599718244453), (4198, 4198, 234015445265588567), (4199, 4199, 231698460658998581), (4200, 4200, 229404416494058001), (4201, 4201, 227133085637681189), (4202, 4202, 224884243205624940), (4203, 4203, 222657666540222713), (4204, 4204, 220453135188339319), (4205, 4205, 218270430879543881), (4206, 4206, 216109337504498892), (4207, 4207, 213969641093563259), (4208, 4208, 211851129795607187), (4209, 4209, 209753593857036819), (4210, 4210, 207676825601026554), (4211, 4211, 205620619406956984), (4212, 4212, 203584771690056420), (4213, 4213, 201569080881243980), (4214, 4214, 199573347407172257), (4215, 4215, 197597373670467581), (4216, 4216, 195640964030165922), (4217, 4217, 193703924782342497), (4218, 4218, 191786064140933166), (4219, 4219, 189887192218745708), (4220, 4220, 188007121008659117), (4221, 4221, 186145664365009027), (4222, 4222, 184302637985157453), (4223, 4223, 182477859391245002), (4224, 4224, 180671147912123765), (4225, 4225, 178882324665469074), (4226, 4226, 177111212540068390), (4227, 4227, 175357636178285535), (4228, 4228, 173621421958698549), (4229, 4229, 171902397978909455), (4230, 4230, 170200394038524213), (4231, 4231, 168515241622301201), (4232, 4232, 166846773883466535), (4233, 4233, 165194825627194589), (4234, 4234, 163559233294252069), (4235, 4235, 161939834944804029), (4236, 4236, 160336470242380226), (4237, 4237, 158748980438000224), (4238, 4238, 157177208354455667), (4239, 4239, 155620998370748186), (4240, 4240, 154080196406681372), (4241, 4241, 152554649907605319), (4242, 4242, 151044207829312197), (4243, 4243, 149548720623081383), (4244, 4244, 148068040220872656), (4245, 4245, 146602020020665996), (4246, 4246, 145150514871946531), (4247, 4247, 143713381061333199), (4248, 4248, 142290476298349702), (4249, 4249, 140881659701336339), (4250, 4250, 139486791783501325), (4251, 4251, 138105734439110223), (4252, 4252, 136738350929812102), (4253, 4253, 135384505871101091), (4254, 4254, 134044065218911972), (4255, 4255, 132716896256348487), (4256, 4256, 131402867580543056), (4257, 4257, 130101849089646590), (4258, 4258, 128813711969947119), (4259, 4259, 127538328683115959), (4260, 4260, 126275572953580158), (4261, 4261, 125025319756019958), (4262, 4262, 123787445302990058), (4263, 4263, 122561827032663423), (4264, 4264, 121348343596696459), (4265, 4265, 120146874848214316), (4266, 4266, 118957301829915164), (4267, 4267, 117779506762292242), (4268, 4268, 116613373031972517), (4269, 4269, 115458785180170808), (4270, 4270, 114315628891258226), (4271, 4271, 113183790981443788), (4272, 4272, 112063159387568107), (4273, 4273, 110953623156008027), (4274, 4274, 109855072431691116), (4275, 4275, 108767398447218927), (4276, 4276, 107690493512097947), (4277, 4277, 106624251002077175), (4278, 4278, 105568565348591263), (4279, 4279, 104523332028308181), (4280, 4280, 103488447552780377), (4281, 4281, 102463809458198393), (4282, 4282, 101449316295245934), (4283, 4283, 100444867619055380), (4284, 4284, 99450363979262753), (4285, 4285, 98465706910161141), (4286, 4286, 97490798920951625), (4287, 4287, 96525543486090718), (4288, 4288, 95569845035733384), (4289, 4289, 94623608946270677), (4290, 4290, 93686741530961066), (4291, 4291, 92759150030654521), (4292, 4292, 91840742604608437), (4293, 4293, 90931428321394492), (4294, 4294, 90031117149895537), (4295, 4295, 89139719950391620), (4296, 4296, 88257148465734278), (4297, 4297, 87383315312608196), (4298, 4298, 86518133972879402), (4299, 4299, 85661518785029111), (4300, 4300, 84813384935672387), (4301, 4301, 83973648451160779), (4302, 4302, 83142226189268098), (4303, 4303, 82319035830958513), (4304, 4304, 81503995872236151), (4305, 4305, 80697025616075397), (4306, 4306, 79898045164431087), (4307, 4307, 79106975410327808), (4308, 4308, 78323738030027533), (4309, 4309, 77548255475274785), (4310, 4310, 76780450965618599), (4311, 4311, 76020248480810494), (4312, 4312, 75267572753277717), (4313, 4313, 74522349260671007), (4314, 4314, 73784504218486146), (4315, 4315, 73053964572758560), (4316, 4316, 72330657992830257), (4317, 4317, 71614512864188374), (4318, 4318, 70905458281374627), (4319, 4319, 70203424040964978), (4320, 4320, 69508340634618790), (4321, 4321, 68820139242196822), (4322, 4322, 68138751724947348), (4323, 4323, 67464110618759751), (4324, 4324, 66796149127484902), (4325, 4325, 66134801116321685), (4326, 4326, 65480001105268995), (4327, 4327, 64831684262642569), (4328, 4328, 64189786398656009), (4329, 4329, 63554243959065356), (4330, 4330, 62924994018876590), (4331, 4331, 62301974276115435), (4332, 4332, 61685123045658847), (4333, 4333, 61074379253127571), (4334, 4334, 60469682428839179), (4335, 4335, 59870972701820970), (4336, 7209, 59278190793882148)]

def glob1 : ℕ := 8116567392432202712

def runs2 : List (ℕ × ℕ × ℕ) := [(0, 3828, 0), (3829, 3841, 41924418349339890037), (3842, 3842, 41758821712242154536), (3843, 3843, 41345368031922925283), (3844, 3844, 40936007952398935924), (3845, 3845, 40530700942969243489), (3846, 3846, 40129406874226973751), (3847, 3847, 39732086014086112625), (3848, 3848, 39338699023847636263), (3849, 3849, 38949206954304590359), (3850, 3850, 38563571241885733029), (3851, 3851, 38181753704837359434), (3852, 3852, 37803716539442930133), (3853, 3853, 37429422316280128845), (3854, 3854, 37058833976514979054), (3855, 3855, 36691914828232652529), (3856, 3856, 36328628542804606464), (3857, 3857, 35968939151291689568), (3858, 3858, 35612811040882860959), (3859, 3859, 35260208951369169266), (3860, 3860, 34911097971652642838), (3861, 3861, 34565443536289745384), (3862, 3862, 34223211422069054836), (3863, 3863, 33884367744622826570), (3864, 3864, 33548878955072105515), (3865, 3865, 33216711836705054965), (3866, 3866, 32887833501688173233), (3867, 3867, 32562211387810072508), (3868, 3868, 32239813255257497532), (3869, 3869, 31920607183423264884), (3870, 3870, 31604561567745806815), (3871, 3871, 31291645116580006748), (3872, 3872, 30981826848099016582), (3873, 3873, 30675076087226749091), (3874, 3874, 30371362462600741674), (3875, 3875, 30070655903565090767), (3876, 3876, 29772926637193159175), (3877, 3877, 29478145185339761559), (3878, 3878, 29186282361722536198), (3879, 3879, 28897309269032214057), (3880, 3880, 28611197296071499066), (3881, 3881, 28327918114922276303), (3882, 3882, 28047443678140867627), (3883, 3883, 27769746215981057056), (3884, 3884, 27494798233644610947), (3885, 3885, 27222572508559020740), (3886, 3886, 26953042087682198752), (3887, 3887, 26686180284833860151), (3888, 3888, 26421960678053326882), (3889, 3889, 26160357106983491962), (3890, 3890, 25901343670280685111), (3891, 3891, 25644894723050183278), (3892, 3892, 25390984874307112157), (3893, 3893, 25139588984462487284), (3894, 3894, 24890682162834145826), (3895, 3895, 24644239765182322600), (3896, 3896, 24400237391269626336), (3897, 3897, 24158650882445174590), (3898, 3898, 23919456319252648109), (3899, 3899, 23682630019062027831), (3900, 3900, 23448148533724780031), (3901, 3901, 23215988647252257456), (3902, 3902, 22986127373517086590), (3903, 3903, 22758541953977313456), (3904, 3904, 22533209855423082629), (3905, 3905, 22310108767745626366), (3906, 3906, 22089216601728342936), (3907, 3907, 21870511486859745482), (3908, 3908, 21653971769168064833), (3909, 3909, 21439576009077291914), (3910, 3910, 21227302979284447440), (3911, 3911, 21017131662657868752), (3912, 3912, 20809041250156305695), (3913, 3913, 20603011138768619500), (3914, 3914, 20399020929473880693), (3915, 3915, 20197050425221664053), (3916, 3916, 19997079628932340646), (3917, 3917, 19799088741517168957), (3918, 3918, 19603058159917989066), (3919, 3919, 19408968475166325808), (3920, 3920, 19216800470461708721), (3921, 3921, 19026535119269018535), (3922, 3922, 18838153583434671817), (3923, 3923, 18651637211321457245), (3924, 3924, 18466967535961838856), (3925, 3925, 18284126273229543422), (3926, 3926, 18103095320029250913), (3927, 3927, 17923856752504208825), (3928, 3928, 17746392824261592896), (3929, 3929, 17570685964615438511), (3930, 3930, 17396718776846968822), (3931, 3931, 17224474036482147349), (3932, 3932, 17053934689586284504), (3933, 3933, 16885083851075529212), (3934, 3934, 16717904803045078428), (3935, 3935, 16552380993113939037), (3936, 3936, 16388496032786078255), (3937, 3937, 16226233695827800252), (3938, 3938, 16065577916661188368), (3939, 3939, 15906512788773453830), (3940, 3940, 15749022563142033495), (3941, 3941, 15593091646675280688), (3942, 3942, 15438704600668594741), (3943, 3943, 15285846139275836377), (3944, 3944, 15134501127995877601), (3945, 3945, 14984654582174136239), (3946, 3946, 14836291665518946771), (3947, 3947, 14689397688632620565), (3948, 3948, 14543958107557050065), (3949, 3949, 14399958522333712935), (3950, 3950, 14257384675577933599), (3951, 3951, 14116222451067260990), (3952, 3952, 13976457872343822762), (3953, 3953, 13838077101330517586), (3954, 3954, 13701066436960908501), (3955, 3955, 13565412313822681684), (3956, 3956, 13431101300814536321), (3957, 3957, 13298120099816372595), (3958, 3958, 13166455544372646134), (3959, 3959, 13036094598388758548), (3960, 3960, 12907024354840354998), (3961, 3961, 12779232034495400988), (3962, 3962, 12652704984648911870), (3963, 3963, 12527430677870209772), (3964, 3964, 12403396710762583933), (3965, 3965, 12280590802735231617), (3966, 3966, 12159000794787358036), (3967, 3967, 12038614648304314887), (3968, 3968, 11919420443865658304), (3969, 3969, 11801406380065008222), (3970, 3970, 11684560772341592299), (3971, 3971, 11568872051823358712), (3972, 3972, 11454328764181543279), (3973, 3973, 11340919568496577504), (3974, 3974, 11228633236135225252), (3975, 3975, 11117458649638836883), (3976, 3976, 11007384801622610775), (3977, 3977, 10898400793685753243), (3978, 3978, 10790495835332428953), (3979, 3979, 10683659242903395003), (3980, 3980, 10577880438518212874), (3981, 3981, 10473148949027933539), (3982, 3982, 10369454404978152019), (3983, 3983, 10266786539582328731), (3984, 3984, 10165135187705275972), (3985, 3985, 10064490284856708883), (3986, 3986, 9964841866194761270), (3987, 3987, 9866180065539367594), (3988, 3988, 9768495114395413460), (3989, 3989, 9671777340985557881), (3990, 3990, 9576017169292631565), (3991, 3991, 9481205118111516401), (3992, 3992, 9387331800110412278), (3993, 3993, 9294387920901398296), (3994, 3994, 9202364278120196332), (3995, 3995, 9111251760515045873), (3996, 3996, 9021041347044599875), (3997, 3997, 8931724105984752351), (3998, 3998, 8843291194044309259), (3999, 3999, 8755733855489415108), (4000, 4000, 8669043421276648621), (4001, 4001, 8583211308194701605), (4002, 4002, 8498229018014556045), (4003, 4003, 8414088136648075292), (4004, 4004, 8330780333314926032), (4005, 4005, 8248297359717748546), (4006, 4006, 8166631049225493610), (4007, 4007, 8085773316064845158), (4008, 4008, 8005716154519648672), (4009, 4009, 7926451638138266012), (4010, 4010, 7847971918948778229), (4011, 4011, 7770269226681958643), (4012, 4012, 7693335868001939250), (4013, 4013, 7617164225744494307), (4014, 4014, 7541746758162865651), (4015, 4015, 7467075998181055100), (4016, 4016, 7393144552654510000), (4017, 4017, 7319945101638128713), (4018, 4018, 7247470397661513577), (4019, 4019, 7175713265011399581), (4020, 4020, 7104666599021187704), (4021, 4021, 7034323365367512578), (4022, 4022, 6964676599373774830), (4023, 4023, 6895719405320569139), (4024, 4024, 6827444955762939741), (4025, 4025, 6759846490854395783), (4026, 4026, 6692917317677619588), (4027, 4027, 6626650809581801572), (4028, 4028, 6561040405526536210), (4029, 4029, 6496079609432214069), (4030, 4030, 6431761989536845613), (4031, 4031, 6368081177759253082), (4032, 4032, 6305030869068567408), (4033, 4033, 6242604820859967731), (4034, 4034, 6180796852336601714), (4035, 4035, 6119600843897625459), (4036, 4036, 6059010736532302435), (4037, 4037, 5999020531220101421), (4038, 4038, 5939624288336734080), (4039, 4039, 5880816127066073346), (4040, 4040, 5822590224817894402), (4041, 4041, 5764940816651380596), (4042, 4042, 5707862194704337224), (4043, 4043, 5651348707628056657), (4044, 4044, 5595394760027778869), (4045, 4045, 5539994811908691949), (4046, 4046, 5485143378127417772), (4047, 4047, 5430835027848928487), (4048, 4048, 5377064384008840086), (4049, 4049, 5323826122781029788), (4050, 4050, 5271114973050524543), (4051, 4051, 5218925715891608458), (4052, 4052, 5167253184051097483), (4053, 4053, 5116092261436730181), (4054, 4054, 5065437882610623942), (4055, 4055, 5015285032287746477), (4056, 4056, 4965628744839352948), (4057, 4057, 4916464103801339552), (4058, 4058, 4867786241387464903), (4059, 4059, 4819590338007390993), (4060, 4060, 4771871621789496033), (4061, 4061, 4724625368108411914), (4062, 4062, 4677846899117239519), (4063, 4063, 4631531583284395563), (4064, 4064, 4585674834935045112), (4065, 4065, 4540272113797074368), (4066, 4066, 4495318924551558780), (4067, 4067, 4450810816387681961), (4068, 4068, 4406743382562061347), (4069, 4069, 4363112259962436978), (4070, 4070, 4319913128675680176), (4071, 4071, 4277141711560079382), (4072, 4072, 4234793773821860774), (4073, 4073, 4192865122595901757), (4074, 4074, 4151351606530595799), (4075, 4075, 4110249115376827523), (4076, 4076, 4069553579581017350), (4077, 4077, 4029260969882195396), (4078, 4078, 3989367296913064749), (4079, 4079, 3949868610805014603), (4080, 4080, 3910761000797044161), (4081, 4081, 3872040594848558575), (4082, 4082, 3833703559255998589), (4083, 4083, 3795746098273265930), (4084, 4084, 3758164453735906861), (4085, 4085, 3720954904689016694), (4086, 4086, 3684113767018828410), (4087, 4087, 3647637393087948921), (4088, 4088, 3611522171374206853), (4089, 4089, 3575764526113076092), (4090, 4090, 3540360916943639695), (4091, 4091, 3505307838558059104), (4092, 4092, 3470601820354513964), (4093, 4093, 3436239426093578182), (4094, 4094, 3402217253557998200), (4095, 4095, 3368531934215839802), (4096, 4096, 3335180132886970101), (4097, 4097, 3302158547412841684), (4098, 4098, 3269463908329546222), (4099, 4099, 3237092978544105171), (4100, 4100, 3205042553013965515), (4101, 4101, 3173309458429668827), (4102, 4102, 3141890552900662205), (4103, 4103, 3110782725644220005), (4104, 4104, 3079982896677445550), (4105, 4105, 3049488016512322326), (4106, 4106, 3019295065853784481), (4107, 4107, 2989401055300776714), (4108, 4108, 2959803025050273975), (4109, 4109, 2930498044604231658), (4110, 4110, 2901483212479437285), (4111, 4111, 2872755655920234936), (4112, 4112, 2844312530614093996), (4113, 4113, 2816151020409994055), (4114, 4114, 2788268337039598075), (4115, 4115, 2760661719841186212), (4116, 4116, 2733328435486322983), (4117, 4117, 2706265777709230676), (4118, 4118, 2679471067038842253), (4119, 4119, 2652941650533507182), (4120, 4120, 2626674901518323942), (4121, 4121, 2600668219325073210), (4122, 4122, 2574919029034725951), (4123, 4123, 2549424781222500941), (4124, 4124, 2524182951705446476), (4125, 4125, 2499191041292521264), (4126, 4126, 2474446575537149766), (4127, 4127, 2449947104492227491), (4128, 4128, 2425690202467551971), (4129, 4129, 2401673467789655417), (4130, 4130, 2377894522564015265), (4131, 4131, 2354351012439619074), (4132, 4132, 2331040606375860469), (4133, 4133, 2307960996411743039), (4134, 4134, 2285109897437369345), (4135, 4135, 2262485046967692421), (4136, 4136, 2240084204918507348), (4137, 4137, 2217905153384660740), (4138, 4138, 2195945696420456179), (4139, 4139, 2174203659822233840), (4140, 4140, 2152676890913102812), (4141, 4141, 2131363258329804764), (4142, 4142, 2110260651811687886), (4143, 4143, 2089366981991770184), (4144, 4144, 2068680180189871469), (4145, 4145, 2048198198207793534), (4146, 4146, 2027919008126528251), (4147, 4147, 2007840602105473516), (4148, 4148, 1987960992183637145), (4149, 4149, 1968278210082809054), (4150, 4150, 1948790307012682232), (4151, 4151, 1929495353477903200), (4152, 4152, 1910391439087032871), (4153, 4153, 1891476672363398882), (4154, 4154, 1872749180557820675), (4155, 4155, 1854207109463188788), (4156, 4156, 1835848623230879988), (4157, 4157, 1817671904188990087), (4158, 4158, 1799675152662366423), (4159, 4159, 1781856586794422201), (4160, 4160, 1764214442370715050), (4161, 4161, 1746746972644272327), (4162, 4162, 1729452448162645868), (4163, 4163, 1712329156596679077), (4164, 4164, 1695375402570969384), (4165, 4165, 1678589507496009291), (4166, 4166, 1661969809401989397), (4167, 4167, 1645514662774246927), (4168, 4168, 1629222438390343493), (4169, 4169, 1613091523158755933), (4170, 4170, 1597120319959164290), (4171, 4171, 1581307247484321080), (4172, 4172, 1565650740083486217), (4173, 4173, 1550149247607412096), (4174, 4174, 1534801235254863462), (4175, 4175, 1519605183420656893), (4176, 4176, 1504559587545204844), (4177, 4177, 1489662957965549351), (4178, 4178, 1474913819767870644), (4179, 4179, 1460310712641456084), (4180, 4180, 1445852190734114934), (4181, 4181, 1431536822509024687), (4182, 4182, 1417363190602994740), (4183, 4183, 1403329891686133406), (4184, 4184, 1389435536322904362), (4185, 4185, 1375678748834558775), (4186, 4186, 1362058167162929480), (4187, 4187, 1348572442735573742), (4188, 4188, 1335220240332251230), (4189, 4189, 1322000237952723990), (4190, 4190, 1308911126685865337), (4191, 4191, 1295951610580064690), (4192, 4192, 1283120406514915535), (4193, 4193, 1270416244074173797), (4194, 4194, 1257837865419974056), (4195, 4195, 1245384025168291145), (4196, 4196, 1233053490265634797), (4197, 4197, 1220845039866965145), (4198, 4198, 1208757465214816976), (4199, 4199, 1196789569519620768), (4200, 4200, 1184940167841208681), (4201, 4201, 1173208086971493744), (4202, 4202, 1161592165318310637), (4203, 4203, 1150091252790406572), (4204, 4204, 1138704210683570863), (4205, 4205, 1127429911567891943), (4206, 4206, 1116267239176130637), (4207, 4207, 1105215088293198651), (4208, 4208, 1094272364646731337), (4209, 4209, 1083437984798743898), (4210, 4210, 1072710876038360295), (4211, 4211, 1062089976275604253), (4212, 4212, 1051574233936241834), (4213, 4213, 1041162607857665183), (4214, 4214, 1030854067185807112), (4215, 4215, 1020647591273076348), (4216, 4216, 1010542169577303315), (4217, 4217, 1000536801561686450), (4218, 4218, 990630496595729159), (4219, 4219, 980822273857157583), (4220, 4220, 971111162234809488), (4221, 4221, 961496200232484642), (4222, 4222, 951976435873747170), (4223, 4223, 942550926607670465), (4224, 4224, 933218739215515312), (4225, 4225, 923978949718331992), (4226, 4226, 914830643285477220), (4227, 4227, 905772914144036852), (4228, 4228, 896804865489145398), (4229, 4229, 887925609395193463), (4230, 4230, 879134266727914320), (4231, 4231, 870429967057340911), (4232, 4232, 861811848571624664), (4233, 4233, 853279057991707588), (4234, 4234, 844830750486839196), (4235, 4235, 836466089590929897), (4236, 4236, 828184247119732572), (4237, 4237, 819984403088844130), (4238, 4238, 811865745632518941), (4239, 4239, 803827470923286080), (4240, 4240, 795868783092362456), (4241, 4241, 787988894150853916), (4242, 4242, 780187023911736551), (4243, 4243, 772462399912610446), (4244, 4244, 764814257339218264), (4245, 4245, 757241838949721053), (4246, 4246, 749744394999723815), (4247, 4247, 742321183168043381), (4248, 4248, 734971468483211269), (4249, 4249, 727694523250704226), (4250, 4250, 720489626980895274), (4251, 4251, 713356066317718093), (4252, 4252, 706293134968037716), (4253, 4253, 699300133631720510), (4254, 4254, 692376369932396545), (4255, 4255, 685521158348907470), (4256, 4256, 678733820147433139), (4257, 4257, 672013683314290237), (4258, 4258, 665360082489396274), (4259, 4259, 658772358900392350), (4260, 4260, 652249860297418169), (4261, 4261, 645791940888532840), (4262, 4262, 639397961275775089), (4263, 4263, 633067288391856524), (4264, 4264, 626799295437481707), (4265, 4265, 620593361819288819), (4266, 4266, 614448873088404771), (4267, 4267, 608365220879608684), (4268, 4268, 602341802851097707), (4269, 4269, 596378022624849215), (4270, 4270, 590473289727573480), (4271, 4271, 584627019532250971), (4272, 4272, 578838633200248486), (4273, 4273, 573107557624008402), (4274, 4274, 567433225370305348), (4275, 4275, 561815074624064701), (4276, 4276, 556252549132737328), (4277, 4277, 550745098151225077), (4278, 4278, 545292176387351562), (4279, 4279, 539893243947872833), (4280, 4280, 534547766285022607), (4281, 4281, 529255214143586740), (4282, 4282, 524015063508501723), (4283, 4283, 518826795552972003), (4284, 4284, 513689896587100993), (4285, 4285, 508603858007030686), (4286, 4286, 503568176244584837), (4287, 4287, 498582352717410730), (4288, 4288, 493645893779614584), (4289, 4289, 488758310672885727), (4290, 4290, 483919119478104680), (4291, 4291, 479127841067430376), (4292, 4292, 474384001056861759), (4293, 4293, 469687129759269068), (4294, 4294, 465036762137890167), (4295, 4295, 460432437760287294), (4296, 4296, 455873700752759697), (4297, 4297, 451360099755207620), (4298, 4298, 446891187876443189), (4299, 4299, 442466522649943751), (4300, 4300, 438085665990043318), (4301, 4301, 433748184148557741), (4302, 4302, 429453647671839347), (4303, 4303, 425201631358256779), (4304, 4304, 420991714216095821), (4305, 4305, 416823479421877051), (4306, 4306, 412696514279086189), (4307, 4307, 408610410177313058), (4308, 4308, 404564762551795107), (4309, 4309, 400559170843361492), (4310, 4310, 396593238458773755), (4311, 4311, 392666572731459163), (4312, 4312, 388778784882632835), (4313, 4313, 384929489982804787), (4314, 4314, 381118306913668106), (4315, 4315, 377344858330364461), (4316, 4316, 373608770624123229), (4317, 4317, 369909673885270524), (4318, 4318, 366247201866604479), (4319, 4319, 362620991947133147), (4320, 4320, 359030685096171433), (4321, 4321, 355475925837793498), (4322, 4322, 351956362215637127), (4323, 4323, 348471645758056561), (4324, 4324, 345021431443620358), (4325, 4325, 341605377666950849), (4326, 4326, 338223146204901831), (4327, 4327, 334874402183071120), (4328, 4328, 331558814042644673), (4329, 4329, 328276053507568983), (4330, 4330, 325025795552048498), (4331, 4331, 321807718368364850), (4332, 4332, 318621503335014703), (4333, 4333, 315466834985163072), (4334, 4334, 312343400975408982), (4335, 4335, 309250892054860378), (4336, 7209, 306189002034515226)]

def glob2 : ℕ := 41924418349339890037

def runs3 : List (ℕ × ℕ × ℕ) := [(0, 3828, 0), (3829, 3829, 72862520323003621), (3830, 3830, 254782139663464492), (3831, 3831, 434900574654019810), (3832, 3832, 613235658803084482), (3833, 3833, 789805049049683166), (3834, 3834, 964626227511662062), (3835, 3835, 1137716503216591661), (3836, 3836, 1309093013815531859), (3837, 3837, 1478772727279829084), (3838, 3838, 1646772443581113466), (3839, 3839, 1813108796354662358), (3840, 3840, 1977798254546294925), (3841, 3841, 2140857124042960833), (3842, 3842, 2302301549287184504), (3843, 3843, 2462147514875524773), (3844, 3844, 2620410847141208207), (3845, 3845, 2777107215721092795), (3846, 3846, 2932252135107117140), (3847, 3847, 3085860966182388768), (3848, 3848, 3237948917742063648), (3849, 3849, 3388531047999167489), (3850, 3850, 3537622266075507926), (3851, 3851, 3685237333477825190), (3852, 3852, 3831390865559327432), (3853, 3853, 3976097332966755394), (3854, 3854, 4119371063073119713), (3855, 3855, 4261226241396252702), (3856, 3856, 4401676913003315068), (3857, 3857, 4540736983901396618), (3858, 3858, 4678420222414348648), (3859, 3859, 4814740260545984321), (3860, 3860, 4949710595329782017), (3861, 3861, 5083344590165225280), (3862, 3862, 5215655476140911679), (3863, 3863, 5346656353344561580), (3864, 3864, 5476360192160056531), (3865, 3865, 5604779834551635690), (3866, 3866, 5731927995335377432), (3867, 3867, 5857817263438092028), (3868, 3868, 5982460103143750043), (3869, 3869, 6105868855327569861), (3870, 3870, 6228055738677886512), (3871, 3871, 6349032850905922800), (3872, 3872, 6468812169943582491), (3873, 3873, 6587405555129384166), (3874, 3874, 6704824748382653150), (3875, 3875, 6821081375366087789), (3876, 3876, 6936186946636815153), (3877, 3877, 7050152858786050168), (3878, 3878, 7162990395567470974), (3879, 3879, 7274710729014422268), (3880, 3880, 7385324920546057212), (3881, 3881, 7494843922062527453), (3882, 3882, 7603278577029329673), (3883, 3883, 7710639621550916029), (3884, 3884, 7816937685433674797), (3885, 3885, 7922183293238386449), (3886, 3886, 8026386865322259371), (3887, 3887, 8129558718870648403), (3888, 3888, 8231709068918558336), (3889, 3889, 8332848029362033517), (3890, 3890, 8432985613959533696), (3891, 3891, 8532131737323395260), (3892, 3892, 8630296215901476016), (3893, 3893, 8727488768949080725), (3894, 3894, 8823719019491263605), (3895, 3895, 8918996495275603090), (3896, 3896, 9013330629715543175), (3897, 3897, 9106730762824394743), (3898, 3898, 9199206142140089366), (3899, 3899, 9290765923640777111), (3900, 3900, 9381419172651359037), (3901, 3901, 9471174864741044112), (3902, 3902, 9560041886612019433), (3903, 3903, 9648029036979321732), (3904, 3904, 9735145027441997276), (3905, 3905, 9821398483345636428), (3906, 3906, 9906797944636368261), (3907, 3907, 9991351866706399780), (3908, 3908, 10075068621231183461), (3909, 3909, 10157956496998296017), (3910, 3910, 10240023700728110429), (3911, 3911, 10321278357886342520), (3912, 3912, 10401728513488552511), (3913, 3913, 10481382132896681215), (3914, 3914, 10560247102607699734), (3915, 3915, 10638331231034450743), (3916, 3916, 10715642249278758672), (3917, 3917, 10792187811896885335), (3918, 3918, 10867975497657406783), (3919, 3919, 10943012810291586435), (3920, 3920, 11017307179236318764), (3921, 3921, 11090865960369717109), (3922, 3922, 11163696436739418440), (3923, 3923, 11235805819283677185), (3924, 3924, 11307201247545319506), (3925, 3925, 11377889790378628735), (3926, 3926, 11447878446649231931), (3927, 3927, 11517174145927056879), (3928, 3928, 11585783749172428114), (3929, 3929, 11653714049415369931), (3930, 3930, 11720971772428183611), (3931, 3931, 11787563577391365472), (3932, 3932, 11853496057552931672), (3933, 3933, 11918775740881215037), (3934, 3934, 11983409090711198568), (3935, 3935, 12047402506384449588), (3936, 3936, 12110762323882717925), (3937, 3937, 12173494816455260833), (3938, 3938, 12235606195239956781), (3939, 3939, 12297102609878269601), (3940, 3940, 12357990149124123879), (3941, 3941, 12418274841446751876), (3942, 3942, 12477962655627571676), (3943, 3943, 12537059501351155635), (3944, 3944, 12595571229790347675), (3945, 3945, 12653503634185587318), (3946, 3946, 12710862450418497855), (3947, 3947, 12767653357579795417), (3948, 3948, 12823881978531575182), (3949, 3949, 12879553880464030394), (3950, 3950, 12934674575446659317), (3951, 3951, 12989249520974014686), (3952, 3952, 13043284120506049705), (3953, 3953, 13096783724003114081), (3954, 3954, 13149753628455653066), (3955, 3955, 13202199078408661963), (3956, 3956, 13254125266480947999), (3957, 3957, 13305537333879251005), (3958, 3958, 13356440370907273783), (3959, 3959, 13406839417469672574), (3960, 3960, 13456739463571057515), (3961, 3961, 13506145449810052506), (3962, 3962, 13555062267868463388), (3963, 3963, 13603494760995602876), (3964, 3964, 13651447724487820190), (3965, 3965, 13698925906163282877), (3966, 3966, 13745934006832057815), (3967, 3967, 13792476680761537952), (3968, 3968, 13838558536137260860), (3969, 3969, 13884184135519164728), (3970, 3970, 13929357996293326975), (3971, 3971, 13974084591119230189), (3972, 3972, 14018368348372599708), (3973, 3973, 14062213652583856658), (3974, 3974, 14105624844872229875), (3975, 3975, 14148606223375569694), (3976, 3976, 14191162043675906149), (3977, 3977, 14233296519220793728), (3978, 3978, 14275013821740484400), (3979, 3979, 14316318081660970214), (3980, 3980, 14357213388512936367), (3981, 3981, 14397703791336665231), (3982, 3982, 14437793299082931432), (3983, 3983, 14477485881009927672), (3984, 3984, 14516785467076260582), (3985, 3985, 14555695948330055543), (3986, 3986, 14594221177294208969), (3987, 3987, 14632364968347826223), (3988, 3988, 14670131098103882910), (3989, 3989, 14707523305783146957), (3990, 3990, 14744545293584398488), (3991, 3991, 14781200727050984163), (3992, 3992, 14817493235433742256), (3993, 3993, 14853426412050334428), (3994, 3994, 14889003814641019747), (3995, 3995, 14924228965720906201), (3996, 3996, 14959105352928714572), (3997, 3997, 14993636429372089196), (3998, 3998, 15027825613969489814), (3999, 3999, 15061676291788698347), (4000, 4000, 15095191814381974121), (4001, 4001, 15128375500117890730), (4002, 4002, 15161230634509887373), (4003, 4003, 15193760470541567217), (4004, 4004, 15225968228988774983), (4005, 4005, 15257857098738485643), (4006, 4006, 15289430237104535801), (4007, 4007, 15320690770140229027), (4008, 4008, 15351641792947846082), (4009, 4009, 15382286369985090691), (4010, 4010, 15412627535368501196), (4011, 4011, 15442668293173858131), (4012, 4012, 15472411617733617472), (4013, 4013, 15501860453931398998), (4014, 4014, 15531017717493558925), (4015, 4015, 15559886295277875684), (4016, 4016, 15588469045559377426), (4017, 4017, 15616768798313339547), (4018, 4018, 15644788355495480261), (4019, 4019, 15672530491319381957), (4020, 4020, 15699997952531165815), (4021, 4021, 15727193458681446863), (4022, 4022, 15754119702394596415), (4023, 4023, 15780779349635338545), (4024, 4024, 15807175039972706992), (4025, 4025, 15833309386841388622), (4026, 4026, 15859184977800479344), (4027, 4027, 15884804374789678080), (4028, 4028, 15910170114382944154), (4029, 4029, 15935284708039643238), (4030, 4030, 15960150642353206687), (4031, 4031, 15984770379297328914), (4032, 4032, 16009146356469727159), (4033, 4033, 16033280987333487797), (4034, 4034, 16057176661456023083), (4035, 4035, 16080835744745661979), (4036, 4036, 16104260579685898510), (4037, 4037, 16127453485567320818), (4038, 4038, 16150416758717243895), (4039, 4039, 16173152672727068724), (4040, 4040, 16195663478677390337), (4041, 4041, 16217951405360877082), (4042, 4042, 16240018659502943167), (4043, 4043, 16261867425980236320), (4044, 4044, 16283499868036962214), (4045, 4045, 16304918127499067059), (4046, 4046, 16326124324986299580), (4047, 4047, 16347120560122173362), (4048, 4048, 16367908911741850375), (4049, 4049, 16388491438097966229), (4050, 4050, 16408870177064417569), (4051, 4051, 16429047146338131767), (4052, 4052, 16449024343638838895), (4053, 4053, 16468803746906865753), (4054, 4054, 16488387314498971554), (4055, 4055, 16507776985382244624), (4056, 4056, 16526974679326079347), (4057, 4057, 16545982297092252339), (4058, 4058, 16564801720623116689), (4059, 4059, 16583434813227932876), (4060, 4060, 16601883419767354844), (4061, 4061, 16620149366836089465), (4062, 4062, 16638234462943747506), (4063, 4063, 16656140498693903983), (4064, 4064, 16673869246961385642), (4065, 4065, 16691422463067803127), (4066, 4066, 16708801884955345192), (4067, 4067, 16726009233358852186), (4068, 4068, 16743046211976185844), (4069, 4069, 16759914507636912237), (4070, 4070, 16776615790469314608), (4071, 4071, 16793151714065752598), (4072, 4072, 16809523915646384271), (4073, 4073, 16825734016221267116), (4074, 4074, 16841783620750854091), (4075, 4075, 16857674318304900602), (4076, 4076, 16873407682219798136), (4077, 4077, 16888985270254350151), (4078, 4078, 16904408624744005611), (4079, 4079, 16919679272753565473), (4080, 4080, 16934798726228377217), (4081, 4081, 16949768482144032409), (4082, 4082, 16964590022654582104), (4083, 4083, 16979264815239284772), (4084, 4084, 16993794312847901276), (4085, 4085, 17008179954044551279), (4086, 4086, 17022423163150145342), (4087, 4087, 17036525350383406790), (4088, 4088, 17050487912000497333), (4089, 4089, 17064312230433260246), (4090, 4090, 17077999674426094815), (4091, 4091, 17091551599171475575), (4092, 4092, 17104969346444129793), (4093, 4093, 17118254244733886445), (4094, 4094, 17131407609377209862), (4095, 4095, 17144430742687431068), (4096, 4096, 17157324934083689687), (4097, 4097, 17170091460218599211), (4098, 4098, 17182731585104648245), (4099, 4099, 17195246560239350259), (4100, 4100, 17207637624729154232), (4101, 4101, 17219906005412128464), (4102, 4102, 17232052916979429683), (4103, 4103, 17244079562095569504), (4104, 4104, 17255987131517490119), (4105, 4105, 17267776804212461025), (4106, 4106, 17279449747474808457), (4107, 4107, 17291007117041489082), (4108, 4108, 17302450057206519404), (4109, 4109, 17313779700934272198), (4110, 4110, 17324997169971651203), (4111, 4111, 17336103574959155167), (4112, 4112, 17347100015540842261), (4113, 4113, 17357987580473205720), (4114, 4114, 17368767347732971521), (4115, 4115, 17379440384623828749), (4116, 4116, 17390007747882103233), (4117, 4117, 17400470483781384900), (4118, 4118, 17410829628236119224), (4119, 4119, 17421086206904173010), (4120, 4120, 17431241235288384680), (4121, 4121, 17441295718837109105), (4122, 4122, 17451250653043766951), (4123, 4123, 17461107023545408384), (4124, 4124, 17470865806220300891), (4125, 4125, 17480527967284550898), (4126, 4126, 17490094463387768727), (4127, 4127, 17499566241707786379), (4128, 4128, 17508944240044437520), (4129, 4129, 17518229386912408947), (4130, 4130, 17527422601633172736), (4131, 4131, 17536524794426008170), (4132, 4132, 17545536866498122462), (4133, 4133, 17554459710133879186), (4134, 4134, 17563294208783143270), (4135, 4135, 17572041237148751273), (4136, 4136, 17580701661273115633), (4137, 4137, 17589276338623971435), (4138, 4138, 17597766118179274209), (4139, 4139, 17606171840511257153), (4140, 4140, 17614494337869656109), (4141, 4141, 17622734434264110520), (4142, 4142, 17630892945545748550), (4143, 4143, 17638970679487964422), (4144, 4144, 17646968435866395979), (4145, 4145, 17654887006538110391), (4146, 4146, 17662727175520005848), (4147, 4147, 17670489719066436995), (4148, 4148, 17678175405746071793), (4149, 4149, 17685784996517987435), (4150, 4150, 17693319244807012823), (4151, 4151, 17700778896578325088), (4152, 4152, 17708164690411307529), (4153, 4153, 17715477357572676282), (4154, 4154, 17722717622088882969), (4155, 4155, 17729886200817800480), (4156, 4156, 17736983803519699006), (4157, 4157, 17744011132927519329), (4158, 4158, 17750968884816450342), (4159, 4159, 17757857748072817681), (4160, 4160, 17764678404762290294), (4161, 4161, 17771431530197411694), (4162, 4162, 17778117793004462584), (4163, 4163, 17784737855189661485), (4164, 4164, 17791292372204709902), (4165, 4165, 17797781993011688533), (4166, 4166, 17804207360147310940), (4167, 4167, 17810569109786541046), (4168, 4168, 17816867871805580754), (4169, 4169, 17823104269844233931), (4170, 4170, 17829278921367652918), (4171, 4171, 17835392437727473697), (4172, 4172, 17841445424222345756), (4173, 4173, 17847438480157862646), (4174, 4174, 17853372198905899170), (4175, 4175, 17859247167963361075), (4176, 4176, 17865063969010353061), (4177, 4177, 17870823177967770869), (4178, 4178, 17876525365054323153), (4179, 4179, 17882171094842988781), (4180, 4180, 17887760926316915146), (4181, 4181, 17893295412924763032), (4182, 4182, 17898775102635503513), (4183, 4183, 17904200537992672306), (4184, 4184, 17909572256168086953), (4185, 4185, 17914890789015032147), (4186, 4186, 17920156663120918479), (4187, 4187, 17925370399859419797), (4188, 4188, 17930532515442094370), (4189, 4189, 17935643520969494936), (4190, 4190, 17940703922481772725), (4191, 4191, 17945714221008780437), (4192, 4192, 17950674912619679162), (4193, 4193, 17955586488472054136), (4194, 4194, 17960449434860544210), (4195, 4195, 17965264233264989828), (4196, 4196, 17970031360398104301), (4197, 4197, 17974751288252673087), (4198, 4198, 17979424484148285745), (4199, 4199, 17984051410777605210), (4200, 4200, 17988632526252178936), (4201, 4201, 17993168284147796488), (4202, 4202, 17997659133549398024), (4203, 4203, 18002105519095538158), (4204, 4204, 18006507881022409579), (4205, 4205, 18010866655207430787), (4206, 4206, 18015182273212402280), (4207, 4207, 18019455162326235442), (4208, 4208, 18023685745607258374), (4209, 4209, 18027874441925102862), (4210, 4210, 18032021666002176612), (4211, 4211, 18036127828454724879), (4212, 4212, 18040193335833485540), (4213, 4213, 18044218590663941640), (4214, 4214, 18048203991486175402), (4215, 4215, 18052149932894327642), (4216, 4216, 18056056805575666493), (4217, 4217, 18059924996349269316), (4218, 4218, 18063754888204321616), (4219, 4219, 18067546860338036765), (4220, 4220, 18071301288193200278), (4221, 4221, 18075018543495342370), (4222, 4222, 18078698994289542462), (4223, 4223, 18082343004976869285), (4224, 4224, 18085950936350460199), (4225, 4225, 18089523145631243283), (4226, 4226, 18093059986503305741), (4227, 4227, 18096561809148912136), (4228, 4228, 18100028960283175894), (4229, 4229, 18103461783188387534), (4230, 4230, 18106860617748003020), (4231, 4231, 18110225800480295581), (4232, 4232, 18113557664571674353), (4233, 4233, 18116856539909673138), (4234, 4234, 18120122753115612529), (4235, 4235, 18123356627576938659), (4236, 4236, 18126558483479241757), (4237, 4237, 18129728637837957696), (4238, 4238, 18132867404529755656), (4239, 4239, 18135975094323615022), (4240, 4240, 18139052014911594592), (4241, 4241, 18142098470939297137), (4242, 4242, 18145114764036032330), (4243, 4243, 18148101192844681036), (4244, 4244, 18151058053051263913), (4245, 4245, 18153985637414217256), (4246, 4246, 18156884235793378983), (4247, 4247, 18159754135178687623), (4248, 4248, 18162595619718597167), (4249, 4249, 18165408970748210577), (4250, 4250, 18168194466817134746), (4251, 4251, 18170952383717059666), (4252, 4252, 18173682994509064536), (4253, 4253, 18176386569550653517), (4254, 4254, 18179063376522523796), (4255, 4255, 18181713680455068626), (4256, 4256, 18184337743754617962), (4257, 4257, 18186935826229419285), (4258, 4258, 18189508185115361190), (4259, 4259, 18192055075101442283), (4260, 4260, 18194576748354987920), (4261, 4261, 18197073454546617263), (4262, 4262, 18199545440874963148), (4263, 4263, 18201992952091147192), (4264, 4264, 18204416230523012583), (4265, 4265, 18206815516099116930), (4266, 4266, 18209191046372487570), (4267, 4267, 18211543056544141670), (4268, 4268, 18213871779486373451), (4269, 4269, 18216177445765810859), (4270, 4270, 18218460283666243936), (4271, 4271, 18220720519211227180), (4272, 4272, 18222958376186458115), (4273, 4273, 18225174076161934288), (4274, 4274, 18227367838513890895), (4275, 4275, 18229539880446521200), (4276, 4276, 18231690417013481897), (4277, 4277, 18233819661139185557), (4278, 4278, 18235927823639882251), (4279, 4279, 18238015113244532443), (4280, 4280, 18240081736615473227), (4281, 4281, 18242127898368879943), (4282, 4282, 18244153801095025208), (4283, 4283, 18246159645378337350), (4284, 4284, 18248145629817260264), (4285, 4285, 18250111951043916614), (4286, 4286, 18252058803743576366), (4287, 4287, 18253986380673932557), (4288, 4288, 18255894872684186211), (4289, 4289, 18257784468733942304), (4290, 4290, 18259655355911918634), (4291, 4291, 18261507719454469455), (4292, 4292, 18263341742763925714), (4293, 4293, 18265157607426753694), (4294, 4294, 18266955493231533871), (4295, 4295, 18268735578186761770), (4296, 4296, 18270498038538472560), (4297, 4297, 18272243048787691165), (4298, 4298, 18273970781707709585), (4299, 4299, 18275681408361193169), (4300, 4300, 18277375098117117511), (4301, 4301, 18279052018667537650), (4302, 4302, 18280712336044191254), (4303, 4303, 18282356214634937396), (4304, 4304, 18283983817200032586), (4305, 4305, 18285595304888245646), (4306, 4306, 18287190837252813032), (4307, 4307, 18288770572267236186), (4308, 4308, 18290334666340922478), (4309, 4309, 18291883274334671281), (4310, 4310, 18293416549576006730), (4311, 4311, 18294934643874358659), (4312, 4312, 18296437707536093243), (4313, 4313, 18297925889379394811), (4314, 4314, 18299399336749000324), (4315, 4315, 18300858195530787961), (4316, 4316, 18302302610166221264), (4317, 4317, 18303732723666650278), (4318, 4318, 18305148677627471083), (4319, 4319, 18306550612242145148), (4320, 4320, 18307938666316079865), (4321, 4321, 18309312977280371665), (4322, 4322, 18310673681205413050), (4323, 4323, 18312020912814364917), (4324, 4324, 18313354805496495479), (4325, 4325, 18314675491320387124), (4326, 4326, 18315983101047012515), (4327, 4327, 18317277764142681219), (4328, 4328, 18318559608791858153), (4329, 4329, 18319828761909855118), (4330, 4330, 18321085349155396668), (4331, 4331, 18322329494943061568), (4332, 4332, 18323561322455601074), (4333, 4333, 18324780953656135237), (4334, 4334, 18325988509300228469), (4335, 4335, 18327184108947845530), (4336, 7209, 18446744073709506122)]

def glob3 : ℕ := 18446744073709551616

def runs4 : List (ℕ × ℕ × ℕ) := [(0, 3000, 175340284961753208822), (3001, 3001, 175341247480004128697), (3002, 3002, 175342219630587838544), (3003, 3003, 175343201509971447559), (3004, 3004, 175344193215589627877), (3005, 3005, 175345194845854348374), (3006, 3006, 175346206500164706996), (3007, 3007, 175347228278916862590), (3008, 3008, 175348260283514067286), (3009, 3009, 175349302616376800434), (3010, 3010, 175350355380953005156), (3011, 3011, 175351418681728428561), (3012, 3012, 175352492624237066668), (3013, 3013, 175353577315071715141), (3014, 3014, 175354672861894626895), (3015, 3015, 175355779373448277683), (3016, 3016, 175356896959566240770), (3017, 3017, 175358025731184171804), (3018, 3018, 175359165800350905038), (3019, 3019, 175360317280239662018), (3020, 3020, 175361480285159373914), (3021, 3021, 175362654930566118653), (3022, 3022, 175363841333074674031), (3023, 3023, 175365039610470188006), (3024, 3024, 175366249881719967365), (3025, 3025, 175367472266985385996), (3026, 3026, 175368706887633913975), (3027, 3027, 175369953866251268742), (3028, 3028, 175371213326653689590), (3029, 3029, 175372485393900336759), (3030, 3030, 175373770194305816412), (3031, 3031, 175375067855452832783), (3032, 3032, 175376378506204968822), (3033, 3033, 175377702276719596650), (3034, 3034, 175379039298460919160), (3035, 3035, 175380389704213144133), (3036, 3036, 175381753628093792219), (3037, 3037, 175383131205567140174), (3038, 3038, 175384522573457800747), (3039, 3039, 175385927869964440627), (3040, 3040, 175387347234673637875), (3041, 3041, 175388780808573880296), (3042, 3042, 175390228734069706177), (3043, 3043, 175391691154995988906), (3044, 3044, 175393168216632366914), (3045, 3045, 175394660065717820484), (3046, 3046, 175396166850465396922), (3047, 3047, 175397688720577085633), (3048, 3048, 175399225827258844658), (3049, 3049, 175400778323235780237), (3050, 3050, 175402346362767480990), (3051, 3051, 175403930101663508301), (3052, 3052, 175405529697299044560), (3053, 3053, 175407145308630700856), (3054, 3054, 175408777096212485819), (3055, 3055, 175410425222211937247), (3056, 3056, 175412089850426418243), (3057, 3057, 175413771146299579536), (3058, 3058, 175415469276937989747), (3059, 3059, 175417184411127935321), (3060, 3060, 175418916719352391898), (3061, 3061, 175420666373808168918), (3062, 3062, 175422433548423229239), (3063, 3063, 175424218418874185617), (3064, 3064, 175426021162603975869), (3065, 3065, 175427841958839718593), (3066, 3066, 175429680988610751324), (3067, 3067, 175431538434766853031), (3068, 3068, 175433414481996652868), (3069, 3069, 175435309316846227141), (3070, 3070, 175437223127737886438), (3071, 3071, 175439156104989154922), (3072, 3072, 175441108440831943787), (3073, 3073, 175443080329431920908), (3074, 3074, 175445071966908078745), (3075, 3075, 175447083551352502561), (3076, 3076, 175449115282850341066), (3077, 3077, 175451167363499981592), (3078, 3078, 175453239997433431959), (3079, 3079, 175455333390836911181), (3080, 3080, 175457447751971651215), (3081, 3081, 175459583291194911959), (3082, 3082, 175461740220981211741), (3083, 3083, 175463918755943775563), (3084, 3084, 175466119112856203385), (3085, 3085, 175468341510674360756), (3086, 3086, 175470586170558494148), (3087, 3087, 175472853315895573335), (3088, 3088, 175475143172321863218), (3089, 3089, 175477455967745727518), (3090, 3090, 175479791932370666764), (3091, 3091, 175482151298718593059), (3092, 3092, 175484534301653344112), (3093, 3093, 175486941178404439070), (3094, 3094, 175489372168591078693), (3095, 3095, 175491827514246392457), (3096, 3096, 175494307459841935192), (3097, 3097, 175496812252312435902), (3098, 3098, 175499342141080801415), (3099, 3099, 175501897378083377587), (3100, 3100, 175504478217795470757), (3101, 3101, 175507084917257132240), (3102, 3102, 175509717736099208620), (3103, 3103, 175512376936569660682), (3104, 3104, 175515062783560153823), (3105, 3105, 175517775544632922823), (3106, 3106, 175520515490047913901), (3107, 3107, 175523282892790206994), (3108, 3108, 175526078028597721240), (3109, 3109, 175528901175989206687), (3110, 3110, 175531752616292525262), (3111, 3111, 175534632633673224094), (3112, 3112, 175537541515163404304), (3113, 3113, 175540479550690888405), (3114, 3114, 175543447033108689515), (3115, 3115, 175546444258224785592), (3116, 3116, 175549471524832201955), (3117, 3117, 175552529134739405391), (3118, 3118, 175555617392801013175), (3119, 3119, 175558736606948820379), (3120, 3120, 175561887088223148875), (3121, 3121, 175565069150804521489), (3122, 3122, 175568283112045664781), (3123, 3123, 175571529292503843987), (3124, 3124, 175574808015973533684), (3125, 3125, 175578119609519427798), (3126, 3126, 175581464403509792582), (3127, 3127, 175584842731650166279), (3128, 3128, 175588254931017409184), (3129, 3129, 175591701342094107893), (3130, 3130, 175595182308803337552), (3131, 3131, 175598698178543785964), (3132, 3132, 175602249302225243474), (3133, 3133, 175605836034304462576), (3134, 3134, 175609458732821391231), (3135, 3135, 175613117759435783963), (3136, 3136, 175616813479464194796), (3137, 3137, 175620546261917356187), (3138, 3138, 175624316479537948140), (3139, 3139, 175628124508838761723), (3140, 3140, 175631970730141261281), (3141, 3141, 175635855527614549680), (3142, 3142, 175639779289314740952), (3143, 3143, 175643742407224744784), (3144, 3144, 175647745277294467344), (3145, 3145, 175651788299481432965), (3146, 3146, 175655871877791831287), (3147, 3147, 175659996420321994504), (3148, 3148, 175664162339300309414), (3149, 3149, 175668370051129569021), (3150, 3150, 175672619976429768500), (3151, 3151, 175676912540081350403), (3152, 3152, 175681248171268904012), (3153, 3153, 175685627303525323834), (3154, 3154, 175690050374776432273), (3155, 3155, 175694517827386071579), (3156, 3156, 175699030108201670243), (3157, 3157, 175703587668600289043), (3158, 3158, 175708190964535152037), (3159, 3159, 175712840456582667858), (3160, 3160, 175717536609989946688), (3161, 3161, 175722279894722818432), (3162, 3162, 175727070785514357585), (3163, 3163, 175731909761913920434), (3164, 3164, 175736797308336700251), (3165, 3165, 175741733914113806215), (3166, 3166, 175746720073542871887), (3167, 3167, 175751756285939199101), (3168, 3168, 175756843055687443239), (3169, 3169, 175761980892293845891), (3170, 3170, 175767170310439021018), (3171, 3171, 175772411830031300762), (3172, 3172, 175777705976260647171), (3173, 3173, 175783053279653136135), (3174, 3174, 175788454276126019939), (3175, 3175, 175793909507043374913), (3176, 3176, 175799419519272340711), (3177, 3177, 175804984865239957869), (3178, 3178, 175810606102990610345), (3179, 3179, 175816283796244079842), (3180, 3180, 175822018514454218777), (3181, 3181, 175827810832868248882), (3182, 3182, 175833661332586692461), (3183, 3183, 175839570600623943450), (3184, 3184, 175845539229969485503), (3185, 3185, 175851567819649764404), (3186, 3186, 175857656974790722221), (3187, 3187, 175863807306681000682), (3188, 3188, 175870019432835821372), (3189, 3189, 175876293977061550412), (3190, 3190, 175882631569520955423), (3191, 3191, 175889032846799162618), (3192, 3192, 175895498451970322016), (3193, 3193, 175902029034664988832), (3194, 3194, 175908625251138229227), (3195, 3195, 175915287764338458684), (3196, 3196, 175922017243977021384), (3197, 3197, 175928814366598519077), (3198, 3198, 175935679815651898031), (3199, 3199, 175942614281562302746), (3200, 3200, 175949618461803705268), (3201, 3201, 175956693060972318995), (3202, 3202, 175963838790860806022), (3203, 3203, 175971056370533287170), (3204, 3204, 175978346526401163965), (3205, 3205, 175985709992299761940), (3206, 3206, 175993147509565804771), (3207, 3207, 176000659827115728872), (3208, 3208, 176008247701524848176), (3209, 3209, 176015911897107379007), (3210, 3210, 176023653185997335003), (3211, 3211, 176031472348230302253), (3212, 3212, 176039370171826104874), (3213, 3213, 176047347452872371445), (3214, 3214, 176055404995609012808), (3215, 3215, 176063543612513621896), (3216, 3216, 176071764124387806399), (3217, 3217, 176080067360444465196), (3218, 3218, 176088454158396019652), (3219, 3219, 176096925364543610985), (3220, 3220, 176105481833867275099), (3221, 3221, 176114124430117106400), (3222, 3222, 176122854025905422264), (3223, 3223, 176131671502799939991), (3224, 3224, 176140577751417978238), (3225, 3225, 176149573671521695052), (3226, 3226, 176158660172114374838), (3227, 3227, 176167838171537776693), (3228, 3228, 176177108597570556772), (3229, 3229, 176186472387527777465), (3230, 3230, 176195930488361516359), (3231, 3231, 176205483856762588144), (3232, 3232, 176215133459263392758), (3233, 3233, 176224880272341903297), (3234, 3234, 176234725282526807349), (3235, 3235, 176244669486503815626), (3236, 3236, 176254713891223151943), (3237, 3237, 176264859514008238789), (3238, 3238, 176275107382665592916), (3239, 3239, 176285458535595945575), (3240, 3240, 176295914021906602246), (3241, 3241, 176306474901525056858), (3242, 3242, 176317142245313875770), (3243, 3243, 176327917135186866931), (3244, 3244, 176338800664226549883), (3245, 3245, 176349793936802942478), (3246, 3246, 176360898068693680393), (3247, 3247, 176372114187205485755), (3248, 3248, 176383443431297001407), (3249, 3249, 176394886951703007583), (3250, 3250, 176406445911060037981), (3251, 3251, 176418121484033412471), (3252, 3252, 176429914857445703903), (3253, 3253, 176441827230406656743), (3254, 3254, 176453859814444575477), (3255, 3255, 176466013833639201012), (3256, 3256, 176478290524756093551), (3257, 3257, 176490691137382540639), (3258, 3258, 176503216934065009411), (3259, 3259, 176515869190448162274), (3260, 3260, 176528649195415455564), (3261, 3261, 176541558251231340996), (3262, 3262, 176554597673685089982), (3263, 3263, 176567768792236261210), (3264, 3264, 176581072950161832132), (3265, 3265, 176594511504705015346), (3266, 3266, 176608085827225781114), (3267, 3267, 176621797303353107594), (3268, 3268, 176635647333138980664), (3269, 3269, 176649637331214165522), (3270, 3270, 176663768726945772589), (3271, 3271, 176678042964596640540), (3272, 3272, 176692461503486559643), (3273, 3273, 176707025818155358901), (3274, 3274, 176721737398527880865), (3275, 3275, 176736597750080868294), (3276, 3276, 176751608394011787224), (3277, 3277, 176766770867409611352), (3278, 3278, 176782086723427593017), (3279, 3279, 176797557531458046417), (3280, 3280, 176813184877309169097), (3281, 3281, 176828970363383928109), (3282, 3282, 176844915608861037656), (3283, 3283, 176861022249878055412), (3284, 3284, 176877291939716625127), (3285, 3285, 176893726348989893528), (3286, 3286, 176910327165832129958), (3287, 3287, 176927096096090577596), (3288, 3288, 176944034863519565577), (3289, 3289, 176961145209976911719), (3290, 3290, 176978428895622646052), (3291, 3291, 176995887699120085784), (3292, 3292, 177013523417839292802), (3293, 3293, 177031337868062945286), (3294, 3294, 177049332885194655472), (3295, 3295, 177067510323969766128), (3296, 3296, 177085872058668658762), (3297, 3297, 177104419983332607106), (3298, 3298, 177123156011982209945), (3299, 3299, 177142082078838437851), (3300, 3300, 177161200138546328960), (3301, 3301, 177180512166401369418), (3302, 3302, 177200020158578594723), (3303, 3303, 177219726132364448728), (3304, 3304, 177239632126391437629), (3305, 3305, 177259740200875616872), (3306, 3306, 177280052437856949492), (3307, 3307, 177300570941442574981), (3308, 3308, 177321297838053028436), (3309, 3309, 177342235276671450313), (3310, 3310, 177363385429095827797), (3311, 3311, 177384750490194309404), (3312, 3312, 177406332678163635115), (3313, 3313, 177428134234790725001), (3314, 3314, 177450157425717469987), (3315, 3315, 177472404540708769087), (3316, 3316, 177494877893923858170), (3317, 3317, 177517579824190976006), (3318, 3318, 177540512695285414113), (3319, 3319, 177563678896210997634), (3320, 3320, 177587080841485045266), (3321, 3321, 177610720971426857021), (3322, 3322, 177634601752449779385), (3323, 3323, 177658725677356898263), (3324, 3324, 177683095265640410885), (3325, 3325, 177707713063784728727), (3326, 3326, 177732581645573364295), (3327, 3327, 177757703612399655540), (3328, 3328, 177783081593581382503), (3329, 3329, 177808718246679331728), (3330, 3330, 177834616257819864866), (3331, 3331, 177860778342021548846), (3332, 3332, 177887207243525905909), (3333, 3333, 177913905736132342807), (3334, 3334, 177940876623537319423), (3335, 3335, 177968122739677818080), (3336, 3336, 177995646949079175830), (3337, 3337, 178023452147207343074), (3338, 3338, 178051541260825632879), (3339, 3339, 178079917248356026507), (3340, 3340, 178108583100245101700), (3341, 3341, 178137541839334651462), (3342, 3342, 178166796521237062158), (3343, 3343, 178196350234715520971), (3344, 3344, 178226206102069123912), (3345, 3345, 178256367279522956812), (3346, 3346, 178286836957623222950), (3347, 3347, 178317618361637492236), (3348, 3348, 178348714751960148152), (3349, 3349, 178380129424523109969), (3350, 3350, 178411865711211909087), (3351, 3351, 178443926980287199696), (3352, 3352, 178476316636811785380), (3353, 3353, 178509038123083244659), (3354, 3354, 178542094919072239940), (3355, 3355, 178575490542866595786), (3356, 3356, 178609228551121233969), (3357, 3357, 178643312539514054223), (3358, 3358, 178677746143207851259), (3359, 3359, 178712533037318360132), (3360, 3360, 178747676937388523702), (3361, 3361, 178783181599869077586), (3362, 3362, 178819050822605549680), (3363, 3363, 178855288445331773060), (3364, 3364, 178891898350170012817), (3365, 3365, 178928884462137809187), (3366, 3366, 178966250749661641165), (3367, 3367, 179004001225097516635), (3368, 3368, 179042139945258596998), (3369, 3369, 179080671011949966161), (3370, 3370, 179119598572510655795), (3371, 3371, 179158926820363040745), (3372, 3372, 179198659995569720548), (3373, 3373, 179238802385398005154), (3374, 3374, 179279358324892125035), (3375, 3375, 179320332197453288114), (3376, 3376, 179361728435427708153), (3377, 3377, 179403551520702731528), (3378, 3378, 179445805985311191661), (3379, 3379, 179488496412044122740), (3380, 3380, 179531627435071966810), (3381, 3381, 179575203740574410767), (3382, 3382, 179619230067378992353), (3383, 3383, 179663711207608616798), (3384, 3384, 179708652007338128422), (3385, 3385, 179754057367260084184), (3386, 3386, 179799932243359878918), (3387, 3387, 179846281647600374817), (3388, 3388, 179893110648616190559), (3389, 3389, 179940424372417808449), (3390, 3390, 179988228003105660871), (3391, 3391, 180036526783594360468), (3392, 3392, 180085326016347241523), (3393, 3393, 180134631064121383244), (3394, 3394, 180184447350723288873), (3395, 3395, 180234780361775397890), (3396, 3396, 180285635645493611942), (3397, 3397, 180337018813476018628), (3398, 3398, 180388935541503000774), (3399, 3399, 180441391570348922483), (3400, 3400, 180494392706605586905), (3401, 3401, 180547944823517664480), (3402, 3402, 180602053861830294227), (3403, 3403, 180656725830649064624), (3404, 3404, 180711966808312584625), (3405, 3405, 180767782943277859496), (3406, 3406, 180824180455018690324), (3407, 3407, 180881165634937320387), (3408, 3408, 180938744847289555931), (3409, 3409, 180996924530123593401), (3410, 3410, 181055711196232789761), (3411, 3411, 181115111434122617208), (3412, 3412, 181175131908992048410), (3413, 3413, 181235779363729623246), (3414, 3414, 181297060619924453079), (3415, 3415, 181358982578892423684), (3416, 3416, 181421552222717863196), (3417, 3417, 181484776615310946776), (3418, 3418, 181548662903481115196), (3419, 3419, 181613218318026790096), (3420, 3420, 181678450174841674412), (3421, 3421, 181744365876037932316), (3422, 3422, 181810972911086548979), (3423, 3423, 181878278857975176595), (3424, 3424, 181946291384383779354), (3425, 3425, 182015018248878396449), (3426, 3426, 182084467302123348746), (3427, 3427, 182154646488112221438), (3428, 3428, 182225563845417961842), (3429, 3429, 182297227508462438535), (3430, 3430, 182369645708805815127), (3431, 3431, 182442826776456099375), (3432, 3432, 182516779141199235778), (3433, 3433, 182591511333950117499), (3434, 3434, 182667031988124901313), (3435, 3435, 182743349841035017291), (3436, 3436, 182820473735303273185), (3437, 3437, 182898412620302461858), (3438, 3438, 182977175553616888747), (3439, 3439, 183056771702527245129), (3440, 3440, 183137210345519262019), (3441, 3441, 183218500873816588716), (3442, 3442, 183300652792938349507), (3443, 3443, 183383675724281841699), (3444, 3444, 183467579406730848034), (3445, 3445, 183552373698290046729), (3446, 3446, 183638068577746012723), (3447, 3447, 183724674146355314357), (3448, 3448, 183812200629560220628), (3449, 3449, 183900658378732545250), (3450, 3450, 183990057872946165227), (3451, 3451, 184080409720778763287), (3452, 3452, 184171724662143355544), (3453, 3453, 184264013570150177971), (3454, 3454, 184357287452999517875), (3455, 3455, 184451557455906089391), (3456, 3456, 184546834863055565226), (3457, 3457, 184643131099593890368), (3458, 3458, 184740457733650017304), (3459, 3459, 184838826478392716494), (3460, 3460, 184938249194122130331), (3461, 3461, 185038737890396753728), (3462, 3462, 185140304728196539708), (3463, 3463, 185242962022122844001), (3464, 3464, 185346722242635938670), (3465, 3465, 185451598018330841199), (3466, 3466, 185557602138252222293), (3467, 3467, 185664747554249172904), (3468, 3468, 185773047383370628636), (3469, 3469, 185882514910302267854), (3470, 3470, 185993163589845718339), (3471, 3471, 186105007049440926432), (3472, 3472, 186218059091732562094), (3473, 3473, 186332333697181353361), (3474, 3474, 186447845026721264187), (3475, 3475, 186564607424463450737), (3476, 3476, 186682635420447952771), (3477, 3477, 186801943733444098909), (3478, 3478, 186922547273800627295), (3479, 3479, 187044461146346546458), (3480, 3480, 187167700653343785073), (3481, 3481, 187292281297492703848), (3482, 3482, 187418218784991567909), (3483, 3483, 187545529028651103858), (3484, 3484, 187674228151065292170), (3485, 3485, 187804332487839572735), (3486, 3486, 187935858590877669270), (3487, 3487, 188068823231728266900), (3488, 3488, 188203243404992806581), (3489, 3489, 188339136331795690189), (3490, 3490, 188476519463318221003), (3491, 3491, 188615410484397636087), (3492, 3492, 188755827317192619647), (3493, 3493, 188897788124916719920), (3494, 3494, 189041311315641126493), (3495, 3495, 189186415546168300223), (3496, 3496, 189333119725977984151), (3497, 3497, 189481443021247160992), (3498, 3498, 189631404858945560974), (3499, 3499, 189783024931008363021), (3500, 3500, 189936323198587772579), (3501, 3501, 190091319896385200717), (3502, 3502, 190248035537065811717), (3503, 3503, 190406490915757249938), (3504, 3504, 190566707114634401683), (3505, 3505, 190728705507592093828), (3506, 3506, 190892507765007678358), (3507, 3507, 191058135858595500598), (3508, 3508, 191225612066355298942), (3509, 3509, 191394958977616635261), (3510, 3510, 191566199498181508001), (3511, 3511, 191739356855567354241), (3512, 3512, 191914454604352702821), (3513, 3513, 192091516631627797962), (3514, 3514, 192270567162552571813), (3515, 3515, 192451630766024404961), (3516, 3516, 192634732360458176294), (3517, 3517, 192819897219681167682), (3518, 3518, 193007150978945454900), (3519, 3519, 193196519641060483945), (3520, 3520, 193388029582648601683), (3521, 3521, 193581707560526381425), (3522, 3522, 193777580718214657805), (3523, 3523, 193975676592580261249), (3524, 3524, 194176023120612520328), (3525, 3525, 194378648646337680674), (3526, 3526, 194583581927874471731), (3527, 3527, 194790852144634137673), (3528, 3528, 195000488904668336356), (3529, 3529, 195212522252168400196), (3530, 3530, 195426982675119545605), (3531, 3531, 195643901113113713026), (3532, 3532, 195863308965324817821), (3533, 3533, 196085238098650293413), (3534, 3534, 196309720856022912169), (3535, 3535, 196536790064896976725), (3536, 3536, 196766479045913084838), (3537, 3537, 196998821621745784505), (3538, 3538, 197233852126138553182), (3539, 3539, 197471605413130655494), (3540, 3540, 197712116866480558037), (3541, 3541, 197955422409290707815), (3542, 3542, 198201558513838612652), (3543, 3543, 198450562211619297737), (3544, 3544, 198702471103604352348), (3545, 3545, 198957323370722925050), (3546, 3546, 199215157784570174168), (3547, 3547, 199476013718348833561), (3548, 3548, 199739931158049711499), (3549, 3549, 200006950713877103205), (3550, 3550, 200277113631925265310), (3551, 3551, 200550461806112273418), (3552, 3552, 200827037790377762282), (3553, 3553, 201106884811151231910), (3554, 3554, 201390046780097792542), (3555, 3555, 201676568307148416943), (3556, 3556, 201966494713821970151), (3557, 3557, 202259872046846494815), (3558, 3558, 202556747092087444860), (3559, 3559, 202857167388790781630), (3560, 3560, 203161181244149075031), (3561, 3561, 203468837748198987946), (3562, 3562, 203780186789058765403), (3563, 3563, 204095279068514600984), (3564, 3564, 204414166117965012093), (3565, 3565, 204736900314732623098), (3566, 3566, 205063534898753031468), (3567, 3567, 205394123989650717055), (3568, 3568, 205728722604212248957), (3569, 3569, 206067386674267348289), (3570, 3570, 206410173064988679035), (3571, 3571, 206757139593621563240), (3572, 3572, 207108345048655151601), (3573, 3573, 207463849209446926330), (3574, 3574, 207823712866312770412), (3575, 3575, 208187997841095206512), (3576, 3576, 208556767008222790160), (3577, 3577, 208930084316274035992), (3578, 3578, 209308014810059663115), (3579, 3579, 209690624653237366703), (3580, 3580, 210077981151473758043), (3581, 3581, 210470152776168565191), (3582, 3582, 210867209188756651438), (3583, 3583, 211269221265603889762), (3584, 3584, 211676261123513428709), (3585, 3585, 212088402145859399461), (3586, 3586, 212505719009365645802), (3587, 3587, 212928287711547608908), (3588, 3588, 213356185598836068112), (3589, 3589, 213789491395402027716), (3590, 3590, 214228285232702649243), (3591, 3591, 214672648679768759124), (3592, 3592, 215122664774255114371), (3593, 3593, 215578418054275284241), (3594, 3594, 216039994591043705061), (3595, 3595, 216507482022348189222), (3596, 3596, 216980969586876918723), (3597, 3597, 217460548159424729659), (3598, 3598, 217946310287004297609), (3599, 3599, 218438350225888666161), (3600, 3600, 218936763979612422844), (3601, 3601, 219441649337959719768), (3602, 3602, 219953105916968261425), (3603, 3603, 220471235199979340718), (3604, 3604, 220996140579764997647), (3605, 3605, 221527927401764404539), (3606, 3606, 222066703008462648736), (3607, 3607, 222612576784946189749), (3608, 3608, 223165660205670414531), (3609, 3609, 223726066882475903458), (3610, 3610, 224293912613891252418), (3611, 3611, 224869315435761574946), (3612, 3612, 225452395673243134391), (3613, 3613, 226043275994205931655), (3614, 3614, 226642081464087501019), (3615, 3615, 227248939602242647177), (3616, 3616, 227863980439835392937), (3617, 3617, 228487336579321001457), (3618, 3618, 229119143255567591731), (3619, 3619, 229759538398668583845), (3620, 3620, 230408662698498993857), (3621, 3621, 231066659671070449783), (3622, 3622, 231733675726741722914), (3623, 3623, 232409860240343565546), (3624, 3624, 233095365623278720223), (3625, 3625, 233790347397660120146), (3626, 3626, 234494964272552538739), (3627, 3627, 235209378222385272159), (3628, 3628, 235933754567605855455), (3629, 3629, 236668262057647324983), (3630, 3630, 237413072956284150727), (3631, 3631, 238168363129454676497), (3632, 3632, 238934312135630728127), (3633, 3633, 239711103318817984380), (3634, 3634, 240498923904273757166), (3635, 3635, 241297965097032002020), (3636, 3636, 242108422183328681922), (3637, 3637, 242930494635024042969), (3638, 3638, 243764386217121935177), (3639, 3639, 244610305098490031735), (3640, 3640, 245468463965888671923), (3641, 3641, 246339080141420083318), (3642, 3642, 247222375703513934954), (3643, 3643, 248118577611569542081), (3644, 3644, 249027917834379592968), (3645, 3645, 249950633482465006869), (3646, 3646, 250886966944455468300), (3647, 3647, 251837166027655325288), (3648, 3648, 252801484102939897363), (3649, 3649, 253780180254132822872), (3650, 3650, 254773519432020894818), (3651, 3651, 255781772613168900852), (3652, 3652, 256805216963703307538), (3653, 3653, 257844136008240223536), (3654, 3654, 258898819804139953504), (3655, 3655, 259969565121277627332), (3656, 3656, 261056675627526871719), (3657, 3657, 262160462080161297577), (3658, 3658, 263281242523386722477), (3659, 3659, 264419342492225548473), (3660, 3660, 265575095222983588880), (3661, 3661, 266748841870538900727), (3662, 3662, 267940931732701851166), (3663, 3663, 269151722481905745777), (3664, 3664, 270381580404497894900), (3665, 3665, 271630880647912012590), (3666, 3666, 272900007476014354245), (3667, 3667, 274189354532928027332), (3668, 3668, 275499325115652480188), (3669, 3669, 276830332455808313051), (3670, 3670, 278182800010851291274), (3671, 3671, 279557161765113802437), (3672, 3672, 280953862541047017805), (3673, 3673, 282373358321052726812), (3674, 3674, 283816116580310245469), (3675, 3675, 285282616631020991831), (3676, 3676, 286773349978511312176), (3677, 3677, 288288820689652970528), (3678, 3678, 289829545774080423899), (3679, 3679, 291396055578704640977), (3680, 3680, 292988894196044829894), (3681, 3681, 294608619886922071072), (3682, 3682, 296255805518082556247), (3683, 3683, 297931039015342970078), (3684, 3684, 299634923832876574638), (3685, 3685, 301368079439285831162), (3686, 3686, 303131141821135982918), (3687, 3687, 304924764004653996570), (3688, 3688, 306749616596328689704), (3689, 3689, 308606388343180835857), (3690, 3690, 310495786713506616582), (3691, 3691, 312418538498934068428), (3692, 3692, 314375390438670241822), (3693, 3693, 316367109866856744382), (3694, 3694, 318394485383993284522), (3695, 3695, 320458327553432869346), (3696, 3696, 322559469623998557128), (3697, 3697, 324698768279820239030), (3698, 3698, 326877104418540953959), (3699, 3699, 329095383959095859041), (3700, 3700, 331354538680323328197), (3701, 3701, 333655527091726883507), (3702, 3702, 335999335337768937827), (3703, 3703, 338386978137142811752), (3704, 3704, 340819499758538362386), (3705, 3705, 343297975034489015578), (3706, 3706, 345823510414964228485), (3707, 3707, 348397245062451639070), (3708, 3708, 351020351990357609826), (3709, 3709, 353694039246643784801), (3710, 3710, 356419551144710906884), (3711, 3711, 359198169543639756611), (3712, 3712, 362031215180002961922), (3713, 3713, 364920049053570894985), (3714, 3714, 367866073869350241569), (3715, 3715, 370870735538515444315), (3716, 3716, 373935524740921449367), (3717, 3717, 377061978552021414684), (3718, 3718, 380251682137155681038), (3719, 3719, 383506270516328802417), (3720, 3720, 386827430402750248455), (3721, 3721, 390216902118582024630), (3722, 3722, 393676481591513434945), (3723, 3723, 397208022435970099745), (3724, 3724, 400813438122961737149), (3725, 3725, 404494704242781758575), (3726, 3726, 408253860864992096548), (3727, 3727, 412093015000359600450), (3728, 3728, 416014343169656574823), (3729, 3729, 420020094084498417643), (3730, 3730, 424112591445666719664), (3731, 3731, 428294236864657545702), (3732, 3732, 432567512914502932208), (3733, 3733, 436934986316239967260), (3734, 3734, 441399311267747305245), (3735, 3735, 445963232922034822077), (3736, 3736, 450629591022459632915), (3737, 3737, 455401323702752256651), (3738, 3738, 460281471460171798022), (3739, 3739, 465273181310570208884), (3740, 3740, 470379711134634673752), (3741, 3741, 475604434225095746855), (3742, 3742, 480950844045238980346), (3743, 3743, 486422559209641492139), (3744, 3744, 492023328698674438816), (3745, 3745, 497757037318970051350), (3746, 3746, 503627711422750293977), (3747, 3747, 509639524899656034541), (3748, 3748, 515796805455503776926), (3749, 3749, 522104041193234620276), (3750, 3750, 528565887512210517644), (3751, 3751, 535187174342959692050), (3752, 3752, 541972913735480074798), (3753, 3753, 548928307820280983584), (3754, 3754, 556058757162483383051), (3755, 3755, 563369869530512720395), (3756, 3756, 570867469102210606946), (3757, 3757, 578557606132568005844), (3758, 3758, 586446567108748977347), (3759, 3759, 594540885419636759420), (3760, 3760, 602847352568799830995), (3761, 3761, 611373029961551942155), (3762, 3762, 620125261298674778625), (3763, 3763, 629111685611393437495), (3764, 3764, 638340250974352356314), (3765, 3765, 647819228935642590414), (3766, 3766, 657557229705390964798), (3767, 3767, 667563218147049050926), (3768, 3768, 677846530618327438531), (3769, 3769, 688416892711721655652), (3770, 3770, 699284437947784647401), (3771, 3771, 710459727477732398094), (3772, 3772, 721953770855640740907), (3773, 3773, 733778047944420642559), (3774, 3774, 745944532023965718379), (3775, 3775, 758465714174370431582), (3776, 3776, 771354629011943064471), (3777, 3777, 784624881860908668775), (3778, 3778, 798290677449240361492), (3779, 3779, 812366850223001263733), (3780, 3780, 826868896379955182800), (3781, 3781, 841813007730045486841), (3782, 3782, 857216107497684992402), (3783, 3783, 873095888188684602119), (3784, 3784, 889470851653117735589), (3785, 3785, 906360351484517748341), (3786, 3786, 923784637905586927567), (3787, 3787, 941764905301112976712), (3788, 3788, 960323342570101522493), (3789, 3789, 979483186481305571024), (3790, 3790, 999268778229435048927), (3791, 3791, 1019705623403437716741), (3792, 3792, 1040820455593439603250), (3793, 3793, 1062641303879308704284), (3794, 3794, 1085197564461457972466), (3795, 3795, 1108520076713539221038), (3796, 3796, 1132641203957214586266), (3797, 3797, 1157594919281353129641), (3798, 3798, 1183416896751924867159), (3799, 3799, 1210144608384703287350), (3800, 3800, 1237817427280804197590), (3801, 3801, 1266476737355262401138), (3802, 3802, 1296166050121473527994), (3803, 3803, 1326931129029619575343), (3804, 3804, 1358820121895386348630), (3805, 3805, 1391883701996623693423), (3806, 3806, 1426175218460373638143), (3807, 3807, 1461750856611201957711), (3808, 3808, 1498669809004348612681), (3809, 3809, 1536994457924227053069), (3810, 3810, 1576790570190651356874), (3811, 3811, 1618127505182291792751), (3812, 3812, 1661078437059734074007), (3813, 3813, 1705720592249672260697), (3814, 3814, 1752135503337778225489), (3815, 3815, 1800409280611296674221), (3816, 3816, 1850632902594111199483), (3817, 3817, 1902902527027679988941), (3818, 3818, 1957319823871692013047), (3819, 3819, 2013992332029472349265), (3820, 3820, 2073033841646088392470), (3821, 3821, 2134564803982899628485), (3822, 3822, 2198712771042188919125), (3823, 3823, 2265612867300875532310), (3824, 3824, 2335408296114641888224), (3825, 3825, 2408250883574764542845), (3826, 3826, 2484301662841354461533), (3827, 3827, 2563731502240601944627), (3828, 3828, 2646721780702219074241), (3829, 3841, 2698500957556355349776), (3842, 3842, 2687842188720188837127), (3843, 3843, 2661229889821969145671), (3844, 3844, 2634881079031652619476), (3845, 3845, 2608793147556091702452), (3846, 3846, 2582963512431773962823), (3847, 3847, 2557389616269083131508), (3848, 3848, 2532068926999092209414), (3849, 3849, 2506998937622863573677), (3850, 3850, 2482177165963231261067), (3851, 3851, 2457601154419040852541), (3852, 3852, 2433268469721822626278), (3853, 3853, 2409176702694873887404), (3854, 3854, 2385323468014726621193), (3855, 3855, 2361706403974976852666), (3856, 3856, 2338323172252452329372), (3857, 3857, 2315171457675695375616), (3858, 3858, 2292248967995737995659), (3859, 3859, 2269553433659146530356), (3860, 3860, 2247082607583313396392), (3861, 3861, 2224834264933973659794), (3862, 3862, 2202806202904924415638), (3863, 3863, 2180996240499925163998), (3864, 3864, 2159402218316757588116), (3865, 3865, 2138021998333423354571), (3866, 3866, 2116853463696458766902), (3867, 3867, 2095894518511345313764), (3868, 3868, 2075143087634995360163), (3869, 3869, 2054597116470292435804), (3870, 3870, 2034254570762665778024), (3871, 3871, 2014113436398678988143), (3872, 3872, 1994171719206612859547), (3873, 3873, 1974427444759022633215), (3874, 3874, 1954878658177250131896), (3875, 3875, 1935523423937871417719), (3876, 3876, 1916359825681060809623), (3877, 3877, 1897385966020852286755), (3878, 3878, 1878599966357279491837), (3879, 3879, 1859999966690375734492), (3880, 3880, 1841584125436015578705), (3881, 3881, 1823350619243579780896), (3882, 3882, 1805297642815425525640), (3883, 3883, 1787423408728144084792), (3884, 3884, 1769726147255588202764), (3885, 3885, 1752204106193651685905), (3886, 3886, 1734855550686783847431), (3887, 3887, 1717678763056221631120), (3888, 3888, 1700672042629922407049), (3889, 3889, 1683833705574180601039), (3890, 3890, 1667162084726911486177), (3891, 3891, 1650655529432585629878), (3892, 3892, 1634312405378797653345), (3893, 3893, 1618131094434453122123), (3894, 3894, 1602109994489557546657), (3895, 3895, 1586247519296591630353), (3896, 3896, 1570542098313457059756), (3897, 3897, 1554992176547977286887), (3898, 3898, 1539596214403937907809), (3899, 3899, 1524352687528651393870), (3900, 3900, 1509260086662031083040), (3901, 3901, 1494316917487159488158), (3902, 3902, 1479521700482336126889), (3903, 3903, 1464872970774590224643), (3904, 3904, 1450369277994643786775), (3905, 3905, 1436009186133310679975), (3906, 3906, 1421791273399317504926), (3907, 3907, 1407714132078532183095), (3908, 3908, 1393776368394586319896), (3909, 3909, 1379976602370877544452), (3910, 3910, 1366313467693938162823), (3911, 3911, 1352785611578156596855), (3912, 3912, 1339391694631838214708), (3913, 3913, 1326130390724592291790), (3914, 3914, 1313000386856031972069), (3915, 3915, 1300000383025774229772), (3916, 3916, 1287129092104726960170), (3917, 3917, 1274385239707650455614), (3918, 3918, 1261767564066980649123), (3919, 3919, 1249274815907901632795), (3920, 3920, 1236905758324655081975), (3921, 3921, 1224659166658074338589), (3922, 3922, 1212533828374331028306), (3923, 3923, 1200528542944882206243), (3924, 3924, 1188642121727606144796), (3925, 3925, 1176873387849114994847), (3926, 3926, 1165221176088232668165), (3927, 3927, 1153684332760626404124), (3928, 3928, 1142261715604580598143), (3929, 3929, 1130952193667901582320), (3930, 3930, 1119754647195942160712), (3931, 3931, 1108667967520734812587), (3932, 3932, 1097691056951222586719), (3933, 3933, 1086822828664576818534), (3934, 3934, 1076062206598590909440), (3935, 3935, 1065408125345139514297), (3936, 3936, 1054859530044692588413), (3937, 3937, 1044415376281873849913), (3938, 3938, 1034074629982053316746), (3939, 3939, 1023836267308963679947), (3940, 3940, 1013699274563330376185), (3941, 3941, 1003662648082505322955), (3942, 3942, 993725394141094379164), (3943, 3943, 983886528852568692241), (3944, 3944, 974145078071850190338), (3945, 3945, 964500077298861574592), (3946, 3946, 954950571583031261972), (3947, 3947, 945495615428743823735), (3948, 3948, 936134272701726558153), (3949, 3949, 926865616536362928865), (3950, 3950, 917688729243923691945), (3951, 3951, 908602702221706625688), (3952, 3952, 899606635863075867018), (3953, 3953, 890699639468391947543), (3954, 3954, 881880831156823710438), (3955, 3955, 873149337779033376672), (3956, 3956, 864504294830726115516), (3957, 3957, 855944846367055559917), (3958, 3958, 847470144917876791997), (3959, 3959, 839079351403838407918), (3960, 3960, 830771635053305354374), (3961, 3961, 822546173320104311262), (3962, 3962, 814402151802083476497), (3963, 3963, 806338764160478689601), (3964, 3964, 798355212040077910496), (3965, 3965, 790450704990176149006), (3966, 3966, 782624460386313018818), (3967, 3967, 774875703352785167146), (3968, 3968, 767203666685925908066), (3969, 3969, 759607590778144463431), (3970, 3970, 752086723542717290526), (3971, 3971, 744640320339324050026), (3972, 3972, 737267643900320841610), (3973, 3973, 729967964257743407534), (3974, 3974, 722740558671033076767), (3975, 3975, 715584711555478293828), (3976, 3976, 708499714411364647355), (3977, 3977, 701484865753826383520), (3978, 3978, 694539471043392458930), (3979, 3979, 687662842617220256367), (3980, 3980, 680854299621010154818), (3981, 3981, 674113167941594212692), (3982, 3982, 667438780140192289794), (3983, 3983, 660830475386328999796), (3984, 3984, 654287599392404950293), (3985, 3985, 647809504348915792369), (3986, 3986, 641395548860312665712), (3987, 3987, 635045097881497688824), (3988, 3988, 628757522654948206756), (3989, 3989, 622532200648463571046), (3990, 3990, 616368515493528288164), (3991, 3991, 610265856924285433826), (3992, 3992, 604223620717114290917), (3993, 3993, 598241208630806228630), (3994, 3994, 592318028347332899634), (3995, 3995, 586453493413200890727), (3996, 3996, 580647023181387020522), (3997, 3997, 574898042753848535170), (3998, 3998, 569205982924602510069), (3999, 3999, 563570280123368821851), (4000, 4000, 557990376359771110743), (4001, 4001, 552465719168090208657), (4002, 4002, 546995761552564563026), (4003, 4003, 541579961933232240620), (4004, 4004, 536217784092309149129), (4005, 4005, 530908697121098167454), (4006, 4006, 525652175367423928173), (4007, 4007, 520447698383588047696), (4008, 4008, 515294750874839651184), (4009, 4009, 510192822648356090281), (4010, 4010, 505141408562728802259), (4011, 4011, 500140008477949309167), (4012, 4012, 495188127205890405116), (4013, 4013, 490285274461277628827), (4014, 4014, 485430964813146167156), (4015, 4015, 480624717636778383323), (4016, 4016, 475866057066117211211), (4017, 4017, 471154511946650704169), (4018, 4018, 466489615788763073435), (4019, 4019, 461870906721547597460), (4020, 4020, 457297927447076829168), (4021, 4021, 452770225195125573434), (4022, 4022, 448287351678342151915), (4023, 4023, 443848863047863516747), (4024, 4024, 439454319849369818562), (4025, 4025, 435103286979574077784), (4026, 4026, 430795333643142651271), (4027, 4027, 426530033310042228981), (4028, 4028, 422306963673309137605), (4029, 4029, 418125706607236769906), (4030, 4030, 413985848125976999907), (4031, 4031, 409886978342551485057), (4032, 4032, 405828691428268797086), (4033, 4033, 401810585572543363451), (4034, 4034, 397832262943112241041), (4035, 4035, 393893329646645783209), (4036, 4036, 389993395689748300207), (4037, 4037, 386132074940344851690), (4038, 4038, 382308985089450348208), (4039, 4039, 378523747613317176443), (4040, 4040, 374775987735957600439), (4041, 4041, 371065334392037228157), (4042, 4042, 367391420190135869463), (4043, 4043, 363753881376372147983), (4044, 4044, 360152357798388265330), (4045, 4045, 356586492869691351812), (4046, 4046, 353055933534347873081), (4047, 4047, 349560330232027597110), (4048, 4048, 346099336863393660505), (4049, 4049, 342672610755835307430), (4050, 4050, 339279812629539908347), (4051, 4051, 335920606563900899353), (4052, 4052, 332594659964258316191), (4053, 4053, 329301643528968629892), (4054, 4054, 326041231216800623656), (4055, 4055, 322813100214654082828), (4056, 4056, 319616930905598101810), (4057, 4057, 316452406837225843376), (4058, 4058, 313319214690322617204), (4059, 4059, 310217044247844175449), (4060, 4060, 307145588364202153910), (4061, 4061, 304104542934853617733), (4062, 4062, 301093606866191700726), (4063, 4063, 298112482045734357154), (4064, 4064, 295160873312608274410), (4065, 4065, 292238488428325024168), (4066, 4066, 289345038047846558582), (4067, 4067, 286480235690937186715), (4068, 4068, 283643797713799194768), (4069, 4069, 280835443280989301750), (4070, 4070, 278054894337613170050), (4071, 4071, 275301875581795217871), (4072, 4072, 272576114437421007793), (4073, 4073, 269877341027149512666), (4074, 4074, 267205288145692586798), (4075, 4075, 264559691233358996830), (4076, 4076, 261940288349860392901), (4077, 4077, 259346820148376626635), (4078, 4078, 256779029849877848153), (4079, 4079, 254236663217700839756), (4080, 4080, 251719468532377069065), (4081, 4081, 249227196566709969371), (4082, 4082, 246759600561098979576), (4083, 4083, 244316436199107900570), (4084, 4084, 241897461583275149079), (4085, 4085, 239502437211163513940), (4086, 4086, 237131125951647043505), (4087, 4087, 234783293021432716341), (4088, 4088, 232458705961814570635), (4089, 4089, 230157134615657990728), (4090, 4090, 227878351104611872008), (4091, 4091, 225622129806546407928), (4092, 4092, 223388247333214265276), (4093, 4093, 221176482508132935916), (4094, 4094, 218986616344686075165), (4095, 4095, 216818432024441658579), (4096, 4096, 214671714875684810474), (4097, 4097, 212546252352163178687), (4098, 4098, 210441834012042751176), (4099, 4099, 208358251497072030867), (4100, 4100, 206295298511952505809), (4101, 4101, 204252770803913372088), (4102, 4102, 202230466142488487216), (4103, 4103, 200228184299493551699), (4104, 4104, 198245727029201536335), (4105, 4105, 196282898048714392411), (4106, 4106, 194339503018529101397), (4107, 4107, 192415349523296139997), (4108, 4108, 190510247052768455443), (4109, 4109, 188624006982939064795), (4110, 4110, 186756442557365410688), (4111, 4111, 184907368868678624444), (4112, 4112, 183076602840275865786), (4113, 4113, 181263963208193926521), (4114, 4114, 179469270503162303486), (4115, 4115, 177692347032833963847), (4116, 4116, 175933016864192043413), (4117, 4117, 174191105806130736053), (4118, 4118, 172466441392208649557), (4119, 4119, 170758852863572920354), (4120, 4120, 169068171152052396390), (4121, 4121, 167394228863418214247), (4122, 4122, 165736860260810113116), (4123, 4123, 164095901248326844669), (4124, 4124, 162471189354779054128), (4125, 4125, 160862563717603023889), (4126, 4126, 159269865066933687019), (4127, 4127, 157692935709835333682), (4128, 4128, 156131619514688449190), (4129, 4129, 154585761895731137812), (4130, 4130, 153055209797753601794), (4131, 4131, 151539811680944160192), (4132, 4132, 150039417505885307121), (4133, 4133, 148553878718698323882), (4134, 4134, 147083048236334974141), (4135, 4135, 145626780432014825882), (4136, 4136, 144184931120806758299), (4137, 4137, 142757357545353226039), (4138, 4138, 141343918361735867365), (4139, 4139, 139944473625481056797), (4140, 4140, 138558884777704016631), (4141, 4141, 137187014631390115476), (4142, 4142, 135828727357811995521), (4143, 4143, 134483888473081183684), (4144, 4144, 133152364824832855133), (4145, 4145, 131834024579042430824), (4146, 4146, 130528737206972703787), (4147, 4147, 129236373472250201769), (4148, 4148, 127956805418069506702), (4149, 4149, 126689906354524264061), (4150, 4150, 125435550846063627783), (4151, 4151, 124193614699072898796), (4152, 4152, 122963974949577127520), (4153, 4153, 121746509851066462891), (4154, 4154, 120541098862442042467), (4155, 4155, 119347622636081230165), (4156, 4156, 118165963006021019965), (4157, 4157, 116996002976258435609), (4158, 4158, 115837626709166767930), (4159, 4159, 114690719514026502901), (4160, 4160, 113555167835669804853), (4161, 4161, 112430859243237430547), (4162, 4162, 111317682419046960938), (4163, 4163, 110215527147571248453), (4164, 4164, 109124284304525988568), (4165, 4165, 108043845846065335215), (4166, 4166, 106974104798084490312), (4167, 4167, 105914955245628208230), (4168, 4168, 104866292322404166564), (4169, 4169, 103828012200400164915), (4170, 4170, 102800012079604123678), (4171, 4171, 101782190177825865028), (4172, 4172, 100774445720619668345), (4173, 4173, 99776678931306602321), (4174, 4174, 98788791021095645863), (4175, 4175, 97810684179302619666), (4176, 4176, 96842261563665960066), (4177, 4177, 95883427290758376303), (4178, 4178, 94934086426493441884), (4179, 4179, 93994144976726180083), (4180, 4180, 93063509877946712953), (4181, 4181, 92142088988066052429), (4182, 4182, 91229791077293121217), (4183, 4183, 90326525819102100215), (4184, 4184, 89432203781289208133), (4185, 4185, 88546736417118027855), (4186, 4186, 87670036056552502827), (4187, 4187, 86802015897576735472), (4188, 4188, 85942589997600728190), (4189, 4189, 85091673264951216030), (4190, 4190, 84249181450446748544), (4191, 4191, 83415031139056186678), (4192, 4192, 82589139741639788790), (4193, 4193, 81771425486772068109), (4194, 4194, 80961807412645611989), (4195, 4195, 80160205359055061375), (4196, 4196, 79366539959460456807), (4197, 4197, 78580732633129165155), (4198, 4198, 77802705577355609065), (4199, 4199, 77032381759758028777), (4200, 4200, 76269684910651513640), (4201, 4201, 75514539515496548159), (4202, 4202, 74766870807422324910), (4203, 4203, 74026604759824084069), (4204, 4204, 73293668079033746603), (4205, 4205, 72567988197063115449), (4206, 4206, 71849493264418926187), (4207, 4207, 71138112142989035828), (4208, 4208, 70433774398999045375), (4209, 4209, 69736410296038658787), (4210, 4210, 69045950788157087908), (4211, 4211, 68362327513026819711), (4212, 4212, 67685472785175069020), (4213, 4213, 67015319589282246555), (4214, 4214, 66351801573546778767), (4215, 4215, 65694853043115622542), (4216, 4216, 65044408953579824299), (4217, 4217, 64400404904534479504), (4218, 4218, 63762777133202454954), (4219, 4219, 63131462508121242529), (4220, 4220, 62506398522892319336), (4221, 4221, 61887523289992395382), (4222, 4222, 61274775534645936022), (4223, 4223, 60668094588758352497), (4224, 4224, 60067420384909259898), (4225, 4225, 59472693450405207820), (4226, 4226, 58883854901391294871), (4227, 4227, 58300846437021084031), (4228, 4228, 57723610333684241614), (4229, 4229, 57152089439291328331), (4230, 4230, 56586227167615176565), (4231, 4231, 56025967492688293629), (4232, 4232, 55471254943255736266), (4233, 4233, 54922034597282907195), (4234, 4234, 54378252076517729896), (4235, 4235, 53839853541106663263), (4236, 4236, 53306785684264023033), (4237, 4237, 52778995726994082211), (4238, 4238, 52256431412865427931), (4239, 4239, 51739041002837057358), (4240, 4240, 51226773270135700354), (4241, 4241, 50719577495183861737), (4242, 4242, 50217403460578080927), (4243, 4243, 49720201446116911809), (4244, 4244, 49227922223878130504), (4245, 4245, 48740517053344683668), (4246, 4246, 48257937676578894720), (4247, 4247, 47780136313444450218), (4248, 4248, 47307065656875693285), (4249, 4249, 46838678868193755728), (4250, 4250, 46374929572469065077), (4251, 4251, 45915771853929767403), (4252, 4252, 45461160251415611290), (4253, 4253, 45011049753876842862), (4254, 4254, 44565395795917666200), (4255, 4255, 44124154253383827921), (4256, 4256, 43687281438993889030), (4257, 4257, 43254734098013751515), (4258, 4258, 42826469403974011401), (4259, 4259, 42402444954429714259), (4260, 4260, 41982618766762093325), (4261, 4261, 41566949274021874580), (4262, 4262, 41155395320813737208), (4263, 4263, 40747916159221521988), (4264, 4264, 40344471444773784146), (4265, 4265, 39945021232449291234), (4266, 4266, 39549525972722070529), (4267, 4267, 39157946507645614385), (4268, 4268, 38770244066975855826), (4269, 4269, 38386380264332530521), (4270, 4270, 38006317093398545071), (4271, 4271, 37630016924156975317), (4272, 4272, 37257442499165322096), (4273, 4273, 36888556929866655541), (4274, 4274, 36523323692937282714), (4275, 4275, 36161706626670576944), (4276, 4276, 35803669927396610836), (4277, 4277, 35449178145937238452), (4278, 4278, 35098196184096275695), (4279, 4279, 34750689291184431381), (4280, 4280, 34406623060578644932), (4281, 4281, 34065963426315490031), (4282, 4282, 33728676659718306962), (4283, 4283, 33394729366057729665), (4284, 4284, 33064088481245276896), (4285, 4285, 32736721268559680095), (4286, 4286, 32412595315405623857), (4287, 4287, 32091678530104578076), (4288, 4288, 31773939138717404035), (4289, 4289, 31459345681898419837), (4290, 4290, 31147867011780613700), (4291, 4291, 30839472288891696733), (4292, 4292, 30534130979100689834), (4293, 4293, 30231812850594742410), (4294, 4294, 29932487970885883575), (4295, 4295, 29636126703847409480), (4296, 4296, 29342699706779613346), (4297, 4297, 29052177927504567670), (4298, 4298, 28764532601489670960), (4299, 4299, 28479735248999674218), (4300, 4300, 28197757672276905166), (4301, 4301, 27918571952749411056), (4302, 4302, 27642150448266743619), (4303, 4303, 27368465790363112495), (4304, 4304, 27097490881547636133), (4305, 4305, 26829198892621421914), (4306, 4306, 26563563260021209816), (4307, 4307, 26300557683189316649), (4308, 4308, 26040156121969620445), (4309, 4309, 25782332794029327173), (4310, 4310, 25527062172306264528), (4311, 4311, 25274318982481450028), (4312, 4312, 25024078200476683196), (4313, 4313, 24776315049976914055), (4314, 4314, 24531004999977142629), (4315, 4315, 24288123762353606563), (4316, 4316, 24047647289459016399), (4317, 4317, 23809551771741600395), (4318, 4318, 23573813635387723164), (4319, 4319, 23340409539987844717), (4320, 4320, 23109316376225588828), (4321, 4321, 22880511263589691909), (4322, 4322, 22653971548108605851), (4323, 4323, 22429674800107530545), (4324, 4324, 22207598811987654005), (4325, 4325, 21987721596027380203), (4326, 4326, 21770021382205326934), (4327, 4327, 21554476616044878152), (4328, 4328, 21341065956480077379), (4329, 4329, 21129768273742650870), (4330, 4330, 20920562647269951356), (4331, 4331, 20713428363633615204), (4332, 4332, 20508344914488727925), (4333, 4333, 20305291994543294975), (4334, 4334, 20104249499547816807), (4335, 4335, 19905197524304769116), (4336, 7209, 19708116360697791204)]

def glob4 : ℕ := 2698500957556355349776

def runs5 : List (ℕ × ℕ × ℕ) := [(0, 3828, 0), (3829, 3829, 222825724555564474), (3830, 3830, 222849066393238851), (3831, 3831, 222919518316825225), (3832, 3832, 223036383083393180), (3833, 3833, 223201152216266230), (3834, 3834, 223415414438458346), (3835, 3835, 223680862945804159), (3836, 3836, 223999303346846159), (3837, 3837, 224372662341109831), (3838, 3838, 224802997216242806), (3839, 3839, 225292506254573605), (3840, 3840, 225843540151151511), (3841, 3841, 226458614558486435), (3842, 3842, 227140423888280474), (3843, 3843, 227891856517741651), (3844, 3844, 228716011567961082), (3845, 3845, 229616217444749482), (3846, 3846, 230596052358778770), (3847, 3847, 231659367072465479), (3848, 3848, 232810310156484733), (3849, 3849, 234053356079973664), (3850, 3850, 235393336506393794), (3851, 3851, 236835475222895104), (3852, 3852, 238385427196324200), (3853, 3853, 240049322325502133), (3854, 3854, 241833814549177024), (3855, 3855, 243746137074678671), (3856, 3856, 245794164616840108), (3857, 3857, 247986483683920944), (3858, 3858, 250332472121570212), (3859, 3859, 252842389332761367), (3860, 3860, 255527478837747356), (3861, 3861, 258400085131475005), (3862, 3862, 261473787146359743), (3863, 3863, 264763551047762312), (3864, 3864, 268285905592397408), (3865, 3865, 272059143883792776), (3866, 3866, 276103556085043334), (3867, 3867, 280441698523056809), (3868, 3868, 285098705670903431), (3869, 3869, 290102652762112387), (3870, 3870, 295484978315350421), (3871, 3871, 301280977678689086), (3872, 3872, 307530380893922903), (3873, 3873, 314278030790592977), (3874, 3874, 321574680301983743), (3875, 3875, 329477931595063357), (3876, 3876, 338053343737234380), (3877, 3877, 347375740238704114), (3878, 3878, 357530752752399545), (3879, 3879, 368616642129774276), (3880, 3880, 380746442235896786), (3881, 3881, 394050474194794405), (3882, 3882, 408679276979270834), (3883, 3883, 424806991064536222), (3884, 3884, 442635209849068086), (3885, 3885, 462397270552505835), (3886, 3886, 484362880567663109), (3887, 3887, 508842850962612922), (3888, 3888, 536193517048720201), (3889, 3889, 566820148698691032), (3890, 3890, 601178283922700514), (3891, 3891, 639771483698715136), (3892, 3892, 683143594700889010), (3893, 3893, 731863412777315383), (3894, 3894, 786499975759852185), (3895, 3895, 847587946646182952), (3896, 3896, 915584892445954814), (3897, 3897, 990825440663401597), (3898, 3898, 1073480258430998701), (3899, 3899, 1163528928824164932), (3900, 3900, 1260753794473362692), (3901, 3901, 1364756862573641442), (3902, 3902, 1474995869774240292), (3903, 3903, 1590831238474022288), (3904, 3904, 1711574543931338436), (3905, 3905, 1836531009032996357), (3906, 3906, 1965031912517422233), (3907, 3907, 2096456016262196310), (3908, 3908, 2230241280977599829), (3909, 3909, 2365889120381244349), (3910, 3910, 2502963554761237205), (3911, 3911, 2641087270727821027), (3912, 3912, 2779936086403937403), (3913, 3913, 2919232837795284134), (3914, 3914, 3058741315507845090), (3915, 3915, 3198260603216185765), (3916, 3916, 3337619984839149241), (3917, 3917, 3476674473100734199), (3918, 3918, 3615300946428455044), (3919, 3919, 3753394846997475752), (3920, 3920, 3890867378048806952), (3921, 3921, 4027643135270088470), (3922, 3922, 4163658109836473808), (3923, 3923, 4298858006486125142), (3924, 3924, 4433196826884068067), (3925, 3925, 4566635675472636371), (3926, 3926, 4699141751484721120), (3927, 3927, 4830687496573434350), (3928, 3928, 4961249872522674291), (3929, 3929, 5090809747771000795), (3930, 3930, 5219351375072765490), (3931, 3931, 5346861945618585563), (3932, 3932, 5473331207426912805), (3933, 3933, 5598751137879099244), (3934, 3934, 5723115661972795398), (3935, 3935, 5846420409273931418), (3936, 3936, 5968662503707789767), (3937, 3937, 6089840381288163670), (3938, 3938, 6209953631676275288), (3939, 3939, 6329002860117641263), (3940, 3940, 6446989566849751340), (3941, 3941, 6563916041526191292), (3942, 3942, 6679785270579987229), (3943, 3943, 6794600855763792593), (3944, 3944, 6908366942367969538), (3945, 3945, 7021088155838540413), (3946, 3946, 7132769545702697258), (3947, 3947, 7243416535866039659), (3948, 3948, 7353034880477877206), (3949, 3949, 7461630624672824726), (3950, 3950, 7569210069591868943), (3951, 3951, 7675779741166846713), (3952, 3952, 7781346362221125834), (3953, 3953, 7885916827498109244), (3954, 3954, 7989498181279563065), (3955, 3955, 8092097597299006885), (3956, 3956, 8193722360692593399), (3957, 3957, 8294379851761958080), (3958, 3958, 8394077531351204448), (3959, 3959, 8492822927664150789), (3960, 3960, 8590623624368742400), (3961, 3961, 8687487249853587269), (3962, 3962, 8783421467517289901), (3963, 3963, 8878433966984965789), (3964, 3964, 8972532456158296559), (3965, 3965, 9065724654015970251), (3966, 3966, 9158018284090544687), (3967, 3967, 9249421068555847270), (3968, 3968, 9339940722866129678), (3969, 3969, 9429584950894457606), (3970, 3970, 9518361440523342928), (3971, 3971, 9606277859645512268), (3972, 3972, 9693341852537032716), (3973, 3973, 9779561036568852374), (3974, 3974, 9864942999226220857), (3975, 3975, 9949495295408485292), (3976, 3976, 10033225444984456296), (3977, 3977, 10116140930580945318), (3978, 3978, 10198249195584224223), (3979, 3979, 10279557642336080000), (3980, 3980, 10360073630507858413), (3981, 3981, 10439804475637433112), (3982, 3982, 10518757447815421480), (3983, 3983, 10596939770508212925), (3984, 3984, 10674358619506494918), (3985, 3985, 10751021121988970659), (3986, 3986, 10826934355691871700), (3987, 3987, 10902105348175689958), (3988, 3988, 10976541076181295600), (3989, 3989, 11050248465068278656), (3990, 3990, 11123234388328960262), (3991, 3991, 11195505667172070704), (3992, 3992, 11267069070170591685), (3993, 3993, 11337931312968714713), (3994, 3994, 11408099058043280699), (3995, 3995, 11477578914515441954), (3996, 3996, 11546377438008630387), (3997, 3997, 11614501130549228057), (3998, 3998, 11681956440506621365), (3999, 3999, 11748749762569580509), (4000, 4000, 11814887437756143940), (4001, 4001, 11880375753454405307), (4002, 4002, 11945220943491799848), (4003, 4003, 12009429188230669953), (4004, 4004, 12073006614688057256), (4005, 4005, 12135959296677822478), (4006, 4006, 12198293254973335573), (4007, 4007, 12260014457489108665), (4008, 4008, 12321128819479863758), (4009, 4009, 12381642203755637233), (4010, 4010, 12441560420911624520), (4011, 4011, 12500889229571561722), (4012, 4012, 12559634336643527222), (4013, 4013, 12617801397587125793), (4014, 4014, 12675396016691091295), (4015, 4015, 12732423747360411903), (4016, 4016, 12788890092412144670), (4017, 4017, 12844800504379144353), (4018, 4018, 12900160385820985241), (4019, 4019, 12954975089641404636), (4020, 4020, 13009249919411642824), (4021, 4021, 13062990129699097313), (4022, 4022, 13116200926400748858), (4023, 4023, 13168887467080853811), (4024, 4024, 13221054861312431621), (4025, 4025, 13272708171022108251), (4026, 4026, 13323852410837905963), (4027, 4027, 13374492548439597539), (4028, 4028, 13424633504911268711), (4029, 4029, 13474280155095756530), (4030, 4030, 13523437327950653724), (4031, 4031, 13572109806905589880), (4032, 4032, 13620302330220519700), (4033, 4033, 13668019591344766682), (4034, 4034, 13715266239276587467), (4035, 4035, 13762046878923037878), (4036, 4036, 13808366071459936417), (4037, 4037, 13854228334691734753), (4038, 4038, 13899638143411117626), (4039, 4039, 13944599929758166633), (4040, 4040, 13989118083578933615), (4041, 4041, 14033196952783279940), (4042, 4042, 14076840843701847833), (4043, 4043, 14120054021442039135), (4044, 4044, 14162840710242885593), (4045, 4045, 14205205093828702821), (4046, 4046, 14247151315761427763), (4047, 4047, 14288683479791546557), (4048, 4048, 14329805650207526448), (4049, 4049, 14370521852183671629), (4050, 4050, 14410836072126328812), (4051, 4051, 14450752258018373850), (4052, 4052, 14490274319761915931), (4053, 4053, 14529406129519160714), (4054, 4054, 14568151522051378399), (4055, 4055, 14606514295055926984), (4056, 4056, 14644498209501285025), (4057, 4057, 14682106989960052012), (4058, 4058, 14719344324939878024), (4059, 4059, 14756213867212287720), (4060, 4060, 14792719234139366826), (4061, 4061, 14828864007998282290), (4062, 4062, 14864651736303610035), (4063, 4063, 14900085932127446880), (4064, 4064, 14935170074417285645), (4065, 4065, 14969907608311634801), (4066, 4066, 15004301945453366192), (4067, 4067, 15038356464300776390), (4068, 4068, 15072074510436349225), (4069, 4069, 15105459396873208782), (4070, 4070, 15138514404359253908), (4071, 4071, 15171242781678966872), (4072, 4072, 15203647745952890306), (4073, 4073, 15235732482934767993), (4074, 4074, 15267500147306346408), (4075, 4075, 15298953862969835149), (4076, 4076, 15330096723338025588), (4077, 4077, 15360931791622068182), (4078, 4078, 15391462101116909915), (4079, 4079, 15421690655484394314), (4080, 4080, 15451620429034027420), (4081, 4081, 15481254367001413930), (4082, 4082, 15510595385824368550), (4083, 4083, 15539646373416708352), (4084, 4084, 15568410189439732630), (4085, 4085, 15596889665571397422), (4086, 4086, 15625087605773192499), (4087, 4087, 15653006786554729167), (4088, 4088, 15680649957236047822), (4089, 4089, 15708019840207654665), (4090, 4090, 15735119131188297486), (4091, 4091, 15761950499480490852), (4092, 4092, 15788516588223801466), (4093, 4093, 15814820014645904824), (4094, 4094, 15840863370311424675), (4095, 4095, 15866649221368567125), (4096, 4096, 15892180108793561497), (4097, 4097, 15917458548632920404), (4098, 4098, 15942487032243531690), (4099, 4099, 15967268026530595204), (4100, 4100, 15991803974183417529), (4101, 4101, 16016097293909078050), (4102, 4102, 16040150380663979905), (4103, 4103, 16063965605883299531), (4104, 4104, 16087545317708348701), (4105, 4105, 16110891841211863053), (4106, 4106, 16134007478621231272), (4107, 4107, 16156894509539679186), (4108, 4108, 16179555191165423142), (4109, 4109, 16201991758508807111), (4110, 4110, 16224206424607438073), (4111, 4111, 16246201380739334276), (4112, 4112, 16267978796634101045), (4113, 4113, 16289540820682148836), (4114, 4114, 16310889580141968324), (4115, 4115, 16332027181345477280), (4116, 4116, 16352955709901454075), (4117, 4117, 16373677230897072625), (4118, 4118, 16394193789097553635), (4119, 4119, 16414507409143946968), (4120, 4120, 16434620095749059994), (4121, 4121, 16454533833891546746), (4122, 4122, 16474250589008172698), (4123, 4123, 16493772307184269972), (4124, 4124, 16513100915342397737), (4125, 4125, 16532238321429222548), (4126, 4126, 16551186414600633332), (4127, 4127, 16569947065405105696), (4128, 4128, 16588522125965330182), (4129, 4129, 16606913430158119045), (4130, 4130, 16625122793792606105), (4131, 4131, 16643152014786754127), (4132, 4132, 16661002873342184176), (4133, 4133, 16678677132117341298), (4134, 4134, 16696176536399010832), (4135, 4135, 16713502814272199601), (4136, 4136, 16730657676788396133), (4137, 4137, 16747642818132224044), (4138, 4138, 16764459915786502589), (4139, 4139, 16781110630695728352), (4140, 4140, 16797596607427991965), (4141, 4141, 16813919474335343652), (4142, 4142, 16830080843712621327), (4143, 4143, 16846082311954754918), (4144, 4144, 16861925459712560449), (4145, 4145, 16877611852047037411), (4146, 4146, 16893143038582182782), (4147, 4147, 16908520553656335051), (4148, 4148, 16923745916472061458), (4149, 4149, 16938820631244601608), (4150, 4150, 16953746187348880514), (4151, 4151, 16968524059465104046), (4152, 4152, 16983155707722949666), (4153, 4153, 16997642577844365251), (4154, 4154, 17011986101284988699), (4155, 4155, 17026187695374200946), (4156, 4156, 17040248763453824904), (4157, 4157, 17054170695015482772), (4158, 4158, 17067954865836624043), (4159, 4159, 17081602638115236479), (4160, 4160, 17095115360603252194), (4161, 4161, 17108494368738660931), (4162, 4162, 17121740984776342491), (4163, 4163, 17134856517917630219), (4164, 4164, 17147842264438617320), (4165, 4165, 17160699507817217718), (4166, 4166, 17173429518858993058), (4167, 4167, 17186033555821757373), (4168, 4168, 17198512864538970843), (4169, 4169, 17210868678541933967), (4170, 4170, 17223102219180793402), (4171, 4171, 17235214695744370616), (4172, 4172, 17247207305578824406), (4173, 4173, 17259081234205158267), (4174, 4174, 17270837655435583467), (4175, 4175, 17282477731488748633), (4176, 4176, 17294002613103846542), (4177, 4177, 17305413439653608717), (4178, 4178, 17316711339256198352), (4179, 4179, 17327897428886012000), (4180, 4180, 17338972814483400357), (4181, 4181, 17349938591063318391), (4182, 4182, 17360795842822915001), (4183, 4183, 17371545643248072253), (4184, 4184, 17382189055218904215), (4185, 4185, 17392727131114225268), (4186, 4186, 17403160912914997725), (4187, 4187, 17413491432306768492), (4188, 4188, 17423719710781104406), (4189, 4189, 17433846759736035824), (4190, 4190, 17443873580575517929), (4191, 4191, 17453801164807919167), (4192, 4192, 17463630494143546094), (4193, 4193, 17473362540591213902), (4194, 4194, 17482998266553871729), (4195, 4195, 17492538624923291849), (4196, 4196, 17501984559173831708), (4197, 4197, 17511337003455277718), (4198, 4198, 17520596882684779618), (4199, 4199, 17529765112637884165), (4200, 4200, 17538842600038676799), (4201, 4201, 17547830242649039886), (4202, 4202, 17556728929357036027), (4203, 4203, 17565539540264424881), (4204, 4204, 17574262946773321845), (4205, 4205, 17582900011672006869), (4206, 4206, 17591451589219891612), (4207, 4207, 17599918525231653063), (4208, 4208, 17608301657160541676), (4209, 4209, 17616601814180872001), (4210, 4210, 17624819817269703708), (4211, 4211, 17632956479287720848), (4212, 4212, 17641012605059317098), (4213, 4213, 17648988991451894676), (4214, 4214, 17656886427454384558), (4215, 4215, 17664705694254995521), (4216, 4216, 17672447565318199501), (4217, 4217, 17680112806460960670), (4218, 4218, 17687702175928215557), (4219, 4219, 17695216424467611502), (4220, 4220, 17702656295403510619), (4221, 4221, 17710022524710266420), (4222, 4222, 17717315841084780155), (4223, 4223, 17724536966018343869), (4224, 4224, 17731686613867777118), (4225, 4225, 17738765491925864196), (4226, 4226, 17745774300491098699), (4227, 4227, 17752713732936742146), (4228, 4228, 17759584475779203342), (4229, 4229, 17766387208745745101), (4230, 4230, 17773122604841524874), (4231, 4231, 17779791330415975765), (4232, 4232, 17786394045228534380), (4233, 4233, 17792931402513721858), (4234, 4234, 17799404049045584398), (4235, 4235, 17805812625201499536), (4236, 4236, 17812157765025354337), (4237, 4237, 17818440096290101661), (4238, 4238, 17824660240559700542), (4239, 4239, 17830818813250446715), (4240, 4240, 17836916423691699236), (4241, 4241, 17842953675186009097), (4242, 4242, 17848931165068655668), (4243, 4243, 17854849484766596770), (4244, 4244, 17860709219856838093), (4245, 4245, 17866510950124227644), (4246, 4246, 17872255249618680845), (4247, 4247, 17877942686711841846), (4248, 4248, 17883573824153186574), (4249, 4249, 17889149219125572969), (4250, 4250, 17894669423300243830), (4251, 4251, 17900134982891287617), (4252, 4252, 17905546438709562518), (4253, 4253, 17910904326216089043), (4254, 4254, 17916209175574916337), (4255, 4255, 17921461511705467375), (4256, 4256, 17926661854334368144), (4257, 4257, 17931810718046765863), (4258, 4258, 17936908612337141249), (4259, 4259, 17941956041659619790), (4260, 4260, 17946953505477786938), (4261, 4261, 17951901498314012075), (4262, 4262, 17956800509798286081), (4263, 4263, 17961651024716577268), (4264, 4264, 17966453523058710399), (4265, 4265, 17971208480065773486), (4266, 4266, 17975916366277056980), (4267, 4267, 17980577647576529953), (4268, 4268, 17985192785238857820), (4269, 4269, 17989762235974966086), (4270, 4270, 17994286451977154588), (4271, 4271, 17998765880963766637), (4272, 4272, 18003200966223417439), (4273, 4273, 18007592146658786106), (4274, 4274, 18011939856829975566), (4275, 4275, 18016244526997444597), (4276, 4276, 18020506583164516199), (4277, 4277, 18024726447119466458), (4278, 4278, 18028904536477198037), (4279, 4279, 18033041264720502361), (4280, 4280, 18037137041240914547), (4281, 4281, 18041192271379165082), (4282, 4282, 18045207356465232208), (4283, 4283, 18049182693857998944), (4284, 4284, 18053118676984518629), (4285, 4285, 18057015695378892843), (4286, 4286, 18060874134720765503), (4287, 4287, 18064694376873436923), (4288, 4288, 18068476799921601576), (4289, 4289, 18072221778208713242), (4290, 4290, 18075929682373981233), (4291, 4291, 18079600879389001305), (4292, 4292, 18083235732594024860), (4293, 4293, 18086834601733869996), (4294, 4294, 18090397842993477931), (4295, 4295, 18093925809033118287), (4296, 4296, 18097418849023246697), (4297, 4297, 18100877308679018152), (4298, 4298, 18104301530294459476), (4299, 4299, 18107691852776304290), (4300, 4300, 18111048611677493788), (4301, 4301, 18114372139230346610), (4302, 4302, 18117662764379401076), (4303, 4303, 18120920812813933005), (4304, 4304, 18124146607000152317), (4305, 4305, 18127340466213081575), (4306, 4306, 18130502706568119611), (4307, 4307, 18133633641052293332), (4308, 4308, 18136733579555200769), (4309, 4309, 18139802828899648434), (4310, 4310, 18142841692871985974), (4311, 4311, 18145850472252141115), (4312, 4312, 18148829464843357852), (4313, 4313, 18151778965501640806), (4314, 4314, 18154699266164908636), (4315, 4315, 18157590655881859394), (4316, 4316, 18160453420840550642), (4317, 4317, 18163287844396697151), (4318, 4318, 18166094207101688967), (4319, 4319, 18168872786730332600), (4320, 4320, 18171623858308318067), (4321, 4321, 18174347694139414485), (4322, 4322, 18177044563832396899), (4323, 4323, 18179714734327706994), (4324, 4324, 18182358469923850309), (4325, 4325, 18184976032303532562), (4326, 4326, 18187567680559537641), (4327, 4327, 18190133671220349837), (4328, 4328, 18192674258275522812), (4329, 4329, 18195189693200797819), (4330, 4330, 18197680224982973642), (4331, 4331, 18200146100144530703), (4332, 4332, 18202587562768011768), (4333, 4333, 18205004854520161639), (4334, 4334, 18207398214675828233), (4335, 4335, 18209767880141627375), (4336, 4336, 18212114085479373661), (4337, 4337, 18214437062929279684), (4338, 4338, 18216737042432925909), (4339, 4339, 18219014251656003474), (4340, 4340, 18221268916010832143), (4341, 4341, 18223501258678655631), (4342, 4342, 18225711500631716514), (4343, 4343, 18227899860655112877), (4344, 4344, 18230066555368438873), (4345, 4345, 18232211799247211316), (4346, 4346, 18234335804644084418), (4347, 4347, 18236438781809854775), (4348, 4348, 18238520938914258657), (4349, 4349, 18240582482066563658), (4350, 4350, 18242623615335956742), (4351, 7209, 18446744073709461440)]

def glob5 : ℕ := 20468299698317289241

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

def meanN : ℕ := 110151
def meanD : ℕ := 100000
def secN : ℕ := 93003
def secD : ℕ := 10000000
def countN : ℕ := 104116
def countD : ℕ := 10000000
def overN : ℕ := 40032
def overD : ℕ := 10000000
def mgfN : ℕ := 11776
def mgfD : ℕ := 1000
def scarfN : ℕ := 20392
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
theorem rc_θ : (rcPar.θ : ℝ) = 397071 / 200000 - 29249 / 2500000 := by norm_num [rcPar]
theorem rc_m : (rcPar.m : ℝ) = (meanN : ℝ) / meanD := by norm_num [rcPar, meanN, meanD]
theorem rc_vv : (rcPar.vv : ℝ) = (secN : ℝ) / secD := by norm_num [rcPar, secN, secD]

/-- `exp (B - a θ_mid) ≤ (9369 / 10000000 : ℝ)` from the Taylor lower bound of `exp (a θ_mid - B)`. -/
theorem rc_exp_mid : Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) ≤ (9369 / 10000000 : ℝ) := by
  have hx : (mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ ≤ -(6973 / 1000 : ℝ) := by norm_num [rcPar, mgfN, mgfD]
  have h0 : (0 : ℝ) ≤ (6973 / 1000 : ℝ) := by norm_num
  have he := Real.sum_le_exp_of_nonneg h0 30
  have hs : (10000000 / 9369 : ℝ) ≤ ∑ i ∈ Finset.range 30, (6973 / 1000 : ℝ) ^ i / (Nat.factorial i) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  refine (Real.exp_le_exp.mpr hx).trans ?_
  rw [Real.exp_neg, show (9369 / 10000000 : ℝ) = ((10000000 / 9369 : ℝ))⁻¹ by norm_num]
  exact inv_anti₀ (by norm_num) (hs.trans he)

/-- Route-C total at the middle threshold: `K0 + K1 + O Λ + tF ≤ (2118 / 1000000 : ℝ)`. -/
theorem rc_total_mid :
    3 / (8 * (rcPar.a : ℝ)) * Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (2118 / 1000000 : ℝ) := by
  have hk : (0 : ℝ) ≤ 3 / (8 * (rcPar.a : ℝ)) := by rw [rc_a]; norm_num
  have h1 := mul_le_mul_of_nonneg_left rc_exp_mid hk
  have h2 : 3 / (8 * (rcPar.a : ℝ)) * (9369 / 10000000 : ℝ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (2118 / 1000000 : ℝ) := by
    rw [rc_a]; norm_num [scarfN, scarfD, overN, overD, countN, countD, longN, longD]
  linarith

/-- Low threshold: `3/(8a) exp (B - a (1 - 29249/2500000)) + O ≤ 49/100`. -/
theorem rc_total_low :
    3 / (8 * (rcPar.a : ℝ)) * Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * (1 - 29249 / 2500000)) + (overN : ℝ) / overD ≤
      49 / 100 := by
  have hy : (mgfN : ℝ) / mgfD - rcPar.a * (1 - 29249 / 2500000) ≤ 2 + 2 / 5 := by norm_num [rcPar, mgfN, mgfD]
  have hx : Real.exp ((2 / 5 : ℝ) / 2) ≤ 1 / (1 - (2 / 5 : ℝ) / 2) := by
    have h := Real.add_one_le_exp (-((2 / 5 : ℝ) / 2))
    rw [Real.exp_neg] at h
    rw [le_div_iff₀ (by norm_num)]
    have hpos := Real.exp_pos ((2 / 5 : ℝ) / 2)
    have h' : (1 - (2 / 5 : ℝ) / 2) * Real.exp ((2 / 5 : ℝ) / 2) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h hpos.le
      rwa [inv_mul_cancel₀ hpos.ne', show -((2 / 5 : ℝ) / 2) + 1 = 1 - (2 / 5 : ℝ) / 2 by ring] at this
    linarith
  have he : Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * (1 - 29249 / 2500000)) ≤
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
    (2:ENNReal)^128 * ((926*2^62:Nat):ENNReal) *
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

noncomputable def feeCoefficient : ENNReal := 926/2^66

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

 theorem feeCoefficient_real : feeCoefficient.toReal = (926:ℝ)/2^66 := by
  norm_num [feeCoefficient,ENNReal.toReal_div]

 theorem cappedIncrement_nat (n : Nat) :
    cappedIncrement (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (Real.exp (6*min ((926:ℝ)/2^66*(n:ℝ)) (6/5))-1) := by
  rw [cappedIncrement_real _ (by unfold feeCoefficient; finiteness),
    ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast]

 theorem cappedResidual_nat (n : Nat) :
    cappedResidual (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (max 0 ((926:ℝ)/2^66*(n:ℝ)-6/5)) := by
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
    ((926:ℝ)/2^66) (alphabetSize:ℝ) ENNReal.toReal_nonneg hx).1
  rw [cappedIncrement_real _ (priceBucket_ne_top W)]
  calc
    _ ≤ ENNReal.ofReal ((maxFee:ℝ)*((926:ℝ)/2^66)*(alphabetSize:ℝ)/scale) :=
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

 theorem law_price_mean_bound : Law.lawAvg honestLaw (2^32) price ≤ (1105:ENNReal)/1000 := by
  rw [law_price_coordAverage]
  apply coordAverage_bound_of_rows (2^32) 1 1 (by norm_num) (by norm_num)
    id forestMoment (1105/1000) (fun _ _ h => h)
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

 theorem law_nearPrice_mean_bound : Law.lawAvg honestLaw (2^32) nearPrice ≤ (22820/50) := by
  rw [law_nearPrice_coordAverage]
  apply coordAverage_history_bound (2^32) 54 1 (by norm_num) (by norm_num)
    nearBucket (fun _ h => feeCoefficient*(SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit h:ENNReal))
    forestNearMoment (22820/50) (fun L b R => nearBucket_insert L R b)
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
    nearPrice average_nearScore (22820/50)
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
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((397071 : ℝ) / 200000 - 29249 / 2500000)) ≤
      ENNReal.ofReal ((2118 : ℝ) / 1000000) := by
  have hP := parFacts_of_ok rcPar par_ok
  have he : (fun W : List Proposal => price W - ENNReal.ofReal ((397071 : ℝ) / 200000 - 29249 / 2500000)) =
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
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((1 : ℝ) - 29249 / 2500000)) ≤
      ENNReal.ofReal ((49 : ℝ) / 100) := by
  have hP := parFacts_of_ok rcPar par_ok
  apply price_excess_of_bucket_bounds (2 ^ 32) (ENNReal.ofReal rcPar.c0) ENNReal.ofReal_ne_top
    (1 - 29249 / 2500000) (rcPar.a : ℝ) ((mgfN : ℝ) / mgfD) ((overN : ℝ) / overD) (49 / 100)
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
      (fun W => price W-ENNReal.ofReal ((397071:ℝ)/200000-29249/2500000)) ≤
        ENNReal.ofReal ((2118 : ℝ) / 1000000) := rc_excess_middle

theorem excess_high_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((2:ℝ)-4326/1000000-29249/2500000)) ≤
        ENNReal.ofReal ((211974000:ℝ)/100000000000) :=
  (Law.lawAvg_mono _ _ (fun W => tsub_le_tsub_left
    (ENNReal.ofReal_le_ofReal (by norm_num : (397071 : ℝ) / 200000 - 29249 / 2500000 ≤ 2 - 4326 / 1000000 - 29249 / 2500000)) _)).trans
    (rc_excess_middle.trans (ENNReal.ofReal_le_ofReal (by norm_num)))

theorem excess_low_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((1:ℝ)-29249/2500000)) ≤
        ENNReal.ofReal ((49:ℝ)/100) := rc_excess_low

/-- Large queries: the cap-777 envelope `(98000/100000) y` from the high and low endpoints (as in #938). -/
theorem excess_large_certified (y : ℝ)
    (hy0 : 2163/1000000 ≤ y) (hy1 : y ≤ 1/2) :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal (2-2*y-29249/2500000)) ≤
        ENNReal.ofReal ((98000/100000)*y) := by
  let t : ℝ := (y-2163/1000000)/(1/2-2163/1000000)
  have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hy0) (by norm_num)
  have ht1 : t≤1 := (div_le_one (by norm_num : (0:ℝ)<1/2-2163/1000000)).2 (by linarith)
  have h := price_excess_affine (2^32) (2-4326/1000000-29249/2500000) (1-29249/2500000)
    (211974000/100000000000) (49/100) t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ht0 ht1 excess_high_certified excess_low_certified
  have harg : (1-t)*(2-4326/1000000-29249/2500000)+t*(1-29249/2500000) = 2-2*y-29249/2500000 := by
    dsimp [t]; ring
  rw [harg] at h
  have hgap : (98000/100000)*y-((1-t)*(211974000/100000000000)+t*(49/100)) = t*(0/200000) := by
    dsimp [t]; ring
  have hval : (1-t)*(211974000/100000000000)+t*(49/100) ≤ (98000/100000)*y := by nlinarith
  exact h.trans (ENNReal.ofReal_le_ofReal hval)

/-- Tiny queries: affine interpolation between the middle and low endpoints. -/
theorem excess_tiny_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W=>price W-ENNReal.ofReal ((249:ℝ)/125-29249/2500000)) ≤
        ENNReal.ofReal ((18:ℝ)/5000) :=
  (Law.lawAvg_mono _ _ (fun W => tsub_le_tsub_left
    (ENNReal.ofReal_le_ofReal (by norm_num : (397071 : ℝ) / 200000 - 29249 / 2500000 ≤ 249 / 125 - 29249 / 2500000)) _)).trans
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
